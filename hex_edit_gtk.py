#!/usr/bin/env python3
"""
Binary Field Annotator — GTK3 / PyGObject edition.

Color-annotate byte ranges in binary files to track protocol header fields,
inspect values, edit bytes inline, and script the buffer from an embedded
Python console.

This is the GTK3 port of the original customtkinter app.  It is intended for
Kali Linux 2025.3+ where GTK3 is already present (Xfce) and only the Python
bindings are needed:

  sudo apt install python3-gi python3-gi-cairo gir1.2-gtk-3.0

The hex view uses GtkTextView + GtkTextBuffer + GtkTextTag, the direct analogue
of the tkinter tk.Text tag system: overlapping per-byte color layers whose
z-order is fixed by tag priority (field colors < selection < edited < cursor).
"""

import gi
gi.require_version('Gtk', '3.0')
gi.require_version('PangoCairo', '1.0')
from gi.repository import Gtk, Gdk, GLib, Pango, PangoCairo  # noqa: E402

import code
import contextlib
import io
import json
import os
import struct

# ── Constants ────────────────────────────────────────────────────────────────

OFFSET_COLS = 10    # "XXXXXXXX  " — 8 hex digits + 2 spaces
HEX_CELL_COLS = 4   # " XX " centered display cell for one byte

PALETTE = [
    "#ff6b6b",  # red
    "#ffd93d",  # yellow
    "#6bcb77",  # green
    "#4d96ff",  # blue
    "#ff6bd6",  # magenta
    "#64ffda",  # cyan
    "#ff9a3c",  # orange
    "#c77dff",  # purple
    "#a8dadc",  # teal
    "#f9c74f",  # amber
]

# The colour strip shows a fixed number of swatches so adding a custom colour never
# widens the Add-Field pane (which would shove the hex/right pane divider). Custom
# colours are capped and compete for slots; the most-used colours sort to the left.
PALETTE_SLOTS = len(PALETTE)
MAX_CUSTOM_COLORS = 6

THEME = {
    'dark': {
        'window':       '#1b1b1d',
        'surface':      '#232327',
        'card':         '#2a2a2e',
        'border':       '#34343a',
        'accent':       '#4d96ff',
        'accent_hover': '#3b7fe0',
        'neutral':      '#3a3a40',
        'neutral_hover':'#45454c',
        'danger':       '#e0524a',
        'danger_hover': '#c0392b',
        'text':         '#e6e6e6',
        'muted':        '#9aa0a6',
        'selection':    '#2d4f78',
        'hex_bg':       '#1b1b1d',
        'cursor_ins':   '#ffffff',
    },
    'light': {
        'window':       '#f2f2f4',
        'surface':      '#e7e7ea',
        'card':         '#ffffff',
        'border':       '#ccccd2',
        'accent':       '#3b7fe0',
        'accent_hover': '#2f6bc4',
        'neutral':      '#d8d8dd',
        'neutral_hover':'#c8c8cf',
        'danger':       '#d93a32',
        'danger_hover': '#b62b24',
        'text':         '#1c1c1e',
        'muted':        '#5f6368',
        'selection':    '#b9d4ff',
        'hex_bg':       '#ffffff',
        'cursor_ins':   '#000000',
    },
}

EDITED_BG = '#ff1744'   # scarlet highlight for session-modified bytes (both modes)
ZOOM_MIN = 0.75
ZOOM_MAX = 1.60
ZOOM_STEP = 0.10


def _contrast_fg(hex_color: str) -> str:
    r = int(hex_color[1:3], 16)
    g = int(hex_color[3:5], 16)
    b = int(hex_color[5:7], 16)
    return '#000000' if 0.299 * r + 0.587 * g + 0.114 * b > 128 else '#ffffff'


def _resolve_font(preferred: list[str], fallback: str) -> str:
    """Return the first installed font family from `preferred`, else `fallback`."""
    try:
        fm = PangoCairo.FontMap.get_default()
        available = {fam.get_name() for fam in fm.list_families()}
    except Exception:
        return fallback
    for fam in preferred:
        if fam in available:
            return fam
    return fallback


def _rgba_to_hex(rgba: "Gdk.RGBA") -> str:
    return '#%02x%02x%02x' % (round(rgba.red * 255),
                              round(rgba.green * 255),
                              round(rgba.blue * 255))


# ── Main application ─────────────────────────────────────────────────────────

class BinaryFieldAnnotator:
    _INSPECT_FORMATS = ['Integer', 'Float', 'String', 'Hex', 'Binary', 'Bytes (dec)']

    def __init__(self, app: "MultiFileApp"):
        # `app` is the owning controller; the GTK window is shared across all tabs.
        self.app = app
        self.root = app.window

        self._mode = app._mode

        self.data: bytearray | None = None
        self.filepath: str | None = None
        self._modified = False
        self.fields: list[dict] = []
        self._next_id = 0
        self._current_color = PALETTE[0]
        self._custom_colors: list[str] = []
        self._color_usage: dict[str, int] = {}   # color -> times applied to a field
        self._editing_field_id: int | None = None

        # Mouse selection state (annotation / drag-to-select)
        self._drag_anchor: int | None = None
        self._dragging = False
        self._sel_range: tuple[int, int] | None = None

        # Live inspector target: 'sel' (mouse selection) | 'field' | None
        self._inspect_mode: str | None = None
        self._inspect_field_id: int | None = None

        # Inline hex-edit state
        self._edit_mode = False
        self._edit_cursor: int | None = None
        self._edit_nibble = 0   # 0 = expecting high nibble, 1 = expecting low nibble
        self._edited: set[int] = set()
        self._ui_scale = app._ui_scale

        # Resolve fonts
        self.mono_family = _resolve_font(
            ['JetBrains Mono', 'Cascadia Code', 'DejaVu Sans Mono', 'Consolas',
             'Courier New'], 'Monospace')
        self.ui_family = _resolve_font(
            ['Inter', 'Segoe UI', 'DejaVu Sans', 'Cantarell', 'Helvetica',
             'Arial'], 'Sans')

        # Widgets needing scaled size requests (set in build; rescaled on zoom)
        self._min_reqs: list[tuple[Gtk.Widget, int | None, int | None]] = []

        # Field tags keyed by field id; tree iters keyed by field id
        self._field_tags: dict[int, Gtk.TextTag] = {}
        self._tree_iters: dict[int, Gtk.TreeIter] = {}

        # Console state
        self._console_visible = False
        self._console_floating = False
        self._console_window: Gtk.Window | None = None
        self._console_more = False
        self._console_history: list[str] = []
        self._console_history_index: int | None = None
        self._console_output_cache = ""
        self._console_drag_origin: tuple[int, int] | None = None
        self._console_dragging = False
        self._console_dirty = False
        self._console_changed_ranges: list[tuple[int, int]] = []
        self._console = code.InteractiveConsole()
        self._init_console_namespace()

        # Shared CSS provider (theme + scaling) — owned by the controller so all
        # tabs render against a single screen-level stylesheet.
        self._css_provider = app.css_provider

        self._build_ui()
        self._update_css(self._mode)
        self._retheme_native(self._mode)
        # Window-level key handling lives on the controller (one handler for all tabs).

    # ── Scaling helpers ───────────────────────────────────────────────────────

    def _scaled_int(self, value: int, minimum: int = 1) -> int:
        return max(minimum, round(value * self._ui_scale))

    def _font_size(self, value: int, minimum: int = 7) -> int:
        return self._scaled_int(value, minimum)

    def _mono_desc(self, size: int, bold: bool = False) -> "Pango.FontDescription":
        suffix = ' Bold' if bold else ''
        return Pango.FontDescription(f"{self.mono_family}{suffix} {self._font_size(size)}")

    # ── CSS theming ───────────────────────────────────────────────────────────

    def _build_css(self, mode: str) -> bytes:
        t = THEME[mode]
        sz = self._font_size(13)
        sz_sm = self._font_size(12)
        # Slim toggle-switch geometry (scales with zoom).
        sw_h = self._scaled_int(18, 14)          # track height
        sw_w = self._scaled_int(34, 26)          # track width
        sl_d = self._scaled_int(14, 10)          # knob diameter
        sl_m = self._scaled_int(2, 1)            # knob inset
        css = f"""
        * {{
            font-family: "{self.ui_family}";
            font-size: {sz}px;
        }}
        window, .window {{ background-color: {t['window']}; color: {t['text']}; }}
        .surface {{ background-color: {t['surface']}; }}
        .card    {{ background-color: {t['card']}; border-radius: 2px; }}
        .toolbar, .statusbar {{ background-color: {t['surface']}; }}
        .title   {{ color: {t['accent']}; font-weight: bold; }}
        .muted   {{ color: {t['muted']}; font-size: {sz_sm}px; }}
        .sep     {{ background-color: {t['border']}; }}
        label    {{ color: {t['text']}; }}

        button {{
            background-image: none;
            background-color: {t['neutral']};
            color: {t['text']};
            border: 1px solid {t['border']};
            border-radius: 2px;
            padding: 4px 10px;
            min-height: 0;
        }}
        button:hover  {{ background-color: {t['neutral_hover']}; }}
        button.accent {{ background-color: {t['accent']}; color: #ffffff; border-color: {t['accent']}; }}
        button.accent:hover {{ background-color: {t['accent_hover']}; border-color: {t['accent_hover']}; }}
        button.danger {{ background-color: {t['danger']}; color: #ffffff; border-color: {t['danger']}; }}
        button.danger:hover {{ background-color: {t['danger_hover']}; border-color: {t['danger_hover']}; }}
        button.swatch {{ border-radius: 1px; padding: 0; }}
        button:disabled {{ opacity: 0.5; }}

        radiobutton.seg {{
            background-image: none;
            background-color: {t['neutral']};
            color: {t['text']};
            border-radius: 2px;
            padding: 2px 10px;
        }}
        radiobutton.seg:checked {{ background-color: {t['accent']}; color: #ffffff; }}
        radiobutton.seg radio {{ -gtk-icon-source: none; min-width: 0; min-height: 0; margin: 0; }}

        switch {{
            background-image: none;
            background-color: {t['neutral']};
            border: 1px solid {t['border']};
            border-radius: {sw_h}px;
            min-width: {sw_w}px;
            min-height: {sw_h}px;
            padding: 0;
            font-size: 0;           /* drop the built-in on/off text that inflates height */
        }}
        switch:checked {{ background-color: {t['accent']}; border-color: {t['accent']}; }}
        switch:hover {{ background-color: {t['neutral_hover']}; }}
        switch:checked:hover {{ background-color: {t['accent_hover']}; }}
        switch image {{ color: transparent; -gtk-icon-source: none; }}
        switch slider {{
            background-color: #ffffff;
            border: none;
            border-radius: {sl_d}px;
            min-width: {sl_d}px;
            min-height: {sl_d}px;
            margin: {sl_m}px;
            box-shadow: 0 1px 2px rgba(0,0,0,0.35);
        }}

        entry {{
            background-image: none;
            background-color: {t['card']};
            color: {t['text']};
            border: 1px solid {t['border']};
            border-radius: 2px;
            padding: 3px 6px;
        }}
        entry:focus {{ border-color: {t['accent']}; }}

        treeview, treeview.view {{
            background-color: {t['card']};
            color: {t['text']};
        }}
        treeview.view:selected {{ background-color: {t['selection']}; color: {t['text']}; }}
        columnview > header > button, columnheader button, treeview header button {{
            background-color: {t['surface']};
            color: {t['muted']};
            border: none;
        }}

        combobox button {{ background-color: {t['neutral']}; color: {t['text']}; }}

        /* Dropdown popups & context menus — without these the menu background
           falls back to the theme default (white), hiding our white label text. */
        menu, .menu, .context-menu,
        combobox > window, combobox window.background, popover, popover.background {{
            background-color: {t['card']};
            color: {t['text']};
            border: 1px solid {t['border']};
            border-radius: 2px;
        }}
        menu menuitem, .menu menuitem, .context-menu menuitem,
        combobox menuitem, popover modelbutton {{
            background-color: transparent;
            color: {t['text']};
            padding: 3px 8px;
        }}
        menu menuitem:hover, menu menuitem:selected,
        .menu menuitem:hover, combobox menuitem:hover, combobox menuitem:selected,
        popover modelbutton:hover {{
            background-color: {t['selection']};
            color: {t['text']};
        }}
        menuitem label, combobox menuitem label {{ color: {t['text']}; }}

        .hover {{
            background-color: {t['surface']};
            border-radius: 2px;
            padding: 4px 6px;
        }}
        paned > separator {{
            background-color: {t['border']};
            min-width: {self._scaled_int(6, 4)}px;
            min-height: {self._scaled_int(6, 4)}px;
        }}

        notebook {{ background-color: {t['window']}; }}
        notebook > header {{
            background-color: {t['surface']};
            border: none;
        }}
        notebook > header > tabs > tab {{
            background-color: {t['neutral']};
            color: {t['muted']};
            border: 1px solid {t['border']};
            border-radius: 2px;
            margin: 3px 1px 0 1px;
            padding: 2px 6px;
            min-height: 0;
        }}
        notebook > header > tabs > tab:checked {{
            background-color: {t['card']};
            color: {t['text']};
            border-bottom-color: {t['accent']};
        }}
        notebook > header > tabs > tab:hover {{ background-color: {t['neutral_hover']}; }}
        notebook > header > tabs > tab button.tabclose {{
            padding: 0 2px;
            margin: 0;
            border: none;
            background-color: transparent;
            color: {t['muted']};
            min-width: 0;
            min-height: 0;
        }}
        notebook > header > tabs > tab button.tabclose:hover {{
            background-color: {t['danger']};
            color: #ffffff;
        }}
        notebook > header > button {{          /* the "+" action widget */
            background-color: {t['neutral']};
            color: {t['text']};
            border: 1px solid {t['border']};
            border-radius: 2px;
            margin: 3px;
            padding: 0 8px;
        }}
        notebook > header > button:hover {{ background-color: {t['neutral_hover']}; }}
        """
        return css.encode('utf-8')

    def _update_css(self, mode: str):
        self._css_provider.load_from_data(self._build_css(mode))

    def _retheme_native(self, mode: str = 'dark'):
        """Re-apply colors/fonts that CSS cannot reach: the GtkTextView buffers,
        the overlay GtkTextTags, and the per-row TreeView colors."""
        self._mode = mode
        t = THEME[mode]

        mono_hex = self._mono_desc(11)
        mono_det = self._mono_desc(10)
        fg = self._gdk_rgba(t['text'])

        for view, bg_key in ((self.hex_view, 'hex_bg'),
                             (self._detail_view, 'card')):
            view.override_font(mono_hex if view is self.hex_view else mono_det)
            view.override_background_color(Gtk.StateFlags.NORMAL, self._gdk_rgba(t[bg_key]))
            view.override_color(Gtk.StateFlags.NORMAL, fg)

        if hasattr(self, '_console_view'):
            self._console_view.override_font(mono_det)
            self._console_view.override_background_color(
                Gtk.StateFlags.NORMAL, self._gdk_rgba(t['hex_bg']))
            self._console_view.override_color(Gtk.StateFlags.NORMAL, fg)

        # Overlay tags — edited constant; cursor inverts per mode.
        self._tag_edited.set_property('background', EDITED_BG)
        self._tag_edited.set_property('foreground', '#ffffff')
        if mode == 'light':
            cur_bg, cur_fg = t['text'], '#ffffff'
        else:
            cur_bg, cur_fg = '#ffffff', '#000000'
        self._tag_cursor.set_property('background', cur_bg)
        self._tag_cursor.set_property('foreground', cur_fg)
        self._tag_cursor.set_property('font', f"{self.mono_family} Bold {self._font_size(11)}")
        self._tag_rangesel.set_property('background', t['selection'])
        self._tag_rangesel.set_property('foreground', t['text'])

        self._update_css(mode)

    @staticmethod
    def _gdk_rgba(hex_color: str) -> "Gdk.RGBA":
        rgba = Gdk.RGBA()
        rgba.parse(hex_color)
        return rgba

    # ── Small widget factories ────────────────────────────────────────────────

    def _btn(self, text, cmd, kind='neutral', width=None, height=28):
        b = Gtk.Button(label=text)
        b.get_style_context().add_class(kind)
        if cmd is not None:
            b.connect('clicked', lambda _w: cmd())
        b.set_size_request(width if width else -1, height)
        return b

    def _class(self, widget, *classes):
        ctx = widget.get_style_context()
        for c in classes:
            ctx.add_class(c)
        return widget

    def _sep(self):
        s = Gtk.Box()
        s.set_size_request(1, 26)
        self._class(s, 'sep')
        return s

    def _segmented(self, values, active, callback):
        """A linked row of radio buttons rendered as a segmented control."""
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=0)
        box.get_style_context().add_class('linked')
        group = None
        mapping: dict[str, Gtk.RadioButton] = {}
        for v in values:
            rb = Gtk.RadioButton.new_with_label_from_widget(group, str(v))
            rb.set_mode(False)
            self._class(rb, 'seg')
            if group is None:
                group = rb
            if str(v) == str(active):
                rb.set_active(True)
            mapping[str(v)] = rb
            box.pack_start(rb, False, False, 0)
        # Connect AFTER initial actives so setup doesn't fire callbacks.
        for v in values:
            mapping[str(v)].connect('toggled', self._seg_toggled, v, callback)
        return box, mapping

    @staticmethod
    def _seg_toggled(widget, value, callback):
        if widget.get_active():
            callback(value)

    def _switch_row(self, label_text, callback, danger=False):
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        sw = Gtk.Switch()
        sw.set_valign(Gtk.Align.CENTER)   # keep natural height; don't stretch to row
        sw.connect('notify::active', lambda _s, _p: callback())
        lbl = Gtk.Label(label=label_text)
        box.pack_start(sw, False, False, 0)
        box.pack_start(lbl, False, False, 0)
        return box, sw

    def _track_min(self, widget, w=None, h=None):
        self._min_reqs.append((widget, w, h))
        widget.set_size_request(self._scaled_int(w) if w else -1,
                                self._scaled_int(h) if h else -1)

    # ── UI construction ───────────────────────────────────────────────────────

    def _build_ui(self):
        # This box is the tab's whole content; the controller packs it into a
        # notebook page rather than directly into the window.
        outer = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        self.content = outer

        self._build_toolbar(outer)

        body = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        body.set_margin_start(8)
        body.set_margin_end(8)
        body.set_margin_top(6)
        body.set_margin_bottom(6)
        outer.pack_start(body, True, True, 0)

        self._main_vpaned = Gtk.Paned(orientation=Gtk.Orientation.VERTICAL)
        self._main_vpaned.set_wide_handle(True)
        body.pack_start(self._main_vpaned, True, True, 0)

        top_hpaned = Gtk.Paned(orientation=Gtk.Orientation.HORIZONTAL)
        top_hpaned.set_wide_handle(True)
        self._main_vpaned.pack1(top_hpaned, resize=True, shrink=False)

        self._build_hex_panel(top_hpaned)
        self._build_right_panel(top_hpaned)

        # Console frame built once, shown on demand.
        self._console_dock_parent = self._main_vpaned
        self._console_frame = self._create_python_console_frame()

        self._build_statusbar(outer)

    def _build_toolbar(self, parent):
        bar = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=4)
        self._class(bar, 'toolbar')
        bar.set_size_request(-1, 54)
        bar.set_margin_start(8)
        bar.set_margin_end(8)
        bar.set_margin_top(6)
        bar.set_margin_bottom(6)
        parent.pack_start(bar, False, False, 0)

        bar.pack_start(self._btn("Open", self.app.open_dialog, 'accent', width=92), False, False, 2)
        bar.pack_start(self._btn("Save Binary As…", self.save_binary, width=130), False, False, 2)
        bar.pack_start(self._sep(), False, False, 8)
        bar.pack_start(self._btn("Save Annot.", self.save_annotations, width=104), False, False, 2)
        bar.pack_start(self._btn("Load Annot.", self.load_annotations, width=104), False, False, 2)
        bar.pack_start(self._sep(), False, False, 8)

        bar.pack_start(self._class(Gtk.Label(label="BPR"), 'muted'), False, False, 4)
        self._bpr_value = 16
        seg, _ = self._segmented(['8', '16', '32'], '16', self._on_bpr_change)
        bar.pack_start(seg, False, False, 4)
        bar.pack_start(self._sep(), False, False, 8)

        edit_box, self._edit_switch = self._switch_row("Hex Edit", self._toggle_edit_mode, danger=True)
        bar.pack_start(edit_box, False, False, 8)
        self._python_btn = self._btn("Python", self._toggle_python_console, width=82)
        bar.pack_start(self._python_btn, False, False, 4)

        # Right side: theme toggle.
        theme_seg, self._appearance_map = self._segmented(
            ['Dark', 'Light'], 'Dark', self._on_appearance_change)
        bar.pack_end(theme_seg, False, False, 8)
        bar.pack_end(self._class(Gtk.Label(label="Theme"), 'muted'), False, False, 2)

    def _build_statusbar(self, parent):
        bar = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL)
        self._class(bar, 'statusbar')
        bar.set_size_request(-1, 28)
        self._status_label = Gtk.Label(label="Open a binary file to begin.", xalign=0.0)
        self._class(self._status_label, 'muted')
        self._status_label.set_margin_start(14)
        bar.pack_start(self._status_label, False, False, 0)
        parent.pack_start(bar, False, False, 0)

    def _set_status(self, text):
        self._status_label.set_text(text)

    def _build_hex_panel(self, paned):
        frame = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        self._class(frame, 'card')
        self._track_min(frame, w=660)
        paned.pack1(frame, resize=True, shrink=False)

        self._hover_label = Gtk.Label(label="  Hover over bytes to inspect", xalign=0.0)
        self._class(self._hover_label, 'muted', 'hover')
        self._hover_label.override_font(self._mono_desc(12))
        self._hover_label.set_margin_start(8)
        self._hover_label.set_margin_end(8)
        self._hover_label.set_margin_top(8)
        self._hover_label.set_margin_bottom(4)
        frame.pack_start(self._hover_label, False, False, 0)

        scroller = Gtk.ScrolledWindow()
        scroller.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scroller.set_margin_start(8)
        scroller.set_margin_end(8)
        scroller.set_margin_bottom(8)
        frame.pack_start(scroller, True, True, 0)

        self.hex_view = Gtk.TextView()
        self.hex_view.set_editable(False)
        self.hex_view.set_cursor_visible(False)
        self.hex_view.set_wrap_mode(Gtk.WrapMode.NONE)
        self.hex_view.set_monospace(True)
        self.hex_view.set_left_margin(6)
        self.hex_view.set_right_margin(6)
        self.hex_buf = self.hex_view.get_buffer()
        scroller.add(self.hex_view)

        self.hex_view.add_events(Gdk.EventMask.BUTTON_PRESS_MASK
                                 | Gdk.EventMask.BUTTON_RELEASE_MASK
                                 | Gdk.EventMask.POINTER_MOTION_MASK)
        self.hex_view.connect('button-press-event', self._on_hex_button_press)
        self.hex_view.connect('button-release-event', self._on_hex_button_release)
        self.hex_view.connect('motion-notify-event', self._on_hex_motion)
        self.hex_view.connect('key-press-event', self._on_hex_key)

        # Overlay tags created in z-order: rangesel < edited < cursor.  Field
        # tags are kept below these by _promote_overlays() after each is made.
        self._tag_rangesel = self.hex_buf.create_tag('rangesel', background='#2d4f78')
        self._tag_edited = self.hex_buf.create_tag('edited', background=EDITED_BG,
                                                   foreground='#ffffff')
        self._tag_cursor = self.hex_buf.create_tag(
            'edit_cursor', background='#ffffff', foreground='#000000',
            font=f"{self.mono_family} Bold 11")

    def _build_right_panel(self, paned):
        frame = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        self._class(frame, 'surface')
        self._track_min(frame, w=400)
        paned.pack2(frame, resize=True, shrink=False)

        self._build_add_form(frame)

        vpaned = Gtk.Paned(orientation=Gtk.Orientation.VERTICAL)
        vpaned.set_wide_handle(True)
        vpaned.set_margin_start(8)
        vpaned.set_margin_end(8)
        vpaned.set_margin_bottom(8)
        frame.pack_start(vpaned, True, True, 0)

        fields_frame = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        self._class(fields_frame, 'card')
        self._track_min(fields_frame, h=130)
        vpaned.pack1(fields_frame, resize=True, shrink=False)

        detail_frame = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        self._class(detail_frame, 'card')
        self._track_min(detail_frame, h=90)
        vpaned.pack2(detail_frame, resize=True, shrink=False)

        self._build_fields_table(fields_frame)
        self._build_action_buttons(fields_frame)
        self._build_detail_pane(detail_frame)

    def _build_add_form(self, parent):
        card = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=2)
        self._class(card, 'card')
        card.set_margin_start(8)
        card.set_margin_end(8)
        card.set_margin_top(8)
        card.set_margin_bottom(8)
        parent.pack_start(card, False, False, 0)

        title = Gtk.Label(label="Add Field", xalign=0.0)
        self._class(title, 'title')
        title.set_margin_start(12)
        title.set_margin_top(10)
        title.set_margin_bottom(6)
        card.pack_start(title, False, False, 0)

        grid = Gtk.Grid(column_spacing=6, row_spacing=4)
        grid.set_margin_start(12)
        grid.set_margin_end(12)
        card.pack_start(grid, False, False, 0)

        def lrow(r, label):
            lbl = Gtk.Label(label=label, xalign=0.0)
            self._class(lbl, 'muted')
            lbl.set_size_request(46, -1)
            grid.attach(lbl, 0, r, 1, 1)
            entry = Gtk.Entry()
            entry.override_font(self._mono_desc(12))
            entry.set_hexpand(True)
            entry.connect('activate', lambda _w: self._submit_field_form())
            grid.attach(entry, 1, r, 3, 1)
            return entry

        self._name_entry = lrow(0, "Name")
        self._start_entry = lrow(1, "Start")
        self._end_entry = lrow(2, "End")
        self._note_entry = lrow(3, "Note")
        self._start_entry.set_text('0x0')
        self._end_entry.set_text('0x0')

        color_lbl = Gtk.Label(label="Color", xalign=0.0)
        self._class(color_lbl, 'muted')
        grid.attach(color_lbl, 0, 4, 1, 1)

        self._palette_frame = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=4)
        grid.attach(self._palette_frame, 1, 4, 3, 1)

        # The "…" picker and the current-colour preview are packed once and stay put;
        # the swatch buttons are (re)built in front of them at a fixed slot count.
        self._pal_btns: list = []
        more = self._btn("…", self._pick_custom_color, width=28, height=22)
        self._palette_frame.pack_start(more, False, False, 6)

        self._swatch = Gtk.Box()
        self._class(self._swatch, 'swatch')
        self._swatch.set_size_request(30, 22)
        self._apply_swatch_color(self._current_color)
        self._palette_frame.pack_start(self._swatch, False, False, 4)

        self._rebuild_palette()

        self._click_hint = Gtk.Label(xalign=0.0)
        self._click_hint.set_margin_start(12)
        self._click_hint.set_margin_top(8)
        card.pack_start(self._click_hint, False, False, 0)
        self._set_hint("Drag in hex view to select a field range", '#ffd93d')

        sub = Gtk.Label(label="Drag to select · Shift+Click to extend · or type offsets",
                        xalign=0.0)
        self._class(sub, 'muted')
        sub.set_margin_start(12)
        card.pack_start(sub, False, False, 0)

        add_btn = self._btn("Add Field   (Enter)", self.add_field, 'accent', height=34)
        add_btn.set_margin_start(12)
        add_btn.set_margin_end(12)
        add_btn.set_margin_top(8)
        card.pack_start(add_btn, False, False, 0)

        edit_bar = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8, homogeneous=True)
        edit_bar.set_margin_start(12)
        edit_bar.set_margin_end(12)
        edit_bar.set_margin_top(4)
        edit_bar.set_margin_bottom(12)
        card.pack_start(edit_bar, False, False, 0)
        self._update_field_btn = self._btn("Update Selected", self.update_field, 'accent', height=30)
        self._update_field_btn.set_sensitive(False)
        edit_bar.pack_start(self._update_field_btn, True, True, 0)
        edit_bar.pack_start(self._btn("New Field", self._reset_field_form, height=30), True, True, 0)

    def _make_swatch_button(self, color):
        b = Gtk.Button()
        self._class(b, 'swatch')
        b.set_size_request(22, 22)
        self._paint_widget_bg(b, color)
        b.connect('clicked', lambda _w, c=color: self._set_color(c))
        return b

    def _ordered_palette(self) -> list[str]:
        """The fixed-length list of colours to display: built-in + custom colours
        sorted by usage (most-used first), capped to PALETTE_SLOTS. Ties keep the
        original order so swatches only move when usage actually differs. The current
        colour is always kept visible (placed last if it would otherwise drop off)."""
        pool = list(PALETTE) + [c for c in self._custom_colors if c not in PALETTE]
        original = {c: i for i, c in enumerate(pool)}
        pool.sort(key=lambda c: (-self._color_usage.get(c, 0), original[c]))
        shown = pool[:PALETTE_SLOTS]
        if self._current_color in pool and self._current_color not in shown:
            shown = shown[:PALETTE_SLOTS - 1] + [self._current_color]
        return shown

    def _rebuild_palette(self):
        """Repopulate the swatch strip in place. Always emits exactly the same number
        of swatches, so the Add-Field pane keeps a constant width and never nudges the
        hex-pane divider."""
        for b in self._pal_btns:
            self._palette_frame.remove(b)
        self._pal_btns = []
        for i, color in enumerate(self._ordered_palette()):
            btn = self._make_swatch_button(color)
            self._palette_frame.pack_start(btn, False, False, 0)
            self._palette_frame.reorder_child(btn, i)   # keep swatches left of "…"/preview
            btn.show()
            self._pal_btns.append(btn)

    def _paint_widget_bg(self, widget, color):
        widget.override_background_color(
            Gtk.StateFlags.NORMAL, self._gdk_rgba(color))

    def _apply_swatch_color(self, color):
        self._paint_widget_bg(self._swatch, color)

    def _build_fields_table(self, parent):
        title = Gtk.Label(label="Defined Fields", xalign=0.0)
        self._class(title, 'title')
        title.set_margin_start(12)
        title.set_margin_top(10)
        title.set_margin_bottom(4)
        parent.pack_start(title, False, False, 0)

        scroller = Gtk.ScrolledWindow()
        scroller.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scroller.set_margin_start(8)
        scroller.set_margin_end(8)
        parent.pack_start(scroller, True, True, 0)

        # Columns: Name, Start, End, Len, Note, bg, fg
        self._store = Gtk.ListStore(str, str, str, str, str, str, str)
        self.tree = Gtk.TreeView(model=self._store)
        self.tree.set_headers_visible(True)
        cols = [('Name', 0, 120), ('Start', 1, 70), ('End', 2, 70),
                ('Len', 3, 55), ('Note', 4, 110)]
        for title_text, idx, width in cols:
            renderer = Gtk.CellRendererText()
            col = Gtk.TreeViewColumn(title_text, renderer, text=idx,
                                     background=5, foreground=6)
            col.set_min_width(width)
            col.set_resizable(True)
            self.tree.append_column(col)
        scroller.add(self.tree)

        self.tree.get_selection().connect('changed', self._on_tree_select)
        self.tree.connect('row-activated', lambda *_: self.scroll_to_field())
        self.tree.connect('key-press-event', self._on_tree_key)

    def _build_action_buttons(self, parent):
        bar = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        bar.set_margin_start(8)
        bar.set_margin_end(8)
        bar.set_margin_top(2)
        bar.set_margin_bottom(10)
        parent.pack_start(bar, False, False, 0)
        bar.pack_start(self._btn("Delete  (Del)", self.delete_field, 'danger', width=112, height=30), False, False, 3)
        bar.pack_start(self._btn("Jump to Field", self.scroll_to_field, width=112, height=30), False, False, 3)
        bar.pack_start(self._btn("Clear All", self.clear_all, width=88, height=30), False, False, 3)

    def _build_detail_pane(self, parent):
        title = Gtk.Label(label="Inspector", xalign=0.0)
        self._class(title, 'title')
        title.set_margin_start(12)
        title.set_margin_top(10)
        title.set_margin_bottom(2)
        parent.pack_start(title, False, False, 0)

        controls = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        controls.set_margin_start(10)
        controls.set_margin_end(10)
        controls.set_margin_bottom(4)
        parent.pack_start(controls, False, False, 0)

        self._fmt_value = 'Integer'
        self._fmt_combo = Gtk.ComboBoxText()
        for f in self._INSPECT_FORMATS:
            self._fmt_combo.append_text(f)
        self._fmt_combo.set_active(0)
        self._fmt_combo.connect('changed', self._on_fmt_change)
        controls.pack_start(self._fmt_combo, False, False, 0)

        self._endian_value = 'LE'
        endian_seg, _ = self._segmented(['LE', 'BE'], 'LE', self._on_endian_change)
        controls.pack_start(endian_seg, False, False, 6)

        signed_box, self._signed_sw = self._switch_row("Signed", self._refresh_inspector)
        controls.pack_start(signed_box, False, False, 6)

        scroller = Gtk.ScrolledWindow()
        scroller.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scroller.set_margin_start(8)
        scroller.set_margin_end(8)
        scroller.set_margin_bottom(8)
        parent.pack_start(scroller, True, True, 0)

        self._detail_view = Gtk.TextView()
        self._detail_view.set_editable(False)
        self._detail_view.set_cursor_visible(False)
        self._detail_view.set_wrap_mode(Gtk.WrapMode.NONE)
        self._detail_view.set_monospace(True)
        self._detail_buf = self._detail_view.get_buffer()
        scroller.add(self._detail_view)
        self._clear_detail()

    # ── Python console UI ─────────────────────────────────────────────────────

    def _create_python_console_frame(self):
        frame = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=0)
        self._class(frame, 'card')

        header = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        header.set_margin_start(10)
        header.set_margin_end(10)
        header.set_margin_top(8)
        header.set_margin_bottom(4)
        frame.pack_start(header, False, False, 0)

        # An event box makes the header draggable for pop-out.
        title_evbox = Gtk.EventBox()
        title_evbox.add_events(Gdk.EventMask.BUTTON_PRESS_MASK
                               | Gdk.EventMask.BUTTON_RELEASE_MASK
                               | Gdk.EventMask.POINTER_MOTION_MASK)
        title_lbl = Gtk.Label(label="Python Console")
        self._class(title_lbl, 'title')
        title_evbox.add(title_lbl)
        title_evbox.connect('button-press-event', self._console_drag_start)
        title_evbox.connect('motion-notify-event', self._console_drag_motion)
        title_evbox.connect('button-release-event', self._console_drag_release)
        header.pack_start(title_evbox, False, False, 0)

        hide_btn = self._btn("Hide", self._hide_python_console, width=68, height=28)
        header.pack_end(hide_btn, False, False, 0)
        # Pop Out / Dock: handler swapped at runtime, so create with no command
        # and attach exclusively through _console_pop_btn_set (avoids a stale
        # second 'clicked' handler firing alongside the current one).
        self._console_pop_btn = self._btn("Pop Out", None, width=78, height=28)
        self._console_pop_btn_set(self._float_python_console)
        header.pack_end(self._console_pop_btn, False, False, 6)
        header.pack_end(self._btn("Clear", self._clear_console, width=68, height=28), False, False, 6)

        scroller = Gtk.ScrolledWindow()
        scroller.set_policy(Gtk.PolicyType.AUTOMATIC, Gtk.PolicyType.AUTOMATIC)
        scroller.set_margin_start(8)
        scroller.set_margin_end(8)
        frame.pack_start(scroller, True, True, 0)

        self._console_view = Gtk.TextView()
        self._console_view.set_editable(False)
        self._console_view.set_cursor_visible(False)
        self._console_view.set_wrap_mode(Gtk.WrapMode.WORD)
        self._console_view.set_monospace(True)
        self._console_view.set_size_request(-1, self._scaled_int(140))
        self._console_buf = self._console_view.get_buffer()
        scroller.add(self._console_view)

        input_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        input_row.set_margin_start(8)
        input_row.set_margin_end(8)
        input_row.set_margin_top(2)
        input_row.set_margin_bottom(8)
        frame.pack_start(input_row, False, False, 0)

        self._console_prompt = Gtk.Label(label='...' if self._console_more else '>>>')
        self._class(self._console_prompt, 'title')
        self._console_prompt.override_font(self._mono_desc(12))
        self._console_prompt.set_size_request(32, -1)
        input_row.pack_start(self._console_prompt, False, False, 2)

        self._console_input = Gtk.Entry()
        self._console_input.override_font(self._mono_desc(12))
        self._console_input.connect('activate', self._execute_console_line)
        self._console_input.connect('key-press-event', self._console_input_key)
        input_row.pack_start(self._console_input, True, True, 0)

        if not self._console_output_cache:
            self._console_output_cache = (
                "Trusted local Python console. Imports and filesystem access are allowed.\n"
                "Scripts run in the UI process; long-running code can block the app.\n"
                "Use buf, app, refresh(), write(), insert(), delete(), hexdump(), len_buf().\n\n")
        self._console_buf.set_text(self._console_output_cache)
        self._console_scroll_end()
        return frame

    # ── Keyboard bindings ─────────────────────────────────────────────────────
    # Window-level shortcuts are handled once by the controller (MultiFileApp._on_key)
    # and routed to the active tab. Per-widget handlers below stay tab-local.

    def _on_tree_key(self, _widget, event):
        if event.keyval == Gdk.KEY_Delete:
            self.delete_field()
            return True
        return False

    # ── Zoom ──────────────────────────────────────────────────────────────────

    def _set_ui_scale(self, scale: float):
        scale = round(max(ZOOM_MIN, min(ZOOM_MAX, scale)), 2)
        if scale == self._ui_scale:
            return
        self._ui_scale = scale
        self._retheme_native(self._mode)
        for widget, w, h in self._min_reqs:
            widget.set_size_request(self._scaled_int(w) if w else -1,
                                    self._scaled_int(h) if h else -1)
        if self.data is not None:
            self._render()
        else:
            self._draw_selection()
            self._draw_edit_cursor()
        self._set_status(f"Scale: {int(round(scale * 100))}%")

    # ── Embedded Python console ───────────────────────────────────────────────

    def _init_console_namespace(self):
        ns = self._console.locals
        ns.update({
            'app': self,
            'buf': self.data,
            'refresh': self._console_refresh,
            'write': self._console_write,
            'insert': self._console_insert,
            'delete': self._console_delete,
            'hexdump': self._console_hexdump,
            'len_buf': self._console_len_buf,
        })

    def _sync_console_buffer(self):
        self._console.locals['buf'] = self.data

    def _toggle_python_console(self):
        if self._console_visible or self._console_floating:
            self._hide_python_console()
        else:
            self._show_python_console()

    def _show_python_console(self):
        if self._console_floating:
            self._console_input.grab_focus()
            return
        if not self._console_visible:
            self._main_vpaned.pack2(self._console_frame, resize=False, shrink=False)
            self._console_frame.show_all()
            self._console_visible = True
            self._python_btn.set_label("Python On")
            self._console_pop_btn.set_label("Pop Out")
            self._console_pop_btn_set(self._float_python_console)
        self._console_input.grab_focus()

    def _hide_python_console(self):
        if self._console_visible:
            self._main_vpaned.remove(self._console_frame)
            self._console_visible = False
        if self._console_floating:
            self._dock_python_console(show=False)
        self._python_btn.set_label("Python")

    def _console_pop_btn_set(self, cmd):
        # Reconnect the Pop Out / Dock button's action.
        if getattr(self, '_console_pop_handler', None) is not None:
            self._console_pop_btn.disconnect(self._console_pop_handler)
        self._console_pop_handler = self._console_pop_btn.connect(
            'clicked', lambda _w: cmd())

    def _float_python_console(self):
        if self._console_floating:
            return
        if self._console_visible:
            self._main_vpaned.remove(self._console_frame)
            self._console_visible = False

        self._console_window = Gtk.Window(title="Python Console")
        self._console_window.set_transient_for(self.root)
        self._console_window.set_default_size(900, 360)
        self._console_window.set_size_request(520, 220)
        self._console_window.connect('delete-event', self._on_console_window_close)
        self._console_window.add(self._console_frame)
        self._console_window.show_all()
        self._console_floating = True
        self._python_btn.set_label("Python Out")
        self._console_pop_btn.set_label("Dock")
        self._console_pop_btn_set(self._dock_python_console)
        self._console_input.grab_focus()

    def _on_console_window_close(self, *_):
        self._hide_python_console()
        return True   # we handle destruction ourselves

    def _dock_python_console(self, show: bool = True):
        if self._console_floating:
            if self._console_window is not None:
                self._console_window.remove(self._console_frame)
                self._console_window.destroy()
            self._console_window = None
            self._console_floating = False
        self._console_pop_btn.set_label("Pop Out")
        self._console_pop_btn_set(self._float_python_console)
        if show:
            self._show_python_console()

    def _console_drag_start(self, _widget, event):
        self._console_drag_origin = (event.x_root, event.y_root)
        self._console_dragging = False
        return True

    def _console_drag_motion(self, _widget, event):
        if self._console_drag_origin is None:
            return True
        ox, oy = self._console_drag_origin
        dx = event.x_root - ox
        dy = event.y_root - oy
        if not self._console_dragging and abs(dx) + abs(dy) < 16:
            return True
        self._console_dragging = True
        if not self._console_floating:
            self._float_python_console()
        if self._console_window is not None:
            self._console_window.move(int(event.x_root - 80), int(event.y_root - 18))
        return True

    def _console_drag_release(self, _widget, event):
        if self._console_dragging and self._console_floating:
            rx, ry = self.root.get_position()
            rw, rh = self.root.get_size()
            if rx <= event.x_root <= rx + rw and ry <= event.y_root <= ry + rh:
                self._dock_python_console()
        self._console_drag_origin = None
        self._console_dragging = False
        return True

    def _clear_console(self):
        self._console_output_cache = ""
        self._console_buf.set_text("")

    def _console_scroll_end(self):
        end = self._console_buf.get_end_iter()
        self._console_view.scroll_to_iter(end, 0.0, False, 0.0, 0.0)

    def _append_console(self, text: str):
        self._console_output_cache += text
        self._console_buf.insert(self._console_buf.get_end_iter(), text)
        self._console_scroll_end()

    def _console_command_needs_snapshot(self, line: str) -> bool:
        stripped = line.lstrip()
        if not stripped or stripped.startswith('#'):
            return False
        return 'buf' in line or 'app.' in line

    def _mark_console_dirty(self, start: int = 0, end: int | None = None):
        self._console_dirty = True
        if self.data is None:
            return
        if end is None:
            end = start
        if self.data:
            start = max(0, min(int(start), len(self.data) - 1))
            end = max(start, min(int(end), len(self.data) - 1))
            self._console_changed_ranges.append((start, end))

    def _console_input_key(self, _widget, event):
        if event.keyval == Gdk.KEY_Up:
            return self._console_history_prev()
        if event.keyval == Gdk.KEY_Down:
            return self._console_history_next()
        return False

    def _console_history_prev(self):
        if not self._console_history:
            return True
        if self._console_history_index is None:
            self._console_history_index = len(self._console_history) - 1
        else:
            self._console_history_index = max(0, self._console_history_index - 1)
        self._console_input.set_text(self._console_history[self._console_history_index])
        self._console_input.set_position(-1)
        return True

    def _console_history_next(self):
        if self._console_history_index is None:
            return True
        self._console_history_index += 1
        if self._console_history_index >= len(self._console_history):
            self._console_history_index = None
            self._console_input.set_text('')
        else:
            self._console_input.set_text(self._console_history[self._console_history_index])
        self._console_input.set_position(-1)
        return True

    def _execute_console_line(self, _widget=None):
        line = self._console_input.get_text()
        prompt = '...' if self._console_more else '>>>'
        self._append_console(f"{prompt} {line}\n")
        if line.strip():
            self._console_history.append(line)
        self._console_history_index = None
        self._console_input.set_text('')

        before = (
            bytes(self.data)
            if self.data is not None and self._console_command_needs_snapshot(line)
            else None
        )
        before_len = len(before) if before is not None else (len(self.data) if self.data is not None else 0)
        self._console_dirty = False
        self._console_changed_ranges.clear()
        self._sync_console_buffer()
        stdout = io.StringIO()
        with contextlib.redirect_stdout(stdout), contextlib.redirect_stderr(stdout):
            self._console_more = self._console.push(line)
        out = stdout.getvalue()
        if out:
            self._append_console(out)
        self._console_prompt.set_text('...' if self._console_more else '>>>')
        if not self._console_more:
            self._sync_console_buffer()
            self._after_console_command(before, before_len)

    def _after_console_command(self, before: bytes | None, before_len: int = 0):
        if self.data is None:
            return
        if before is None and not self._console_dirty and len(self.data) == before_len:
            return
        after_len = len(self.data)
        if before is not None:
            after = bytes(self.data)
            if before == after:
                return
            first = 0
            limit = min(len(before), len(after))
            while first < limit and before[first] == after[first]:
                first += 1
            if len(before) == len(after):
                changed = sum(1 for i in range(first, len(after)) if before[i] != after[i])
            else:
                changed = abs(len(after) - len(before))
            for i in range(first, len(after)):
                if i >= len(before) or before[i] != after[i]:
                    self._edited.add(i)
        elif self._console_changed_ranges:
            first = min(start for start, _end in self._console_changed_ranges)
            changed = sum(end - start + 1 for start, end in self._console_changed_ranges)
            for start, end in self._console_changed_ranges:
                self._edited.update(range(start, end + 1))
        else:
            first = 0
            changed = abs(after_len - before_len)
            self._edited.update(range(first, min(after_len, first + 4096)))
        self._modified = True
        self._update_title()
        self._render()
        self._refresh_inspector()
        self._set_status(
            f"Python console changed buffer: {changed} byte(s), size {after_len}")

    def _require_console_buffer(self) -> bytearray:
        if self.data is None:
            raise RuntimeError("Open a binary file first; no buffer is loaded.")
        return self.data

    def _coerce_console_bytes(self, data) -> bytes:
        if isinstance(data, int):
            if not 0 <= data <= 255:
                raise ValueError("Integer byte value must be between 0 and 255.")
            return bytes([data])
        if isinstance(data, str):
            raise TypeError("Use bytes, bytearray, int, or an iterable of ints; strings are ambiguous.")
        return bytes(data)

    def _console_write(self, offset: int, data):
        buf = self._require_console_buffer()
        payload = self._coerce_console_bytes(data)
        offset = int(offset)
        if offset < 0 or offset + len(payload) > len(buf):
            raise IndexError("write() range is outside the loaded buffer.")
        buf[offset:offset + len(payload)] = payload
        if payload:
            self._mark_console_dirty(offset, offset + len(payload) - 1)
        return len(payload)

    def _console_insert(self, offset: int, data):
        buf = self._require_console_buffer()
        payload = self._coerce_console_bytes(data)
        offset = int(offset)
        if offset < 0 or offset > len(buf):
            raise IndexError("insert() offset is outside the loaded buffer.")
        buf[offset:offset] = payload
        if payload:
            self._mark_console_dirty(offset, offset + len(payload) - 1)
        return len(payload)

    def _console_delete(self, start: int, end: int | None = None):
        buf = self._require_console_buffer()
        start = int(start)
        end = start if end is None else int(end)
        if start > end:
            start, end = end, start
        if start < 0 or end >= len(buf):
            raise IndexError("delete() range is outside the loaded buffer.")
        count = end - start + 1
        del buf[start:end + 1]
        self._mark_console_dirty(start, min(start, len(buf) - 1))
        return count

    def _console_len_buf(self) -> int:
        return len(self._require_console_buffer())

    def _console_hexdump(self, start: int = 0, length: int = 256) -> str:
        buf = self._require_console_buffer()
        start = max(0, int(start))
        length = max(0, int(length))
        end = min(len(buf), start + length)
        lines = []
        for off in range(start, end, 16):
            chunk = buf[off:off + 16]
            h = ' '.join(f'{b:02X}' for b in chunk)
            a = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
            lines.append(f"{off:08X}: {h:<48} |{a}|")
        return '\n'.join(lines)

    def _console_refresh(self):
        self._sync_console_buffer()
        if self.data is not None:
            self._render()
            self._refresh_inspector()
        return len(self.data) if self.data is not None else 0

    # ── Appearance ────────────────────────────────────────────────────────────

    def _on_appearance_change(self, choice: str):
        # Theme is global: let the controller apply it to every tab and keep the
        # per-tab toggles in sync. The _syncing guard suppresses the echo when the
        # controller programmatically sets this tab's segmented control.
        if self.app._syncing_theme:
            return
        self.app.set_theme(choice.lower())

    def _on_bpr_change(self, value: str):
        self._bpr_value = int(value)
        self._rerender()

    def _on_endian_change(self, value: str):
        self._endian_value = value
        self._refresh_inspector()

    def _on_fmt_change(self, _combo):
        self._fmt_value = self._fmt_combo.get_active_text() or 'Integer'
        self._refresh_inspector()

    # ── Color helpers ─────────────────────────────────────────────────────────

    def _set_color(self, color: str):
        self._current_color = color
        self._apply_swatch_color(color)

    def _pick_custom_color(self):
        dlg = Gtk.ColorChooserDialog(title="Pick Field Color", transient_for=self.root)
        rgba = Gdk.RGBA()
        rgba.parse(self._current_color)
        dlg.set_rgba(rgba)
        if dlg.run() == Gtk.ResponseType.OK:
            color = _rgba_to_hex(dlg.get_rgba())
            self._set_color(color)              # select first so it stays pinned visible
            self._remember_custom_color(color)
        dlg.destroy()

    def _remember_custom_color(self, color: str):
        color = color.lower()
        if color in [c.lower() for c in PALETTE] or \
           color in [c.lower() for c in self._custom_colors]:
            self._rebuild_palette()
            return
        self._custom_colors.append(color)
        # Cap the custom pool: evict the least-used existing custom (never the new one).
        if len(self._custom_colors) > MAX_CUSTOM_COLORS:
            victim = min((c for c in self._custom_colors if c != color),
                         key=lambda c: self._color_usage.get(c, 0))
            self._custom_colors.remove(victim)
            self._color_usage.pop(victim, None)
        self._rebuild_palette()

    # ── Message / file dialogs ────────────────────────────────────────────────

    def _message(self, kind, title, text, parent=None):
        dlg = Gtk.MessageDialog(
            transient_for=parent or self.root, modal=True,
            message_type=kind, buttons=Gtk.ButtonsType.OK, text=title)
        dlg.format_secondary_text(text)
        dlg.run()
        dlg.destroy()

    def _error(self, title, text, parent=None):
        self._message(Gtk.MessageType.ERROR, title, text, parent)

    def _warn(self, title, text):
        self._message(Gtk.MessageType.WARNING, title, text)

    def _info(self, title, text):
        self._message(Gtk.MessageType.INFO, title, text)

    def _ask_yes_no(self, title, text) -> bool:
        dlg = Gtk.MessageDialog(
            transient_for=self.root, modal=True,
            message_type=Gtk.MessageType.QUESTION,
            buttons=Gtk.ButtonsType.YES_NO, text=title)
        dlg.format_secondary_text(text)
        resp = dlg.run()
        dlg.destroy()
        return resp == Gtk.ResponseType.YES

    def _file_dialog(self, title, action, filters, initial=None):
        if action == Gtk.FileChooserAction.SAVE:
            ok_label = "Save"
        else:
            ok_label = "Open"
        dlg = Gtk.FileChooserDialog(title=title, transient_for=self.root, action=action)
        dlg.add_buttons("Cancel", Gtk.ResponseType.CANCEL, ok_label, Gtk.ResponseType.OK)
        if action == Gtk.FileChooserAction.SAVE:
            dlg.set_do_overwrite_confirmation(True)
            if initial:
                dlg.set_current_name(initial)
        for name, patterns in filters:
            ff = Gtk.FileFilter()
            ff.set_name(name)
            for pat in patterns:
                ff.add_pattern(pat)
            dlg.add_filter(ff)
        path = None
        if dlg.run() == Gtk.ResponseType.OK:
            path = dlg.get_filename()
        dlg.destroy()
        return path

    # ── File I/O ──────────────────────────────────────────────────────────────

    def is_pristine(self) -> bool:
        """True if this tab has never had a file loaded and carries no work —
        safe for the controller to reuse instead of spawning a fresh tab."""
        return self.data is None and not self.fields

    def load_path(self, path: str):
        """Load `path` into this tab. The Open chooser lives on the controller
        (MultiFileApp.open_dialog), which spawns a fresh tab per file."""
        try:
            with open(path, 'rb') as f:
                self.data = bytearray(f.read())
            self._sync_console_buffer()
            self.filepath = path
            self._modified = False
            self._edited.clear()
            self._clear_selection()
            self._inspect_mode = None
            self._clear_detail()
            self._update_title()
            sz = len(self.data)
            self._set_status(f"{os.path.basename(path)}  |  {sz} bytes  ({hex(sz)})")
            self._render()
        except Exception as exc:
            self._error("Open Error", str(exc))

    def save_annotations(self):
        if not self.fields:
            self._info("Nothing to save", "No fields defined yet.")
            return
        default = (os.path.basename(self.filepath) if self.filepath else "annotations")
        path = self._file_dialog(
            "Save Annotations", Gtk.FileChooserAction.SAVE,
            [("JSON", ["*.json"])], initial=f"{default}.fields.json")
        if not path:
            return
        if not path.lower().endswith('.json'):
            path += '.json'
        with open(path, 'w') as f:
            json.dump({
                'filepath': self.filepath,
                'fields': self.fields,
                'custom_colors': self._custom_colors,
            }, f, indent=2)
        self._set_status(f"Saved {len(self.fields)} field(s) → {os.path.basename(path)}")

    def load_annotations(self):
        path = self._file_dialog(
            "Load Annotations", Gtk.FileChooserAction.OPEN,
            [("JSON", ["*.json"]), ("All files", ["*"])])
        if not path:
            return
        try:
            with open(path) as f:
                saved = json.load(f)
        except Exception as exc:
            self._error("Load Error", str(exc))
            return

        self.fields = saved.get('fields', [])
        for color in saved.get('custom_colors', []):
            self._remember_custom_color(color)
        for fld in self.fields:
            color = fld.get('color')
            if color:
                self._remember_custom_color(color)
        self._next_id = max((fld['id'] for fld in self.fields), default=-1) + 1
        self._editing_field_id = None
        self._update_field_btn.set_sensitive(False)
        self._rebuild_tree()
        if self.data:
            self._render()
        self._set_status(f"Loaded {len(self.fields)} field(s) from {os.path.basename(path)}")

    def save_binary(self):
        if self.data is None:
            self._info("No Data", "Open a binary file first.")
            return
        if self.filepath:
            stem, ext = os.path.splitext(os.path.basename(self.filepath))
        else:
            stem, ext = "output", ""
        path = self._file_dialog(
            "Save Binary As", Gtk.FileChooserAction.SAVE,
            [("All files", ["*"]), ("Binary", ["*.bin"]), ("Raw", ["*.raw"])],
            initial=f"{stem}_edited{ext}")
        if not path:
            return
        try:
            with open(path, 'wb') as f:
                f.write(bytes(self.data))
            self._modified = False
            self._update_title()
            self._set_status(f"Binary saved → {os.path.basename(path)}")
        except Exception as exc:
            self._error("Save Error", str(exc))

    def title_text(self) -> str:
        fname = os.path.basename(self.filepath) if self.filepath else ""
        mod = "  [modified]" if self._modified else ""
        return f"Binary Field Annotator  {fname}{mod}".rstrip()

    def tab_label_text(self) -> str:
        name = os.path.basename(self.filepath) if self.filepath else "Untitled"
        return f"{name}{' •' if self._modified else ''}"

    def _update_title(self):
        # Drives the shared window title (only when this tab is active) and this
        # tab's label, both via the controller.
        self.app.refresh_titles(self)

    # ── Hex rendering ─────────────────────────────────────────────────────────

    @property
    def bpr(self) -> int:
        return self._bpr_value

    def _rerender(self):
        if self.data is not None:
            self._render()

    def _iter(self, line: int, col: int) -> "Gtk.TextIter":
        return self.hex_buf.get_iter_at_line_offset(line, col)

    def _promote_overlays(self):
        """Keep the overlay tags above all field tags (cursor on top)."""
        table = self.hex_buf.get_tag_table()
        top = table.get_size() - 1
        # Priority lives on the tag in GTK3; each call lifts that tag to `top`
        # and shifts the rest down, so the last set ends up highest.
        self._tag_rangesel.set_priority(top)
        self._tag_edited.set_priority(top)
        self._tag_cursor.set_priority(top)

    def _render(self):
        bpr = self.bpr
        lines = []
        for i in range(0, len(self.data), bpr):
            chunk = self.data[i:i + bpr]
            h = ''.join(f' {b:02X} ' for b in chunk)
            a = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
            lines.append(f"{i:08X}  {h:<{bpr * HEX_CELL_COLS}} |{a}|")

        self.hex_buf.set_text('\n'.join(lines))   # clears all applied tags
        self._apply_all_tags()
        self._apply_edited_tags()
        self._draw_selection()
        self._draw_edit_cursor()

    def _apply_all_tags(self):
        for fld in self.fields:
            self._apply_tag(fld)

    def _field_tag(self, fid: int) -> "Gtk.TextTag":
        tag = self._field_tags.get(fid)
        if tag is None:
            tag = self.hex_buf.create_tag(f"f:{fid}")
            self._field_tags[fid] = tag
            self._promote_overlays()   # keep overlays above this new field tag
        return tag

    def _tag_range(self, tag: "Gtk.TextTag", start: int, end: int):
        """apply_tag over the hex + ascii cells spanning byte offsets [start, end]."""
        bpr = self.bpr
        ascii_base = OFFSET_COLS + bpr * HEX_CELL_COLS + 2
        for row in range(start // bpr, end // bpr + 1):
            row_base = row * bpr
            col_start = max(start, row_base) - row_base
            col_end = min(end, row_base + bpr - 1) - row_base
            line = row

            hc_s = OFFSET_COLS + col_start * HEX_CELL_COLS
            hc_e = OFFSET_COLS + (col_end + 1) * HEX_CELL_COLS
            ac_s = ascii_base + col_start
            ac_e = ascii_base + col_end + 1

            self.hex_buf.apply_tag(tag, self._iter(line, hc_s), self._iter(line, hc_e))
            self.hex_buf.apply_tag(tag, self._iter(line, ac_s), self._iter(line, ac_e))

    def _apply_tag(self, fld: dict):
        if self.data is None:
            return
        bg = fld['color']
        start = fld['start']
        end = min(fld['end'], len(self.data) - 1)
        tag = self._field_tag(fld['id'])
        tag.set_property('background', bg)
        tag.set_property('foreground', _contrast_fg(bg))
        self._tag_range(tag, start, end)

    # ── Hex view interaction ──────────────────────────────────────────────────

    def _click_to_offset(self, event) -> int | None:
        if self.data is None:
            return None
        bx, by = self.hex_view.window_to_buffer_coords(
            Gtk.TextWindowType.WIDGET, int(event.x), int(event.y))
        res = self.hex_view.get_iter_at_location(bx, by)
        if isinstance(res, tuple):
            ok, it = res
        else:
            ok, it = True, res
        if it is None:
            return None
        line = it.get_line()
        col = it.get_line_offset()
        bpr = self.bpr
        base = line * bpr

        hz_end = OFFSET_COLS + bpr * HEX_CELL_COLS
        az_start = OFFSET_COLS + bpr * HEX_CELL_COLS + 2
        az_end = az_start + bpr

        if OFFSET_COLS <= col < hz_end:
            byte_col = (col - OFFSET_COLS) // HEX_CELL_COLS
        elif az_start <= col < az_end:
            byte_col = col - az_start
        else:
            return None

        off = base + byte_col
        return off if 0 <= off < len(self.data) else None

    def _set_selection(self, a: int, b: int):
        lo, hi = (a, b) if a <= b else (b, a)
        self._sel_range = (lo, hi)
        self._start_entry.set_text(hex(lo))
        self._end_entry.set_text(hex(hi))
        self._draw_selection()
        self._inspect_mode = 'sel'
        self._refresh_inspector()

    def _clear_selection(self):
        self._sel_range = None
        self._drag_anchor = None
        self._dragging = False
        self.hex_buf.remove_tag(self._tag_rangesel,
                                self.hex_buf.get_start_iter(),
                                self.hex_buf.get_end_iter())
        if self._inspect_mode == 'sel':
            self._inspect_mode = None
            self._clear_detail()

    def _draw_selection(self):
        self.hex_buf.remove_tag(self._tag_rangesel,
                                self.hex_buf.get_start_iter(),
                                self.hex_buf.get_end_iter())
        if self._sel_range is None or self.data is None:
            return
        lo, hi = self._sel_range
        lo = max(0, lo)
        hi = min(hi, len(self.data) - 1)
        if lo > hi:
            return
        self._tag_range(self._tag_rangesel, lo, hi)

    def _on_hex_button_press(self, _widget, event):
        if event.button == 3:
            return self._on_hex_right_click(event)
        if event.button != 1:
            return False
        shift = bool(event.state & Gdk.ModifierType.SHIFT_MASK)
        if shift:
            return self._on_hex_shift_click(event)
        return self._on_hex_press(event)

    def _on_hex_button_release(self, _widget, event):
        if event.button != 1:
            return False
        return self._on_hex_release(event)

    def _on_hex_motion(self, _widget, event):
        if event.state & Gdk.ModifierType.BUTTON1_MASK:
            return self._on_hex_drag(event)
        self._on_hex_hover(event)
        return False

    def _on_hex_press(self, event):
        off = self._click_to_offset(event)
        if off is None:
            if not self._edit_mode:
                self._clear_selection()
                self._set_hint(
                    "Drag in hex view to select a field range  ·  Shift+Click to extend",
                    '#ffd93d')
            return True
        if self._edit_mode:
            self._set_edit_cursor(off)
            self.hex_view.grab_focus()
            return True
        self._drag_anchor = off
        self._dragging = False
        self._set_selection(off, off)
        self._set_hint(f"Selecting… start={hex(off)}  (drag to extend)", '#ffd93d')
        return True

    def _on_hex_drag(self, event):
        if self._edit_mode or self._drag_anchor is None:
            return False
        off = self._click_to_offset(event)
        if off is None:
            return True
        self._dragging = True
        self._set_selection(self._drag_anchor, off)
        lo, hi = self._sel_range
        self._set_hint(f"Selecting… {hex(lo)}–{hex(hi)}  ({hi - lo + 1} bytes)", '#ff6b6b')
        return True

    def _on_hex_release(self, event):
        if self._edit_mode or self._drag_anchor is None:
            return False
        off = self._click_to_offset(event)
        if off is not None:
            self._set_selection(self._drag_anchor, off)
        if self._sel_range is not None:
            lo, hi = self._sel_range
            n = hi - lo + 1
            self._set_hint(
                f"Selected {hex(lo)}–{hex(hi)}  ({n} byte{'s' if n != 1 else ''}) "
                f"— name it, then Add Field", '#6bcb77')
        self._drag_anchor = None
        self._dragging = False
        return True

    def _on_hex_shift_click(self, event):
        if self._edit_mode:
            return self._on_hex_press(event)
        off = self._click_to_offset(event)
        if off is None:
            return True
        anchor = self._sel_range[0] if self._sel_range is not None else off
        self._drag_anchor = anchor
        self._set_selection(anchor, off)
        lo, hi = self._sel_range
        self._set_hint(f"Extended to {hex(lo)}–{hex(hi)}  ({hi - lo + 1} bytes)", '#6bcb77')
        return True

    def _on_hex_hover(self, event):
        off = self._click_to_offset(event)
        if off is None or self.data is None:
            return
        b = self.data[off]
        names = [f['name'] for f in self.fields if f['start'] <= off <= f['end']]
        field_str = f"   [{', '.join(names)}]" if names else ""
        self._hover_label.set_text(
            f"  Off: {hex(off)} ({off})   "
            f"Byte: 0x{b:02X} ({b:3d}) "
            f"'{chr(b) if 32 <= b < 127 else '.'}'"
            f"{field_str}")

    def _set_hint(self, text, color):
        safe = GLib.markup_escape_text(text)
        self._click_hint.set_markup(f'<span foreground="{color}">{safe}</span>')

    # ── Inline hex editing ────────────────────────────────────────────────────

    def _toggle_edit_mode(self):
        self._edit_mode = self._edit_switch.get_active()
        if self._edit_mode:
            self._clear_selection()
            self._set_hint("HEX EDIT: click a byte, type 2 hex digits to overwrite", '#ff6b6b')
            self._set_status(
                "Hex Edit mode — click to position cursor, type hex digits, "
                "arrows to navigate, Esc to exit")
        else:
            self._set_edit_cursor(None)
            self._set_hint(
                "Drag in hex view to select a field range  ·  Shift+Click to extend",
                '#ffd93d')
            self._set_status("Hex Edit mode off")

    def _set_edit_cursor(self, offset: int | None):
        self._edit_cursor = offset
        self._edit_nibble = 0
        self._draw_edit_cursor()
        if offset is not None and self.data is not None:
            b = self.data[offset]
            self._set_status(
                f"Edit @ {hex(offset)}  current: 0x{b:02X} ({b})  — type high nibble")

    def _scroll_hex_to(self, line, col):
        self.hex_view.scroll_to_iter(self._iter(line, col), 0.1, False, 0.0, 0.0)

    def _draw_edit_cursor(self):
        self.hex_buf.remove_tag(self._tag_cursor,
                                self.hex_buf.get_start_iter(),
                                self.hex_buf.get_end_iter())
        if self._edit_cursor is None or self.data is None or not self._edit_mode:
            return

        off = self._edit_cursor
        bpr = self.bpr
        row = off // bpr
        col = off % bpr
        ascii_base = OFFSET_COLS + bpr * HEX_CELL_COLS + 2

        hc_start = OFFSET_COLS + col * HEX_CELL_COLS + 1
        if self._edit_nibble == 0:
            hc_s, hc_e = hc_start, hc_start + 2
        else:
            hc_s, hc_e = hc_start + 1, hc_start + 2

        ac_s = ascii_base + col
        ac_e = ac_s + 1

        self.hex_buf.apply_tag(self._tag_cursor, self._iter(row, hc_s), self._iter(row, hc_e))
        self.hex_buf.apply_tag(self._tag_cursor, self._iter(row, ac_s), self._iter(row, ac_e))
        self._scroll_hex_to(row, hc_start)

    def _move_edit_cursor(self, delta: int):
        if self._edit_cursor is None or self.data is None:
            return
        new = self._edit_cursor + delta
        if 0 <= new < len(self.data):
            self._edit_cursor = new
            self._edit_nibble = 0
            b = self.data[new]
            self._set_status(
                f"Edit @ {hex(new)}  current: 0x{b:02X} ({b})  — type high nibble")
        self._draw_edit_cursor()

    def _byte_indices(self, off: int) -> tuple[int, int, int]:
        """Return (row, hex_start_col, ascii_col) for a byte offset (0-based row)."""
        bpr = self.bpr
        row = off // bpr
        col = off % bpr
        ascii_base = OFFSET_COLS + bpr * HEX_CELL_COLS + 2
        return row, OFFSET_COLS + col * HEX_CELL_COLS + 1, ascii_base + col

    def _tag_byte(self, tag: "Gtk.TextTag", off: int):
        row, hc_s, ac_s = self._byte_indices(off)
        self.hex_buf.apply_tag(tag, self._iter(row, hc_s - 1), self._iter(row, hc_s + 3))
        self.hex_buf.apply_tag(tag, self._iter(row, ac_s), self._iter(row, ac_s + 1))

    def _apply_edited_tags(self):
        self.hex_buf.remove_tag(self._tag_edited,
                                self.hex_buf.get_start_iter(),
                                self.hex_buf.get_end_iter())
        if self.data is None:
            return
        for off in self._edited:
            if 0 <= off < len(self.data):
                self._tag_byte(self._tag_edited, off)

    def _replace_text(self, line, c1, c2, text):
        s = self._iter(line, c1)
        e = self._iter(line, c2)
        self.hex_buf.delete(s, e)
        self.hex_buf.insert(self._iter(line, c1), text)

    def _write_byte(self, off: int, value: int):
        """Patch one byte and repaint only its cell — no full re-render."""
        self.data[off] = value
        self._edited.add(off)
        self._modified = True
        self._update_title()

        row, hc_s, ac_s = self._byte_indices(off)
        ch = chr(value) if 32 <= value < 127 else '.'
        self._replace_text(row, hc_s, hc_s + 2, f'{value:02X}')
        self._replace_text(row, ac_s, ac_s + 1, ch)

        # delete+insert drops tags on the new chars, so re-mark this byte edited.
        self._tag_byte(self._tag_edited, off)
        if self._edit_mode and self._edit_cursor == off:
            self._draw_edit_cursor()

    def _on_hex_key(self, _widget, event):
        if not self._edit_mode or self._edit_cursor is None or self.data is None:
            return False

        kv = event.keyval
        ch = chr(kv).upper() if 32 <= kv <= 126 else ''

        if kv in (Gdk.KEY_Right, Gdk.KEY_Tab):
            self._move_edit_cursor(1)
        elif kv == Gdk.KEY_Left:
            if self._edit_nibble == 1:
                self._edit_nibble = 0
                self._draw_edit_cursor()
            else:
                self._move_edit_cursor(-1)
        elif kv == Gdk.KEY_BackSpace:
            self._move_edit_cursor(-1)
        elif kv == Gdk.KEY_Up:
            self._move_edit_cursor(-self.bpr)
        elif kv == Gdk.KEY_Down:
            self._move_edit_cursor(self.bpr)
        elif kv == Gdk.KEY_Escape:
            self._set_edit_cursor(None)
        elif ch in '0123456789ABCDEF':
            nib = int(ch, 16)
            off = self._edit_cursor
            cur = self.data[off]
            if self._edit_nibble == 0:
                self._write_byte(off, (nib << 4) | (cur & 0x0F))
                self._edit_nibble = 1
                self._draw_edit_cursor()
                self._set_status(f"Edit @ {hex(off)}: {ch}_ — type low nibble")
            else:
                new = (cur & 0xF0) | nib
                self._write_byte(off, new)
                self._move_edit_cursor(1)
                self._set_status(f"Wrote 0x{new:02X} @ {hex(off)}  — type high nibble")
        else:
            return False

        return True   # swallow handled keys

    # ── Byte editor dialog (right-click) ──────────────────────────────────────

    def _on_hex_right_click(self, event):
        off = self._click_to_offset(event)
        if off is None:
            return False
        menu = Gtk.Menu()
        item = Gtk.MenuItem(
            label=f"Edit byte @ {hex(off)}  (0x{self.data[off]:02X} / {self.data[off]})")
        item.connect('activate', lambda _w: self._open_byte_editor(off))
        menu.append(item)
        menu.show_all()
        self._ctx_menu = menu   # keep a reference so it isn't GC'd
        menu.popup_at_pointer(event)
        return True

    def _open_byte_editor(self, offset: int):
        current = self.data[offset]

        dlg = Gtk.Window(title=f"Edit Byte @ {hex(offset)}")
        dlg.set_transient_for(self.root)
        dlg.set_modal(True)
        dlg.set_resizable(False)
        dlg.set_default_size(340, 250)

        box = Gtk.Box(orientation=Gtk.Orientation.VERTICAL, spacing=4)
        box.set_margin_start(18)
        box.set_margin_end(18)
        box.set_margin_top(16)
        box.set_margin_bottom(14)
        dlg.add(box)

        off_lbl = Gtk.Label(label=f"Offset:  {hex(offset)}  ({offset})", xalign=0.0)
        self._class(off_lbl, 'title')
        box.pack_start(off_lbl, False, False, 2)
        cur_lbl = Gtk.Label(label=f"Current: 0x{current:02X}  ({current})", xalign=0.0)
        self._class(cur_lbl, 'muted')
        box.pack_start(cur_lbl, False, False, 6)

        lock = [False]
        hex_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        hl = Gtk.Label(label="Hex", xalign=0.0)
        hl.set_size_request(40, -1)
        hex_row.pack_start(hl, False, False, 0)
        hex_entry = Gtk.Entry()
        hex_entry.set_text(f'{current:02X}')
        hex_entry.override_font(self._mono_desc(12))
        hex_row.pack_start(hex_entry, False, False, 0)
        box.pack_start(hex_row, False, False, 4)

        dec_row = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        dl = Gtk.Label(label="Dec", xalign=0.0)
        dl.set_size_request(40, -1)
        dec_row.pack_start(dl, False, False, 0)
        dec_entry = Gtk.Entry()
        dec_entry.set_text(str(current))
        dec_entry.override_font(self._mono_desc(12))
        dec_row.pack_start(dec_entry, False, False, 0)
        box.pack_start(dec_row, False, False, 4)

        def hex_changed(_w):
            if lock[0]:
                return
            raw = hex_entry.get_text().strip()
            if raw.lower().startswith('0x'):
                raw = raw[2:]
            try:
                v = int(raw or '0', 16)
                if 0 <= v <= 255:
                    lock[0] = True
                    dec_entry.set_text(str(v))
                    lock[0] = False
            except ValueError:
                pass

        def dec_changed(_w):
            if lock[0]:
                return
            try:
                v = int(dec_entry.get_text().strip())
                if 0 <= v <= 255:
                    lock[0] = True
                    hex_entry.set_text(f'{v:02X}')
                    lock[0] = False
            except ValueError:
                pass

        hex_entry.connect('changed', hex_changed)
        dec_entry.connect('changed', dec_changed)

        def apply(*_):
            raw = hex_entry.get_text().strip()
            if raw.lower().startswith('0x'):
                raw = raw[2:]
            try:
                v = int(raw or '0', 16)
                if not (0 <= v <= 255):
                    raise ValueError
            except ValueError:
                self._error("Invalid Value", "Enter a hex value between 00 and FF.", parent=dlg)
                return
            self.data[offset] = v
            self._edited.add(offset)
            self._modified = True
            self._update_title()
            self._render()
            self._set_status(f"Byte @ {hex(offset)} changed: 0x{current:02X} → 0x{v:02X}")
            dlg.destroy()

        def cancel(*_):
            dlg.destroy()

        btns = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=8)
        btns.set_margin_top(18)
        apply_btn = self._btn("Apply", apply, 'accent', width=96)
        btns.pack_start(apply_btn, False, False, 0)
        btns.pack_start(self._btn("Cancel", cancel, width=96), False, False, 0)
        box.pack_start(btns, False, False, 0)

        dlg.connect('key-press-event', self._byte_editor_keys, apply, cancel)
        dlg.show_all()
        hex_entry.grab_focus()

    @staticmethod
    def _byte_editor_keys(_widget, event, apply, cancel):
        if event.keyval == Gdk.KEY_Return:
            apply()
            return True
        if event.keyval == Gdk.KEY_Escape:
            cancel()
            return True
        return False

    # ── Field management ──────────────────────────────────────────────────────

    def _parse_field_form(self) -> dict | None:
        if self.data is None:
            self._warn("No File", "Open a binary file first.")
            return None
        name = self._name_entry.get_text().strip()
        if not name:
            self._warn("Name Required", "Enter a field name.")
            return None
        try:
            start = int(self._start_entry.get_text(), 0)
            end = int(self._end_entry.get_text(), 0)
        except ValueError:
            self._error("Invalid Offset", "Start/End must be integers (e.g. 42 or 0x2a).")
            return None
        if start > end:
            start, end = end, start
        if start < 0:
            self._warn("Out of Range", "Start must be 0 or greater.")
            return None
        if end >= len(self.data):
            self._warn("Out of Range",
                       f"End {hex(end)} exceeds file size {hex(len(self.data) - 1)}.")
            return None
        return {
            'name': name,
            'start': start,
            'end': end,
            'color': self._current_color,
            'note': self._note_entry.get_text().strip(),
        }

    def _submit_field_form(self):
        if self._editing_field_id is not None:
            return self.update_field()
        self.add_field()

    def _field_by_id(self, fid: int) -> dict | None:
        return next((f for f in self.fields if f['id'] == fid), None)

    def _reset_field_form(self):
        self._editing_field_id = None
        self._update_field_btn.set_sensitive(False)
        self._name_entry.set_text('')
        self._start_entry.set_text('0x0')
        self._end_entry.set_text('0x0')
        self._note_entry.set_text('')
        sel = self.tree.get_selection()
        sel.unselect_all()
        if not self._edit_mode:
            self._set_hint(
                "Drag in hex view to select a field range  ·  Shift+Click to extend",
                '#ffd93d')

    def _update_tree_item(self, fld: dict):
        length = fld['end'] - fld['start'] + 1
        color = fld['color']
        fg = _contrast_fg(color)
        row = [fld['name'], hex(fld['start']), hex(fld['end']),
               str(length), fld.get('note', ''), color, fg]
        existing = self._tree_iter_for(fld['id'])
        if existing is not None:
            for i, val in enumerate(row):
                self._store.set_value(existing, i, val)
        else:
            it = self._store.append(row)
            self._tree_iters[fld['id']] = it

    def _tree_iter_for(self, fid: int):
        return self._tree_iters.get(fid)

    def _clear_field_tag(self, fid: int):
        tag = self._field_tags.pop(fid, None)
        if tag is not None:
            self.hex_buf.get_tag_table().remove(tag)

    def add_field(self):
        parsed = self._parse_field_form()
        if parsed is None:
            return

        fld = {'id': self._next_id, **parsed}
        self._next_id += 1
        self.fields.append(fld)
        self._update_tree_item(fld)

        if self.data is not None:
            self._apply_tag(fld)

        # Record colour usage and re-sort the strip (most-used colours drift left).
        self._color_usage[fld['color']] = self._color_usage.get(fld['color'], 0) + 1

        try:
            idx = PALETTE.index(self._current_color)
            self._set_color(PALETTE[(idx + 1) % len(PALETTE)])
        except ValueError:
            pass

        self._rebuild_palette()

        self._reset_field_form()
        self._clear_selection()
        self._inspect_mode = 'field'
        self._inspect_field_id = fld['id']
        self._refresh_inspector()
        if not self._edit_mode:
            self._set_hint(
                "Drag in hex view to select a field range  ·  Shift+Click to extend",
                '#ffd93d')

    def update_field(self):
        if self._editing_field_id is None:
            model, it = self.tree.get_selection().get_selected()
            if it is None:
                return
            self._editing_field_id = self._fid_for_iter(it)
        fld = self._field_by_id(self._editing_field_id)
        if fld is None:
            self._editing_field_id = None
            self._update_field_btn.set_sensitive(False)
            return

        parsed = self._parse_field_form()
        if parsed is None:
            return

        fid = fld['id']
        fld.update(parsed)
        self._update_tree_item(fld)
        if self.data is not None:
            self._clear_field_tag(fid)
            self._apply_tag(fld)
            self._apply_edited_tags()
            self._draw_selection()
            self._draw_edit_cursor()

        self._select_tree_row(fid)
        self._inspect_mode = 'field'
        self._inspect_field_id = fid
        self._refresh_inspector()
        self._set_status(f"Updated field: {fld['name']}")

    def delete_field(self):
        model, it = self.tree.get_selection().get_selected()
        if it is None:
            return
        fid = self._fid_for_iter(it)
        self.fields = [f for f in self.fields if f['id'] != fid]
        self._store.remove(it)
        self._tree_iters.pop(fid, None)
        self._clear_field_tag(fid)
        if self._inspect_mode == 'field' and self._inspect_field_id == fid:
            self._inspect_mode = None
        if self._editing_field_id == fid:
            self._editing_field_id = None
            self._update_field_btn.set_sensitive(False)
        self._clear_detail()

    def clear_all(self):
        if not self.fields:
            return
        if not self._ask_yes_no("Clear All", "Delete all field annotations?"):
            return
        for fld in list(self.fields):
            self._clear_field_tag(fld['id'])
        self.fields.clear()
        self._store.clear()
        self._tree_iters.clear()
        self._clear_selection()
        self._editing_field_id = None
        self._update_field_btn.set_sensitive(False)
        self._inspect_mode = None
        self._clear_detail()

    def scroll_to_field(self):
        model, it = self.tree.get_selection().get_selected()
        if it is None:
            return
        fid = self._fid_for_iter(it)
        fld = self._field_by_id(fid)
        if fld:
            row = fld['start'] // self.bpr
            self._scroll_hex_to(row, 0)

    # ── Tree helpers ──────────────────────────────────────────────────────────

    def _fid_for_iter(self, it) -> int:
        target = self._store.get_path(it)
        for fid, stored in self._tree_iters.items():
            if self._store.get_path(stored) == target:
                return fid
        return -1

    def _select_tree_row(self, fid: int):
        it = self._tree_iters.get(fid)
        if it is not None:
            self.tree.get_selection().select_iter(it)

    def _rebuild_tree(self):
        self._store.clear()
        self._tree_iters.clear()
        for fld in self.fields:
            self._update_tree_item(fld)

    # ── Field detail pane / inspector ─────────────────────────────────────────

    def _on_tree_select(self, _selection):
        model, it = self.tree.get_selection().get_selected()
        if it is None:
            return
        fid = self._fid_for_iter(it)
        fld = self._field_by_id(fid)
        if fld is None:
            return
        self._editing_field_id = fid
        self._name_entry.set_text(fld['name'])
        self._start_entry.set_text(hex(fld['start']))
        self._end_entry.set_text(hex(fld['end']))
        self._note_entry.set_text(fld.get('note', ''))
        self._set_color(fld['color'])
        self._update_field_btn.set_sensitive(True)
        self._set_hint("Editing selected field. Change values, then Update Selected.", '#6bcb77')
        self._inspect_mode = 'field'
        self._inspect_field_id = fid
        self._refresh_inspector()

    def _interpret_lines(self, raw, fmt: str, endian: str, signed: bool) -> list[str]:
        bo = 'little' if endian == 'LE' else 'big'
        sc = '<' if endian == 'LE' else '>'
        n = len(raw)

        if fmt == 'Integer':
            if n == 0:
                return ["(no bytes)"]
            if n > 64:
                return [f"Selection is {n} bytes — select ≤ 64 to read as one integer.",
                        "Use the Hex or Bytes view for large ranges."]
            val = int.from_bytes(raw, bo, signed=signed)
            other = int.from_bytes(raw, bo, signed=not signed)
            sign = '-' if val < 0 else ''
            return [
                f"{'int' if signed else 'uint'}{n * 8}  ({endian})",
                f"  dec : {val}",
                f"  hex : {sign}0x{abs(val):X}",
                f"  {'unsigned' if signed else 'signed'} : {other}",
            ]

        if fmt == 'Float':
            code_ = {2: 'e', 4: 'f', 8: 'd'}.get(n)
            if code_ is None:
                return [f"Select 2, 4, or 8 bytes for a float (have {n})."]
            width = {2: 'float16', 4: 'float32', 8: 'float64'}[n]
            val = struct.unpack(sc + code_, bytes(raw))[0]
            return [f"{width}  ({endian})", f"  {val!r}"]

        if fmt == 'String':
            sample = bytes(raw[:4096])
            trunc = '  …(truncated)' if n > 4096 else ''
            out = [f"ascii   : {''.join(chr(b) if 32 <= b < 127 else '.' for b in sample)!r}{trunc}"]
            try:
                out.append(f"utf-8   : {sample.decode('utf-8')!r}{trunc}")
            except UnicodeDecodeError:
                out.append("utf-8   : (decode error)")
            u16 = 'utf-16-le' if endian == 'LE' else 'utf-16-be'
            try:
                out.append(f"utf-16  : {sample.decode(u16)!r}{trunc}")
            except UnicodeDecodeError:
                out.append("utf-16  : (decode error)")
            out.append(f"latin-1 : {sample.decode('latin-1')!r}{trunc}")
            return out

        if fmt == 'Hex':
            hx = bytes(raw).hex()
            return [' '.join(hx[i:i + 2] for i in range(0, len(hx), 2)) or "(no bytes)"]

        if fmt == 'Binary':
            out = [' '.join(f'{b:08b}' for b in raw[:16]) or "(no bytes)"]
            if n > 16:
                out.append(f"(showing first 16 of {n} bytes)")
            return out

        if fmt == 'Bytes (dec)':
            out = [' '.join(str(b) for b in raw[:64]) or "(no bytes)"]
            if n > 64:
                out.append(f"(showing first 64 of {n} bytes)")
            return out

        return ["(unknown format)"]

    def _refresh_inspector(self):
        if self.data is None:
            return
        note = None
        if self._inspect_mode == 'sel' and self._sel_range is not None:
            start, end = self._sel_range
            title = f"Selection  {hex(start)}–{hex(end)}"
        elif self._inspect_mode == 'field' and self._inspect_field_id is not None:
            fld = self._field_by_id(self._inspect_field_id)
            if fld is None:
                self._clear_detail()
                return
            start, end = fld['start'], fld['end']
            title = f"Field “{fld['name']}”  {hex(start)}–{hex(end)}"
            note = fld.get('note', '')
        else:
            self._clear_detail()
            return

        start = max(0, start)
        end = min(end, len(self.data) - 1)
        if start > end:
            self._clear_detail()
            return

        raw = self.data[start:end + 1]
        n = len(raw)
        fmt = self._fmt_value
        endian = self._endian_value
        signed = self._signed_sw.get_active()

        lines = [title, f"Length : {n} byte{'s' if n != 1 else ''} ({hex(n)})"]
        if note:
            lines.append(f"Note   : {note}")
        lines += ["", f"── {fmt} " + "─" * 30]
        lines += self._interpret_lines(raw, fmt, endian, signed)
        lines += ["", "── Hex " + "─" * 30]
        dump = raw[:256]
        for i in range(0, len(dump), 16):
            chunk = dump[i:i + 16]
            h = ' '.join(f'{b:02X}' for b in chunk)
            a = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
            lines.append(f"  {start + i:08X}: {h:<48} |{a}|")
        if n > 256:
            lines.append(f"  …(showing first 256 of {n} bytes)")

        self._set_detail_text('\n'.join(lines))

    def _set_detail_text(self, text: str):
        self._detail_buf.set_text(text)

    def _clear_detail(self):
        self._set_detail_text(
            "Drag bytes in the hex view, or click a field, to inspect them here.")


# ── Multi-file controller ─────────────────────────────────────────────────────

class MultiFileApp:
    """Owns the shared window, the one screen-level CSS provider, the global theme
    and zoom, and a notebook tab bar. Each tab is an independent
    BinaryFieldAnnotator with its own panes, state and Python console."""

    def __init__(self, window: "Gtk.Window"):
        self.window = window
        window.set_title("Binary Field Annotator")
        window.set_default_size(1480, 900)
        window.set_size_request(960, 640)

        # Global (cross-tab) appearance state.
        self._mode = 'dark'
        self._ui_scale = 1.0
        self._syncing_theme = False     # guards programmatic theme-toggle echoes

        # One CSS provider for the whole screen, shared by every tab.
        self.css_provider = Gtk.CssProvider()
        Gtk.StyleContext.add_provider_for_screen(
            Gdk.Screen.get_default(), self.css_provider,
            Gtk.STYLE_PROVIDER_PRIORITY_APPLICATION)

        self.tabs: list[BinaryFieldAnnotator] = []

        self.notebook = Gtk.Notebook()
        self.notebook.set_scrollable(True)
        self.notebook.connect('switch-page', self._on_switch_page)

        # "+" new-tab button pinned to the end of the tab strip.
        plus = Gtk.Button(label="+")
        plus.set_relief(Gtk.ReliefStyle.NONE)
        plus.set_tooltip_text("New tab  (Ctrl+T)")
        plus.connect('clicked', lambda _w: self.new_tab())
        plus.show()
        self.notebook.set_action_widget(plus, Gtk.PackType.END)

        window.add(self.notebook)
        window.connect('key-press-event', self._on_key)

        self.new_tab()   # start with one empty tab

    # ── Active-tab helpers ────────────────────────────────────────────────────

    @property
    def active_tab(self) -> "BinaryFieldAnnotator | None":
        idx = self.notebook.get_current_page()
        if idx < 0:
            return None
        page = self.notebook.get_nth_page(idx)
        return next((t for t in self.tabs if t.content is page), None)

    # ── Tab lifecycle ─────────────────────────────────────────────────────────

    def new_tab(self, path: str | None = None) -> "BinaryFieldAnnotator":
        tab = BinaryFieldAnnotator(self)
        self.tabs.append(tab)
        label = self._make_tab_label(tab)
        idx = self.notebook.append_page(tab.content, label)
        self.notebook.set_tab_reorderable(tab.content, True)
        tab.content.show_all()
        self.notebook.set_current_page(idx)
        if path:
            tab.load_path(path)
        else:
            self.refresh_titles(tab)
        return tab

    def _make_tab_label(self, tab) -> Gtk.Widget:
        box = Gtk.Box(orientation=Gtk.Orientation.HORIZONTAL, spacing=6)
        lbl = Gtk.Label(label=tab.tab_label_text())
        lbl.set_ellipsize(Pango.EllipsizeMode.END)
        lbl.set_width_chars(14)          # stable allocation so short names aren't clipped
        lbl.set_max_width_chars(22)
        lbl.set_xalign(0.0)
        close = Gtk.Button(label="×")
        close.set_relief(Gtk.ReliefStyle.NONE)
        close.get_style_context().add_class('tabclose')
        close.set_tooltip_text("Close tab  (Ctrl+W)")
        close.connect('clicked', lambda _w: self.close_tab(tab))
        box.pack_start(lbl, False, False, 0)
        box.pack_start(close, False, False, 0)
        # Wrap in an EventBox so middle-click on the tab can close it.
        evbox = Gtk.EventBox()
        evbox.add(box)
        evbox.connect('button-press-event', self._on_tab_click, tab)
        evbox.show_all()
        tab._tab_label = lbl     # so refresh_titles can update the text
        return evbox

    def _on_tab_click(self, _widget, event, tab):
        if event.button == 2:            # middle-click closes
            self.close_tab(tab)
            return True
        return False

    def close_tab(self, tab):
        if tab not in self.tabs:
            return
        # Tear down any floating console window this tab owns.
        if getattr(tab, '_console_window', None) is not None:
            tab._console_window.destroy()
            tab._console_window = None
        idx = self.notebook.page_num(tab.content)
        if idx >= 0:
            self.notebook.remove_page(idx)
        self.tabs.remove(tab)
        if not self.tabs:
            self.new_tab()               # never leave the window tab-less
        else:
            self.refresh_titles(self.active_tab)

    # ── Open ──────────────────────────────────────────────────────────────────

    def open_dialog(self):
        """Run the file chooser (parented to the shared window). Reuse the active
        tab if it's still pristine (no file loaded yet); otherwise open in a new tab."""
        ref = self.active_tab or (self.tabs[0] if self.tabs else None)
        if ref is None:
            return
        path = ref._file_dialog(
            "Open Binary File", Gtk.FileChooserAction.OPEN,
            [("All files", ["*"]),
             ("Binary", ["*.bin", "*.raw", "*.dat"]),
             ("ELF", ["*.elf", "*.so", "*.o"]),
             ("PCAP", ["*.pcap", "*.pcapng"])])
        if not path:
            return
        if ref.is_pristine():
            ref.load_path(path)
        else:
            self.new_tab(path)

    # ── Titles ────────────────────────────────────────────────────────────────

    def refresh_titles(self, tab):
        if getattr(tab, '_tab_label', None) is not None:
            tab._tab_label.set_text(tab.tab_label_text())
        if tab is self.active_tab:
            self.window.set_title(tab.title_text())

    def _on_switch_page(self, _nb, page, _num):
        tab = next((t for t in self.tabs if t.content is page), None)
        if tab is not None:
            self.window.set_title(tab.title_text())

    # ── Global theme / zoom ───────────────────────────────────────────────────

    def set_theme(self, mode: str):
        self._mode = mode
        self._syncing_theme = True
        try:
            for tab in self.tabs:
                tab._retheme_native(mode)      # re-themes native widgets + shared CSS
                seg = getattr(tab, '_appearance_map', None)
                if seg:
                    seg[mode.capitalize()].set_active(True)
        finally:
            self._syncing_theme = False

    def zoom_in(self):
        self._set_scale(self._ui_scale + ZOOM_STEP)

    def zoom_out(self):
        self._set_scale(self._ui_scale - ZOOM_STEP)

    def _set_scale(self, scale: float):
        scale = round(max(ZOOM_MIN, min(ZOOM_MAX, scale)), 2)
        if scale == self._ui_scale:
            return
        self._ui_scale = scale
        for tab in self.tabs:
            tab._set_ui_scale(scale)

    # ── Window keys (one handler for all tabs) ────────────────────────────────

    def _on_key(self, _widget, event):
        ctrl = bool(event.state & Gdk.ModifierType.CONTROL_MASK)
        kv = event.keyval
        if not ctrl:
            return False
        active = self.active_tab
        if kv in (Gdk.KEY_o, Gdk.KEY_O):
            self.open_dialog(); return True
        if kv in (Gdk.KEY_t, Gdk.KEY_T):
            self.new_tab(); return True
        if kv in (Gdk.KEY_w, Gdk.KEY_W):
            if active:
                self.close_tab(active)
            return True
        if kv in (Gdk.KEY_plus, Gdk.KEY_equal, Gdk.KEY_KP_Add):
            self.zoom_in(); return True
        if kv in (Gdk.KEY_minus, Gdk.KEY_underscore, Gdk.KEY_KP_Subtract):
            self.zoom_out(); return True
        if active is None:
            return False
        if kv == Gdk.KEY_s:
            active.save_annotations(); return True
        if kv == Gdk.KEY_S:                      # Ctrl+Shift+S
            active.save_binary(); return True
        if kv in (Gdk.KEY_l, Gdk.KEY_L):
            active.load_annotations(); return True
        return False


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    win = Gtk.Window()
    win.connect('destroy', Gtk.main_quit)
    app = MultiFileApp(win)
    win._app_ref = app   # keep a reference
    win.show_all()
    Gtk.main()


if __name__ == '__main__':
    main()
