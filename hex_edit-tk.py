#!/usr/bin/env python3
"""
Binary Field Annotator
Color-annotate byte ranges in binary files to track protocol header fields,
inspect values, and edit bytes inline.

Requires:
  - python3-tk       (pre-installed on Kali 2025.3)
  - customtkinter    (pip install customtkinter)
                     On Kali/Debian (PEP 668) use a venv, or:
                     pip install --user --break-system-packages customtkinter
"""

import tkinter as tk
from tkinter import ttk, filedialog, colorchooser, messagebox
from tkinter import font as tkfont
import code
import contextlib
import io
import json
import os
import struct

try:
    import customtkinter as ctk
except ImportError:
    raise SystemExit(
        "This app requires CustomTkinter.\n"
        "  pip install customtkinter\n"
        "On Kali/Debian you may need a venv, or:\n"
        "  pip install --user --break-system-packages customtkinter")

# ── Constants ────────────────────────────────────────────────────────────────

OFFSET_COLS = 10   # "XXXXXXXX  " — 8 hex digits + 2 spaces

HEX_CELL_COLS = 4  # " XX " centered display cell for one byte

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

# Design tokens for the NATIVE widgets (tk.Text / Treeview / Menu / PanedWindow)
# and for CTk accents.  CTk widgets receive (light, dark) tuples via _tok() so
# they auto-switch on appearance change; native widgets are re-themed manually
# by _retheme_native().
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


def _resolve_font(root, preferred: list[str], fallback: str) -> str:
    """Return the first installed font family from `preferred`, else `fallback`."""
    try:
        available = set(tkfont.families(root))
    except Exception:
        return fallback
    for fam in preferred:
        if fam in available:
            return fam
    return fallback


# ── Main application ─────────────────────────────────────────────────────────

class BinaryFieldAnnotator:
    def __init__(self, root: "ctk.CTk"):
        self.root = root
        self.root.title("Binary Field Annotator")
        self.root.geometry("1480x900")

        self._mode = 'dark'
        self.root.configure(fg_color=self._tok('window'))

        self.data: bytearray | None = None
        self.filepath: str | None = None
        self._modified = False
        self.fields: list[dict] = []
        self._next_id = 0
        self._current_color = PALETTE[0]
        self._custom_colors: list[str] = []
        self._editing_field_id: int | None = None

        # Mouse selection state (annotation / drag-to-select)
        self._drag_anchor: int | None = None
        self._dragging = False
        self._sel_range: tuple[int, int] | None = None

        # Live inspector target: 'sel' (mouse selection) | 'field' | None
        self._inspect_mode: str | None = None
        self._inspect_field_id: int | None = None

        # Inline hex-edit state
        self._edit_mode   = False
        self._edit_cursor: int | None = None
        self._edit_nibble: int = 0   # 0 = expecting high nibble, 1 = expecting low nibble
        self._edited: set[int] = set()  # offsets modified this session
        self._ui_scale = 1.0

        # Resolve fonts (needs an existing root)
        self.mono_family = _resolve_font(
            self.root,
            ['JetBrains Mono', 'Cascadia Code', 'DejaVu Sans Mono', 'Consolas',
             'Courier New'], 'Courier New')
        self.ui_family = _resolve_font(
            self.root,
            ['Inter', 'Segoe UI', 'DejaVu Sans', 'Helvetica', 'Arial'], 'Arial')

        self.ui_font      = ctk.CTkFont(family=self.ui_family, size=13)
        self.ui_font_sm   = ctk.CTkFont(family=self.ui_family, size=12)
        self.ui_font_bold = ctk.CTkFont(family=self.ui_family, size=13, weight='bold')
        self.mono_font    = ctk.CTkFont(family=self.mono_family, size=12)

        self._paneds: list[tk.PanedWindow] = []
        self._pane_minsizes: list[tuple[tk.PanedWindow, tk.Widget, int]] = []
        self._console_visible = False
        self._console_more = False
        self._console_history: list[str] = []
        self._console_history_index: int | None = None
        self._console_output_cache = ""
        self._console_floating = False
        self._console_window: "ctk.CTkToplevel" | None = None
        self._console_drag_origin: tuple[int, int] | None = None
        self._console_dragging = False
        self._console_dirty = False
        self._console_changed_ranges: list[tuple[int, int]] = []
        self._console = code.InteractiveConsole()
        self._init_console_namespace()

        ttk.Style().theme_use('clam')   # required for Treeview color control
        self._build_ui()
        self._bind_keys()

    # ── Theme helpers ─────────────────────────────────────────────────────────

    def _tok(self, key: str) -> tuple[str, str]:
        """(light, dark) color tuple for a token — CTk auto-picks by mode."""
        return (THEME['light'][key], THEME['dark'][key])

    def _btn(self, parent, text, cmd, kind='neutral', **kw):
        styles = {
            'accent':  dict(fg_color=self._tok('accent'),
                            hover_color=self._tok('accent_hover'), text_color='#ffffff'),
            'danger':  dict(fg_color=self._tok('danger'),
                            hover_color=self._tok('danger_hover'), text_color='#ffffff'),
            'neutral': dict(fg_color=self._tok('neutral'),
                            hover_color=self._tok('neutral_hover'),
                            text_color=self._tok('text')),
        }
        opts = dict(corner_radius=8, font=self.ui_font, height=32)
        opts.update(styles[kind])
        opts.update(kw)
        return ctk.CTkButton(parent, text=text, command=cmd, **opts)

    def _sep(self, parent):
        ctk.CTkFrame(parent, width=1, height=26,
                     fg_color=self._tok('border')).pack(side=tk.LEFT, padx=10, pady=12)

    def _scaled_int(self, value: int, minimum: int = 1) -> int:
        return max(minimum, round(value * self._ui_scale))

    def _font_size(self, value: int, minimum: int = 7) -> int:
        return self._scaled_int(value, minimum)

    def _make_paned(self, parent, orient):
        paned = tk.PanedWindow(
            parent, orient=orient, bd=0, sashwidth=self._scaled_int(6, 6),
            sashrelief='flat', sashpad=0, handlesize=0, showhandle=False,
            opaqueresize=False)
        self._paneds.append(paned)
        return paned

    def _add_pane(self, paned, child, minsize: int, **kw):
        paned.add(child, minsize=self._scaled_int(minsize), **kw)
        self._pane_minsizes.append((paned, child, minsize))

    def _retheme_native(self, mode: str = 'dark'):
        """Apply the active palette to the non-CTk widgets (CTk ones auto-adapt)."""
        self._mode = mode
        t = THEME[mode]

        self.hex_text.configure(bg=t['hex_bg'], fg=t['text'],
                                insertbackground=t['cursor_ins'],
                                selectbackground=t['selection'],
                                font=(self.mono_family, self._font_size(11)))
        self._detail_text.configure(bg=t['card'], fg=t['text'],
                                    insertbackground=t['cursor_ins'],
                                    selectbackground=t['selection'],
                                    font=(self.mono_family, self._font_size(10)))
        if hasattr(self, '_console_text'):
            self._console_text.configure(bg=t['hex_bg'], fg=t['text'],
                                         insertbackground=t['cursor_ins'],
                                         selectbackground=t['selection'],
                                         font=(self.mono_family, self._font_size(10)))

        # Edited highlight is constant; the edit cursor inverts per mode.
        self.hex_text.tag_configure('edited', background=EDITED_BG, foreground='#ffffff')
        if mode == 'light':
            cur_bg, cur_fg = t['text'], '#ffffff'
        else:
            cur_bg, cur_fg = '#ffffff', '#000000'
        self.hex_text.tag_configure('edit_cursor', background=cur_bg, foreground=cur_fg,
                                    font=(self.mono_family, self._font_size(11), 'bold'))
        self.hex_text.tag_configure('rangesel', background=t['selection'],
                                    foreground=t['text'])

        style = ttk.Style()
        style.configure('Treeview', background=t['card'], fieldbackground=t['card'],
                        foreground=t['text'], rowheight=self._scaled_int(24, 18),
                        borderwidth=0, font=(self.ui_family, self._font_size(10)))
        style.configure('Treeview.Heading', background=t['surface'],
                        foreground=t['muted'], borderwidth=0,
                        font=(self.ui_family, self._font_size(10), 'bold'))
        style.map('Treeview',
                  background=[('selected', t['selection'])],
                  foreground=[('selected', t['text'])])

        for pw in self._paneds:
            pw.configure(bg=t['border'],
                         sashwidth=self._scaled_int(6, 6),
                         proxybackground=t['accent'],
                         proxyborderwidth=1,
                         proxyrelief='flat')

        for paned, child, minsize in self._pane_minsizes:
            if str(child) in paned.panes():
                paned.paneconfigure(child, minsize=self._scaled_int(minsize))

    # ── UI construction ──────────────────────────────────────────────────────

    def _build_ui(self):
        self._build_toolbar()
        self._build_statusbar()          # packed to the bottom first

        body = ctk.CTkFrame(self.root, fg_color='transparent')
        body.pack(side=tk.TOP, fill=tk.BOTH, expand=True, padx=8, pady=6)

        self._main_vpaned = self._make_paned(body, tk.VERTICAL)
        self._main_vpaned.pack(fill=tk.BOTH, expand=True)

        top = ctk.CTkFrame(self._main_vpaned, fg_color='transparent')
        self._add_pane(self._main_vpaned, top, minsize=480, stretch='always')

        paned = self._make_paned(top, tk.HORIZONTAL)
        paned.pack(fill=tk.BOTH, expand=True)

        self._build_hex_panel(paned)
        self._build_right_panel(paned)
        self._build_python_console(self._main_vpaned)

        self._retheme_native('dark')

    def _build_toolbar(self):
        bar = ctk.CTkFrame(self.root, corner_radius=0, height=54,
                           fg_color=self._tok('surface'))
        bar.pack(side=tk.TOP, fill=tk.X)
        bar.pack_propagate(False)

        self._btn(bar, "Open", self.open_file, kind='accent',
                  width=92).pack(side=tk.LEFT, padx=(10, 4), pady=11)
        self._btn(bar, "Save Binary As…", self.save_binary,
                  width=130).pack(side=tk.LEFT, padx=4, pady=11)
        self._sep(bar)
        self._btn(bar, "Save Annot.", self.save_annotations,
                  width=104).pack(side=tk.LEFT, padx=4, pady=11)
        self._btn(bar, "Load Annot.", self.load_annotations,
                  width=104).pack(side=tk.LEFT, padx=4, pady=11)
        self._sep(bar)

        ctk.CTkLabel(bar, text="BPR", font=self.ui_font_sm,
                     text_color=self._tok('muted')).pack(side=tk.LEFT, padx=(4, 6))
        self._bpr_var = tk.StringVar(value='16')
        self._bpr_seg = ctk.CTkSegmentedButton(
            bar, values=['8', '16', '32'], variable=self._bpr_var,
            command=lambda _v: self._rerender(), font=self.ui_font_sm, height=30)
        self._bpr_seg.pack(side=tk.LEFT, padx=4, pady=12)
        self._sep(bar)

        self._edit_switch = ctk.CTkSwitch(
            bar, text="Hex Edit", command=self._toggle_edit_mode,
            font=self.ui_font, progress_color=self._tok('danger'))
        self._edit_switch.pack(side=tk.LEFT, padx=10)
        self._python_btn = self._btn(bar, "Python", self._toggle_python_console,
                                     width=82, height=32)
        self._python_btn.pack(side=tk.LEFT, padx=(2, 8), pady=11)

        # Right side: appearance toggle
        self._appearance = ctk.CTkSegmentedButton(
            bar, values=['Dark', 'Light'], command=self._on_appearance_change,
            font=self.ui_font_sm, height=30)
        self._appearance.set('Dark')
        self._appearance.pack(side=tk.RIGHT, padx=12)
        ctk.CTkLabel(bar, text="Theme", font=self.ui_font_sm,
                     text_color=self._tok('muted')).pack(side=tk.RIGHT, padx=(0, 2))

    def _build_statusbar(self):
        bar = ctk.CTkFrame(self.root, corner_radius=0, height=28,
                           fg_color=self._tok('surface'))
        bar.pack(side=tk.BOTTOM, fill=tk.X)
        bar.pack_propagate(False)
        self._status_var = tk.StringVar(value="Open a binary file to begin.")
        ctk.CTkLabel(bar, textvariable=self._status_var, anchor='w',
                     font=self.ui_font_sm, text_color=self._tok('muted')).pack(
                         side=tk.LEFT, padx=14)

    def _build_hex_panel(self, paned):
        frame = ctk.CTkFrame(paned, corner_radius=10, fg_color=self._tok('card'))
        self._add_pane(paned, frame, minsize=660)

        self._hover_label = ctk.CTkLabel(
            frame, text="  Hover over bytes to inspect", anchor='w',
            font=self.mono_font, text_color=self._tok('muted'),
            fg_color=self._tok('surface'), corner_radius=8, height=28)
        self._hover_label.pack(fill=tk.X, padx=8, pady=(8, 4))

        hex_frame = ctk.CTkFrame(frame, fg_color='transparent')
        hex_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))

        self.hex_text = tk.Text(
            hex_frame, font=(self.mono_family, self._font_size(11)),
            bd=0, relief='flat', highlightthickness=0,
            wrap=tk.NONE, state=tk.DISABLED, cursor='arrow')
        vsb = ctk.CTkScrollbar(hex_frame, command=self.hex_text.yview)
        hsb = ctk.CTkScrollbar(hex_frame, orientation='horizontal',
                               command=self.hex_text.xview)
        self.hex_text.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side=tk.RIGHT,  fill=tk.Y)
        hsb.pack(side=tk.BOTTOM, fill=tk.X)
        self.hex_text.pack(fill=tk.BOTH, expand=True)

        self.hex_text.bind('<Button-1>',        self._on_hex_press)
        self.hex_text.bind('<B1-Motion>',       self._on_hex_drag)
        self.hex_text.bind('<ButtonRelease-1>', self._on_hex_release)
        self.hex_text.bind('<Shift-Button-1>',  self._on_hex_shift_click)
        self.hex_text.bind('<Button-3>',        self._on_hex_right_click)
        self.hex_text.bind('<Motion>',          self._on_hex_hover)
        self.hex_text.bind('<KeyPress>',        self._on_hex_key)

        # Pre-configure overlay tags so priority is stable and tag_raise never
        # hits an undefined tag (colors finalized in _retheme_native).  Note the
        # selection tag is 'rangesel', NOT 'sel' — 'sel' is Tk's built-in
        # selection tag and would collide.
        self.hex_text.tag_configure('edited', background=EDITED_BG, foreground='#ffffff')
        self.hex_text.tag_configure('rangesel', background='#2d4f78')
        self.hex_text.tag_configure('edit_cursor', background='#ffffff',
                                    foreground='#000000',
                                    font=(self.mono_family, self._font_size(11), 'bold'))

    def _build_right_panel(self, paned):
        frame = ctk.CTkFrame(paned, corner_radius=10, fg_color=self._tok('surface'))
        paned.add(frame, minsize=400)

        self._build_add_form(frame)

        vpaned = self._make_paned(frame, tk.VERTICAL)
        vpaned.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))

        fields_frame = ctk.CTkFrame(vpaned, corner_radius=10, fg_color=self._tok('card'))
        self._add_pane(vpaned, fields_frame, minsize=130, stretch='always')

        detail_frame = ctk.CTkFrame(vpaned, corner_radius=10, fg_color=self._tok('card'))
        self._add_pane(vpaned, detail_frame, minsize=90, stretch='always')

        self._build_fields_table(fields_frame)
        self._build_action_buttons(fields_frame)
        self._build_detail_pane(detail_frame)

    def _build_python_console(self, paned):
        self._console_dock_parent = paned
        self._console_frame = self._create_python_console_frame(paned)
        self._pane_minsizes.append((paned, self._console_frame, 180))

    def _create_python_console_frame(self, parent):
        frame = ctk.CTkFrame(parent, corner_radius=10, fg_color=self._tok('card'))

        header = ctk.CTkFrame(frame, fg_color='transparent')
        header.pack(fill=tk.X, padx=10, pady=(8, 4))
        self._console_header = header
        self._console_title = ctk.CTkLabel(
            header, text="Python Console", font=self.ui_font_bold,
            text_color=self._tok('accent'))
        self._console_title.pack(side=tk.LEFT)
        for widget in (header, self._console_title):
            widget.bind('<ButtonPress-1>', self._console_drag_start)
            widget.bind('<B1-Motion>', self._console_drag_motion)
            widget.bind('<ButtonRelease-1>', self._console_drag_release)
        self._btn(header, "Hide", self._hide_python_console,
                  width=68, height=28, font=self.ui_font_sm).pack(side=tk.RIGHT, padx=(6, 0))
        self._console_pop_btn = self._btn(
            header, "Pop Out", self._float_python_console,
            width=78, height=28, font=self.ui_font_sm)
        self._console_pop_btn.pack(side=tk.RIGHT, padx=(6, 0))
        self._btn(header, "Clear", self._clear_console,
                  width=68, height=28, font=self.ui_font_sm).pack(side=tk.RIGHT)

        holder = ctk.CTkFrame(frame, fg_color='transparent')
        holder.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 6))

        self._console_text = tk.Text(
            holder, font=(self.mono_family, self._font_size(10)),
            bd=0, relief='flat', highlightthickness=0,
            state=tk.DISABLED, wrap=tk.WORD, height=8)
        csb = ctk.CTkScrollbar(holder, command=self._console_text.yview)
        self._console_text.configure(yscrollcommand=csb.set)
        csb.pack(side=tk.RIGHT, fill=tk.Y)
        self._console_text.pack(fill=tk.BOTH, expand=True)

        input_row = ctk.CTkFrame(frame, fg_color='transparent')
        input_row.pack(fill=tk.X, padx=8, pady=(0, 8))
        self._console_prompt_var = tk.StringVar(value='...' if self._console_more else '>>>')
        ctk.CTkLabel(input_row, textvariable=self._console_prompt_var,
                     font=self.mono_font, width=32,
                     text_color=self._tok('accent')).pack(side=tk.LEFT, padx=(2, 6))
        self._console_input_var = tk.StringVar()
        self._console_input = ctk.CTkEntry(
            input_row, textvariable=self._console_input_var,
            font=self.mono_font, height=30)
        self._console_input.pack(side=tk.LEFT, fill=tk.X, expand=True)
        self._console_input.bind('<Return>', self._execute_console_line)
        self._console_input.bind('<Up>', self._console_history_prev)
        self._console_input.bind('<Down>', self._console_history_next)

        if not self._console_output_cache:
            self._console_output_cache = (
                "Trusted local Python console. Imports and filesystem access are allowed.\n"
                "Scripts run in the UI process; long-running code can block the app.\n"
                "Use buf, app, refresh(), write(), insert(), delete(), hexdump(), len_buf().\n\n")
        self._console_text.configure(state=tk.NORMAL)
        self._console_text.insert('1.0', self._console_output_cache)
        self._console_text.see(tk.END)
        self._console_text.configure(state=tk.DISABLED)
        self._retheme_native(self._mode)
        return frame

    def _build_add_form(self, parent):
        card = ctk.CTkFrame(parent, corner_radius=10, fg_color=self._tok('card'))
        card.pack(fill=tk.X, padx=8, pady=8)
        card.columnconfigure(1, weight=1)

        ctk.CTkLabel(card, text="Add Field", font=self.ui_font_bold,
                     text_color=self._tok('accent')).grid(
                         row=0, column=0, columnspan=4, sticky='w', padx=12, pady=(10, 6))

        self._name_var  = tk.StringVar()
        self._start_var = tk.StringVar(value='0x0')
        self._end_var   = tk.StringVar(value='0x0')
        self._note_var  = tk.StringVar()

        def lrow(r, label, var):
            ctk.CTkLabel(card, text=label, font=self.ui_font_sm,
                         text_color=self._tok('muted'), width=46, anchor='w').grid(
                             row=r, column=0, sticky='w', padx=(12, 4), pady=3)
            ctk.CTkEntry(card, textvariable=var, font=self.mono_font, height=30).grid(
                row=r, column=1, columnspan=3, sticky='ew', padx=(0, 12), pady=3)

        lrow(1, "Name",  self._name_var)
        lrow(2, "Start", self._start_var)
        lrow(3, "End",   self._end_var)
        lrow(4, "Note",  self._note_var)

        ctk.CTkLabel(card, text="Color", font=self.ui_font_sm,
                     text_color=self._tok('muted')).grid(
                         row=5, column=0, sticky='w', padx=(12, 4), pady=(8, 3))
        self._palette_frame = ctk.CTkFrame(card, fg_color='transparent')
        self._palette_frame.grid(row=5, column=1, columnspan=3, sticky='w', pady=(8, 3))
        pal = self._palette_frame

        self._pal_btns: list = []
        for color in PALETTE:
            b = ctk.CTkButton(self._palette_frame, text='', width=22, height=22, corner_radius=6,
                              fg_color=color, hover_color=color,
                              border_width=0, command=lambda c=color: self._set_color(c))
            b.pack(side=tk.LEFT, padx=2)
            self._pal_btns.append(b)

        ctk.CTkButton(pal, text="…", width=28, height=22, corner_radius=6,
                      fg_color=self._tok('neutral'), hover_color=self._tok('neutral_hover'),
                      text_color=self._tok('text'),
                      command=self._pick_custom_color).pack(side=tk.LEFT, padx=(8, 4))

        self._swatch = ctk.CTkFrame(pal, width=30, height=22, corner_radius=6,
                                    fg_color=self._current_color)
        self._swatch.pack(side=tk.LEFT, padx=4)

        self._click_hint = ctk.CTkLabel(
            card, text="Drag in hex view to select a field range",
            font=self.ui_font_sm, text_color='#ffd93d', anchor='w')
        self._click_hint.grid(row=6, column=0, columnspan=4, sticky='w',
                              padx=12, pady=(8, 0))

        ctk.CTkLabel(card, text="Drag to select · Shift+Click to extend · or type offsets",
                     font=self.ui_font_sm, text_color=self._tok('muted'),
                     anchor='w').grid(row=7, column=0, columnspan=4, sticky='w',
                                      padx=12, pady=(0, 4))

        self._btn(card, "Add Field   (Enter)", self.add_field, kind='accent',
                  font=self.ui_font_bold, height=34).grid(
                      row=8, column=0, columnspan=4, sticky='ew', padx=12, pady=(8, 4))
        edit_bar = ctk.CTkFrame(card, fg_color='transparent')
        edit_bar.grid(row=9, column=0, columnspan=4, sticky='ew', padx=12, pady=(0, 12))
        edit_bar.columnconfigure((0, 1), weight=1)
        self._update_field_btn = self._btn(
            edit_bar, "Update Selected", self.update_field, kind='accent',
            font=self.ui_font_sm, height=30, state=tk.DISABLED)
        self._update_field_btn.grid(row=0, column=0, sticky='ew', padx=(0, 4))
        self._btn(edit_bar, "New Field", self._reset_field_form,
                  font=self.ui_font_sm, height=30).grid(
                      row=0, column=1, sticky='ew', padx=(4, 0))

    def _build_fields_table(self, parent):
        ctk.CTkLabel(parent, text="Defined Fields", font=self.ui_font_bold,
                     text_color=self._tok('accent')).pack(
                         anchor='w', padx=12, pady=(10, 4))
        holder = ctk.CTkFrame(parent, fg_color='transparent')
        holder.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 4))

        cols = ('Name', 'Start', 'End', 'Len', 'Note')
        self.tree = ttk.Treeview(holder, columns=cols, show='headings', height=8)
        for col, w in zip(cols, (120, 70, 70, 55, 110)):
            self.tree.heading(col, text=col)
            self.tree.column(col, width=w, minwidth=30)

        tsb = ctk.CTkScrollbar(holder, command=self.tree.yview)
        self.tree.configure(yscrollcommand=tsb.set)
        tsb.pack(side=tk.RIGHT, fill=tk.Y)
        self.tree.pack(fill=tk.BOTH, expand=True)

        self.tree.bind('<<TreeviewSelect>>', self._on_tree_select)
        self.tree.bind('<Double-Button-1>',  lambda _: self.scroll_to_field())

    def _build_action_buttons(self, parent):
        bar = ctk.CTkFrame(parent, fg_color='transparent')
        bar.pack(fill=tk.X, padx=8, pady=(2, 10))
        self._btn(bar, "Delete  (Del)", self.delete_field, kind='danger',
                  width=112, height=30, font=self.ui_font_sm).pack(side=tk.LEFT, padx=3)
        self._btn(bar, "Jump to Field", self.scroll_to_field,
                  width=112, height=30, font=self.ui_font_sm).pack(side=tk.LEFT, padx=3)
        self._btn(bar, "Clear All", self.clear_all,
                  width=88, height=30, font=self.ui_font_sm).pack(side=tk.LEFT, padx=3)

    def _build_detail_pane(self, parent):
        ctk.CTkLabel(parent, text="Inspector", font=self.ui_font_bold,
                     text_color=self._tok('accent')).pack(
                         anchor='w', padx=12, pady=(10, 2))

        controls = ctk.CTkFrame(parent, fg_color='transparent')
        controls.pack(fill=tk.X, padx=10, pady=(0, 4))

        self._fmt_var = tk.StringVar(value='Integer')
        ctk.CTkOptionMenu(
            controls, values=self._INSPECT_FORMATS, variable=self._fmt_var,
            command=lambda _v: self._refresh_inspector(),
            font=self.ui_font_sm, width=120, height=28).pack(side=tk.LEFT)

        self._endian_var = tk.StringVar(value='LE')
        ctk.CTkSegmentedButton(
            controls, values=['LE', 'BE'], variable=self._endian_var,
            command=lambda _v: self._refresh_inspector(),
            font=self.ui_font_sm, width=72, height=28).pack(side=tk.LEFT, padx=6)

        self._signed_sw = ctk.CTkSwitch(
            controls, text="Signed", command=self._refresh_inspector,
            font=self.ui_font_sm)
        self._signed_sw.pack(side=tk.LEFT, padx=(6, 0))

        holder = ctk.CTkFrame(parent, fg_color='transparent')
        holder.pack(fill=tk.BOTH, expand=True, padx=8, pady=(0, 8))

        self._detail_text = tk.Text(
            holder, font=(self.mono_family, self._font_size(10)),
            bd=0, relief='flat', highlightthickness=0,
            state=tk.DISABLED, wrap=tk.NONE)
        dsb = ctk.CTkScrollbar(holder, command=self._detail_text.yview)
        hsb = ctk.CTkScrollbar(holder, orientation='horizontal',
                               command=self._detail_text.xview)
        self._detail_text.configure(yscrollcommand=dsb.set, xscrollcommand=hsb.set)
        dsb.pack(side=tk.RIGHT,  fill=tk.Y)
        hsb.pack(side=tk.BOTTOM, fill=tk.X)
        self._detail_text.pack(fill=tk.BOTH, expand=True)
        self._clear_detail()

    # ── Keyboard bindings ────────────────────────────────────────────────────

    def _bind_keys(self):
        self.root.bind('<Control-o>', lambda _: self.open_file())
        self.root.bind('<Control-s>', lambda _: self.save_annotations())
        self.root.bind('<Control-l>', lambda _: self.load_annotations())
        self.root.bind('<Control-S>', lambda _: self.save_binary())
        self.root.bind('<Return>',    lambda _: self._submit_field_form())
        self.root.bind('<Delete>',    lambda _: self.delete_field())
        for seq in ('<Control-plus>', '<Control-equal>', '<Control-KP_Add>'):
            self.root.bind(seq, self._zoom_in)
        for seq in ('<Control-minus>', '<Control-underscore>', '<Control-KP_Subtract>'):
            self.root.bind(seq, self._zoom_out)

    # Scaling

    def _set_ui_scale(self, scale: float) -> str:
        scale = round(max(ZOOM_MIN, min(ZOOM_MAX, scale)), 2)
        if scale == self._ui_scale:
            return 'break'

        self._ui_scale = scale
        ctk.set_widget_scaling(scale)
        self._retheme_native(self._mode)
        if self.data is not None:
            self._render()
        else:
            self._draw_selection()
            self._draw_edit_cursor()
        self._status_var.set(f"Scale: {int(round(scale * 100))}%")
        return 'break'

    def _zoom_in(self, _event=None) -> str:
        return self._set_ui_scale(self._ui_scale + ZOOM_STEP)

    def _zoom_out(self, _event=None) -> str:
        return self._set_ui_scale(self._ui_scale - ZOOM_STEP)

    # Embedded Python console

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
            self._console_input.focus_set()
            return
        if not self._console_visible:
            self._main_vpaned.add(
                self._console_frame, minsize=self._scaled_int(180, 120),
                stretch='never')
            self._console_visible = True
            self._python_btn.configure(text="Python On")
            self._console_pop_btn.configure(text="Pop Out",
                                            command=self._float_python_console)
        self._console_input.focus_set()

    def _hide_python_console(self):
        if self._console_visible:
            self._main_vpaned.forget(self._console_frame)
            self._console_visible = False
        if self._console_floating:
            self._dock_python_console(show=False)
        self._python_btn.configure(text="Python")

    def _float_python_console(self):
        if self._console_floating:
            return
        if self._console_visible:
            self._main_vpaned.forget(self._console_frame)
            self._console_visible = False
        self._console_frame.destroy()

        self._console_window = ctk.CTkToplevel(self.root)
        self._console_window.title("Python Console")
        self._console_window.geometry("900x360")
        self._console_window.minsize(520, 220)
        self._console_window.protocol("WM_DELETE_WINDOW", self._hide_python_console)
        self._console_frame = self._create_python_console_frame(self._console_window)
        self._console_frame.pack(fill=tk.BOTH, expand=True, padx=8, pady=8)
        self._console_floating = True
        self._python_btn.configure(text="Python Out")
        self._console_pop_btn.configure(text="Dock", command=self._dock_python_console)
        self._console_input.focus_set()

    def _dock_python_console(self, show: bool = True):
        if self._console_floating:
            self._console_frame.pack_forget()
            if self._console_window is not None:
                self._console_window.destroy()
            self._console_window = None
            self._console_floating = False
            self._console_frame = self._create_python_console_frame(self._console_dock_parent)
            self._pane_minsizes.append((self._console_dock_parent, self._console_frame, 180))
        self._console_pop_btn.configure(text="Pop Out",
                                        command=self._float_python_console)
        if show:
            self._show_python_console()

    def _console_drag_start(self, event):
        self._console_drag_origin = (event.x_root, event.y_root)
        self._console_dragging = False
        return 'break'

    def _console_drag_motion(self, event):
        if self._console_drag_origin is None:
            return 'break'
        ox, oy = self._console_drag_origin
        dx = event.x_root - ox
        dy = event.y_root - oy
        if not self._console_dragging and abs(dx) + abs(dy) < 16:
            return 'break'
        self._console_dragging = True
        if not self._console_floating:
            self._float_python_console()
        if self._console_window is not None:
            width = max(self._console_window.winfo_width(), 520)
            height = max(self._console_window.winfo_height(), 220)
            self._console_window.geometry(
                f"{width}x{height}+{event.x_root - 80}+{event.y_root - 18}")
        return 'break'

    def _console_drag_release(self, event):
        if self._console_dragging and self._console_floating:
            rx = self.root.winfo_rootx()
            ry = self.root.winfo_rooty()
            rw = self.root.winfo_width()
            rh = self.root.winfo_height()
            if rx <= event.x_root <= rx + rw and ry <= event.y_root <= ry + rh:
                self._dock_python_console()
        self._console_drag_origin = None
        self._console_dragging = False
        return 'break'

    def _clear_console(self):
        self._console_output_cache = ""
        self._console_text.configure(state=tk.NORMAL)
        self._console_text.delete('1.0', tk.END)
        self._console_text.configure(state=tk.DISABLED)

    def _append_console(self, text: str):
        self._console_output_cache += text
        self._console_text.configure(state=tk.NORMAL)
        self._console_text.insert(tk.END, text)
        self._console_text.see(tk.END)
        self._console_text.configure(state=tk.DISABLED)

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

    def _console_history_prev(self, _event=None):
        if not self._console_history:
            return 'break'
        if self._console_history_index is None:
            self._console_history_index = len(self._console_history) - 1
        else:
            self._console_history_index = max(0, self._console_history_index - 1)
        self._console_input_var.set(self._console_history[self._console_history_index])
        self._console_input.icursor(tk.END)
        return 'break'

    def _console_history_next(self, _event=None):
        if self._console_history_index is None:
            return 'break'
        self._console_history_index += 1
        if self._console_history_index >= len(self._console_history):
            self._console_history_index = None
            self._console_input_var.set('')
        else:
            self._console_input_var.set(self._console_history[self._console_history_index])
        self._console_input.icursor(tk.END)
        return 'break'

    def _execute_console_line(self, _event=None):
        line = self._console_input_var.get()
        prompt = '...' if self._console_more else '>>>'
        self._append_console(f"{prompt} {line}\n")
        if line.strip():
            self._console_history.append(line)
        self._console_history_index = None
        self._console_input_var.set('')

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
        self._console_prompt_var.set('...' if self._console_more else '>>>')
        if not self._console_more:
            self._sync_console_buffer()
            self._after_console_command(before, before_len)
        return 'break'

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
        self._status_var.set(
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

    # ── Appearance ─────────────────────────────────────────────────────────────

    def _on_appearance_change(self, choice: str):
        mode = choice.lower()
        ctk.set_appearance_mode(mode)
        self._retheme_native(mode)

    # ── Color helpers ────────────────────────────────────────────────────────

    def _set_color(self, color: str):
        self._current_color = color
        self._swatch.configure(fg_color=color)

    def _pick_custom_color(self):
        result = colorchooser.askcolor(color=self._current_color, title="Pick Field Color")
        if result[1]:
            color = result[1]
            self._remember_custom_color(color)
            self._set_color(color)

    def _remember_custom_color(self, color: str):
        color = color.lower()
        if color in [c.lower() for c in PALETTE + self._custom_colors]:
            return
        self._custom_colors.append(color)
        b = ctk.CTkButton(self._palette_frame, text='', width=22, height=22,
                          corner_radius=6, fg_color=color, hover_color=color,
                          border_width=0, command=lambda c=color: self._set_color(c))
        b.pack(side=tk.LEFT, padx=2)
        self._pal_btns.append(b)

    # ── File I/O ─────────────────────────────────────────────────────────────

    def open_file(self):
        path = filedialog.askopenfilename(
            title="Open Binary File",
            filetypes=[("All files", "*"),
                       ("Binary",    "*.bin *.raw *.dat"),
                       ("ELF",       "*.elf *.so *.o"),
                       ("PCAP",      "*.pcap *.pcapng")])
        if not path:
            return
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
            self._status_var.set(
                f"{os.path.basename(path)}  |  {sz} bytes  ({hex(sz)})")
            self._render()
        except Exception as exc:
            messagebox.showerror("Open Error", str(exc))

    def save_annotations(self):
        if not self.fields:
            messagebox.showinfo("Nothing to save", "No fields defined yet.")
            return
        default = (os.path.basename(self.filepath) if self.filepath else "annotations")
        path = filedialog.asksaveasfilename(
            title="Save Annotations",
            defaultextension=".json",
            initialfile=f"{default}.fields.json",
            filetypes=[("JSON", "*.json")])
        if not path:
            return
        with open(path, 'w') as f:
            json.dump({
                'filepath': self.filepath,
                'fields': self.fields,
                'custom_colors': self._custom_colors,
            }, f, indent=2)
        self._status_var.set(
            f"Saved {len(self.fields)} field(s) → {os.path.basename(path)}")

    def load_annotations(self):
        path = filedialog.askopenfilename(
            title="Load Annotations",
            filetypes=[("JSON", "*.json"), ("All files", "*")])
        if not path:
            return
        try:
            with open(path) as f:
                saved = json.load(f)
        except Exception as exc:
            messagebox.showerror("Load Error", str(exc))
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
        self._update_field_btn.configure(state=tk.DISABLED)
        self._rebuild_tree()
        if self.data:
            self._render()
        self._status_var.set(
            f"Loaded {len(self.fields)} field(s) from {os.path.basename(path)}")

    def save_binary(self):
        if self.data is None:
            messagebox.showinfo("No Data", "Open a binary file first.")
            return
        if self.filepath:
            stem, ext = os.path.splitext(os.path.basename(self.filepath))
        else:
            stem, ext = "output", ""
        path = filedialog.asksaveasfilename(
            title="Save Binary As",
            initialfile=f"{stem}_edited{ext}",
            filetypes=[("All files", "*"),
                       ("Binary",    "*.bin"),
                       ("Raw",       "*.raw")])
        if not path:
            return
        try:
            with open(path, 'wb') as f:
                f.write(bytes(self.data))
            self._modified = False
            self._update_title()
            self._status_var.set(f"Binary saved → {os.path.basename(path)}")
        except Exception as exc:
            messagebox.showerror("Save Error", str(exc))

    def _update_title(self):
        fname = os.path.basename(self.filepath) if self.filepath else ""
        mod   = "  [modified]" if self._modified else ""
        self.root.title(f"Binary Field Annotator  {fname}{mod}")

    # ── Hex rendering ────────────────────────────────────────────────────────

    @property
    def bpr(self) -> int:
        return int(self._bpr_var.get())

    def _rerender(self):
        if self.data is not None:
            self._render()

    def _render(self):
        bpr = self.bpr
        self.hex_text.config(state=tk.NORMAL)
        self.hex_text.delete('1.0', tk.END)

        lines = []
        for i in range(0, len(self.data), bpr):
            chunk = self.data[i:i + bpr]
            h = ''.join(f' {b:02X} ' for b in chunk)
            a = ''.join(chr(b) if 32 <= b < 127 else '.' for b in chunk)
            lines.append(f"{i:08X}  {h:<{bpr * HEX_CELL_COLS}} |{a}|")

        self.hex_text.insert('1.0', '\n'.join(lines))
        self.hex_text.config(state=tk.DISABLED)
        self._apply_all_tags()
        self._apply_edited_tags()  # above field tags
        self._draw_selection()     # pending field selection, above edited
        self._draw_edit_cursor()   # above everything

    def _apply_all_tags(self):
        for tag in list(self.hex_text.tag_names()):
            if tag.startswith('f:'):
                self.hex_text.tag_delete(tag)
        for fld in self.fields:
            self._apply_tag(fld)

    def _tag_range(self, tag: str, start: int, end: int):
        """tag_add over the hex + ascii cells spanning byte offsets [start, end]."""
        bpr = self.bpr
        ascii_base = OFFSET_COLS + bpr * HEX_CELL_COLS + 2
        for row in range(start // bpr, end // bpr + 1):
            row_base  = row * bpr
            col_start = max(start, row_base) - row_base
            col_end   = min(end,   row_base + bpr - 1) - row_base
            line      = row + 1

            hc_s = OFFSET_COLS + col_start * HEX_CELL_COLS
            hc_e = OFFSET_COLS + (col_end + 1) * HEX_CELL_COLS
            ac_s = ascii_base + col_start
            ac_e = ascii_base + col_end + 1

            self.hex_text.tag_add(tag, f"{line}.{hc_s}", f"{line}.{hc_e}")
            self.hex_text.tag_add(tag, f"{line}.{ac_s}", f"{line}.{ac_e}")

    def _apply_tag(self, fld: dict):
        if self.data is None:
            return
        tag   = f"f:{fld['id']}"
        bg    = fld['color']
        start = fld['start']
        end   = min(fld['end'], len(self.data) - 1)
        self.hex_text.tag_configure(tag, background=bg, foreground=_contrast_fg(bg))
        self._tag_range(tag, start, end)

    # ── Hex view interaction ─────────────────────────────────────────────────

    def _click_to_offset(self, event) -> int | None:
        if self.data is None:
            return None
        idx  = self.hex_text.index(f"@{event.x},{event.y}")
        line, col = map(int, idx.split('.'))
        bpr  = self.bpr
        base = (line - 1) * bpr

        hz_end   = OFFSET_COLS + bpr * HEX_CELL_COLS
        az_start = OFFSET_COLS + bpr * HEX_CELL_COLS + 2
        az_end   = az_start + bpr

        if OFFSET_COLS <= col < hz_end:
            byte_col = (col - OFFSET_COLS) // HEX_CELL_COLS
        elif az_start <= col < az_end:
            byte_col = col - az_start
        else:
            return None

        off = base + byte_col
        return off if 0 <= off < len(self.data) else None

    def _set_selection(self, a: int, b: int):
        """Set start/end offsets and the live highlight from two endpoints."""
        lo, hi = (a, b) if a <= b else (b, a)
        self._sel_range = (lo, hi)
        self._start_var.set(hex(lo))
        self._end_var.set(hex(hi))
        self._draw_selection()
        self._inspect_mode = 'sel'
        self._refresh_inspector()

    def _clear_selection(self):
        self._sel_range = None
        self._drag_anchor = None
        self._dragging = False
        self.hex_text.tag_remove('rangesel', '1.0', tk.END)
        if self._inspect_mode == 'sel':
            self._inspect_mode = None
            self._clear_detail()

    def _draw_selection(self):
        self.hex_text.tag_remove('rangesel', '1.0', tk.END)
        if self._sel_range is None or self.data is None:
            return
        lo, hi = self._sel_range
        lo = max(0, lo)
        hi = min(hi, len(self.data) - 1)
        if lo > hi:
            return
        self._tag_range('rangesel', lo, hi)
        self.hex_text.tag_raise('rangesel')
        if self._edit_mode:
            self.hex_text.tag_raise('edit_cursor')

    def _on_hex_press(self, event):
        off = self._click_to_offset(event)
        if off is None:
            # Clicked a non-byte area (offset column, the hex/ASCII gap, or the
            # empty space below the data): dismiss any pending mouse selection.
            # Field colors and the edited-byte highlight are separate tags and
            # are left intact.
            if not self._edit_mode:
                self._clear_selection()
                self._click_hint.configure(
                    text="Drag in hex view to select a field range  ·  Shift+Click to extend",
                    text_color='#ffd93d')
            return 'break'
        if self._edit_mode:
            self._set_edit_cursor(off)
            self.hex_text.focus_set()
            return 'break'
        # Annotation mode: anchor a new selection at this byte
        self._drag_anchor = off
        self._dragging = False
        self._set_selection(off, off)
        self._click_hint.configure(
            text=f"Selecting… start={hex(off)}  (drag to extend)",
            text_color='#ffd93d')
        return 'break'

    def _on_hex_drag(self, event):
        if self._edit_mode or self._drag_anchor is None:
            return
        off = self._click_to_offset(event)
        if off is None:
            return 'break'
        self._dragging = True
        self._set_selection(self._drag_anchor, off)
        lo, hi = self._sel_range
        self._click_hint.configure(
            text=f"Selecting… {hex(lo)}–{hex(hi)}  ({hi - lo + 1} bytes)",
            text_color='#ff6b6b')
        return 'break'

    def _on_hex_release(self, event):
        if self._edit_mode or self._drag_anchor is None:
            return
        off = self._click_to_offset(event)
        if off is not None:
            self._set_selection(self._drag_anchor, off)
        if self._sel_range is not None:
            lo, hi = self._sel_range
            n = hi - lo + 1
            self._click_hint.configure(
                text=f"Selected {hex(lo)}–{hex(hi)}  ({n} byte{'s' if n != 1 else ''}) "
                     f"— name it, then Add Field",
                text_color='#6bcb77')
        self._drag_anchor = None
        self._dragging = False
        return 'break'

    def _on_hex_shift_click(self, event):
        """Shift+Click extends the current selection to the clicked byte
        (lets you select ranges larger than the viewport: click start,
        scroll, then Shift+Click the end)."""
        if self._edit_mode:
            return self._on_hex_press(event)
        off = self._click_to_offset(event)
        if off is None:
            return 'break'
        anchor = self._sel_range[0] if self._sel_range is not None else off
        self._drag_anchor = anchor
        self._set_selection(anchor, off)
        lo, hi = self._sel_range
        self._click_hint.configure(
            text=f"Extended to {hex(lo)}–{hex(hi)}  ({hi - lo + 1} bytes)",
            text_color='#6bcb77')
        return 'break'

    def _on_hex_hover(self, event):
        off = self._click_to_offset(event)
        if off is None or self.data is None:
            return
        b     = self.data[off]
        names = [f['name'] for f in self.fields if f['start'] <= off <= f['end']]
        field_str = f"   [{', '.join(names)}]" if names else ""
        self._hover_label.configure(
            text=f"  Off: {hex(off)} ({off})   "
                 f"Byte: 0x{b:02X} ({b:3d}) "
                 f"'{chr(b) if 32 <= b < 127 else '.'}'"
                 f"{field_str}")

    # ── Inline hex editing ───────────────────────────────────────────────────

    def _toggle_edit_mode(self):
        self._edit_mode = bool(self._edit_switch.get())
        if self._edit_mode:
            self._clear_selection()
            self._click_hint.configure(
                text="HEX EDIT: click a byte, type 2 hex digits to overwrite",
                text_color='#ff6b6b')
            self._status_var.set(
                "Hex Edit mode — click to position cursor, type hex digits, "
                "arrows to navigate, Esc to exit")
        else:
            self._set_edit_cursor(None)
            self._click_hint.configure(
                text="Drag in hex view to select a field range  ·  Shift+Click to extend",
                text_color='#ffd93d')
            self._status_var.set("Hex Edit mode off")

    def _set_edit_cursor(self, offset: int | None):
        self._edit_cursor = offset
        self._edit_nibble = 0
        self._draw_edit_cursor()
        if offset is not None and self.data is not None:
            b = self.data[offset]
            self._status_var.set(
                f"Edit @ {hex(offset)}  current: 0x{b:02X} ({b})  — type high nibble")

    def _draw_edit_cursor(self):
        self.hex_text.tag_remove('edit_cursor', '1.0', tk.END)
        if self._edit_cursor is None or self.data is None or not self._edit_mode:
            return

        off  = self._edit_cursor
        bpr  = self.bpr
        row  = off // bpr + 1
        col  = off % bpr
        ascii_base = OFFSET_COLS + bpr * HEX_CELL_COLS + 2

        # High nibble position is hc_start, low nibble is hc_start+1
        hc_start = OFFSET_COLS + col * HEX_CELL_COLS + 1
        if self._edit_nibble == 0:
            hc_s, hc_e = hc_start, hc_start + 2      # whole byte
        else:
            hc_s, hc_e = hc_start + 1, hc_start + 2  # low nibble only

        ac_s = ascii_base + col
        ac_e = ac_s + 1

        self.hex_text.tag_add('edit_cursor', f'{row}.{hc_s}', f'{row}.{hc_e}')
        self.hex_text.tag_add('edit_cursor', f'{row}.{ac_s}', f'{row}.{ac_e}')
        self.hex_text.tag_raise('edit_cursor')
        self.hex_text.see(f'{row}.{hc_start}')

    def _move_edit_cursor(self, delta: int):
        if self._edit_cursor is None or self.data is None:
            return
        new = self._edit_cursor + delta
        if 0 <= new < len(self.data):
            self._edit_cursor = new
            self._edit_nibble = 0
            b = self.data[new]
            self._status_var.set(
                f"Edit @ {hex(new)}  current: 0x{b:02X} ({b})  — type high nibble")
        self._draw_edit_cursor()

    def _byte_indices(self, off: int) -> tuple[int, int, int]:
        """Return (row, hex_start_col, ascii_col) for a byte offset."""
        bpr = self.bpr
        row = off // bpr + 1
        col = off % bpr
        ascii_base = OFFSET_COLS + bpr * HEX_CELL_COLS + 2
        return row, OFFSET_COLS + col * HEX_CELL_COLS + 1, ascii_base + col

    def _tag_byte(self, tag: str, off: int):
        row, hc_s, ac_s = self._byte_indices(off)
        self.hex_text.tag_add(tag, f'{row}.{hc_s - 1}', f'{row}.{hc_s + 3}')
        self.hex_text.tag_add(tag, f'{row}.{ac_s}', f'{row}.{ac_s + 1}')

    def _apply_edited_tags(self):
        """Re-paint the edited-byte highlight across the whole buffer."""
        self.hex_text.tag_remove('edited', '1.0', tk.END)
        if self.data is None:
            return
        for off in self._edited:
            if 0 <= off < len(self.data):
                self._tag_byte('edited', off)
        self.hex_text.tag_raise('edited')

    def _write_byte(self, off: int, value: int):
        """Patch one byte and repaint only its cell — no full re-render."""
        self.data[off] = value
        self._edited.add(off)
        self._modified = True
        self._update_title()

        row, hc_s, ac_s = self._byte_indices(off)
        ch = chr(value) if 32 <= value < 127 else '.'
        self.hex_text.config(state=tk.NORMAL)
        self.hex_text.replace(f'{row}.{hc_s}', f'{row}.{hc_s + 2}', f'{value:02X}')
        self.hex_text.replace(f'{row}.{ac_s}', f'{row}.{ac_s + 1}', ch)
        self.hex_text.config(state=tk.DISABLED)

        # replace() drops tags on the new chars, so re-mark this byte as edited
        self._tag_byte('edited', off)
        self.hex_text.tag_raise('edited')
        self.hex_text.tag_raise('edit_cursor')

    def _on_hex_key(self, event) -> str:
        # Always swallow keys when edit mode is active and cursor is set,
        # so nothing leaks to the root-level bindings (Delete → delete_field, etc.)
        if not self._edit_mode or self._edit_cursor is None or self.data is None:
            return ''

        key  = event.keysym
        char = event.char.upper() if event.char else ''

        if key in ('Right', 'Tab'):
            self._move_edit_cursor(1)
        elif key == 'Left':
            if self._edit_nibble == 1:
                # Cancel partial nibble, stay on same byte
                self._edit_nibble = 0
                self._draw_edit_cursor()
            else:
                self._move_edit_cursor(-1)
        elif key == 'BackSpace':
            self._move_edit_cursor(-1)
        elif key == 'Up':
            self._move_edit_cursor(-self.bpr)
        elif key == 'Down':
            self._move_edit_cursor(self.bpr)
        elif key == 'Escape':
            self._set_edit_cursor(None)
        elif char in '0123456789ABCDEF':
            nib = int(char, 16)
            off = self._edit_cursor
            cur = self.data[off]
            if self._edit_nibble == 0:
                # Write high nibble, keep existing low nibble
                self._write_byte(off, (nib << 4) | (cur & 0x0F))
                self._edit_nibble = 1
                self._draw_edit_cursor()   # narrow cursor to the low nibble
                self._status_var.set(
                    f"Edit @ {hex(off)}: {char}_ — type low nibble")
            else:
                # Write low nibble, then advance to the next byte
                new = (cur & 0xF0) | nib
                self._write_byte(off, new)
                self._move_edit_cursor(1)  # redraws cursor on the next byte
                self._status_var.set(
                    f"Wrote 0x{new:02X} @ {hex(off)}  — type high nibble")

        return 'break'  # prevent all default Text-widget key handling

    # ── Byte editor dialog (right-click) ─────────────────────────────────────

    def _on_hex_right_click(self, event):
        off = self._click_to_offset(event)
        if off is None:
            return
        t = THEME[self._mode]
        menu = tk.Menu(self.root, tearoff=0, bd=0,
                       bg=t['card'], fg=t['text'],
                       activebackground=t['selection'], activeforeground=t['text'],
                       font=(self.mono_family, self._font_size(10)))
        menu.add_command(
            label=f"  Edit byte @ {hex(off)}  (0x{self.data[off]:02X} / {self.data[off]})",
            command=lambda: self._open_byte_editor(off))
        menu.tk_popup(event.x_root, event.y_root)

    def _open_byte_editor(self, offset: int):
        current = self.data[offset]

        dlg = ctk.CTkToplevel(self.root)
        dlg.title(f"Edit Byte @ {hex(offset)}")
        dlg.resizable(False, False)
        dlg.transient(self.root)

        dlg.geometry("340x250")
        dlg.update_idletasks()
        px = self.root.winfo_x() + self.root.winfo_width()  // 2 - 170
        py = self.root.winfo_y() + self.root.winfo_height() // 2 - 125
        dlg.geometry(f"340x250+{px}+{py}")

        ctk.CTkLabel(dlg, text=f"Offset:  {hex(offset)}  ({offset})",
                     font=self.mono_font, text_color=self._tok('accent'),
                     anchor='w').pack(padx=18, pady=(16, 2), fill=tk.X)
        ctk.CTkLabel(dlg, text=f"Current: 0x{current:02X}  ({current})",
                     font=self.mono_font, text_color=self._tok('muted'),
                     anchor='w').pack(padx=18, pady=(0, 10), fill=tk.X)

        hex_var = tk.StringVar(value=f'{current:02X}')
        dec_var = tk.StringVar(value=str(current))

        r1 = ctk.CTkFrame(dlg, fg_color='transparent')
        r1.pack(fill=tk.X, padx=18, pady=4)
        ctk.CTkLabel(r1, text="Hex", width=40, anchor='w',
                     font=self.ui_font_sm).pack(side=tk.LEFT)
        hex_entry = ctk.CTkEntry(r1, textvariable=hex_var, font=self.mono_font, width=130)
        hex_entry.pack(side=tk.LEFT)

        r2 = ctk.CTkFrame(dlg, fg_color='transparent')
        r2.pack(fill=tk.X, padx=18, pady=4)
        ctk.CTkLabel(r2, text="Dec", width=40, anchor='w',
                     font=self.ui_font_sm).pack(side=tk.LEFT)
        ctk.CTkEntry(r2, textvariable=dec_var, font=self.mono_font, width=130).pack(side=tk.LEFT)

        _lock = [False]

        def _hex_changed(*_):
            if _lock[0]:
                return
            raw = hex_var.get().strip()
            if raw.lower().startswith('0x'):
                raw = raw[2:]
            try:
                v = int(raw or '0', 16)
                if 0 <= v <= 255:
                    _lock[0] = True
                    dec_var.set(str(v))
                    _lock[0] = False
            except ValueError:
                pass

        def _dec_changed(*_):
            if _lock[0]:
                return
            try:
                v = int(dec_var.get().strip())
                if 0 <= v <= 255:
                    _lock[0] = True
                    hex_var.set(f'{v:02X}')
                    _lock[0] = False
            except ValueError:
                pass

        hex_var.trace_add('write', _hex_changed)
        dec_var.trace_add('write', _dec_changed)

        def _apply():
            raw = hex_var.get().strip()
            if raw.lower().startswith('0x'):
                raw = raw[2:]
            try:
                v = int(raw or '0', 16)
                if not (0 <= v <= 255):
                    raise ValueError
            except ValueError:
                messagebox.showerror("Invalid Value",
                                     "Enter a hex value between 00 and FF.",
                                     parent=dlg)
                return
            self.data[offset] = v
            self._edited.add(offset)
            self._modified = True
            self._update_title()
            self._render()
            self._status_var.set(
                f"Byte @ {hex(offset)} changed: 0x{current:02X} → 0x{v:02X}")
            dlg.destroy()

        def _cancel():
            dlg.destroy()

        btns = ctk.CTkFrame(dlg, fg_color='transparent')
        btns.pack(fill=tk.X, padx=18, pady=(18, 14))
        self._btn(btns, "Apply", _apply, kind='accent', width=96,
                  font=self.ui_font_bold).pack(side=tk.LEFT, padx=(0, 8))
        self._btn(btns, "Cancel", _cancel, width=96).pack(side=tk.LEFT)

        dlg.bind('<Return>', lambda _: _apply())
        dlg.bind('<Escape>', lambda _: _cancel())
        # CTkToplevel needs to be viewable before grabbing input focus.
        dlg.after(120, lambda: (dlg.grab_set(), hex_entry.focus_set()))

    # ── Field management ─────────────────────────────────────────────────────

    def _parse_field_form(self) -> dict | None:
        if self.data is None:
            messagebox.showwarning("No File", "Open a binary file first.")
            return None
        name = self._name_var.get().strip()
        if not name:
            messagebox.showwarning("Name Required", "Enter a field name.")
            return None
        try:
            start = int(self._start_var.get(), 0)
            end   = int(self._end_var.get(),   0)
        except ValueError:
            messagebox.showerror("Invalid Offset",
                                  "Start/End must be integers (e.g. 42 or 0x2a).")
            return None
        if start > end:
            start, end = end, start
        if start < 0:
            messagebox.showwarning("Out of Range", "Start must be 0 or greater.")
            return None
        if end >= len(self.data):
            messagebox.showwarning("Out of Range",
                                    f"End {hex(end)} exceeds file size "
                                    f"{hex(len(self.data) - 1)}.")
            return None
        return {
            'name':  name,
            'start': start,
            'end':   end,
            'color': self._current_color,
            'note':  self._note_var.get().strip(),
        }

    def _submit_field_form(self):
        if self._editing_field_id is not None:
            return self.update_field()
        self.add_field()
        return 'break'

    def _field_by_id(self, fid: int) -> dict | None:
        return next((f for f in self.fields if f['id'] == fid), None)

    def _reset_field_form(self):
        self._editing_field_id = None
        self._update_field_btn.configure(state=tk.DISABLED)
        self._name_var.set('')
        self._start_var.set('0x0')
        self._end_var.set('0x0')
        self._note_var.set('')
        sel = self.tree.selection()
        if sel:
            self.tree.selection_remove(*sel)
        if not self._edit_mode:
            self._click_hint.configure(
                text="Drag in hex view to select a field range  Â·  Shift+Click to extend",
                text_color='#ffd93d')
        return 'break'

    def _update_tree_item(self, fld: dict):
        length = fld['end'] - fld['start'] + 1
        color = fld['color']
        values = (fld['name'], hex(fld['start']), hex(fld['end']),
                  length, fld.get('note', ''))
        iid = str(fld['id'])
        if self.tree.exists(iid):
            self.tree.item(iid, values=values, tags=(color,))
        else:
            self.tree.insert('', tk.END, iid=iid, values=values, tags=(color,))
        self.tree.tag_configure(color, background=color,
                                foreground=_contrast_fg(color))

    def _clear_field_tag(self, fid: int):
        tag = f"f:{fid}"
        if tag in self.hex_text.tag_names():
            self.hex_text.tag_delete(tag)

    def add_field(self):
        parsed = self._parse_field_form()
        if parsed is None:
            return

        fld = {'id': self._next_id, **parsed}
        self._next_id += 1
        self.fields.append(fld)
        self._update_tree_item(fld)

        if self.data is not None:
            self.hex_text.config(state=tk.NORMAL)
            self._apply_tag(fld)
            self.hex_text.config(state=tk.DISABLED)

        try:
            idx = PALETTE.index(self._current_color)
            self._set_color(PALETTE[(idx + 1) % len(PALETTE)])
        except ValueError:
            pass

        self._reset_field_form()
        self._clear_selection()
        # Show the freshly created field in the inspector as confirmation.
        self._inspect_mode = 'field'
        self._inspect_field_id = fld['id']
        self._refresh_inspector()
        if not self._edit_mode:
            self._click_hint.configure(
                text="Drag in hex view to select a field range  ·  Shift+Click to extend",
                text_color='#ffd93d')

    def update_field(self):
        if self._editing_field_id is None:
            sel = self.tree.selection()
            if not sel:
                return 'break'
            self._editing_field_id = int(sel[0])
        fld = self._field_by_id(self._editing_field_id)
        if fld is None:
            self._editing_field_id = None
            self._update_field_btn.configure(state=tk.DISABLED)
            return 'break'

        parsed = self._parse_field_form()
        if parsed is None:
            return 'break'

        fid = fld['id']
        fld.update(parsed)
        self._update_tree_item(fld)
        if self.data is not None:
            self.hex_text.config(state=tk.NORMAL)
            self._clear_field_tag(fid)
            self._apply_tag(fld)
            self.hex_text.config(state=tk.DISABLED)
            self._apply_edited_tags()
            self._draw_selection()
            self._draw_edit_cursor()

        self.tree.selection_set(str(fid))
        self._inspect_mode = 'field'
        self._inspect_field_id = fid
        self._refresh_inspector()
        self._status_var.set(f"Updated field: {fld['name']}")
        return 'break'

    def delete_field(self):
        sel = self.tree.selection()
        if not sel:
            return
        fid = int(sel[0])
        self.fields = [f for f in self.fields if f['id'] != fid]
        self.tree.delete(sel[0])
        tag = f"f:{fid}"
        if tag in self.hex_text.tag_names():
            self.hex_text.tag_delete(tag)
        if self._inspect_mode == 'field' and self._inspect_field_id == fid:
            self._inspect_mode = None
        if self._editing_field_id == fid:
            self._editing_field_id = None
            self._update_field_btn.configure(state=tk.DISABLED)
        self._clear_detail()

    def clear_all(self):
        if not self.fields:
            return
        if not messagebox.askyesno("Clear All", "Delete all field annotations?"):
            return
        for fld in self.fields:
            tag = f"f:{fld['id']}"
            if tag in self.hex_text.tag_names():
                self.hex_text.tag_delete(tag)
        self.fields.clear()
        for item in self.tree.get_children():
            self.tree.delete(item)
        self._clear_selection()
        self._editing_field_id = None
        self._update_field_btn.configure(state=tk.DISABLED)
        self._inspect_mode = None
        self._clear_detail()

    def scroll_to_field(self):
        sel = self.tree.selection()
        if not sel:
            return
        fid   = int(sel[0])
        fld   = next((f for f in self.fields if f['id'] == fid), None)
        if fld:
            row = fld['start'] // self.bpr + 1
            self.hex_text.see(f"{row}.0")

    # ── Field detail pane ────────────────────────────────────────────────────

    def _on_tree_select(self, _event):
        sel = self.tree.selection()
        if not sel:
            return
        fid = int(sel[0])
        fld = self._field_by_id(fid)
        if fld is None:
            return
        self._editing_field_id = fid
        self._name_var.set(fld['name'])
        self._start_var.set(hex(fld['start']))
        self._end_var.set(hex(fld['end']))
        self._note_var.set(fld.get('note', ''))
        self._set_color(fld['color'])
        self._update_field_btn.configure(state=tk.NORMAL)
        self._click_hint.configure(
            text="Editing selected field. Change values, then Update Selected.",
            text_color='#6bcb77')
        self._inspect_mode = 'field'
        self._inspect_field_id = fid
        self._refresh_inspector()

    _INSPECT_FORMATS = ['Integer', 'Float', 'String', 'Hex', 'Binary', 'Bytes (dec)']

    def _interpret_lines(self, raw, fmt: str, endian: str, signed: bool) -> list[str]:
        """Render the selected bytes as the chosen single format."""
        bo = 'little' if endian == 'LE' else 'big'
        sc = '<' if endian == 'LE' else '>'
        n  = len(raw)

        if fmt == 'Integer':
            if n == 0:
                return ["(no bytes)"]
            if n > 64:
                return [f"Selection is {n} bytes — select ≤ 64 to read as one integer.",
                        "Use the Hex or Bytes view for large ranges."]
            val   = int.from_bytes(raw, bo, signed=signed)
            other = int.from_bytes(raw, bo, signed=not signed)
            sign  = '-' if val < 0 else ''
            return [
                f"{'int' if signed else 'uint'}{n * 8}  ({endian})",
                f"  dec : {val}",
                f"  hex : {sign}0x{abs(val):X}",
                f"  {'unsigned' if signed else 'signed'} : {other}",
            ]

        if fmt == 'Float':
            code = {2: 'e', 4: 'f', 8: 'd'}.get(n)
            if code is None:
                return [f"Select 2, 4, or 8 bytes for a float (have {n})."]
            width = {2: 'float16', 4: 'float32', 8: 'float64'}[n]
            val = struct.unpack(sc + code, bytes(raw))[0]
            return [f"{width}  ({endian})", f"  {val!r}"]

        if fmt == 'String':
            sample = bytes(raw[:4096])
            trunc  = '  …(truncated)' if n > 4096 else ''
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
        """Render the current inspect target (live selection or field) using
        the picked format / endianness / signedness."""
        if self.data is None:
            return
        note = None
        if self._inspect_mode == 'sel' and self._sel_range is not None:
            start, end = self._sel_range
            title = f"Selection  {hex(start)}–{hex(end)}"
        elif self._inspect_mode == 'field' and self._inspect_field_id is not None:
            fld = next((f for f in self.fields if f['id'] == self._inspect_field_id), None)
            if fld is None:
                self._clear_detail()
                return
            start, end = fld['start'], fld['end']
            title = f"Field “{fld['name']}”  {hex(start)}–{hex(end)}"
            note  = fld.get('note', '')
        else:
            self._clear_detail()
            return

        start = max(0, start)
        end   = min(end, len(self.data) - 1)
        if start > end:
            self._clear_detail()
            return

        raw    = self.data[start:end + 1]
        n      = len(raw)
        fmt    = self._fmt_var.get()
        endian = self._endian_var.get()
        signed = bool(self._signed_sw.get())

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
        self._detail_text.config(state=tk.NORMAL)
        self._detail_text.delete('1.0', tk.END)
        self._detail_text.insert('1.0', text)
        self._detail_text.config(state=tk.DISABLED)

    def _clear_detail(self):
        self._set_detail_text(
            "Drag bytes in the hex view, or click a field, to inspect them here.")

    def _rebuild_tree(self):
        for item in self.tree.get_children():
            self.tree.delete(item)
        for fld in self.fields:
            self._update_tree_item(fld)


# ── Entry point ───────────────────────────────────────────────────────────────

def main():
    ctk.set_appearance_mode("dark")
    ctk.set_default_color_theme("dark-blue")
    root = ctk.CTk()
    root.minsize(960, 640)
    BinaryFieldAnnotator(root)
    root.mainloop()


if __name__ == '__main__':
    main()
