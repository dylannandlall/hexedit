# AI Protocol Annotation Template

Use this template when asking an AI model to generate annotations for Hex Edit
(Binary Field Annotator). The final answer from the AI must be plain JSON only,
with no Markdown fences, comments, prose, or trailing commas.

## Prompt To Give The AI

You are generating a loadable annotation JSON file for Hex Edit (Binary Field
Annotator).

Inputs I will provide:

- A protocol specification or header layout.
- The binary file name or path, if known.
- The base offset where this protocol structure begins in the binary.
- Any known dynamic lengths, repeated fields, optional fields, or endianness.

Output requirements:

- Return exactly one JSON object.
- Do not include Markdown code fences.
- Do not include comments.
- Use decimal integer byte offsets for `start` and `end`.
- `start` and `end` are inclusive byte offsets from the beginning of the opened
  binary file.
- If the protocol header begins at a nonzero base offset, add that base offset
  to every field offset.
- Assign unique integer `id` values starting at 0 and increasing by 1.
- Use short, human-readable field names.
- Put useful interpretation details in `note`, such as width, endianness,
  bit layout, enum meanings, units, masks, or conditions.
- Use valid hex colors in `#RRGGBB` format.
- Do not generate fields for bytes that are not described by the specification.
- If a field length cannot be determined from the provided information, do not
  guess. Add a field only for the known fixed portion, and explain the missing
  dependency in `note`.
- If the specification has repeated elements, expand them only when the repeat
  count is known. Otherwise annotate the count/length field and explain the
  repeated region in `note`.

JSON schema to produce:

```json
{
  "filepath": "path/or/name/of/binary-or-null",
  "fields": [
    {
      "id": 0,
      "name": "Field Name",
      "start": 0,
      "end": 3,
      "color": "#ff6b6b",
      "note": "4 bytes, big endian. Explain meaning, enum, units, masks, or conditions."
    }
  ]
}
```

Use this color palette unless I ask for a different one:

- `#ff6b6b` red
- `#ffd93d` yellow
- `#6bcb77` green
- `#4d96ff` blue
- `#ff6bd6` magenta
- `#64ffda` cyan
- `#ff9a3c` orange
- `#c77dff` purple
- `#a8dadc` teal
- `#f9c74f` amber

Before producing the final JSON, internally verify:

- The JSON is syntactically valid.
- Every field has `id`, `name`, `start`, `end`, `color`, and `note`.
- All IDs are unique.
- For every field, `start <= end`.
- Offsets are inclusive and are absolute offsets within the opened binary.
- Adjacent fields do not accidentally overlap unless the protocol defines
  overlapping bit fields or alternate interpretations.
- Any overlap is explained in `note`.

## Example Request

Generate annotations for a packet header that starts at offset 0x20. The header
layout is:

- Magic: 4 bytes at relative offset 0x00, ASCII string.
- Version: 1 byte at relative offset 0x04.
- Flags: 1 byte at relative offset 0x05, bit 0 encrypted, bit 1 compressed.
- Payload length: 2 bytes at relative offset 0x06, little endian unsigned.

## Example Valid Output

```json
{
  "filepath": "example_packet.bin",
  "fields": [
    {
      "id": 0,
      "name": "Magic",
      "start": 32,
      "end": 35,
      "color": "#ff6b6b",
      "note": "4 byte ASCII magic value. Relative offset 0x00."
    },
    {
      "id": 1,
      "name": "Version",
      "start": 36,
      "end": 36,
      "color": "#ffd93d",
      "note": "1 byte protocol version. Relative offset 0x04."
    },
    {
      "id": 2,
      "name": "Flags",
      "start": 37,
      "end": 37,
      "color": "#6bcb77",
      "note": "1 byte bit field. bit0=encrypted, bit1=compressed. Relative offset 0x05."
    },
    {
      "id": 3,
      "name": "Payload Length",
      "start": 38,
      "end": 39,
      "color": "#4d96ff",
      "note": "uint16 little endian payload length in bytes. Relative offset 0x06."
    }
  ]
}
```

When saving the generated result, use a filename like:

```text
protocol_name.fields.json
```
