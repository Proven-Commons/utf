# Specification: utf

This library is a UTF-8 encoder and a validating decoder. It turns Unicode scalar values into bytes and back. A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, and the other files `bar.toml` lists.

Characters are Lean's `Char`, which holds exactly the Unicode scalar values: 0 to 0xD7FF and 0xE000 to 0x10FFFF. Bytes are `List UInt8`.

The sources are RFC 3629, *UTF-8, a transformation format of ISO 10646*, and Table 3-7, *Well-Formed UTF-8 Byte Sequences*, in section 3.9 of the Unicode Standard. The two describe the same encoding in different ways, and the proofs show that they agree.

## Encoding

`encode` writes each character in one to four bytes, by the table in section 3 of RFC 3629:

| Code points | Bytes |
|-------------|-------|
| U+0000 to U+007F | `0xxxxxxx` |
| U+0080 to U+07FF | `110xxxxx 10xxxxxx` |
| U+0800 to U+FFFF | `1110xxxx 10xxxxxx 10xxxxxx` |
| U+10000 to U+10FFFF | `11110xxx 10xxxxxx 10xxxxxx 10xxxxxx` |

The bits of the code point fill the `x` positions, the lowest bit last. Every list of characters can be encoded, so `encode` has no failure case.

## Decoding

`decode` returns the characters when its input is the encoding of a list of characters. It returns `none` otherwise, and it never skips or replaces a bad byte. So it refuses:

- overlong forms, which spend more bytes than a code point needs, such as `C0 AF` for `/`;
- surrogate halves, U+D800 to U+DFFF, such as `ED A0 80`, alone or in pairs;
- values past U+10FFFF, such as `F4 90 80 80`;
- the bytes 0xC0, 0xC1, and 0xF5 to 0xFF, which never start a valid sequence;
- the five- and six-byte forms of the original UTF-8;
- a continuation byte (0x80 to 0xBF) where a character should start;
- a lead byte followed by a byte that is not a continuation;
- a sequence cut short by the end of the input.

A byte order mark (`EF BB BF`) is read as the character U+FEFF, like any other character. The decoder does not strip it.

## Lean core

Lean core encodes and decodes UTF-8 inside `String`. Two statements tie this library to core, as core defines it:

- Core's `String.toUTF8`, as core defines it, writes the same bytes as `encode`.
- Core's `String.fromUTF8?` accepts exactly the bytes `decode` accepts, and reads the same characters.

At run time, core checks the bytes with C code (`lean_string_validate_utf8`), which no proof covers. The differential tests compare that C code with this decoder too.

## The command-line tool

`utf8 serve`, in `Main.lean`, answers requests from the differential tests, one per line. Its header comment gives the protocol.

- `decode` and `encode` requests are answered by the proved functions.
- `core` requests are answered by Lean core's `String.fromUTF8?`. They are there only so that the tests can compare core with this decoder.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given. The definitions the statements use are in `Spec/Defs.lean`. They are written from RFC 3629 and Table 3-7, and checked against the RFC's examples and against the first and last sequence of each row of the table and the bytes just outside its edges.

| Property | Theorem |
|----------|---------|
| The encoder writes each character as the table of RFC 3629, section 3, sets out. | `Spec.encode_eq` |
| `decode` returns `cs` exactly when the bytes are the encoding of `cs`, so every byte string it accepts has one reading, and it refuses everything listed above. | `Spec.decode_iff` |
| Decoding what the encoder wrote gives the characters back. | `Spec.decode_encode` |
| The decoder accepts exactly the byte sequences that Table 3-7 calls well formed. | `Spec.decode_wellFormed` |
| Lean core's `String.toUTF8`, as core defines it, writes the same bytes as the encoder. | `Spec.encode_toUTF8` |
| Lean core's `String.fromUTF8?`, as core defines it, agrees with the decoder. | `Spec.fromUTF8?_eq` |
| The examples of RFC 3629, section 7, both ways. | `Spec.rfc3629_examples` |
| The first and last code points of each length, those on either side of the surrogates, and the empty input. | `Spec.boundary_vectors` |
| A selection of malformed inputs, most of them from Markus Kuhn's UTF-8 decoder test file, and each byte from 0xF5 to 0xFF. Every case in that file follows from `Spec.decode_iff`, and the tests run them all. | `Spec.reject_vectors` |

Together, these fix every output.

- `encode` is fixed for every input.
- `decode` is fixed for every input.
- A decoder that accepted nothing would fail `Spec.decode_encode`.
- A decoder that accepted too much would fail `Spec.decode_iff`.

## Oracle

Python's strict `utf-8` codec, on every input. Lean core's `String.fromUTF8?` at run time is checked against the same answers.
