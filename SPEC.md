# Specification: utf

This library is a UTF-8 encoder, a validating decoder, and a lossy decoder. It turns Unicode scalar values into bytes and back. A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, and the other files `bar.toml` lists.

Characters are Lean's `Char`, which holds exactly the Unicode scalar values: 0 to 0xD7FF and 0xE000 to 0x10FFFF. Bytes are `List UInt8`.

The sources are RFC 3629, *UTF-8, a transformation format of ISO 10646*, and Table 3-7, *Well-Formed UTF-8 Byte Sequences*, in section 3.9 of the Unicode Standard. The two describe the same encoding in different ways, and the proofs show that they agree. The lossy decoder follows section 3.9.6 of the Unicode Standard, version 16.0, *U+FFFD Substitution of Maximal Subparts*.

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

## Lossy decoding

`decodeLossy` never fails. Where `decode` would give up, it puts one U+FFFD in place of the bad bytes and goes on. How many bytes one U+FFFD stands for is set by section 3.9.6 of the Unicode Standard:

- An offset is *unconvertible* when no well-formed sequence starts there (definition D93a).
- The *maximal subpart* at an unconvertible offset is the longest run of bytes from there that could still be the start of a well-formed sequence, or one byte if no run could (definition D93b).
- At an unconvertible offset, the maximal subpart becomes one U+FFFD, and decoding goes on after it. Everywhere else, the character there is read as `decode` reads it.

So `F0 9F 98 41` gives U+FFFD and `A`: the first three bytes could start a four-byte sequence, and `41` cannot continue it. `C0 AF` gives two U+FFFD, since `C0` never starts a well-formed sequence. A maximal subpart only goes on through continuation bytes (0x80 to 0xBF), which never start a character, so it never takes in the first byte of the text after it.

The Unicode Standard describes this practice but does not require it for conformance. The WHATWG Encoding Standard requires it of browsers, and Python's `errors="replace"`, Rust's `String::from_utf8_lossy` and Node's `TextDecoder` follow it. With Node's default, `ignoreBOM` not set, `TextDecoder` drops a byte order mark at the start, where `decodeLossy` reads it as U+FEFF. Other policies exist: a Go `range` loop over a string puts one U+FFFD in place of each bad byte.

## Lean core

Lean core encodes and decodes UTF-8 inside `String`. Two statements tie this library to core, as core defines it:

- Core's `String.toUTF8`, as core defines it, writes the same bytes as `encode`.
- Core's `String.fromUTF8?` accepts exactly the bytes `decode` accepts, and reads the same characters.

At run time, core checks the bytes with C code (`lean_string_validate_utf8`), which no proof covers. The differential tests compare that C code with this decoder too.

## The command-line tool

`utf8 serve`, in `Main.lean`, answers requests from the differential tests, one per line. Its header comment gives the protocol.

- `decode`, `lossy` and `encode` requests are answered by the proved functions.
- `core` requests are answered by Lean core's `String.fromUTF8?`. They are there only so that the tests can compare core with this decoder.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given. The definitions the statements use are in `Spec/Defs.lean`. They are written from RFC 3629, Table 3-7 and section 3.9.6 (D93a, D93b). Those from RFC 3629 and Table 3-7 are checked against the RFC's examples and against the first and last sequence of each row of the table and the bytes just outside its edges. Those from section 3.9.6 have two direct checks there, and are checked against the standard's examples, Tables 3-8 to 3-11, through `Spec.substitution_vectors` together with `Spec.decodeLossy_iff`.

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
| `decodeLossy` gives exactly the conversion of section 3.9.6: each character read as `decode` reads it, and one U+FFFD for each maximal subpart. | `Spec.decodeLossy_iff` |
| On well-formed bytes, `decodeLossy` reads what `decode` reads. | `Spec.decodeLossy_of_decode` |
| On bytes that are not well formed, `decodeLossy` gives at least one U+FFFD. | `Spec.decodeLossy_replaces` |
| Well-formed text before or after bad bytes comes through unchanged. | `Spec.decodeLossy_encode_append`, `Spec.decodeLossy_append_encode` |
| The examples of section 3.9.6, Tables 3-8 to 3-11, and two cut-short sequences followed by a character. | `Spec.substitution_vectors` |

Together, these fix every output.

- `encode` is fixed for every input.
- `decode` is fixed for every input.
- `decodeLossy` is fixed for every input, by `Spec.decodeLossy_iff`.
- A decoder that accepted nothing would fail `Spec.decode_encode`.
- A decoder that accepted too much would fail `Spec.decode_iff`.

## Oracle

Python's strict `utf-8` codec, on every input, and its `replace` error handler for the lossy decoder. Lean core's `String.fromUTF8?` at run time is checked against the same answers as the strict decoder.
