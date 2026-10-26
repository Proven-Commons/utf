# Specification: utf

This library is a UTF-8 encoder, a validating decoder, and a lossy decoder, and the same three for UTF-16. It turns Unicode scalar values into bytes, or into UTF-16 code units, and back. A reviewer who did not write this specification approves it. The approval also covers `Spec.lean`, `Spec/Defs.lean`, `Spec/Utf16.lean`, and the other files `bar.toml` lists.

Characters are Lean's `Char`, which holds exactly the Unicode scalar values: 0 to 0xD7FF and 0xE000 to 0x10FFFF. Bytes are `List UInt8`, and UTF-16 code units `List UInt16`.

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

## UTF-16

The sources are RFC 2781, *UTF-16, an encoding of ISO 10646*, and the Unicode Standard, version 16.0: D72 to D75 for surrogates, D91 and Table 3-5 for the UTF-16 encoding form, D96 to D98 for the encoding schemes, and section 3.9.6 again for lossy decoding. The lossy byte decoders follow the shared UTF-16 decoder of the WHATWG Encoding Standard, section 14.2.1, and `toWellFormed` follows ECMAScript's `String.prototype.toWellFormed`. `Spec/Utf16.lean` quotes RFC 2781, the Unicode Standard and the WHATWG decoder, and sets out ECMAScript's rule in words.

### Code units

`Utf16.encode` writes a character below U+10000 as one unit with its own value. It writes any other character as a surrogate pair: a high surrogate (0xD800 to 0xDBFF) carrying the top ten bits of the code point less 0x10000, then a low surrogate (0xDC00 to 0xDFFF) carrying the bottom ten. That is section 2.1 of RFC 2781. So U+10302 is `D800 DF02`.

`Utf16.decode` returns the characters when its input is the encoding of a list of characters, and `none` otherwise. A unit list is the encoding of some characters exactly when it has no isolated surrogate. An isolated surrogate is a high surrogate with no low surrogate right after it, or a low surrogate with no high surrogate right before it. So the decoder refuses `D800` alone, `DC00` alone, `DBFF 0041`, and `DC00 D800`.

`Utf16.decodeLossy` never fails. Section 3.9.6 applies to UTF-16 as to UTF-8. In UTF-16 a maximal subpart is always a single isolated surrogate. The proofs show this as a lemma, `Utf16.Proofs.maximalSubpart_iff`; it is a fact about the definitions alone, so it is not one of the approved statements. So `decodeLossy` puts one U+FFFD in place of each isolated surrogate, and reads everything else as `decode` reads it. `D800 D800 DC00` gives U+FFFD and then U+10000: the second high surrogate still pairs with the low one. JavaScript's `toWellFormed`, Rust's `String::from_utf16_lossy` and Go's `utf16.Decode` follow the same rule.

`Utf16.toWellFormed` gives the units of `decodeLossy`'s answer. That is the list with each isolated surrogate replaced by the unit 0xFFFD and every other unit kept, as ECMAScript's `String.prototype.toWellFormed` gives.

### Bytes

The encoding schemes write each code unit as two bytes:

- **UTF-16BE** (D96) writes the high byte first.
- **UTF-16LE** (D97) writes the low byte first.

`encodeBE` and `encodeLE` never write a byte order mark. `decodeBE` and `decodeLE` return the characters exactly when the bytes are such an encoding. So they refuse an odd number of bytes, and wherever `decode` refuses the units. In these two schemes a leading `FE FF` (big-endian) or `FF FE` (little-endian) is the character U+FEFF, not a mark. The other order's mark, `FF FE` in UTF-16BE or `FE FF` in UTF-16LE, reads as U+FFFE, a noncharacter, as the Unicode Standard has it. RFC 2781, sections 4.1 and 4.2, would call it an error instead.

`decodeScheme` reads the **UTF-16 encoding scheme** (D98, RFC 2781 section 4.3):

- A leading `FE FF` is a byte order mark for big-endian.
- A leading `FF FE` is a byte order mark for little-endian.
- The mark is not part of the text.
- With neither mark, the text is big-endian.

Python's `utf-16` codec, by contrast, reads text with no mark in the machine's own order, little-endian on most machines. The WHATWG Encoding Standard makes the label `utf-16` mean UTF-16LE.

`decodeLossyBE` and `decodeLossyLE` are the WHATWG Encoding Standard's UTF-16BE and UTF-16LE decoders, with error mode "replacement":

- Each isolated surrogate becomes U+FFFD, as above.
- A byte left over at the end becomes one U+FFFD.
- A high surrogate followed by a leftover byte becomes a single U+FFFD for both, since the standard's decoder reports one error at the end of the input.

Like the WHATWG decoders themselves, they read a leading mark in their own order as U+FEFF. The standard's other steps are not part of these functions. Its `decode` algorithm sniffs a mark first: a leading `EF BB BF`, `FE FF` or `FF FE` picks the encoding, whatever the label, and is skipped. `TextDecoder` does not use `decode`. Unless `ignoreBOM` is set, it drops a U+FEFF that the decoder gives at the start, so only a mark in its own order.

## The command-line tool

`utf8 serve`, in `Main.lean`, answers requests from the differential tests, one per line. Its header comment gives the protocol.

- `decode`, `lossy` and `encode` requests, and the UTF-16 requests (`enc16`, `dec16`, `lossy16`, `wf16`, `encbe`, `encle`, `decbe`, `decle`, `decutf16`, `lossybe`, `lossyle`), are answered by the proved functions.
- `core` requests are answered by Lean core's `String.fromUTF8?`. They are there only so that the tests can compare core with this decoder.

## What must always hold

Each property is a theorem in `Spec.lean`, under the name given. The definitions the statements use are in `Spec/Defs.lean` and, for UTF-16, `Spec/Utf16.lean`. They are written from RFC 3629, Table 3-7 and section 3.9.6 (D93a, D93b). Those from RFC 3629 and Table 3-7 are checked against the RFC's examples and against the first and last sequence of each row of the table and the bytes just outside its edges. Those from section 3.9.6 have two direct checks there, and are checked against the standard's examples, Tables 3-8 to 3-11, through `Spec.substitution_vectors` together with `Spec.decodeLossy_iff`.

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
| The UTF-16 encoder writes each character as RFC 2781, section 2.1, sets out. | `Spec.utf16_encode_eq` |
| `Utf16.decode` returns `cs` exactly when the units are the encoding of `cs`. | `Spec.utf16_decode_iff` |
| Decoding what the UTF-16 encoder wrote gives the characters back. | `Spec.utf16_decode_encode` |
| `Utf16.decode` accepts exactly the unit lists that D91 and Table 3-5 call well formed. | `Spec.utf16_decode_wellFormed` |
| `Utf16.decode` fails exactly when some unit is an isolated surrogate. | `Spec.utf16_decode_none_iff` |
| The number of units is one for each character and one more for each character from U+10000 up. | `Spec.utf16_encode_length` |
| `Utf16.decodeLossy` gives exactly the conversion of section 3.9.6, for UTF-16. | `Spec.utf16_decodeLossy_iff` |
| An isolated surrogate becomes one U+FFFD, and decoding goes on at the very next unit. | `Spec.utf16_decodeLossy_unpaired` |
| On well-formed units, `Utf16.decodeLossy` reads what `Utf16.decode` reads; on any other units it gives at least one U+FFFD. | `Spec.utf16_decodeLossy_of_decode`, `Spec.utf16_decodeLossy_replaces` |
| Well-formed text before or after bad units comes through unchanged. | `Spec.utf16_decodeLossy_encode_append`, `Spec.utf16_decodeLossy_append_encode` |
| `toWellFormed` keeps the number of units, puts 0xFFFD in place of each isolated surrogate, and keeps every other unit. | `Spec.utf16_toWellFormed` |
| `encodeBE` and `encodeLE` write the bytes of RFC 2781, section 3.1, and D96 and D97. | `Spec.utf16_encodeBytes` |
| `decodeBE` and `decodeLE` return `cs` exactly when the bytes are its UTF-16BE or UTF-16LE encoding. | `Spec.utf16be_decode_iff`, `Spec.utf16le_decode_iff` |
| `decodeScheme` reads the UTF-16 encoding scheme as D98 and RFC 2781, section 4.3, say. | `Spec.utf16_decodeScheme_iff` |
| `decodeLossyBE` and `decodeLossyLE` give exactly what the WHATWG UTF-16BE and UTF-16LE decoders give. | `Spec.utf16_whatwg` |
| On whole units, the lossy byte decoders give the conversion of section 3.9.6. | `Spec.utf16_decodeLossyBytes_units` |
| The examples of D91, D96, D97 and RFC 2781, section 5, both ways, and D98's and RFC 2781's texts with a mark, read; the ends of the ranges; marks; isolated surrogates refused and replaced; and a high surrogate cut off by an odd byte. | `Spec.utf16_vectors` |

Together, these fix every output.

- `encode` is fixed for every input.
- `decode` is fixed for every input.
- `decodeLossy` is fixed for every input, by `Spec.decodeLossy_iff`.
- A decoder that accepted nothing would fail `Spec.decode_encode`.
- A decoder that accepted too much would fail `Spec.decode_iff`.
- For UTF-16, the same holds by the statements of the same names. Each byte function is fixed for every input: the encoders and the strict decoders by their own statements, `decodeScheme` by `Spec.utf16_decodeScheme_iff`, and the lossy byte decoders by `Spec.utf16_whatwg`. `toWellFormed` is fixed unit by unit.

## Oracle

Python's strict `utf-8` codec, on every input, and its `replace` error handler for the lossy decoder. Lean core's `String.fromUTF8?` at run time is checked against the same answers as the strict decoder.

For UTF-16, Python's `utf-16-be` and `utf-16-le` codecs, strict and with `replace`, for the unit decoders and the byte decoders. Python's `utf-16` codec reads text that starts with a byte order mark. Text with no mark goes to `utf-16-be`, since Python's `utf-16` would read it in the machine's byte order, little-endian on most machines. For `toWellFormed`, the oracle is ECMAScript's `CodePointAt` rule, written out in `tests/run_tests.py`.
