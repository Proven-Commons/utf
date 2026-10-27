# utf: UTF-8 and UTF-16, proved

This library is a UTF-8 encoder, a validating decoder and a lossy decoder in Lean, and the same three for UTF-16, over code units and over bytes. Machine-checked proofs show five things for UTF-8:

- The encoder writes what RFC 3629 sets out.
- The decoder accepts a byte string exactly when it is the encoding of some list of characters, and returns those characters.
- The bytes the decoder accepts are exactly those that Table 3-7 of the Unicode Standard calls well formed.
- Lean core's own UTF-8 functions, as core defines them, agree with both.
- The lossy decoder puts one U+FFFD in place of each maximal subpart of bad bytes, exactly as section 3.9.6 of the Unicode Standard sets out, and valid text on either side comes through unchanged.

So the validating decoder refuses overlong forms, surrogate halves, values past U+10FFFF and sequences cut short. A byte string has one reading or none, never two.

For UTF-16 they show:

- The encoder writes what RFC 2781 sets out.
- The decoder accepts a list of code units exactly when it is the encoding of some list of characters, so it refuses exactly the lists with an isolated surrogate, one in no surrogate pair.
- The lossy decoder follows section 3.9.6 too. In UTF-16 that comes to one U+FFFD for each isolated surrogate, and `toWellFormed` does what JavaScript's `String.prototype.toWellFormed` does.
- UTF-16BE and UTF-16LE read and write bytes as D96 and D97 of the Unicode Standard set out, and the UTF-16 encoding scheme, with its byte order mark, is read as D98 and RFC 2781 say.
- The lossy byte decoders give exactly what the WHATWG Encoding Standard's UTF-16BE and UTF-16LE decoders give.

It is tested against Python's UTF-8 and UTF-16 codecs, strict and with `errors="replace"`, with Lean core's compiled UTF-8 check compared alongside; `tests/TEST-RESULTS.md` has the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean:

- `Utf8.encode : List Char → List UInt8`
- `Utf8.decode : List UInt8 → Option (List Char)`
- `Utf8.decodeLossy : List UInt8 → List Char`
- `Utf16.encode : List Char → List UInt16`
- `Utf16.decode : List UInt16 → Option (List Char)`
- `Utf16.decodeLossy : List UInt16 → List Char`
- `Utf16.toWellFormed : List UInt16 → List UInt16`
- `Utf16.encodeBE`, `Utf16.encodeLE : List Char → List UInt8`
- `Utf16.decodeBE`, `Utf16.decodeLE`, `Utf16.decodeScheme : List UInt8 → Option (List Char)`
- `Utf16.decodeLossyBE`, `Utf16.decodeLossyLE : List UInt8 → List Char`

`SPEC.md` says what each one does.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean` and `Spec/Utf16.lean`, and the proofs in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| The encoder writes each character as the table of RFC 3629, section 3, sets out. | `Spec.encode_eq` |
| `decode` returns a list of characters exactly when the bytes are its encoding. So every byte string it accepts has one reading. It refuses everything else: overlong forms, surrogate halves, values past U+10FFFF, stray continuation bytes, the bytes 0xC0, 0xC1 and 0xF5 to 0xFF, and sequences cut short. | `Spec.decode_iff` |
| Decoding what the encoder wrote gives the characters back. | `Spec.decode_encode` |
| The decoder accepts exactly the byte sequences that Table 3-7 of the Unicode Standard calls well formed. | `Spec.decode_wellFormed` |
| Lean core's `String.toUTF8`, as core defines it, writes the same bytes as the encoder. | `Spec.encode_toUTF8` |
| Lean core's `String.fromUTF8?`, as core defines it, accepts exactly the bytes the decoder accepts and reads the same characters. | `Spec.fromUTF8?_eq` |
| The examples of RFC 3629, section 7, both ways; the boundaries of each length and of the surrogates; and a selection of malformed inputs, most of them from Markus Kuhn's UTF-8 decoder test file. Every case in that file follows from `Spec.decode_iff`, and the tests run them all. | `Spec.rfc3629_examples`, `Spec.boundary_vectors`, `Spec.reject_vectors` |
| `decodeLossy` gives exactly what section 3.9.6 of the Unicode Standard, *U+FFFD Substitution of Maximal Subparts*, sets out: each well-formed sequence becomes its character, and each maximal subpart of bad bytes becomes one U+FFFD. | `Spec.decodeLossy_iff` |
| On well-formed bytes, `decodeLossy` reads what `decode` reads; on any other bytes it gives at least one U+FFFD. | `Spec.decodeLossy_of_decode`, `Spec.decodeLossy_replaces` |
| Well-formed text before or after bad bytes comes through unchanged: no U+FFFD takes in any of it. | `Spec.decodeLossy_encode_append`, `Spec.decodeLossy_append_encode` |
| The examples of Tables 3-8 to 3-11 of the Unicode Standard, and six cut-short sequences followed by a character. | `Spec.substitution_vectors` |
| The UTF-16 encoder writes each character as RFC 2781, section 2.1, sets out. | `Spec.utf16_encode_eq` |
| `Utf16.decode` returns a list of characters exactly when the code units are its encoding. So every unit list it accepts has one reading, and it refuses everything else. | `Spec.utf16_decode_iff` |
| Decoding what the UTF-16 encoder wrote gives the characters back. | `Spec.utf16_decode_encode` |
| `Utf16.decode` accepts exactly the unit lists that D91 and Table 3-5 of the Unicode Standard call well formed. | `Spec.utf16_decode_wellFormed` |
| `Utf16.decode` fails exactly when some unit is an isolated surrogate: a high surrogate with no low surrogate after it, or a low surrogate with no high surrogate before it. | `Spec.utf16_decode_none_iff` |
| The number of UTF-16 units is one for each character, and one more for each character from U+10000 up. | `Spec.utf16_encode_length` |
| `Utf16.decodeLossy` gives exactly the conversion of section 3.9.6, written for UTF-16 code units. | `Spec.utf16_decodeLossy_iff` |
| An isolated surrogate becomes one U+FFFD, and decoding goes on at the very next unit, so a high surrogate never takes the unit after it with it. That is what section 3.9.6 comes to in UTF-16. The proofs go through a lemma, `Utf16.Proofs.maximalSubpart_iff`, that each maximal subpart in UTF-16 is one isolated surrogate. It is a fact about the definitions alone, so the bar does not take it as one of the approved statements. | `Spec.utf16_decodeLossy_unpaired` |
| On well-formed units, `Utf16.decodeLossy` reads what `Utf16.decode` reads; on any other units it gives at least one U+FFFD. | `Spec.utf16_decodeLossy_of_decode`, `Spec.utf16_decodeLossy_replaces` |
| Well-formed text before or after bad units comes through unchanged. | `Spec.utf16_decodeLossy_encode_append`, `Spec.utf16_decodeLossy_append_encode` |
| `toWellFormed` keeps the number of units, puts 0xFFFD in place of each isolated surrogate and keeps every other unit, as ECMAScript's `String.prototype.toWellFormed` does. | `Spec.utf16_toWellFormed` |
| UTF-16BE writes each unit's high byte first, and UTF-16LE its low byte first, with no byte order mark. | `Spec.utf16_encodeBytes` |
| The UTF-16BE and UTF-16LE decoders accept exactly the encodings, so they refuse an odd number of bytes and read a leading byte order mark as U+FEFF. | `Spec.utf16be_decode_iff`, `Spec.utf16le_decode_iff` |
| The decoder for the UTF-16 encoding scheme reads a byte order mark as D98 and RFC 2781, section 4.3, say: FE FF for big-endian, FF FE for little-endian, the mark not part of the text, and big-endian with no mark. | `Spec.utf16_decodeScheme_iff` |
| The lossy byte decoders give exactly what the WHATWG Encoding Standard's UTF-16BE and UTF-16LE decoders give, run as the standard writes them. | `Spec.utf16_whatwg` |
| On whole units, the lossy byte decoders give the conversion of section 3.9.6, so the WHATWG decoders and the Unicode Standard agree. | `Spec.utf16_decodeLossyBytes_units` |
| The examples of D91, D96 and D97 of the Unicode Standard and of RFC 2781, section 5, both ways, and the texts of D98 and RFC 2781 with a byte order mark, read; the ends of the ranges; byte order marks; isolated surrogates refused and replaced; and a high surrogate cut off by an odd byte, which the WHATWG decoders turn into one U+FFFD. | `Spec.utf16_vectors` |

The command-line tool in `Main.lean` answers `decode`, `lossy` and `encode` requests, and each UTF-16 request, with these functions directly.

## What is not proved

- Lean core's compiled check. At run time, `String.fromUTF8?` runs C code, `lean_string_validate_utf8`, in place of the definition `Spec.fromUTF8?_eq` is about. The differential tests compare that C code with the proved decoder.
- Reading requests and printing answers in `Main.lean`: the hex parsing and printing, and the request format. The differential tests cover them, with malformed requests and CR LF line endings.
- Other replacement policies. The lossy decoder follows section 3.9.6 only. It has no mode that puts U+FFFD in place of each bad byte on its own, as a Go `range` loop does. A byte order mark is read as a character, not stripped.
- For UTF-16: byte order marks in the lossy byte decoders. They are the WHATWG decoders themselves, which read a leading FE FF (UTF-16BE) or FF FE (UTF-16LE) as U+FEFF. The standard's other steps are not here. Its `decode` algorithm sniffs a mark first, and a leading EF BB BF, FE FF or FF FE then picks the encoding and is skipped. `TextDecoder`, unless `ignoreBOM` is set, drops a U+FEFF that the decoder gives at the start.
- For UTF-16: writing the UTF-16 encoding scheme. The encoders never write a mark, and with no mark `decodeScheme` reads big-endian. So whoever writes this scheme must put a mark first: always for little-endian, and for big-endian whenever the text starts with U+FEFF or U+FFFE. Without a mark, `encodeLE` output is read big-endian: "AB" is written 41 00 42 00 and reads as U+4100 U+4200. If the text starts with U+FEFF, `encodeLE` writes FF FE first, which reads as the little-endian mark, so the rest reads right but the U+FEFF is lost. If it starts with U+FFFE, `encodeLE` writes FE FF first, which reads as the big-endian mark, so the U+FFFE is lost and the rest reads in the wrong order. `encodeBE` of text that starts with U+FEFF begins FE FF, which `decodeScheme` reads as a mark, so the U+FEFF is lost. `encodeBE` of text that starts with U+FFFE begins FF FE, which reads as the little-endian mark. Then the U+FFFE is lost and the rest reads in the wrong order, so U+FFFE "AB" reads as U+4100 U+4200, with no error.
- For UTF-16: the error rule of RFC 2781, sections 4.1 and 4.2. It calls FF FE in UTF-16BE, and FE FF in UTF-16LE, an error, since it takes U+FFFE as no character. Here those bytes read as U+FFFE, a noncharacter, as the Unicode Standard (D91), Python, Node and Rust read them. `SPEC.md` quotes both sources on this choice.
- For UTF-16: other ways to choose a byte order. With no mark, `decodeScheme` reads big-endian, as RFC 2781 and D98 say, where Python's `utf-16` codec reads it in the machine's byte order, little-endian on most machines, and the WHATWG Encoding Standard's `utf-16` label means little-endian.
- UTF-32, and Unicode normalization.
- Speed and size. The code works on lists and recurses once per character, which suits proofs, not bulk data. With an 8 MB stack, a request of 12 million bytes is answered, but one of 16 million runs out of stack: the program stops, with the answers before it already written, and never gives a wrong one.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the arithmetic on natural numbers, the fixed-width byte type, and the conversion between strings, byte arrays and lists.
- The operating system and hardware it runs on.
- Python's `utf-8`, `utf-16-be`, `utf-16-le` and `utf-16` codecs, strict and with the `replace` error handler, and the `toWellFormed` rule written in `tests/run_tests.py`, as the oracles in the differential tests. The record names the Python version.

This project has no dependencies beyond Lean itself.

## Other decoders

`tests/CROSS-CHECK.md` records a one-off comparison with Go's `utf8.Valid`, Rust's `String::from_utf8`, and Node's `TextDecoder` with `fatal` and `ignoreBOM` set. It is not part of the verified bar. On every byte string the tests decode, all three accept exactly what this decoder accepts and read the same code points.

It also compares the lossy decoder with Rust's `String::from_utf8_lossy` and Node's `TextDecoder` without `fatal` and with `ignoreBOM` set. On every byte string the tests decode, both read the same code points as the lossy decoder. With Node's default, `ignoreBOM` not set, `TextDecoder` drops a byte order mark at the start, where this library reads it as U+FEFF. A Go `range` loop differs on purpose, since it puts one U+FFFD in place of each bad byte.

For UTF-16, it compares the unit decoders with Rust's `String::from_utf16` and `from_utf16_lossy`, Node's `isWellFormed` and `toWellFormed`, and Go's `unicode/utf16.Decode`, and the byte decoders with Node's `TextDecoder` for UTF-16BE and UTF-16LE, fatal and not, with `ignoreBOM` set. `tests/CROSS-CHECK.md` gives the counts.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake build` compiles the code and the proofs, and fails on any error in them. It only warns about a `sorry`, and it does not check the axioms a proof uses or compare the proofs with `Spec.lean`. `lake comparator --paranoid` is the command that checks every statement is proved, with no `sorry`.

`lake comparator` is part of Lake in Lean 4.35.0, the toolchain that `lean-toolchain` pins and elan installs. `lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script builds the tool alone, not the proofs, and compares it with Python's UTF-8 and UTF-16 codecs, strict and with the `replace` error handler. For UTF-8 it runs every byte string of one and two bytes, a grid of three- and four-byte strings, and random and mutated inputs from a recorded seed. For UTF-16 it runs every single code unit, every pair and triple of units at the edges of the surrogate ranges, every byte string of one and two bytes through each byte decoder, and random and mutated inputs. It then rewrites `tests/TEST-RESULTS.md`. `tests/planted_bugs.py` plants 30 small bugs in the code under proof, one at a time in a copy: seven in the strict UTF-8 codec, nine in the lossy UTF-8 decoder and 14 in UTF-16. `tests/PLANTED-BUGS.md` records that the tests catch 28 of them, why the other two change no answer, and that each of the 30 stops the proofs from building.

## Layout

- `Utf8/Codec.lean`, `Utf8/Lossy.lean`, `Utf16/Codec.lean` and `Utf16/Bytes.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from RFC 3629, Table 3-7 and section 3.9.6, with checks against the RFC's examples.
- `Spec/Utf16.lean`: the definitions the UTF-16 statements use, written from RFC 2781, the Unicode Standard, the WHATWG Encoding Standard and ECMAScript, with checks against the examples of the first two and against each step of the WHATWG decoder.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/planted_bugs.py`: the planted bugs, which check that the tests catch small mistakes in the code under proof.
- `tests/cross_check.py` and `tests/cross_check/`: the one-off comparison with Go, Rust and Node.
