# utf: a UTF-8 codec, proved

This library is a UTF-8 encoder and a validating decoder in Lean. Machine-checked proofs show four things:

- The encoder writes what RFC 3629 sets out.
- The decoder accepts a byte string exactly when it is the encoding of some list of characters, and returns those characters.
- The bytes the decoder accepts are exactly those that Table 3-7 of the Unicode Standard calls well formed.
- Lean core's own UTF-8 functions, as core defines them, agree with both.

So the decoder refuses overlong forms, surrogate halves, values past U+10FFFF and sequences cut short. A byte string has one reading or none, never two.

It is tested against Python's strict UTF-8 codec, with Lean core's compiled check compared alongside; `tests/TEST-RESULTS.md` has the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean:

- `Utf8.encode : List Char → List UInt8`
- `Utf8.decode : List UInt8 → Option (List Char)`

`SPEC.md` says what each one does.

## What is proved

The statements are in `Spec.lean`, the definitions they use in `Spec/Defs.lean`, and the proofs in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| The encoder writes each character as the table of RFC 3629, section 3, sets out. | `Spec.encode_eq` |
| `decode` returns a list of characters exactly when the bytes are its encoding. So every byte string it accepts has one reading. It refuses everything else: overlong forms, surrogate halves, values past U+10FFFF, stray continuation bytes, the bytes 0xC0, 0xC1 and 0xF5 to 0xFF, and sequences cut short. | `Spec.decode_iff` |
| Decoding what the encoder wrote gives the characters back. | `Spec.decode_encode` |
| The decoder accepts exactly the byte sequences that Table 3-7 of the Unicode Standard calls well formed. | `Spec.decode_wellFormed` |
| Lean core's `String.toUTF8`, as core defines it, writes the same bytes as the encoder. | `Spec.encode_toUTF8` |
| Lean core's `String.fromUTF8?`, as core defines it, accepts exactly the bytes the decoder accepts and reads the same characters. | `Spec.fromUTF8?_eq` |
| The examples of RFC 3629, section 7, both ways; the boundaries of each length and of the surrogates; and a selection of malformed inputs, most of them from Markus Kuhn's UTF-8 decoder test file. Every case in that file follows from `Spec.decode_iff`, and the tests run them all. | `Spec.rfc3629_examples`, `Spec.boundary_vectors`, `Spec.reject_vectors` |

The command-line tool in `Main.lean` answers `decode` and `encode` requests with these functions directly.

## What is not proved

- Lean core's compiled check. At run time, `String.fromUTF8?` runs C code, `lean_string_validate_utf8`, in place of the definition `Spec.fromUTF8?_eq` is about. The differential tests compare that C code with the proved decoder.
- Reading requests and printing answers in `Main.lean`: the hex parsing and printing, and the request format. The differential tests cover them, with malformed requests and CR LF line endings.
- Other decoding policies. There is no lossy mode that puts U+FFFD in place of bad bytes, and a byte order mark is read as a character, not stripped.
- UTF-16, UTF-32, and Unicode normalization.
- Speed and size. The code works on lists and recurses once per character, which suits proofs, not bulk data. With an 8 MB stack, a request of 12 million bytes is answered, but one of 16 million runs out of stack: the program stops, with the answers before it already written, and never gives a wrong one.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about (by `implemented_by` and `extern`), such as the arithmetic on natural numbers, the fixed-width byte type, and the conversion between strings, byte arrays and lists.
- The operating system and hardware it runs on.
- Python's `utf-8` codec, as the oracle in the differential tests. The record names the Python version.

This project has no dependencies beyond Lean itself.

## Other decoders

`tests/CROSS-CHECK.md` records a one-off comparison with Go's `utf8.Valid`, Rust's `String::from_utf8`, and Node's `TextDecoder` with `fatal` set. It is not part of the verified bar. On every byte string the tests decode, all three accept exactly what this decoder accepts and read the same code points.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`), and Python 3.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
```

`lake build` checks every proof in `Proofs/`, and fails if one is broken.

`lake comparator` is part of Lake in Lean 4.35.0, the toolchain that `lean-toolchain` pins and elan installs. `lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

The test script compares the tool with Python's strict UTF-8 codec. It runs every byte string of one and two bytes, a grid of three- and four-byte strings, and random and mutated inputs from a recorded seed. It then rewrites `tests/TEST-RESULTS.md`.

## Layout

- `Utf8/Codec.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from RFC 3629 and Table 3-7, with checks against the RFC's examples.
- `Proofs.lean` and `Proofs/`: the proofs, under the same names.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/run_tests.py`: the differential tests.
- `tests/cross_check.py` and `tests/cross_check/`: the one-off comparison with Go, Rust and Node.
