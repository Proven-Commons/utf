/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry`s below are expected in this
  file only.

  The definitions the statements use, written from RFC 3629 and Table
  3-7 of the Unicode Standard, are in `Spec/Defs.lean`, which is part of
  the specification too.
-/

import Utf8
import Spec.Defs

/-! ## Encoding -/

/-- The encoder writes each character as RFC 3629, section 3, sets
    out. -/
theorem Spec.encode_eq (cs : List Char) : Utf8.encode cs = Spec.encode cs := sorry

/-! ## Decoding -/

/-- `decode` returns `cs` exactly when the bytes are the encoding of
    `cs`. So every byte string it accepts has one reading, and it
    refuses everything else: overlong forms, surrogate halves, values
    past U+10FFFF, stray continuation bytes, the bytes 0xC0, 0xC1 and
    0xF5 to 0xFF, and sequences cut short. -/
theorem Spec.decode_iff (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs ↔ bs = Spec.encode cs := sorry

/-- Round trip: decoding what the encoder wrote gives the characters
    back. -/
theorem Spec.decode_encode (cs : List Char) : Utf8.decode (Utf8.encode cs) = some cs := sorry

/-- The decoder accepts exactly the byte sequences that Table 3-7 of the
    Unicode Standard calls well formed. -/
theorem Spec.decode_wellFormed (bs : List UInt8) :
    (Utf8.decode bs).isSome ↔ Spec.WellFormed bs := sorry

/-! ## Lean core -/

/-- The encoder agrees with Lean core's own UTF-8 encoding of a
    string. -/
theorem Spec.encode_toUTF8 (s : String) : Utf8.encode s.toList = s.toUTF8.toList := sorry

/-- The decoder agrees with Lean core's `String.fromUTF8?`, as core
    defines it: core accepts exactly the bytes this decoder accepts, and
    reads the same characters. (At run time core checks the bytes with
    compiled C code, which this statement does not cover; the tests
    compare the two.) -/
theorem Spec.fromUTF8?_eq (bs : List UInt8) :
    (String.fromUTF8? bs.toByteArray).map String.toList = Utf8.decode bs := sorry

/-! ## Test vectors -/

/-- The examples of RFC 3629, section 7, both ways. -/
theorem Spec.rfc3629_examples :
    Utf8.encode ['A', '≢', 'Α', '.'] =
      [0x41, 0xE2, 0x89, 0xA2, 0xCE, 0x91, 0x2E] ∧
    Utf8.encode ['한', '국', '어'] =
      [0xED, 0x95, 0x9C, 0xEA, 0xB5, 0xAD, 0xEC, 0x96, 0xB4] ∧
    Utf8.encode ['日', '本', '語'] =
      [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E] ∧
    Utf8.encode ['﻿', Char.ofNat 0x233B4] = [0xEF, 0xBB, 0xBF, 0xF0, 0xA3, 0x8E, 0xB4] ∧
    Utf8.decode [0x41, 0xE2, 0x89, 0xA2, 0xCE, 0x91, 0x2E] =
      some ['A', '≢', 'Α', '.'] ∧
    Utf8.decode [0xED, 0x95, 0x9C, 0xEA, 0xB5, 0xAD, 0xEC, 0x96, 0xB4] =
      some ['한', '국', '어'] ∧
    Utf8.decode [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E] =
      some ['日', '本', '語'] ∧
    Utf8.decode [0xEF, 0xBB, 0xBF, 0xF0, 0xA3, 0x8E, 0xB4] =
      some ['﻿', Char.ofNat 0x233B4] := sorry

/-- The first and last code points of each length, the code points on
    either side of the surrogates, and the empty input. -/
theorem Spec.boundary_vectors :
    Utf8.encode ['\u0000', '\u007F'] = [0x00, 0x7F] ∧
    Utf8.encode ['\u0080', '߿'] = [0xC2, 0x80, 0xDF, 0xBF] ∧
    Utf8.encode ['ࠀ', '￿'] = [0xE0, 0xA0, 0x80, 0xEF, 0xBF, 0xBF] ∧
    Utf8.encode [Char.ofNat 0x10000, Char.ofNat 0x10FFFF] =
      [0xF0, 0x90, 0x80, 0x80, 0xF4, 0x8F, 0xBF, 0xBF] ∧
    Utf8.encode ['퟿', ''] = [0xED, 0x9F, 0xBF, 0xEE, 0x80, 0x80] ∧
    Utf8.decode [0xF4, 0x8F, 0xBF, 0xBF] = some [Char.ofNat 0x10FFFF] ∧
    Utf8.encode [] = [] ∧
    Utf8.decode [] = some [] := sorry

/-- Bytes the decoder refuses, a selection, most of them from the hard
    cases of Markus Kuhn's UTF-8 decoder test file: overlong forms of
    `/` and of NUL, the largest overlong form of each length, surrogate
    halves and a surrogate pair, a value past U+10FFFF, each byte from
    0xF5 to 0xFF, five and six byte forms, lone continuation bytes,
    sequences cut short, and a lead byte followed by a byte that is not
    a continuation. Every other input follows from `Spec.decode_iff`. -/
theorem Spec.reject_vectors :
    Utf8.decode [0xC0, 0xAF] = none ∧
    Utf8.decode [0xE0, 0x80, 0xAF] = none ∧
    Utf8.decode [0xF0, 0x80, 0x80, 0xAF] = none ∧
    Utf8.decode [0xC0, 0x80] = none ∧
    Utf8.decode [0xE0, 0x80, 0x80] = none ∧
    Utf8.decode [0xF0, 0x80, 0x80, 0x80] = none ∧
    Utf8.decode [0xC1, 0xBF] = none ∧
    Utf8.decode [0xE0, 0x9F, 0xBF] = none ∧
    Utf8.decode [0xF0, 0x8F, 0xBF, 0xBF] = none ∧
    Utf8.decode [0xED, 0xA0, 0x80] = none ∧
    Utf8.decode [0xED, 0xBF, 0xBF] = none ∧
    Utf8.decode [0xED, 0xA0, 0x80, 0xED, 0xB0, 0x80] = none ∧
    Utf8.decode [0xF4, 0x90, 0x80, 0x80] = none ∧
    Utf8.decode [0xF5, 0x80, 0x80, 0x80] = none ∧
    Utf8.decode [0xF8, 0x88, 0x80, 0x80, 0x80] = none ∧
    Utf8.decode [0xFC, 0x84, 0x80, 0x80, 0x80, 0x80] = none ∧
    Utf8.decode [0xF5] = none ∧
    Utf8.decode [0xF6] = none ∧
    Utf8.decode [0xF7] = none ∧
    Utf8.decode [0xF8] = none ∧
    Utf8.decode [0xF9] = none ∧
    Utf8.decode [0xFA] = none ∧
    Utf8.decode [0xFB] = none ∧
    Utf8.decode [0xFC] = none ∧
    Utf8.decode [0xFD] = none ∧
    Utf8.decode [0xFE] = none ∧
    Utf8.decode [0xFF] = none ∧
    Utf8.decode [0x80] = none ∧
    Utf8.decode [0xBF] = none ∧
    Utf8.decode [0xC2] = none ∧
    Utf8.decode [0xE2, 0x89] = none ∧
    Utf8.decode [0xF0, 0x9F, 0x98] = none ∧
    Utf8.decode [0xC2, 0x41] = none := sorry
