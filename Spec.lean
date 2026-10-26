/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry`s below are expected in this
  file only.

  The definitions the statements use, written from RFC 3629, Table 3-7
  of the Unicode Standard and section 3.9.6 of the Unicode Standard, are
  in `Spec/Defs.lean`; those for UTF-16, written from RFC 2781, the
  Unicode Standard, the WHATWG Encoding Standard and ECMAScript, are in
  `Spec/Utf16.lean`. Both are part of the specification too.
-/

import Utf8
import Utf16
import Spec.Defs
import Spec.Utf16

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
    Utf8.encode ['A', '≢', '\u0391', '.'] =
      [0x41, 0xE2, 0x89, 0xA2, 0xCE, 0x91, 0x2E] ∧
    Utf8.encode ['한', '국', '어'] =
      [0xED, 0x95, 0x9C, 0xEA, 0xB5, 0xAD, 0xEC, 0x96, 0xB4] ∧
    Utf8.encode ['日', '本', '語'] =
      [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E] ∧
    Utf8.encode ['\uFEFF', Char.ofNat 0x233B4] = [0xEF, 0xBB, 0xBF, 0xF0, 0xA3, 0x8E, 0xB4] ∧
    Utf8.decode [0x41, 0xE2, 0x89, 0xA2, 0xCE, 0x91, 0x2E] =
      some ['A', '≢', '\u0391', '.'] ∧
    Utf8.decode [0xED, 0x95, 0x9C, 0xEA, 0xB5, 0xAD, 0xEC, 0x96, 0xB4] =
      some ['한', '국', '어'] ∧
    Utf8.decode [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E] =
      some ['日', '本', '語'] ∧
    Utf8.decode [0xEF, 0xBB, 0xBF, 0xF0, 0xA3, 0x8E, 0xB4] =
      some ['\uFEFF', Char.ofNat 0x233B4] := sorry

/-- The first and last code points of each length, the code points on
    either side of the surrogates, and the empty input. -/
theorem Spec.boundary_vectors :
    Utf8.encode ['\u0000', '\u007F'] = [0x00, 0x7F] ∧
    Utf8.encode ['\u0080', '\u07FF'] = [0xC2, 0x80, 0xDF, 0xBF] ∧
    Utf8.encode ['\u0800', '\uFFFF'] = [0xE0, 0xA0, 0x80, 0xEF, 0xBF, 0xBF] ∧
    Utf8.encode [Char.ofNat 0x10000, Char.ofNat 0x10FFFF] =
      [0xF0, 0x90, 0x80, 0x80, 0xF4, 0x8F, 0xBF, 0xBF] ∧
    Utf8.encode ['\uD7FF', '\uE000'] = [0xED, 0x9F, 0xBF, 0xEE, 0x80, 0x80] ∧
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

/-! ## Lossy decoding -/

/-- `decodeLossy` gives exactly the conversion that section 3.9.6 of
    the Unicode Standard sets out: each well-formed sequence becomes its
    character, and each maximal subpart of an ill-formed sequence
    becomes one U+FFFD. -/
theorem Spec.decodeLossy_iff (bs : List UInt8) (out : List Char) :
    Utf8.decodeLossy bs = out ↔ Spec.Substitutes bs out := sorry

/-- On well-formed bytes, the lossy decoder reads what the strict one
    reads. -/
theorem Spec.decodeLossy_of_decode (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs → Utf8.decodeLossy bs = cs := sorry

/-- On bytes that are not well formed, the lossy decoder puts in at
    least one U+FFFD. -/
theorem Spec.decodeLossy_replaces (bs : List UInt8) :
    Utf8.decode bs = none → '�' ∈ Utf8.decodeLossy bs := sorry

/-- Well-formed text before bad bytes comes through unchanged. -/
theorem Spec.decodeLossy_encode_append (cs : List Char) (bs : List UInt8) :
    Utf8.decodeLossy (Utf8.encode cs ++ bs) = cs ++ Utf8.decodeLossy bs := sorry

/-- Well-formed text after bad bytes comes through unchanged: no
    replacement swallows any of it. -/
theorem Spec.decodeLossy_append_encode (bs : List UInt8) (cs : List Char) :
    Utf8.decodeLossy (bs ++ Utf8.encode cs) = Utf8.decodeLossy bs ++ cs := sorry

/-- The examples of section 3.9.6 of the Unicode Standard, Tables 3-8
    to 3-11, and six cases of a cut-short sequence followed by a
    character, where replacing too many bytes would swallow that
    character. -/
theorem Spec.substitution_vectors :
    -- Table 3-8, non-shortest forms
    Utf8.decodeLossy [0xC0, 0xAF, 0xE0, 0x80, 0xBF, 0xF0, 0x81, 0x82, 0x41] =
      ['�', '�', '�', '�', '�', '�', '�', '�', 'A'] ∧
    -- Table 3-9, surrogates
    Utf8.decodeLossy [0xED, 0xA0, 0x80, 0xED, 0xBF, 0xBF, 0xED, 0xAF, 0x41] =
      ['�', '�', '�', '�', '�', '�', '�', '�', 'A'] ∧
    -- Table 3-10, other ill-formed sequences
    Utf8.decodeLossy [0xF4, 0x91, 0x92, 0x93, 0xFF, 0x41, 0x80, 0xBF, 0x42] =
      ['�', '�', '�', '�', '�', 'A', '�', '�', 'B'] ∧
    -- Table 3-11, truncated sequences
    Utf8.decodeLossy [0xE1, 0x80, 0xE2, 0xF0, 0x91, 0x92, 0xF1, 0xBF, 0x41] =
      ['�', '�', '�', '�', 'A'] ∧
    -- A cut-short sequence, then a character
    Utf8.decodeLossy [0xF0, 0x9F, 0x98, 0x3C] = ['�', '<'] ∧
    Utf8.decodeLossy [0xE2, 0x41, 0x42] = ['�', 'A', 'B'] ∧
    Utf8.decodeLossy [0xC3, 0x41] = ['�', 'A'] ∧
    Utf8.decodeLossy [0xE1, 0x80, 0x41] = ['�', 'A'] ∧
    Utf8.decodeLossy [0xF0, 0x9F, 0x98, 0x41] = ['�', 'A'] ∧
    Utf8.decodeLossy [0xE1, 0x80, 0xE2, 0x82, 0xAC] = ['�', '€'] := sorry

/-! ## UTF-16 code units -/

/-- The UTF-16 encoder writes each character as RFC 2781, section 2.1,
    sets out. -/
theorem Spec.utf16_encode_eq (cs : List Char) : Utf16.encode cs = Spec.encode16 cs := sorry

/-- `Utf16.decode` returns `cs` exactly when the units are the encoding
    of `cs`. So every unit sequence it accepts has one reading, and it
    refuses everything else: a high surrogate with no low surrogate
    after it, and a low surrogate with no high surrogate before it. -/
theorem Spec.utf16_decode_iff (us : List UInt16) (cs : List Char) :
    Utf16.decode us = some cs ↔ us = Spec.encode16 cs := sorry

/-- Round trip: decoding what the encoder wrote gives the characters
    back. -/
theorem Spec.utf16_decode_encode (cs : List Char) :
    Utf16.decode (Utf16.encode cs) = some cs := sorry

/-- The decoder accepts exactly the unit sequences that D91 and Table
    3-5 of the Unicode Standard call well formed. -/
theorem Spec.utf16_decode_wellFormed (us : List UInt16) :
    (Utf16.decode us).isSome ↔ Spec.WellFormed16 us := sorry

/-- The decoder fails exactly when some unit is an isolated surrogate,
    in no surrogate pair. -/
theorem Spec.utf16_decode_none_iff (us : List UInt16) :
    Utf16.decode us = none ↔ ∃ l w r, us = l ++ w :: r ∧ Spec.Unpaired l w r := sorry

/-- The number of units: one for each character, and one more for each
    character from U+10000 up. This is what JavaScript's `length` counts
    for a string. -/
theorem Spec.utf16_encode_length (cs : List Char) :
    (Utf16.encode cs).length = cs.length + (cs.filter fun c => 0x10000 ≤ c.toNat).length := sorry

/-! ## UTF-16 lossy decoding -/

/-- `Utf16.decodeLossy` gives exactly the conversion that section 3.9.6
    of the Unicode Standard sets out, for UTF-16: each well-formed
    sequence becomes its character, and each maximal subpart of an
    ill-formed sequence becomes one U+FFFD. -/
theorem Spec.utf16_decodeLossy_iff (us : List UInt16) (out : List Char) :
    Utf16.decodeLossy us = out ↔ Spec.Substitutes16 us out := sorry

/-- An isolated surrogate at the front becomes one U+FFFD, and decoding
    goes on at the very next unit: a high surrogate never takes the unit
    after it with it. This is the rule of JavaScript's `toWellFormed`,
    Rust's `String::from_utf16_lossy` and the WHATWG decoders. -/
theorem Spec.utf16_decodeLossy_unpaired (w : UInt16) (rest : List UInt16) :
    Spec.Unpaired [] w rest → Utf16.decodeLossy (w :: rest) = '�' :: Utf16.decodeLossy rest := sorry

/-- On well-formed units, the lossy decoder reads what the strict one
    reads. -/
theorem Spec.utf16_decodeLossy_of_decode (us : List UInt16) (cs : List Char) :
    Utf16.decode us = some cs → Utf16.decodeLossy us = cs := sorry

/-- On units that are not well formed, the lossy decoder puts in at
    least one U+FFFD. -/
theorem Spec.utf16_decodeLossy_replaces (us : List UInt16) :
    Utf16.decode us = none → '�' ∈ Utf16.decodeLossy us := sorry

/-- Well-formed text before bad units comes through unchanged. -/
theorem Spec.utf16_decodeLossy_encode_append (cs : List Char) (us : List UInt16) :
    Utf16.decodeLossy (Utf16.encode cs ++ us) = cs ++ Utf16.decodeLossy us := sorry

/-- Well-formed text after bad units comes through unchanged: a high
    surrogate at the end of the bad units never takes the first unit of
    the text as its partner. -/
theorem Spec.utf16_decodeLossy_append_encode (us : List UInt16) (cs : List Char) :
    Utf16.decodeLossy (us ++ Utf16.encode cs) = Utf16.decodeLossy us ++ cs := sorry

/-- `toWellFormed` does what ECMAScript's `String.prototype.toWellFormed`
    does: it keeps the number of units, puts 0xFFFD in place of each
    isolated surrogate, and keeps every other unit. -/
theorem Spec.utf16_toWellFormed (us : List UInt16) :
    (Utf16.toWellFormed us).length = us.length ∧
    ∀ (i : Nat) (h : i < us.length),
      (Spec.Unpaired (us.take i) us[i] (us.drop (i + 1)) →
        (Utf16.toWellFormed us)[i]? = some 0xFFFD) ∧
      (¬ Spec.Unpaired (us.take i) us[i] (us.drop (i + 1)) →
        (Utf16.toWellFormed us)[i]? = some us[i]) := sorry

/-! ## UTF-16 as bytes -/

/-- UTF-16BE writes each unit's high byte first, and UTF-16LE its low
    byte first, as RFC 2781, section 3.1, and D96 and D97 set out; no
    byte order mark is written. -/
theorem Spec.utf16_encodeBytes (cs : List Char) :
    Utf16.encodeBE cs = Spec.serializeBE (Spec.encode16 cs) ∧
    Utf16.encodeLE cs = Spec.serializeLE (Spec.encode16 cs) := sorry

/-- The UTF-16BE decoder returns `cs` exactly when the bytes are the
    UTF-16BE encoding of `cs`. So it refuses an odd number of bytes, and
    it reads a leading FE FF as U+FEFF (D96). -/
theorem Spec.utf16be_decode_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeBE bs = some cs ↔ bs = Spec.serializeBE (Spec.encode16 cs) := sorry

/-- The UTF-16LE decoder returns `cs` exactly when the bytes are the
    UTF-16LE encoding of `cs`, so it reads a leading FF FE as U+FEFF
    (D97). -/
theorem Spec.utf16le_decode_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeLE bs = some cs ↔ bs = Spec.serializeLE (Spec.encode16 cs) := sorry

/-- The decoder for the UTF-16 encoding scheme reads `cs` exactly as
    D98 and RFC 2781, section 4.3, say: after a byte order mark, in the
    order it gives, the mark not part of the text; with no mark,
    big-endian. -/
theorem Spec.utf16_decodeScheme_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeScheme bs = some cs ↔ Spec.SchemeReads bs cs := sorry

/-- The lossy byte decoders give exactly what the WHATWG Encoding
    Standard's UTF-16BE and UTF-16LE decoders give, with error mode
    "replacement". -/
theorem Spec.utf16_whatwg (bs : List UInt8) :
    Utf16.decodeLossyBE bs = Spec.whatwgDecode true bs ∧
    Utf16.decodeLossyLE bs = Spec.whatwgDecode false bs := sorry

/-- On whole units, the lossy byte decoders give the conversion of
    section 3.9.6 (`Spec.utf16_decodeLossy_iff`): the WHATWG decoders
    and the Unicode Standard agree. -/
theorem Spec.utf16_decodeLossyBytes_units (us : List UInt16) :
    Utf16.decodeLossyBE (Spec.serializeBE us) = Utf16.decodeLossy us ∧
    Utf16.decodeLossyLE (Spec.serializeLE us) = Utf16.decodeLossy us := sorry

/-! ## UTF-16 test vectors -/

/-- The examples of D91, D96 and D97 of the Unicode Standard and of RFC
    2781, section 5, both ways, and D98's and RFC 2781's texts with a
    byte order mark, read; the ends of the ranges; isolated surrogates
    refused and replaced; and the WHATWG decoder's single U+FFFD for a
    high surrogate cut off with an odd byte. -/
theorem Spec.utf16_vectors :
    -- D91 and D96 to D98: <004D 0430 4E8C 10302>
    Utf16.encode ['M', '\u0430', '二', Char.ofNat 0x10302] =
      [0x004D, 0x0430, 0x4E8C, 0xD800, 0xDF02] ∧
    Utf16.decode [0x004D, 0x0430, 0x4E8C, 0xD800, 0xDF02] =
      some ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    Utf16.encodeBE ['M', '\u0430', '二', Char.ofNat 0x10302] =
      [0x00, 0x4D, 0x04, 0x30, 0x4E, 0x8C, 0xD8, 0x00, 0xDF, 0x02] ∧
    Utf16.encodeLE ['M', '\u0430', '二', Char.ofNat 0x10302] =
      [0x4D, 0x00, 0x30, 0x04, 0x8C, 0x4E, 0x00, 0xD8, 0x02, 0xDF] ∧
    Utf16.decodeScheme [0xFE, 0xFF, 0x00, 0x4D, 0x04, 0x30, 0x4E, 0x8C, 0xD8, 0x00, 0xDF, 0x02] =
      some ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    Utf16.decodeScheme [0xFF, 0xFE, 0x4D, 0x00, 0x30, 0x04, 0x8C, 0x4E, 0x00, 0xD8, 0x02, 0xDF] =
      some ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    Utf16.decodeScheme [0x00, 0x4D, 0x04, 0x30, 0x4E, 0x8C, 0xD8, 0x00, 0xDF, 0x02] =
      some ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    Utf16.decodeBE [0x00, 0x4D, 0x04, 0x30, 0x4E, 0x8C, 0xD8, 0x00, 0xDF, 0x02] =
      some ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    Utf16.decodeLE [0x4D, 0x00, 0x30, 0x04, 0x8C, 0x4E, 0x00, 0xD8, 0x02, 0xDF] =
      some ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    -- RFC 2781, section 5: U+12345 then "=Ra", both ways, and with each mark
    Utf16.encode [Char.ofNat 0x12345, '=', 'R', 'a'] = [0xD808, 0xDF45, 0x003D, 0x0052, 0x0061] ∧
    Utf16.encodeBE [Char.ofNat 0x12345, '=', 'R', 'a'] =
      [0xD8, 0x08, 0xDF, 0x45, 0x00, 0x3D, 0x00, 0x52, 0x00, 0x61] ∧
    Utf16.encodeLE [Char.ofNat 0x12345, '=', 'R', 'a'] =
      [0x08, 0xD8, 0x45, 0xDF, 0x3D, 0x00, 0x52, 0x00, 0x61, 0x00] ∧
    Utf16.decodeBE [0xD8, 0x08, 0xDF, 0x45, 0x00, 0x3D, 0x00, 0x52, 0x00, 0x61] =
      some [Char.ofNat 0x12345, '=', 'R', 'a'] ∧
    Utf16.decodeLE [0x08, 0xD8, 0x45, 0xDF, 0x3D, 0x00, 0x52, 0x00, 0x61, 0x00] =
      some [Char.ofNat 0x12345, '=', 'R', 'a'] ∧
    Utf16.decodeScheme [0xFE, 0xFF, 0xD8, 0x08, 0xDF, 0x45, 0x00, 0x3D, 0x00, 0x52, 0x00, 0x61] =
      some [Char.ofNat 0x12345, '=', 'R', 'a'] ∧
    Utf16.decodeScheme [0xFF, 0xFE, 0x08, 0xD8, 0x45, 0xDF, 0x3D, 0x00, 0x52, 0x00, 0x61, 0x00] =
      some [Char.ofNat 0x12345, '=', 'R', 'a'] ∧
    -- The ends of the ranges
    Utf16.encode [Char.ofNat 0xD7FF, Char.ofNat 0xE000, Char.ofNat 0xFFFF,
        Char.ofNat 0x10000, Char.ofNat 0x10FFFF] =
      [0xD7FF, 0xE000, 0xFFFF, 0xD800, 0xDC00, 0xDBFF, 0xDFFF] ∧
    -- A mark in UTF-16BE and UTF-16LE is U+FEFF; in the scheme it is not text
    Utf16.decodeBE [0xFE, 0xFF, 0x00, 0x41] = some ['\uFEFF', 'A'] ∧
    Utf16.decodeLE [0xFF, 0xFE, 0x41, 0x00] = some ['\uFEFF', 'A'] ∧
    Utf16.decodeScheme [0xFE, 0xFF, 0x00, 0x41] = some ['A'] ∧
    Utf16.decodeScheme [0x00, 0x41] = some ['A'] ∧
    -- Isolated surrogates, refused
    Utf16.decode [0xD800] = none ∧
    Utf16.decode [0xDC00] = none ∧
    Utf16.decode [0xDBFF, 0x0041] = none ∧
    Utf16.decode [0xDC00, 0xD800] = none ∧
    Utf16.decodeBE [0x00, 0x41, 0x00] = none ∧
    -- and replaced
    Utf16.decodeLossy [0xD800, 0x0041] = ['�', 'A'] ∧
    Utf16.decodeLossy [0xDC00, 0xD800, 0xDC00] = ['�', Char.ofNat 0x10000] ∧
    Utf16.decodeLossy [0xD800, 0xD800, 0xDC00] = ['�', Char.ofNat 0x10000] ∧
    Utf16.decodeLossy [0x0041, 0xDBFF] = ['A', '�'] ∧
    Utf16.toWellFormed [0xDC00, 0xD800, 0xDC00, 0xD800] = [0xFFFD, 0xD800, 0xDC00, 0xFFFD] ∧
    -- The WHATWG decoders: an odd byte at the end, alone or after a high surrogate
    Utf16.decodeLossyLE [0x41, 0x00, 0x42] = ['A', '�'] ∧
    Utf16.decodeLossyLE [0x00, 0xD8, 0x41] = ['�'] ∧
    Utf16.decodeLossyBE [0xD8, 0x00, 0x00, 0x41] = ['�', 'A'] := sorry
