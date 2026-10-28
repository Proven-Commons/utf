/-
  The statements of `Utf/Spec.lean`, under the same names, from the lemmas
  in the other files of `Utf/Proofs/`. The test vectors are checked by
  evaluation.
-/

import Utf8
import Utf.Spec.Defs
import Utf.Proofs.Encode
import Utf.Proofs.Decode
import Utf.Proofs.Table
import Utf.Proofs.Core
import Utf.Proofs.Lossy.Main
import Utf.Proofs.Utf16.Units
import Utf.Proofs.Utf16.Lossy
import Utf.Proofs.Utf16.Bytes
import Utf.Proofs.Utf16.Whatwg

theorem Utf.Spec.encode_eq (cs : List Char) : Utf8.encode cs = Utf.Spec.encode cs :=
  Utf8.Proofs.Encode.encode_eq cs

theorem Utf.Spec.decode_iff (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs ↔ bs = Utf.Spec.encode cs := by
  rw [Utf8.Proofs.Decode.decode_iff, Utf8.Proofs.Encode.encode_eq]

theorem Utf.Spec.decode_encode (cs : List Char) : Utf8.decode (Utf8.encode cs) = some cs :=
  Utf8.Proofs.Decode.decode_encode cs

theorem Utf.Spec.decode_wellFormed (bs : List UInt8) :
    (Utf8.decode bs).isSome ↔ Utf.Spec.WellFormed bs := by
  rw [Utf8.Proofs.Table.wellFormed_iff, Option.isSome_iff_exists]
  simp only [Utf8.Proofs.Decode.decode_iff]

theorem Utf.Spec.encode_toUTF8 (s : String) : Utf8.encode s.toList = s.toUTF8.toList :=
  Utf8.Proofs.Encode.encode_toUTF8 s

theorem Utf.Spec.fromUTF8?_eq (bs : List UInt8) :
    (String.fromUTF8? bs.toByteArray).map String.toList = Utf8.decode bs :=
  Utf8.Proofs.Core.fromUTF8?_eq bs

theorem Utf.Spec.rfc3629_examples :
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
      some ['\uFEFF', Char.ofNat 0x233B4] := by
  decide

theorem Utf.Spec.boundary_vectors :
    Utf8.encode ['\u0000', '\u007F'] = [0x00, 0x7F] ∧
    Utf8.encode ['\u0080', '\u07FF'] = [0xC2, 0x80, 0xDF, 0xBF] ∧
    Utf8.encode ['\u0800', '\uFFFF'] = [0xE0, 0xA0, 0x80, 0xEF, 0xBF, 0xBF] ∧
    Utf8.encode [Char.ofNat 0x10000, Char.ofNat 0x10FFFF] =
      [0xF0, 0x90, 0x80, 0x80, 0xF4, 0x8F, 0xBF, 0xBF] ∧
    Utf8.encode ['\uD7FF', '\uE000'] = [0xED, 0x9F, 0xBF, 0xEE, 0x80, 0x80] ∧
    Utf8.decode [0xF4, 0x8F, 0xBF, 0xBF] = some [Char.ofNat 0x10FFFF] ∧
    Utf8.encode [] = [] ∧
    Utf8.decode [] = some [] := by
  decide

theorem Utf.Spec.reject_vectors :
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
    Utf8.decode [0xC2, 0x41] = none := by
  decide

theorem Utf.Spec.decodeLossy_iff (bs : List UInt8) (out : List Char) :
    Utf8.decodeLossy bs = out ↔ Utf.Spec.Substitutes bs out :=
  Utf8.Proofs.Lossy.decodeLossy_iff bs out

theorem Utf.Spec.decodeLossy_of_decode (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs → Utf8.decodeLossy bs = cs :=
  Utf8.Proofs.Lossy.decodeLossy_of_decode bs cs

theorem Utf.Spec.decodeLossy_replaces (bs : List UInt8) :
    Utf8.decode bs = none → '�' ∈ Utf8.decodeLossy bs :=
  Utf8.Proofs.Lossy.decodeLossy_replaces bs

theorem Utf.Spec.decodeLossy_encode_append (cs : List Char) (bs : List UInt8) :
    Utf8.decodeLossy (Utf8.encode cs ++ bs) = cs ++ Utf8.decodeLossy bs :=
  Utf8.Proofs.Lossy.decodeLossy_encode_append cs bs

theorem Utf.Spec.decodeLossy_append_encode (bs : List UInt8) (cs : List Char) :
    Utf8.decodeLossy (bs ++ Utf8.encode cs) = Utf8.decodeLossy bs ++ cs :=
  Utf8.Proofs.Lossy.decodeLossy_append_encode bs cs

theorem Utf.Spec.substitution_vectors :
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
    -- A cut-short sequence, then `<` and `A`
    Utf8.decodeLossy [0xF0, 0x9F, 0x98, 0x3C] = ['�', '<'] ∧
    Utf8.decodeLossy [0xE2, 0x41, 0x42] = ['�', 'A', 'B'] ∧
    Utf8.decodeLossy [0xE2, 0x82, 0x3C] = ['�', '<'] := by
  decide

theorem Utf.Spec.utf16_encode_eq (cs : List Char) : Utf16.encode cs = Utf.Spec.encode16 cs :=
  Utf16.Proofs.encode_eq cs

theorem Utf.Spec.utf16_decode_iff (us : List UInt16) (cs : List Char) :
    Utf16.decode us = some cs ↔ us = Utf.Spec.encode16 cs := by
  rw [Utf16.Proofs.decode_iff, Utf16.Proofs.encode_eq]

theorem Utf.Spec.utf16_decode_encode (cs : List Char) :
    Utf16.decode (Utf16.encode cs) = some cs :=
  Utf16.Proofs.decode_encode cs

theorem Utf.Spec.utf16_decode_wellFormed (us : List UInt16) :
    (Utf16.decode us).isSome ↔ Utf.Spec.WellFormed16 us := by
  rw [Utf16.Proofs.wellFormed_iff, Option.isSome_iff_exists]
  simp only [Utf16.Proofs.decode_iff]

theorem Utf.Spec.utf16_decode_none_iff (us : List UInt16) :
    Utf16.decode us = none ↔ ∃ l w r, us = l ++ w :: r ∧ Utf.Spec.Unpaired l w r :=
  Utf16.Proofs.decode_none_iff us

theorem Utf.Spec.utf16_encode_length (cs : List Char) :
    (Utf16.encode cs).length = cs.length + (cs.filter fun c => 0x10000 ≤ c.toNat).length :=
  Utf16.Proofs.encode_length cs

theorem Utf.Spec.utf16_decodeLossy_iff (us : List UInt16) (out : List Char) :
    Utf16.decodeLossy us = out ↔ Utf.Spec.Substitutes16 us out :=
  Utf16.Proofs.decodeLossy_iff us out

theorem Utf.Spec.utf16_decodeLossy_unpaired (w : UInt16) (rest : List UInt16) :
    Utf.Spec.Unpaired [] w rest → Utf16.decodeLossy (w :: rest) = '�' :: Utf16.decodeLossy rest :=
  Utf16.Proofs.decodeLossy_unpaired w rest

theorem Utf.Spec.utf16_decodeLossy_of_decode (us : List UInt16) (cs : List Char) :
    Utf16.decode us = some cs → Utf16.decodeLossy us = cs :=
  Utf16.Proofs.decodeLossy_of_decode us cs

theorem Utf.Spec.utf16_decodeLossy_replaces (us : List UInt16) :
    Utf16.decode us = none → '�' ∈ Utf16.decodeLossy us :=
  Utf16.Proofs.decodeLossy_replaces us

theorem Utf.Spec.utf16_decodeLossy_encode_append (cs : List Char) (us : List UInt16) :
    Utf16.decodeLossy (Utf16.encode cs ++ us) = cs ++ Utf16.decodeLossy us :=
  Utf16.Proofs.decodeLossy_encode_append cs us

theorem Utf.Spec.utf16_decodeLossy_append_encode (us : List UInt16) (cs : List Char) :
    Utf16.decodeLossy (us ++ Utf16.encode cs) = Utf16.decodeLossy us ++ cs :=
  Utf16.Proofs.decodeLossy_append_encode us cs

theorem Utf.Spec.utf16_toWellFormed (us : List UInt16) :
    (Utf16.toWellFormed us).length = us.length ∧
    ∀ (i : Nat) (h : i < us.length),
      (Utf.Spec.Unpaired (us.take i) us[i] (us.drop (i + 1)) →
        (Utf16.toWellFormed us)[i]? = some 0xFFFD) ∧
      (¬ Utf.Spec.Unpaired (us.take i) us[i] (us.drop (i + 1)) →
        (Utf16.toWellFormed us)[i]? = some us[i]) :=
  Utf16.Proofs.toWellFormed_spec us

theorem Utf.Spec.utf16_encodeBytes (cs : List Char) :
    Utf16.encodeBE cs = Utf.Spec.serializeBE (Utf.Spec.encode16 cs) ∧
    Utf16.encodeLE cs = Utf.Spec.serializeLE (Utf.Spec.encode16 cs) :=
  Utf16.Proofs.encodeBytes cs

theorem Utf.Spec.utf16be_decode_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeBE bs = some cs ↔ bs = Utf.Spec.serializeBE (Utf.Spec.encode16 cs) :=
  Utf16.Proofs.decodeBE_iff bs cs

theorem Utf.Spec.utf16le_decode_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeLE bs = some cs ↔ bs = Utf.Spec.serializeLE (Utf.Spec.encode16 cs) :=
  Utf16.Proofs.decodeLE_iff bs cs

theorem Utf.Spec.utf16_decodeScheme_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeScheme bs = some cs ↔ Utf.Spec.SchemeReads bs cs :=
  Utf16.Proofs.decodeScheme_iff bs cs

theorem Utf.Spec.utf16_whatwg (bs : List UInt8) :
    Utf16.decodeLossyBE bs = Utf.Spec.whatwgDecode true bs ∧
    Utf16.decodeLossyLE bs = Utf.Spec.whatwgDecode false bs :=
  Utf16.Proofs.whatwg bs

theorem Utf.Spec.utf16_decodeLossyBytes_units (us : List UInt16) :
    Utf16.decodeLossyBE (Utf.Spec.serializeBE us) = Utf16.decodeLossy us ∧
    Utf16.decodeLossyLE (Utf.Spec.serializeLE us) = Utf16.decodeLossy us :=
  Utf16.Proofs.decodeLossyBytes_units us

theorem Utf.Spec.utf16_vectors :
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
    Utf16.decodeLossyBE [0xD8, 0x00, 0x00, 0x41] = ['�', 'A'] := by
  and_intros <;> decide +kernel
