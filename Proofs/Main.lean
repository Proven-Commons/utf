/-
  The statements of `Spec.lean`, under the same names, from the lemmas
  in the other files of `Proofs/`. The test vectors are checked by
  evaluation.
-/

import Utf8
import Spec.Defs
import Proofs.Encode
import Proofs.Decode
import Proofs.Table
import Proofs.Core
import Proofs.Lossy.Main

theorem Spec.encode_eq (cs : List Char) : Utf8.encode cs = Spec.encode cs :=
  Utf8.Proofs.Encode.encode_eq cs

theorem Spec.decode_iff (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs ↔ bs = Spec.encode cs := by
  rw [Utf8.Proofs.Decode.decode_iff, Utf8.Proofs.Encode.encode_eq]

theorem Spec.decode_encode (cs : List Char) : Utf8.decode (Utf8.encode cs) = some cs :=
  Utf8.Proofs.Decode.decode_encode cs

theorem Spec.decode_wellFormed (bs : List UInt8) :
    (Utf8.decode bs).isSome ↔ Spec.WellFormed bs := by
  rw [Utf8.Proofs.Table.wellFormed_iff, Option.isSome_iff_exists]
  simp only [Utf8.Proofs.Decode.decode_iff]

theorem Spec.encode_toUTF8 (s : String) : Utf8.encode s.toList = s.toUTF8.toList :=
  Utf8.Proofs.Encode.encode_toUTF8 s

theorem Spec.fromUTF8?_eq (bs : List UInt8) :
    (String.fromUTF8? bs.toByteArray).map String.toList = Utf8.decode bs :=
  Utf8.Proofs.Core.fromUTF8?_eq bs

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
      some ['\uFEFF', Char.ofNat 0x233B4] := by
  decide

theorem Spec.boundary_vectors :
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
    Utf8.decode [0xC2, 0x41] = none := by
  decide

theorem Spec.decodeLossy_iff (bs : List UInt8) (out : List Char) :
    Utf8.decodeLossy bs = out ↔ Spec.Substitutes bs out :=
  Utf8.Proofs.Lossy.decodeLossy_iff bs out

theorem Spec.decodeLossy_of_decode (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs → Utf8.decodeLossy bs = cs :=
  Utf8.Proofs.Lossy.decodeLossy_of_decode bs cs

theorem Spec.decodeLossy_replaces (bs : List UInt8) :
    Utf8.decode bs = none → '�' ∈ Utf8.decodeLossy bs :=
  Utf8.Proofs.Lossy.decodeLossy_replaces bs

theorem Spec.decodeLossy_encode_append (cs : List Char) (bs : List UInt8) :
    Utf8.decodeLossy (Utf8.encode cs ++ bs) = cs ++ Utf8.decodeLossy bs :=
  Utf8.Proofs.Lossy.decodeLossy_encode_append cs bs

theorem Spec.decodeLossy_append_encode (bs : List UInt8) (cs : List Char) :
    Utf8.decodeLossy (bs ++ Utf8.encode cs) = Utf8.decodeLossy bs ++ cs :=
  Utf8.Proofs.Lossy.decodeLossy_append_encode bs cs

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
    -- A cut-short sequence, then `<` and `A`
    Utf8.decodeLossy [0xF0, 0x9F, 0x98, 0x3C] = ['�', '<'] ∧
    Utf8.decodeLossy [0xE2, 0x41, 0x42] = ['�', 'A', 'B'] := by
  decide
