/-
  The decoder of `Utf8/Codec.lean` against Lean core's
  `String.fromUTF8?`: core accepts a byte string exactly when this
  decoder does, and the string it builds has the characters the decoder
  reads.
-/

import Utf8
import Utf.Spec.Defs
import Utf.Proofs.Encode
import Utf.Proofs.Decode

namespace Utf8.Proofs.Core

/-- Our encoding of a list of characters is the byte list of core's
    `List.utf8Encode`. -/
theorem encode_eq_utf8Encode (cs : List Char) : Utf8.encode cs = cs.utf8Encode.toList := by
  rw [List.utf8Encode, Utf8.Proofs.Encode.toList_toByteArray, Utf8.encode]
  congr 1
  funext c
  exact Utf8.Proofs.Encode.encodeChar_eq_core c

/-- The byte array of our encoding is core's `List.utf8Encode`. -/
theorem toByteArray_encode (cs : List Char) : (Utf8.encode cs).toByteArray = cs.utf8Encode := by
  rw [List.utf8Encode, Utf8.encode]
  congr 2
  funext c
  exact Utf8.Proofs.Encode.encodeChar_eq_core c

theorem fromUTF8?_eq (bs : List UInt8) :
    (String.fromUTF8? bs.toByteArray).map String.toList = Utf8.decode bs := by
  unfold String.fromUTF8?
  by_cases h : bs.toByteArray.IsValidUTF8
  · simp only [h, ↓reduceDIte, Option.map_some]
    symm
    rw [Utf8.Proofs.Decode.decode_iff, encode_eq_utf8Encode, String.utf8Encode_toList]
    show bs = (bs.toByteArray).toList
    rw [Utf8.Proofs.Encode.toList_toByteArray]
  · simp only [h, ↓reduceDIte, Option.map_none]
    symm
    cases hd : Utf8.decode bs with
    | none => rfl
    | some cs =>
      exfalso
      apply h
      rw [(Utf8.Proofs.Decode.decode_iff bs cs).mp hd, toByteArray_encode]
      exact ByteArray.isValidUTF8_utf8Encode

end Utf8.Proofs.Core
