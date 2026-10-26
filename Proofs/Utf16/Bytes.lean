/-
  UTF-16 as bytes: UTF-16BE, UTF-16LE and the UTF-16 encoding scheme
  against RFC 2781 and D96 to D98, and the lossy byte decoders on whole
  units.
-/

import Proofs.Utf16.Units

namespace Utf16.Proofs

/-! ## Helpers: bytes of a unit, and units of bytes -/


theorem by_hi (u : UInt16) : (u.toNat / 0x100).toUInt8 = (u >>> 8).toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp [UInt16.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem by_lo (u : UInt16) : (u.toNat % 0x100).toUInt8 = (u &&& 0xFF).toUInt8 := by
  apply UInt8.toNat_inj.mp
  simp
  rw [show (255 : Nat) = 2^8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem by_bytesBE (us : List UInt16) : bytesBE us = Spec.serializeBE us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [bytesBE, Spec.serializeBE, List.flatMap_cons, List.map_cons, List.flatten_cons] at *
    rw [ih, by_hi, by_lo]

theorem by_bytesLE (us : List UInt16) : bytesLE us = Spec.serializeLE us := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [bytesLE, Spec.serializeLE, List.flatMap_cons, List.map_cons, List.flatten_cons] at *
    rw [ih, by_hi, by_lo]

theorem by_unit_bytes (u : UInt16) : unit (u >>> 8).toUInt8 (u &&& 0xFF).toUInt8 = u := by
  rw [← by_hi, ← by_lo]
  apply UInt16.toNat_inj.mp
  simp [unit]
  have := u.toNat_lt
  omega

theorem by_hi_unit (a b : UInt8) : (unit a b >>> 8).toUInt8 = a := by
  rw [← by_hi]
  apply UInt8.toNat_inj.mp
  simp [unit]
  have := a.toNat_lt
  have := b.toNat_lt
  omega

theorem by_lo_unit (a b : UInt8) : (unit a b &&& 0xFF).toUInt8 = b := by
  rw [← by_lo]
  apply UInt8.toNat_inj.mp
  have := a.toNat_lt
  have := b.toNat_lt
  simp [unit] <;> omega

theorem by_units_serializeBE (us : List UInt16) :
    units true (Spec.serializeBE us) = (us, none) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [Spec.serializeBE, List.map_cons, List.flatten_cons, List.cons_append,
      List.nil_append] at *
    simp only [units, ih, by_unit_bytes, ite_true]

theorem by_units_serializeLE (us : List UInt16) :
    units false (Spec.serializeLE us) = (us, none) := by
  induction us with
  | nil => rfl
  | cons u us ih =>
    simp only [Spec.serializeLE, List.map_cons, List.flatten_cons, List.cons_append,
      List.nil_append] at *
    simp only [units, ih, by_unit_bytes, Bool.false_eq_true, ite_false]

theorem by_serializeBE_units : (bs : List UInt8) → (us : List UInt16) →
    units true bs = (us, none) → bs = Spec.serializeBE us
  | [], us, h => by
    simp only [units, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | [b], us, h => by simp [units] at h
  | a :: b :: rest, us, h => by
    simp only [units, ite_true] at h
    have ih := by_serializeBE_units rest (units true rest).1
    revert h ih
    rcases units true rest with ⟨vs, last⟩
    intro h ih
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    rw [ih rfl]
    simp only [Spec.serializeBE, List.map_cons, List.flatten_cons, by_hi_unit, by_lo_unit,
      List.cons_append, List.nil_append]

theorem by_serializeLE_units : (bs : List UInt8) → (us : List UInt16) →
    units false bs = (us, none) → bs = Spec.serializeLE us
  | [], us, h => by
    simp only [units, Prod.mk.injEq] at h
    rw [← h.1]; rfl
  | [b], us, h => by simp [units] at h
  | a :: b :: rest, us, h => by
    simp only [units, Bool.false_eq_true, ite_false] at h
    have ih := by_serializeLE_units rest (units false rest).1
    revert h ih
    rcases units false rest with ⟨vs, last⟩
    intro h ih
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    rw [ih rfl]
    simp only [Spec.serializeLE, List.map_cons, List.flatten_cons, by_hi_unit, by_lo_unit,
      List.cons_append, List.nil_append]

/-! ## The statements -/

theorem encodeBytes (cs : List Char) :
    Utf16.encodeBE cs = Spec.serializeBE (Spec.encode16 cs) ∧
    Utf16.encodeLE cs = Spec.serializeLE (Spec.encode16 cs) := by
  refine ⟨?_, ?_⟩
  · rw [encodeBE, by_bytesBE, encode_eq]
  · rw [encodeLE, by_bytesLE, encode_eq]

theorem decodeBE_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeBE bs = some cs ↔ bs = Spec.serializeBE (Spec.encode16 cs) := by
  constructor
  · intro h
    unfold decodeBE decodeBytes at h
    have hs := by_serializeBE_units bs
    revert h hs
    rcases units true bs with ⟨us, last⟩
    intro h hs
    cases last with
    | some _ => simp at h
    | none =>
      simp only at h
      rw [hs us rfl, (decode_iff us cs).1 h, encode_eq]
  · intro h
    subst h
    unfold decodeBE decodeBytes
    rw [by_units_serializeBE, ← encode_eq]
    exact decode_encode cs

theorem decodeLE_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeLE bs = some cs ↔ bs = Spec.serializeLE (Spec.encode16 cs) := by
  constructor
  · intro h
    unfold decodeLE decodeBytes at h
    have hs := by_serializeLE_units bs
    revert h hs
    rcases units false bs with ⟨us, last⟩
    intro h hs
    cases last with
    | some _ => simp at h
    | none =>
      simp only at h
      rw [hs us rfl, (decode_iff us cs).1 h, encode_eq]
  · intro h
    subst h
    unfold decodeLE decodeBytes
    rw [by_units_serializeLE, ← encode_eq]
    exact decode_encode cs

theorem decodeScheme_iff (bs : List UInt8) (cs : List Char) :
    Utf16.decodeScheme bs = some cs ↔ Spec.SchemeReads bs cs := by
  unfold Spec.SchemeReads
  match bs with
  | [] =>
    simp only [decodeScheme, decodeBE_iff]
    simp
  | [x] =>
    simp only [decodeScheme, decodeBE_iff]
    simp
  | a :: b :: rest =>
    simp only [decodeScheme]
    by_cases h1 : a = 0xFE ∧ b = 0xFF
    · obtain ⟨rfl, rfl⟩ := h1
      simp [decodeBE_iff]
    · by_cases h2 : a = 0xFF ∧ b = 0xFE
      · obtain ⟨rfl, rfl⟩ := h2
        simp [decodeLE_iff]
      · simp only [h1, h2, ↓reduceIte, decodeBE_iff]
        simp only [List.take_succ_cons, List.take_zero, List.cons_append, List.nil_append,
          List.cons.injEq, ne_eq]
        constructor
        · intro h
          exact Or.inr (Or.inr ⟨fun h' => h1 ⟨h'.1, h'.2.1⟩, fun h' => h2 ⟨h'.1, h'.2.1⟩, h⟩)
        · rintro (⟨ha, hb, _⟩ | ⟨ha, hb, _⟩ | ⟨_, _, h⟩)
          · exact absurd ⟨ha, hb⟩ h1
          · exact absurd ⟨ha, hb⟩ h2
          · exact h

theorem decodeLossyBytes_units (us : List UInt16) :
    Utf16.decodeLossyBE (Spec.serializeBE us) = Utf16.decodeLossy us ∧
    Utf16.decodeLossyLE (Spec.serializeLE us) = Utf16.decodeLossy us := by
  refine ⟨?_, ?_⟩
  · unfold decodeLossyBE decodeLossyBytes
    rw [by_units_serializeBE]
  · unfold decodeLossyLE decodeLossyBytes
    rw [by_units_serializeLE]

end Utf16.Proofs
