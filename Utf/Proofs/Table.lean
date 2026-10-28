/-
  Table 3-7 of the Unicode Standard against the encoder of
  `Utf8/Codec.lean`: a byte list is one well-formed row of the table
  exactly when it is `Utf8.encodeChar c` for some character `c`, and a
  byte list is well formed (rows one after another) exactly when it is
  `Utf8.encode cs` for some list of characters `cs`.
-/

import Utf8
import Utf.Spec.Defs

namespace Utf8.Proofs.Table

/-! ## Characters and bytes as numbers -/

/-- The code point of a character is a Unicode scalar value. -/
theorem toNat_range (c : Char) :
    c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  show c.val.toNat < 0xD800 ∨ (0xDFFF < c.val.toNat ∧ c.val.toNat < 0x110000)
  omega

/-- `Char.ofNat` keeps a Unicode scalar value as it is. -/
theorem toNat_ofNat (n : Nat) (h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by simp only [Nat.isValidChar]; omega
  simp only [Char.ofNat, hv, ↓reduceDIte, Char.ofNatAux, Char.toNat]
  simp

/-- A byte is determined by its value. -/
theorem eq_toUInt8 (b : UInt8) (m : Nat) (h : b.toNat = m % 256) : b = m.toUInt8 := by
  apply UInt8.toNat_inj.mp
  simpa using h

/-! ## One character -/

/-- Each encoded character is one row of Table 3-7. -/
theorem encodeChar_wellFormed (c : Char) : Utf.Spec.WellFormedChar (Utf8.encodeChar c) := by
  have hc := toNat_range c
  unfold Utf8.encodeChar
  generalize c.toNat = n at *
  by_cases h1 : n < 0x80
  · simp [h1, Utf.Spec.WellFormedChar, Utf.Spec.InRange]
    omega
  by_cases h2 : n < 0x800
  · simp [h1, h2, Utf.Spec.WellFormedChar, Utf.Spec.InRange]
    omega
  by_cases h3 : n < 0x10000
  · simp [h1, h2, h3, Utf.Spec.WellFormedChar, Utf.Spec.InRange]
    omega
  · simp [h1, h2, h3, Utf.Spec.WellFormedChar, Utf.Spec.InRange]
    omega

/-- Each row of Table 3-7 is an encoded character. -/
theorem wellFormedChar_encode (s : List UInt8) (h : Utf.Spec.WellFormedChar s) :
    ∃ c, s = Utf8.encodeChar c := by
  have hb := UInt8.toNat_lt_size
  match s, h with
  | [b0], h =>
    simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange] at h
    have h0 := hb b0
    refine ⟨Char.ofNat b0.toNat, ?_⟩
    unfold Utf8.encodeChar
    rw [toNat_ofNat _ (by omega)]
    simp only [show b0.toNat < 0x80 by omega, ↓reduceIte, List.cons.injEq, and_true]
    exact eq_toUInt8 _ _ (by omega)
  | [b0, b1], h =>
    simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange] at h
    have h0 := hb b0
    have h1 := hb b1
    refine ⟨Char.ofNat ((b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80)), ?_⟩
    unfold Utf8.encodeChar
    rw [toNat_ofNat _ (by omega)]
    simp only [show ¬ (b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80) < 0x80 by omega,
      show (b0.toNat - 0xC0) * 0x40 + (b1.toNat - 0x80) < 0x800 by omega,
      ↓reduceIte, List.cons.injEq, and_true]
    exact ⟨eq_toUInt8 _ _ (by omega), eq_toUInt8 _ _ (by omega)⟩
  | [b0, b1, b2], h =>
    simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange] at h
    have h0 := hb b0
    have h1 := hb b1
    have h2 := hb b2
    refine ⟨Char.ofNat ((b0.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
      (b2.toNat - 0x80)), ?_⟩
    unfold Utf8.encodeChar
    rw [toNat_ofNat _ (by omega)]
    simp only [show ¬ (b0.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
        (b2.toNat - 0x80) < 0x80 by omega,
      show ¬ (b0.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
        (b2.toNat - 0x80) < 0x800 by omega,
      show (b0.toNat - 0xE0) * 0x1000 + (b1.toNat - 0x80) * 0x40 +
        (b2.toNat - 0x80) < 0x10000 by omega,
      ↓reduceIte, List.cons.injEq, and_true]
    exact ⟨eq_toUInt8 _ _ (by omega), eq_toUInt8 _ _ (by omega), eq_toUInt8 _ _ (by omega)⟩
  | [b0, b1, b2, b3], h =>
    simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange] at h
    have h0 := hb b0
    have h1 := hb b1
    have h2 := hb b2
    have h3 := hb b3
    refine ⟨Char.ofNat ((b0.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
      (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80)), ?_⟩
    unfold Utf8.encodeChar
    rw [toNat_ofNat _ (by omega)]
    simp only [show ¬ (b0.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
        (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) < 0x80 by omega,
      show ¬ (b0.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
        (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) < 0x800 by omega,
      show ¬ (b0.toNat - 0xF0) * 0x40000 + (b1.toNat - 0x80) * 0x1000 +
        (b2.toNat - 0x80) * 0x40 + (b3.toNat - 0x80) < 0x10000 by omega,
      ↓reduceIte, List.cons.injEq, and_true]
    exact ⟨eq_toUInt8 _ _ (by omega), eq_toUInt8 _ _ (by omega), eq_toUInt8 _ _ (by omega),
      eq_toUInt8 _ _ (by omega)⟩

theorem wellFormedChar_iff (s : List UInt8) : Utf.Spec.WellFormedChar s ↔ ∃ c, s = Utf8.encodeChar c := by
  constructor
  · exact wellFormedChar_encode s
  · rintro ⟨c, rfl⟩
    exact encodeChar_wellFormed c

/-! ## Byte strings -/

theorem encode_cons (c : Char) (cs : List Char) :
    Utf8.encode (c :: cs) = Utf8.encodeChar c ++ Utf8.encode cs := by
  simp [Utf8.encode, List.flatMap_cons]

theorem wellFormed_iff (bs : List UInt8) : Utf.Spec.WellFormed bs ↔ ∃ cs, bs = Utf8.encode cs := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], rfl⟩
    | cons hs _ ih =>
      obtain ⟨c, rfl⟩ := wellFormedChar_encode _ hs
      obtain ⟨cs, rfl⟩ := ih
      exact ⟨c :: cs, (encode_cons c cs).symm⟩
  · rintro ⟨cs, rfl⟩
    induction cs with
    | nil => exact Utf.Spec.WellFormed.nil
    | cons c cs ih =>
      rw [encode_cons]
      exact Utf.Spec.WellFormed.cons (encodeChar_wellFormed c) ih

end Utf8.Proofs.Table
