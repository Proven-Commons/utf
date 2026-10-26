/-
  The decoder of `Utf8/Codec.lean` against the encoder. `decodeChar`
  reads the character `c` and leaves `rest` exactly when the bytes are
  `encodeChar c ++ rest`; `decode` returns `cs` exactly when the bytes
  are `encode cs`; and decoding what the encoder wrote gives the
  characters back.
-/

import Utf8
import Spec.Defs

namespace Utf8.Proofs.Decode

open Utf8

/-! ## Bytes and characters as numbers -/

theorem toNat_toUInt8 (n : Nat) : n.toUInt8.toNat = n % 256 := by
  simp [Nat.toUInt8]

/-- A byte equals `m.toUInt8` when their values agree modulo 256. -/
theorem eq_toUInt8 {b : UInt8} {m : Nat} (h : m % 256 = b.toNat) : b = m.toUInt8 :=
  (UInt8.toNat_inj.mp (by rw [toNat_toUInt8]; exact h)).symm

theorem toNat_ofNat_of_valid {n : Nat} (h : n.isValidChar) : (Char.ofNat n).toNat = n := by
  simp [Char.ofNat, h, Char.ofNatAux, Char.toNat]

/-- A character's code point is a Unicode scalar value. -/
theorem toNat_valid (c : Char) :
    c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid

theorem toNat_ofNat_of {n : Nat} (h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n :=
  toNat_ofNat_of_valid h

/-! ## `encodeChar` by range -/

theorem encodeChar_1 (c : Char) (h : c.toNat < 0x80) : encodeChar c = [c.toNat.toUInt8] := by
  simp only [encodeChar, h, ↓reduceIte]

theorem encodeChar_2 (c : Char) (h1 : 0x80 ≤ c.toNat) (h2 : c.toNat < 0x800) :
    encodeChar c = [(0xC0 + c.toNat / 0x40).toUInt8, (0x80 + c.toNat % 0x40).toUInt8] := by
  have a1 : ¬ c.toNat < 0x80 := by omega
  simp only [encodeChar, a1, h2, ↓reduceIte]

theorem encodeChar_3 (c : Char) (h1 : 0x800 ≤ c.toNat) (h2 : c.toNat < 0x10000) :
    encodeChar c = [(0xE0 + c.toNat / 0x1000).toUInt8, (0x80 + c.toNat / 0x40 % 0x40).toUInt8,
      (0x80 + c.toNat % 0x40).toUInt8] := by
  have a1 : ¬ c.toNat < 0x80 := by omega
  have a2 : ¬ c.toNat < 0x800 := by omega
  simp only [encodeChar, a1, a2, h2, ↓reduceIte]

theorem encodeChar_4 (c : Char) (h1 : 0x10000 ≤ c.toNat) :
    encodeChar c = [(0xF0 + c.toNat / 0x40000).toUInt8, (0x80 + c.toNat / 0x1000 % 0x40).toUInt8,
      (0x80 + c.toNat / 0x40 % 0x40).toUInt8, (0x80 + c.toNat % 0x40).toUInt8] := by
  have a1 : ¬ c.toNat < 0x80 := by omega
  have a2 : ¬ c.toNat < 0x800 := by omega
  have a3 : ¬ c.toNat < 0x10000 := by omega
  simp only [encodeChar, a1, a2, a3, ↓reduceIte]

theorem encodeChar_ne_nil (c : Char) : encodeChar c ≠ [] := by
  simp only [encodeChar]
  split
  · simp
  · split
    · simp
    · split <;> simp

theorem encode_cons (c : Char) (cs : List Char) : encode (c :: cs) = encodeChar c ++ encode cs := by
  simp [encode, List.flatMap_cons]

/-! ## Continuation bytes -/

theorem tail_eq {b : UInt8} {t : Nat} (h1 : b.toNat = 0x80 + t) (ht : t < 0x40) :
    tail b = some t := by
  unfold tail
  rw [h1]
  have hc : 0x80 ≤ 0x80 + t ∧ 0x80 + t ≤ 0xBF := by omega
  simp only [hc, and_self, ↓reduceIte, Nat.add_sub_cancel_left]

theorem tail_some {b : UInt8} {t : Nat} (h : tail b = some t) : b.toNat = 0x80 + t ∧ t < 0x40 := by
  unfold tail at h
  split at h
  · simp only [Option.some.injEq] at h; omega
  · simp at h

/-! ## `decodeChar` on each shape -/

theorem decodeChar_1 {b0 : UInt8} {rest : List UInt8} (h0 : b0.toNat < 0x80) :
    decodeChar (b0 :: rest) = some (Char.ofNat b0.toNat, rest) := by
  simp only [decodeChar, h0, ↓reduceIte]

theorem decodeChar_2 {b0 b1 : UInt8} {rest : List UInt8} {x t : Nat}
    (h0 : b0.toNat = x) (h1 : b1.toNat = 0x80 + t) (hx1 : 0xC2 ≤ x) (hx2 : x < 0xE0)
    (ht : t < 0x40) :
    decodeChar (b0 :: b1 :: rest) = some (Char.ofNat ((x - 0xC0) * 0x40 + t), rest) := by
  have a1 : ¬ x < 0x80 := by omega
  have a2 : ¬ x < 0xC2 := by omega
  simp only [decodeChar, h0, a1, a2, hx2, tail_eq h1 ht, ↓reduceIte]

theorem decodeChar_3 {b0 b1 b2 : UInt8} {rest : List UInt8} {x t1 t2 : Nat}
    (h0 : b0.toNat = x) (h1 : b1.toNat = 0x80 + t1) (h2 : b2.toNat = 0x80 + t2)
    (hx1 : 0xE0 ≤ x) (hx2 : x < 0xF0) (ht1 : t1 < 0x40) (ht2 : t2 < 0x40)
    (hn : 0x800 ≤ (x - 0xE0) * 0x1000 + t1 * 0x40 + t2 ∧
      ¬ (0xD800 ≤ (x - 0xE0) * 0x1000 + t1 * 0x40 + t2 ∧
        (x - 0xE0) * 0x1000 + t1 * 0x40 + t2 ≤ 0xDFFF)) :
    decodeChar (b0 :: b1 :: b2 :: rest) =
      some (Char.ofNat ((x - 0xE0) * 0x1000 + t1 * 0x40 + t2), rest) := by
  have a1 : ¬ x < 0x80 := by omega
  have a2 : ¬ x < 0xC2 := by omega
  have a3 : ¬ x < 0xE0 := by omega
  simp only [decodeChar, h0, a1, a2, a3, hx2, tail_eq h1 ht1, tail_eq h2 ht2, ↓reduceIte]
  split
  · omega
  · rfl

theorem decodeChar_4 {b0 b1 b2 b3 : UInt8} {rest : List UInt8} {x t1 t2 t3 : Nat}
    (h0 : b0.toNat = x) (h1 : b1.toNat = 0x80 + t1) (h2 : b2.toNat = 0x80 + t2)
    (h3 : b3.toNat = 0x80 + t3)
    (hx1 : 0xF0 ≤ x) (hx2 : x < 0xF5) (ht1 : t1 < 0x40) (ht2 : t2 < 0x40) (ht3 : t3 < 0x40)
    (hn1 : 0x10000 ≤ (x - 0xF0) * 0x40000 + t1 * 0x1000 + t2 * 0x40 + t3)
    (hn2 : (x - 0xF0) * 0x40000 + t1 * 0x1000 + t2 * 0x40 + t3 ≤ 0x10FFFF) :
    decodeChar (b0 :: b1 :: b2 :: b3 :: rest) =
      some (Char.ofNat ((x - 0xF0) * 0x40000 + t1 * 0x1000 + t2 * 0x40 + t3), rest) := by
  have a1 : ¬ x < 0x80 := by omega
  have a2 : ¬ x < 0xC2 := by omega
  have a3 : ¬ x < 0xE0 := by omega
  have a4 : ¬ x < 0xF0 := by omega
  simp only [decodeChar, h0, a1, a2, a3, a4, hx2, tail_eq h1 ht1, tail_eq h2 ht2,
    tail_eq h3 ht3, ↓reduceIte]
  split
  · omega
  · rfl

/-! ## Decoding what the encoder wrote -/

theorem decodeChar_encodeChar (c : Char) (rest : List UInt8) :
    decodeChar (encodeChar c ++ rest) = some (c, rest) := by
  have hv := toNat_valid c
  by_cases h1 : c.toNat < 0x80
  · rw [encodeChar_1 c h1, List.singleton_append,
      decodeChar_1 (by rw [toNat_toUInt8]; omega), toNat_toUInt8, Nat.mod_eq_of_lt (by omega),
      Char.ofNat_toNat]
  by_cases h2 : c.toNat < 0x800
  · rw [encodeChar_2 c (by omega) h2]
    simp only [List.cons_append, List.nil_append]
    rw [decodeChar_2 (x := 0xC0 + c.toNat / 0x40) (t := c.toNat % 0x40)
      (by rw [toNat_toUInt8]; omega) (by rw [toNat_toUInt8]; omega) (by omega) (by omega)
      (by omega)]
    have : (0xC0 + c.toNat / 0x40 - 0xC0) * 0x40 + c.toNat % 0x40 = c.toNat := by omega
    rw [this, Char.ofNat_toNat]
  by_cases h3 : c.toNat < 0x10000
  · rw [encodeChar_3 c (by omega) h3]
    simp only [List.cons_append, List.nil_append]
    rw [decodeChar_3 (x := 0xE0 + c.toNat / 0x1000) (t1 := c.toNat / 0x40 % 0x40)
      (t2 := c.toNat % 0x40)
      (by rw [toNat_toUInt8]; omega) (by rw [toNat_toUInt8]; omega)
      (by rw [toNat_toUInt8]; omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    have : (0xE0 + c.toNat / 0x1000 - 0xE0) * 0x1000 + c.toNat / 0x40 % 0x40 * 0x40 +
        c.toNat % 0x40 = c.toNat := by omega
    rw [this, Char.ofNat_toNat]
  · rw [encodeChar_4 c (by omega)]
    simp only [List.cons_append, List.nil_append]
    rw [decodeChar_4 (x := 0xF0 + c.toNat / 0x40000) (t1 := c.toNat / 0x1000 % 0x40)
      (t2 := c.toNat / 0x40 % 0x40) (t3 := c.toNat % 0x40)
      (by rw [toNat_toUInt8]; omega) (by rw [toNat_toUInt8]; omega)
      (by rw [toNat_toUInt8]; omega) (by rw [toNat_toUInt8]; omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    have : (0xF0 + c.toNat / 0x40000 - 0xF0) * 0x40000 + c.toNat / 0x1000 % 0x40 * 0x1000 +
        c.toNat / 0x40 % 0x40 * 0x40 + c.toNat % 0x40 = c.toNat := by omega
    rw [this, Char.ofNat_toNat]

/-! ## What the decoder reads is what the encoder writes -/

theorem decodeChar_sound {bs : List UInt8} {c : Char} {rest : List UInt8}
    (h : decodeChar bs = some (c, rest)) : bs = encodeChar c ++ rest := by
  match bs with
  | [] => simp [decodeChar] at h
  | b0 :: r =>
    have hb0 := UInt8.toNat_lt b0
    simp only [decodeChar] at h
    split at h
    · -- one byte: 0x00 to 0x7F
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc := toNat_ofNat_of (n := b0.toNat) (by omega)
      rw [encodeChar_1 _ (by omega), hc]
      simp only [List.singleton_append, List.cons.injEq, and_true]
      exact eq_toUInt8 (by omega)
    · split at h
      · simp at h
      · split at h
        · -- two bytes: lead 0xC2 to 0xDF
          split at h
          · split at h
            · rename_i b1 r' _ t1 heq
              obtain ⟨ht1, ht1'⟩ := tail_some heq
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hc := toNat_ofNat_of (n := (b0.toNat - 0xC0) * 0x40 + t1) (by omega)
              rw [encodeChar_2 _ (by omega) (by omega), hc]
              simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
              exact ⟨eq_toUInt8 (by omega), eq_toUInt8 (by omega)⟩
            · simp at h
          · simp at h
        · split at h
          · -- three bytes: lead 0xE0 to 0xEF
            split at h
            · split at h
              · rename_i b1 b2 r' _ _ t1 t2 heq1 heq2
                obtain ⟨ht1, ht1'⟩ := tail_some heq1
                obtain ⟨ht2, ht2'⟩ := tail_some heq2
                split at h
                · simp at h
                · simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hc := toNat_ofNat_of
                    (n := (b0.toNat - 0xE0) * 0x1000 + t1 * 0x40 + t2) (by omega)
                  rw [encodeChar_3 _ (by omega) (by omega), hc]
                  simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
                  exact ⟨eq_toUInt8 (by omega), eq_toUInt8 (by omega), eq_toUInt8 (by omega)⟩
              · simp at h
            · simp at h
          · split at h
            · -- four bytes: lead 0xF0 to 0xF4
              split at h
              · split at h
                · rename_i b1 b2 b3 r' _ _ _ t1 t2 t3 heq1 heq2 heq3
                  obtain ⟨ht1, ht1'⟩ := tail_some heq1
                  obtain ⟨ht2, ht2'⟩ := tail_some heq2
                  obtain ⟨ht3, ht3'⟩ := tail_some heq3
                  split at h
                  · simp at h
                  · simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    have hc := toNat_ofNat_of
                      (n := (b0.toNat - 0xF0) * 0x40000 + t1 * 0x1000 + t2 * 0x40 + t3)
                      (by omega)
                    rw [encodeChar_4 _ (by omega), hc]
                    simp only [List.cons_append, List.nil_append, List.cons.injEq, and_true]
                    exact ⟨eq_toUInt8 (by omega), eq_toUInt8 (by omega), eq_toUInt8 (by omega),
                      eq_toUInt8 (by omega)⟩
                · simp at h
              · simp at h
            · simp at h

theorem decodeChar_iff (bs : List UInt8) (c : Char) (rest : List UInt8) :
    Utf8.decodeChar bs = some (c, rest) ↔ bs = Utf8.encodeChar c ++ rest := by
  constructor
  · exact decodeChar_sound
  · rintro rfl
    exact decodeChar_encodeChar c rest

/-! ## Whole inputs -/

theorem decodeAux_sound :
    ∀ (fuel : Nat) (bs : List UInt8) (cs : List Char), decodeAux fuel bs = some cs → bs = encode cs
  | _, [], cs, h => by
    simp only [decodeAux, Option.some.injEq] at h
    subst h
    rfl
  | 0, _ :: _, _, h => by simp [decodeAux] at h
  | fuel + 1, b :: bs, cs, h => by
    simp only [decodeAux] at h
    split at h
    · rename_i c rest hc
      split at h
      · rename_i cs' hcs
        simp only [Option.some.injEq] at h
        subst h
        rw [encode_cons, ← decodeAux_sound fuel rest cs' hcs]
        exact decodeChar_sound hc
      · simp at h
    · simp at h

theorem decodeAux_encode :
    ∀ (cs : List Char) (fuel : Nat), (encode cs).length ≤ fuel → decodeAux fuel (encode cs) = some cs
  | [], fuel, _ => by
    cases fuel <;> rfl
  | c :: cs, fuel, hf => by
    rw [encode_cons] at hf ⊢
    have hne := encodeChar_ne_nil c
    have hlen : 1 ≤ (encodeChar c).length := by
      cases h : encodeChar c with
      | nil => exact absurd h hne
      | cons _ _ => simp
    rw [List.length_append] at hf
    obtain ⟨b, bs, hb⟩ : ∃ b bs, encodeChar c ++ encode cs = b :: bs := by
      cases h : encodeChar c with
      | nil => exact absurd h hne
      | cons b bs => exact ⟨b, bs ++ encode cs, rfl⟩
    obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hdc := decodeChar_encodeChar c (encode cs)
    have ih := decodeAux_encode cs fuel (by omega)
    rw [hb] at hdc ⊢
    simp only [decodeAux, hdc, ih]

theorem decode_iff (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs ↔ bs = Utf8.encode cs := by
  constructor
  · exact decodeAux_sound _ _ _
  · rintro rfl
    exact decodeAux_encode cs _ (Nat.le_refl _)

theorem decode_encode (cs : List Char) : Utf8.decode (Utf8.encode cs) = some cs :=
  (decode_iff _ _).mpr rfl

end Utf8.Proofs.Decode
