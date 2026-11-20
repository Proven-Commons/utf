/-
  The encoder of `Utf8/Codec.lean` against the specification and
  against Lean core: `Utf8.encodeChar` writes the same bytes as the
  bit-level table of RFC 3629 (`Utf.Spec.encodeChar`), and the same bytes
  as core's `String.utf8EncodeChar`; so `Utf8.encode` is `Utf.Spec.encode`,
  and on a string it gives the bytes of `String.toUTF8`.
-/

import Utf8
import Utf.Spec.Defs

namespace Utf8.Proofs.Encode

/-! ## Bit operations as arithmetic -/

/-- Or-ing a number whose low `k` bits are zero with a number below
    `2 ^ k` is adding them. -/
theorem or_eq_add (a b k : Nat) (ha : a % 2 ^ k = 0) (hb : b < 2 ^ k) : a ||| b = a + b := by
  have h := Nat.two_pow_add_eq_or_of_lt hb (a / 2 ^ k)
  rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero ha)] at h
  exact h.symm

theorem and_63 (x : Nat) : x &&& 0b111111 = x % 64 :=
  Nat.and_two_pow_sub_one_eq_mod x 6

/-- A continuation byte as arithmetic: the marker 0x80 plus six bits. -/
theorem contByte_eq (n k : Nat) : Utf.Spec.contByte n k = (0x80 + n / 2 ^ (6 * k) % 0x40).toUInt8 := by
  unfold Utf.Spec.contByte
  rw [Nat.shiftRight_eq_div_pow, and_63, or_eq_add 128 _ 6 rfl (Nat.mod_lt _ (by decide))]

theorem lead2 (n : Nat) (h : n < 0x800) : (0b11000000 ||| n >>> 6) = 0xC0 + n / 0x40 := by
  rw [Nat.shiftRight_eq_div_pow, or_eq_add 192 _ 5 rfl (by simp; omega)]

theorem lead3 (n : Nat) (h : n < 0x10000) : (0b11100000 ||| n >>> 12) = 0xE0 + n / 0x1000 := by
  rw [Nat.shiftRight_eq_div_pow, or_eq_add 224 _ 4 rfl (by simp; omega)]

theorem lead4 (n : Nat) (h : n < 0x110000) : (0b11110000 ||| n >>> 18) = 0xF0 + n / 0x40000 := by
  rw [Nat.shiftRight_eq_div_pow, or_eq_add 240 _ 3 rfl (by simp; omega)]

theorem toNat_lt (c : Char) : c.toNat < 0x110000 := by
  have := c.valid
  simp only [UInt32.isValidChar, Nat.isValidChar] at this
  show c.val.toNat < 0x110000
  omega

/-! ## One character -/

theorem encodeChar_eq (c : Char) : Utf8.encodeChar c = Utf.Spec.encodeChar c := by
  have hc := toNat_lt c
  unfold Utf8.encodeChar Utf.Spec.encodeChar
  simp only [contByte_eq]
  generalize c.toNat = n at *
  by_cases h1 : n < 0x80
  · simp [h1, show n ≤ 0x7F by omega]
  by_cases h2 : n < 0x800
  · simp [h1, h2, show ¬ n ≤ 0x7F by omega, show n ≤ 0x7FF by omega, lead2 n h2]
  by_cases h3 : n < 0x10000
  · simp [h1, h2, h3, show ¬ n ≤ 0x7F by omega, show ¬ n ≤ 0x7FF by omega,
      show n ≤ 0xFFFF by omega, lead3 n h3]
  · simp [h1, h2, h3, show ¬ n ≤ 0x7F by omega, show ¬ n ≤ 0x7FF by omega,
      show ¬ n ≤ 0xFFFF by omega, lead4 n hc]

theorem encode_eq (cs : List Char) : Utf8.encode cs = Utf.Spec.encode cs := by
  unfold Utf8.encode Utf.Spec.encode
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [List.flatMap_cons, ih, encodeChar_eq]

/-! ## Lean core -/

theorem encodeChar_eq_core (c : Char) : Utf8.encodeChar c = String.utf8EncodeChar c := by
  have hc := toNat_lt c
  unfold Utf8.encodeChar String.utf8EncodeChar
  simp only [Char.toNat_val]
  generalize c.toNat = n at *
  by_cases h1 : n < 0x80
  · simp [h1, show n ≤ 0x7F by omega]
  by_cases h2 : n < 0x800
  · simp only [h1, h2, show ¬ n ≤ 0x7F by omega, show n ≤ 0x7FF by omega, ↓reduceIte]
    rw [show n / 64 % 32 + 192 = 192 + n / 64 by omega, show n % 64 + 128 = 128 + n % 64 by omega]
  by_cases h3 : n < 0x10000
  · simp only [h1, h2, h3, show ¬ n ≤ 0x7F by omega, show ¬ n ≤ 0x7FF by omega,
      show n ≤ 0xFFFF by omega, ↓reduceIte]
    rw [show n / 4096 % 16 + 224 = 224 + n / 4096 by omega,
      show n / 64 % 64 + 128 = 128 + n / 64 % 64 by omega,
      show n % 64 + 128 = 128 + n % 64 by omega]
  · simp only [h1, h2, h3, show ¬ n ≤ 0x7F by omega, show ¬ n ≤ 0x7FF by omega,
      show ¬ n ≤ 0xFFFF by omega, ↓reduceIte]
    rw [show n / 262144 % 8 + 240 = 240 + n / 262144 by omega,
      show n / 4096 % 64 + 128 = 128 + n / 4096 % 64 by omega,
      show n / 64 % 64 + 128 = 128 + n / 64 % 64 by omega,
      show n % 64 + 128 = 128 + n % 64 by omega]

/-! `ByteArray.toList` reads the bytes of the underlying array in order. -/

theorem toList_loop (b : ByteArray) (i : Nat) (r : List UInt8) :
    ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i := by
  fun_induction ByteArray.toList.loop b i r with
  | case1 i r h ih =>
    have hi : i < b.data.toList.length := by simpa using h
    rw [ih, List.drop_eq_getElem_cons hi]
    have hg : b.get! i = b.data.toList[i] := by
      cases b with
      | mk d =>
        have hd : i < d.size := h
        simp [ByteArray.get!, getElem!_pos d i hd]
    simp [hg]
  | case2 i r h =>
    have hi : b.data.toList.length ≤ i := by simp at h ⊢; omega
    simp [List.drop_eq_nil_of_le hi]

theorem toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  simp [ByteArray.toList, toList_loop]

/-- Reading back a byte array made from a list of bytes gives the list. -/
theorem toList_toByteArray (l : List UInt8) : l.toByteArray.toList = l := by
  rw [toList_eq, List.toList_data_toByteArray]

theorem encode_toUTF8 (s : String) : Utf8.encode s.toList = s.toUTF8.toList := by
  rw [String.toUTF8_eq_toByteArray, ← String.utf8Encode_toList, List.utf8Encode,
    toList_toByteArray, Utf8.encode]
  congr 1
  funext c
  exact encodeChar_eq_core c

end Utf8.Proofs.Encode
