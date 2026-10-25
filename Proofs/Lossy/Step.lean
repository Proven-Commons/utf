/-
  Byte arithmetic about one step of the lossy decoder: `badLength` gives
  the longest prefix that `prefixB` accepts, and appending bytes that do
  not start with a continuation byte changes nothing at the front.
-/

import Utf8
import Spec.Defs
import Proofs.Decode
import Proofs.Lossy.Defs

namespace Utf8.Proofs.Lossy

open Utf8

/-! ## Helpers: bytes as ranges -/

theorem stp_isCont_iff (b : UInt8) : isCont b = true ↔ 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF := by
  simp [isCont]

theorem stp_secondOK_iff (x : Nat) (b : UInt8) : secondOK x b = true ↔
    (x = 0xE0 → 0xA0 ≤ b.toNat ∧ b.toNat ≤ 0xBF) ∧
    (x = 0xED → 0x80 ≤ b.toNat ∧ b.toNat ≤ 0x9F) ∧
    (x = 0xF0 → 0x90 ≤ b.toNat ∧ b.toNat ≤ 0xBF) ∧
    (x = 0xF4 → 0x80 ≤ b.toNat ∧ b.toNat ≤ 0x8F) ∧
    (0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF) := by
  unfold secondOK
  repeat' split
  all_goals simp_all <;> omega

/-- A byte that is not a continuation byte never comes second. -/
theorem stp_secondOK_cont {x : Nat} {b : UInt8} (h : isCont b = false) : secondOK x b = false := by
  unfold secondOK
  unfold isCont at h
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at h
  repeat' split
  all_goals simp; omega

/-! ## Helpers: where `decodeChar` succeeds -/

theorem stp_dec2 {b0 b1 : UInt8} (r : List UInt8) (h0 : 0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF)
    (h1 : isCont b1 = true) : decodeChar (b0 :: b1 :: r) ≠ none := by
  rw [stp_isCont_iff] at h1
  rw [Decode.decodeChar_2 (x := b0.toNat) (t := b1.toNat - 0x80) rfl (by omega) (by omega)
    (by omega) (by omega)]
  simp

theorem stp_dec3 {b0 b1 b2 : UInt8} (r : List UInt8) (h0 : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xEF)
    (h1 : secondOK b0.toNat b1 = true) (h2 : isCont b2 = true) :
    decodeChar (b0 :: b1 :: b2 :: r) ≠ none := by
  rw [stp_isCont_iff] at h2
  rw [stp_secondOK_iff] at h1
  rw [Decode.decodeChar_3 (x := b0.toNat) (t1 := b1.toNat - 0x80) (t2 := b2.toNat - 0x80) rfl
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  · simp
  · by_cases e0 : b0.toNat = 0xE0
    · have := h1.1 e0; omega
    by_cases ed : b0.toNat = 0xED
    · have := h1.2.1 ed; omega
    omega

theorem stp_dec4 {b0 b1 b2 b3 : UInt8} (r : List UInt8) (h0 : 0xF0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4)
    (h1 : secondOK b0.toNat b1 = true) (h2 : isCont b2 = true) (h3 : isCont b3 = true) :
    decodeChar (b0 :: b1 :: b2 :: b3 :: r) ≠ none := by
  rw [stp_isCont_iff] at h2 h3
  rw [stp_secondOK_iff] at h1
  rw [Decode.decodeChar_4 (x := b0.toNat) (t1 := b1.toNat - 0x80) (t2 := b2.toNat - 0x80)
    (t3 := b3.toNat - 0x80) rfl (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega)]
  · simp
  · by_cases e0 : b0.toNat = 0xF0
    · have := h1.2.2.1 e0; omega
    omega
  · by_cases e4 : b0.toNat = 0xF4
    · have := h1.2.2.2.1 e4; omega
    omega

/-! ## Helpers: the bytes of one character -/

/-- The first byte of a character's encoding is not a continuation byte. -/
theorem stp_encodeChar_head (c : Char) : ∃ b s, encodeChar c = b :: s ∧ isCont b = false := by
  have hv := Decode.toNat_valid c
  by_cases h1 : c.toNat < 0x80
  · rw [Decode.encodeChar_1 c h1]
    refine ⟨_, _, rfl, ?_⟩
    simp only [isCont, Decode.toNat_toUInt8, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  by_cases h2 : c.toNat < 0x800
  · rw [Decode.encodeChar_2 c (by omega) h2]
    refine ⟨_, _, rfl, ?_⟩
    simp only [isCont, Decode.toNat_toUInt8, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  by_cases h3 : c.toNat < 0x10000
  · rw [Decode.encodeChar_3 c (by omega) h3]
    refine ⟨_, _, rfl, ?_⟩
    simp only [isCont, Decode.toNat_toUInt8, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  · rw [Decode.encodeChar_4 c (by omega)]
    refine ⟨_, _, rfl, ?_⟩
    simp only [isCont, Decode.toNat_toUInt8, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega

/-- Every byte after the first of a character's encoding is a continuation byte. -/
theorem stp_encodeChar_tail_cont (c : Char) : ∀ e ∈ (encodeChar c).tail, isCont e = true := by
  have hv := Decode.toNat_valid c
  by_cases h1 : c.toNat < 0x80
  · rw [Decode.encodeChar_1 c h1]
    simp
  by_cases h2 : c.toNat < 0x800
  · rw [Decode.encodeChar_2 c (by omega) h2]
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq,
      stp_isCont_iff, Decode.toNat_toUInt8]
    omega
  by_cases h3 : c.toNat < 0x10000
  · rw [Decode.encodeChar_3 c (by omega) h3]
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, stp_isCont_iff, Decode.toNat_toUInt8]
    omega
  · rw [Decode.encodeChar_4 c (by omega)]
    simp only [List.tail_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, stp_isCont_iff, Decode.toNat_toUInt8]
    omega

/-! ## `badLength` -/

theorem badLength_pos (b0 : UInt8) (rest : List UInt8) : 1 ≤ badLength b0 rest := by
  rcases rest with _ | ⟨b1, _ | ⟨b2, r⟩⟩ <;> simp only [badLength] <;> repeat' split
  all_goals omega

theorem badLength_le (b0 : UInt8) (rest : List UInt8) :
    badLength b0 rest ≤ (b0 :: rest).length := by
  rcases rest with _ | ⟨b1, _ | ⟨b2, r⟩⟩ <;>
    simp only [badLength, List.length_cons, List.length_nil] <;> repeat' split
  all_goals omega

/-- Where no character can be read, a replacement of two or more bytes
    covers the start of a character's bytes. -/
theorem badLength_prefix (b0 : UInt8) (rest : List UInt8) (h : decodeChar (b0 :: rest) = none)
    (h2 : 2 ≤ badLength b0 rest) :
    prefixB ((b0 :: rest).take (badLength b0 rest)) = true := by
  rcases rest with _ | ⟨b1, _ | ⟨b2, r⟩⟩
  · simp [badLength] at h2
  · by_cases hx : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4
    · by_cases hs : secondOK b0.toNat b1 = true
      · simp [badLength, hx, hs, prefixB]
      · simp [badLength, hx, hs] at h2
    · simp [badLength, hx] at h2
  · by_cases hx : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4
    · by_cases hs : secondOK b0.toNat b1 = true
      · by_cases h3 : 0xF0 ≤ b0.toNat ∧ isCont b2 = true
        · simp [badLength, hx, hs, h3, prefixB]
        · simp [badLength, hx, hs, h3, prefixB]
      · simp [badLength, hx, hs] at h2
    · simp [badLength, hx] at h2

/-- Where no character can be read, one more byte would not begin a
    character's bytes. -/
theorem badLength_max (b0 : UInt8) (rest : List UInt8) (h : decodeChar (b0 :: rest) = none)
    (hlt : badLength b0 rest < (b0 :: rest).length) :
    prefixB ((b0 :: rest).take (badLength b0 rest + 1)) = false := by
  rcases rest with _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, r⟩⟩⟩
  · simp [badLength] at hlt
  · have hc2 : ¬ (0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF ∧ isCont b1 = true) := fun hc =>
      stp_dec2 [] ⟨hc.1, hc.2.1⟩ hc.2.2 h
    by_cases hx : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4 <;> cases hs : secondOK b0.toNat b1 <;>
      simp only [badLength, hx, hs, ↓reduceIte, Bool.false_eq_true] at hlt ⊢ <;>
      cases hb1 : isCont b1 <;> simp_all [prefixB] <;> omega
  · have hc2 : ¬ (0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF ∧ isCont b1 = true) := fun hc =>
      stp_dec2 _ ⟨hc.1, hc.2.1⟩ hc.2.2 h
    have hc3 : ¬ (0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xEF ∧ secondOK b0.toNat b1 = true ∧
        isCont b2 = true) := fun hc =>
      stp_dec3 [] ⟨hc.1, hc.2.1⟩ hc.2.2.1 hc.2.2.2 h
    by_cases hx : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4 <;> cases hs : secondOK b0.toNat b1 <;>
      by_cases hf : 0xF0 ≤ b0.toNat ∧ isCont b2 = true <;>
      simp only [badLength, hx, hs, hf, ↓reduceIte, Bool.false_eq_true] at hlt ⊢ <;>
      cases hb1 : isCont b1 <;> cases hb2 : isCont b2 <;> simp_all [prefixB] <;> omega
  · have hc2 : ¬ (0xC2 ≤ b0.toNat ∧ b0.toNat ≤ 0xDF ∧ isCont b1 = true) := fun hc =>
      stp_dec2 _ ⟨hc.1, hc.2.1⟩ hc.2.2 h
    have hc3 : ¬ (0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xEF ∧ secondOK b0.toNat b1 = true ∧
        isCont b2 = true) := fun hc =>
      stp_dec3 _ ⟨hc.1, hc.2.1⟩ hc.2.2.1 hc.2.2.2 h
    have hc4 : ¬ (0xF0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4 ∧ secondOK b0.toNat b1 = true ∧
        isCont b2 = true ∧ isCont b3 = true) := fun hc =>
      stp_dec4 _ ⟨hc.1, hc.2.1⟩ hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2 h
    by_cases hx : 0xE0 ≤ b0.toNat ∧ b0.toNat ≤ 0xF4 <;> cases hs : secondOK b0.toNat b1 <;>
      by_cases hf : 0xF0 ≤ b0.toNat ∧ isCont b2 = true <;>
      simp only [badLength, hx, hs, hf, ↓reduceIte, Bool.false_eq_true] at hlt ⊢ <;>
      cases hb1 : isCont b1 <;> cases hb2 : isCont b2 <;> cases hb3 : isCont b3 <;>
      simp_all [prefixB] <;> omega

/-- The prefixes of a prefix of a character's bytes are prefixes too. -/
theorem prefixB_take (q : List UInt8) (n : Nat) (h : prefixB q = true) :
    prefixB (q.take n) = true := by
  rcases q with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, q⟩⟩⟩⟩⟩ <;>
    rcases n with _ | _ | _ | _ | n <;> simp_all [prefixB] <;> omega

/-- An encoding never starts with a continuation byte. -/
theorem encode_noContHead (cs : List Char) : NoContHead (Utf8.encode cs) := by
  intro b E' hE
  cases cs with
  | nil => simp [encode] at hE
  | cons c cs =>
    rw [Decode.encode_cons] at hE
    obtain ⟨b', s, hs, hb'⟩ := stp_encodeChar_head c
    rw [hs, List.cons_append, List.cons.injEq] at hE
    rw [← hE.1]
    exact hb'

theorem decodeChar_append_none (b0 : UInt8) (rest E : List UInt8) (hE : NoContHead E)
    (h : decodeChar (b0 :: rest) = none) : decodeChar (b0 :: (rest ++ E)) = none := by
  cases hd : decodeChar (b0 :: (rest ++ E)) with
  | none => rfl
  | some p =>
    obtain ⟨c, r⟩ := p
    have h1 := (Decode.decodeChar_iff _ c r).mp hd
    rw [← List.cons_append] at h1
    rcases List.append_eq_append_iff.mp h1 with ⟨a', h2, h3⟩ | ⟨c', h2, h3⟩
    · -- the character's bytes run past `b0 :: rest` into `E`
      cases a' with
      | nil =>
        rw [List.append_nil] at h2
        rw [(Decode.decodeChar_iff _ c []).mpr (by rw [List.append_nil]; exact h2.symm)] at h
        simp at h
      | cons e a'' =>
        have he := hE e (a'' ++ r) (by rw [h3, List.cons_append])
        have ht := stp_encodeChar_tail_cont c e (by rw [h2]; simp)
        rw [he] at ht
        simp at ht
    · -- the character's bytes fit inside `b0 :: rest`
      rw [(Decode.decodeChar_iff _ c c').mpr h2] at h
      simp at h

theorem badLength_append (b0 : UInt8) (rest E : List UInt8) (hE : NoContHead E) :
    badLength b0 (rest ++ E) = badLength b0 rest := by
  rcases rest with _ | ⟨b1, _ | ⟨b2, r⟩⟩
  · rcases E with _ | ⟨e1, _ | ⟨e2, E⟩⟩
    · rfl
    · have := stp_secondOK_cont (x := b0.toNat) (hE e1 [] rfl); simp [badLength, this]
    · have := stp_secondOK_cont (x := b0.toNat) (hE e1 _ rfl); simp [badLength, this]
  · rcases E with _ | ⟨e1, E⟩
    · rfl
    · have := hE e1 E rfl; simp [badLength, this]
  · rfl

end Utf8.Proofs.Lossy
