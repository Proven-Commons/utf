/-
  The definitions of section 3.9.6 (`Spec.Unconvertible`,
  `Spec.Initial`) in terms of the strict decoder and `prefixB`.
-/

import Utf8
import Spec.Defs
import Proofs.Decode
import Proofs.Table
import Proofs.Lossy.Defs

namespace Utf8.Proofs.Lossy

open Utf8

/-- `secondOK` as a statement about numbers. -/
theorem tbl_secondOK_iff (x : Nat) (b : UInt8) : secondOK x b = true ↔
    (x = 0xE0 ∧ 0xA0 ≤ b.toNat ∧ b.toNat ≤ 0xBF) ∨
    (x = 0xED ∧ 0x80 ≤ b.toNat ∧ b.toNat ≤ 0x9F) ∨
    (x = 0xF0 ∧ 0x90 ≤ b.toNat ∧ b.toNat ≤ 0xBF) ∨
    (x = 0xF4 ∧ 0x80 ≤ b.toNat ∧ b.toNat ≤ 0x8F) ∨
    (x ≠ 0xE0 ∧ x ≠ 0xED ∧ x ≠ 0xF0 ∧ x ≠ 0xF4 ∧ 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF) := by
  unfold secondOK
  by_cases h1 : x = 0xE0 <;> by_cases h2 : x = 0xED <;> by_cases h3 : x = 0xF0 <;>
    by_cases h4 : x = 0xF4 <;> simp [h1, h2, h3, h4] <;> omega

/-- `isCont` as a statement about numbers. -/
theorem tbl_isCont_iff (b : UInt8) : isCont b = true ↔ 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF := by
  simp [isCont]

/-- An encoded character, as a well-formed sequence on its own. -/
theorem tbl_wellFormed_encodeChar (c : Char) : Spec.WellFormed (Utf8.encodeChar c) := by
  have h := Spec.WellFormed.cons (Utf8.Proofs.Table.encodeChar_wellFormed c) Spec.WellFormed.nil
  rwa [List.append_nil] at h

/-- A nonempty well-formed sequence starts with the bytes of one
    character, and the rest is well formed. -/
theorem wellFormed_cons {s : List UInt8} (h : Spec.WellFormed s) (hs : s ≠ []) :
    ∃ c t, s = Utf8.encodeChar c ++ t ∧ Spec.WellFormed t := by
  obtain ⟨cs, rfl⟩ := (Utf8.Proofs.Table.wellFormed_iff s).mp h
  match cs with
  | [] => exact absurd rfl hs
  | c :: cs =>
    exact ⟨c, Utf8.encode cs, Utf8.Proofs.Table.encode_cons c cs,
      (Utf8.Proofs.Table.wellFormed_iff _).mpr ⟨cs, rfl⟩⟩

/-- D93a in terms of the strict decoder: no well-formed sequence starts
    at the front exactly when no character can be read there. -/
theorem unconvertible_iff (b0 : UInt8) (rest : List UInt8) :
    Spec.Unconvertible (b0 :: rest) ↔ Utf8.decodeChar (b0 :: rest) = none := by
  constructor
  · intro hu
    match hd : Utf8.decodeChar (b0 :: rest) with
    | none => rfl
    | some (c, r) =>
      have he := (Utf8.Proofs.Decode.decodeChar_iff _ c r).mp hd
      exact absurd (tbl_wellFormed_encodeChar c)
        (hu _ (Utf8.Proofs.Decode.encodeChar_ne_nil c) ⟨r, he.symm⟩)
  · intro hd s hs hpre hw
    obtain ⟨c, t, rfl, -⟩ := wellFormed_cons hw hs
    obtain ⟨u, hu⟩ := hpre
    have : Utf8.decodeChar (b0 :: rest) = some (c, t ++ u) :=
      (Utf8.Proofs.Decode.decodeChar_iff _ c _).mpr (by rw [← hu, List.append_assoc])
    rw [hd] at this
    simp at this

/-- A prefix of one row of Table 3-7 passes `prefixB`. -/
theorem tbl_prefixB_of_wellFormedChar {s q : List UInt8} (hs : Spec.WellFormedChar s)
    (hq : q <+: s) : prefixB q = true := by
  match s, hs with
  | [b0], h =>
    simp only [Spec.WellFormedChar, Spec.InRange] at h
    simp only [List.prefix_cons_iff, List.prefix_nil] at hq
    rcases hq with rfl | ⟨t, rfl, rfl⟩
    · rfl
    · simp [prefixB]; omega
  | [b0, b1], h =>
    simp only [Spec.WellFormedChar, Spec.InRange] at h
    simp only [List.prefix_cons_iff, List.prefix_nil] at hq
    rcases hq with rfl | ⟨t, rfl, rfl | ⟨t, rfl, rfl⟩⟩
    · rfl
    · simp [prefixB]; omega
    · simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff]; omega
  | [b0, b1, b2], h =>
    simp only [Spec.WellFormedChar, Spec.InRange] at h
    simp only [List.prefix_cons_iff, List.prefix_nil] at hq
    rcases hq with rfl | ⟨t, rfl, rfl | ⟨t, rfl, rfl | ⟨t, rfl, rfl⟩⟩⟩
    · rfl
    · simp [prefixB]; omega
    · simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff]; omega
    · simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff]; omega
  | [b0, b1, b2, b3], h =>
    simp only [Spec.WellFormedChar, Spec.InRange] at h
    simp only [List.prefix_cons_iff, List.prefix_nil] at hq
    rcases hq with rfl | ⟨t, rfl, rfl | ⟨t, rfl, rfl | ⟨t, rfl, rfl | ⟨t, rfl, rfl⟩⟩⟩⟩
    · rfl
    · simp [prefixB]; omega
    · simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff]; omega
    · simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff]; omega
    · simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff]; omega

/-- A prefix of a row of Table 3-7 is a prefix of an encoded character. -/
theorem tbl_prefix_encodeChar {q s : List UInt8} (hs : Spec.WellFormedChar s) (hq : q <+: s) :
    ∃ c, q <+: Utf8.encodeChar c := by
  obtain ⟨c, rfl⟩ := (Utf8.Proofs.Table.wellFormedChar_iff s).mp hs
  exact ⟨c, hq⟩

/-- What passes `prefixB` begins an encoded character: extend it with
    continuation bytes to a full row of Table 3-7. -/
theorem tbl_encodeChar_of_prefixB (q : List UInt8) (h : prefixB q = true) :
    ∃ c, q <+: Utf8.encodeChar c := by
  match q with
  | [] => exact ⟨'a', List.nil_prefix⟩
  | [b0] =>
    simp [prefixB] at h
    by_cases a1 : b0.toNat ≤ 0x7F
    · exact tbl_prefix_encodeChar (s := [b0])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; omega) ⟨[], rfl⟩
    by_cases a2 : b0.toNat ≤ 0xDF
    · exact tbl_prefix_encodeChar (s := [b0, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0x80], rfl⟩
    by_cases a3 : b0.toNat = 0xE0
    · exact tbl_prefix_encodeChar (s := [b0, 0xA0, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0xA0, 0x80], rfl⟩
    by_cases a4 : b0.toNat ≤ 0xEF
    · exact tbl_prefix_encodeChar (s := [b0, 0x80, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0x80, 0x80], rfl⟩
    by_cases a5 : b0.toNat = 0xF0
    · exact tbl_prefix_encodeChar (s := [b0, 0x90, 0x80, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0x90, 0x80, 0x80], rfl⟩
    · exact tbl_prefix_encodeChar (s := [b0, 0x80, 0x80, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0x80, 0x80, 0x80], rfl⟩
  | [b0, b1] =>
    simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff] at h
    by_cases a2 : b0.toNat ≤ 0xDF
    · exact tbl_prefix_encodeChar (s := [b0, b1])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; omega) ⟨[], rfl⟩
    by_cases a4 : b0.toNat ≤ 0xEF
    · exact tbl_prefix_encodeChar (s := [b0, b1, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0x80], rfl⟩
    · exact tbl_prefix_encodeChar (s := [b0, b1, 0x80, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0x80, 0x80], rfl⟩
  | [b0, b1, b2] =>
    simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff] at h
    by_cases a4 : b0.toNat ≤ 0xEF
    · exact tbl_prefix_encodeChar (s := [b0, b1, b2])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; omega) ⟨[], rfl⟩
    · exact tbl_prefix_encodeChar (s := [b0, b1, b2, 0x80])
        (by simp only [Spec.WellFormedChar, Spec.InRange]; simp; omega) ⟨[0x80], rfl⟩
  | [b0, b1, b2, b3] =>
    simp [prefixB, tbl_isCont_iff, tbl_secondOK_iff] at h
    exact tbl_prefix_encodeChar (s := [b0, b1, b2, b3])
      (by simp only [Spec.WellFormedChar, Spec.InRange]; omega) ⟨[], rfl⟩
  | _ :: _ :: _ :: _ :: _ :: _ => simp [prefixB] at h

/-- `prefixB` says what it should. -/
theorem prefixB_iff (q : List UInt8) :
    prefixB q = true ↔ ∃ c, q <+: Utf8.encodeChar c := by
  constructor
  · exact tbl_encodeChar_of_prefixB q
  · rintro ⟨c, hc⟩
    exact tbl_prefixB_of_wellFormedChar (Utf8.Proofs.Table.encodeChar_wellFormed c) hc

/-- At an unconvertible offset, a prefix is the initial subsequence of a
    well-formed sequence exactly when `prefixB` holds of it. -/
theorem initial_iff {q bs : List UInt8} (hu : Spec.Unconvertible bs) (hq : q <+: bs) :
    Spec.Initial q ↔ prefixB q = true := by
  constructor
  · rintro ⟨s, hw, hqs⟩
    match q, hq, hqs with
    | [], _, _ => rfl
    | b :: q', hq, hqs =>
      have hs : s ≠ [] := by
        intro h; subst h; simp at hqs
      obtain ⟨c, t, rfl, -⟩ := wellFormed_cons hw hs
      rcases List.prefix_or_prefix_of_prefix hqs (List.prefix_append (Utf8.encodeChar c) t) with
        h | h
      · exact (prefixB_iff _).mpr ⟨c, h⟩
      · exact absurd (tbl_wellFormed_encodeChar c)
          (hu _ (Utf8.Proofs.Decode.encodeChar_ne_nil c) (h.trans hq))
  · intro h
    obtain ⟨c, hc⟩ := (prefixB_iff q).mp h
    exact ⟨_, tbl_wellFormed_encodeChar c, hc⟩

end Utf8.Proofs.Lossy
