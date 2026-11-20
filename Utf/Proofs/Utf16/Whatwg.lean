/-
  The lossy byte decoders against the WHATWG Encoding Standard's shared
  UTF-16 decoder.
-/

import Utf16
import Utf.Spec.Utf16

namespace Utf16.Proofs

/-- The unit of two bytes in stream order, in the byte order `be`. -/
def wh_u (be : Bool) (a b : UInt8) : UInt16 := if be then unit a b else unit b a

/-- What `decodeLossyBytes` does with the result of `units`. -/
def wh_fin : List UInt16 × Option UInt8 → List Char
  | (us, none) => decodeLossy us
  | (us, some _) =>
    if us.getLast?.any isHigh then decodeLossy us else decodeLossy us ++ [replacement]

theorem wh_dlb_eq (be : Bool) (bs : List UInt8) :
    decodeLossyBytes be bs = wh_fin (units be bs) := by
  unfold decodeLossyBytes
  rcases units be bs with ⟨us, _ | x⟩ <;> rfl

theorem wh_units_cons2 (be : Bool) (a b : UInt8) (rest : List UInt8) :
    units be (a :: b :: rest) = (wh_u be a b :: (units be rest).1, (units be rest).2) := by
  simp only [units, wh_u]

theorem wh_fin_notHigh (u : UInt16) (us : List UInt16) (l : Option UInt8)
    (hu : isHigh u = false) :
    wh_fin (u :: us, l) = (if isLow u then replacement else Char.ofNat u.toNat) :: wh_fin (us, l) := by
  have hd : decodeLossy (u :: us) =
      (if isLow u then replacement else Char.ofNat u.toNat) :: decodeLossy us := by
    rw [decodeLossy.eq_def]; cases hl : isLow u <;> simp [hu, hl]
  cases l with
  | none => simp only [wh_fin, hd]
  | some x =>
    cases us with
    | nil => simp [wh_fin, hd, hu]
    | cons v vs =>
      simp only [wh_fin, List.getLast?_cons_cons, hd]
      split <;> simp

theorem wh_fin_high_one (u : UInt16) (l : Option UInt8) (hu : isHigh u = true) :
    wh_fin ([u], l) = [replacement] := by
  cases l <;> simp [wh_fin, decodeLossy, hu]

theorem wh_fin_high_low (u v : UInt16) (us : List UInt16) (l : Option UInt8)
    (hu : isHigh u = true) (hv : isLow v = true) (hv' : isHigh v = false) :
    wh_fin (u :: v :: us, l) = pair u v :: wh_fin (us, l) := by
  cases l with
  | none => simp [wh_fin, decodeLossy, hu, hv]
  | some x =>
    cases us with
    | nil => simp [wh_fin, decodeLossy, hu, hv, hv']
    | cons w ws =>
      simp only [wh_fin, List.getLast?_cons_cons]
      rw [decodeLossy.eq_def]
      simp only [hu, hv]
      split <;> simp_all

theorem wh_fin_high_notLow (u v : UInt16) (us : List UInt16) (l : Option UInt8)
    (hu : isHigh u = true) (hv : isLow v = false) :
    wh_fin (u :: v :: us, l) = replacement :: wh_fin (v :: us, l) := by
  cases l with
  | none => simp [wh_fin, decodeLossy, hu, hv]
  | some x =>
    simp only [wh_fin, List.getLast?_cons_cons]
    rw [decodeLossy.eq_def]
    simp only [hu, hv]
    split <;> simp_all

theorem wh_dlb_nil (be : Bool) : decodeLossyBytes be [] = [] := rfl

theorem wh_dlb_one (be : Bool) (x : UInt8) : decodeLossyBytes be [x] = [replacement] := rfl

theorem wh_dlb_notHigh (be : Bool) (a b : UInt8) (rest : List UInt8)
    (hu : isHigh (wh_u be a b) = false) :
    decodeLossyBytes be (a :: b :: rest) =
      (if isLow (wh_u be a b) then replacement else Char.ofNat (wh_u be a b).toNat) ::
        decodeLossyBytes be rest := by
  rw [wh_dlb_eq, wh_units_cons2, wh_fin_notHigh _ _ _ hu, wh_dlb_eq]

theorem wh_dlb_high_two (be : Bool) (a b : UInt8) (hu : isHigh (wh_u be a b) = true) :
    decodeLossyBytes be [a, b] = [replacement] := by
  rw [wh_dlb_eq, wh_units_cons2]
  exact wh_fin_high_one _ _ hu

theorem wh_dlb_high_three (be : Bool) (a b c : UInt8) (hu : isHigh (wh_u be a b) = true) :
    decodeLossyBytes be [a, b, c] = [replacement] := by
  rw [wh_dlb_eq, wh_units_cons2]
  exact wh_fin_high_one _ _ hu

theorem wh_dlb_high_low (be : Bool) (a b c d : UInt8) (rest : List UInt8)
    (hu : isHigh (wh_u be a b) = true) (hv : isLow (wh_u be c d) = true) :
    decodeLossyBytes be (a :: b :: c :: d :: rest) =
      pair (wh_u be a b) (wh_u be c d) :: decodeLossyBytes be rest := by
  have hv' : isHigh (wh_u be c d) = false := by
    simp only [isLow, Bool.and_eq_true, decide_eq_true_eq] at hv
    simp only [isHigh, Bool.and_eq_false_iff, decide_eq_false_iff_not]
    omega
  rw [wh_dlb_eq, wh_units_cons2, wh_units_cons2]
  rw [wh_fin_high_low _ _ _ _ hu hv hv', wh_dlb_eq]

theorem wh_dlb_high_notLow (be : Bool) (a b c d : UInt8) (rest : List UInt8)
    (hu : isHigh (wh_u be a b) = true) (hv : isLow (wh_u be c d) = false) :
    decodeLossyBytes be (a :: b :: c :: d :: rest) =
      replacement :: decodeLossyBytes be (c :: d :: rest) := by
  rw [wh_dlb_eq, wh_units_cons2, wh_units_cons2]
  rw [wh_fin_high_notLow _ _ _ _ hu hv, wh_dlb_eq, wh_units_cons2]

theorem wh_u_toNat (be : Bool) (a b : UInt8) :
    (if be then (a.toNat <<< 8) + b.toNat else (b.toNat <<< 8) + a.toNat) = (wh_u be a b).toNat := by
  have ha := UInt8.toNat_lt a
  have hb := UInt8.toNat_lt b
  cases be <;> simp [wh_u, unit, Nat.shiftLeft_eq] <;> omega

theorem wh_bytes (be : Bool) (a b : UInt8) :
    (if be then [((wh_u be a b).toNat >>> 8).toUInt8, ((wh_u be a b).toNat &&& 0x00FF).toUInt8]
      else [((wh_u be a b).toNat &&& 0x00FF).toUInt8, ((wh_u be a b).toNat >>> 8).toUInt8]) = [a, b] := by
  have ha := UInt8.toNat_lt a
  have hb := UInt8.toNat_lt b
  have hff : (0x00FF : Nat) = 2 ^ 8 - 1 := rfl
  rw [hff, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  cases be
  · simp only [wh_u, unit, Bool.false_eq_true, ite_false, List.cons.injEq, and_true]
    constructor <;> apply UInt8.toNat_inj.mp <;> simp <;> omega
  · simp only [wh_u, unit, ite_true, List.cons.injEq, and_true]
    constructor <;> apply UInt8.toNat_inj.mp <;> simp <;> omega

theorem wh_run_nil (be : Bool) (fuel : Nat) : Utf.Spec.whatwgRun be fuel none none [] = [] := by
  cases fuel <;> simp [Utf.Spec.whatwgRun]

theorem wh_high_iff (u : UInt16) : isHigh u = true ↔ 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF := by
  simp [isHigh]

theorem wh_low_iff (u : UInt16) : isLow u = true ↔ 0xDC00 ≤ u.toNat ∧ u.toNat ≤ 0xDFFF := by
  simp [isLow]

theorem wh_repl : replacement = '�' := rfl

theorem wh_pair (h l : UInt16) :
    Char.ofNat (0x10000 + ((h.toNat - 0xD800) <<< 10) + (l.toNat - 0xDC00)) = pair h l := by
  simp only [pair, Nat.shiftLeft_eq]

theorem wh_run (be : Bool) : ∀ fuel : Nat,
    (∀ q, 2 * q.length + 1 ≤ fuel →
      Utf.Spec.whatwgRun be fuel none none q = decodeLossyBytes be q) ∧
    (∀ a q, 2 * q.length + 2 ≤ fuel →
      Utf.Spec.whatwgRun be fuel (some a) none q = decodeLossyBytes be (a :: q)) ∧
    (∀ x y q, isHigh (wh_u be x y) = true → 2 * q.length + 3 ≤ fuel →
      Utf.Spec.whatwgRun be fuel none (some (wh_u be x y).toNat) q =
        decodeLossyBytes be (x :: y :: q)) ∧
    (∀ x y a q, isHigh (wh_u be x y) = true → 2 * q.length + 4 ≤ fuel →
      Utf.Spec.whatwgRun be fuel (some a) (some (wh_u be x y).toNat) q =
        decodeLossyBytes be (x :: y :: a :: q)) := by
  intro fuel
  induction fuel with
  | zero => refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> omega
  | succ f ih =>
    obtain ⟨ih1, ih2, ih3, ih4⟩ := ih
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      cases q with
      | nil => exact wh_run_nil be _
      | cons b q =>
        simp only [Utf.Spec.whatwgRun]
        exact ih2 b q (by simp at hq; omega)
    · intro a q hq
      cases q with
      | nil => simp [Utf.Spec.whatwgRun, wh_run_nil, wh_dlb_one, wh_repl]
      | cons b q =>
        simp only [List.length_cons] at hq
        simp only [Utf.Spec.whatwgRun, wh_u_toNat]
        cases hh : isHigh (wh_u be a b)
        · have hh' : ¬ (0xD800 ≤ (wh_u be a b).toNat ∧ (wh_u be a b).toNat ≤ 0xDBFF) := by
            rw [← wh_high_iff, hh]; simp
          rw [ite_eq_right hh', wh_dlb_notHigh be a b q hh, ih1 q (by omega)]
          cases hl : isLow (wh_u be a b)
          · have hl' : ¬ (0xDC00 ≤ (wh_u be a b).toNat ∧ (wh_u be a b).toNat ≤ 0xDFFF) := by
              rw [← wh_low_iff, hl]; simp
            rw [ite_eq_right hl']
            rfl
          · rw [ite_eq_left ((wh_low_iff _).mp hl)]
            rfl
        · rw [ite_eq_left ((wh_high_iff _).mp hh)]
          exact ih3 a b q hh (by omega)
    · intro x y q hh hq
      cases q with
      | nil => simp [Utf.Spec.whatwgRun, wh_run_nil, wh_dlb_high_two be x y hh, wh_repl]
      | cons b q =>
        simp only [List.length_cons] at hq
        simp only [Utf.Spec.whatwgRun]
        exact ih4 x y b q hh (by omega)
    · intro x y a q hh hq
      cases q with
      | nil => simp [Utf.Spec.whatwgRun, wh_run_nil, wh_dlb_high_three be x y a hh, wh_repl]
      | cons b q =>
        simp only [List.length_cons] at hq
        simp only [Utf.Spec.whatwgRun, wh_u_toNat, wh_bytes]
        cases hl : isLow (wh_u be a b)
        · have hl' : ¬ (0xDC00 ≤ (wh_u be a b).toNat ∧ (wh_u be a b).toNat ≤ 0xDFFF) := by
            rw [← wh_low_iff, hl]; simp
          rw [ite_eq_right hl', wh_dlb_high_notLow be x y a b q hh hl,
            ← ih1 (a :: b :: q) (by simp; omega)]
          rfl
        · rw [ite_eq_left ((wh_low_iff _).mp hl), wh_dlb_high_low be x y a b q hh hl,
            ih1 q (by omega), wh_pair]

theorem whatwg (bs : List UInt8) :
    Utf16.decodeLossyBE bs = Utf.Spec.whatwgDecode true bs ∧
    Utf16.decodeLossyLE bs = Utf.Spec.whatwgDecode false bs := by
  constructor
  · exact ((wh_run true _).1 bs (by omega)).symm
  · exact ((wh_run false _).1 bs (by omega)).symm

end Utf16.Proofs
