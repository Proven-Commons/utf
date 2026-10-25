/-
  The lossy decoder against section 3.9.6 of the Unicode Standard, from
  the lemmas in `Table.lean` and `Step.lean`.
-/

import Utf8
import Spec.Defs
import Proofs.Encode
import Proofs.Decode
import Proofs.Table
import Proofs.Lossy.Defs
import Proofs.Lossy.Table
import Proofs.Lossy.Step

namespace Utf8.Proofs.Lossy

open Utf8

theorem mn_encodeChar_length_pos (c : Char) : 0 < (encodeChar c).length := by
  have h := Utf8.Proofs.Decode.encodeChar_ne_nil c
  cases hc : encodeChar c with
  | nil => exact absurd hc h
  | cons _ _ => simp

theorem mn_lossyStep_length (b : UInt8) (bs : List UInt8) :
    (lossyStep b bs).2.length ≤ bs.length := by
  unfold lossyStep
  split
  · rename_i c rest' h
    have h1 := (Utf8.Proofs.Decode.decodeChar_iff _ _ _).mp h
    have h2 := mn_encodeChar_length_pos c
    have h3 : (b :: bs).length = (encodeChar c).length + rest'.length := by
      rw [h1, List.length_append]
    simp only [List.length_cons] at h3
    simp only
    omega
  · have := badLength_pos b bs
    simp only [List.length_drop, List.length_cons]
    omega

theorem mn_aux_fuel (f1 : Nat) : ∀ (f2 : Nat) (bs : List UInt8), bs.length ≤ f1 →
    bs.length ≤ f2 → decodeLossyAux f1 bs = decodeLossyAux f2 bs := by
  induction f1 with
  | zero =>
    intro f2 bs h1 h2
    cases bs with
    | nil => cases f2 <;> rfl
    | cons b bs => simp at h1
  | succ n ih =>
    intro f2 bs h1 h2
    cases bs with
    | nil => cases f2 <;> rfl
    | cons b bs =>
      cases f2 with
      | zero => simp at h2
      | succ m =>
        have hl := mn_lossyStep_length b bs
        rcases hs : lossyStep b bs with ⟨c, rest⟩
        rw [hs] at hl
        simp only [List.length_cons] at h1 h2 hl
        simp only [decodeLossyAux, hs]
        rw [ih m _ (by omega) (by omega)]

theorem mn_decodeLossy_nil : decodeLossy [] = [] := rfl

theorem mn_decodeLossy_cons (b : UInt8) (bs : List UInt8) :
    decodeLossy (b :: bs) = (lossyStep b bs).1 :: decodeLossy (lossyStep b bs).2 := by
  have hl := mn_lossyStep_length b bs
  rcases hs : lossyStep b bs with ⟨c, rest⟩
  rw [hs] at hl
  simp only at hl ⊢
  unfold decodeLossy
  simp only [List.length_cons, decodeLossyAux, hs]
  rw [mn_aux_fuel _ _ _ hl (Nat.le_refl _)]

theorem mn_decodeLossy_some {b : UInt8} {bs : List UInt8} {c : Char} {rest : List UInt8}
    (h : decodeChar (b :: bs) = some (c, rest)) :
    decodeLossy (b :: bs) = c :: decodeLossy rest := by
  rw [mn_decodeLossy_cons]
  simp only [lossyStep, h]

theorem mn_decodeLossy_none {b : UInt8} {bs : List UInt8}
    (h : decodeChar (b :: bs) = none) :
    decodeLossy (b :: bs) = replacement :: decodeLossy ((b :: bs).drop (badLength b bs)) := by
  rw [mn_decodeLossy_cons]
  simp only [lossyStep, h]

theorem mn_decodeLossy_encodeChar_append (c : Char) (rest : List UInt8) :
    decodeLossy (encodeChar c ++ rest) = c :: decodeLossy rest := by
  have h := Utf8.Proofs.Decode.decodeChar_encodeChar c rest
  have hne := Utf8.Proofs.Decode.encodeChar_ne_nil c
  obtain ⟨b, t, hbt⟩ := List.ne_nil_iff_exists_cons.mp hne
  rw [hbt, List.cons_append] at h ⊢
  exact mn_decodeLossy_some h


theorem mn_maximalSubpart (b0 : UInt8) (rest : List UInt8) (h : decodeChar (b0 :: rest) = none) :
    Spec.MaximalSubpart ((b0 :: rest).take (badLength b0 rest))
      ((b0 :: rest).drop (badLength b0 rest)) := by
  have hpos := badLength_pos b0 rest
  have hle := badLength_le b0 rest
  have hu : Spec.Unconvertible (b0 :: rest) := (unconvertible_iff b0 rest).mpr h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h0
    have := congrArg List.length h0
    simp only [List.length_take, List.length_nil] at this
    omega
  · rw [List.take_append_drop]; exact hu
  · by_cases h1 : badLength b0 rest = 1
    · right
      simp only [List.length_take]
      simp only [List.length_cons] at hle ⊢
      omega
    · left
      exact (initial_iff hu (List.take_prefix _ _)).mpr
        (badLength_prefix b0 rest h (by omega))
  · intro q hq hq'
    rw [List.take_append_drop] at hq
    simp only [List.length_take]
    have hql := hq.length_le
    rw [Nat.min_eq_left hle]
    refine Nat.le_of_not_lt (fun hlt => ?_)
    rcases hq' with hi | h1
    · have hp := (initial_iff hu hq).mp hi
      have hp2 := prefixB_take q (badLength b0 rest + 1) hp
      have hqe := List.prefix_iff_eq_take.mp hq
      rw [hqe, List.take_take, Nat.min_eq_left (by omega)] at hp2
      have := badLength_max b0 rest h (by omega)
      rw [hp2] at this
      exact Bool.noConfusion this
    · omega

theorem mn_maximalSubpart_unique {p r p' r' : List UInt8} (h : Spec.MaximalSubpart p r)
    (h' : Spec.MaximalSubpart p' r') (he : p ++ r = p' ++ r') : p = p' ∧ r = r' := by
  have l1 : p'.length ≤ p.length := h.2.2.2 p' (he ▸ List.prefix_append p' r') h'.2.2.1
  have l2 : p.length ≤ p'.length := h'.2.2.2 p (he ▸ List.prefix_append p r) h.2.2.1
  exact List.append_inj he (by omega)


theorem mn_substitutes_decodeLossy (n : Nat) : ∀ bs : List UInt8, bs.length < n →
    Spec.Substitutes bs (decodeLossy bs) := by
  induction n with
  | zero => intro bs h; omega
  | succ n ih =>
    intro bs hn
    cases bs with
    | nil => exact Spec.Substitutes.nil
    | cons b r =>
      cases hd : decodeChar (b :: r) with
      | some cr =>
        obtain ⟨c, rest⟩ := cr
        rw [mn_decodeLossy_some hd]
        have he := (Utf8.Proofs.Decode.decodeChar_iff _ _ _).mp hd
        have hl : (b :: r).length = (encodeChar c).length + rest.length := by
          rw [he, List.length_append]
        have hp := mn_encodeChar_length_pos c
        have ih' := ih rest (by omega)
        rw [he, Utf8.Proofs.Encode.encodeChar_eq]
        exact Spec.Substitutes.char ih'
      | none =>
        rw [mn_decodeLossy_none hd]
        have hpos := badLength_pos b r
        have ih' := ih ((b :: r).drop (badLength b r)) (by simp only [List.length_drop, List.length_cons] at hn ⊢; omega)
        have hm := mn_maximalSubpart b r hd
        have := Spec.Substitutes.replace hm ih'
        rw [List.take_append_drop] at this
        exact this

theorem mn_decodeLossy_of_substitutes {bs : List UInt8} {out : List Char}
    (h : Spec.Substitutes bs out) : decodeLossy bs = out := by
  induction h with
  | nil => rfl
  | @char c rest out _ ih =>
    rw [← Utf8.Proofs.Encode.encodeChar_eq, mn_decodeLossy_encodeChar_append, ih]
  | @replace p rest out hm _ ih =>
    obtain ⟨b0, r', hbr⟩ := List.ne_nil_iff_exists_cons.mp hm.1
    have hu := hm.2.1
    rw [hbr, List.cons_append] at hu ⊢
    have hd := (unconvertible_iff b0 (r' ++ rest)).mp hu
    rw [mn_decodeLossy_none hd]
    have hm' := mn_maximalSubpart b0 (r' ++ rest) hd
    have heq : (b0 :: (r' ++ rest)).take (badLength b0 (r' ++ rest)) ++
        (b0 :: (r' ++ rest)).drop (badLength b0 (r' ++ rest)) = p ++ rest := by
      rw [List.take_append_drop, hbr, List.cons_append]
    rw [(mn_maximalSubpart_unique hm' hm heq).2, ih]
    rfl

theorem decodeLossy_iff (bs : List UInt8) (out : List Char) :
    Utf8.decodeLossy bs = out ↔ Spec.Substitutes bs out := by
  constructor
  · rintro rfl
    exact mn_substitutes_decodeLossy (bs.length + 1) bs (Nat.lt_succ_self _)
  · exact mn_decodeLossy_of_substitutes

theorem decodeLossy_encode_append (cs : List Char) (bs : List UInt8) :
    Utf8.decodeLossy (Utf8.encode cs ++ bs) = cs ++ Utf8.decodeLossy bs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [Utf8.Proofs.Decode.encode_cons, List.append_assoc, mn_decodeLossy_encodeChar_append, ih,
      List.cons_append]

theorem decodeLossy_of_decode (bs : List UInt8) (cs : List Char) :
    Utf8.decode bs = some cs → Utf8.decodeLossy bs = cs := by
  intro h
  rw [(Utf8.Proofs.Decode.decode_iff bs cs).mp h, ← List.append_nil (encode cs),
    decodeLossy_encode_append, mn_decodeLossy_nil, List.append_nil]

theorem mn_replaces (n : Nat) : ∀ bs : List UInt8, bs.length < n →
    Utf8.decode bs = none → '�' ∈ Utf8.decodeLossy bs := by
  induction n with
  | zero => intro bs h; omega
  | succ n ih =>
    intro bs hn hdec
    cases bs with
    | nil => simp [decode, decodeAux] at hdec
    | cons b r =>
      cases hd : decodeChar (b :: r) with
      | some cr =>
        obtain ⟨c, rest⟩ := cr
        rw [mn_decodeLossy_some hd]
        have he := (Utf8.Proofs.Decode.decodeChar_iff _ _ _).mp hd
        have hl : (b :: r).length = (encodeChar c).length + rest.length := by
          rw [he, List.length_append]
        have hp := mn_encodeChar_length_pos c
        have hr : decode rest = none := by
          cases hdr : decode rest with
          | none => rfl
          | some cs =>
            have := (Utf8.Proofs.Decode.decode_iff rest cs).mp hdr
            have h2 : decode (b :: r) = some (c :: cs) := by
              rw [Utf8.Proofs.Decode.decode_iff, Utf8.Proofs.Decode.encode_cons, he, this]
            rw [h2] at hdec
            exact absurd hdec (by simp)
        exact List.mem_cons_of_mem _ (ih rest (by omega) hr)
      | none =>
        rw [mn_decodeLossy_none hd]
        exact List.mem_cons_self

theorem decodeLossy_replaces (bs : List UInt8) :
    Utf8.decode bs = none → '�' ∈ Utf8.decodeLossy bs :=
  mn_replaces (bs.length + 1) bs (Nat.lt_succ_self _)

theorem mn_append_encode (cs : List Char) (n : Nat) : ∀ bs : List UInt8, bs.length < n →
    Utf8.decodeLossy (bs ++ Utf8.encode cs) = Utf8.decodeLossy bs ++ cs := by
  induction n with
  | zero => intro bs h; omega
  | succ n ih =>
    intro bs hn
    cases bs with
    | nil =>
      rw [List.nil_append, ← List.append_nil (encode cs), decodeLossy_encode_append,
        mn_decodeLossy_nil, List.append_nil, List.nil_append]
    | cons b r =>
      cases hd : decodeChar (b :: r) with
      | some cr =>
        obtain ⟨c, rest⟩ := cr
        have he := (Utf8.Proofs.Decode.decodeChar_iff _ _ _).mp hd
        have hl : (b :: r).length = (encodeChar c).length + rest.length := by
          rw [he, List.length_append]
        have hp := mn_encodeChar_length_pos c
        rw [he, List.append_assoc, mn_decodeLossy_encodeChar_append,
          mn_decodeLossy_encodeChar_append, ih rest (by omega), List.cons_append]
      | none =>
        have hE := encode_noContHead cs
        have hd' := decodeChar_append_none b r (encode cs) hE hd
        have hle := badLength_le b r
        have hpos := badLength_pos b r
        rw [List.cons_append, mn_decodeLossy_none hd', mn_decodeLossy_none hd,
          badLength_append b r (encode cs) hE, ← List.cons_append,
          List.drop_append_of_le_length hle,
          ih _ (by simp only [List.length_drop, List.length_cons] at hn ⊢; omega), List.cons_append]

theorem decodeLossy_append_encode (bs : List UInt8) (cs : List Char) :
    Utf8.decodeLossy (bs ++ Utf8.encode cs) = Utf8.decodeLossy bs ++ cs :=
  mn_append_encode cs (bs.length + 1) bs (Nat.lt_succ_self _)

end Utf8.Proofs.Lossy
