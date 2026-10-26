/-
  UTF-16 lossy decoding against section 3.9.6 of the Unicode Standard,
  and `toWellFormed` against ECMAScript.
-/

import Proofs.Utf16.Units

namespace Utf16.Proofs

/-! ## Units and characters -/


theorem lo_isHigh_iff (u : UInt16) : isHigh u = true ↔ Spec.High u := by
  simp [isHigh, Spec.High]

theorem lo_isLow_iff (u : UInt16) : isLow u = true ↔ Spec.Low u := by
  simp [isLow, Spec.Low]

theorem lo_high_not_low {u : UInt16} (h : Spec.High u) : ¬ Spec.Low u := by
  unfold Spec.High at h; unfold Spec.Low; omega

theorem lo_isHigh_not_isLow {u : UInt16} (h : isHigh u = true) : isLow u = false := by
  have h1 := lo_high_not_low ((lo_isHigh_iff u).1 h)
  rw [← lo_isLow_iff] at h1
  simpa using h1

theorem lo_dl_nil : decodeLossy [] = [] := by
  rw [decodeLossy.eq_def]

theorem lo_dl_pair {u v : UInt16} (rest : List UInt16) (hu : isHigh u = true)
    (hv : isLow v = true) :
    decodeLossy (u :: v :: rest) = pair u v :: decodeLossy rest := by
  rw [decodeLossy.eq_def]; simp [hu, hv]

theorem lo_dl_high_bad {u v : UInt16} (rest : List UInt16) (hu : isHigh u = true)
    (hv : ¬ isLow v = true) :
    decodeLossy (u :: v :: rest) = replacement :: decodeLossy (v :: rest) := by
  rw [decodeLossy.eq_def]; simp [hu, hv]

theorem lo_dl_high_end {u : UInt16} (hu : isHigh u = true) :
    decodeLossy [u] = [replacement] := by
  rw [decodeLossy.eq_def]; simp [hu]

theorem lo_dl_low {u : UInt16} (rest : List UInt16) (hu : ¬ isHigh u = true)
    (hl : isLow u = true) :
    decodeLossy (u :: rest) = replacement :: decodeLossy rest := by
  rw [decodeLossy.eq_def]; simp [hu, hl]

theorem lo_dl_plain {u : UInt16} (rest : List UInt16) (hu : ¬ isHigh u = true)
    (hl : ¬ isLow u = true) :
    decodeLossy (u :: rest) = Char.ofNat u.toNat :: decodeLossy rest := by
  rw [decodeLossy.eq_def]; simp [hu, hl]

theorem lo_decode_one {u : UInt16} {c : Char} (hd : decode [u] = some [c]) :
    isHigh u = false ∧ isLow u = false ∧ Char.ofNat u.toNat = c := by
  rw [decode.eq_def] at hd
  by_cases h1 : isHigh u = true <;> by_cases h2 : isLow u = true <;> simp_all [decode]

theorem lo_decode_two {h l : UInt16} {c : Char} (hd : decode [h, l] = some [c]) :
    isHigh h = true ∧ isLow l = true ∧ pair h l = c := by
  rw [decode.eq_def] at hd
  by_cases h1 : isHigh h = true <;> by_cases h2 : isLow l = true <;>
    by_cases h3 : isLow h = true <;> by_cases h4 : isHigh l = true <;> simp_all [decode]

theorem lo_encode_cons (c : Char) (cs : List Char) :
    encode (c :: cs) = encodeChar c ++ encode cs := by
  simp [encode]

theorem lo_encode_single (c : Char) : encode [c] = encodeChar c := by
  simp [encode]

theorem lo_encodeChar_cases (c : Char) :
    (∃ u, encodeChar c = [u] ∧ isHigh u = false ∧ isLow u = false ∧
      Char.ofNat u.toNat = c) ∨
    (∃ h l, encodeChar c = [h, l] ∧ isHigh h = true ∧ isLow l = true ∧ pair h l = c) := by
  have hd := decode_encode [c]
  rw [lo_encode_single] at hd
  revert hd
  unfold encodeChar
  dsimp only
  split
  · intro hd
    exact Or.inl ⟨_, rfl, lo_decode_one hd⟩
  · intro hd
    exact Or.inr ⟨_, _, rfl, lo_decode_two hd⟩

theorem lo_encodeChar16 (c : Char) : Spec.encodeChar16 c = encodeChar c := by
  have h := encode_eq [c]
  simpa [encode, Spec.encode16] using h.symm

theorem lo_encodeChar_pair {u v : UInt16} (hu : isHigh u = true) (hv : isLow v = true) :
    encodeChar (pair u v) = [u, v] := by
  have hd : decode [u, v] = some [pair u v] := by
    rw [decode.eq_def]; simp [hu, hv, decode]
  rw [decode_iff, lo_encode_single] at hd
  exact hd.symm

theorem lo_encodeChar_plain {u : UInt16} (hu : ¬ isHigh u = true) (hl : ¬ isLow u = true) :
    encodeChar (Char.ofNat u.toNat) = [u] := by
  have hd : decode [u] = some [Char.ofNat u.toNat] := by
    rw [decode.eq_def]; simp [hu, hl, decode]
  rw [decode_iff, lo_encode_single] at hd
  exact hd.symm

theorem lo_encodeChar_replacement : encodeChar replacement = [0xFFFD] := by
  decide

theorem lo_dl_encodeChar_append (c : Char) (rest : List UInt16) :
    decodeLossy (encodeChar c ++ rest) = c :: decodeLossy rest := by
  rcases lo_encodeChar_cases c with ⟨u, he, h1, h2, h3⟩ | ⟨h, l, he, h1, h2, h3⟩
  · rw [he, List.singleton_append, lo_dl_plain _ (by simp [h1]) (by simp [h2]), h3]
  · rw [he, List.cons_append, List.singleton_append, lo_dl_pair _ h1 h2, h3]

theorem lo_encode_head {cs : List Char} {e : UInt16} {X : List UInt16}
    (h : encode cs = e :: X) : isLow e = false := by
  cases cs with
  | nil => simp [encode] at h
  | cons c cs =>
    rw [lo_encode_cons] at h
    rcases lo_encodeChar_cases c with ⟨u, he, h1, h2, _⟩ | ⟨a, b, he, h1, h2, _⟩
    · rw [he, List.singleton_append] at h
      simp only [List.cons.injEq] at h
      rw [← h.1]; exact h2
    · rw [he, List.cons_append] at h
      simp only [List.cons.injEq] at h
      rw [← h.1]; exact lo_isHigh_not_isLow h1

/-! ## Unconvertible offsets and initial subsequences -/

theorem lo_wf_head {s : List UInt16} (hs : Spec.WellFormed16 s) :
    ∀ w t, s = w :: t →
      ¬ Spec.Low w ∧ (Spec.High w → ∃ v t', t = v :: t' ∧ Spec.Low v) := by
  cases hs with
  | nil => intro w t h; simp at h
  | cons hc hr =>
    rename_i s1 rest
    intro w t h
    rcases s1 with _ | ⟨x, _ | ⟨y, _ | ⟨z, s2⟩⟩⟩
    · simp [Spec.WellFormedChar16] at hc
    · simp only [Spec.WellFormedChar16] at hc
      simp only [List.singleton_append, List.cons.injEq] at h
      obtain ⟨rfl, -⟩ := h
      unfold Spec.Low Spec.High
      omega
    · simp only [Spec.WellFormedChar16] at hc
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨lo_high_not_low hc.1, fun _ => ⟨y, rest, rfl, hc.2⟩⟩
    · simp [Spec.WellFormedChar16] at hc

theorem lo_wf_single {w : UInt16} (h1 : ¬ Spec.High w) (h2 : ¬ Spec.Low w) :
    Spec.WellFormed16 [w] := by
  have hc : Spec.WellFormedChar16 [w] := by
    simp only [Spec.WellFormedChar16]
    unfold Spec.High at h1; unfold Spec.Low at h2
    omega
  have := Spec.WellFormed16.cons hc Spec.WellFormed16.nil
  simpa using this

theorem lo_wf_pair {w v : UInt16} (h1 : Spec.High w) (h2 : Spec.Low v) :
    Spec.WellFormed16 [w, v] := by
  have hc : Spec.WellFormedChar16 [w, v] := by
    simp only [Spec.WellFormedChar16]
    exact ⟨h1, h2⟩
  have := Spec.WellFormed16.cons hc Spec.WellFormed16.nil
  simpa using this

theorem lo_unconv_cons (w : UInt16) (r : List UInt16) :
    Spec.Unconvertible16 (w :: r) ↔
      Spec.Low w ∨ (Spec.High w ∧ ¬ ∃ v r', r = v :: r' ∧ Spec.Low v) := by
  constructor
  · intro hU
    by_cases hl : Spec.Low w
    · exact Or.inl hl
    by_cases hh : Spec.High w
    · refine Or.inr ⟨hh, ?_⟩
      rintro ⟨v, r', rfl, hv⟩
      exact hU [w, v] (by simp) ⟨r', rfl⟩ (lo_wf_pair hh hv)
    · exact absurd (lo_wf_single hh hl) (hU [w] (by simp) ⟨r, rfl⟩)
  · intro h s hne hpre hwf
    obtain ⟨t, ht⟩ := hpre
    cases s with
    | nil => exact hne rfl
    | cons x s' =>
      simp only [List.cons_append, List.cons.injEq] at ht
      obtain ⟨rfl, ht⟩ := ht
      have hh := lo_wf_head hwf x s' rfl
      rcases h with hl | ⟨hh', hn⟩
      · exact hh.1 hl
      · obtain ⟨v, t', rfl, hv⟩ := hh.2 hh'
        exact hn ⟨v, t' ++ t, by rw [← ht]; simp, hv⟩

theorem lo_initial_two {w v : UInt16} {q : List UInt16} (h : Spec.Initial16 (w :: v :: q)) :
    ¬ Spec.Low w ∧ (Spec.High w → Spec.Low v) := by
  obtain ⟨s, hs, t, rfl⟩ := h
  have := lo_wf_head hs w (v :: q ++ t) (by simp)
  refine ⟨this.1, fun hh => ?_⟩
  obtain ⟨v', t', he, hv⟩ := this.2 hh
  simp only [List.cons_append, List.cons.injEq] at he
  rw [he.1]; exact hv

theorem lo_maximalSubpart_iff (p rest : List UInt16) :
    Spec.MaximalSubpart16 p rest ↔ ∃ w, p = [w] ∧ Spec.Unpaired [] w rest := by
  constructor
  · rintro ⟨hne, hU, hI, -⟩
    cases p with
    | nil => exact absurd rfl hne
    | cons w p' =>
      cases p' with
      | nil =>
        refine ⟨w, rfl, ?_⟩
        rcases (lo_unconv_cons w rest).1 hU with hl | hh
        · right
          refine ⟨hl, ?_⟩
          rintro ⟨l', v, he, -⟩
          simp at he
        · left; exact hh
      | cons v p'' =>
        exfalso
        have hI' : Spec.Initial16 (w :: v :: p'') := by
          rcases hI with hI | hI
          · exact hI
          · simp at hI
        have h2 := lo_initial_two hI'
        rcases (lo_unconv_cons w (v :: (p'' ++ rest))).1 hU with hl | ⟨hh, hn⟩
        · exact h2.1 hl
        · exact hn ⟨v, p'' ++ rest, rfl, h2.2 hh⟩
  · rintro ⟨w, rfl, hu⟩
    refine ⟨by simp, ?_, Or.inr rfl, ?_⟩
    · rw [List.singleton_append, lo_unconv_cons]
      rcases hu with hh | ⟨hl, -⟩
      · exact Or.inr hh
      · exact Or.inl hl
    · intro q hq hI
      match q, hq, hI with
      | [], _, _ => simp
      | [_], _, _ => simp
      | x :: y :: q'', hq, hI =>
        exfalso
        have hI' : Spec.Initial16 (x :: y :: q'') := by
          rcases hI with hI | hI
          · exact hI
          · simp at hI
        have h2 := lo_initial_two hI'
        obtain ⟨t, ht⟩ := hq
        simp only [List.cons_append, List.cons.injEq] at ht
        obtain ⟨rfl, ht⟩ := ht
        rcases hu with ⟨hh, hn⟩ | ⟨hl, -⟩
        · exact hn ⟨y, q'' ++ t, ht.symm, h2.2 hh⟩
        · exact h2.1 hl


/-! ## Lossy decoding -/

theorem lo_dl_unpaired {w : UInt16} {rest : List UInt16} (hu : Spec.Unpaired [] w rest) :
    decodeLossy (w :: rest) = replacement :: decodeLossy rest := by
  rcases hu with ⟨hh, hn⟩ | ⟨hl, -⟩
  · rw [← lo_isHigh_iff] at hh
    cases rest with
    | nil => rw [lo_dl_high_end hh, lo_dl_nil]
    | cons v r' =>
      have hv : ¬ isLow v = true := by
        rw [lo_isLow_iff]; exact fun hv => hn ⟨v, r', rfl, hv⟩
      rw [lo_dl_high_bad _ hh hv]
  · have hh : ¬ isHigh w = true := by
      rw [lo_isHigh_iff]; exact fun hh => lo_high_not_low hh hl
    rw [← lo_isLow_iff] at hl
    rw [lo_dl_low _ hh hl]

theorem lo_subst_dl (us : List UInt16) : Spec.Substitutes16 us (decodeLossy us) := by
  induction us using decodeLossy.induct with
  | case1 => rw [lo_dl_nil]; exact Spec.Substitutes16.nil
  | case2 u hu v rest' hv ih =>
    rw [lo_dl_pair _ hu hv]
    have := Spec.Substitutes16.char (c := pair u v) ih
    rw [lo_encodeChar16, lo_encodeChar_pair hu hv] at this
    exact this
  | case3 u hu v rest' hv ih =>
    rw [lo_dl_high_bad _ hu hv]
    have hm : Spec.MaximalSubpart16 [u] (v :: rest') := by
      rw [lo_maximalSubpart_iff]
      refine ⟨u, rfl, Or.inl ⟨(lo_isHigh_iff u).1 hu, ?_⟩⟩
      rintro ⟨v', r', he, hv'⟩
      simp only [List.cons.injEq] at he
      rw [← he.1, ← lo_isLow_iff] at hv'
      exact hv hv'
    exact Spec.Substitutes16.replace hm ih
  | case4 u hu =>
    rw [lo_dl_high_end hu]
    have hm : Spec.MaximalSubpart16 [u] [] := by
      rw [lo_maximalSubpart_iff]
      refine ⟨u, rfl, Or.inl ⟨(lo_isHigh_iff u).1 hu, ?_⟩⟩
      rintro ⟨v', r', he, -⟩
      simp at he
    exact Spec.Substitutes16.replace hm Spec.Substitutes16.nil
  | case5 u rest hu hl ih =>
    rw [lo_dl_low _ hu hl]
    have hm : Spec.MaximalSubpart16 [u] rest := by
      rw [lo_maximalSubpart_iff]
      refine ⟨u, rfl, Or.inr ⟨(lo_isLow_iff u).1 hl, ?_⟩⟩
      rintro ⟨l', v, he, -⟩
      simp at he
    exact Spec.Substitutes16.replace hm ih
  | case6 u rest hu hl ih =>
    rw [lo_dl_plain _ hu hl]
    have := Spec.Substitutes16.char (c := Char.ofNat u.toNat) ih
    rw [lo_encodeChar16, lo_encodeChar_plain hu hl] at this
    exact this

theorem lo_dl_of_subst {us : List UInt16} {out : List Char} (h : Spec.Substitutes16 us out) :
    decodeLossy us = out := by
  induction h with
  | nil => exact lo_dl_nil
  | char _ ih => rw [lo_encodeChar16, lo_dl_encodeChar_append, ih]
  | replace hm _ ih =>
    obtain ⟨w, rfl, hu⟩ := (lo_maximalSubpart_iff _ _).1 hm
    rw [List.singleton_append, lo_dl_unpaired hu, ih]
    rfl

theorem lo_dl_encode_append (cs : List Char) (us : List UInt16) :
    decodeLossy (encode cs ++ us) = cs ++ decodeLossy us := by
  induction cs with
  | nil => simp [encode]
  | cons c cs ih =>
    rw [lo_encode_cons, List.append_assoc, lo_dl_encodeChar_append, ih]
    rfl

theorem lo_dl_encode (cs : List Char) : decodeLossy (encode cs) = cs := by
  have := lo_dl_encode_append cs []
  rw [List.append_nil, lo_dl_nil, List.append_nil] at this
  exact this

theorem decodeLossy_iff (us : List UInt16) (out : List Char) :
    Utf16.decodeLossy us = out ↔ Spec.Substitutes16 us out := by
  constructor
  · rintro rfl; exact lo_subst_dl us
  · exact lo_dl_of_subst

/-- In UTF-16 a maximal subpart is always one isolated surrogate. A
    fact about the definitions alone, so not one of the statements of
    `Spec.lean`; `decodeLossy_iff` rests on it. -/
theorem maximalSubpart_iff (p rest : List UInt16) :
    Spec.MaximalSubpart16 p rest ↔ ∃ w, p = [w] ∧ Spec.Unpaired [] w rest :=
  lo_maximalSubpart_iff p rest

theorem decodeLossy_unpaired (w : UInt16) (rest : List UInt16) :
    Spec.Unpaired [] w rest → Utf16.decodeLossy (w :: rest) = '�' :: Utf16.decodeLossy rest :=
  fun hu => lo_dl_unpaired hu

theorem decodeLossy_of_decode (us : List UInt16) (cs : List Char) :
    Utf16.decode us = some cs → Utf16.decodeLossy us = cs := by
  intro h
  rw [(decode_iff _ _).1 h]
  exact lo_dl_encode cs

theorem decodeLossy_replaces (us : List UInt16) :
    Utf16.decode us = none → '�' ∈ Utf16.decodeLossy us := by
  induction us using decode.induct with
  | case1 => intro h; simp [decode] at h
  | case2 u hu v rest' hv ih =>
    intro h
    rw [decode.eq_def] at h
    simp [hu, hv] at h
    rw [lo_dl_pair _ hu hv]
    exact List.mem_cons_of_mem _ (ih h)
  | case3 u hu v rest' hv =>
    intro _
    rw [lo_dl_high_bad _ hu hv]
    exact List.mem_cons_self
  | case4 u hu =>
    intro _
    rw [lo_dl_high_end hu]
    exact List.mem_cons_self
  | case5 u rest hu hl =>
    intro _
    rw [lo_dl_low _ hu hl]
    exact List.mem_cons_self
  | case6 u rest hu hl ih =>
    intro h
    rw [decode.eq_def] at h
    simp [hu, hl] at h
    rw [lo_dl_plain _ hu hl]
    exact List.mem_cons_of_mem _ (ih h)

theorem decodeLossy_encode_append (cs : List Char) (us : List UInt16) :
    Utf16.decodeLossy (Utf16.encode cs ++ us) = cs ++ Utf16.decodeLossy us :=
  lo_dl_encode_append cs us

theorem decodeLossy_append_encode (us : List UInt16) (cs : List Char) :
    Utf16.decodeLossy (us ++ Utf16.encode cs) = Utf16.decodeLossy us ++ cs := by
  induction us using decodeLossy.induct with
  | case1 => rw [List.nil_append, lo_dl_encode, lo_dl_nil, List.nil_append]
  | case2 u hu v rest' hv ih =>
    rw [List.cons_append, List.cons_append, lo_dl_pair _ hu hv, lo_dl_pair _ hu hv, ih]
    rfl
  | case3 u hu v rest' hv ih =>
    rw [List.cons_append, List.cons_append, lo_dl_high_bad _ hu hv, lo_dl_high_bad _ hu hv,
      ← List.cons_append, ih]
    rfl
  | case4 u hu =>
    rw [lo_dl_high_end hu]
    have hcs := lo_dl_encode cs
    generalize hE : encode cs = E at hcs
    cases E with
    | nil =>
      rw [lo_dl_nil] at hcs
      rw [← hcs, List.append_nil, List.append_nil, lo_dl_high_end hu]
    | cons e X =>
      have he : ¬ isLow e = true := by simp [lo_encode_head hE]
      rw [List.singleton_append, lo_dl_high_bad _ hu he, hcs]
      rfl
  | case5 u rest hu hl ih =>
    rw [List.cons_append, lo_dl_low _ hu hl, lo_dl_low _ hu hl, ih]
    rfl
  | case6 u rest hu hl ih =>
    rw [List.cons_append, lo_dl_plain _ hu hl, lo_dl_plain _ hu hl, ih]
    rfl


/-! ## `toWellFormed` -/

theorem lo_tw_pair {u v : UInt16} (r : List UInt16) (hu : isHigh u = true)
    (hv : isLow v = true) :
    encode (decodeLossy (u :: v :: r)) = u :: v :: encode (decodeLossy r) := by
  rw [lo_dl_pair _ hu hv, lo_encode_cons, lo_encodeChar_pair hu hv]; rfl

theorem lo_tw_high_bad {u v : UInt16} (r : List UInt16) (hu : isHigh u = true)
    (hv : ¬ isLow v = true) :
    encode (decodeLossy (u :: v :: r)) = 0xFFFD :: encode (decodeLossy (v :: r)) := by
  rw [lo_dl_high_bad _ hu hv, lo_encode_cons, lo_encodeChar_replacement]; rfl

theorem lo_tw_high_end {u : UInt16} (hu : isHigh u = true) :
    encode (decodeLossy [u]) = [0xFFFD] := by
  rw [lo_dl_high_end hu, lo_encode_single, lo_encodeChar_replacement]

theorem lo_tw_low {u : UInt16} (r : List UInt16) (hu : ¬ isHigh u = true)
    (hl : isLow u = true) :
    encode (decodeLossy (u :: r)) = 0xFFFD :: encode (decodeLossy r) := by
  rw [lo_dl_low _ hu hl, lo_encode_cons, lo_encodeChar_replacement]; rfl

theorem lo_tw_plain {u : UInt16} (r : List UInt16) (hu : ¬ isHigh u = true)
    (hl : ¬ isLow u = true) :
    encode (decodeLossy (u :: r)) = u :: encode (decodeLossy r) := by
  rw [lo_dl_plain _ hu hl, lo_encode_cons, lo_encodeChar_plain hu hl]; rfl

/-- `out` is `us` with each unit that is unpaired, with the units `l`
    before `us`, replaced by 0xFFFD. -/
def lo_TW (l us out : List UInt16) : Prop :=
  out.length = us.length ∧
  ∀ (i : Nat) (h : i < us.length),
    (Spec.Unpaired (l ++ us.take i) us[i] (us.drop (i + 1)) → out[i]? = some 0xFFFD) ∧
    (¬ Spec.Unpaired (l ++ us.take i) us[i] (us.drop (i + 1)) → out[i]? = some us[i])

theorem lo_TW_nil (l : List UInt16) : lo_TW l [] [] :=
  ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem lo_TW_cons {l rest X : List UInt16} {u a : UInt16}
    (h1 : Spec.Unpaired l u rest → a = 0xFFFD) (h2 : ¬ Spec.Unpaired l u rest → a = u)
    (h : lo_TW (l ++ [u]) rest X) : lo_TW l (u :: rest) (a :: X) := by
  refine ⟨by simp [h.1], fun i hi => ?_⟩
  match i, hi with
  | 0, _ =>
    simp only [List.take_zero, List.append_nil, List.getElem_cons_zero, List.drop_succ_cons,
      List.drop_zero, List.getElem?_cons_zero, Option.some.injEq]
    exact ⟨h1, h2⟩
  | i + 1, hi =>
    simp only [List.take_succ_cons, List.getElem_cons_succ, List.drop_succ_cons,
      List.getElem?_cons_succ]
    have he : l ++ u :: rest.take i = (l ++ [u]) ++ rest.take i := by simp
    rw [he]
    exact h.2 i (by simpa using hi)

theorem lo_endsHigh_append {l : List UInt16} {x : UInt16} :
    (∃ l' v, l ++ [x] = l' ++ [v] ∧ Spec.High v) ↔ Spec.High x := by
  constructor
  · rintro ⟨l', v, he, hv⟩
    have := congrArg List.reverse he
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons.injEq] at this
    rw [this.1]; exact hv
  · intro hx; exact ⟨l, x, rfl, hx⟩

theorem lo_tw_main (us : List UInt16) : ∀ (l : List UInt16),
    (∀ v r, us = v :: r → Spec.Low v → ¬ ∃ l' x, l = l' ++ [x] ∧ Spec.High x) →
    lo_TW l us (encode (decodeLossy us)) := by
  induction us using decodeLossy.induct with
  | case1 => intro l _; rw [lo_dl_nil]; exact lo_TW_nil l
  | case2 u hu v rest' hv ih =>
    intro l _
    rw [lo_tw_pair _ hu hv]
    have hU := (lo_isHigh_iff u).1 hu
    have hV := (lo_isLow_iff v).1 hv
    refine lo_TW_cons ?_ (fun _ => rfl) (lo_TW_cons ?_ (fun _ => rfl) (ih _ ?_))
    · rintro (⟨-, hn⟩ | ⟨hl, -⟩)
      · exact absurd ⟨v, rest', rfl, hV⟩ hn
      · exact absurd hl (lo_high_not_low hU)
    · rintro (⟨hh, -⟩ | ⟨-, hn⟩)
      · exact absurd hV (lo_high_not_low hh)
      · exact absurd (lo_endsHigh_append.2 hU) hn
    · intro v' r _ _ hx
      rw [lo_endsHigh_append] at hx
      exact lo_high_not_low hx hV
  | case3 u hu v rest' hv ih =>
    intro l _
    rw [lo_tw_high_bad _ hu hv]
    have hU := (lo_isHigh_iff u).1 hu
    refine lo_TW_cons (fun _ => rfl) ?_ (ih _ ?_)
    · intro hn
      refine absurd (Or.inl ⟨hU, ?_⟩) hn
      rintro ⟨v', r', he, hv'⟩
      simp only [List.cons.injEq] at he
      rw [← he.1, ← lo_isLow_iff] at hv'
      exact hv hv'
    · intro v' r he hv'
      simp only [List.cons.injEq] at he
      rw [← he.1, ← lo_isLow_iff] at hv'
      exact absurd hv' hv
  | case4 u hu =>
    intro l _
    rw [lo_tw_high_end hu]
    have hU := (lo_isHigh_iff u).1 hu
    refine lo_TW_cons (fun _ => rfl) ?_ (lo_TW_nil _)
    intro hn
    refine absurd (Or.inl ⟨hU, ?_⟩) hn
    rintro ⟨v', r', he, -⟩
    simp at he
  | case5 u rest hu hl ih =>
    intro l hlh
    rw [lo_tw_low _ hu hl]
    have hL := (lo_isLow_iff u).1 hl
    refine lo_TW_cons (fun _ => rfl) ?_ (ih _ ?_)
    · intro hn
      exact absurd (Or.inr ⟨hL, hlh u rest rfl hL⟩) hn
    · intro v' r _ _ hx
      rw [lo_endsHigh_append] at hx
      exact lo_high_not_low hx hL
  | case6 u rest hu hl ih =>
    intro l _
    rw [lo_tw_plain _ hu hl]
    rw [lo_isHigh_iff] at hu
    rw [lo_isLow_iff] at hl
    refine lo_TW_cons ?_ (fun _ => rfl) (ih _ ?_)
    · rintro (⟨hh, -⟩ | ⟨hl', -⟩)
      · exact absurd hh hu
      · exact absurd hl' hl
    · intro v' r _ _ hx
      rw [lo_endsHigh_append] at hx
      exact hu hx

theorem toWellFormed_spec (us : List UInt16) :
    (Utf16.toWellFormed us).length = us.length ∧
    ∀ (i : Nat) (h : i < us.length),
      (Spec.Unpaired (us.take i) us[i] (us.drop (i + 1)) →
        (Utf16.toWellFormed us)[i]? = some 0xFFFD) ∧
      (¬ Spec.Unpaired (us.take i) us[i] (us.drop (i + 1)) →
        (Utf16.toWellFormed us)[i]? = some us[i]) := by
  have h := lo_tw_main us [] (by
    rintro v r - - ⟨l', x, he, -⟩
    simp at he)
  exact ⟨h.1, fun i hi => h.2 i hi⟩

end Utf16.Proofs
