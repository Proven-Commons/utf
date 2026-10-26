/-
  UTF-16 code units: the encoder against RFC 2781, section 2.1, and the
  strict decoder against the encoding, Table 3-5, and isolated
  surrogates.
-/

import Utf16
import Spec.Utf16

namespace Utf16.Proofs

/-! ## Helpers: characters, units and the encoder -/

private theorem un_valid (c : Char) :
    c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := c.valid

private theorem un_toNat_ofNat {n : Nat} (h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  have h' : n.isValidChar := h
  simp [Char.ofNat, h', Char.ofNatAux, Char.toNat]

private theorem un_toNat_toUInt16 (n : Nat) : n.toUInt16.toNat = n % 65536 := by simp

private theorem un_toUInt16_eq {u : UInt16} {n : Nat} (h : n = u.toNat) : n.toUInt16 = u := by
  subst h; simp

private theorem un_encode_cons (c : Char) (cs : List Char) :
    encode (c :: cs) = encodeChar c ++ encode cs := by
  simp [encode, List.flatMap_cons]

private theorem un_encodeChar_lt (c : Char) (h : c.toNat < 0x10000) :
    encodeChar c = [c.toNat.toUInt16] := by
  simp only [encodeChar, h, ↓reduceIte]

private theorem un_encodeChar_ge (c : Char) (h : ¬ c.toNat < 0x10000) :
    encodeChar c = [(0xD800 + (c.toNat - 0x10000) / 0x400).toUInt16,
      (0xDC00 + (c.toNat - 0x10000) % 0x400).toUInt16] := by
  simp only [encodeChar, h, ↓reduceIte]

private theorem un_isHigh_iff (u : UInt16) :
    isHigh u = true ↔ 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF := by
  simp [isHigh]

private theorem un_isLow_iff (u : UInt16) :
    isLow u = true ↔ 0xDC00 ≤ u.toNat ∧ u.toNat ≤ 0xDFFF := by
  simp [isLow]

/-! ## RFC 2781's bit operations as arithmetic -/

private theorem un_or_hi (m : Nat) (hm : m < 0x100000) :
    (0xD800 ||| m >>> 10) = 0xD800 + m / 0x400 := by
  rw [Nat.shiftRight_eq_div_pow]
  have hb : m / 1024 < 2 ^ 10 := by
    show m / 1024 < 1024
    omega
  exact (Nat.two_pow_add_eq_or_of_lt hb 54).symm

private theorem un_or_lo (m : Nat) :
    (0xDC00 ||| m &&& 0x3FF) = 0xDC00 + m % 0x400 := by
  have h1 : m &&& 0x3FF = m % 2 ^ 10 := Nat.and_two_pow_sub_one_eq_mod m 10
  rw [h1]
  have hb : m % 2 ^ 10 < 2 ^ 10 := Nat.mod_lt _ (by decide)
  exact (Nat.two_pow_add_eq_or_of_lt hb 55).symm

private theorem un_encodeChar_spec (c : Char) : encodeChar c = Spec.encodeChar16 c := by
  have hv := un_valid c
  unfold encodeChar Spec.encodeChar16
  simp only
  split
  · rfl
  · rw [un_or_hi _ (by omega), un_or_lo]

theorem encode_eq (cs : List Char) : Utf16.encode cs = Spec.encode16 cs := by
  induction cs with
  | nil => simp [encode, Spec.encode16]
  | cons c cs ih =>
    rw [un_encode_cons, ih, un_encodeChar_spec]
    simp only [Spec.encode16, List.map_cons, List.flatten_cons]


/-! ## The decoder, one character at a time -/

private theorem un_decode_single (u : UInt16) (rest : List UInt16) (hh : ¬ isHigh u = true)
    (hl : ¬ isLow u = true) : decode (u :: rest) = (decode rest).map (Char.ofNat u.toNat :: ·) := by
  cases rest <;> simp [decode, hh, hl]

private theorem un_decode_pair (u v : UInt16) (rest : List UInt16) (hh : isHigh u = true)
    (hl : isLow v = true) : decode (u :: v :: rest) = (decode rest).map (pair u v :: ·) := by
  simp [decode, hh, hl]

/-- A unit outside the surrogates is the encoding of the character it names. -/
private theorem un_encodeChar_single (u : UInt16) (h : u.toNat < 0xD800 ∨ 0xDFFF < u.toNat) :
    encodeChar (Char.ofNat u.toNat) = [u] := by
  have hu := u.toNat_lt
  have hc : (Char.ofNat u.toNat).toNat = u.toNat := un_toNat_ofNat (by omega)
  rw [un_encodeChar_lt _ (by omega), hc, un_toUInt16_eq rfl]

/-- A high then a low surrogate are the encoding of the character they name. -/
private theorem un_encodeChar_pair (u v : UInt16) (hu : 0xD800 ≤ u.toNat ∧ u.toNat ≤ 0xDBFF)
    (hv : 0xDC00 ≤ v.toNat ∧ v.toNat ≤ 0xDFFF) : encodeChar (pair u v) = [u, v] := by
  have hp : (pair u v).toNat = 0x10000 + (u.toNat - 0xD800) * 0x400 + (v.toNat - 0xDC00) := by
    unfold pair; apply un_toNat_ofNat; omega
  rw [un_encodeChar_ge _ (by omega), hp]
  simp only [List.cons.injEq, and_true]
  constructor <;> apply un_toUInt16_eq <;> omega

private theorem un_decode_encodeChar_append (c : Char) (rest : List UInt16) :
    decode (encodeChar c ++ rest) = (decode rest).map (c :: ·) := by
  have hv := un_valid c
  by_cases h : c.toNat < 0x10000
  · rw [un_encodeChar_lt c h]
    have hu : c.toNat.toUInt16.toNat = c.toNat := by rw [un_toNat_toUInt16]; omega
    have hh : ¬ isHigh c.toNat.toUInt16 = true := by rw [un_isHigh_iff, hu]; omega
    have hl : ¬ isLow c.toNat.toUInt16 = true := by rw [un_isLow_iff, hu]; omega
    rw [List.singleton_append, un_decode_single _ _ hh hl, hu, Char.ofNat_toNat]
  · rw [un_encodeChar_ge c h]
    generalize hm : c.toNat - 0x10000 = m
    have h1 : (0xD800 + m / 0x400).toUInt16.toNat = 0xD800 + m / 0x400 := by
      rw [un_toNat_toUInt16]; omega
    have h2 : (0xDC00 + m % 0x400).toUInt16.toNat = 0xDC00 + m % 0x400 := by
      rw [un_toNat_toUInt16]; omega
    have hh : isHigh (0xD800 + m / 0x400).toUInt16 = true := by rw [un_isHigh_iff, h1]; omega
    have hl : isLow (0xDC00 + m % 0x400).toUInt16 = true := by rw [un_isLow_iff, h2]; omega
    have hp : pair (0xD800 + m / 0x400).toUInt16 (0xDC00 + m % 0x400).toUInt16 = c := by
      unfold pair
      rw [h1, h2]
      have e : 0x10000 + (0xD800 + m / 0x400 - 0xD800) * 0x400 + (0xDC00 + m % 0x400 - 0xDC00)
          = c.toNat := by omega
      rw [e, Char.ofNat_toNat]
    rw [List.cons_append, List.cons_append, List.nil_append, un_decode_pair _ _ _ hh hl, hp]

theorem decode_iff (us : List UInt16) (cs : List Char) :
    Utf16.decode us = some cs ↔ us = Utf16.encode cs := by
  constructor
  · intro h
    induction us using decode.induct generalizing cs with
    | case1 =>
      simp [decode] at h
      subst h
      simp [encode]
    | case2 u hu v rest' hv ih =>
      rw [un_decode_pair _ _ _ hu hv] at h
      obtain ⟨cs', h', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [un_encode_cons, un_encodeChar_pair u v ((un_isHigh_iff u).1 hu) ((un_isLow_iff v).1 hv),
        ← ih cs' h']
      rfl
    | case3 u hu v rest' hv => simp [decode, hu, hv] at h
    | case4 u hu => simp [decode, hu] at h
    | case5 u rest hu hl => cases rest <;> simp [decode, hu, hl] at h
    | case6 u rest hu hl ih =>
      rw [un_decode_single _ _ hu hl] at h
      obtain ⟨cs', h', rfl⟩ := Option.map_eq_some_iff.1 h
      rw [un_isHigh_iff] at hu
      rw [un_isLow_iff] at hl
      rw [un_encode_cons, un_encodeChar_single u (by omega), ← ih cs' h']
      rfl
  · rintro rfl
    induction cs with
    | nil => simp [encode, decode]
    | cons c cs ih => rw [un_encode_cons, un_decode_encodeChar_append, ih]; rfl

theorem decode_encode (cs : List Char) : Utf16.decode (Utf16.encode cs) = some cs :=
  (decode_iff _ _).2 rfl

/-! ## Well-formed sequences -/

private theorem un_wellFormedChar_iff (s : List UInt16) :
    Spec.WellFormedChar16 s ↔ ∃ c, s = encodeChar c := by
  constructor
  · intro h
    rcases s with _ | ⟨w, _ | ⟨w2, _ | ⟨w3, s⟩⟩⟩
    · simp [Spec.WellFormedChar16] at h
    · simp only [Spec.WellFormedChar16] at h
      exact ⟨Char.ofNat w.toNat, (un_encodeChar_single w (by omega)).symm⟩
    · simp only [Spec.WellFormedChar16, Spec.High, Spec.Low] at h
      exact ⟨pair w w2, (un_encodeChar_pair w w2 h.1 h.2).symm⟩
    · simp [Spec.WellFormedChar16] at h
  · rintro ⟨c, rfl⟩
    have hv := un_valid c
    by_cases h : c.toNat < 0x10000
    · rw [un_encodeChar_lt c h]
      simp only [Spec.WellFormedChar16, un_toNat_toUInt16]
      omega
    · rw [un_encodeChar_ge c h]
      simp only [Spec.WellFormedChar16, Spec.High, Spec.Low, un_toNat_toUInt16]
      omega

theorem wellFormed_iff (us : List UInt16) :
    Spec.WellFormed16 us ↔ ∃ cs, us = Utf16.encode cs := by
  constructor
  · intro h
    induction h with
    | nil => exact ⟨[], by simp [encode]⟩
    | cons hs _ ih =>
      obtain ⟨c, rfl⟩ := (un_wellFormedChar_iff _).1 hs
      obtain ⟨cs, rfl⟩ := ih
      exact ⟨c :: cs, (un_encode_cons c cs).symm⟩
  · rintro ⟨cs, rfl⟩
    induction cs with
    | nil => simpa [encode] using Spec.WellFormed16.nil
    | cons c cs ih =>
      rw [un_encode_cons]
      exact Spec.WellFormed16.cons ((un_wellFormedChar_iff _).2 ⟨c, rfl⟩) ih

/-! ## Unpaired surrogates -/

/-- A unit put before the units on the left of `w` changes nothing, so
    long as it is not a high surrogate right before `w`. -/
private theorem un_unpaired_cons_iff {a : UInt16} {l : List UInt16} {w : UInt16}
    {r : List UInt16} (ha : l = [] → ¬ Spec.High a) :
    Spec.Unpaired (a :: l) w r ↔ Spec.Unpaired l w r := by
  unfold Spec.Unpaired
  have key : (∃ l' v, a :: l = l' ++ [v] ∧ Spec.High v) ↔ (∃ l' v, l = l' ++ [v] ∧ Spec.High v) := by
    constructor
    · rintro ⟨l', v, he, hv⟩
      rcases l' with _ | ⟨b, l''⟩
      · simp only [List.nil_append, List.cons.injEq] at he
        exact absurd (he.1 ▸ hv) (ha he.2)
      · simp only [List.cons_append, List.cons.injEq] at he
        exact ⟨l'', v, he.2, hv⟩
    · rintro ⟨l', v, he, hv⟩
      exact ⟨a :: l', v, by rw [he]; rfl, hv⟩
  rw [key]

/-- No unit of an encoding is an unpaired surrogate. -/
private theorem un_encode_not_unpaired (cs : List Char) :
    ∀ l w r, encode cs = l ++ w :: r → ¬ Spec.Unpaired l w r := by
  induction cs with
  | nil => intro l w r h; simp [encode] at h
  | cons c cs ih =>
    intro l w r h hun
    rw [un_encode_cons] at h
    have hv := un_valid c
    by_cases hc : c.toNat < 0x10000
    · rw [un_encodeChar_lt c hc] at h
      have hu : c.toNat.toUInt16.toNat = c.toNat := by rw [un_toNat_toUInt16]; omega
      have hnh : ¬ Spec.High c.toNat.toUInt16 := by unfold Spec.High; rw [hu]; omega
      rcases l with _ | ⟨a, l'⟩
      · simp only [List.nil_append, List.singleton_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases hun with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact hnh h1
        · unfold Spec.Low at h1; rw [hu] at h1; omega
      · simp only [List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, h⟩ := h
        exact ih l' w r h ((un_unpaired_cons_iff (fun _ => hnh)).1 hun)
    · rw [un_encodeChar_ge c hc] at h
      generalize hm : c.toNat - 0x10000 = m at h
      have hmb : m < 0x100000 := by omega
      have h1 : (0xD800 + m / 0x400).toUInt16.toNat = 0xD800 + m / 0x400 := by
        rw [un_toNat_toUInt16]; omega
      have h2 : (0xDC00 + m % 0x400).toUInt16.toNat = 0xDC00 + m % 0x400 := by
        rw [un_toNat_toUInt16]; omega
      generalize (0xD800 + m / 0x400).toUInt16 = hi at h h1
      generalize (0xDC00 + m % 0x400).toUInt16 = lo at h h2
      have hhi : Spec.High hi := by unfold Spec.High; rw [h1]; omega
      have hlo : Spec.Low lo := by unfold Spec.Low; rw [h2]; omega
      have hlo' : ¬ Spec.High lo := by unfold Spec.High; rw [h2]; omega
      have hhi' : ¬ Spec.Low hi := by unfold Spec.Low; rw [h1]; omega
      rcases l with _ | ⟨a, _ | ⟨b, l''⟩⟩
      · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        rcases hun with ⟨_, hn⟩ | ⟨hl, _⟩
        · exact hn ⟨lo, encode cs, rfl, hlo⟩
        · exact hhi' hl
      · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rcases hun with ⟨hh, _⟩ | ⟨_, hn⟩
        · exact hlo' hh
        · exact hn ⟨[], _, rfl, hhi⟩
      · simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
        obtain ⟨rfl, rfl, h⟩ := h
        rw [un_unpaired_cons_iff (by simp), un_unpaired_cons_iff (fun _ => hlo')] at hun
        exact ih l'' w r h hun

theorem decode_none_iff (us : List UInt16) :
    Utf16.decode us = none ↔ ∃ l w r, us = l ++ w :: r ∧ Spec.Unpaired l w r := by
  constructor
  · intro h
    induction us using decode.induct with
    | case1 => simp [decode] at h
    | case2 u hu v rest' hv ih =>
      rw [un_decode_pair _ _ _ hu hv, Option.map_eq_none_iff] at h
      obtain ⟨l, w, r, rfl, hun⟩ := ih h
      refine ⟨u :: v :: l, w, r, rfl, ?_⟩
      have hvh : ¬ Spec.High v := by
        rw [un_isLow_iff] at hv; unfold Spec.High; omega
      rw [un_unpaired_cons_iff (by simp), un_unpaired_cons_iff (fun _ => hvh)]
      exact hun
    | case3 u hu v rest' hv =>
      refine ⟨[], u, v :: rest', rfl, Or.inl ⟨(un_isHigh_iff u).1 hu, ?_⟩⟩
      rintro ⟨v', r', he, hl⟩
      simp only [List.cons.injEq] at he
      exact hv (he.1 ▸ (un_isLow_iff _).2 hl)
    | case4 u hu =>
      refine ⟨[], u, [], rfl, Or.inl ⟨(un_isHigh_iff u).1 hu, ?_⟩⟩
      rintro ⟨v', r', he, _⟩
      cases he
    | case5 u rest hu hl =>
      refine ⟨[], u, rest, rfl, Or.inr ⟨(un_isLow_iff u).1 hl, ?_⟩⟩
      rintro ⟨l', v, he, _⟩
      simp at he
    | case6 u rest hu hl ih =>
      rw [un_decode_single _ _ hu hl, Option.map_eq_none_iff] at h
      obtain ⟨l, w, r, rfl, hun⟩ := ih h
      refine ⟨u :: l, w, r, rfl, ?_⟩
      have huh : ¬ Spec.High u := fun h' => hu ((un_isHigh_iff u).2 h')
      rw [un_unpaired_cons_iff (fun _ => huh)]
      exact hun
  · rintro ⟨l, w, r, hus, hun⟩
    cases hd : decode us with
    | none => rfl
    | some cs =>
      exfalso
      rw [(decode_iff us cs).1 hd] at hus
      exact un_encode_not_unpaired cs l w r hus hun

theorem encode_length (cs : List Char) :
    (Utf16.encode cs).length = cs.length + (cs.filter fun c => 0x10000 ≤ c.toNat).length := by
  induction cs with
  | nil => simp [encode]
  | cons c cs ih =>
    rw [un_encode_cons, List.length_append, ih, List.filter_cons]
    by_cases h : c.toNat < 0x10000
    · have h' : ¬ 0x10000 ≤ c.toNat := by omega
      simp [un_encodeChar_lt c h, h']
      omega
    · have h' : 0x10000 ≤ c.toNat := by omega
      simp [un_encodeChar_ge c h, h']
      omega

end Utf16.Proofs
