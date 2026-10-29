/-
  The definitions the specification uses, written from RFC 3629, from
  Table 3-7 of the Unicode Standard (section 3.9), and from section 3.9.6
  of the Unicode Standard, version 16.0 (D93a, D93b), independently of
  the code in `Utf8/`. Part of the approved specification, with
  `Utf/Spec.lean`.

  Characters are Lean's `Char`, which holds exactly the Unicode scalar
  values: 0 to 0xD7FF and 0xE000 to 0x10FFFF.

  Both the challenge file and the proofs import this file, so each
  statement means the same thing on both sides. The `example`s check the
  definitions against the RFC's examples, and against the first and last
  sequence of each row of the table and the bytes just outside its edges.
  The definitions of section 3.9.6 have two direct checks here; the
  standard's own examples, Tables 3-8 to 3-11, are checked through
  `Utf.Spec.substitution_vectors` together with `Utf.Spec.decodeLossy_iff`.
-/

import Utf8

/-! ## RFC 3629, section 3

```
Char. number range  |        UTF-8 octet sequence
   (hexadecimal)    |              (binary)
--------------------+---------------------------------------------
0000 0000-0000 007F | 0xxxxxxx
0000 0080-0000 07FF | 110xxxxx 10xxxxxx
0000 0800-0000 FFFF | 1110xxxx 10xxxxxx 10xxxxxx
0001 0000-0010 FFFF | 11110xxx 10xxxxxx 10xxxxxx 10xxxxxx
```

"Fill in the bits marked x from the bits of the character number,
expressed in binary. Start by putting the lowest-order bit of the
character number in the lowest-order position of the last octet of the
sequence, then put the next higher-order bit of the character number in
the next higher-order position of that octet, etc. When the x bits of
the last octet are filled in, move on to the next to last octet, then to
the preceding one, etc. until all x bits are filled in." -/

/-- The six bits of `n` that go in a continuation byte, `k` bytes from
    the end, after the marker `10`. -/
def Utf.Spec.contByte (n k : Nat) : UInt8 :=
  (0b10000000 ||| (n >>> (6 * k) &&& 0b111111)).toUInt8

/-- The octet sequence of RFC 3629, section 3, for one character. -/
def Utf.Spec.encodeChar (c : Char) : List UInt8 :=
  let n := c.toNat
  if n ≤ 0x7F then [n.toUInt8]
  else if n ≤ 0x7FF then [(0b11000000 ||| n >>> 6).toUInt8, Utf.Spec.contByte n 0]
  else if n ≤ 0xFFFF then
    [(0b11100000 ||| n >>> 12).toUInt8, Utf.Spec.contByte n 1, Utf.Spec.contByte n 0]
  else
    [(0b11110000 ||| n >>> 18).toUInt8, Utf.Spec.contByte n 2, Utf.Spec.contByte n 1,
     Utf.Spec.contByte n 0]

/-- The UTF-8 bytes of a list of characters, one after another. -/
def Utf.Spec.encode (cs : List Char) : List UInt8 :=
  (cs.map Utf.Spec.encodeChar).flatten

-- The examples of RFC 3629, section 7: "A≢Α." (U+0041 U+2262 U+0391
-- U+002E), the Korean word "hangugeo" (U+D55C U+AD6D U+C5B4), the
-- Japanese word "nihongo" (U+65E5 U+672C U+8A9E), and a byte order mark
-- followed by U+233B4.
example : Utf.Spec.encode ['A', '≢', '\u0391', '.'] =
    [0x41, 0xE2, 0x89, 0xA2, 0xCE, 0x91, 0x2E] := by decide
example : Utf.Spec.encode ['한', '국', '어'] =
    [0xED, 0x95, 0x9C, 0xEA, 0xB5, 0xAD, 0xEC, 0x96, 0xB4] := by decide
example : Utf.Spec.encode ['日', '本', '語'] =
    [0xE6, 0x97, 0xA5, 0xE6, 0x9C, 0xAC, 0xE8, 0xAA, 0x9E] := by decide
example : Utf.Spec.encode ['\uFEFF', Char.ofNat 0x233B4] =
    [0xEF, 0xBB, 0xBF, 0xF0, 0xA3, 0x8E, 0xB4] := by decide

/-! ## The Unicode Standard, Table 3-7, Well-Formed UTF-8 Byte Sequences

```
Code Points          First Byte  Second Byte  Third Byte  Fourth Byte
U+0000..U+007F       00..7F
U+0080..U+07FF       C2..DF      80..BF
U+0800..U+0FFF       E0          A0..BF       80..BF
U+1000..U+CFFF       E1..EC      80..BF       80..BF
U+D000..U+D7FF       ED          80..9F       80..BF
U+E000..U+FFFF       EE..EF      80..BF       80..BF
U+10000..U+3FFFF     F0          90..BF       80..BF      80..BF
U+40000..U+FFFFF     F1..F3      80..BF       80..BF      80..BF
U+100000..U+10FFFF   F4          80..8F       80..BF      80..BF
```
-/

/-- `b` is in the range `lo..hi`, both ends included. -/
def Utf.Spec.InRange (lo hi : Nat) (b : UInt8) : Prop := lo ≤ b.toNat ∧ b.toNat ≤ hi

/-- One row of Table 3-7: the bytes of a single well-formed sequence. -/
def Utf.Spec.WellFormedChar : List UInt8 → Prop
  | [b0] => Utf.Spec.InRange 0x00 0x7F b0
  | [b0, b1] => Utf.Spec.InRange 0xC2 0xDF b0 ∧ Utf.Spec.InRange 0x80 0xBF b1
  | [b0, b1, b2] =>
    ((Utf.Spec.InRange 0xE0 0xE0 b0 ∧ Utf.Spec.InRange 0xA0 0xBF b1) ∨
     (Utf.Spec.InRange 0xE1 0xEC b0 ∧ Utf.Spec.InRange 0x80 0xBF b1) ∨
     (Utf.Spec.InRange 0xED 0xED b0 ∧ Utf.Spec.InRange 0x80 0x9F b1) ∨
     (Utf.Spec.InRange 0xEE 0xEF b0 ∧ Utf.Spec.InRange 0x80 0xBF b1)) ∧
    Utf.Spec.InRange 0x80 0xBF b2
  | [b0, b1, b2, b3] =>
    ((Utf.Spec.InRange 0xF0 0xF0 b0 ∧ Utf.Spec.InRange 0x90 0xBF b1) ∨
     (Utf.Spec.InRange 0xF1 0xF3 b0 ∧ Utf.Spec.InRange 0x80 0xBF b1) ∨
     (Utf.Spec.InRange 0xF4 0xF4 b0 ∧ Utf.Spec.InRange 0x80 0x8F b1)) ∧
    Utf.Spec.InRange 0x80 0xBF b2 ∧ Utf.Spec.InRange 0x80 0xBF b3
  | _ => False

/-- A well-formed byte sequence: well-formed sequences from Table 3-7,
    one after another. -/
inductive Utf.Spec.WellFormed : List UInt8 → Prop where
  | nil : Utf.Spec.WellFormed []
  | cons {s rest : List UInt8} :
      Utf.Spec.WellFormedChar s → Utf.Spec.WellFormed rest → Utf.Spec.WellFormed (s ++ rest)

example : Utf.Spec.WellFormedChar [0xF4, 0x8F, 0xBF, 0xBF] := by
  unfold Utf.Spec.WellFormedChar Utf.Spec.InRange; decide
example : ¬ Utf.Spec.WellFormedChar [0xED, 0xA0, 0x80] := by
  unfold Utf.Spec.WellFormedChar Utf.Spec.InRange; decide

-- The first and last sequence of each row of Table 3-7.
example :
    Utf.Spec.WellFormedChar [0x00] ∧ Utf.Spec.WellFormedChar [0x7F] ∧
    Utf.Spec.WellFormedChar [0xC2, 0x80] ∧ Utf.Spec.WellFormedChar [0xDF, 0xBF] ∧
    Utf.Spec.WellFormedChar [0xE0, 0xA0, 0x80] ∧ Utf.Spec.WellFormedChar [0xE0, 0xBF, 0xBF] ∧
    Utf.Spec.WellFormedChar [0xE1, 0x80, 0x80] ∧ Utf.Spec.WellFormedChar [0xEC, 0xBF, 0xBF] ∧
    Utf.Spec.WellFormedChar [0xED, 0x80, 0x80] ∧ Utf.Spec.WellFormedChar [0xED, 0x9F, 0xBF] ∧
    Utf.Spec.WellFormedChar [0xEE, 0x80, 0x80] ∧ Utf.Spec.WellFormedChar [0xEF, 0xBF, 0xBF] ∧
    Utf.Spec.WellFormedChar [0xF0, 0x90, 0x80, 0x80] ∧ Utf.Spec.WellFormedChar [0xF0, 0xBF, 0xBF, 0xBF] ∧
    Utf.Spec.WellFormedChar [0xF1, 0x80, 0x80, 0x80] ∧ Utf.Spec.WellFormedChar [0xF3, 0xBF, 0xBF, 0xBF] ∧
    Utf.Spec.WellFormedChar [0xF4, 0x80, 0x80, 0x80] ∧ Utf.Spec.WellFormedChar [0xF4, 0x8F, 0xBF, 0xBF] := by
  simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange, UInt8.toNat]; and_intros <;> decide

-- Just outside the edges of the rows.
example :
    ¬ Utf.Spec.WellFormedChar [0x80] ∧ ¬ Utf.Spec.WellFormedChar [0xC1, 0xBF] ∧
    ¬ Utf.Spec.WellFormedChar [0xC2, 0x7F] ∧ ¬ Utf.Spec.WellFormedChar [0xC2, 0xC0] ∧
    ¬ Utf.Spec.WellFormedChar [0xE0, 0x9F, 0xBF] ∧ ¬ Utf.Spec.WellFormedChar [0xED, 0xA0, 0x80] ∧
    ¬ Utf.Spec.WellFormedChar [0xF0, 0x8F, 0xBF, 0xBF] ∧ ¬ Utf.Spec.WellFormedChar [0xF4, 0x90, 0x80, 0x80] ∧
    ¬ Utf.Spec.WellFormedChar [0xF5, 0x80, 0x80, 0x80] := by
  simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange, UInt8.toNat]; and_intros <;> decide

/-! ## The Unicode Standard, section 3.9.6, U+FFFD Substitution of Maximal Subparts

```
D93a Unconvertible offset: An offset in a code unit sequence for which
     no code unit subsequence starting at that offset is well-formed.

D93b Maximal subpart of an ill-formed subsequence: The longest code
     unit subsequence starting at an unconvertible offset that is
     either:
     a. the initial subsequence of a well-formed code unit sequence, or
     b. a subsequence of length one.
```

"Whenever an unconvertible offset is reached during conversion of a
code unit sequence:
1. The maximal subpart at that offset is replaced by a single U+FFFD.
2. The conversion proceeds at the offset immediately after the maximal
   subpart."

Below, an offset is the front of the bytes that remain, and a
subsequence starting there is a prefix of them (`<+:`).
-/

/-- `p` is the initial subsequence of a well-formed code unit sequence.

    That sequence may hold more than one character. The note under D93b
    speaks of one character: "as many code units as match the beginning
    of a well-formed character". Where this definition is used, the two
    readings agree. `Utf.Spec.MaximalSubpart` asks it only of bytes at an
    unconvertible offset. By D93a, no well-formed sequence starts there,
    not even the bytes of one whole character. So `p` stops inside the
    bytes of the first character of the well-formed sequence. That is,
    `p` is the start of one character. The proofs show this as
    `Utf8.Proofs.Lossy.initial_iff`, in `Utf/Proofs/Lossy/Table.lean`. -/
def Utf.Spec.Initial (p : List UInt8) : Prop :=
  ∃ s, Utf.Spec.WellFormed s ∧ p <+: s

/-- D93a: no subsequence starting at the front of `bs` is well formed.
    (The empty one is left out: it starts nowhere.) -/
def Utf.Spec.Unconvertible (bs : List UInt8) : Prop :=
  ∀ s, s ≠ [] → s <+: bs → ¬ Utf.Spec.WellFormed s

/-- D93b: `p` is the maximal subpart at the front of `p ++ rest`. The
    front is an unconvertible offset, and `p` is the longest prefix
    there that is either the start of a well-formed sequence or one
    byte long. -/
def Utf.Spec.MaximalSubpart (p rest : List UInt8) : Prop :=
  p ≠ [] ∧ Utf.Spec.Unconvertible (p ++ rest) ∧
  (Utf.Spec.Initial p ∨ p.length = 1) ∧
  ∀ q, q <+: p ++ rest → (Utf.Spec.Initial q ∨ q.length = 1) → q.length ≤ p.length

/-- Conversion with U+FFFD substitution of maximal subparts: converting
    `bs` gives `out`. Where a character's well-formed sequence starts,
    it gives the character; at an unconvertible offset, the maximal
    subpart gives one U+FFFD; either way, conversion proceeds after the
    bytes used. -/
inductive Utf.Spec.Substitutes : List UInt8 → List Char → Prop where
  | nil : Utf.Spec.Substitutes [] []
  | char {c : Char} {rest : List UInt8} {out : List Char} :
      Utf.Spec.Substitutes rest out → Utf.Spec.Substitutes (Utf.Spec.encodeChar c ++ rest) (c :: out)
  | replace {p rest : List UInt8} {out : List Char} :
      Utf.Spec.MaximalSubpart p rest → Utf.Spec.Substitutes rest out →
      Utf.Spec.Substitutes (p ++ rest) ('�' :: out)

-- A well-formed sequence starts at the front of `E2 82 AC` (U+20AC), so
-- that offset is not unconvertible.
example : ¬ Utf.Spec.Unconvertible [0xE2, 0x82, 0xAC] := by
  intro h
  apply h [0xE2, 0x82, 0xAC] (by simp) (List.prefix_refl _)
  have : Utf.Spec.WellFormedChar [0xE2, 0x82, 0xAC] := by
    simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange, UInt8.toNat]; decide
  simpa using Utf.Spec.WellFormed.cons this Utf.Spec.WellFormed.nil

-- `F0 9F 98` is the start of a well-formed sequence, `F0 9F 98 80`.
example : Utf.Spec.Initial [0xF0, 0x9F, 0x98] := by
  refine ⟨[0xF0, 0x9F, 0x98, 0x80], ?_, ⟨[0x80], rfl⟩⟩
  have : Utf.Spec.WellFormedChar [0xF0, 0x9F, 0x98, 0x80] := by
    simp only [Utf.Spec.WellFormedChar, Utf.Spec.InRange, UInt8.toNat]; decide
  simpa using Utf.Spec.WellFormed.cons this Utf.Spec.WellFormed.nil
