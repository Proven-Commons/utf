/-
  The definitions the UTF-16 statements use, written from RFC 2781,
  from the Unicode Standard, version 16.0 (D72 to D75, D91, Table 3-5,
  D96 to D98, and section 3.9.6, D93a and D93b), from the WHATWG Encoding
  Standard (section 14.2.1, the shared UTF-16 decoder), and from
  ECMAScript's `String.prototype.toWellFormed`, independently of the code
  in `Utf16/`. Part of the approved specification, with `Utf/Spec.lean`.

  Code units are `UInt16`. Characters are Lean's `Char`, which holds
  exactly the Unicode scalar values: 0 to 0xD7FF and 0xE000 to 0x10FFFF.

  The `example`s check the definitions against the examples of D91,
  D96 to D98 and RFC 2781, section 5, at the edges of the surrogate
  ranges, and on the cases of the WHATWG decoder's steps.
-/

import Utf.Spec.Defs

/-! ## Surrogates: the Unicode Standard, D72, D74, D75

```
D72 High-surrogate code unit: A 16-bit code unit in the range D800 to
    DBFF, used in UTF-16 as the leading code unit of a surrogate pair.
D74 Low-surrogate code unit: A 16-bit code unit in the range DC00 to
    DFFF, used in UTF-16 as the trailing code unit of a surrogate pair.
D75 Surrogate pair: A representation for a single abstract character
    that consists of a sequence of two 16-bit code units, where the
    first value of the pair is a high-surrogate code unit and the second
    value is a low-surrogate code unit. [...] Isolated surrogate code
    units have no interpretation on their own.
```
-/

/-- D72: a high-surrogate code unit. -/
def Utf.Spec.High (w : UInt16) : Prop := 0xD800 ≤ w.toNat ∧ w.toNat ≤ 0xDBFF

/-- D74: a low-surrogate code unit. -/
def Utf.Spec.Low (w : UInt16) : Prop := 0xDC00 ≤ w.toNat ∧ w.toNat ≤ 0xDFFF

/-- The unit `w`, with the units `l` before it and `r` after it, is an
    isolated surrogate, in no surrogate pair (D75): a high surrogate
    that no low surrogate follows, or a low surrogate that no high
    surrogate comes right before. -/
def Utf.Spec.Unpaired (l : List UInt16) (w : UInt16) (r : List UInt16) : Prop :=
  (Utf.Spec.High w ∧ ¬ ∃ v r', r = v :: r' ∧ Utf.Spec.Low v) ∨
  (Utf.Spec.Low w ∧ ¬ ∃ l' v, l = l' ++ [v] ∧ Utf.Spec.High v)

/-! ## RFC 2781, section 2.1, Encoding UTF-16

```
1) If U < 0x10000, encode U as a 16-bit unsigned integer and
   terminate.
2) Let U' = U - 0x10000. Because U is less than or equal to 0x10FFFF,
   U' must be less than or equal to 0xFFFFF. That is, U' can be
   represented in 20 bits.
3) Initialize two 16-bit unsigned integers, W1 and W2, to 0xD800 and
   0xDC00, respectively. These integers each have 10 bits free to
   encode the character value, for a total of 20 bits.
4) Assign the 10 high-order bits of the 20-bit U' to the 10 low-order
   bits of W1 and the 10 low-order bits of U' to the 10 low-order
   bits of W2. Terminate.
```
-/

/-- The units of one character, by the four steps of RFC 2781,
    section 2.1. -/
def Utf.Spec.encodeChar16 (c : Char) : List UInt16 :=
  let u := c.toNat
  if u < 0x10000 then [u.toUInt16]
  else
    let u' := u - 0x10000
    [(0xD800 ||| u' >>> 10).toUInt16, (0xDC00 ||| u' &&& 0x3FF).toUInt16]

/-- The UTF-16 code units of a list of characters, one after another. -/
def Utf.Spec.encode16 (cs : List Char) : List UInt16 :=
  (cs.map Utf.Spec.encodeChar16).flatten

-- D91: "In UTF-16, the code point sequence <004D, 0430, 4E8C, 10302> is
-- represented as <004D 0430 4E8C D800 DF02>".
example : Utf.Spec.encode16 ['M', '\u0430', '二', Char.ofNat 0x10302] =
    [0x004D, 0x0430, 0x4E8C, 0xD800, 0xDF02] := by decide +kernel

-- RFC 2781, section 5: U+12345, then "=Ra".
example : Utf.Spec.encode16 [Char.ofNat 0x12345, '=', 'R', 'a'] =
    [0xD808, 0xDF45, 0x003D, 0x0052, 0x0061] := by decide +kernel

-- The ends of the ranges: U+D7FF, U+E000, U+FFFF, U+10000, U+10FFFF.
example : Utf.Spec.encode16 [Char.ofNat 0xD7FF, Char.ofNat 0xE000, Char.ofNat 0xFFFF,
      Char.ofNat 0x10000, Char.ofNat 0x10FFFF] =
    [0xD7FF, 0xE000, 0xFFFF, 0xD800, 0xDC00, 0xDBFF, 0xDFFF] := by decide +kernel

/-! ## The Unicode Standard, D91 and Table 3-5

```
D91 UTF-16 encoding form: The Unicode encoding form that assigns each
    Unicode scalar value in the ranges U+0000..U+D7FF and U+E000..U+FFFF
    to a single unsigned 16-bit code unit with the same numeric value as
    the Unicode scalar value, and that assigns each Unicode scalar value
    in the range U+10000..U+10FFFF to a surrogate pair, according to
    Table 3-5. [...] Because surrogate code points are not Unicode
    scalar values, isolated UTF-16 code units in the range D800..DFFF
    are ill-formed.

Table 3-5. UTF-16 Bit Distribution
Scalar Value                 UTF-16
xxxxxxxxxxxxxxxx             xxxxxxxxxxxxxxxx
000uuuuuxxxxxxxxxxxxxxxx     110110wwwwxxxxxx 110111xxxxxxxxxx
Note: wwww = uuuuu - 1
```
-/

/-- The code units of a single well-formed sequence in UTF-16: one unit
    outside D800..DFFF, or a high surrogate then a low surrogate. -/
def Utf.Spec.WellFormedChar16 : List UInt16 → Prop
  | [w] => w.toNat ≤ 0xD7FF ∨ 0xE000 ≤ w.toNat
  | [w1, w2] => Utf.Spec.High w1 ∧ Utf.Spec.Low w2
  | _ => False

/-- A well-formed UTF-16 code unit sequence: well-formed sequences, one
    after another. -/
inductive Utf.Spec.WellFormed16 : List UInt16 → Prop where
  | nil : Utf.Spec.WellFormed16 []
  | cons {s rest : List UInt16} :
      Utf.Spec.WellFormedChar16 s → Utf.Spec.WellFormed16 rest → Utf.Spec.WellFormed16 (s ++ rest)

example : Utf.Spec.WellFormedChar16 [0xD800, 0xDF02] := by
  unfold Utf.Spec.WellFormedChar16 Utf.Spec.High Utf.Spec.Low; decide
example : ¬ Utf.Spec.WellFormedChar16 [0xDF02, 0xD800] := by
  unfold Utf.Spec.WellFormedChar16 Utf.Spec.High Utf.Spec.Low; decide
example : Utf.Spec.WellFormedChar16 [0xD7FF] ∧ Utf.Spec.WellFormedChar16 [0xE000] ∧
    ¬ Utf.Spec.WellFormedChar16 [0xD800] ∧ ¬ Utf.Spec.WellFormedChar16 [0xDFFF] := by
  unfold Utf.Spec.WellFormedChar16; decide

-- In <0041 D800 DC00 DC00>, the second low surrogate is isolated: the
-- unit before it is a low surrogate. The high surrogate is not: a low
-- surrogate follows it.
example : Utf.Spec.Unpaired [0x0041, 0xD800, 0xDC00] 0xDC00 [] := by
  refine Or.inr ⟨by unfold Utf.Spec.Low; decide, ?_⟩
  rintro ⟨l', v, h, hv⟩
  have : v = 0xDC00 := by
    have := congrArg List.getLast? h; simpa using this.symm
  subst this; unfold Utf.Spec.High at hv; revert hv; decide
example : ¬ Utf.Spec.Unpaired [0x0041] 0xD800 [0xDC00, 0xDC00] := by
  rintro (⟨-, h⟩ | ⟨hl, -⟩)
  · exact h ⟨0xDC00, [0xDC00], rfl, by unfold Utf.Spec.Low; decide⟩
  · unfold Utf.Spec.Low at hl; revert hl; decide

/-! ## The Unicode Standard, section 3.9.6, for UTF-16

D93a and D93b, as `Spec/Defs.lean` quotes them for UTF-8, over UTF-16
code units: at an unconvertible offset, the maximal subpart is replaced
by one U+FFFD, and conversion goes on after it.
-/

/-- `p` is the initial subsequence of a well-formed UTF-16 code unit
    sequence.

    As with `Utf.Spec.Initial`, that sequence may hold more than one
    character. Where this definition is used, that changes no answer.
    `Utf.Spec.MaximalSubpart16` asks it only of units at an unconvertible
    offset. By D93a, no well-formed sequence starts there, not even the
    units of one whole character. So `p` stops inside the units of the
    first character, which are at most two. That is, `p` is empty or one
    high surrogate. The proofs show that each maximal subpart is one
    unit, as `Utf16.Proofs.maximalSubpart_iff`, in
    `Utf/Proofs/Utf16/Lossy.lean`. -/
def Utf.Spec.Initial16 (p : List UInt16) : Prop :=
  ∃ s, Utf.Spec.WellFormed16 s ∧ p <+: s

/-- D93a: no subsequence starting at the front of `us` is well formed.
    (The empty one is left out: it starts nowhere.) -/
def Utf.Spec.Unconvertible16 (us : List UInt16) : Prop :=
  ∀ s, s ≠ [] → s <+: us → ¬ Utf.Spec.WellFormed16 s

/-- D93b: `p` is the maximal subpart at the front of `p ++ rest`. The
    front is an unconvertible offset, and `p` is the longest prefix
    there that is either the start of a well-formed sequence or one unit
    long. -/
def Utf.Spec.MaximalSubpart16 (p rest : List UInt16) : Prop :=
  p ≠ [] ∧ Utf.Spec.Unconvertible16 (p ++ rest) ∧
  (Utf.Spec.Initial16 p ∨ p.length = 1) ∧
  ∀ q, q <+: p ++ rest → (Utf.Spec.Initial16 q ∨ q.length = 1) → q.length ≤ p.length

/-- Conversion with U+FFFD substitution of maximal subparts: converting
    the units `us` gives `out`. Where a character's units start, it
    gives the character; at an unconvertible offset, the maximal subpart
    gives one U+FFFD; either way, conversion proceeds after the units
    used. -/
inductive Utf.Spec.Substitutes16 : List UInt16 → List Char → Prop where
  | nil : Utf.Spec.Substitutes16 [] []
  | char {c : Char} {rest : List UInt16} {out : List Char} :
      Utf.Spec.Substitutes16 rest out → Utf.Spec.Substitutes16 (Utf.Spec.encodeChar16 c ++ rest) (c :: out)
  | replace {p rest : List UInt16} {out : List Char} :
      Utf.Spec.MaximalSubpart16 p rest → Utf.Spec.Substitutes16 rest out →
      Utf.Spec.Substitutes16 (p ++ rest) ('�' :: out)

/-! ## The encoding schemes: RFC 2781, section 3.1, and D96 to D98

RFC 2781, section 3.1: "when written out to disk or to a network
interface (serializing), the high-order octet thus appears first in the
data stream" for big-endian, and the low-order octet first for
little-endian. Its C fragment for big-endian:

```
putc(u >> 8,   f);                     /* output high-order byte */
putc(u & 0xFF, f);                     /* then low-order */
```

RFC 2781, sections 4.1 and 4.2, add that in UTF-16BE "Finding 0xFF
followed by 0xFE is an error since there is no Unicode character
0xFFFE", and the same of FE FF in UTF-16LE. The Unicode Standard does
not: U+FFFE is a noncharacter, which D91 encodes like any other scalar
value. The definitions here follow the Unicode Standard, so such bytes
read as U+FFFE.

D98: "In the UTF-16 encoding scheme, an initial byte sequence
corresponding to U+FEFF is interpreted as a byte order mark [...]. An
initial byte sequence <FE FF> indicates big-endian order, and an initial
byte sequence <FF FE> indicates little-endian order. The BOM is not
considered part of the content of the text. [...] when there is no BOM,
and in the absence of a higher-level protocol, the byte order of the
UTF-16 encoding scheme is big-endian." RFC 2781, section 4.3, says the
same: with neither mark, the text "SHOULD be interpreted as being
big-endian". D96 and D97: in UTF-16BE and UTF-16LE, an initial U+FEFF
is the character ZERO WIDTH NO-BREAK SPACE.
-/

/-- The bytes of code units, big-endian. -/
def Utf.Spec.serializeBE (us : List UInt16) : List UInt8 :=
  (us.map fun (u : UInt16) => [(u >>> 8).toUInt8, (u &&& 0xFF).toUInt8]).flatten

/-- The bytes of code units, little-endian. -/
def Utf.Spec.serializeLE (us : List UInt16) : List UInt8 :=
  (us.map fun (u : UInt16) => [(u &&& 0xFF).toUInt8, (u >>> 8).toUInt8]).flatten

/-- D98, read: the bytes `bs`, in the UTF-16 encoding scheme, are the
    text `cs`. A byte order mark FE FF and the text big-endian; a mark
    FF FE and the text little-endian; or no mark, and the text
    big-endian. -/
def Utf.Spec.SchemeReads (bs : List UInt8) (cs : List Char) : Prop :=
  bs = [0xFE, 0xFF] ++ Utf.Spec.serializeBE (Utf.Spec.encode16 cs) ∨
  bs = [0xFF, 0xFE] ++ Utf.Spec.serializeLE (Utf.Spec.encode16 cs) ∨
  (bs.take 2 ≠ [0xFE, 0xFF] ∧ bs.take 2 ≠ [0xFF, 0xFE] ∧
    bs = Utf.Spec.serializeBE (Utf.Spec.encode16 cs))

-- D96, D97 and D98's examples, for <004D 0430 4E8C D800 DF02>.
example : Utf.Spec.serializeBE [0x004D, 0x0430, 0x4E8C, 0xD800, 0xDF02] =
    [0x00, 0x4D, 0x04, 0x30, 0x4E, 0x8C, 0xD8, 0x00, 0xDF, 0x02] := by decide +kernel
example : Utf.Spec.serializeLE [0x004D, 0x0430, 0x4E8C, 0xD800, 0xDF02] =
    [0x4D, 0x00, 0x30, 0x04, 0x8C, 0x4E, 0x00, 0xD8, 0x02, 0xDF] := by decide +kernel

-- D98's three serializations of it all read as its characters.
example : Utf.Spec.SchemeReads [0xFE, 0xFF, 0x00, 0x4D, 0x04, 0x30, 0x4E, 0x8C, 0xD8, 0x00, 0xDF, 0x02]
      ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    Utf.Spec.SchemeReads [0xFF, 0xFE, 0x4D, 0x00, 0x30, 0x04, 0x8C, 0x4E, 0x00, 0xD8, 0x02, 0xDF]
      ['M', '\u0430', '二', Char.ofNat 0x10302] ∧
    Utf.Spec.SchemeReads [0x00, 0x4D, 0x04, 0x30, 0x4E, 0x8C, 0xD8, 0x00, 0xDF, 0x02]
      ['M', '\u0430', '二', Char.ofNat 0x10302] := by
  unfold Utf.Spec.SchemeReads; decide +kernel
-- With a mark, the mark is not text; text that starts with U+FEFF and has
-- no mark cannot be told from text after a mark, and reads as the latter.
example : ¬ Utf.Spec.SchemeReads [0xFE, 0xFF, 0x00, 0x41] ['\uFEFF', 'A'] := by
  unfold Utf.Spec.SchemeReads; decide +kernel

/-! ## The WHATWG Encoding Standard, section 14.2.1, shared UTF-16 decoder

```
shared UTF-16 decoder has an associated:
  UTF-16 leading byte: Null or a byte, initially null.
  UTF-16 leading surrogate: Null or a leading surrogate, initially null.
  is UTF-16BE decoder: A boolean, initially false.

shared UTF-16 decoder's handler, given ioQueue and byte, runs these
steps:
 1. If byte is end-of-queue and either UTF-16 leading byte or UTF-16
    leading surrogate is non-null, then set UTF-16 leading byte and
    UTF-16 leading surrogate to null, and return error.
 2. If byte is end-of-queue and UTF-16 leading byte and UTF-16 leading
    surrogate are null, then return finished.
 3. If UTF-16 leading byte is null, then set UTF-16 leading byte to
    byte and return continue.
 4. Let codeUnit be the result of:
      is UTF-16BE decoder is true: (UTF-16 leading byte << 8) + byte.
      is UTF-16BE decoder is false: (byte << 8) + UTF-16 leading byte.
 5. Set UTF-16 leading byte to null.
 6. If UTF-16 leading surrogate is non-null:
    1. Let leadingSurrogate be UTF-16 leading surrogate.
    2. Set UTF-16 leading surrogate to null.
    3. If codeUnit is a trailing surrogate, then return a scalar value
       from surrogates given leadingSurrogate and codeUnit.
    4. Let byte1 be codeUnit >> 8.
    5. Let byte2 be codeUnit & 0x00FF.
    6. Let bytes be a list of two bytes whose values are byte1 and
       byte2, if is UTF-16BE decoder is true; otherwise byte2 and byte1.
    7. Restore bytes to ioQueue and return error.
 7. If codeUnit is a leading surrogate, then set UTF-16 leading
    surrogate to codeUnit and return continue.
 8. If codeUnit is a trailing surrogate, then return error.
 9. Return code point codeUnit.
```

To get a scalar value from surrogates, given a leading surrogate
`leading` and a trailing surrogate `trailing`, return `0x10000 +
((leading − 0xD800) << 10) + (trailing − 0xDC00)`. Decoding runs the
handler on each byte of the queue and then on end-of-queue; with the
error mode "replacement", each error gives U+FFFD (section 4.1,
"process a queue" and "process an item"; the `decode` algorithm of
section 6 uses that mode).

Below, `lead` is UTF-16 leading byte and `sur` is UTF-16 leading
surrogate, `none` for null. Each step takes a byte from the queue or,
at step 6.7, puts one back, so `fuel` of three steps for each byte, and
two for the end, is enough.
-/

/-- The shared UTF-16 decoder, run over the queue `q` from the state
    `lead`, `sur`, with error mode "replacement". -/
def Utf.Spec.whatwgRun (isBE : Bool) : Nat → Option UInt8 → Option Nat → List UInt8 → List Char
  | 0, _, _, _ => []
  | fuel + 1, lead, sur, [] =>
    -- Steps 1 and 2.
    if lead.isSome ∨ sur.isSome then '�' :: Utf.Spec.whatwgRun isBE fuel none none [] else []
  | fuel + 1, none, sur, byte :: q =>
    -- Step 3.
    Utf.Spec.whatwgRun isBE fuel (some byte) sur q
  | fuel + 1, some leadByte, sur, byte :: q =>
    -- Steps 4 and 5.
    let codeUnit : Nat :=
      if isBE then (leadByte.toNat <<< 8) + byte.toNat else (byte.toNat <<< 8) + leadByte.toNat
    match sur with
    | some leadingSurrogate =>
      -- Step 6.
      if 0xDC00 ≤ codeUnit ∧ codeUnit ≤ 0xDFFF then
        Char.ofNat (0x10000 + ((leadingSurrogate - 0xD800) <<< 10) + (codeUnit - 0xDC00)) ::
          Utf.Spec.whatwgRun isBE fuel none none q
      else
        let byte1 := (codeUnit >>> 8).toUInt8
        let byte2 := (codeUnit &&& 0x00FF).toUInt8
        let bytes := if isBE then [byte1, byte2] else [byte2, byte1]
        '�' :: Utf.Spec.whatwgRun isBE fuel none none (bytes ++ q)
    | none =>
      -- Steps 7 to 9.
      if 0xD800 ≤ codeUnit ∧ codeUnit ≤ 0xDBFF then Utf.Spec.whatwgRun isBE fuel none (some codeUnit) q
      else if 0xDC00 ≤ codeUnit ∧ codeUnit ≤ 0xDFFF then '�' :: Utf.Spec.whatwgRun isBE fuel none none q
      else Char.ofNat codeUnit :: Utf.Spec.whatwgRun isBE fuel none none q

/-- The WHATWG UTF-16BE (`isBE`) or UTF-16LE decoder over all of `bs`,
    from the initial state. -/
def Utf.Spec.whatwgDecode (isBE : Bool) (bs : List UInt8) : List Char :=
  Utf.Spec.whatwgRun isBE (3 * bs.length + 2) none none bs

-- Each step: a pair (6.3), a leading surrogate then a unit that is not
-- trailing (6.4 to 6.7, the unit read again), a trailing surrogate alone
-- (8), a plain unit (9), a byte left over (1), a leading surrogate left
-- over (1), and both left over, which give one error between them.
example : Utf.Spec.whatwgDecode true [0xD8, 0x3D, 0xDE, 0x00] = [Char.ofNat 0x1F600] ∧
    Utf.Spec.whatwgDecode true [0xD8, 0x00, 0x00, 0x41] = ['�', 'A'] ∧
    Utf.Spec.whatwgDecode true [0xD8, 0x00, 0xD8, 0x00, 0xDC, 0x00] = ['�', Char.ofNat 0x10000] ∧
    Utf.Spec.whatwgDecode false [0x00, 0xDC, 0x41, 0x00] = ['�', 'A'] ∧
    Utf.Spec.whatwgDecode false [0x41, 0x00] = ['A'] ∧
    Utf.Spec.whatwgDecode false [0x41, 0x00, 0x42] = ['A', '�'] ∧
    Utf.Spec.whatwgDecode true [0xD8, 0x00] = ['�'] ∧
    Utf.Spec.whatwgDecode false [0x00, 0xD8, 0x41] = ['�'] ∧
    Utf.Spec.whatwgDecode true [0xFE, 0xFF, 0x00, 0x41] = ['\uFEFF', 'A'] := by
  decide +kernel

/-! ## ECMAScript, `String.prototype.toWellFormed`

Set out in words here, not quoted: ECMAScript 2024 adds `toWellFormed`,
which returns the string with each
code unit that `CodePointAt` reports as an unpaired surrogate replaced
by 0xFFFD, and every other code unit kept. `CodePointAt` reports the
unit at a position as an unpaired surrogate when it is a trailing
surrogate, or a leading surrogate that no trailing surrogate follows.
Read from the left, a trailing surrogate right after a leading one is
taken with it as a pair, so a trailing surrogate is reported unpaired
exactly when no leading surrogate comes right before it: that is
`Utf.Spec.Unpaired`. The statement in `Utf/Spec.lean` says it unit by unit.
-/
