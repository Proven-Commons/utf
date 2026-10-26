/-
  Lossy UTF-8 decoding: bad bytes become U+FFFD instead of failing the
  whole input.
-/

import Utf8.Codec

namespace Utf8

/-- The replacement character, U+FFFD. -/
def replacement : Char := '�'

/-- `b` is a continuation byte, 0x80 to 0xBF. -/
def isCont (b : UInt8) : Bool := 0x80 ≤ b.toNat && b.toNat ≤ 0xBF

/-- After lead byte `x` of a sequence of three or four bytes, whether
    `b` may come second. Most leads take any continuation byte; four
    narrow the range, to keep out overlong forms (E0, F0), surrogates
    (ED) and values past U+10FFFF (F4). -/
def secondOK (x : Nat) (b : UInt8) : Bool :=
  let y := b.toNat
  if x = 0xE0 then 0xA0 ≤ y && y ≤ 0xBF
  else if x = 0xED then 0x80 ≤ y && y ≤ 0x9F
  else if x = 0xF0 then 0x90 ≤ y && y ≤ 0xBF
  else if x = 0xF4 then 0x80 ≤ y && y ≤ 0x8F
  else 0x80 ≤ y && y ≤ 0xBF

/-- Where no character can be read at the front of `b0 :: rest`, the
    number of bytes to replace: the lead byte, and the bytes after it
    that could still begin a well-formed sequence with it. One for a
    byte that never leads (0x80 to 0xC1, 0xF5 to 0xFF). -/
def badLength (b0 : UInt8) (rest : List UInt8) : Nat :=
  let x := b0.toNat
  if 0xE0 ≤ x ∧ x ≤ 0xF4 then
    match rest with
    | b1 :: b2 :: _ =>
      if secondOK x b1 then (if 0xF0 ≤ x ∧ isCont b2 then 3 else 2) else 1
    | [b1] => if secondOK x b1 then 2 else 1
    | [] => 1
  else 1

/-- One step: the character at the front of `b0 :: rest` and the bytes
    after it, or U+FFFD and the bytes after the bad ones. -/
def lossyStep (b0 : UInt8) (rest : List UInt8) : Char × List UInt8 :=
  match decodeChar (b0 :: rest) with
  | some (c, rest') => (c, rest')
  | none => (replacement, (b0 :: rest).drop (badLength b0 rest))

/-- Reads characters until the input ends. Each step takes at least one
    byte, so `fuel` equal to the input's length is enough. -/
def decodeLossyAux : Nat → List UInt8 → List Char
  | _, [] => []
  | 0, _ :: _ => []
  | fuel + 1, b :: bs =>
    let (c, rest) := lossyStep b bs
    c :: decodeLossyAux fuel rest

/-- Reads bytes as UTF-8, putting U+FFFD in place of each maximal
    subpart of an ill-formed sequence, as section 3.9.6 of the Unicode
    Standard sets out. It never fails. -/
def decodeLossy (bs : List UInt8) : List Char :=
  decodeLossyAux bs.length bs

end Utf8
