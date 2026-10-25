/-
  UTF-8: Unicode scalar values (Lean's `Char`) to bytes and back.
-/

namespace Utf8

/-! ## Encoding -/

/-- The bytes of one character: one to four, by the range its code
    point falls in. Each continuation byte carries six bits, most
    significant first. -/
def encodeChar (c : Char) : List UInt8 :=
  let n := c.toNat
  if n < 0x80 then [n.toUInt8]
  else if n < 0x800 then
    [(0xC0 + n / 0x40).toUInt8, (0x80 + n % 0x40).toUInt8]
  else if n < 0x10000 then
    [(0xE0 + n / 0x1000).toUInt8, (0x80 + n / 0x40 % 0x40).toUInt8, (0x80 + n % 0x40).toUInt8]
  else
    [(0xF0 + n / 0x40000).toUInt8, (0x80 + n / 0x1000 % 0x40).toUInt8,
     (0x80 + n / 0x40 % 0x40).toUInt8, (0x80 + n % 0x40).toUInt8]

/-- The bytes of a list of characters, one after another. -/
def encode (cs : List Char) : List UInt8 :=
  cs.flatMap encodeChar

/-! ## Decoding -/

/-- The six low bits of a continuation byte, 0x80 to 0xBF. -/
def tail (b : UInt8) : Option Nat :=
  if 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF then some (b.toNat - 0x80) else none

/-- Reads one character from the front of the input: the character, and
    the bytes after it. The lead byte gives the length; the value the
    bytes make must need that length (no overlong forms), must not be a
    surrogate (0xD800 to 0xDFFF), and must not pass 0x10FFFF. -/
def decodeChar : List UInt8 → Option (Char × List UInt8)
  | [] => none
  | b0 :: rest =>
    let x := b0.toNat
    if x < 0x80 then some (Char.ofNat x, rest)
    else if x < 0xC2 then none
    else if x < 0xE0 then
      match rest with
      | b1 :: rest =>
        match tail b1 with
        | some t1 => some (Char.ofNat ((x - 0xC0) * 0x40 + t1), rest)
        | none => none
      | [] => none
    else if x < 0xF0 then
      match rest with
      | b1 :: b2 :: rest =>
        match tail b1, tail b2 with
        | some t1, some t2 =>
          let n := (x - 0xE0) * 0x1000 + t1 * 0x40 + t2
          if n < 0x800 ∨ (0xD800 ≤ n ∧ n ≤ 0xDFFF) then none else some (Char.ofNat n, rest)
        | _, _ => none
      | _ => none
    else if x < 0xF5 then
      match rest with
      | b1 :: b2 :: b3 :: rest =>
        match tail b1, tail b2, tail b3 with
        | some t1, some t2, some t3 =>
          let n := (x - 0xF0) * 0x40000 + t1 * 0x1000 + t2 * 0x40 + t3
          if n < 0x10000 ∨ 0x10FFFF < n then none else some (Char.ofNat n, rest)
        | _, _, _ => none
      | _ => none
    else none

/-- Reads characters until the input ends. Each character takes at
    least one byte, so `fuel` equal to the input's length is enough. -/
def decodeAux : Nat → List UInt8 → Option (List Char)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, b :: bs =>
    match decodeChar (b :: bs) with
    | some (c, rest) =>
      match decodeAux fuel rest with
      | some cs => some (c :: cs)
      | none => none
    | none => none

/-- Reads bytes as UTF-8. Fails on anything that is not the encoding of
    a list of characters; it never skips or replaces a bad byte. -/
def decode (bs : List UInt8) : Option (List Char) :=
  decodeAux bs.length bs

end Utf8
