/-
  UTF-16: Unicode scalar values (Lean's `Char`) to 16-bit code units and
  back. A character below U+10000 is one unit with its own value; any
  other is a surrogate pair. `decode` refuses any unpaired surrogate;
  `decodeLossy` puts U+FFFD in place of each one.
-/

namespace Utf16

/-- A high surrogate, 0xD800 to 0xDBFF: the first unit of a pair. -/
def isHigh (u : UInt16) : Bool := 0xD800 ≤ u.toNat && u.toNat ≤ 0xDBFF

/-- A low surrogate, 0xDC00 to 0xDFFF: the second unit of a pair. -/
def isLow (u : UInt16) : Bool := 0xDC00 ≤ u.toNat && u.toNat ≤ 0xDFFF

/-! ## Encoding -/

/-- The units of one character: its own value below U+10000; above,
    a pair that carries the code point less 0x10000, ten bits in
    each. -/
def encodeChar (c : Char) : List UInt16 :=
  let n := c.toNat
  if n < 0x10000 then [n.toUInt16]
  else
    let m := n - 0x10000
    [(0xD800 + m / 0x400).toUInt16, (0xDC00 + m % 0x400).toUInt16]

/-- The units of a list of characters, one after another. -/
def encode (cs : List Char) : List UInt16 :=
  cs.flatMap encodeChar

/-! ## Decoding -/

/-- The character a high and a low surrogate stand for together. -/
def pair (hi lo : UInt16) : Char :=
  Char.ofNat (0x10000 + (hi.toNat - 0xD800) * 0x400 + (lo.toNat - 0xDC00))

/-- Reads units as UTF-16. Fails on a high surrogate that no low
    surrogate follows, and on a low surrogate that no high surrogate
    comes before; it never skips or replaces a unit. -/
def decode : List UInt16 → Option (List Char)
  | [] => some []
  | u :: rest =>
    if isHigh u then
      match rest with
      | v :: rest' => if isLow v then (decode rest').map (pair u v :: ·) else none
      | [] => none
    else if isLow u then none
    else (decode rest).map (Char.ofNat u.toNat :: ·)

/-- The replacement character, U+FFFD. -/
def replacement : Char := '�'

/-- Reads units as UTF-16, putting U+FFFD in place of each unpaired
    surrogate. It never fails. -/
def decodeLossy : List UInt16 → List Char
  | [] => []
  | u :: rest =>
    if isHigh u then
      match rest with
      | v :: rest' =>
        if isLow v then pair u v :: decodeLossy rest' else replacement :: decodeLossy (v :: rest')
      | [] => [replacement]
    else if isLow u then replacement :: decodeLossy rest
    else Char.ofNat u.toNat :: decodeLossy rest

/-- The units with each unpaired surrogate replaced by 0xFFFD, as
    JavaScript's `String.prototype.toWellFormed` gives. -/
def toWellFormed (us : List UInt16) : List UInt16 :=
  encode (decodeLossy us)

end Utf16
