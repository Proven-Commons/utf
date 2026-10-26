/-
  UTF-16 as bytes: the encoding schemes UTF-16BE and UTF-16LE, the
  UTF-16 encoding scheme with its byte order mark, and the WHATWG
  Encoding Standard's lossy decoders for UTF-16BE and UTF-16LE.
-/

import Utf16.Codec

namespace Utf16

/-- The bytes of the units, each unit's high byte first. -/
def bytesBE (us : List UInt16) : List UInt8 :=
  us.flatMap fun u => [(u.toNat / 0x100).toUInt8, (u.toNat % 0x100).toUInt8]

/-- The bytes of the units, each unit's low byte first. -/
def bytesLE (us : List UInt16) : List UInt8 :=
  us.flatMap fun u => [(u.toNat % 0x100).toUInt8, (u.toNat / 0x100).toUInt8]

/-- The unit of a high and a low byte. -/
def unit (hi lo : UInt8) : UInt16 := (hi.toNat * 0x100 + lo.toNat).toUInt16

/-- The bytes read two at a time as units, the high byte first when
    `be` holds; and the last byte, when the count is odd. -/
def units (be : Bool) : List UInt8 → List UInt16 × Option UInt8
  | [] => ([], none)
  | [b] => ([], some b)
  | a :: b :: rest =>
    let (us, last) := units be rest
    ((if be then unit a b else unit b a) :: us, last)

/-- UTF-16BE: the characters, each unit's high byte first. -/
def encodeBE (cs : List Char) : List UInt8 := bytesBE (encode cs)

/-- UTF-16LE: the characters, each unit's low byte first. -/
def encodeLE (cs : List Char) : List UInt8 := bytesLE (encode cs)

/-- Reads bytes as UTF-16 in one byte order. Fails on an odd number of
    bytes, and wherever `decode` fails. -/
def decodeBytes (be : Bool) (bs : List UInt8) : Option (List Char) :=
  match units be bs with
  | (us, none) => decode us
  | (_, some _) => none

/-- UTF-16BE. A leading FE FF is U+FEFF, not a byte order mark. -/
def decodeBE (bs : List UInt8) : Option (List Char) := decodeBytes true bs

/-- UTF-16LE. A leading FF FE is U+FEFF, not a byte order mark. -/
def decodeLE (bs : List UInt8) : Option (List Char) := decodeBytes false bs

/-- The UTF-16 encoding scheme: a leading FE FF is a byte order mark
    for big-endian, FF FE for little-endian, and neither is part of the
    text; with no mark, the text is big-endian. -/
def decodeScheme : List UInt8 → Option (List Char)
  | a :: b :: rest =>
    if a = 0xFE ∧ b = 0xFF then decodeBE rest
    else if a = 0xFF ∧ b = 0xFE then decodeLE rest
    else decodeBE (a :: b :: rest)
  | bs => decodeBE bs

/-- Reads bytes as UTF-16 in one byte order, never failing: U+FFFD in
    place of each unpaired surrogate, and one U+FFFD at the end for a
    last byte left over, unless the units end in a high surrogate,
    whose U+FFFD stands for both. -/
def decodeLossyBytes (be : Bool) (bs : List UInt8) : List Char :=
  match units be bs with
  | (us, none) => decodeLossy us
  | (us, some _) =>
    if us.getLast?.any isHigh then decodeLossy us else decodeLossy us ++ [replacement]

/-- The lossy UTF-16BE decoder. -/
def decodeLossyBE (bs : List UInt8) : List Char := decodeLossyBytes true bs

/-- The lossy UTF-16LE decoder. -/
def decodeLossyLE (bs : List UInt8) : List Char := decodeLossyBytes false bs

end Utf16
