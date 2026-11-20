/-
  A helper for the proofs about lossy decoding: `prefixB q` says the
  bytes `q` begin the encoding of one character (or are all of it). It
  reads Table 3-7 row by row, as the code's `secondOK` and `isCont` do.
-/

import Utf8
import Utf.Spec.Defs

namespace Utf8.Proofs.Lossy

open Utf8

/-- `q` is a prefix of the bytes of one character. -/
def prefixB : List UInt8 → Bool
  | [] => true
  | [b0] => b0.toNat ≤ 0x7F || (0xC2 ≤ b0.toNat && b0.toNat ≤ 0xF4)
  | [b0, b1] =>
    (0xC2 ≤ b0.toNat && b0.toNat ≤ 0xDF && isCont b1) ||
    (0xE0 ≤ b0.toNat && b0.toNat ≤ 0xF4 && secondOK b0.toNat b1)
  | [b0, b1, b2] => 0xE0 ≤ b0.toNat && b0.toNat ≤ 0xF4 && secondOK b0.toNat b1 && isCont b2
  | [b0, b1, b2, b3] =>
    0xF0 ≤ b0.toNat && b0.toNat ≤ 0xF4 && secondOK b0.toNat b1 && isCont b2 && isCont b3
  | _ :: _ :: _ :: _ :: _ :: _ => false

/-- The bytes `E` do not start with a continuation byte. -/
def NoContHead (E : List UInt8) : Prop := ∀ b E', E = b :: E' → isCont b = false

end Utf8.Proofs.Lossy
