/-
  Command line front end, used by the differential tests.

    utf8 serve

  answers requests on standard input, one per line:

    decode HEX      prints  OK: and the code points read, in lower case
                    hex, separated by commas; or REJECT
    core HEX        prints  the same answer from Lean core's
                    `String.fromUTF8?`, for comparison
    lossy HEX       prints  OK: and the code points the lossy decoder
                    reads, with fffd for each replacement
    encode POINTS   prints  the hex of the encoding, or INVALID when a
                    code point is not a Unicode scalar value

  and for UTF-16:

    enc16 POINTS    prints  the UTF-16 code units, or INVALID
    dec16 UNITS     prints  OK: and the code points the strict decoder
                    reads; or REJECT
    lossy16 UNITS   prints  OK: and the code points the lossy decoder
                    reads, with fffd for each replacement
    wf16 UNITS      prints  the units with each isolated surrogate
                    replaced by fffd (`toWellFormed`)
    encbe POINTS    prints  the hex of the UTF-16BE encoding, or INVALID
    encle POINTS    prints  the same for UTF-16LE
    decbe HEX       prints  OK: and the code points, or REJECT: UTF-16BE
    decle HEX       prints  the same for UTF-16LE
    decutf16 HEX    prints  the same for the UTF-16 encoding scheme, with
                    its byte order mark
    lossybe HEX     prints  OK: and the code points the lossy UTF-16BE
                    decoder reads
    lossyle HEX     prints  the same for UTF-16LE

  HEX is the bytes in lower case hex, empty for no bytes. UNITS is the
  UTF-16 code units in lower case hex, four digits each, empty for none.
  POINTS is code points in lower case hex, of at most 8 digits,
  separated by commas, or `-` for none.

  A malformed request prints `error`: an unknown operation, hex that is
  not lower case or not in pairs, units not in fours, or a code point
  that does not parse. A
  request line may end in LF or CR LF. Each answer is flushed as soon as
  it is written.

  `decode`, `lossy` and `encode` come from the proved functions in
  `Utf8/`, and the UTF-16 requests from those in `Utf16/`. `core` is there only so the tests can compare Lean core's
  compiled check with them. The parsing and printing here are covered by
  the tests, not by a proof.
-/

import Utf8
import Utf16

def hexValue (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def hexBytes : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexValue a
    let lo ← hexValue b
    let bs ← hexBytes rest
    pure ((hi * 16 + lo).toUInt8 :: bs)
  | [_] => none

/-- A number in lower case hex, of one to eight digits. -/
def hexNumber (s : String) : Option Nat := do
  let ds := s.toList
  if ds.isEmpty || ds.length > 8 then none
  let vs ← ds.mapM hexValue
  pure (vs.foldl (fun acc d => 16 * acc + d) 0)

/-- UTF-16 code units in lower case hex, four digits each. -/
def hexUnits : List Char → Option (List UInt16)
  | [] => some []
  | a :: b :: c :: d :: rest => do
    let vs ← [a, b, c, d].mapM hexValue
    let us ← hexUnits rest
    pure ((vs.foldl (fun acc v => 16 * acc + v) 0).toUInt16 :: us)
  | _ => none

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '?'

def showHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

def showUnits (us : List UInt16) : String :=
  String.ofList (us.flatMap fun u =>
    let n := u.toNat
    [hexDigit (n / 0x1000), hexDigit (n / 0x100 % 16), hexDigit (n / 16 % 16), hexDigit (n % 16)])

/-- The code points of a request, or `none` when one does not parse. -/
def points (s : String) : Option (List Nat) :=
  if s = "-" then some [] else (s.splitOn ",").mapM hexNumber

/-- The answer to an encoding request: the encoder's output, shown, or
    INVALID when a code point is not a scalar value. -/
def encodeWith (render : List Char → String) (s : String) : Option String := do
  let ns ← points s
  pure <| if ns.all Nat.isValidChar then render (ns.map Char.ofNat) else "INVALID"

def showPoint (c : Char) : String :=
  String.ofList (Nat.toDigits 16 c.toNat)

def showDecoded : Option (List Char) → String
  | some cs => "OK:" ++ ",".intercalate (cs.map showPoint)
  | none => "REJECT"

/-- The answer to one request line, or `none` when it is malformed. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | ["decode", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded (Utf8.decode bs))
  | ["lossy", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded (some (Utf8.decodeLossy bs)))
  | ["core", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded ((String.fromUTF8? bs.toByteArray).map String.toList))
  | ["encode", "-"] => pure (showHex (Utf8.encode []))
  | ["encode", points] => do
    let ns ← (points.splitOn ",").mapM hexNumber
    pure <| if ns.all Nat.isValidChar then showHex (Utf8.encode (ns.map Char.ofNat))
      else "INVALID"
  | ["enc16", ps] => encodeWith (fun cs => showUnits (Utf16.encode cs)) ps
  | ["dec16", h] => do
    let us ← hexUnits h.toList
    pure (showDecoded (Utf16.decode us))
  | ["lossy16", h] => do
    let us ← hexUnits h.toList
    pure (showDecoded (some (Utf16.decodeLossy us)))
  | ["wf16", h] => do
    let us ← hexUnits h.toList
    pure (showUnits (Utf16.toWellFormed us))
  | ["encbe", ps] => encodeWith (fun cs => showHex (Utf16.encodeBE cs)) ps
  | ["encle", ps] => encodeWith (fun cs => showHex (Utf16.encodeLE cs)) ps
  | ["decbe", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded (Utf16.decodeBE bs))
  | ["decle", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded (Utf16.decodeLE bs))
  | ["decutf16", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded (Utf16.decodeScheme bs))
  | ["lossybe", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded (some (Utf16.decodeLossyBE bs)))
  | ["lossyle", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded (some (Utf16.decodeLossyLE bs)))
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main (args : List String) : IO UInt32 := do
  match args with
  | ["serve"] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      stdout.putStrLn ((request (chomp line)).getD "error")
      stdout.flush
    return 0
  | _ =>
    IO.eprintln "usage: utf8 serve"
    return 2
