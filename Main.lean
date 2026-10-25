/-
  Command line front end, used by the differential tests.

    utf8 serve

  answers requests on standard input, one per line:

    decode HEX      prints  OK: and the code points read, in lower case
                    hex, separated by commas; or REJECT
    core HEX        prints  the same answer from Lean core's
                    `String.fromUTF8?`, for comparison
    encode POINTS   prints  the hex of the encoding, or INVALID when a
                    code point is not a Unicode scalar value

  HEX is the bytes in lower case hex, empty for no bytes. POINTS is code
  points in lower case hex, of at most 8 digits, separated by commas, or
  `-` for none.

  A malformed request prints `error`: an unknown operation, hex that is
  not lower case or not in pairs, or a code point that does not parse. A
  request line may end in LF or CR LF. Each answer is flushed as soon as
  it is written.

  `decode` and `encode` come from the proved functions in `Utf8/`. `core`
  is there only so the tests can compare Lean core's compiled check with
  them. The parsing and printing here are covered by the tests, not by a
  proof.
-/

import Utf8

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

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '?'

def showHex (bs : List UInt8) : String :=
  String.ofList (bs.flatMap fun b => [hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)])

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
  | ["core", h] => do
    let bs ← hexBytes h.toList
    pure (showDecoded ((String.fromUTF8? bs.toByteArray).map String.toList))
  | ["encode", "-"] => pure (showHex (Utf8.encode []))
  | ["encode", points] => do
    let ns ← (points.splitOn ",").mapM hexNumber
    pure <| if ns.all Nat.isValidChar then showHex (Utf8.encode (ns.map Char.ofNat))
      else "INVALID"
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
