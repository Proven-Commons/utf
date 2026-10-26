# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `utf-8`, `utf-16-be` and `utf-16-le` codecs, strict and with the `replace` error handler, and its `utf-16` codec for text with a byte order mark; for `toWellFormed`, ECMAScript's `CodePointAt`, written in tests/run_tests.py
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 2818530
- Requests: 8714292, each decoded byte string also sent as `core` and as `lossy`; each list of UTF-16 units as `dec16`, `lossy16` and `wf16`; each UTF-16 byte string to `decbe`, `decle`, `decutf16`, `lossybe` and `lossyle`; each list of code points for UTF-16 to `enc16`, `encbe` and `encle`
- Mutated: 269430 of the inputs are mutated encodings
- By kind: bytes grid 66792, bytes grid (decle) 66792, bytes grid (decutf16) 66792, bytes grid (lossybe) 66792, bytes grid (lossyle) 66792, bytes mutated 97444, bytes mutated (decle) 97444, bytes mutated (decutf16) 97444, bytes mutated (lossybe) 97444, bytes mutated (lossyle) 97444, bytes valid 22616, bytes valid (decle) 22616, bytes valid (decutf16) 22616, bytes valid (lossybe) 22616, bytes valid (lossyle) 22616, enc16 22457, enc16 (encbe) 22457, enc16 (encle) 22457, enc16 invalid 7483, enc16 invalid (encbe) 7483, enc16 invalid (encle) 7483, encode 45333, encode invalid 12136, error 32, grid 2220288, grid (core) 2220288, grid (lossy) 2220288, kuhn 77, kuhn (core) 77, kuhn (lossy) 77, mutated 74542, mutated (core) 74542, mutated (lossy) 74542, random 17989, random (core) 17989, random (lossy) 17989, utf16 grid 65948, utf16 grid (lossy16) 65948, utf16 grid (wf16) 65948, utf16 mutated 97444, utf16 mutated (lossy16) 97444, utf16 mutated (wf16) 97444, utf16 valid 22616, utf16 valid (lossy16) 22616, utf16 valid (wf16) 22616, valid 45333, valid (core) 45333, valid (lossy) 45333
- Byte strings decoded: 2358229, of which 148759 well formed and 2209470 refused
- The same byte strings given to Lean core's `String.fromUTF8?`, agreeing with Python: 2358229 of 2358229
- The same byte strings given to the lossy decoder, agreeing with Python's `replace` handler: 2358229 of 2358229, of which 2212132 have a U+FFFD in the answer
- UTF-16 unit lists decoded: 186008, of which 134596 well formed and 51412 refused; the lossy decoder agreeing with Python's `replace` handler on 186008 of 186008; `toWellFormed` agreeing with ECMAScript's rule on 186008 of 186008
- UTF-16 byte strings: 186852, of which 19180 of odd length; the lossy byte decoders agreeing with Python's `replace` handler on 373704 of 373704
- Byte strings with no byte order mark that Python's own `utf-16` codec, reading them little-endian, would read differently from RFC 2781's big-endian rule: 130714
- Code point lists given to the UTF-16 encoders: 29940
- Malformed requests answered `error`: 32 of 32
- Requests ending in CR LF: every seventh, 1244898
- Last lines sent alone, with no LF or with CR LF, answered right: 6 of 6
- Failures: 0
