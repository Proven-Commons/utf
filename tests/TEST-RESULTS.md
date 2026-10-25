# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Oracle: Python 3.13.17 `utf-8` codec, strict and with the `replace` error handler
- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Seed: 20261025
- Inputs: 2415715
- Requests: 7132173, each decoded byte string also sent as `core` and as `lossy`
- Mutated: 74542 of the inputs are mutated encodings
- By kind: encode 45333, encode invalid 12136, error 17, grid 2220288, grid (core) 2220288, grid (lossy) 2220288, kuhn 77, kuhn (core) 77, kuhn (lossy) 77, mutated 74542, mutated (core) 74542, mutated (lossy) 74542, random 17989, random (core) 17989, random (lossy) 17989, valid 45333, valid (core) 45333, valid (lossy) 45333
- Byte strings decoded: 2358229, of which 148759 well formed and 2209470 refused
- The same byte strings given to Lean core's `String.fromUTF8?`, agreeing with Python: 2358229 of 2358229
- The same byte strings given to the lossy decoder, agreeing with Python's `replace` handler: 2358229 of 2358229, of which 2212132 have a U+FFFD in the answer
- Malformed requests answered `error`: 17 of 17
- Requests ending in CR LF: every seventh, 1018881
- Last lines sent alone, with no LF or with CR LF, answered right: 4 of 4
- Failures: 0
