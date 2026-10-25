# Cross-check with other decoders

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- Seed: 20261025
- Byte strings: 2358229, of which 148759 this project accepts

| Decoder | Differences from this project |
| --- | --- |
| Go `utf8.Valid` (go version go1.24.7 linux/amd64) | 0 |
| Rust `String::from_utf8` (rustc 1.97.0 (2d8144b78 2026-07-07)) | 0 |
| Node `TextDecoder`, fatal (v22.22.0) | 0 |

