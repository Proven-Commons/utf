# Cross-check with other decoders

Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.

- Seed: 20261025
- Byte strings: 2358234, of which 148762 this project accepts

| Decoder | Differences from this project |
| --- | --- |
| Go `utf8.Valid` (go version go1.24.7 linux/amd64) | 0 |
| Rust `String::from_utf8` (rustc 1.97.0 (2d8144b78 2026-07-07)) | 0 |
| Node `TextDecoder`, fatal, `ignoreBOM` set (v22.22.0) | 0 |

## Lossy decoding

The same byte strings, given to the lossy decoder. 2209472 of its answers have a U+FFFD in place of bad bytes, one for each byte string this project refuses. 2212134 have a U+FFFD anywhere, which also counts well-formed input that holds a U+FFFD of its own, `EF BF BD`.

| Decoder | Differences from this project |
| --- | --- |
| Go, a `range` loop over the string (go version go1.24.7 linux/amd64) | 275301 |
| Rust `String::from_utf8_lossy` (rustc 1.97.0 (2d8144b78 2026-07-07)) | 0 |
| Node `TextDecoder`, not fatal, `ignoreBOM` set (v22.22.0) | 0 |

Go's `range` loop follows another policy, on purpose: the Go specification says that on an invalid UTF-8 sequence it gives U+FFFD and "will advance a single byte". So it gives one U+FFFD for each bad byte, and differs wherever a maximal subpart is longer than one byte.

- Go, a `range` loop over the string (go version go1.24.7 linux/amd64): `efbf`: this project `OK:fffd`, theirs `OK:fffd,fffd`
- Go, a `range` loop over the string (go version go1.24.7 linux/amd64): `c0e080f08080f8808080fc80808080dfefbff7bfbffbbfbfbffdbfbfbfbf`: this project `OK:fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd`, theirs `OK:fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd,fffd`
- Go, a `range` loop over the string (go version go1.24.7 linux/amd64): `e0a0`: this project `OK:fffd`, theirs `OK:fffd,fffd`
- Go, a `range` loop over the string (go version go1.24.7 linux/amd64): `e0a1`: this project `OK:fffd`, theirs `OK:fffd,fffd`
- Go, a `range` loop over the string (go version go1.24.7 linux/amd64): `e0a2`: this project `OK:fffd`, theirs `OK:fffd,fffd`
