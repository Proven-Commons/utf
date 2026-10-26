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

The same byte strings, given to the lossy decoder. Of the 2209472 that this project refuses, 2209472 have a lossy answer that holds a U+FFFD. Of the 148762 that it accepts, 2662 do, and 2662 of those byte strings hold `EF BF BD`, the bytes of U+FFFD.

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

## UTF-16

- Lists of code units: 186008, of which 134596 this project accepts
- Byte strings: 186852

| Operation | Other decoder | Differences from this project |
| --- | --- | --- |
| Units, strict | Rust `String::from_utf16` (rustc 1.97.0 (2d8144b78 2026-07-07)) | 0 |
| Units, strict | Node `isWellFormed` (v22.22.0) | 0 |
| Units, lossy | Rust `String::from_utf16_lossy` (rustc 1.97.0 (2d8144b78 2026-07-07)) | 0 |
| Units, lossy | Node `toWellFormed` (v22.22.0) | 0 |
| Units, lossy | Go `utf16.Decode` (go version go1.24.7 linux/amd64) | 0 |
| `toWellFormed`, as units | Node `toWellFormed` (v22.22.0) | 0 |
| UTF-16BE, strict | Node `TextDecoder`, fatal, `ignoreBOM` set (v22.22.0) | 0 |
| UTF-16LE, strict | Node `TextDecoder`, fatal, `ignoreBOM` set (v22.22.0) | 0 |
| UTF-16BE, lossy | Node `TextDecoder`, not fatal, `ignoreBOM` set (v22.22.0) | 0 |
| UTF-16LE, lossy | Node `TextDecoder`, not fatal, `ignoreBOM` set (v22.22.0) | 0 |

