# Planted bugs

Written by `python3 tests/planted_bugs.py`. Each row is one small change to the
code under proof, made in a copy. Before any change, the copy's tool builds, the
tests report 0 failures, and `lake build Proofs` succeeds. With each change, the
tests ran as `python3 tests/run_tests.py --count 20000` runs them, on 2,415,209
inputs from their recorded seed, counted as `tests/TEST-RESULTS.md` counts them,
against the changed tool. A bug is caught when they report failures. The last
column says whether `lake build Proofs` still succeeds with the change.

| Bug | File | Failures | Proofs |
|-----|------|----------|--------|
| Three-byte overlong forms read | `Utf8/Codec.lean` | 4833 | fail to build |
| Surrogates read | `Utf8/Codec.lean` | 5902 | fail to build |
| Values past U+10FFFF read | `Utf8/Codec.lean` | 920 | fail to build |
| Leads 0xC0 and 0xC1 read | `Utf8/Codec.lean` | 37877 | fail to build |
| 0xC0 read as a continuation byte | `Utf8/Codec.lean` | 19175 | fail to build |
| U+0800 written in two bytes | `Utf8/Codec.lean` | 250 | fail to build |
| Leads 0xF5 to 0xF7 start four-byte sequences | `Utf8/Codec.lean` | 0, equivalent: with a lead of 0xF5 to 0xF7 the value is at least 5 * 0x40000 = 0x140000, past 0x10FFFF, so the four-byte branch refuses it. `decodeChar` gives `none` on the same inputs as before, and the encoder is unchanged. | fail to build |
| One U+FFFD for each bad byte | `Utf8/Lossy.lean` | 261672 | fail to build |
| Second byte after 0xE0 not narrowed | `Utf8/Lossy.lean` | 8854 | fail to build |
| Second byte after 0xED not narrowed | `Utf8/Lossy.lean` | 9526 | fail to build |
| Second byte after 0xF0 not narrowed | `Utf8/Lossy.lean` | 4731 | fail to build |
| Second byte after 0xF4 not narrowed | `Utf8/Lossy.lean` | 13595 | fail to build |
| Third byte of a cut-short four-byte sequence not counted | `Utf8/Lossy.lean` | 18788 | fail to build |
| Leads 0xF5 to 0xF7 take continuation bytes | `Utf8/Lossy.lean` | 54410 | fail to build |
| Leads 0xC2 to 0xDF and 0xF5 to 0xFF swallow the next byte | `Utf8/Lossy.lean` | 696466 | fail to build |
| A bad last byte given its own branch | `Utf8/Lossy.lean` | 0, equivalent: when `rest` is empty, `badLength b0 []` is 1 for every `b0`, so the old code also gives U+FFFD and drops the one byte, leaving nothing. `lossyStep` gives the same pair on every input. The change was meant to drop a lone lead byte at the end, but as written it gives the same answer. | fail to build |
| High surrogate range misses 0xDBFF | `Utf16/Codec.lean` | 3943 | fail to build |
| Low surrogate range misses 0xDC00 | `Utf16/Codec.lean` | 8679 | fail to build |
| U+10000 written as one unit | `Utf16/Codec.lean` | 969 | fail to build |
| Pair arithmetic off by one | `Utf16/Codec.lean` | 30786 | fail to build |
| Lone low surrogate accepted | `Utf16/Codec.lean` | 11129 | fail to build |
| High surrogate paired with any unit | `Utf16/Codec.lean` | 3569 | fail to build |
| Lossy decoding swallows the unit after a high surrogate | `Utf16/Codec.lean` | 7677 | fail to build |
| Lossy decoding drops a final high surrogate | `Utf16/Codec.lean` | 10627 | fail to build |
| Two U+FFFD for a high surrogate and an odd byte | `Utf16/Bytes.lean` | 764 | fail to build |
| Big-endian mark kept as text | `Utf16/Bytes.lean` | 998 | fail to build |
| Text with no mark read little-endian | `Utf16/Bytes.lean` | 73811 | fail to build |
| UTF-16LE written big-endian | `Utf16/Bytes.lean` | 2642 | fail to build |
| Odd byte ignored by the strict byte decoders | `Utf16/Bytes.lean` | 8192 | fail to build |
| Little-endian mark read big-endian | `Utf16/Bytes.lean` | 1441 | fail to build |

## The changes

**Three-byte overlong forms read** in `Utf8/Codec.lean`:

```
- if n < 0x800 ∨ (0xD800 ≤ n ∧ n ≤ 0xDFFF) then none
+ if (0xD800 ≤ n ∧ n ≤ 0xDFFF) then none
```

**Surrogates read** in `Utf8/Codec.lean`:

```
- if n < 0x800 ∨ (0xD800 ≤ n ∧ n ≤ 0xDFFF) then none
+ if n < 0x800 then none
```

**Values past U+10FFFF read** in `Utf8/Codec.lean`:

```
- if n < 0x10000 ∨ 0x10FFFF < n then none
+ if n < 0x10000 then none
```

**Leads 0xC0 and 0xC1 read** in `Utf8/Codec.lean`:

```
- else if x < 0xC2 then none
+ else if x < 0xC0 then none
```

**0xC0 read as a continuation byte** in `Utf8/Codec.lean`:

```
- if 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF then
+ if 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xC0 then
```

**U+0800 written in two bytes** in `Utf8/Codec.lean`:

```
-   else if n < 0x800 then
-     [(0xC0
+   else if n ≤ 0x800 then
+     [(0xC0
```

**Leads 0xF5 to 0xF7 start four-byte sequences** in `Utf8/Codec.lean`:

```
- else if x < 0xF5 then
+ else if x < 0xF8 then
```

**One U+FFFD for each bad byte** in `Utf8/Lossy.lean`:

```
- (b0 :: rest).drop (badLength b0 rest)
+ (b0 :: rest).drop 1
```

**Second byte after 0xE0 not narrowed** in `Utf8/Lossy.lean`:

```
- if x = 0xE0 then 0xA0 ≤ y
+ if x = 0xE0 then 0x80 ≤ y
```

**Second byte after 0xED not narrowed** in `Utf8/Lossy.lean`:

```
- else if x = 0xED then 0x80 ≤ y && y ≤ 0x9F
+ else if x = 0xED then 0x80 ≤ y && y ≤ 0xBF
```

**Second byte after 0xF0 not narrowed** in `Utf8/Lossy.lean`:

```
- else if x = 0xF0 then 0x90 ≤ y
+ else if x = 0xF0 then 0x80 ≤ y
```

**Second byte after 0xF4 not narrowed** in `Utf8/Lossy.lean`:

```
- else if x = 0xF4 then 0x80 ≤ y && y ≤ 0x8F
+ else if x = 0xF4 then 0x80 ≤ y && y ≤ 0xBF
```

**Third byte of a cut-short four-byte sequence not counted** in `Utf8/Lossy.lean`:

```
- then 3 else 2
+ then 2 else 2
```

**Leads 0xF5 to 0xF7 take continuation bytes** in `Utf8/Lossy.lean`:

```
- if 0xE0 ≤ x ∧ x ≤ 0xF4 then
+ if 0xE0 ≤ x ∧ x ≤ 0xF7 then
```

**Leads 0xC2 to 0xDF and 0xF5 to 0xFF swallow the next byte** in `Utf8/Lossy.lean`:

```
-   else 1
- 
- /-- One step
+   else if 0xC2 ≤ x ∧ rest ≠ [] then 2 else 1
+ 
+ /-- One step
```

**A bad last byte given its own branch** in `Utf8/Lossy.lean`:

```
- | none => (replacement, (b0 :: rest).drop (badLength b0 rest))
+ | none => (if rest = [] then (replacement, []) else (replacement, (b0 :: rest).drop (badLength b0 rest)))
```

**High surrogate range misses 0xDBFF** in `Utf16/Codec.lean`:

```
- u.toNat ≤ 0xDBFF
+ u.toNat < 0xDBFF
```

**Low surrogate range misses 0xDC00** in `Utf16/Codec.lean`:

```
- 0xDC00 ≤ u.toNat
+ 0xDC01 ≤ u.toNat
```

**U+10000 written as one unit** in `Utf16/Codec.lean`:

```
- if n < 0x10000 then [n.toUInt16]
+ if n ≤ 0x10000 then [n.toUInt16]
```

**Pair arithmetic off by one** in `Utf16/Codec.lean`:

```
- Char.ofNat (0x10000 + (hi.toNat
+ Char.ofNat (0xFFFF + (hi.toNat
```

**Lone low surrogate accepted** in `Utf16/Codec.lean`:

```
-     else if isLow u then none
+     else if false then none
```

**High surrogate paired with any unit** in `Utf16/Codec.lean`:

```
- if isLow v then (decode rest').map (pair u v :: ·) else none
+ (decode rest').map (pair u v :: ·)
```

**Lossy decoding swallows the unit after a high surrogate** in `Utf16/Codec.lean`:

```
- else replacement :: decodeLossy (v :: rest')
+ else replacement :: decodeLossy rest'
```

**Lossy decoding drops a final high surrogate** in `Utf16/Codec.lean`:

```
-       | [] => [replacement]
+       | [] => []
```

**Two U+FFFD for a high surrogate and an odd byte** in `Utf16/Bytes.lean`:

```
- if us.getLast?.any isHigh then decodeLossy us else decodeLossy us ++ [replacement]
+ decodeLossy us ++ [replacement]
```

**Big-endian mark kept as text** in `Utf16/Bytes.lean`:

```
- if a = 0xFE ∧ b = 0xFF then decodeBE rest
+ if a = 0xFE ∧ b = 0xFF then decodeBE (a :: b :: rest)
```

**Text with no mark read little-endian** in `Utf16/Bytes.lean`:

```
-     else decodeBE (a :: b :: rest)
+     else decodeLE (a :: b :: rest)
```

**UTF-16LE written big-endian** in `Utf16/Bytes.lean`:

```
- [(u.toNat % 0x100).toUInt8, (u.toNat / 0x100).toUInt8]
+ [(u.toNat / 0x100).toUInt8, (u.toNat % 0x100).toUInt8]
```

**Odd byte ignored by the strict byte decoders** in `Utf16/Bytes.lean`:

```
-   | (_, some _) => none
+   | (us, some _) => decode us
```

**Little-endian mark read big-endian** in `Utf16/Bytes.lean`:

```
-     else if a = 0xFF ∧ b = 0xFE then decodeLE rest
+     else if a = 0xFF ∧ b = 0xFE then decodeBE rest
```
