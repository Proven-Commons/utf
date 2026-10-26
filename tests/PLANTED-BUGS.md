# Planted bugs

Written by `python3 tests/planted_bugs.py`. Each row is one small change to the
code under proof, made in a copy. The tests ran with `--count 20000`: their fixed
sets, then 20,000 random inputs from their recorded seed, against the changed
tool. A bug is caught when they report failures. The last column says whether
`lake build Proofs` still succeeds with the change.

| Bug | File | Failures | Proofs |
|-----|------|----------|--------|
| Three-byte overlong forms read | `Utf8/Codec.lean` | 2308 | fail to build |
| Surrogates read | `Utf8/Codec.lean` | 2721 | fail to build |
| Values past U+10FFFF read | `Utf8/Codec.lean` | 417 | fail to build |
| Leads 0xC0 and 0xC1 read | `Utf8/Codec.lean` | 336 | fail to build |
| 0xC0 read as a continuation byte | `Utf8/Codec.lean` | 4602 | fail to build |
| U+0800 written in two bytes | `Utf8/Codec.lean` | 250 | fail to build |
| Leads 0xF5 to 0xF7 start four-byte sequences | `Utf8/Codec.lean` | 0, equivalent: with a lead of 0xF5 to 0xF7 the value is at least 5 * 0x40000 = 0x140000, past 0x10FFFF, so the four-byte branch refuses it. `decodeChar` gives `none` on the same inputs as before, and the encoder is unchanged. | fail to build |

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
