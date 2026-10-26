#!/usr/bin/env python3
"""Plant each bug below in a copy of the code, and check the tests catch it.

A planted bug is a small change to the code under proof, of a kind a
person could make by mistake. The script copies the project into a
temporary directory. There, before any change, it checks that the tool
builds, that the tests report 0 failures, and that the proofs build.
Then, for each bug, it makes the change, builds the command-line tool,
and runs the differential tests as `tests/run_tests.py --count N` runs
them. The tests catch the bug when they report failures.

A change that alters an answer of the code under proof also breaks the
proofs, since the code no longer meets its statements, and a full
`lake build` then fails. So the tests run against the tool built on its
own, as `tests/run_tests.py` builds it. After the tests, the script
builds the proofs against the changed code and records whether they
still build.

Apart from tests/PLANTED-BUGS.md, which it rewrites, the script never
changes the project; each bug is planted in the copy. It exits with 1
if a bug is not caught and is not marked as equivalent, and with an
error if a test run gives no clear result. An equivalent change gives
the same answer on every input, so no test can catch it; its entry says
why.

Usage: python3 tests/planted_bugs.py [--count N]
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
import textwrap
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = "utf8"  # the lake target of the command-line tool
COUNT = 20_000

# (name, file, text to replace, replacement, why it is equivalent or None)
BUGS = [
    # The strict UTF-8 codec.
    ("Three-byte overlong forms read", "Utf8/Codec.lean",
     "if n < 0x800 ∨ (0xD800 ≤ n ∧ n ≤ 0xDFFF) then none",
     "if (0xD800 ≤ n ∧ n ≤ 0xDFFF) then none", None),
    ("Surrogates read", "Utf8/Codec.lean",
     "if n < 0x800 ∨ (0xD800 ≤ n ∧ n ≤ 0xDFFF) then none",
     "if n < 0x800 then none", None),
    ("Values past U+10FFFF read", "Utf8/Codec.lean",
     "if n < 0x10000 ∨ 0x10FFFF < n then none",
     "if n < 0x10000 then none", None),
    ("Leads 0xC0 and 0xC1 read", "Utf8/Codec.lean",
     "else if x < 0xC2 then none",
     "else if x < 0xC0 then none", None),
    ("0xC0 read as a continuation byte", "Utf8/Codec.lean",
     "if 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xBF then",
     "if 0x80 ≤ b.toNat ∧ b.toNat ≤ 0xC0 then", None),
    ("U+0800 written in two bytes", "Utf8/Codec.lean",
     "  else if n < 0x800 then\n    [(0xC0",
     "  else if n ≤ 0x800 then\n    [(0xC0", None),
    ("Leads 0xF5 to 0xF7 start four-byte sequences", "Utf8/Codec.lean",
     "else if x < 0xF5 then",
     "else if x < 0xF8 then",
     "with a lead of 0xF5 to 0xF7 the value is at least 5 * 0x40000 = 0x140000, "
     "past 0x10FFFF, so the four-byte branch refuses it. `decodeChar` gives `none` "
     "on the same inputs as before, and the encoder is unchanged."),
    # The lossy UTF-8 decoder.
    ("One U+FFFD for each bad byte", "Utf8/Lossy.lean",
     "(b0 :: rest).drop (badLength b0 rest)",
     "(b0 :: rest).drop 1", None),
    ("Second byte after 0xE0 not narrowed", "Utf8/Lossy.lean",
     "if x = 0xE0 then 0xA0 ≤ y",
     "if x = 0xE0 then 0x80 ≤ y", None),
    ("Second byte after 0xED not narrowed", "Utf8/Lossy.lean",
     "else if x = 0xED then 0x80 ≤ y && y ≤ 0x9F",
     "else if x = 0xED then 0x80 ≤ y && y ≤ 0xBF", None),
    ("Second byte after 0xF0 not narrowed", "Utf8/Lossy.lean",
     "else if x = 0xF0 then 0x90 ≤ y",
     "else if x = 0xF0 then 0x80 ≤ y", None),
    ("Second byte after 0xF4 not narrowed", "Utf8/Lossy.lean",
     "else if x = 0xF4 then 0x80 ≤ y && y ≤ 0x8F",
     "else if x = 0xF4 then 0x80 ≤ y && y ≤ 0xBF", None),
    ("Third byte of a cut-short four-byte sequence not counted", "Utf8/Lossy.lean",
     "then 3 else 2",
     "then 2 else 2", None),
    ("Leads 0xF5 to 0xF7 take continuation bytes", "Utf8/Lossy.lean",
     "if 0xE0 ≤ x ∧ x ≤ 0xF4 then",
     "if 0xE0 ≤ x ∧ x ≤ 0xF7 then", None),
    ("Leads 0xC2 to 0xDF and 0xF5 to 0xFF swallow the next byte", "Utf8/Lossy.lean",
     "  else 1\n\n/-- One step",
     "  else if 0xC2 ≤ x ∧ rest ≠ [] then 2 else 1\n\n/-- One step", None),
    ("A bad last byte given its own branch", "Utf8/Lossy.lean",
     "| none => (replacement, (b0 :: rest).drop (badLength b0 rest))",
     "| none => (if rest = [] then (replacement, []) else "
     "(replacement, (b0 :: rest).drop (badLength b0 rest)))",
     "when `rest` is empty, `badLength b0 []` is 1 for every `b0`, so the old code also "
     "gives U+FFFD and drops the one byte, leaving nothing. `lossyStep` gives the same "
     "pair on every input. The change was meant to drop a lone lead byte at the end, "
     "but as written it gives the same answer."),
    # UTF-16 code units.
    ("High surrogate range misses 0xDBFF", "Utf16/Codec.lean",
     "u.toNat ≤ 0xDBFF",
     "u.toNat < 0xDBFF", None),
    ("Low surrogate range misses 0xDC00", "Utf16/Codec.lean",
     "0xDC00 ≤ u.toNat",
     "0xDC01 ≤ u.toNat", None),
    ("U+10000 written as one unit", "Utf16/Codec.lean",
     "if n < 0x10000 then [n.toUInt16]",
     "if n ≤ 0x10000 then [n.toUInt16]", None),
    ("Pair arithmetic off by one", "Utf16/Codec.lean",
     "Char.ofNat (0x10000 + (hi.toNat",
     "Char.ofNat (0xFFFF + (hi.toNat", None),
    ("Lone low surrogate accepted", "Utf16/Codec.lean",
     "    else if isLow u then none",
     "    else if false then none", None),
    ("High surrogate paired with any unit", "Utf16/Codec.lean",
     "if isLow v then (decode rest').map (pair u v :: ·) else none",
     "(decode rest').map (pair u v :: ·)", None),
    ("Lossy decoding swallows the unit after a high surrogate", "Utf16/Codec.lean",
     "else replacement :: decodeLossy (v :: rest')",
     "else replacement :: decodeLossy rest'", None),
    ("Lossy decoding drops a final high surrogate", "Utf16/Codec.lean",
     "      | [] => [replacement]",
     "      | [] => []", None),
    # UTF-16 as bytes.
    ("Two U+FFFD for a high surrogate and an odd byte", "Utf16/Bytes.lean",
     "if us.getLast?.any isHigh then decodeLossy us else decodeLossy us ++ [replacement]",
     "decodeLossy us ++ [replacement]", None),
    ("Big-endian mark kept as text", "Utf16/Bytes.lean",
     "if a = 0xFE ∧ b = 0xFF then decodeBE rest",
     "if a = 0xFE ∧ b = 0xFF then decodeBE (a :: b :: rest)", None),
    ("Text with no mark read little-endian", "Utf16/Bytes.lean",
     "    else decodeBE (a :: b :: rest)",
     "    else decodeLE (a :: b :: rest)", None),
    ("UTF-16LE written big-endian", "Utf16/Bytes.lean",
     "[(u.toNat % 0x100).toUInt8, (u.toNat / 0x100).toUInt8]",
     "[(u.toNat / 0x100).toUInt8, (u.toNat % 0x100).toUInt8]", None),
    ("Odd byte ignored by the strict byte decoders", "Utf16/Bytes.lean",
     "  | (_, some _) => none",
     "  | (us, some _) => decode us", None),
    ("Little-endian mark read big-endian", "Utf16/Bytes.lean",
     "    else if a = 0xFF ∧ b = 0xFE then decodeLE rest",
     "    else if a = 0xFF ∧ b = 0xFE then decodeBE rest", None),
]


def failures(out):
    m = re.search(r"(\d+) failures?", out)
    return int(m.group(1)) if m else None


def build(work, target):
    return subprocess.run(["lake", "build", target], cwd=work, capture_output=True, text=True)


def test(work, name, count):
    """The number of failures the tests report in `work`. Exits when the
    run gives no failure count, or when its exit status disagrees with
    the count."""
    run = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count)],
                         cwd=work, capture_output=True, text=True)
    n = failures(run.stdout + run.stderr)
    if n is None:
        sys.exit(f"{name}: the tests gave no failure count\n{(run.stdout + run.stderr)[-2000:]}")
    if (run.returncode == 0) != (n == 0):
        sys.exit(f"{name}: the tests exited with {run.returncode} but report {n} failures\n"
                 f"{(run.stdout + run.stderr)[-2000:]}")
    return n


def run(count):
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "project"
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns(".git"))
        # The control: with no change, everything must pass.
        tool = build(work, EXE)
        if tool.returncode != 0:
            sys.exit(f"with no change, the tool does not build\n{tool.stdout[-2000:]}")
        if test(work, "with no change", count) != 0:
            sys.exit("with no change, the tests report failures")
        proofs = build(work, "Proofs")
        if proofs.returncode != 0:
            sys.exit(f"with no change, the proofs do not build\n{proofs.stdout[-2000:]}")
        m = re.search(r"^- Inputs: (\d+)$", (work / "tests" / "TEST-RESULTS.md").read_text(),
                      re.M)
        if not m:
            sys.exit("with no change, the test record gives no count of inputs")
        inputs = int(m.group(1))
        print(f"with no change: the tool builds, 0 failures on {inputs} inputs, the proofs build",
              flush=True)
        for name, rel, old, new, equivalent in BUGS:
            path = work / rel
            original = (ROOT / rel).read_text()
            if original.count(old) != 1:
                sys.exit(f"{name}: the text to replace is not in {rel} exactly once")
            path.write_text(original.replace(old, new))
            tool = build(work, EXE)
            if tool.returncode != 0:
                path.write_text(original)
                sys.exit(f"{name}: the tool does not build with this change\n{tool.stdout[-2000:]}")
            n = test(work, name, count)
            broke = build(work, "Proofs").returncode != 0
            path.write_text(original)
            rows.append((name, rel, old, new, equivalent, n, broke))
            print(f"{name}: {n} failures; proofs {'fail to build' if broke else 'build'}",
                  flush=True)
    return rows, inputs


def write(rows, count, inputs):
    intro = (
        "Written by `python3 tests/planted_bugs.py`. Each row is one small change to the "
        "code under proof, made in a copy. Before any change, the copy's tool builds, the "
        "tests report 0 failures, and `lake build Proofs` succeeds. With each change, the "
        f"tests ran as `python3 tests/run_tests.py --count {count}` runs them, on {inputs:,} "
        "inputs from their recorded seed, counted as `tests/TEST-RESULTS.md` counts them, "
        "against the changed tool. A bug is caught when they report failures. The last "
        "column says whether `lake build Proofs` still succeeds with the change."
    )
    lines = ["# Planted bugs", "", *textwrap.wrap(intro, 80), "",
             "| Bug | File | Failures | Proofs |",
             "|-----|------|----------|--------|"]
    for name, rel, _, _, equivalent, n, broke in rows:
        cell = str(n) if n else ("0, equivalent: " + equivalent if equivalent else "0, NOT CAUGHT")
        lines.append(f"| {name} | `{rel}` | {cell} | {'fail to build' if broke else 'build'} |")
    lines += ["", "## The changes", ""]
    for name, rel, old, new, _, _, _ in rows:
        lines += [f"**{name}** in `{rel}`:", "", "```", "- " + old.replace("\n", "\n- "),
                  "+ " + new.replace("\n", "\n+ "), "```", ""]
    (ROOT / "tests" / "PLANTED-BUGS.md").write_text("\n".join(lines))


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--count", type=int, default=COUNT)
    args = ap.parse_args()
    rows, inputs = run(args.count)
    write(rows, args.count, inputs)
    missed = [r[0] for r in rows if not r[5] and not r[4]]
    caught = sum(1 for r in rows if r[5])
    print(f"{caught} of {len(rows)} planted bugs caught; results in tests/PLANTED-BUGS.md")
    if missed:
        sys.exit("not caught: " + ", ".join(missed))


if __name__ == "__main__":
    main()
