#!/usr/bin/env python3
"""Plant each bug below in a copy of the code, and check the tests catch it.

A planted bug is a small change to the code under proof, of a kind a
person could make by mistake. For each one, this script copies the
project into a temporary directory, makes the change there, builds the
command-line tool, and runs the differential tests with a given number
of random inputs after their fixed sets. The tests catch the bug when
they report failures.

It then builds the proofs against the changed code and records whether
they still build. A change that breaks the proofs stops a full
`lake build`, so the tests here run against the tool built on its own,
as `tests/run_tests.py` builds it.

The project itself is never changed. The script writes the results to
tests/PLANTED-BUGS.md, and exits with 1 if a bug is not caught and is
not marked as equivalent. An equivalent change gives the same answer on
every input, so no test can catch it; its entry says why.

Usage: python3 tests/planted_bugs.py [--count N]
"""

import argparse
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = "utf8"  # the lake target of the command-line tool
COUNT = 20_000

# (name, file, text to replace, replacement, why it is equivalent or None)
BUGS = [
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
]


def failures(out):
    m = re.search(r"(\d+) failures?", out)
    return int(m.group(1)) if m else None


def run(count):
    rows = []
    with tempfile.TemporaryDirectory() as tmp:
        work = Path(tmp) / "project"
        shutil.copytree(ROOT, work, ignore=shutil.ignore_patterns(".git"))
        for name, rel, old, new, equivalent in BUGS:
            path = work / rel
            original = (ROOT / rel).read_text()
            if original.count(old) != 1:
                sys.exit(f"{name}: the text to replace is not in {rel} exactly once")
            path.write_text(original.replace(old, new))
            build = subprocess.run(["lake", "build", EXE], cwd=work, capture_output=True, text=True)
            if build.returncode != 0:
                path.write_text(original)
                sys.exit(f"{name}: the tool does not build with this change\n{build.stdout[-2000:]}")
            test = subprocess.run([sys.executable, "tests/run_tests.py", "--count", str(count)],
                                  cwd=work, capture_output=True, text=True)
            proofs = subprocess.run(["lake", "build", "Proofs"], cwd=work, capture_output=True,
                                    text=True)
            path.write_text(original)
            n = failures(test.stdout + test.stderr)
            broke = proofs.returncode != 0
            rows.append((name, rel, old, new, equivalent, n, broke))
            print(f"{name}: {n} failures; proofs {'fail to build' if broke else 'build'}",
                  flush=True)
    return rows


def write(rows, count):
    lines = [
        "# Planted bugs",
        "",
        "Written by `python3 tests/planted_bugs.py`. Each row is one small change to the",
        f"code under proof, made in a copy. The tests ran with `--count {count}`: their fixed",
        f"sets, then {count:,} random inputs from their recorded seed, against the changed",
        "tool. A bug is caught when they report failures. The last column says whether",
        "`lake build Proofs` still succeeds with the change.",
        "",
        "| Bug | File | Failures | Proofs |",
        "|-----|------|----------|--------|",
    ]
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
    rows = run(args.count)
    write(rows, args.count)
    missed = [r[0] for r in rows if not r[5] and not r[4]]
    caught = sum(1 for r in rows if r[5])
    print(f"{caught} of {len(rows)} planted bugs caught; results in tests/PLANTED-BUGS.md")
    if missed:
        sys.exit("not caught: " + ", ".join(missed))


if __name__ == "__main__":
    main()
