#!/usr/bin/env python3
"""A one-off comparison of this decoder with three other strict ones.

Unlike tests/run_tests.py, this is not part of the verified bar and is
not run in CI. It needs Go, Rust and Node:

    python3 tests/cross_check.py [--seed N] [--count N]

The byte strings are the ones tests/run_tests.py decodes, from the same
seed. Each is given to this project's tool, to Go's `utf8.Valid`, to
Rust's `String::from_utf8`, and to Node's `TextDecoder` with `fatal`
set. Each must accept exactly what this decoder accepts and read the
same code points. The counts go to tests/CROSS-CHECK.md.
"""

import argparse
import subprocess
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
import run_tests  # noqa: E402

ROOT = run_tests.ROOT
REPORT = ROOT / "tests" / "CROSS-CHECK.md"
HELPERS = ROOT / "tests" / "cross_check"
BUILD = ROOT / ".lake" / "cross_check"


def version(cmd):
    out = subprocess.run(cmd, capture_output=True, text=True)
    return (out.stdout or out.stderr).strip().splitlines()[0]


def tools():
    BUILD.mkdir(parents=True, exist_ok=True)
    subprocess.run(["go", "build", "-o", str(BUILD / "go-utf8"), "main.go"], cwd=HELPERS,
                   check=True, env={**__import__("os").environ, "GO111MODULE": "off"})
    subprocess.run(["rustc", "-O", "-o", str(BUILD / "rust-utf8"), "main.rs"], cwd=HELPERS,
                   check=True)
    return {
        f"Go `utf8.Valid` ({version(['go', 'version'])})": [str(BUILD / "go-utf8")],
        f"Rust `String::from_utf8` ({version(['rustc', '--version'])})": [str(BUILD / "rust-utf8")],
        f"Node `TextDecoder`, fatal ({version(['node', '--version'])})":
            ["node", str(HELPERS / "main.js")],
    }


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--count", type=int, default=150_000)
    args = ap.parse_args()
    hexes = [req.split(" ", 1)[1] for label, req, _, _ in run_tests.cases(args.seed, args.count)
             if req.startswith("decode ") and label != "error"]
    ours, problem = run_tests.run_tool("".join(f"decode {h}\n" for h in hexes))
    if problem or len(ours) != len(hexes):
        sys.exit(f"the tool failed: {problem}")
    data = "".join(h + "\n" for h in hexes)
    lines = [
        "# Cross-check with other decoders",
        "",
        "Written by `tests/cross_check.py`, once, by hand. It is not part of the verified bar.",
        "",
        f"- Seed: {args.seed}",
        f"- Byte strings: {len(hexes)}, of which {sum(o.startswith('OK') for o in ours)} "
        "this project accepts",
        "",
        "| Decoder | Differences from this project |",
        "| --- | --- |",
    ]
    examples = []
    for name, cmd in tools().items():
        out = subprocess.run(cmd, input=data, capture_output=True, text=True, check=True)
        theirs = out.stdout.split("\n")[: len(hexes)]
        diffs = [(h, o, t) for h, o, t in zip(hexes, ours, theirs) if o != t]
        lines.append(f"| {name} | {len(diffs)} |")
        examples += [f"- {name}: `{h}`: this project `{o}`, theirs `{t}`" for h, o, t in diffs[:5]]
    lines += [""] + examples
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(hexes)} byte strings; report in {REPORT}")


if __name__ == "__main__":
    main()
