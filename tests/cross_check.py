#!/usr/bin/env python3
"""A one-off comparison of this decoder with three others, strict and lossy.

Unlike tests/run_tests.py, this is not part of the verified bar and is
not run in CI. It needs Go, Rust and Node:

    python3 tests/cross_check.py [--seed N] [--count N]

The byte strings are the ones tests/run_tests.py decodes, from the same
seed. Each is given to this project's tool, to Go's `utf8.Valid`, to
Rust's `String::from_utf8`, and to Node's `TextDecoder` with `fatal`
and `ignoreBOM` set. Each must accept exactly what this decoder accepts and read the
same code points.

Then each byte string goes to the lossy decoder, and to the lossy
decoding of the other three: Rust's `String::from_utf8_lossy`, Node's
`TextDecoder` without `fatal`, and a Go `range` loop.

For UTF-16, the lists of code units the tests decode go to Rust's
`String::from_utf16` and `from_utf16_lossy`, to Node's `isWellFormed`
and `toWellFormed`, and to Go's `unicode/utf16.Decode`; the byte strings
go to Node's `TextDecoder` for UTF-16BE and UTF-16LE, fatal and not,
with `ignoreBOM` set. The counts go to tests/CROSS-CHECK.md.
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


def tools(mode=""):
    """The command for each other decoder, by name."""
    BUILD.mkdir(parents=True, exist_ok=True)
    arg = [mode] if mode else []
    subprocess.run(["go", "build", "-o", str(BUILD / "go-utf8"), "main.go"], cwd=HELPERS,
                   check=True, env={**__import__("os").environ, "GO111MODULE": "off"})
    subprocess.run(["rustc", "-O", "-o", str(BUILD / "rust-utf8"), "main.rs"], cwd=HELPERS,
                   check=True)
    go, rust, node = (version(["go", "version"]), version(["rustc", "--version"]),
                      version(["node", "--version"]))
    if mode == "lossy":
        return {
            f"Go, a `range` loop over the string ({go})": [str(BUILD / "go-utf8"), *arg],
            f"Rust `String::from_utf8_lossy` ({rust})": [str(BUILD / "rust-utf8"), *arg],
            f"Node `TextDecoder`, not fatal, `ignoreBOM` set ({node})":
                ["node", str(HELPERS / "main.js"), *arg],
        }
    return {
        f"Go `utf8.Valid` ({go})": [str(BUILD / "go-utf8")],
        f"Rust `String::from_utf8` ({rust})": [str(BUILD / "rust-utf8")],
        f"Node `TextDecoder`, fatal, `ignoreBOM` set ({node})": ["node", str(HELPERS / "main.js")],
    }


def utf16_tools():
    BUILD.mkdir(parents=True, exist_ok=True)
    subprocess.run(["go", "build", "-o", str(BUILD / "go-utf16"), "main.go"], cwd=HELPERS / "go16",
                   check=True, env={**__import__("os").environ, "GO111MODULE": "off"})
    subprocess.run(["rustc", "-O", "-o", str(BUILD / "rust-utf16"), "utf16.rs"], cwd=HELPERS,
                   check=True)
    return (version(["go", "version"]), version(["rustc", "--version"]),
            version(["node", "--version"]))


def ask(req, hexes):
    out, problem = run_tests.run_tool("".join(f"{req} {h}\n" for h in hexes))
    if problem or len(out) != len(hexes):
        sys.exit(f"the tool failed: {problem}")
    return out


def utf16_section(args):
    items = list(run_tests.cases(args.seed, args.count))
    units = [req.split(" ", 1)[1] for label, req, _, _ in items
             if req.startswith("dec16 ") and label != "error"]
    byte_hexes = [req.split(" ", 1)[1] for label, req, _, _ in items
                  if req.startswith("decbe ") and label != "error"]
    go, rust, node = utf16_tools()
    js = str(HELPERS / "utf16.js")
    unit_data = "".join(h + "\n" for h in units)
    byte_data = "".join(h + "\n" for h in byte_hexes)
    strict = ask("dec16", units)
    lines = [
        "",
        "## UTF-16",
        "",
        f"- Lists of code units: {len(units)}, of which {sum(o.startswith('OK') for o in strict)} "
        "this project accepts",
        f"- Byte strings: {len(byte_hexes)}",
        "",
        "| Operation | Other decoder | Differences from this project |",
        "| --- | --- | --- |",
    ]
    examples = []
    for op, req, data, hexes, commands in [
        ("Units, strict", "dec16", unit_data, units, {
            f"Rust `String::from_utf16` ({rust})": [str(BUILD / "rust-utf16")],
            f"Node `isWellFormed` ({node})": ["node", js, "units"]}),
        ("Units, lossy", "lossy16", unit_data, units, {
            f"Rust `String::from_utf16_lossy` ({rust})": [str(BUILD / "rust-utf16"), "lossy"],
            f"Node `toWellFormed` ({node})": ["node", js, "units-lossy"],
            f"Go `utf16.Decode` ({go})": [str(BUILD / "go-utf16")]}),
        ("`toWellFormed`, as units", "wf16", unit_data, units, {
            f"Node `toWellFormed` ({node})": ["node", js, "wf"]}),
        ("UTF-16BE, strict", "decbe", byte_data, byte_hexes, {
            f"Node `TextDecoder`, fatal, `ignoreBOM` set ({node})": ["node", js, "be"]}),
        ("UTF-16LE, strict", "decle", byte_data, byte_hexes, {
            f"Node `TextDecoder`, fatal, `ignoreBOM` set ({node})": ["node", js, "le"]}),
        ("UTF-16BE, lossy", "lossybe", byte_data, byte_hexes, {
            f"Node `TextDecoder`, not fatal, `ignoreBOM` set ({node})": ["node", js, "be-lossy"]}),
        ("UTF-16LE, lossy", "lossyle", byte_data, byte_hexes, {
            f"Node `TextDecoder`, not fatal, `ignoreBOM` set ({node})": ["node", js, "le-lossy"]}),
    ]:
        ours = strict if req == "dec16" else ask(req, hexes)
        rows = []
        examples += compare(commands, hexes, ours, data, rows)
        lines += [f"| {op} |{row[1:]}" for row in rows]
    return lines + [""] + examples


def compare(commands, hexes, ours, data, lines):
    """Adds a table row for each command and returns examples of where it
    differs from `ours`."""
    examples = []
    for name, cmd in commands.items():
        out = subprocess.run(cmd, input=data, capture_output=True, text=True, check=True)
        theirs = out.stdout.split("\n")[: len(hexes)]
        if len(theirs) != len(hexes):
            sys.exit(f"{name} gave {len(theirs)} answers for {len(hexes)} byte strings")
        diffs = [(h, o, t) for h, o, t in zip(hexes, ours, theirs) if o != t]
        lines.append(f"| {name} | {len(diffs)} |")
        examples += [f"- {name}: `{h}`: this project `{o}`, theirs `{t}`" for h, o, t in diffs[:5]]
    return examples


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
    examples = compare(tools(), hexes, ours, data, lines)
    lines += [""] + examples

    lossy, problem = run_tests.run_tool("".join(f"lossy {h}\n" for h in hexes))
    if problem or len(lossy) != len(hexes):
        sys.exit(f"the tool failed: {problem}")
    lines += [
        "## Lossy decoding",
        "",
        f"The same byte strings, given to the lossy decoder. "
        f"{sum(o == 'REJECT' for o in ours)} of its answers have a U+FFFD in place of bad bytes, "
        "one for each byte string this project refuses. "
        f"{sum('fffd' in o.split(':', 1)[1].split(',') for o in lossy)} have a U+FFFD anywhere, "
        "which also counts well-formed input that holds a U+FFFD of its own, `EF BF BD`.",
        "",
        "| Decoder | Differences from this project |",
        "| --- | --- |",
    ]
    examples = compare(tools("lossy"), hexes, lossy, data, lines)
    lines += ["", "Go's `range` loop follows another policy, on purpose: the Go specification "
              "says that on an invalid UTF-8 sequence it gives U+FFFD and \"will advance a "
              "single byte\". So it gives one U+FFFD for each bad byte, and differs wherever a "
              "maximal subpart is longer than one byte.", ""] + examples
    lines += utf16_section(args)
    REPORT.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"{len(hexes)} byte strings; report in {REPORT}")


if __name__ == "__main__":
    main()
