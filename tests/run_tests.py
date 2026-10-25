#!/usr/bin/env python3
"""Differential tests: the Lean UTF-8 codec against Python's, with Lean
core's compiled check alongside.

The oracle is Python's strict UTF-8 codec: `bytes.decode("utf-8")`,
which raises on any byte string that is not well formed, and
`str.encode("utf-8")`. For every byte string the Lean decoder must give
Python's answer. Lean core's `String.fromUTF8?`, which at run time is
C code that no proof covers, must give the same answer too: the tool
answers `core` requests with it.

Inputs come from a recorded seed, after fixed sets:

- every string of one and two bytes;
- every three-byte string whose bytes are all 0x80 or more, and every
  three-byte string led by 0xE0 to 0xEF with a third byte at the edges
  of the continuation range;
- four-byte strings led by 0xF0 to 0xF7 over every second byte, with the
  third and fourth at the edges;
- the hard cases from Markus Kuhn's UTF-8 decoder test file;
- random lists of code points, weighted to the edges of each length and
  of the surrogates, encoded and decoded;
- mutations of those encodings: a byte changed, dropped, added or
  flipped, the string cut short, a character rewritten in a longer form
  than it needs, a surrogate or a value past U+10FFFF put in;
- random short byte strings;
- lists with a code point that is not a scalar value, which the encoder
  must refuse;
- malformed requests, which the tool must answer with `error`.

Every seventh request ends in CR LF.

    python3 tests/run_tests.py [--seed N] [--count N]

`--count` is the number of random inputs after the fixed sets. The
script builds the executable first, writes tests/TEST-RESULTS.md, and
exits non-zero if any input disagrees.
"""

import argparse
import itertools
import platform
import random
import subprocess
import sys
import threading
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
EXE = ROOT / ".lake" / "build" / "bin" / "utf8"
RESULTS = ROOT / "tests" / "TEST-RESULTS.md"
TIMEOUT = 1800
BUILD_TIMEOUT = 3600


def oracle_decode(data):
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError:
        return "REJECT"
    return "OK:" + ",".join(f"{ord(ch):x}" for ch in text)


def oracle_encode(points):
    if any(0xD800 <= p <= 0xDFFF or p > 0x10FFFF for p in points):
        return "INVALID"
    return "".join(map(chr, points)).encode("utf-8").hex()


# The fixed sets.

def all_short():
    for n in range(256):
        yield bytes([n])
    for a in range(256):
        for b in range(256):
            yield bytes([a, b])


def three_byte():
    for a in range(0x80, 0x100):
        for b in range(0x80, 0x100):
            for c in range(0x80, 0x100):
                yield bytes([a, b, c])
    for a in range(0xE0, 0xF0):
        for b in range(256):
            for c in (0x00, 0x7F, 0xC0, 0xFF):
                yield bytes([a, b, c])


def four_byte():
    for a in range(0xF0, 0xF8):
        for b in range(256):
            for c in (0x7F, 0x80, 0xA5, 0xBF, 0xC0):
                for d in (0x80, 0xBF, 0xC0):
                    yield bytes([a, b, c, d])


# The hard cases of Markus Kuhn's UTF-8 decoder test file
# (https://www.cl.cam.ac.uk/~mgk25/ucs/examples/UTF-8-test.txt),
# sections 2 to 5, written out here.
KUHN = [
    "00", "c280", "e0a080", "f0908080", "f888808080", "fc8480808080",
    "7f", "dfbf", "efbfbf", "f7bfbfbf", "fbbfbfbfbf", "fdbfbfbfbfbf",
    "ed9fbf", "ee8080", "efbfbd", "f48fbfbf", "f4908080",
    "80", "bf", "80bf", "80bf80", "80bf80bf", "80bf80bf80",
    "".join(f"{b:02x}" for b in range(0x80, 0xC0)),
    "".join(f"{b:02x}20" for b in range(0xC0, 0xE0)),
    "".join(f"{b:02x}20" for b in range(0xE0, 0xF0)),
    "".join(f"{b:02x}20" for b in range(0xF0, 0xF8)),
    "".join(f"{b:02x}20" for b in range(0xF8, 0xFC)),
    "fc20fd20",
    "c0", "e080", "f08080", "f8808080", "fc80808080",
    "df", "efbf", "f7bfbf", "fbbfbfbf", "fdbfbfbfbf",
    "c0e080f08080f8808080fc80808080dfefbff7bfbffbbfbfbffdbfbfbfbf",
    "fe", "ff", "fefeffff",
    "c0af", "e080af", "f08080af", "f8808080af", "fc80808080af",
    "c1bf", "e09fbf", "f08fbfbf", "f887bfbfbf", "fc83bfbfbfbf",
    "c080", "e08080", "f0808080", "f880808080", "fc8080808080",
    "eda080", "edadbf", "edae80", "edafbf", "edb080", "edbe80", "edbfbf",
    "eda080edb080", "eda080edbfbf", "edadbfedb080", "edadbfedbfbf",
    "edae80edb080", "edae80edbfbf", "edafbfedb080", "edafbfedbfbf",
    "efbfbe", "efbfbf", "efb790", "efb7af",
]


def random_point(rng):
    r = rng.random()
    if r < 0.3:
        return rng.randint(0, 0x7F)
    if r < 0.5:
        return rng.choice([0x7F, 0x80, 0x7FF, 0x800, 0xFFF, 0x1000, 0xCFFF, 0xD000, 0xD7FF,
                           0xE000, 0xFFFD, 0xFFFE, 0xFFFF, 0x10000, 0x3FFFF, 0x40000, 0xFFFFF,
                           0x100000, 0x10FFFF, 0xFEFF, 0x2028])
    if r < 0.8:
        return rng.choice([rng.randint(0x80, 0x7FF), rng.randint(0x800, 0xD7FF),
                           rng.randint(0xE000, 0xFFFF)])
    return rng.randint(0x10000, 0x10FFFF)


def random_points(rng):
    return [random_point(rng) for _ in range(rng.choice([0, 1, 1, 2, 3, 5, 8, 20]))]


def longer_form(p, size):
    """`p` written in `size` bytes, longer than it needs: an overlong
    form (sizes up to 6, as in the old definition of UTF-8)."""
    lead = {2: 0xC0, 3: 0xE0, 4: 0xF0, 5: 0xF8, 6: 0xFC}[size]
    tail = [0x80 | ((p >> (6 * k)) & 0x3F) for k in reversed(range(size - 1))]
    return bytes([lead | (p >> (6 * (size - 1)))] + tail)


def mutate(rng, data):
    b = bytearray(data)
    op = rng.randrange(9)
    if op == 0 and b:
        b[rng.randrange(len(b))] = rng.getrandbits(8)
    elif op == 1 and b:
        del b[rng.randrange(len(b))]
    elif op == 2:
        b.insert(rng.randint(0, len(b)), rng.getrandbits(8))
    elif op == 3 and b:
        b[rng.randrange(len(b))] ^= 1 << rng.randrange(8)
    elif op == 4 and b:
        b = b[: rng.randrange(len(b))]
    elif op == 5:
        p = rng.choice([0x2F, 0, rng.randint(0, 0x7F), rng.randint(0x80, 0x7FF), rng.randint(0x800, 0xFFFF)])
        need = 1 if p < 0x80 else 2 if p < 0x800 else 3
        b[rng.randint(0, len(b)):0] = longer_form(p, rng.randint(need + 1, need + 2))
    elif op == 6:
        p = rng.randint(0xD800, 0xDFFF)
        b[rng.randint(0, len(b)):0] = bytes([0xED, 0x80 | ((p >> 6) & 0x3F), 0x80 | (p & 0x3F)])
    elif op == 7:
        p = rng.randint(0x110000, 0x1FFFFF)
        b[rng.randint(0, len(b)):0] = longer_form(p, 4)
    else:
        b += bytes(rng.getrandbits(8) for _ in range(rng.randint(1, 3)))
    return bytes(b)


def invalid_points(rng):
    points = random_points(rng) or [random_point(rng)]
    points[rng.randrange(len(points))] = rng.choice(
        [0xD800, 0xDFFF, rng.randint(0xD800, 0xDFFF), 0x110000, rng.randint(0x110000, 0xFFFFFFFF)])
    return points


MALFORMED = [
    ("frob 41", "unknown operation"),
    ("DECODE 41", "operations are lower case"),
    ("decode", "no argument"),
    ("decode 4", "an odd number of hex digits"),
    ("decode 4G", "not a hex digit"),
    ("decode 4A", "hex digits are lower case"),
    ("decode 41 41", "two arguments"),
    ("core", "no argument"),
    ("encode", "no argument"),
    ("encode 41,", "an empty code point"),
    ("encode 123456789", "a code point of more than 8 digits"),
    ("encode 4G", "a code point that is not hex"),
    ("encode 41 42", "two arguments"),
    ("", "an empty line"),
    (" decode 41", "a leading space"),
]

AT_EOF = [("decode 41", "OK:41"), ("encode 41", "41"), ("decode 41\r\n", "OK:41")]


def decode_pair(label, data, mutated=False):
    want = oracle_decode(data)
    return [(label, f"decode {data.hex()}", want, mutated),
            (label + " (core)", f"core {data.hex()}", want, mutated)]


def cases(seed, count):
    """(label, request, expected answer, mutated) for each input."""
    for req, _ in MALFORMED:
        yield ("error", req, "error", False)
    for s in KUHN:
        yield from decode_pair("kuhn", bytes.fromhex(s))
    for data in itertools.chain(all_short(), three_byte(), four_byte()):
        yield from decode_pair("grid", data)
    rng = random.Random(seed)
    for _ in range(count):
        r = rng.random()
        if r < 0.3:
            points = random_points(rng)
            yield ("encode", "encode " + (",".join(f"{p:x}" for p in points) or "-"),
                   oracle_encode(points), False)
            yield from decode_pair("valid", "".join(map(chr, points)).encode("utf-8"))
        elif r < 0.8:
            base = "".join(map(chr, random_points(rng))).encode("utf-8")
            data = mutate(rng, base)
            while data == base:
                data = mutate(rng, base)
            yield from decode_pair("mutated", data, True)
        elif r < 0.92:
            yield from decode_pair("random", bytes(rng.getrandbits(8) for _ in range(rng.randint(0, 8))))
        else:
            points = invalid_points(rng)
            yield ("encode invalid", "encode " + ",".join(f"{p:x}" for p in points), "INVALID", False)


def run_tool(data, timeout=TIMEOUT):
    """The tool's answer lines for `data`, and a note on how the run
    failed, or None."""
    raw = data.encode("utf-8")
    limit = 2 * len(raw) + 64 * (data.count("\n") + 1)
    try:
        proc = subprocess.Popen([str(EXE), "serve"], stdin=subprocess.PIPE,
                                stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    except OSError as e:
        return [], f"could not run {EXE.relative_to(ROOT)}: {e.strerror or e}"
    out, err = bytearray(), bytearray()

    def feed():
        try:
            proc.stdin.write(raw)
            proc.stdin.close()
        except (BrokenPipeError, ValueError):
            pass

    def drain(stream, buf, cap):
        while chunk := stream.read1(1 << 16):
            buf += chunk
            if len(buf) > cap:
                proc.kill()
                return

    threads = [threading.Thread(target=feed),
               threading.Thread(target=drain, args=(proc.stdout, out, limit)),
               threading.Thread(target=drain, args=(proc.stderr, err, 1 << 20))]
    for t in threads:
        t.start()
    problem = None
    try:
        proc.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        proc.kill()
        problem = f"no end after {timeout} seconds"
    for t in threads:
        t.join()
    proc.wait()
    if len(out) > limit:
        problem = problem or f"more than {limit} bytes of output, stopped"
    elif proc.returncode != 0 and not problem:
        tail = " / ".join(err.decode("utf-8", "backslashreplace").splitlines()[-3:])
        problem = f"exit status {proc.returncode}: {tail}"
    text = bytes(out).decode("utf-8", "backslashreplace")
    if text and not text.endswith("\n"):
        problem = problem or "the last answer has no LF"
    lines = text.split("\n")
    if lines and lines[-1] == "":
        lines.pop()
    return lines, problem


def oracle():
    return f"Python {platform.python_version()} strict `utf-8` codec"


def lean_version():
    try:
        out = subprocess.run(["lake", "env", "lean", "--version"], cwd=ROOT,
                             capture_output=True, text=True, errors="backslashreplace",
                             timeout=300)
        first = out.stdout.strip().splitlines()[:1]
        return first[0] if first else "unknown"
    except (OSError, subprocess.TimeoutExpired):
        return "unknown"


def count(text):
    n = int(text)
    if n < 1:
        raise argparse.ArgumentTypeError("the count must be at least 1")
    return n


def write(lines):
    RESULTS.write_text("\n".join(lines), encoding="utf-8")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--seed", type=int, default=20261025)
    ap.add_argument("--count", type=count, default=150_000)
    args = ap.parse_args()

    try:
        build = subprocess.run(["lake", "build", "utf8"], cwd=ROOT, capture_output=True,
                               text=True, errors="backslashreplace", timeout=BUILD_TIMEOUT)
        built, log = build.returncode == 0, build.stdout + build.stderr
    except (OSError, subprocess.TimeoutExpired) as e:
        built, log = False, str(e)
    if not built:
        write(["# Test results", "", f"- Oracle: {oracle()}", f"- Seed: {args.seed}",
               "- Inputs: 0", "- Failures: 1 (`lake build utf8` failed)", ""])
        sys.exit("lake build utf8 failed:\n" + log)

    items = list(cases(args.seed, args.count))
    # Every seventh request ends in CR LF, which the tool must take as LF.
    out, problem = run_tool("".join(req + ("\r\n" if i % 7 == 6 else "\n")
                                    for i, (_, req, _, _) in enumerate(items)))
    failures = [("(whole run)", "a clean run", problem)] if problem else []
    for item, got in itertools.zip_longest(items, out):
        if item is None:
            failures.append(("(no request)", "nothing", got))
        elif got != item[2]:
            failures.append((item[1], item[2], "(no answer)" if got is None else got))
    eof_right = 0
    for req, want in AT_EOF:
        got, problem = run_tool(req, timeout=60)
        if got == [want] and not problem:
            eof_right += 1
        else:
            failures.append((req + " (at end of input)", want, f"{got} {problem or ''}".strip()))

    by_label = {}
    for label, _, _, _ in items:
        by_label[label] = by_label.get(label, 0) + 1
    decodes = [want for label, req, want, _ in items if req.startswith("decode ")
               and label != "error"]
    accepted = sum(1 for w in decodes if w.startswith("OK"))
    core_items = [(item, got) for item, got in zip(items, out) if item[1].startswith("core ")]
    core_agree = sum(1 for item, got in core_items if got == item[2])
    mutated = sum(1 for item in items if item[3])
    malformed = [got for item, got in zip(items, out) if item[0] == "error"]

    lines = [
        "# Test results",
        "",
        "Written by `tests/run_tests.py`. Rerun it to check these numbers.",
        "",
        f"- Oracle: {oracle()}",
        f"- Lean: {lean_version()}",
        f"- Seed: {args.seed}",
        f"- Inputs: {len(items)}",
        f"- Mutated: {mutated} of the inputs are mutated encodings",
        "- By kind: " + ", ".join(f"{k} {v}" for k, v in sorted(by_label.items())),
        f"- Byte strings decoded: {len(decodes)}, of which {accepted} well formed and "
        f"{len(decodes) - accepted} refused",
        f"- The same byte strings given to Lean core's `String.fromUTF8?`, agreeing with "
        f"Python: {core_agree} of {len(core_items)}",
        f"- Malformed requests answered `error`: {malformed.count('error')} of "
        f"{by_label.get('error', 0)}",
        f"- Requests ending in CR LF: every seventh, {len(items) // 7}",
        f"- Last lines sent alone, with no LF or with CR LF, answered right: {eof_right} of "
        f"{len(AT_EOF)}",
        f"- Failures: {len(failures)}",
        "",
    ]
    if failures:
        lines += ["## Failures", ""]
        lines += [f"- `{req[:160]!r}`: expected `{want[:120]!r}`, got `{got[:120]!r}`"
                  for req, want, got in failures[:50]]
        lines.append("")
    write(lines)
    agree = sum(1 for item, got in zip(items, out) if got == item[2])
    print(f"{agree}/{len(items)} inputs agree, {len(failures)} failures; results in {RESULTS}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
