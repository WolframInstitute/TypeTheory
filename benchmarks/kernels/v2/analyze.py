#!/usr/bin/env python3
"""TypeTheory's test suite on the v2 Wolfram kernel against Wolfram 15: the v2 failures grouped by first-cut cause.

Usage: python3 benchmarks/kernels/v2/analyze.py <v2 .test-runs directory> <Wolfram 15 log>

The v2 directory is what scripts/run_tests_by_file.sh leaves in .test-runs/: one <file>.log a test file, with
scripts/run_tests.wls's per-file line and failure blocks, and the results file. The Wolfram 15 log is the output of
scripts/run_tests.wls over the whole suite. A v2 failure counts only when the same test passes on Wolfram 15 (its
file ran there and the test is not among its failures); a test failing on both is TypeTheory's own. Each counted
failure gets a first-cut cause: a function the v2 kernel reports as not implemented; else the first message the test
raised; else a System function in the actual result that the expected result lacks, most often a call left
unevaluated; else a wrong result with no message. The causes are a starting point: one bug can show under several,
and the wrong results need reading test by test (README.md).

Prints the causes, biggest first, with their test counts and files, then the timeouts and memory kills, then
TypeTheory's own failures, and writes the same as JSON beside the Wolfram 15 log. Files are keyed by their path under TypeTheory/Tests, as the
logs name them; test IDs keep their tests apart.
The System names come from wolframscript on first use, cached beside the JSON as system_names.txt.
"""
import json, os, re, subprocess, sys
from collections import defaultdict

FAILED = re.compile(r"^ {10}failed: (.*)$")
FIELD = re.compile(r"^ *(actual|expected|messages|expected messages): (.*)$")
FILELINE = re.compile(r"^  (ok|FAIL) +(\S+\.wlt) +\((\d+)/(\d+)\)")
UNIMPL = re.compile(r"(\w+) is not implemented in this kernel yet|Message\[(\w+)::unimpl\w*")
MESSAGE = re.compile(r"Message\[(\w+)::(\w+)")
KILLED = re.compile(r"^  (TIMEOUT|MEMORY|NORESULT) ")
IDENT = re.compile(r"(?<![\w`$])([A-Z][A-Za-z0-9]+)\[")
# heads that appear in ordinary results and say nothing about a call left unevaluated
INERT = {"HoldForm", "List", "Rule", "RuleDelayed", "Association", "Times", "Plus", "Power", "Rational", "Complex",
    "Missing", "Failure", "Quantity", "Interval", "Graph", "SparseArray", "Function", "Slot", "Hold", "Sqrt", "Equal",
    "Less", "Greater", "LessEqual", "GreaterEqual", "And", "Or", "Not", "Subscript", "Sequence", "Root", "Removed", "Real",
    "Integer", "String", "DirectedInfinity", "Indeterminate", "ByteArray", "NumericArray", "Entity", "Pi", "E"}


def failures(lines):
    """The failure blocks of a run_tests.wls output, each after its file's line: {file: {test id: fields}}."""
    out, current_file, block = defaultdict(dict), None, None
    for line in lines:
        m = FILELINE.match(line)
        if m:
            current_file, block = m.group(2), None
            continue
        m = FAILED.match(line)
        if m and current_file:
            block = {}
            out[current_file][m.group(1).strip()] = block
            continue
        m = FIELD.match(line)
        if m and block is not None:
            block[m.group(1)] = m.group(2)
    return out


def file_lines(lines):
    return {m.group(2): m.group(1) for m in map(FILELINE.match, lines) if m}


def system_names(cache):
    if not os.path.exists(cache):
        code = 'Export["%s", Names["System`*"], "Lines"]' % cache.replace("\\", "\\\\").replace('"', '\\"')
        subprocess.run(["wolframscript", "-code", code], check=True, stdout=subprocess.DEVNULL)
    return set(open(cache).read().split())


def cause(fields, system):
    text = fields.get("messages", "") + " " + fields.get("actual", "")
    m = UNIMPL.search(text)
    if m:
        return "not implemented on v2: " + (m.group(1) or m.group(2))
    m = MESSAGE.search(fields.get("messages", ""))
    if m:
        return f"message {m.group(1)}::{m.group(2)}"
    expected = set(IDENT.findall(fields.get("expected", "")))
    heads = [h for h in IDENT.findall(fields.get("actual", "")) if h in system and h not in INERT and h not in expected]
    if heads:
        return "unevaluated on v2 (no message): " + heads[0]
    return "wrong result, no message"


def main(v2dir, w15log):
    base = os.path.splitext(w15log)[0]
    system = system_names(os.path.join(os.path.dirname(os.path.abspath(w15log)), "system_names.txt"))
    w15 = open(w15log, errors="replace").read().splitlines()
    w15_fail, w15_files = failures(w15), file_lines(w15)
    v2_fail, v2_files = defaultdict(dict), {}
    for name in sorted(os.listdir(v2dir)):
        if name.endswith(".wlt.log"):
            lines = open(os.path.join(v2dir, name), errors="replace").read().splitlines()
            for f, tests in failures(lines).items():
                v2_fail[f].update(tests)
            v2_files.update(file_lines(lines))
    results = os.path.join(v2dir, "results")
    killed = [l.strip() for l in open(results, errors="replace") if KILLED.match(l)] if os.path.exists(results) else []
    causes, own, unmatched = defaultdict(list), [], []
    for f, tests in v2_fail.items():
        for tid, fields in tests.items():
            if f not in w15_files:
                unmatched.append((f, tid))
            elif tid in w15_fail.get(f, {}):
                own.append((f, tid, fields.get("actual", "")[:160]))
            else:
                causes[cause(fields, system)].append((f, tid, fields.get("actual", "")[:160], fields.get("messages", "")[:200]))
    ranked = sorted(causes.items(), key=lambda kv: -len(kv[1]))
    print(f"v2 files with a result: {len(v2_files)}; Wolfram 15 files with a result: {len(w15_files)}")
    print(f"v2 failures of tests that pass on Wolfram 15: {sum(len(v) for v in causes.values())} tests, {len(causes)} causes")
    for c, items in ranked:
        files = sorted({f for f, *_ in items})
        print(f"\n{len(items):4d}  {c}\n      files ({len(files)}): {', '.join(files[:12])}{' ...' if len(files) > 12 else ''}")
        f, tid, actual, messages = items[0]
        print(f"      e.g. {f} {tid}: actual {actual}\n           messages {messages}")
    print(f"\ntimeouts and memory kills ({len(killed)}):")
    for k in killed:
        print("  " + k)
    print(f"\nTypeTheory's own (failing on Wolfram 15 too): {len(own)} tests")
    for f, tid, actual in own[:40]:
        print(f"  {f} {tid}")
    if unmatched:
        print(f"\nv2 failures in files Wolfram 15 did not report: {len(unmatched)}")
    with open(base + ".analysis.json", "w") as out:
        json.dump({"causes": dict(ranked), "killed": killed, "own": own, "unmatched": unmatched}, out, indent=1)


if __name__ == "__main__":
    if len(sys.argv) != 3:
        sys.exit(__doc__)
    main(sys.argv[1], sys.argv[2])
