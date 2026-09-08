#!/usr/bin/env bash
# Documentation-vs-tree consistency check (RELEASE_READINESS.md X3i). Exit 1 on any finding.
#
# 1. Pins. `lean-toolchain` and the `mathlib` `inputRev` in `lake-manifest.json` are the truth.
#    In README.md, CLAUDE.md and PROVE2ME.md:
#    - each file must quote the current toolchain version and the current Mathlib rev (a prefix
#      of at least 7 hex digits) at least once;
#    - every `leanprover/lean4:<v>` token must equal the toolchain;
#    - a stale token — a `vX.Y.Z[-rcN]` other than the toolchain, or, on a line that mentions
#      Mathlib, a 7–40 hex-digit string prefixing neither the Mathlib rev nor another manifest
#      package's rev — fails when its line asserts this repo's pin (contains one of
#      `lean-toolchain`, `lake-manifest`, `pinned to`, `pin is`, `this repo`, `this project`,
#      `both repos`, `toolchain`) unless its block (bullet, table row, heading or paragraph) is
#      history or a foreign environment: it contains `bumped from`, `prove2me`, `environment`,
#      `env #`, `mirror`, `workspace`, or the marker `pin-history` (write `<!-- pin-history -->`
#      beside a deliberate historical mention).
# 2. Cited-axiom ledger. In tools/cited_axioms.md (this repo's copy, else the sibling's at
#    ../LevyStochCalc/tools/cited_axioms.md) the live count stated in the header must equal
#    the number of `### <n>` entries, and tools/axiom_allowlist.txt must have exactly that many
#    entries. With no ledger reachable the count check is skipped and says so.
#
# Run manually: bash tools/check_docs.sh
set -euo pipefail

cd "$(git rev-parse --show-toplevel 2>/dev/null)" || cd "$(dirname "$0")/.."

python3 - <<'EOF'
import json
import re
import sys
from pathlib import Path

findings = []


def read(path):
    return Path(path).read_text(encoding="utf-8", errors="replace").replace("\r", "")


def prefix_of(token, rev):
    return len(token) >= 7 and rev.startswith(token)


toolchain_full = read("lean-toolchain").strip()
toolchain_ver = toolchain_full.split(":", 1)[-1]
mathlib_rev, other_revs = "", set()
for pkg in json.loads(read("lake-manifest.json")).get("packages", []):
    if pkg.get("name") == "mathlib":
        mathlib_rev = pkg.get("inputRev") or ""
    else:
        other_revs |= {pkg.get("inputRev"), pkg.get("rev")} - {None}
if not re.fullmatch(r"[0-9a-f]{40}", mathlib_rev):
    findings.append(f"lake-manifest.json: mathlib inputRev is not a 40-hex commit: {mathlib_rev!r}")
print(f"truth: toolchain {toolchain_full}; mathlib inputRev {mathlib_rev or '?'}")

TOOL_RE = re.compile(r"\bv\d+\.\d+\.\d+(?:-rc\d+)?\b")
FULL_RE = re.compile(r"leanprover/lean4:([A-Za-z0-9.\-]+)")
HEX_RE = re.compile(r"(?<![0-9A-Za-z])[0-9a-f]{7,40}(?![0-9A-Za-z])")
ASSERT_RE = re.compile(r"lean-toolchain|lake-manifest|pinned to|pin is|this repo|this project"
                       r"|both repos|toolchain", re.I)
EXEMPT_RE = re.compile(r"bumped from|prove2me|environment|env #|mirror|workspace|pin-history",
                       re.I)
BLOCK_START = re.compile(r"^\s*(?:[-*+]\s|\|\s|#|\d+\.\s)")


def block_texts(lines):
    """Text of the enclosing block (bullet, table row, heading or paragraph) per line."""
    ids, current = [], -1
    for i, line in enumerate(lines):
        if i == 0 or not line.strip() or not lines[i - 1].strip() or BLOCK_START.match(line):
            current += 1
        ids.append(current)
    grouped = {}
    for i, b in enumerate(ids):
        grouped.setdefault(b, []).append(lines[i])
    return ["\n".join(grouped[b]) for b in ids]


for name in ("README.md", "CLAUDE.md", "PROVE2ME.md"):
    if not Path(name).exists():
        findings.append(f"{name}: file missing")
        continue
    text = read(name)
    lines = text.split("\n")
    blocks = block_texts(lines)
    if toolchain_ver not in text:
        findings.append(f"{name}: never quotes the toolchain version {toolchain_ver}")
    if mathlib_rev and not any(prefix_of(t, mathlib_rev) for t in HEX_RE.findall(text)):
        findings.append(f"{name}: never quotes the Mathlib rev {mathlib_rev[:8]}")
    for i, line in enumerate(lines, 1):
        for full in FULL_RE.findall(line):
            if full != toolchain_ver:
                findings.append(f"{name}:{i}: leanprover/lean4:{full} but lean-toolchain says "
                                f"{toolchain_full}")
        stale = [t for t in TOOL_RE.findall(line) if t != toolchain_ver]
        if re.search("mathlib", line, re.I):
            stale += [t for t in HEX_RE.findall(line) if not prefix_of(t, mathlib_rev)
                      and not any(prefix_of(t, r) for r in other_revs)]
        if stale and ASSERT_RE.search(line) and not EXEMPT_RE.search(blocks[i - 1]):
            findings.append(f"{name}:{i}: stale pin {', '.join(stale)} in: "
                            f"{line.strip()[:70]}")

allow_path = "tools/axiom_allowlist.txt"
if Path(allow_path).exists():
    allow = sorted({e.split("#", 1)[0].strip() for e in read(allow_path).split("\n")} - {""})
else:
    allow = []
    findings.append(f"{allow_path}: file missing")
ledger = next((p for p in ("tools/cited_axioms.md", "../LevyStochCalc/tools/cited_axioms.md")
               if Path(p).exists()), None)
if ledger is None:
    print("cited-axiom ledger: no tools/cited_axioms.md here or in ../LevyStochCalc; the "
          "live-count check is skipped")
else:
    lines = read(ledger).split("\n")
    first = next((i for i, l in enumerate(lines) if l.startswith("### ")), len(lines))
    header = "\n".join(lines[:first])
    words = {"zero": 0, "no": 0, "one": 1, "two": 2, "three": 3, "four": 4, "five": 5,
             "six": 6, "seven": 7, "eight": 8, "nine": 9, "ten": 10}
    num = r"(\d+|zero|no|one|two|three|four|five|six|seven|eight|nine|ten)"
    patterns = [
        num + r"\s+(?:cited\s+)?axioms?\s+(?:is|are|remains?)\s+(?:currently\s+)?live\b",
        num + r"\s+currently\s+live\b",
        num + r"\s+live\s+(?:cited\s+)?axioms?\b",
        r'grep -c "\^### \[0-9\]"[^=\n]*==\s*(\d+)',
    ]
    claims = set()
    for pat in patterns:
        for m in re.finditer(r"\b" + pat, header, re.I):
            word = m.group(1).lower()
            claims.add(int(word) if word.isdigit() else words[word])
    entries = [l for l in lines if re.match(r"### \d+\b", l)]
    print(f"{ledger}: header live count {sorted(claims) or 'not found'}; "
          f"'### <n>' entries {len(entries)}; {allow_path} entries {len(allow)}")
    if not claims:
        findings.append(f"{ledger}: header states no live-axiom count in a recognised phrasing")
    elif len(claims) > 1:
        findings.append(f"{ledger}: header states conflicting live counts {sorted(claims)}")
    else:
        live = claims.pop()
        if live != len(entries):
            findings.append(f"{ledger}: header says {live} live but has {len(entries)} "
                            f"'### <n>' entries")
        if len(allow) != live:
            findings.append(f"{allow_path}: {len(allow)} entries but {ledger} says {live} live")

if findings:
    print("FAIL:")
    for item in findings:
        print("  - " + item)
    sys.exit(1)
print("PASS: documentation pins and cited-axiom counts match the tree.")
EOF
