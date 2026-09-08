#!/usr/bin/env python3
"""Check a `#print axioms` transcript against the audit script that produced it.

usage: audit_check.py AUDIT_OUTPUT AUDIT_LEAN ALLOWLIST [--sorry-baseline FILE]
                      [--show-nonstandard] [--allow-unused]

Exit status: 0 every check passed, 1 a check failed, 2 bad invocation or unreadable input.

Checks, in order:
  1. no line of AUDIT_OUTPUT matches `: error` (Lean's `file:line:col: error(kind): ...` form);
  2. every `#print axioms <name>` command in AUDIT_LEAN has a report in AUDIT_OUTPUT, either
     `'<name>' depends on axioms: [...]` or `'<name>' does not depend on any axioms`, one report
     per command, and no report names a declaration the script did not ask about;
  3. every reported axiom is one of propext / Classical.choice / Quot.sound or listed in
     ALLOWLIST; `sorryAx` is tolerated only on names listed in --sorry-baseline;
  4. every ALLOWLIST entry is used by some report (unless --allow-unused: the allowlist is
     shared with a wider audit) and every baseline entry is an audited name, so neither file
     can drift away from the tree.

Lean wraps long axiom lists over several lines whose continuations start with whitespace; they
are joined before parsing, and the report regex is anchored per line so that names ending in a
prime (`foo'`) are matched like any other.

A pass certifies the logical trust base of the audited declarations: the kernel axioms each one
reduces to. It says nothing about the mathematical coverage or grounding of their statements;
those live in the coverage ledgers (PaperC_CoverageMatrix.md, GOAL.md).
"""

import re
import sys
from collections import Counter

STANDARD = ("propext", "Classical.choice", "Quot.sound")
REPORT_RE = re.compile(r"^'(.+)' (?:depends on axioms: \[(.*)\]|does not depend on any axioms)$")
PRINT_RE = re.compile(r"#print\s+axioms")
USAGE = (
    "usage: audit_check.py AUDIT_OUTPUT AUDIT_LEAN ALLOWLIST [--sorry-baseline FILE]"
    " [--show-nonstandard] [--allow-unused]"
)


def read_text(path):
    try:
        with open(path, encoding="utf-8", errors="replace") as handle:
            return handle.read().replace("\r", "")
    except OSError as exc:
        sys.exit(f"audit_check: cannot read {path}: {exc}")


def logical_lines(text):
    """Join Lean's wrapped continuation lines (leading whitespace) onto the line they extend."""
    lines = []
    for raw in text.split("\n"):
        if raw[:1].isspace() and lines:
            lines[-1] += " " + raw.strip()
        else:
            lines.append(raw.rstrip())
    return lines


def strip_comments(src):
    """Blank out `--` line comments and `/- -/` block comments, preserving newlines."""
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if depth and src.startswith("-/", i):
            depth -= 1
            i += 2
            continue
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
            continue
        out.append(src[i] if depth == 0 or src[i] == "\n" else " ")
        i += 1
    return "".join(out)


def audit_commands(src):
    """Return ([(name, line)], [malformed line]) for every `#print axioms` in the script."""
    clean = strip_comments(src)
    commands, malformed = [], []
    for match in PRINT_RE.finditer(clean):
        line = clean.count("\n", 0, match.start()) + 1
        token = re.match(r"\s*(\S+)", clean[match.end():])
        if token is None or token.group(1).startswith("#"):
            malformed.append(line)
        else:
            commands.append((token.group(1), line))
    return commands, malformed


def read_list(path):
    entries = []
    for raw in read_text(path).split("\n"):
        entry = raw.split("#", 1)[0].strip()
        if entry:
            entries.append(entry)
    return entries


def parse_args(argv):
    positional, baseline, show, allow_unused = [], None, False, False
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg == "--sorry-baseline":
            if i + 1 >= len(argv):
                sys.exit(USAGE)
            baseline = argv[i + 1]
            i += 2
        elif arg == "--show-nonstandard":
            show = True
            i += 1
        elif arg == "--allow-unused":
            allow_unused = True
            i += 1
        elif arg.startswith("-"):
            sys.exit(USAGE)
        else:
            positional.append(arg)
            i += 1
    if len(positional) != 3:
        sys.exit(USAGE)
    return positional, baseline, show, allow_unused


def main(argv):
    (out_path, lean_path, allow_path), baseline_path, show, allow_unused = parse_args(argv)
    failures = []

    lines = logical_lines(read_text(out_path))
    errors = [ln for ln in lines if ": error" in ln]
    if errors:
        failures.append(f"{len(errors)} error line(s) in {out_path}:\n"
                        + "\n".join("    " + ln for ln in errors))

    reports, unparsed, other = [], [], []
    for ln in lines:
        if not ln:
            continue
        match = REPORT_RE.match(ln)
        if match:
            axioms = match.group(2)
            deps = None if axioms is None else [a.strip() for a in axioms.split(",")]
            reports.append((match.group(1), deps))
        elif ln.startswith("'"):
            unparsed.append(ln)
        elif ": error" not in ln:
            other.append(ln)
    if unparsed:
        failures.append(f"{len(unparsed)} report-like line(s) did not parse:\n"
                        + "\n".join("    " + ln for ln in unparsed))

    commands, malformed = audit_commands(read_text(lean_path))
    if malformed:
        failures.append(f"`#print axioms` without a name in {lean_path} at line(s): "
                        + ", ".join(str(n) for n in malformed))
    reported = Counter(name for name, _ in reports)
    reported_names = list(reported)

    def resolve(name):
        # A script may print a short name under an `open`; Lean reports the qualified one.
        if name in reported:
            return name
        candidates = [m for m in reported_names if m.endswith("." + name)]
        return candidates[0] if len(candidates) == 1 else name

    expected = Counter(resolve(name) for name, _ in commands)
    missing = sorted(n for n in expected if n not in reported)
    unexpected = sorted(n for n in reported if n not in expected)
    miscount = sorted(n for n in expected if n in reported and reported[n] != expected[n])
    if missing:
        failures.append(f"{len(missing)} audited name(s) have no report in {out_path}:\n"
                        + "\n".join("    " + n for n in missing))
    if unexpected:
        failures.append(f"{len(unexpected)} report(s) for names not audited by {lean_path}:\n"
                        + "\n".join("    " + n for n in unexpected))
    if miscount:
        failures.append("report count differs from command count for:\n" + "\n".join(
            f"    {n}: {expected[n]} command(s), {reported[n]} report(s)" for n in miscount))

    allow = read_list(allow_path)
    dup_allow = sorted(n for n, k in Counter(allow).items() if k > 1)
    allow = set(allow)
    baseline = set(read_list(baseline_path)) if baseline_path else set()
    bad_baseline = sorted(n for n in baseline if n not in expected)
    if bad_baseline:
        failures.append(f"sorry-baseline entries that are not audited by {lean_path}:\n"
                        + "\n".join("    " + n for n in bad_baseline))

    seen_axioms = Counter()
    off, nonstandard, used_allow, sorried = [], [], {}, set()
    for name, deps in reports:
        if deps is None:
            continue
        seen_axioms.update(deps)
        extra = [a for a in deps if a not in STANDARD]
        if extra:
            nonstandard.append((name, extra))
        for axiom in extra:
            if axiom in allow:
                used_allow.setdefault(axiom, set()).add(name)
            elif axiom == "sorryAx" and name in baseline:
                sorried.add(name)
            else:
                off.append((name, axiom))
    if off:
        failures.append("axioms outside {propext, Classical.choice, Quot.sound} and the allowlist "
                        f"({allow_path}):\n" + "\n".join(f"    {n}: {a}" for n, a in off))
    unused_allow = sorted(allow - set(used_allow))
    if unused_allow and not allow_unused:
        failures.append("allowlist entries no audited declaration depends on (delete them in the "
                        "commit that discharges the axiom):\n"
                        + "\n".join("    " + a for a in unused_allow))
    resolved = sorted(baseline - sorried - set(bad_baseline))

    depends = sum(1 for _, deps in reports if deps is not None)
    print(f"audit_check: {out_path} against {lean_path}")
    print(f"  #print axioms commands: {len(commands)} ({len(expected)} distinct names)")
    print(f"  reports: {len(reports)} ({depends} 'depends on axioms', "
          f"{len(reports) - depends} 'does not depend on any axioms')")
    print(f"  error lines: {len(errors)}; other non-report lines: {len(other)}")
    for ln in other[:10]:
        print("    " + ln)
    print("  axioms seen: " + (", ".join(sorted(seen_axioms)) or "none"))
    if dup_allow:
        print("  duplicate allowlist entries: " + ", ".join(dup_allow))
    for axiom in sorted(used_allow):
        users = sorted(used_allow[axiom])
        print(f"  allowlisted axiom {axiom}")
        print(f"    used by {len(users)} declaration(s): " + ", ".join(users))
    if sorried:
        print("  sorryAx within the baseline: " + ", ".join(sorted(sorried)))
    if resolved:
        print("  INFO: baseline entries with no sorryAx any more (remove them): "
              + ", ".join(resolved))
    if show:
        print(f"  reports with axioms beyond the standard three: {len(nonstandard)}")
        for name, extra in nonstandard:
            print(f"    {name}: " + ", ".join(extra))

    if failures:
        print("FAIL:")
        for item in failures:
            print("  - " + item)
        return 1
    print("PASS: every audited declaration reduces to the standard axioms plus the allowlist.")
    print("      (This certifies the logical trust base only, not mathematical coverage or"
          " grounding.)")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
