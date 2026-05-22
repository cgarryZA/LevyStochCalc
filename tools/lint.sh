#!/usr/bin/env bash
# Project lint: lake build must succeed + every load-bearing theorem in
# _audit.lean must be axiom-clean (no NEW sorryAx beyond the baseline).
#
# The baseline is `tools/sorry_baseline.txt` — a list of theorems that are
# KNOWN to currently depend on sorryAx (work in progress). New sorries
# (theorems with sorryAx not in the baseline) cause the lint to FAIL.
# When you prove one of these baseline sorries, REMOVE its name from the
# baseline file.
#
# Run manually:  ./tools/lint.sh
# Wire into pre-commit:  cp tools/lint.sh .git/hooks/pre-commit
set -euo pipefail

cd "$(git rev-parse --show-toplevel 2>/dev/null)" || cd "$(dirname "$0")/.."

echo "==> lake build"
lake build

echo "==> running _audit.lean"
if [[ ! -f _audit.lean ]]; then
  echo "FAIL: _audit.lean missing — cannot run axiom audit (red-team finding C9)."
  exit 1
fi
lake env lean _audit.lean > audit_output.txt 2>&1 || true
if [[ ! -s audit_output.txt ]]; then
  echo "FAIL: _audit.lean produced empty audit_output.txt — audit did not run."
  exit 1
fi
# Verify the audit actually ran (output contains at least one axiom-set line).
if ! grep -q "depends on axioms" audit_output.txt; then
  echo "FAIL: audit_output.txt does not contain '#print axioms' output."
  echo "      _audit.lean may have failed to elaborate. First 30 lines:"
  head -30 audit_output.txt | sed 's/^/  /'
  exit 1
fi

# Extract theorems whose axiom set contains sorryAx.
# Force LF line endings (sys.stdout reconfigure) to match the baseline file
# on Windows hosts where Python defaults to CRLF.
CURRENT_SORRIES=$(python3 -c "
import re, sys
sys.stdout.reconfigure(newline='\n')
content = open('audit_output.txt').read()
pattern = re.compile(r\"'([^']+)' depends on axioms: \[([^\]]+)\]\", re.DOTALL)
seen = set()
for match in pattern.finditer(content):
    name = match.group(1)
    deps = match.group(2)
    if 'sorryAx' in deps and name not in seen:
        seen.add(name)
        print(name)
" | tr -d '\r' | sort -u)

# Compare against baseline.
BASELINE_FILE="tools/sorry_baseline.txt"
if [[ ! -f "$BASELINE_FILE" ]]; then
  echo "ERROR: missing $BASELINE_FILE — cannot compare against baseline."
  exit 1
fi
BASELINE=$(tr -d '\r' < "$BASELINE_FILE" | sort -u)

# New sorries = current minus baseline.
NEW_SORRIES=$(comm -23 <(echo "$CURRENT_SORRIES") <(echo "$BASELINE"))

if [[ -n "$NEW_SORRIES" ]]; then
  echo "FAIL: new sorryAx-tainted theorems beyond baseline:"
  echo "$NEW_SORRIES" | sed 's/^/  /'
  echo ""
  echo "If intentional, add them to $BASELINE_FILE."
  exit 1
fi

# Resolved sorries = baseline minus current. (Informational only.)
RESOLVED=$(comm -13 <(echo "$CURRENT_SORRIES") <(echo "$BASELINE"))
if [[ -n "$RESOLVED" ]]; then
  echo "INFO: theorems in baseline that no longer have sorryAx (good!):"
  echo "$RESOLVED" | sed 's/^/  /'
  echo "  -> Remove them from $BASELINE_FILE to tighten the baseline."
fi

echo "PASS: lake build + audit at or below baseline."
