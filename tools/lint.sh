#!/usr/bin/env bash
# Project lint: `lake build` must succeed, `_audit.lean` must run to completion, and its
# `#print axioms` transcript must pass tools/audit_check.py — no `: error` line, a report for
# every audited name, every axiom inside {propext, Classical.choice, Quot.sound} ∪
# tools/axiom_allowlist.txt, and `sorryAx` only on names in tools/sorry_baseline.txt (the
# baseline is empty; a new sorry fails). Finally tools/check_docs.sh checks that the pins and
# counts quoted in the prose match the tree.
#
# The transcript check can be replayed on a saved transcript without a build:
#   python3 tools/audit_check.py audit_output.txt _audit.lean tools/axiom_allowlist.txt \
#     --sorry-baseline tools/sorry_baseline.txt
#
# A pass certifies the logical trust base of the audited declarations (the kernel axioms they
# reduce to). It does not certify the mathematical coverage or grounding of their statements.
#
# Run manually:  bash tools/lint.sh
set -euo pipefail

cd "$(git rev-parse --show-toplevel 2>/dev/null)" || cd "$(dirname "$0")/.."

echo "==> lake build"
lake build

echo "==> running _audit.lean"
if [[ ! -f _audit.lean ]]; then
  echo "FAIL: _audit.lean missing — cannot run the axiom audit."
  exit 1
fi
set +e
lake env lean _audit.lean > audit_output.txt 2>&1
AUDIT_EXIT=$?
set -e
if [[ ! -s audit_output.txt ]]; then
  echo "FAIL: _audit.lean produced an empty audit_output.txt — the audit did not run."
  exit 1
fi
if (( AUDIT_EXIT != 0 )); then
  echo "FAIL: lake env lean _audit.lean exited $AUDIT_EXIT. Error lines:"
  grep -n ': error' audit_output.txt | head -20 | sed 's/^/  /' || true
  exit 1
fi

echo "==> checking audit_output.txt (errors, coverage, axiom allowlist, sorry baseline)"
python3 tools/audit_check.py audit_output.txt _audit.lean tools/axiom_allowlist.txt \
  --sorry-baseline tools/sorry_baseline.txt

echo "==> tools/check_docs.sh"
bash tools/check_docs.sh

echo "PASS: lake build, _audit.lean transcript, and documentation pins."
