#!/bin/bash
# SessionStart hook — provisions the Lean 4 + Mathlib toolchain so that
# `lake build`, `tools/lint.sh`, and `tools/verify_import_contract.sh` work in
# Claude Code on the web. Idempotent, non-interactive, and degrades gracefully
# if a required host is not on the environment's network egress allowlist.
#
# Strategy: install elan (Lean toolchain manager), materialise the toolchain
# pinned in `lean-toolchain`, then pull Mathlib's prebuilt `.olean` cache
# (`lake exe cache get`) so Mathlib is NOT recompiled. Only the LevyStochCalc
# files themselves compile after that.
#
# REQUIRED EGRESS HOSTS (add these in the environment's network settings):
#   • release.lean-lang.org             — Lean toolchain downloads (elan)
#   • lakecache.blob.core.windows.net   — Mathlib prebuilt olean cache
#   • reservoir.lean-lang.org           — Lake package registry (if used)
#   (github.com / raw.githubusercontent.com are typically already allowed.)
set -uo pipefail   # NOTE: no -e — a blocked download must not abort startup.

# Local dev machines already have a toolchain — only provision the web container.
if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

# Async: provision in the background so session startup isn't blocked by the
# (sizable) Mathlib cache download. This control line MUST be the first stdout.
echo '{"async": true, "asyncTimeout": 600000}'

PROJ="${CLAUDE_PROJECT_DIR:-$(cd "$(dirname "${BASH_SOURCE[0]}")/../.." && pwd)}"

# Persist elan/lake on PATH for the whole session.
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  echo 'export PATH="$HOME/.elan/bin:$PATH"' >> "$CLAUDE_ENV_FILE"
fi
export PATH="$HOME/.elan/bin:$PATH"

note() { echo "session-start: $*"; }

allowlist_help() {
  note "A required host is not on the network egress allowlist. Add these in"
  note "the environment's network settings, then start a new session:"
  note "  • release.lean-lang.org            (Lean toolchain)"
  note "  • lakecache.blob.core.windows.net  (Mathlib olean cache)"
  note "  • reservoir.lean-lang.org          (Lake registry, if used)"
  note "Docs: https://code.claude.com/docs/en/claude-code-on-the-web"
}

# 1. Install elan if absent (from raw.githubusercontent.com — usually allowed).
if ! command -v elan >/dev/null 2>&1; then
  if ! curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
       | sh -s -- -y --default-toolchain none; then
    note "elan install failed (network?). Skipping provisioning."
    exit 0
  fi
  export PATH="$HOME/.elan/bin:$PATH"
fi

# 2. Materialise the toolchain pinned by `lean-toolchain`.
if ! elan toolchain install "$(tr -d '[:space:]' < "$PROJ/lean-toolchain")"; then
  note "Could not install the Lean toolchain."
  allowlist_help
  exit 0
fi

cd "$PROJ"

# 3. Pull Mathlib's prebuilt oleans (avoids a multi-hour Mathlib recompile).
if ! lake exe cache get; then
  note "'lake exe cache get' failed."
  allowlist_help
  note "Without the cache, 'lake build' would recompile Mathlib from source."
  exit 0
fi

note "Provisioning complete. Mathlib cached; run 'lake build' to compile LevyStochCalc."
# A full `lake build` (8402 jobs) is intentionally NOT run here — it would block
# session startup. Build on demand; Mathlib is already cached.
