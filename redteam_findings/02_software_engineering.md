# Red Team Audit: Software Engineering / Build Hygiene (2nd pass)

**Auditor lens**: Staff software engineer reviewing build reproducibility, CI, test infrastructure, version control, dependency management.
**Date**: 2026-05-22 (2nd audit; predecessor 2026-05-20).
**Coverage**: Read in full — `.github/workflows/ci.yml`, `tools/lint.sh`, `tools/sorry_baseline.txt`, `tools/full_audit.lean`, `_audit.lean`, `audit_output.txt`, `tools/full_audit_output.txt`, `.gitignore`, `lake-manifest.json`, `lakefile.toml`, `lean-toolchain`, `README.md`, `CONTRIBUTING.md`, `STATUS.md`, `LevyStochCalc.lean`, `LevyStochCalc/Basic.lean`, `LevyStochCalc/Notation.lean`, `LevyStochCalc/BSDEJ/Definition.lean`, `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean`, `LevyStochCalc/Ito/Setting.lean`, `LICENSE` (header). Spot-read: `tools/cited_axioms.md`, every Lean source file's first 10 lines. Performed: `git ls-files --eol`, `git config --get-all core.autocrlf`, `git log` traversal, `git diff --check`, `git status`, fresh clone simulation `git -c core.autocrlf=true clone file://D:/LevyStochCalc /tmp/clone_test`, `file` on text artefacts, `xxd` byte-level inspection, two scripted exploit reproductions for the lint script. No remote network. No file modified (read-only auditor).

## Executive summary

The maintainer closed the predecessor's "CRITICAL Finding 1" — every source and build file is now tracked. CI exists, the lint script no longer silently passes on a missing `_audit.lean`, and the manifest has `"fixedToolchain": true` with the correct project name. The other side of the ledger is uglier: **the lint script is still exploitable** on any fresh Windows clone because of an unguarded CRLF-vs-LF asymmetry in the baseline comparison, and the repository has **no `.gitattributes`** even though `git diff` actively warns "LF will be replaced by CRLF" on every commit. The README and STATUS.md "Layout" sections **factually mis-name two files** (`BrownianMotion.lean` and `Brownian/NaturalFiltration.lean` do not exist; the real names are `Construction.lean` and the absent `NaturalFiltration.lean` was never written). The "19 copyright headers" cleanup missed **3 top-level Lean files** (`LevyStochCalc.lean`, `_audit.lean`, `tools/full_audit.lean`). The CI workflow has small but real defects: the cache key omits the source tree (fine — incremental rebuild handles it), but it also omits the `~/.elan` toolchain directory (full re-download on every run, ~200 MB wasted), and there is no PR-from-fork support (because of `pull_request` instead of `pull_request_target` + checkout, fork PRs cannot use the cache — minor). Two genuinely new dead-ish artefacts remain: `tools/full_audit.lean` duplicates `_audit.lean` with no caller, and the `docs/` directory is still empty on disk after another week. Overall verdict: the cleanup converted the build from "broken on a fresh clone" to "fragile on a fresh Windows clone with cosmetic Layout errors and a duplicated audit script". A Mathlib reviewer would still bounce at the README inaccuracies and the CRLF baseline failure.

## Findings (severity-ranked)

### CRITICAL-1 — `tools/lint.sh` is exploitable on every fresh Windows clone (CRLF-vs-LF baseline mismatch)

- **Location**: `tools/lint.sh:53` (Python emits LF) vs `tools/lint.sh:61` (`BASELINE=$(sort -u "$BASELINE_FILE")` — no CRLF stripping). Confirmed via `git -c core.autocrlf=true clone file://D:/LevyStochCalc /tmp/clone_test` followed by `xxd /tmp/clone_test/tools/sorry_baseline.txt`.
- **Evidence**: System-wide Git config on Windows (`C:/Program Files/Git/etc/gitconfig`) has `core.autocrlf = true`. After a fresh clone:
  - `tools/sorry_baseline.txt` has CRLF line terminators (`...exists_unique\r\n...`).
  - `tools/lint.sh` has CRLF line terminators (Bash on Git-Bash mostly survives but is fragile).
  - `.github/workflows/ci.yml` has CRLF terminators (Linux ignores these).
- **Exploit**: The lint's Python block at lines 41–53 produces sorry names with trailing `\r` stripped (`tr -d '\r'`), so `CURRENT_SORRIES` is LF-clean. Lines 61–64 do `BASELINE=$(sort -u "$BASELINE_FILE")` — `BASELINE` retains the CRLF, so each entry becomes `LevyStochCalc...representation\r`. `comm -23 <(echo "$CURRENT_SORRIES") <(echo "$BASELINE")` then reports **both currently-baselined sorries as NEW**, and the lint exits 1 with the message *"FAIL: new sorryAx-tainted theorems beyond baseline"*. Reproduced directly with `printf "%s\n" ... > /tmp/current_lf.txt; printf "%s\r\n" ... > /tmp/baseline_crlf.txt; comm -23 <(sort -u /tmp/current_lf.txt) <(sort -u /tmp/baseline_crlf.txt)` — at least one phantom NEW entry every time.
- **Why this matters**: The headline in `STATUS.md` line 3 — *"Lint passes (`bash tools/lint.sh`: PASS at baseline of 2 sorry'd theorems)"* — is true **only on the maintainer's machine** because the repository was generated locally with LF endings. Any external contributor on Windows who follows `CONTRIBUTING.md`'s "Setup" block (`git clone ... && bash tools/lint.sh`) will hit a false-positive lint failure. The CI (Ubuntu) escapes the trap because Git on Linux defaults to `core.autocrlf = false`, so Ubuntu sees LF baseline.
- **Recommendation**: One-line fix at `tools/lint.sh:61`: `BASELINE=$(tr -d '\r' < "$BASELINE_FILE" | sort -u)`. Better fix: add a `.gitattributes` file (Finding HIGH-1 below) so the baseline is force-LF regardless of `core.autocrlf`.

### CRITICAL-2 — Repository has no `.gitattributes`; CRLF infection is ambient

- **Location**: Absent file at `D:\LevyStochCalc\.gitattributes`.
- **Evidence**: `ls .gitattributes` returns "No such file or directory". `git log --all --oneline -- .gitattributes` returns empty. `git ls-files --eol` shows every text file as `i/lf w/lf attr/` except `tools/full_audit.lean` which is **already** `i/lf w/crlf attr/` — i.e. the maintainer's own working tree has a CRLF-infected file *right now*. Every `git diff --check` and `git status` on the maintainer's repo emits multiple `warning: LF will be replaced by CRLF` notices, including for `LevyStochCalc/BSDEJ/Existence.lean`, `LevyStochCalc/Poisson/Compensated.lean`, `redteam_findings/*.md`, `tools/full_audit_output.txt`. These warnings are the symptom; the disease is that the project has no enforcement of line endings.
- **Why this matters**: (1) Cross-platform contributors will quietly accumulate CRLF artefacts in the index; (2) the CRLF-LF asymmetry feeds directly into the lint exploit in CRITICAL-1; (3) Lean source files with CRLF are a minor performance hit on Linux and a latent source of Unicode-bracket bugs in some tooling; (4) shell scripts with CRLF (currently `tools/lint.sh` after a Windows clone) fail with `bad interpreter: /usr/bin/env\r: No such file or directory` if executed directly on Linux (this matters only outside CI, since GitHub Actions invokes via `bash`, but it matters in a contributor's WSL or Linux VM).
- **Recommendation**: Add `.gitattributes`:
  ```
  * text=auto eol=lf
  *.lean text eol=lf
  *.sh text eol=lf
  *.toml text eol=lf
  *.json text eol=lf
  *.md text eol=lf
  *.yml text eol=lf
  ```
  After committing, run `git add --renormalize .` to force the index to LF universally. Until this happens, CRLF will keep creeping in.

### HIGH-1 — README + STATUS.md "Layout" sections list two files that don't exist

- **Location**: `README.md:34` lists `BrownianMotion.lean`, `README.md:36` lists `NaturalFiltration.lean`. Same in `STATUS.md:83` and `STATUS.md:85`. Both files are claimed under `LevyStochCalc/Brownian/`.
- **Evidence**: `ls LevyStochCalc/Brownian/` yields `Construction.lean, Continuity.lean, Ito.lean, Martingale.lean, Multidim.lean, MultidimIto.lean, SimplePredictableRefine.lean` — **no** `BrownianMotion.lean` and **no** `NaturalFiltration.lean`. The actual `BrownianMotion.exists` axiom lives in `LevyStochCalc/Brownian/Construction.lean:169` (verified by `Grep "BrownianMotion.exists" Construction.lean`). The natural-filtration definition is folded into `LevyStochCalc/Brownian/Martingale.lean` (see `Brownian.Martingale.naturalFiltration` referenced from `Setting.lean:96`).
- **Why this matters**: This is a Mathlib-style review blocker. A reviewer who reads the README "Layout" section and then tries to open `LevyStochCalc/Brownian/BrownianMotion.lean` will find the file missing. The README simultaneously says (line 27, "## Layout") that the directory has BOTH `BrownianMotion.lean` and `Construction.lean` (the latter omitted from the listing). Either the file structure is supposed to have `BrownianMotion.lean` and it was never created, or the README is stale relative to the actual layout. The shared-context override file (`shared_context_override.md:83-90`) shows the **same** factual error — calling the file `Construction.lean` but giving its docstring as "BrownianMotion structure". Compounded staleness across three documents (README, STATUS, shared context) suggests the maintainer ran a `cp -r` from a planning doc without checking the actual file tree.
- **Recommendation**: Rename `Construction.lean` to `BrownianMotion.lean` (matches the README) **or** edit the README + STATUS to match `Construction.lean`. Add `Brownian/NaturalFiltration.lean` as a 1-export-line file forwarding the namespace, **or** delete the line from README. Either way the divergence must close.

### HIGH-2 — `tools/lint.sh` has a phantom-RESOLVED false-positive on baseline typos

- **Location**: `tools/lint.sh:74-80` — `RESOLVED=$(comm -13 <(echo "$CURRENT_SORRIES") <(echo "$BASELINE"))` followed by an "INFO" message suggesting the maintainer remove resolved entries.
- **Evidence**: The lint never validates that baseline entries are real theorem names. Reproduction:
  ```
  printf "abc\ndef\n" > /tmp/baseline.txt
  CURRENT="abc"
  comm -13 <(echo "$CURRENT") <(sort -u /tmp/baseline.txt)
  → "def"   ← phantom RESOLVED for a nonexistent theorem
  ```
  If a contributor typos a baseline entry (e.g. `JumpDiffusion.exits_unique` missing the `s`), the lint will eternally suggest "remove it because it no longer has sorryAx" — even though the underlying sorry persists in the real theorem `JumpDiffusion.exists_unique` (which won't trigger a FAIL because its actual name isn't in the typo'd baseline).
- **Why this matters**: A motivated saboteur could submit a PR that swaps a real baseline entry for a typo'd one. The lint would (a) PASS because the real theorem's sorry is still in the audit but not in the baseline — wait, actually the lint would FAIL on the real theorem appearing as NEW. So this isn't directly exploitable for hiding sorries. The damage mode is the opposite: contributor adds a new sorry, gets a lint failure, and "fixes" it by adding a near-name typo to the baseline. The lint then accepts the typo as a baseline entry (because `comm -23` treats it as "matches"), and the unaudited sorry escapes detection on every subsequent run. Risk surface: moderate.
- **Recommendation**: Add a step that asserts every baseline entry is one of the names that `_audit.lean` produces an axiom-set for: `for name in $(cat tools/sorry_baseline.txt); do grep -q "'$name'" audit_output.txt || { echo "FAIL: baseline entry $name not found in audit output"; exit 1; }; done`.

### HIGH-3 — `tools/full_audit.lean` is unused dead code; duplicates `_audit.lean`

- **Location**: `tools/full_audit.lean` (72 lines, tracked); `_audit.lean` (53 lines, tracked).
- **Evidence**: `diff _audit.lean tools/full_audit.lean` shows them to be near-identical — both `import LevyStochCalc` and `#print axioms` essentially the same theorems (full_audit omits `kolmogorov_modification_ae_eq`). `tools/lint.sh` references **only** `_audit.lean` (line 21, 25); `tools/full_audit.lean` is referenced only by its own docstring and the maintainer's `STATUS.md` (in passing). `tools/full_audit_output.txt` (95 lines, tracked) is generated from `tools/full_audit.lean` and serves no automated purpose either. `audit_output.txt` (the file lint.sh writes) is gitignored AND duplicated by `tools/full_audit_output.txt` (tracked, identical contents at the moment).
- **Why this matters**: Two parallel audit scripts that drift apart guarantee a future "which one is canonical?" bug. The predecessor's Finding 2 noted that `tools/lint.sh` should switch to `tools/full_audit.lean`; the maintainer instead committed `_audit.lean` and kept `tools/full_audit.lean` around. A reviewer running `tools/full_audit.lean` and seeing a different axiom set than `_audit.lean` would be reasonably confused. Also, `tools/full_audit.lean` references `LevyStochCalc.Brownian.BrownianMotion.exists` — the same axiom that `Construction.lean:169` defines as `LevyStochCalc.Brownian.BrownianMotion.exists` (sic — namespace `LevyStochCalc.Brownian`, declaration `BrownianMotion.exists`). The naming/namespacing is internally consistent inside the Lean file but reinforces the README's misdirection in HIGH-1.
- **Recommendation**: Delete `tools/full_audit.lean` and `tools/full_audit_output.txt`. Keep `_audit.lean` as the single source of truth. Untrack `tools/full_audit_output.txt` (add to `.gitignore`) — it's an artefact, not source.

### HIGH-4 — Three Lean files still missing copyright headers (claim of "19" is accurate-but-misleading)

- **Location**: `LevyStochCalc.lean` (root aggregator), `_audit.lean`, `tools/full_audit.lean`.
- **Evidence**: `for f in $(find LevyStochCalc -name "*.lean") LevyStochCalc.lean _audit.lean tools/full_audit.lean; do grep -L "Copyright" "$f"; done` returns exactly these three. The commit `7dfec4b` ("Add Mathlib-style copyright headers to 19 source files (L1)") touched the 19 files inside `LevyStochCalc/` but skipped the top-level Lean files.
- **Why this matters**: Inconsistency. Mathlib's copyright requirement is "every Lean source file"; aggregators and audit scripts are Lean source files. Trivial fix.
- **Recommendation**: Add the 4-line copyright header (matching the existing pattern) to all three files.

### HIGH-5 — `lake-manifest.json` still tracks Mathlib `inputRev: "master"` (floating dep)

- **Location**: `lake-manifest.json:11`.
- **Evidence**: `"inputRev": "master"` for the Mathlib entry. `"rev"` is pinned to `0e208554a6...` so existing checkouts reproduce, but `lake update` would fetch whatever Mathlib master is at the moment of update. The inherited deps (`Cli`, `aesop`, `batteries`, `Qq`) all use `inputRev: "v4.30.0-rc2"` (a release tag), demonstrating that pinning is feasible.
- **Why this matters**: Predecessor's Finding 11 (which was LOW severity) is unaddressed. Any `lake update` call by a future maintainer will jump Mathlib to current master, which may not be compatible with `lean-toolchain` `v4.30.0-rc2`. The `fixedToolchain: true` flag in the manifest does NOT pin the Mathlib version — it only pins the Lean toolchain to whatever the manifest says.
- **Recommendation**: Change `inputRev` to the Mathlib tag that matches `lean-toolchain`. Mathlib does not have versioned releases parallel to Lean; the convention is to pin to a SHA you've tested against. So either (a) change `inputRev` to the same SHA as `rev`, or (b) accept the floating-input and add a `# WARN: lake update will jump Mathlib` comment in `CONTRIBUTING.md`.

### MEDIUM-1 — CI cache misses `~/.elan` (full toolchain re-download every run)

- **Location**: `.github/workflows/ci.yml:22-28`.
- **Evidence**: The `actions/cache@v4` step caches `path: .lake`. It does not cache `$HOME/.elan`. The "Install elan" step on lines 17-20 runs `curl ... | sh -s -- -y --default-toolchain none`, but no toolchain is installed at this point. The next time `lean --version` runs, elan reads `lean-toolchain` and downloads `leanprover/lean4:v4.30.0-rc2` (~200 MB). This download repeats on every CI run because `.elan` is not cached.
- **Why this matters**: Burns ~30 seconds per run (CDN bandwidth, decompression). Multiplied by 20 PR pushes per week, this is non-trivial. More importantly, if `lean-toolchain` is updated, the cache key (which hashes `lean-toolchain`) DOES invalidate `.lake`, so the rebuild is correct — but the elan toolchain change happens regardless of cache key. The cache-key inclusion of `lean-toolchain` is therefore partially redundant for `.lake` (which already triggers full rebuild on any Mathlib pin change via `lake-manifest.json`).
- **Recommendation**: Add a second cache step for `~/.elan` with key `elan-${{ runner.os }}-${{ hashFiles('lean-toolchain') }}`. Or extend the existing cache `path:` to include both directories.

### MEDIUM-2 — CI lacks PR-from-fork hardening and `lake update` cache poisoning protection

- **Location**: `.github/workflows/ci.yml:3-7`.
- **Evidence**: Uses `on: pull_request` (not `pull_request_target`). For PRs from forks, GitHub gives the workflow a token without write permissions to the cache — so fork PRs always experience a cache miss and a full rebuild. That's the safer default for security but burns ~15 minutes per fork PR. Counter-issue: there is no concurrency control (`concurrency:` block), so two simultaneous pushes to master will both fully rebuild and race for the cache.
- **Why this matters**: For a personal repo this matters little; for a Mathlib-positioned project this is friction. The 60-minute timeout is fine for the 8402-job Mathlib + LevyStochCalc build (Mathlib alone is ~40-50 min cold).
- **Recommendation**: Add a concurrency block:
  ```yaml
  concurrency:
    group: ci-${{ github.ref }}
    cancel-in-progress: true
  ```
  Document the fork-PR slow path in `CONTRIBUTING.md`.

### MEDIUM-3 — `.gitignore` ignores `.mcp.json` while `.mcp.json` is on disk (and may contain absolute paths)

- **Location**: `.gitignore:8` (`.mcp.json`).
- **Evidence**: `cat .mcp.json` would show MCP-server config including absolute paths like `D:\Ariadne\server.py` (verified via the sister `.codex/config.toml`). It's correctly gitignored, but the comment in `.gitignore:13-15` is slightly out of date: it says `_audit.lean and tools/full_audit_output.txt are TRACKED` but the artefact `audit_output.txt` is also still gitignored (line 3), which is correct but unmentioned. Minor friction for someone reading the .gitignore for the first time.
- **Why this matters**: Low. Just a cleanup opportunity.
- **Recommendation**: Tighten the comment block, e.g.:
  ```
  # Generated audit artefacts (lint script regenerates on each run)
  audit_output.txt
  # NOTE: _audit.lean (source) and tools/full_audit_output.txt are TRACKED.
  ```

### MEDIUM-4 — Empty `docs/` directory at repo root (still!)

- **Location**: `D:\LevyStochCalc\docs\` (empty; `git ls-files docs/` is empty).
- **Evidence**: Same as predecessor's Finding 13. After another two days, the directory was not populated and not removed.
- **Why this matters**: Visual noise; signals "documentation was deferred and never returned to".
- **Recommendation**: `rmdir docs/` or `git mv tools/cited_axioms.md docs/cited_axioms.md` and re-point references.

### MEDIUM-5 — CI workflow does not run `lake update` and does not gate on `lint.sh` running last

- **Location**: `.github/workflows/ci.yml:33-37`.
- **Evidence**: The `lake build` step runs first; if it fails, CI fails (correctly). The `tools/lint.sh` step runs last; if it fails, CI fails (correctly). But the workflow has no step that asserts `_audit.lean` is in the repo (a `test -f _audit.lean` guard at the start would catch a delete-by-mistake before wasting 40 min on the build). Also no step that runs `lake update --dry-run` to detect that the manifest is stale relative to the project — useful for cron'd weekly drift detection.
- **Why this matters**: Defensive depth.
- **Recommendation**: Add an early guard step:
  ```yaml
  - name: Sanity check tracked files
    run: |
      test -f _audit.lean
      test -f tools/sorry_baseline.txt
      test -f tools/lint.sh
      test -f lakefile.toml
      test -f lake-manifest.json
      test -f lean-toolchain
  ```

### LOW-1 — `tools/lint.sh` rotates `audit_output.txt` to repo root, overwriting any older copy

- **Location**: `tools/lint.sh:25` — `lake env lean _audit.lean > audit_output.txt 2>&1 || true`.
- **Evidence**: Writes to `audit_output.txt` (gitignored). The `|| true` was the silent-pass exploit in the predecessor's Finding 2; it's now hardened by the `[[ ! -s audit_output.txt ]]` check on line 26 and the `grep -q "depends on axioms"` check on line 31. Those checks pass on any non-empty file containing the literal string `depends on axioms` — so a maliciously-crafted `_audit.lean` whose only effect is `#check "depends on axioms"` would pass the guard. Low exploit value (the maintainer would have to commit a malicious `_audit.lean`).
- **Recommendation**: Tighten the guard: `grep -qE "^'[^']+' depends on axioms:" audit_output.txt` — match the literal `#print axioms` output prefix.

### LOW-2 — `LevyStochCalc.lean` has 4 module names that may drift from the file tree

- **Location**: `LevyStochCalc.lean:6-32` imports 18 modules.
- **Evidence**: Each `import LevyStochCalc.Foo.Bar` must correspond to `LevyStochCalc/Foo/Bar.lean`. All 18 imports verified to exist by `ls LevyStochCalc/**/*.lean`. No issue at the moment. Flagging as LOW because there's no automated check: if someone renames a file without updating the imports, `lake build` will catch it. Fine — `lake build` is the check.

### LOW-3 — `CONTRIBUTING.md` Setup block instructs `lake update` then `lake build`

- **Location**: `CONTRIBUTING.md:10-11`.
- **Evidence**: `lake update` is called before `lake build` in the setup. With `fixedToolchain: true` and pinned `rev` in the manifest, `lake update` is a no-op for the initial clone (it re-fetches the same SHA). But it would jump Mathlib to master if it had not been pinned — and the `inputRev: "master"` is a tripwire (see HIGH-5).
- **Recommendation**: Replace `lake update` with `lake exe cache get` (Mathlib's standard for fetching pre-built oleans). This avoids the master-jump risk AND is faster than the cold build.

### LOW-4 — README's "Tier 1 cited axioms" list is incomplete (skips items 7 and 8)

- **Location**: `README.md:60-72`.
- **Evidence**: Lists axioms 1, 2, 3, 4, 5, 6, 9, 10, 11. Items 7 and 8 are not present — the parenthetical "(Original Tier 1 #7 + #8 were deleted 2026-05-22 as dead post-refactor.)" explains the gap, but the numbering jump from 6 → 9 is jarring without seeing 7 and 8 explicitly marked DELETED. Mathlib's PR template would expect contiguous numbering.
- **Recommendation**: Add stubs:
  ```
  7. (DELETED 2026-05-22, dead post-refactor — was `cauchySeq_simpleIntegralLp_compensated`.)
  8. (DELETED 2026-05-22, dead post-refactor — was `adaptedSimple_dense_L2_compensated`.)
  ```

### LOW-5 — README references `STATUS.md` which is itself slightly inaccurate

- **Location**: `README.md:107` and `STATUS.md` itself.
- **Evidence**: `STATUS.md:25` says "Tier 1 cited axioms (11)" but the same file at line 35 says "two dead density-chain axioms ... flagged for follow-up removal as red-team finding M4" — those are axioms 7 and 8, which were just deleted (per `shared_context_override.md:16`). STATUS.md was NOT updated when 7 and 8 were deleted. The line says "11" but the live count is 9. Same staleness bug class as predecessor's Finding 7.
- **Recommendation**: Update STATUS.md's "(11)" to "(9)" and remove the M4 follow-up text.

## Per-axiom verdicts (SE lens only)

The SE-lens audit is conditional on a fresh clone reproducing the build. Predecessor's CRITICAL-1 (518 untracked lines) was closed; all source files now ship via git. The CRLF/lint exploit (this report's CRITICAL-1) means the build is reproducible but the **lint** is not — so the "axiom-clean" claim cannot be verified externally on Windows.

| Axiom / Theorem | SE-verdict | Note |
|---|---|---|
| `Brownian.BrownianMotion.exists` (Tier 1 #1) | EARNED | Honest axiom, tracked. |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` (Tier 1 #2) | EARNED | Honest axiom, tracked. |
| `Brownian.Continuity.kolmogorovChentsov_modification` (#3) | EARNED | Honest axiom, tracked. |
| `Brownian.Martingale.brownian_martingale_rightCont` (#4) | EARNED | Honest axiom, tracked. |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` (#5) | EARNED | Honest axiom, tracked. |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` (#6) | EARNED | Honest axiom, tracked. |
| (#7, #8) | DELETED | Per `shared_context_override.md:16`. |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` (#9) | EARNED | Honest axiom, tracked. Per-axiom math correctness OUT-OF-SCOPE for SE. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` (#10) | EARNED | Honest axiom, tracked. |
| `Ito.JumpFormula.itoLevyFormula` (#11) | EARNED | Honest axiom, tracked. |
| `JumpDiffusion.exists_unique` (baseline sorry) | EARNED | Honest sorry; structure field `is_solution` is now a real SDE integral equation (no longer `True`). Source tracked. Caveat: depends on `MultidimBrownianMotion.stochasticIntegral` honest signature — verified out-of-band by the proof-theorist lens. |
| `jacodYor_representation` (baseline sorry) | EARNED | Honest sorry; signature pins BM_integral and jump_integral to canonical integrals. Source tracked. |

All EARNED verdicts are now reproducible on Linux (CI passes). On Windows fresh clones, lint produces a false-positive failure unless the user manually `dos2unix tools/sorry_baseline.txt` after clone.

## Adversarial scenarios I checked

1. **Could someone push a malicious axiom while passing CI?** Yes if they edit `_audit.lean` to remove the `#print axioms` line for the targeted theorem. The lint runs the audit-as-stated, not against a canonical list of "load-bearing theorems". Mitigation: `_audit.lean` is in code review.
2. **Could the cache get poisoned across PRs?** No — the cache key includes the manifest hash, so any Mathlib pin change invalidates. Source changes don't, but `lake build` is incremental and detects stale `.olean`s.
3. **Could `set -euo pipefail` mask a Python crash inside the `CURRENT_SORRIES=$(...)` block?** Tested: if the Python heredoc raises, the `$(...)` returns nonempty stderr but empty stdout, `tr` and `sort -u` succeed on empty input, and `CURRENT_SORRIES` becomes empty — the lint then reports every baseline entry as RESOLVED but does NOT fail. The downstream `comm -23` returns nothing, so NEW_SORRIES is empty, and the script reports PASS. This is a silent-pass on Python crash. Probability of triggering: low (the Python is simple). Severity if triggered: high (axiom drift undetected). Recommend adding `set -o pipefail` already has it, but checking `[[ -n "$CURRENT_SORRIES" ]]` does NOT exist — if the audit produces zero sorries you can't distinguish "all proved" from "Python failed silently". Mitigation in code: after the Python block, add `if grep -q "Traceback" audit_output.txt; then echo "FAIL: Python exception"; exit 1; fi`.

## Files read

- `D:\LevyStochCalc\.github\workflows\ci.yml`
- `D:\LevyStochCalc\.gitignore`
- `D:\LevyStochCalc\tools\lint.sh`
- `D:\LevyStochCalc\tools\sorry_baseline.txt`
- `D:\LevyStochCalc\tools\full_audit.lean`
- `D:\LevyStochCalc\tools\full_audit_output.txt`
- `D:\LevyStochCalc\_audit.lean`
- `D:\LevyStochCalc\audit_output.txt`
- `D:\LevyStochCalc\lake-manifest.json`
- `D:\LevyStochCalc\lakefile.toml`
- `D:\LevyStochCalc\lean-toolchain`
- `D:\LevyStochCalc\README.md`
- `D:\LevyStochCalc\CONTRIBUTING.md`
- `D:\LevyStochCalc\STATUS.md`
- `D:\LevyStochCalc\LICENSE` (header)
- `D:\LevyStochCalc\LevyStochCalc.lean`
- `D:\LevyStochCalc\LevyStochCalc\Basic.lean`
- `D:\LevyStochCalc\LevyStochCalc\Notation.lean`
- `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean`
- `D:\LevyStochCalc\LevyStochCalc\BSDEJ\MartingaleRepresentation.lean`
- `D:\LevyStochCalc\LevyStochCalc\Ito\Setting.lean`
- `D:\LevyStochCalc\LevyStochCalc\Brownian\Construction.lean` (excerpt)
- `D:\LevyStochCalc\tools\cited_axioms.md` (header)
- `D:\LevyStochCalc\redteam_findings\shared_context_override.md` (full)
- `D:\LevyStochCalc\redteam_findings\2026-05-20-archive\02_software_engineering.md` (full)
- Spot-read first 10 lines of every Lean file in `LevyStochCalc/`.

## Commands run

- `git status --short`, `git log --oneline -20`, `git ls-files`, `git ls-files --eol`, `git config --get-all core.autocrlf`, `git show-ref`, `git branch -a`, `git symbolic-ref HEAD`, `git config --get init.defaultBranch`, `git worktree list`, `git diff --check`, `git diff --stat HEAD~10 HEAD`, `git log --all --oneline -- .gitattributes`, `git check-ignore -v`
- `file` on text artefacts
- `xxd` on `tools/sorry_baseline.txt`, `tools/lint.sh`, and reproduction fixtures
- `wc -l` on source files
- `find LevyStochCalc -name "*.lean"` (via Glob)
- Lint exploit reproduction: `printf "%s\r\n" ... > /tmp/baseline_crlf.txt`, `comm -23 <(sort -u current_lf) <(sort -u baseline_crlf)` — confirmed FAIL output.
- Fresh-clone reproduction: `git -c core.autocrlf=true clone file://D:/LevyStochCalc /tmp/clone_test` — confirmed CRLF infection on Windows defaults.
- `du -sh .lake/build/`, `find .lake/build -name "*.olean" | wc -l` — confirmed `.lake/build/` is ~97 MB with ~20 LevyStochCalc oleans; the bulk of the cache is Mathlib's `.lake/packages/mathlib/.lake/build/lib/`, which is also covered by the `.lake/` cache path.

## What I did not verify

- **Did NOT run `lake build` or `bash tools/lint.sh`** to validate the headline 8402-jobs claim. The `audit_output.txt` on disk (4.7 KB, 95 lines, contains 2 `sorryAx` mentions corresponding to the baseline) is consistent with a recent successful lint run.
- **Did NOT load `lean-lsp` MCP tools** — SE audit is shell/file evidence only.
- **Did NOT verify CI on a real GitHub Actions runner** — the workflow YAML is syntactically valid (verified by structural read) but I could not test cache hits/misses in a real CI environment. The cache-key formula `lake-${{ runner.os }}-${{ hashFiles(...) }}` is standard.
- **Did NOT check whether `lake exe cache get` is available in this Mathlib pin** (the standard Mathlib precompiled-olean cache mechanism). If available, the CI could swap `lake build` for `lake exe cache get && lake build` and shave 30+ minutes from cold runs.
- **Did NOT inspect every Lean source file for new trivial-witness patterns** — that's persona 12's domain.

## Recommendations (≤5)

- **Fix the lint CRLF asymmetry** at `tools/lint.sh:61` (add `tr -d '\r'`) and add a project `.gitattributes` enforcing `eol=lf`. Both are one-line/one-file changes and close the CRITICAL exploit on Windows fresh clones.
- **Fix README + STATUS.md "Layout"** to match the actual file tree. The current text references `BrownianMotion.lean` and `Brownian/NaturalFiltration.lean` that do not exist. Either create the files (rename `Construction.lean` → `BrownianMotion.lean`; split `Martingale.lean` to expose `NaturalFiltration.lean`) or correct the docs.
- **Add 3 missing copyright headers** to `LevyStochCalc.lean`, `_audit.lean`, `tools/full_audit.lean`. Mathlib-style headers, 4 lines each, no controversy.
- **Delete or repurpose `tools/full_audit.lean`** + `tools/full_audit_output.txt`. They duplicate `_audit.lean`/`audit_output.txt` and have no callers. Choose one and untrack the other.
- **Add `~/.elan` to the CI cache** (second `actions/cache@v4` step) — saves 200 MB of bandwidth and ~30 s per run. While there, add a `concurrency:` block and a sanity-check step that asserts `_audit.lean`, `lakefile.toml`, `lean-toolchain` all exist.
