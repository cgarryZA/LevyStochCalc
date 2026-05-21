# Red Team Audit: Software Engineering / Build Hygiene

**Auditor lens**: Staff software engineer reviewing build reproducibility, file organization, git hygiene, tool-script quality, and operational sanity.
**Date**: 2026-05-20
**Coverage**: 17 files read in full (`.gitignore`, `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `tools/lint.sh`, `tools/cited_axioms.md`, `tools/full_audit.lean`, `tools/full_audit_output.txt`, `tools/sorry_baseline.txt`, `_audit.lean`, `audit_output.txt`, `_mcp_snippet_*.lean`, `STATUS.md`, `STATUS_strong_exists.md`, `LevyStochCalc.lean`, `LevyStochCalc/Notation.lean`, `.mcp.json`); 4 substantial source files read in full (`LevyStochCalc/Brownian/Multidim.lean`, `LevyStochCalc/Ito/Setting.lean`, `LevyStochCalc/Poisson/L2Isometry.lean`, `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean`); 12 source files spot-read for git hygiene / sorry-content (`Brownian/Ito.lean`, `Brownian/SimplePredictableRefine.lean`, `Brownian/Continuity.lean`, `Brownian/Construction.lean`, `Brownian/Martingale.lean`, `Poisson/Compensated.lean`, `Poisson/Martingale.lean`, `Poisson/RandomMeasure.lean`, `Poisson/NaturalFiltration.lean`, `BSDEJ/Definition.lean`, `BSDEJ/Existence.lean`, `BSDEJ/PathRegularity.lean`, `Ito/JumpFormula.lean`); ran `git status`, `git ls-files`, `git log --all --diff-filter=A`, `git check-ignore`, `git worktree list`, `lake --version`. No remote network calls (Mathlib upstream ref-tip listed but not paginated). No file modified.

## Executive summary (≤ 3 sentences)

The repository is **structurally broken from a reproducibility standpoint**: the project's `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, **five source files** including the trivial-witness-tainted `Multidim.lean` / `Setting.lean` / `MartingaleRepresentation.lean`, and the `tools/lint.sh` script itself **have never been committed to any branch** — a fresh `git clone` produces a non-building repo that is missing 518 lines of source and the entire build configuration. The lint script that the audit narrative depends on is also **silently broken on any fresh checkout**: it executes `lake env lean _audit.lean` against a file that is gitignored, gets nothing back, then runs a regex over an empty file and reports PASS — meaning **the "8401 jobs, PASS at baseline" claim in the shared context cannot survive a clean clone**. On top of that, two newly-discovered trivial-witness theorems (`JumpDiffusion.exists_unique` with constant-path witness, `jacodYor_representation` with `Z=0, U=0, BM=0` witness) sit in the untracked files — invisible to git history and to the recursive trivial-witness audit that landed in commit `db582f9`.

## Top findings (ranked by severity, highest first)

### Finding 1 — Build configuration and 518 lines of source code are UNTRACKED in git

- **Severity**: CRITICAL
- **Location**: Repository root + multiple source paths. Verified by `git status -uall --short` and `git log --all --diff-filter=A --oneline --name-only | grep -E "(lakefile|toolchain|manifest|Notation|Multidim|L2Isometry|Setting\.lean|MartingaleRepresentation)"` (returned empty).
- **Evidence**: `git status -uall --short` (run at `D:\LevyStochCalc` on `master` at `db582f9`):
  ```
  ?? .claude/settings.local.json
  ?? .claude/worktrees/magical-wozniak-2e9f4f/
  ?? .codex/config.toml
  ?? .mcp.json
  ?? LevyStochCalc/BSDEJ/MartingaleRepresentation.lean
  ?? LevyStochCalc/Brownian/Multidim.lean
  ?? LevyStochCalc/Ito/Setting.lean
  ?? LevyStochCalc/Notation.lean
  ?? LevyStochCalc/Poisson/L2Isometry.lean
  ?? lake-manifest.json
  ?? lakefile.toml
  ?? lean-toolchain
  ?? redteam_findings/shared_context_override.md
  ?? tools/lint.sh
  ```
  Line counts of the untracked source files: `Notation.lean` 13, `MartingaleRepresentation.lean` 86, `Multidim.lean` 232, `Setting.lean` 114, `L2Isometry.lean` 73 — total **518 lines**.

  None of these files has ever been added to any commit in the repository's history (`git log --all --diff-filter=A` returns empty for each).

- **Why this matters**: This is not a "tracked file that was deleted" or a "gitignore covering them" situation — the rules in `.gitignore` are only `.lake/`, `_audit.lean`, `_mcp_snippet_*.lean`, `audit_output.txt`. The build files and the source files are untracked because they were **never staged**. Consequences:
  1. A fresh `git clone` produces a repo that does not build: `lakefile.toml` is missing, so `lake build` has no target. Even if a contributor manually re-creates `lakefile.toml`, the dependency pins (Mathlib at `0e208554a6...`) are in the untracked `lake-manifest.json`, so Mathlib would float and the build could break on any upstream merge.
  2. The root aggregator `LevyStochCalc.lean:2` imports `LevyStochCalc.Notation` — but `Notation.lean` is untracked. A fresh clone hits an immediate import error.
  3. The full Tier 1 audit chain depends on `LevyStochCalc/Ito/Setting.lean` (defines `JumpDiffusion`), `LevyStochCalc/Brownian/Multidim.lean` (defines `MultidimBrownianMotion.exists` — listed in `tools/full_audit.lean:44` as one of the audited derivative theorems!), `LevyStochCalc/Poisson/L2Isometry.lean` (the I02 forwarder — listed in `tools/full_audit.lean:66`), and `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean` (Tier 1 #9 prerequisite — listed in `tools/full_audit.lean:72`). All four files are referenced by the canonical audit script `tools/full_audit.lean` but **none of them is tracked**.
  4. Two of the four untracked source files contain trivial-witness theorems that the recursive audit was supposed to be exorcising — see Finding 4.

- **Recommendation**: `git add lakefile.toml lean-toolchain lake-manifest.json LevyStochCalc/Notation.lean LevyStochCalc/Brownian/Multidim.lean LevyStochCalc/Ito/Setting.lean LevyStochCalc/Poisson/L2Isometry.lean LevyStochCalc/BSDEJ/MartingaleRepresentation.lean tools/lint.sh` and commit immediately. This is a single one-line fix that converts a non-reproducible repository into a reproducible one. The fact that the project author reports "build passes, 8401 jobs PASS at baseline" but cannot survive a fresh clone is exactly the kind of build-hygiene failure a Mathlib reviewer would catch in the first five minutes.

### Finding 2 — `tools/lint.sh` is silently broken on any fresh checkout (audits a gitignored file)

- **Severity**: CRITICAL
- **Location**: `tools/lint.sh:21`
- **Evidence**:
  ```bash
  echo "==> running _audit.lean"
  lake env lean _audit.lean > audit_output.txt 2>&1 || true
  ```
  And from `.gitignore`:
  ```
  .lake/
  _audit.lean
  _mcp_snippet_*.lean
  audit_output.txt
  ```
  `_audit.lean` is the file the lint script audits — and it's gitignored. `git check-ignore -v _audit.lean` returns `.gitignore:2:_audit.lean    _audit.lean`. On a fresh clone, `_audit.lean` does not exist; `lake env lean _audit.lean` fails; the `|| true` suppresses the error; `audit_output.txt` is empty or contains a "no such file" error; the Python regex `r"'([^']+)' depends on axioms: \[([^\]]+)\]"` matches nothing; `CURRENT_SORRIES` is empty; the script reports `PASS: lake build + audit at or below baseline`. **The audit silently runs over zero theorems and concludes "no sorries"**.

  Meanwhile, the project introduced `tools/full_audit.lean` in commit `febee60` ("Items 1+2+3: 10 Tier 1 cited axioms documented + full-project axiom audit") that does the same job from a tracked source — but `tools/lint.sh` was never updated to use it.

- **Why this matters**: The headline claim in `shared_context_override.md` line 18 — "Build state: `cd D:\LevyStochCalc && bash tools/lint.sh` → 8401 jobs, PASS at baseline" — only holds because the author has the local gitignored `_audit.lean` on disk. Anyone reviewing this library by following the documented procedure (clone + `bash tools/lint.sh`) gets a green-light PASS that **proves nothing about axiom hygiene**.

  Compounding: even with the local `_audit.lean` present, the lint's `lake env lean _audit.lean > audit_output.txt 2>&1 || true` swallows compilation errors (e.g., a broken import, a typo'd `#print axioms` argument) — the script would still report PASS. There is no `grep -q "depends on axioms"` sanity check to verify the audit actually ran.

- **Recommendation**: (a) Replace `tools/lint.sh:21` with `lake env lean tools/full_audit.lean > tools/full_audit_output.txt 2>&1` (drop the `|| true`, since `tools/full_audit.lean` is tracked). (b) Add a sanity check: `grep -q "depends on axioms:" tools/full_audit_output.txt || { echo "FAIL: audit produced no axiom output"; exit 1; }`. (c) Delete the now-obsolete `_audit.lean` and `audit_output.txt` rules from `.gitignore`. (d) Consider failing loudly on `lake build` exit code (currently `set -euo pipefail` + bare `lake build` already does this — fine — but ensure the same applies to the audit step).

### Finding 3 — `lake-manifest.json` mis-identifies project as "Dissertation"

- **Severity**: HIGH
- **Location**: `lake-manifest.json:94` (UNTRACKED — but the file as it sits on disk and is hashed into the Mathlib reproducibility chain)
- **Evidence**:
  ```json
  "name": "Dissertation",
  "lakeDir": ".lake",
  "fixedToolchain": false}
  ```
  Cross-referenced against `lakefile.toml:1`:
  ```
  name = "LevyStochCalc"
  ```

- **Why this matters**: (1) The manifest is the file Lake reads to identify the workspace and resolve packages; a name mismatch with the `lakefile.toml` can confuse Lake's package resolution and downstream tooling that introspects `lake-manifest.json` (e.g., Reservoir, doc-gen, Mathlib4 doc indexing). (2) The mis-name is direct evidence that this file was copy-pasted from the sister Dissertation repo without an audit step. (3) `"fixedToolchain": false` is a separate red flag — combined with the `lean-toolchain` file being **untracked**, the Lean version is doubly unpinned at the git level.

- **Recommendation**: Track `lake-manifest.json` (per Finding 1), regenerate it from a clean `lake update` to obtain `"name": "LevyStochCalc"` and the current pinned toolchain hash, then commit. Also flip `"fixedToolchain": true` if and only if you want `lean-toolchain` (tracked!) to be the binding constraint — which you do, for reproducibility.

### Finding 4 — Trivial-witness theorems remain in the untracked source files (out-of-scope for SE but flagged for orchestrator)

- **Severity**: HIGH (relays a math/audit-hygiene finding visible from SE-level inspection of files that should have been audited)
- **Location**: `LevyStochCalc/Ito/Setting.lean:85-112` (`JumpDiffusion.exists_unique`); `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:55-84` (`jacodYor_representation`).
- **Evidence**:

  `LevyStochCalc/Ito/Setting.lean:93-102` (the proof body of `JumpDiffusion.exists_unique`):
  ```lean
  Nonempty (JumpDiffusion W N coeffs x₀) := by
    -- Existence witness: the constant path X t ω = x₀. Substantive Picard solution
    -- (Applebaum 2009 Thm 6.2.9) replaces this in a future refinement.
    refine ⟨{
      X := fun _ _ => x₀
      measurable_path := measurable_const
      initial_value := Filter.Eventually.of_forall (fun _ => rfl)
      sup_L2 := ?_
      is_solution := trivial
    }⟩
  ```
  The structure has an `is_solution : True` field (`Setting.lean:72`) — so "being a solution" reduces to `trivial`, and the existential `∃ X, JumpDiffusion = ...` is satisfied by the constant path. This is the exact pattern that got `itoLevyFormula` demoted to an axiom on 2026-05-11.

  `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:73-84` (the proof body of `jacodYor_representation`):
  ```lean
    -- Existence: take Z = 0, U = 0, BM_integral = 0, jump_integral = ξ - 𝔼[ξ].
    -- The substantive (Jacod 1976) decomposition (with Z, U from orthogonal
    -- projection) replaces these in a future refinement.
    refine ⟨0, 0, 0, fun ω => ξ ω - ∫ ω', ξ ω' ∂P, ?_, ?_, ?_, ?_, ?_⟩
    · exact measurable_const
    · exact measurable_const
    · simp
    · simp
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      show ξ ω = (∫ ω', ξ ω' ∂P) + 0 + (ξ ω - ∫ ω', ξ ω' ∂P)
      ring
  ```
  Exactly the `⟨0, 0, 0, change⟩; ring` pattern that got `itoLevyFormula` demoted. The existential has four conjuncts; three are zero, the entire content is stuffed into the fourth.

- **Why this matters**: The 2026-05-11 recursive audit (shared_context_override.md:15-17) claims "No trivial-witness theorems remain." (`tools/cited_axioms.md:140` — "No trivial-witness theorems remain. Dissertation forwarders now transitively surface real Tier 1 cited axioms in their audit, including the newly-demoted #11 `itoLevyFormula`."). That claim is **false**: two trivial-witness theorems sit in plain sight in `Setting.lean` and `MartingaleRepresentation.lean`. They evaded the recursive audit because **both files are untracked** (Finding 1) — they don't show up in `git log` diffs, they don't trigger code-review attention, and the recursive-audit workflow appears to have keyed on commit diffs rather than file-system scans.

  `tools/full_audit_output.txt:43-46` confirms that `MultidimBrownianMotion.exists` is reported by the audit script with axiom set `[propext, Classical.choice, Quot.sound, LevyStochCalc.Brownian.BrownianMotion.exists]`. But `jacodYor_representation` is reported (line 94-96) as `[propext, Classical.choice, Quot.sound]` — i.e., the script *did* run over it but did NOT detect that it's a trivial-witness theorem. The audit catches `sorryAx` but cannot detect "this proof body satisfies the existential with zero terms." Same for `JumpDiffusion.exists_unique` (line 89): `[propext, Classical.choice, Quot.sound]`.

  These two theorems are **not in `tools/cited_axioms.md`** Tier 1 list (which has 11 entries). They are listed in `tools/full_audit.lean:69, 72` as honest derivative theorems — they would be **better demoted to documented `axiom`s** following the same logic that demoted `itoLevyFormula`.

- **Recommendation**: (a) Flag to persona 5 / persona 12 for confirmation. (b) Demote both to documented Tier 1 axioms (Applebaum 2009 Thm 6.2.9 for `JumpDiffusion.exists_unique`, Jacod 1976 for `jacodYor_representation`) following the 2026-05-11 pattern. (c) Critically: the only reason these slipped through is that the recursive-audit pass operated on `git log` diffs. The next pass MUST do a filesystem `grep -rn "refine ⟨0" LevyStochCalc/` to catch all trivial-witness patterns regardless of git-track status.

### Finding 5 — `LevyStochCalc/Poisson/Martingale.lean` is an ~677-line orphan: never imported by any other file

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Poisson/Martingale.lean` (full file; tracked in git via `git ls-files | grep Martingale` returns it)
- **Evidence**: `LevyStochCalc.lean` (the root aggregator) imports 18 modules but not `LevyStochCalc.Poisson.Martingale`. `Grep -r "LevyStochCalc.Poisson.Martingale" D:\LevyStochCalc --include=*.lean` returns 0 matches across all Lean files. The file is 677 lines, ~34kB; it declares e.g. `theorem itoIsometry_compensatedPoisson_general` at line 651.

  `wc -l LevyStochCalc/Poisson/Martingale.lean` → 677.

- **Why this matters**: 5% of the project's Lean LOC is dead code that compiles into `.olean` only because nothing else compels it. It bloats `lake build` time, confuses navigation for new contributors ("oh, there's a Poisson.Martingale module — let me look at it..."), and represents abandoned scaffolding from an earlier design iteration. The file imports `Compensated.lean` (a 2752-line beast), so simply touching `Martingale.lean` triggers a recompile of that downstream chain.

- **Recommendation**: Either (a) delete `LevyStochCalc/Poisson/Martingale.lean` outright and `git rm`; (b) merge the still-useful lemmas into `Compensated.lean` and delete the file; or (c) add `import LevyStochCalc.Poisson.Martingale` to `LevyStochCalc.lean` AND make sure something in the public theorem tree actually references it. Decide and commit; do not leave the orphan in place.

### Finding 6 — Multiple sorries in private lemmas evade the audit (Continuity.lean:184, Compensated.lean:1893, RandomMeasure.lean:139, Ito.lean:3984)

- **Severity**: MEDIUM
- **Location**:
  - `LevyStochCalc/Brownian/Continuity.lean:184` — `kolmogorov_modification_ae_eq` (no callers anywhere in the codebase — dead code with `sorry`)
  - `LevyStochCalc/Brownian/Ito.lean:3984` — `quadVar_simpleIntegral_brownian` (no callers anywhere — dead private lemma)
  - `LevyStochCalc/Poisson/Compensated.lean:1893` — `simplePredictable_dense_L2_bounded` (called by `simplePredictable_dense_L2` at line 1903, which has no callers in the audited public API)
  - `LevyStochCalc/Poisson/RandomMeasure.lean:139` — `poissonRandomMeasure_finite_exists` (called by `exists_of_sigmaFinite` — but that's a Tier 1 *axiom*, so the call is inside the axiom's proof... wait, axioms have no proof — let me re-check)
- **Evidence**: `git show master:LevyStochCalc/Brownian/Continuity.lean | sed -n '180,190p'`:
  ```lean
      (_h_dyadic_eq : ∀ s ∈ dyadicRationals, ∀ᵐ ω ∂P, _Y s ω = X s ω) :
      ∀ t : ℝ, ∀ᵐ ω ∂P, _Y t ω = X t ω := by
    sorry
  ```
  `Grep "kolmogorov_modification_ae_eq" -r LevyStochCalc/` → single file (the declaration site itself). Zero callers.

  `git show master:LevyStochCalc/Brownian/Ito.lean | sed -n '3982,3986p'`:
  ```lean
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P := by
    sorry
  ```
  `Grep "quadVar_simpleIntegral_brownian" -r LevyStochCalc/` → single file (declaration site only). Zero callers.

  `git show master:LevyStochCalc/Poisson/Compensated.lean | sed -n '1893,1894p'`:
  ```lean
    sorry
  ```
  (inside the proof body of `simplePredictable_dense_L2_bounded`). Caller `simplePredictable_dense_L2` at line 1903; its callers? `Grep "simplePredictable_dense_L2\b" -r LevyStochCalc/` — only references inside the same file. The Compensated `simplePredictable_dense_L2` is not surfaced through any public audited theorem, but it lives in the same module as `Compensated.itoLevyIsometry`.

- **Why this matters**: The lint script's contract is "no NEW `sorryAx` in public theorems beyond baseline" — and the baseline is currently empty. The reason it passes despite four `sorry`s in the codebase is that all four are inside `private lemma`s with no transitive caller in the audited theorem set. From a software-engineering standpoint:
  1. `sorry` in dead code is misleading. It signals to a reader "this lemma is provisional and required" when actually it's neither — it's a stub from an abandoned proof attempt.
  2. The `set -euo pipefail` lint catches typo'd lemma names that *would* hit the `sorry`, but it doesn't catch the inverse: the lemma is never typo'd anywhere because it's never called.
  3. From a `tools/cited_axioms.md` accounting perspective, "11 Tier 1 cited axioms + 10 honest derivative theorems" is the headline. But the four `sorry`'d private lemmas mean **the proof state of the library is misrepresented by the lint output**: there are sorries on disk that compile, just nobody depends on them.

- **Recommendation**: Either (a) finish proving these private lemmas and use them, or (b) delete them. The third option ("leave them as `sorry` placeholders for future use") is the worst, because it persistently lies about what the library has proven.

### Finding 7 — `STATUS.md` and `STATUS_strong_exists.md` are 12 days stale relative to current axiom state

- **Severity**: MEDIUM
- **Location**: `D:\LevyStochCalc\STATUS.md` (last edit 2026-05-08), `D:\LevyStochCalc\STATUS_strong_exists.md` (last edit 2026-05-09).
- **Evidence**: `STATUS.md:76` says "## What's still sorry'd (`tools/sorry_baseline.txt`, 19 entries)" and lists 19 theorem names. But `tools/sorry_baseline.txt` is **0 bytes** (`wc -c tools/sorry_baseline.txt` → `0 tools/sorry_baseline.txt`). The 2026-05-11 commit `ab8d2ce` ("BASELINE EMPTY: stage 13 deep-prerequisite theorems as paper-cited axioms") moved all 19 baseline entries to documented `axiom`s in `tools/cited_axioms.md` and emptied the baseline. `STATUS.md` was never updated.

  `STATUS.md:158-164` claims "$ bash tools/lint.sh ⇒ PASS: lake build + audit at or below baseline. 8400 jobs, no errors, no new sorries beyond baseline." But the baseline now has 0 entries, not the 19 documented in STATUS.md.

  `STATUS_strong_exists.md` is an internal refactor-plan document; it's not the public face of the project, but it sits at the repo root next to STATUS.md and would be the first thing a new contributor opens.

- **Why this matters**: A new contributor reading `STATUS.md` will think the library has 19 outstanding sorries and is mid-refactor toward closing them. The real story (per `tools/cited_axioms.md`) is "the 19 sorries were converted to 11 Tier 1 cited axioms (with paper references) + 8 honest derivative theorems on 2026-05-11." Those are different stories with different implications for Mathlib-ready status, downstream use, and what work remains.

- **Recommendation**: Either (a) delete `STATUS.md` and `STATUS_strong_exists.md` entirely (the canonical project status now lives in `tools/cited_axioms.md`), or (b) rewrite both to reflect the 2026-05-11 state and add a "Last updated: YYYY-MM-DD" header so future staleness is detectable.

### Finding 8 — No README, LICENSE, CONTRIBUTING — repository is incomplete for external use

- **Severity**: MEDIUM
- **Location**: Repository root (absent files).
- **Evidence**: `find . -maxdepth 2 -iname "README*" -type f` → empty; same for `CONTRIBUTING*`, `LICENSE*`. The repository ships with `STATUS.md` and `STATUS_strong_exists.md` only.

- **Why this matters**: This is a library that is being positioned (per `shared_context_override.md`) as a candidate Mathlib upstream contribution + a foundation for the sister Dissertation repo. A Mathlib reviewer landing at this repository's GitHub page would see no README, no license, no contributing guide. They would have to read `STATUS.md` (stale, internal jargon) or `tools/cited_axioms.md` (better, but technical) to understand what the library is. There is no quickstart, no `lake build` instructions, no description of what the 11 Tier 1 axioms collectively achieve.

  Specifically: the library lacks even a one-paragraph description of its purpose, scope, and dependency on Mathlib. A new user has no entry point.

- **Recommendation**: Add a `README.md` with: project description (1 paragraph), build instructions (`lake build`), pointer to `tools/cited_axioms.md` for the axiom roster, a brief "what's NOT in scope" disclaimer (no finance, no MFG, no deep learning), and a license declaration. Add a `LICENSE` file (likely Apache 2.0 to match Mathlib). Without these, the library cannot be packaged or contributed to Mathlib.

### Finding 9 — No CI: no GitHub Actions, no GitLab CI, no pre-commit hook installed

- **Severity**: MEDIUM
- **Location**: Repository root — `find . -maxdepth 3 -path './.github*' -o -path './.git/hooks/pre-commit'` returns nothing.
- **Evidence**: `ls .github/` → "No such file or directory". `ls .gitlab-ci.yml` → "No such file or directory". `ls .pre-commit-config.yaml` → "No such file or directory". `ls .git/hooks/pre-commit` → "No such file or directory" (only `.git/hooks/*.sample` files from the default git install).

  `tools/lint.sh:12` claims:
  ```bash
  # Wire into pre-commit:  cp tools/lint.sh .git/hooks/pre-commit
  ```
  But this command has not been run — the hook is not installed.

- **Why this matters**: The audit hygiene depends entirely on humans remembering to run `bash tools/lint.sh` before each commit. With 23+ commits already authored by `claude@anthropic.com`, the chance that every commit was lint-checked locally is low. Combined with Finding 2 (the lint silently passes on fresh checkouts), this means there is no automated guarantee that any of the 118 commits in this repository ever satisfied the axiom-hygiene contract.

  For a library that markets itself on "no `sorryAx` in public theorems," the lack of any automated enforcement is a hole.

- **Recommendation**: Add `.github/workflows/lint.yml` that runs `bash tools/lint.sh` on every push to `master` and every PR. The workflow needs to install `elan` + the toolchain from `lean-toolchain`, run `lake build`, and execute the lint. Mathlib's own CI templates can be cribbed. Without CI, every claim about axiom hygiene is "trust me, I ran it locally."

### Finding 10 — Naming drift across files: `itoIsometry_brownian_*` has 4 distinct surface forms

- **Severity**: LOW
- **Location**: `LevyStochCalc/Brownian/Ito.lean`, `LevyStochCalc/Brownian/SimplePredictableRefine.lean`, `LevyStochCalc/Poisson/Compensated.lean`, `LevyStochCalc/Poisson/Martingale.lean`.
- **Evidence**: `Grep "^theorem itoIsometry" -r LevyStochCalc/ --include="*.lean"`:
  ```
  LevyStochCalc/Brownian/Ito.lean:4035: theorem itoIsometry_brownian_general
  LevyStochCalc/Brownian/SimplePredictableRefine.lean:1977: theorem itoIsometry_brownian_existence
  LevyStochCalc/Brownian/SimplePredictableRefine.lean:2152: theorem itoIsometry
  LevyStochCalc/Poisson/Compensated.lean:2636: theorem itoIsometry_compensated_existence
  LevyStochCalc/Poisson/Martingale.lean:651: theorem itoIsometry_compensatedPoisson_general
  ```
  Plus the unified-existence axioms: `itoIsometry_brownian_unified_existence`, `itoIsometry_compensated_unified_existence`.

- **Why this matters**: The convention is unclear: `_general` vs `_existence` vs no suffix vs `_unified_existence`. The `Poisson/Martingale.lean` file (Finding 5: orphan) uses `compensatedPoisson` while the active code uses `compensated`. These distinctions reflect different proof iterations that never got cleaned up.

- **Recommendation**: Pick a convention. Standard Mathlib idiom for the L²-isometry theorem is just `itoIsometry` (or `MeasureTheory.itoIsometry` once Mathlib gets one). For the Brownian / compensated-Poisson distinction, use namespaces (`LevyStochCalc.Brownian.itoIsometry`, `LevyStochCalc.Poisson.Compensated.itoIsometry`) rather than name suffixes. Document the convention in the project README (Finding 8).

### Finding 11 — `lake-manifest.json:11` declares Mathlib `inputRev: "master"` (floating dep specification)

- **Severity**: LOW (mitigated by the pinned commit hash)
- **Location**: `lake-manifest.json:11`.
- **Evidence**:
  ```json
  {"url": "https://github.com/leanprover-community/mathlib4",
   ...
   "rev": "0e208554a6143756c125878a8fe8b17a331d39f7",
   ...
   "inputRev": "master",
   ...
   "configFile": "lakefile.lean"},
  ```
  The `rev` field is a pinned 40-char commit SHA. The `inputRev` says "master" — meaning the next `lake update` would jump to the current Mathlib master tip.

- **Why this matters**: `inputRev: "master"` means anyone running `lake update` will refresh to whatever Mathlib master is at that moment, potentially breaking the entire library. The actual current pin is `0e208554a6...` (verified as a real commit in the Mathlib upstream history). The combination of "tracking master + pinning a specific SHA" is a moving-target setup that requires discipline to keep stable.

  Compare with the inherited dependencies (`Cli`, `aesop`, `batteries`, `Qq`) which use `inputRev: "v4.30.0-rc2"` — a release tag — and would resolve to a stable target on `lake update`.

- **Recommendation**: Change `inputRev` to a Mathlib release tag (e.g. `v4.30.0-rc2`-compatible Mathlib tag, or the nightly tag that matches your `lean-toolchain`). This makes `lake update` reproducible. Document the chosen update cadence in `CONTRIBUTING.md` (Finding 8).

### Finding 12 — `.gitignore` is sparse (4 lines); misses common patterns

- **Severity**: LOW
- **Location**: `.gitignore` (4 lines).
- **Evidence**: Full content:
  ```
  .lake/
  _audit.lean
  _mcp_snippet_*.lean
  audit_output.txt
  ```
  Missing patterns observed on disk: `.claude/` (Claude config), `.codex/` (Codex config), `.mcp.json` (MCP server config — currently untracked but should be either tracked or ignored explicitly), `__pycache__/`, `*.pyc` (Python tooling artifacts), `.DS_Store`, `Thumbs.db`, `.idea/`, `.vscode/`. Also the empty `docs/` directory at the repo root is tracked but orphan.

- **Why this matters**: The current state is "anything not explicitly ignored shows up as untracked in git status, including IDE config and editor backups." This is why `.claude/` and `.codex/` and `.mcp.json` appear as untracked. A user who decides to track them later will accidentally include personal config. The opposite risk also applies: hand-edited per-user settings get committed because they weren't gitignored.

- **Recommendation**: Adopt the Mathlib `.gitignore` as a baseline (covers Lean, Lake, Python, common IDEs) and add LevyStochCalc-specific entries (`_audit.lean`, `_mcp_snippet_*.lean`, `audit_output.txt`). Decide whether `.claude/` `.codex/` `.mcp.json` are per-user (ignore) or per-project (track) — currently they're neither, which is the worst of both worlds.

### Finding 13 — Empty `docs/` directory tracked at root

- **Severity**: LOW
- **Location**: `D:\LevyStochCalc\docs\` (empty).
- **Evidence**:
  ```
  $ ls -la docs/
  total 4
  drwxr-xr-x 1 Christian 197121 0 May  2 16:35 .
  drwxr-xr-x 1 Christian 197121 0 May 20 21:07 ..
  ```
  Created on `2026-05-02 16:35` (project bootstrap date based on root dir mtime) and never populated.

- **Why this matters**: Git doesn't track empty directories — so `docs/` is not actually tracked. The fact that it's on disk but git doesn't see it tells me the contributor intended to put documentation there and never did. After 18 days of active commits, the absence of content is signal.

- **Recommendation**: Either populate `docs/` with the project README + axiom inventory (per Finding 8), or `rmdir docs/`. Leaving it empty is just a visual reminder that documentation was deferred.

### Finding 14 — `tools/full_audit.lean` audits a theorem (`MultidimBrownianMotion.exists`) whose source file is untracked

- **Severity**: LOW (chained with Finding 1)
- **Location**: `tools/full_audit.lean:44` references `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists`; `LevyStochCalc/Brownian/Multidim.lean` is untracked.
- **Evidence**: `tools/full_audit.lean:44`:
  ```lean
  #print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists
  ```
  `git ls-files | grep Multidim` → empty.

- **Why this matters**: The tracked audit script lists theorems from untracked files. On a fresh clone, `tools/full_audit.lean` would fail to compile (its dependency `LevyStochCalc` imports `LevyStochCalc.Brownian.Multidim` which doesn't exist). Same problem applies for `JumpDiffusion.exists_unique` (Setting.lean:85 — untracked) and `jacodYor_representation` (MartingaleRepresentation.lean:55 — untracked) and `Poisson.L2Isometry.itoLevyIsometry` (L2Isometry.lean:55 — untracked).

  Once Finding 1 is fixed (commit the untracked files), this finding self-resolves. Listing it separately because it's a concrete consequence that a reviewer can immediately see.

- **Recommendation**: Fixed by Finding 1.

## Per-claim verdicts on the 11 Tier 1 axioms + 16 derivative theorems

The verdicts are from a software-engineering / build-hygiene lens, NOT a math correctness lens.

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `Brownian.BrownianMotion.exists` (Tier 1 #1) | EARNED | Honest `axiom` with citation; tracked. |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` (Tier 1 #2) | EARNED | Honest `axiom` with citation; tracked. |
| `Brownian.Continuity.kolmogorovChentsov_modification` (Tier 1 #3) | EARNED | Honest `axiom` with citation; tracked. |
| `Brownian.Martingale.brownian_martingale_rightCont` (Tier 1 #4) | EARNED | Honest `axiom` with citation; tracked. |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` (Tier 1 #5) | EARNED | Honest `axiom` with citation; tracked. |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` (Tier 1 #6) | EARNED | Honest `axiom` with citation; tracked. |
| `Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` (Tier 1 #7) | EARNED | Honest `axiom` with citation; tracked. |
| `Poisson.Compensated.adaptedSimple_dense_L2_compensated` (Tier 1 #8) | EARNED | Honest `axiom` with citation; tracked. |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` (Tier 1 #9) | EARNED | Honest `axiom` with citation; tracked. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` (Tier 1 #10) | EARNED | Honest `axiom` with citation; tracked. |
| `Ito.JumpFormula.itoLevyFormula` (Tier 1 #11) | EARNED | Honest `axiom` (newly demoted 2026-05-11); tracked. |
| `Brownian.Multidim.MultidimBrownianMotion.exists` | UNVERIFIABLE | **Source file UNTRACKED** — cannot be cloned. SE finding 1. |
| `Brownian.Continuity.brownian_continuous_modification` | EARNED | Tracked, forwards via Tier 1 #3. |
| `Brownian.Martingale.brownian_martingale` | EARNED | Tracked, axiom-clean modulo std. |
| `Brownian.Martingale.brownian_quadVar` | EARNED | Tracked, axiom-clean modulo std. |
| `Brownian.Martingale.brownian_filtration_rightContinuous` | EARNED | Tracked, forwards via Tier 1 #4. |
| `Brownian.Ito.itoIsometry` | EARNED | Tracked, extracts conjunct 3 of Tier 1 #5. |
| `Brownian.Ito.martingale_stochasticIntegral` | EARNED | Tracked, extracts conjunct 1 of Tier 1 #5. |
| `Brownian.Ito.quadVar_stochasticIntegral` | EARNED | Tracked, extracts conjunct 2 of Tier 1 #5. |
| `Poisson.Compensated.itoLevyIsometry` | EARNED | Tracked, extracts conjunct 3 of Tier 1 #6. |
| `Poisson.Compensated.martingale_stochasticIntegral` | EARNED | Tracked, extracts conjunct 1 of Tier 1 #6. |
| `Poisson.Compensated.quadVar_stochasticIntegral` | EARNED | Tracked, extracts conjunct 2 of Tier 1 #6. |
| `Poisson.Compensated.cadlag_modification_exists` | EARNED | Tracked, extracts conjunct 4 of Tier 1 #6. |
| `Poisson.L2Isometry.itoLevyIsometry` | UNVERIFIABLE | **Source file UNTRACKED** — 1-line forwarder over `Compensated.itoLevyIsometry`, but the file containing this declaration cannot be cloned. SE finding 1. |
| `Ito.Setting.JumpDiffusion.exists_unique` | TRIVIAL | Constant-path witness `X := fun _ _ => x₀` + `is_solution : True`. **Source file UNTRACKED**. Equivalent to the `itoLevyFormula` pattern that got demoted. See SE finding 4. |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` | TRIVIAL | `⟨0, 0, 0, ξ - 𝔼[ξ]⟩` witness — exactly the `⟨0, 0, 0, change⟩; ring` pattern. **Source file UNTRACKED**. See SE finding 4. |

The "EARNED" verdicts are conditional on Finding 1 being resolved — a fresh clone today cannot reproduce any of them because the build configuration is untracked.

## Tools and sources used

- **Lean tools called**: none required (read-only SE audit; all evidence from source files + git history).
- **Bash / git commands**:
  - `git status` / `git status -uall --short` / `git ls-files` (compare tracked vs on-disk)
  - `git log --all --diff-filter=A --oneline --name-only` (proved lakefile/toolchain/manifest never committed)
  - `git log --reverse --all --oneline` (root commit was `d125bad`, NOT a genesis commit with build files)
  - `git worktree list` (confirmed two worktrees: master + `claude/magical-wozniak-2e9f4f`)
  - `git check-ignore -v _audit.lean lakefile.toml lean-toolchain LevyStochCalc/Notation.lean` (verified gitignore vs untracked-but-not-ignored)
  - `git show master:<path>` (read master content from the worktree-on-branch perspective)
  - `lake --version` (5.0.0-src+3dc1a08 / Lean 4.30.0-rc2)
  - `git ls-remote https://github.com/leanprover-community/mathlib4` (confirmed the pinned SHA `0e208554a6` is reachable in upstream history)
- **Grep queries**: `\bsorry\b`, `\b(TODO|FIXME|XXX|HACK)\b`, `\badmit\b`, `^theorem itoIsometry`, `^theorem itoLevyIsometry`, `^axiom\s`, `LevyStochCalc.Poisson.Martingale`, `simplePredictable_dense_L2`, `kolmogorov_modification_ae_eq`, `quadVar_simpleIntegral_brownian`, `simplePredictable_dense_L2_bounded`, `cadlag_modification_exists` (all via `--include=*.lean`).
- **Web searches**: none. SE audit is local-evidence-only.
- **Web fetches**: none.
- **Papers consulted**: none (out of scope for SE).

## What you couldn't verify

- **Full `lake build` timing**: did not run `lake build` (long-running, would burn the audit budget). The build is referenced in STATUS.md as "8400 jobs" (stale) and in `shared_context_override.md:18` as "8401 jobs at baseline". I confirmed `lake --version` works and `.lake/build/lib/lean/LevyStochCalc/*.olean` are present on disk, so the build has run at some point recently. I did not validate the "no errors / no warnings" claim.
- **Mathlib commit `0e208554a6` semantics**: I confirmed it is reachable in upstream Mathlib history (the locally-checked-out `.lake/packages/mathlib/.git` HEAD matches), but did NOT verify what features that commit provides for the project's Tier 1 axiom replacement plans. That's persona 4 / persona 7 territory.
- **Python regex semantics in `tools/lint.sh:30`**: I traced the logic by reading. I did not execute the lint script in a sandbox to confirm the silent-pass scenario, but the control flow is unambiguous: `|| true` swallows the lake-env failure; the subsequent regex over an empty file matches nothing.
- **What the orphan `docs/` directory was intended to contain**: zero git history, zero file content. Pure intent inference.
- **Whether the `claude/magical-wozniak-2e9f4f` branch has any unique content vs `master`**: It's 3 commits behind master (`4dea618` vs `db582f9`). The worktree-staged "deleted" files reflect the diff. Out of scope for the SE audit of the main project.

## Recommendations for the project (≤ 5 bullets)

- **Fix the git tracking IMMEDIATELY** (Finding 1): `git add lakefile.toml lean-toolchain lake-manifest.json LevyStochCalc/Notation.lean LevyStochCalc/Brownian/Multidim.lean LevyStochCalc/Ito/Setting.lean LevyStochCalc/Poisson/L2Isometry.lean LevyStochCalc/BSDEJ/MartingaleRepresentation.lean tools/lint.sh && git commit -m "track build config + 5 source files that were never staged"`. Without this fix, the library cannot be reproduced.
- **Fix `tools/lint.sh` and add CI** (Findings 2, 9): Switch `lint.sh` from gitignored `_audit.lean` to tracked `tools/full_audit.lean`, add a sanity check that the audit actually produced output, and wire `bash tools/lint.sh` into a GitHub Actions workflow. Otherwise the axiom-hygiene narrative has no enforcement.
- **Demote the two newly-discovered trivial-witness theorems** (Finding 4): `JumpDiffusion.exists_unique` (Setting.lean) and `jacodYor_representation` (MartingaleRepresentation.lean) follow the exact pattern that got `itoLevyFormula` demoted on 2026-05-11. Apply the same fix: convert to documented `axiom`s with citations (Applebaum 2009 Thm 6.2.9; Jacod 1976). And run a filesystem-wide `grep -rn "refine ⟨0" LevyStochCalc/` next time, not just a git-log-diff scan.
- **Add a README + LICENSE + minimal Mathlib-style docs** (Findings 7, 8, 13): Either populate `docs/` or delete it. Replace stale `STATUS.md` / `STATUS_strong_exists.md` with a concise current README that points to `tools/cited_axioms.md` as the canonical project state. Add a license file (Apache 2.0 to match Mathlib).
- **Clean up dead code** (Findings 5, 6): Either prove or delete `LevyStochCalc/Poisson/Martingale.lean` (677 dead lines), `kolmogorov_modification_ae_eq` (Continuity.lean:184), `quadVar_simpleIntegral_brownian` (Ito.lean:3984), `simplePredictable_dense_L2_bounded` Compensated (Compensated.lean:1893), and `poissonRandomMeasure_finite_exists` (RandomMeasure.lean:139). Persistent unused-with-sorry private lemmas misrepresent the library's proof state to anyone running the audit.
