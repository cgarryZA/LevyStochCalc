# Red Team Audit: Library quality reviewer (Mathlib-acceptability lens, 2nd audit)

**Auditor lens**: Library quality reviewer for a stand-alone Lean 4 stochastic calculus library; would a Mathlib reviewer accept this, and could a fresh user pick it up?
**Date**: 2026-05-22 (2nd audit)
**Branch / commit audited**: `master` @ `237cc19` ("Close red-team L2, M10, H6 (naming drift, vector-Y scope, predictable caveat)")
**Coverage**: 21 files Read in full or in load-bearing range (`README.md`, `LICENSE` (verified Apache 2.0 boilerplate complete), `CONTRIBUTING.md`, `STATUS.md`, `LevyStochCalc.lean`, `lakefile.toml`, `lake-manifest.json`, `.github/workflows/ci.yml`, `_audit.lean`, `audit_output.txt`, `tools/cited_axioms.md` (full), `tools/full_audit.lean`, `tools/full_audit_output.txt`, `tools/lint.sh`, `tools/sorry_baseline.txt`, `Basic.lean`, `Notation.lean`, `Brownian/Construction.lean`, `Brownian/Multidim.lean`, `Brownian/Continuity.lean` (partial), `Brownian/SimplePredictableRefine.lean` (axiom site), `Poisson/RandomMeasure.lean`, `Poisson/Compensated.lean` (axiom site + docstring + master HEAD diff), `Poisson/L2Isometry.lean`, `Ito/Setting.lean`, `Ito/JumpFormula.lean`, `BSDEJ/Definition.lean`, `BSDEJ/Existence.lean`, `BSDEJ/PathRegularity.lean`, `BSDEJ/MartingaleRepresentation.lean`, `_mcp_snippet_952bdcfd68b74942a7ef219170b0f2aa.lean`). Git history scanned (recent 25 commits). 1st-audit archived persona-10 report read in full. Live `lake build` run on master HEAD (clean) and on the worktree's uncommitted modifications (BROKEN). Other personas' findings (05, 07, 11, 12) sampled to avoid redundancy.

## Executive summary

The library has come a long way in two days: a respectable Apache-2.0 boilerplate is in place, a hand-written `README.md` + `CONTRIBUTING.md` exist, a CI workflow runs `lake build` + `tools/lint.sh`, the audit output enumerates exactly 9 Tier 1 cited axioms (matching the post-deletion claim), and `lake build` on master HEAD genuinely lands at "8402 jobs, 2 warnings" (= the two sorry baseline entries). **None of that is, by itself, enough.** A Mathlib reviewer would still reject this library at first contact for three reasons: (1) the project orientation files (README.md, STATUS.md, tools/full_audit.lean, top-level LevyStochCalc.lean module docstring) are mutually inconsistent — they variously claim 9 vs 11 Tier 1 axioms, list two file names (`Brownian/BrownianMotion.lean`, `Brownian/NaturalFiltration.lean`) that DO NOT EXIST in the source tree, and the top-level module docstring still cites the FABRICATED "Bouchard-Elie-Touzi 2009 Thm 2.1" reference whose correction was supposedly the headline of the citation cleanup; (2) the library ships ZERO examples or tests demonstrating its API — every "public" theorem is either an axiom, a forwarder around an axiom, or a derivative of an axiom, with no `example` block anywhere showing a user how to invoke `Compensated.stochasticIntegral` or instantiate `BrownianMotion`; (3) the H6 "closure" of the predictable-vs-measurable gap is documentation-only at the master HEAD signature — the docstring honestly admits the over-claim, but the BSDEJ + Itô-Lévy chain still propagates the over-claim into every load-bearing caller, so a Mathlib reviewer cross-checking the axiom signature against the cited Applebaum statement would note the literature requires predictable σ-algebra and the Lean axiom does not.

## Top findings (ranked by severity, highest first)

### Finding 1 — Top-level module docstring `LevyStochCalc.lean:44` STILL cites the fabricated "Bouchard-Elie-Touzi 2009 Thm 2.1" reference whose correction is the project's headline citation fix

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc.lean:44` (verbatim):
  > `* `Cu05` — BSDEJ path regularity (Bouchard-Elie-Touzi 2009 Thm 2.1)`
- **Evidence**: `grep -rn "Bouchard-Elie-Touzi"` in the live source tree returns:
  - `LevyStochCalc.lean:44` (top-level project docstring; the FIRST thing a Mathlib reviewer reads)
  - `STATUS.md:59` (acceptable — narrating the fix)
  - Multiple historical references in `BSDEJ/PathRegularity.lean` (acceptable — quoting the fix narrative)
- **Why this matters**: The 1st audit's `_REDTEAM_SUMMARY.md` listed "C7. Tier 1 #10 citation 'Bouchard, Elie & Touzi 2009 SPA 119(11)' is wrong on every field" as a CRITICAL finding. The `cited_axioms.md` line 102 fix is correct (Bouchard-Elie 2008 SPA 118(1)), `STATUS.md:58-60` narrates the fix correctly, the in-axiom docstring at `PathRegularity.lean:103` is correct, AND the `tools/cited_axioms.md` `Red-team audit fix log` line 192-193 says "C7 closed". But the project root module file `LevyStochCalc.lean` — the file that re-exports every public-facing identifier and is the most-visible "what is this library?" surface — STILL CARRIES THE OLD FABRICATED CITATION. A Mathlib reviewer running `head -50 LevyStochCalc.lean` (the standard first action when reading a Lean library) sees the bad citation and concludes the citation cleanup was not consistently applied. The shared-context-override.md claims "Tier 1 #10: 'Bouchard-Elie-Touzi 2009 SPA 119(11)' (Touzi not an author; no such SPA volume) → Bouchard-Elie 2008 SPA 118(1) pp. 53-75." — but the project's own front door doesn't reflect that.
- **Recommendation**: Update `LevyStochCalc.lean:44` to `* `Cu05` — BSDEJ path regularity (Bouchard-Elie 2008 SPA 118(1) Thm 2.1)`.

### Finding 2 — `STATUS.md`, `tools/full_audit.lean`, and (in spirit) `README.md` are mutually inconsistent on the Tier 1 axiom count (9 vs 11)

- **Severity**: HIGH
- **Locations**:
  - `STATUS.md:24` (header): "Tier 1 cited axioms (11)"
  - `STATUS.md:31-37`: enumerates "Compensated-Poisson foundations (3 axioms): ... plus two dead density-chain axioms (`cauchySeq_simpleIntegralLp_compensated`, `adaptedSimple_dense_L2_compensated`) that the 2026-05-10 unified-existence refactor made redundant; **flagged for follow-up removal as red-team finding M4.**"
  - `tools/full_audit.lean:8`: "every theorem listed should have axiom set ⊆ {propext, Classical.choice, Quot.sound} ∪ {the **11 Tier 1 cited axioms** documented in tools/cited_axioms.md}"
  - `tools/full_audit.lean:12`: "The **9 currently-live Tier 1 cited axioms** (axioms #7 and #8 were deleted 2026-05-22..."
  - `tools/cited_axioms.md:10` (header): "Tier 1: Honest cited axioms (**9 currently live; #7 and #8 deleted 2026-05-22**)"
  - `tools/cited_axioms.md:220-221` (`MEDIUM` fix log): "**M4** (Tier 1 #7 + #8 dead post-refactor): retained pending careful walk-up deletion of the intertwined dead chain (substantial follow-up)."
  - `README.md:60`: "9 axioms total"
  - `audit_output.txt`: enumerates exactly 9 distinct cited axioms (verified count).
- **Why this matters**: Three different files give three different answers on the same factual question. `STATUS.md` (dated 2026-05-22) says 11 axioms AND that the two extra are "flagged for follow-up removal" — but `cited_axioms.md` (also dated 2026-05-22) says the two were DELETED on that day. `full_audit.lean`'s docstring CONTRADICTS ITSELF — line 8 says 11, line 12 says 9. The audit script and the README correctly say 9. A Mathlib reviewer who reads STATUS.md first ("Status: Tier 1 cited axioms (11)") will form a mistaken model of the library's axiom budget, then notice the discrepancy with audit_output.txt and lose trust in the documentation. The honest count is 9.
- **Recommendation**: One edit to `STATUS.md` (the "Tier 1 cited axioms" header and bullet list); one edit to `tools/full_audit.lean:8` (change `11` → `9`); one edit to `tools/cited_axioms.md:220-221` (M4 already closed by deletion; mark as such).

### Finding 3 — `README.md` and `STATUS.md` list TWO file names that do not exist in the source tree

- **Severity**: HIGH
- **Locations**:
  - `README.md:34`: `│   ├── BrownianMotion.lean                    — structure + Tier 1 #1 axiom`
  - `README.md:36`: `│   ├── NaturalFiltration.lean                 — filtration definition`
  - `STATUS.md:82`: same two non-existent files
- **Evidence**: `ls D:/LevyStochCalc/LevyStochCalc/Brownian/` returns: `Construction.lean Continuity.lean Ito.lean Martingale.lean Multidim.lean MultidimIto.lean SimplePredictableRefine.lean`. There is no `Brownian/BrownianMotion.lean`; the `BrownianMotion` structure + Tier 1 #1 `BrownianMotion.exists` axiom both live in `Brownian/Construction.lean`. There is no `Brownian/NaturalFiltration.lean`; the natural-filtration definition lives in `Brownian/Martingale.lean` (line 54). The Poisson counterpart `Poisson/NaturalFiltration.lean` does exist, which is probably why the README author assumed the Brownian one would mirror.
- **Why this matters**: A new user running through the README's "Layout" section will `cat LevyStochCalc/Brownian/BrownianMotion.lean` and get a `cat: No such file or directory` error. The layout block is the orientation tool for new contributors; getting the file names wrong defeats its purpose. Same issue for the docstring on `LevyStochCalc.lean`'s self-described layer scheme.
- **Recommendation**: In both `README.md` and `STATUS.md`, change the "Brownian/" layout block to reflect the actual files (`Construction.lean — structure + Tier 1 #1 axiom`, then list `Continuity.lean`, `Martingale.lean — naturalFiltration + Tier 1 #4 axiom`, `Multidim.lean`, `MultidimIto.lean`, `Ito.lean`, `SimplePredictableRefine.lean`).

### Finding 4 — Library ships ZERO examples or tests demonstrating the public API

- **Severity**: HIGH
- **Evidence**: `glob "D:/LevyStochCalc/**/example*.lean"` returns nothing; `glob "D:/LevyStochCalc/**/test*.lean"` returns nothing (only Mathlib's own); `grep -rn "^example" LevyStochCalc/` returns no in-project example blocks demonstrating how to USE the public API. The `tools/` folder contains `lint.sh`, `full_audit.lean`, `cited_axioms.md`, `sorry_baseline.txt` — no `tools/examples/`. The `docs/` folder is empty (verified by `ls -la`).
- **Why this matters**: A Mathlib PR reviewer's third action (after "does it build" and "are there sorries") is to look for `example` blocks demonstrating the API. For a library that claims to "discharge the four cited continuous-time axioms" of a downstream dissertation, the reviewer expects at least: (a) an `example` showing how to construct a Brownian motion via `BrownianMotion.exists`, (b) an `example` constructing a Poisson random measure via `PoissonRandomMeasure.exists_of_sigmaFinite`, (c) an `example` showing the Itô isometry `itoLevyIsometry` applied to a specific predictable integrand, (d) an `example` instantiating `IsBSDEJSolution` for a trivial driver (e.g. `f = 0, g = 0`). None exist. The closest thing to a usage example is the downstream sister repo `D:/Dissertation/Dissertation/Continuous.lean` — but that's out-of-scope per the shared context. A library with zero in-repo `example` blocks signals to a reviewer that the API is unused externally, hence (a) untested in practice and (b) liable to break under refactoring.
- **Recommendation**: Add `LevyStochCalc/Examples.lean` (or a `tests/` directory) with at minimum the four examples above. Each `example` block doubles as a smoke test: if a future Mathlib API rename breaks the type signature, the example block will fail to compile and CI will catch it.

### Finding 5 — H6 "closure" is documentation-only; the axiom signature still over-claims predictability-vs-measurability per the docstring's own admission

- **Severity**: HIGH (literature-divergence misleading a reviewer)
- **Location**: `Poisson/Compensated.lean:1755-1764` (docstring) and `:1793-1819` (axiom signature, master HEAD)
- **Evidence** (verbatim docstring, master HEAD 237cc19):
  > **Hypothesis-strength caveat (red-team H6, 2026-05-22)**: the signature gates conjuncts on `Measurable (Function.uncurry φ)` rather than on `ProgMeasurable Filt φ` (predictable in the literature sense). The literature claim is for **predictable** φ; the present signature is strictly weaker on this axis (it asserts the conjuncts for arbitrary joint-measurable φ, not just predictable). In practice this gap is harmless: every load-bearing caller (the BSDEJ + Itô-Lévy formula chain) provides φ via `IsBSDEJSolution`'s adaptedness layer, which delivers progressive measurability. Strengthening the axiom to require ProgMeasurable is a multi-file signature refactor tracked as future work; **the present axiom over-claims by one σ-algebra but the over-claim is not exploited anywhere in the audited chain.**
- **Why this matters**: The shared-context override claims "H6 added a documented caveat noting the signature uses `Measurable` not `ProgMeasurable`." That's true — the docstring was added — but the underlying gap is that the **axiom signature is mathematically over-strong** relative to Applebaum 2009 Thm 4.2.3. Applebaum's theorem is about predictable (σ(𝒫)-measurable) integrands; the Lean axiom asserts the same conclusion for arbitrary jointly-measurable integrands. A Mathlib reviewer comparing the Lean axiom statement against Applebaum 4.2.3 would correctly observe that the Lean version asserts something stronger than the cited paper proves. The "harmless in practice" claim is true (no caller exploits the gap) but does not change the fact that the axiom AS STATED claims more than its citation supports. For a project that has set up an explicit `tools/cited_axioms.md` precisely to ensure axiom statements faithfully match cited theorems, this is a Rule-0 violation by the project's own standard. The 1st audit's persona-10 Finding 4 made the same observation; the 2026-05-22 fix only added the caveat docstring, leaving the soundness/literature gap open.
- **Recommendation**: Either (a) make H6 a real fix by adding `(h_predMeas : ProgMeasurable ... φ)` to the axiom signature and threading it through the BSDEJ + Itô-Lévy callers (multi-file refactor, per the docstring's own admission), or (b) restate the cited axiom as the "L²-Itô-Lévy integral for jointly-measurable integrands" with a separate downstream theorem proving that when φ is genuinely predictable the cited Applebaum 4.2.3 form is recovered. The current state — claim that Applebaum 4.2.3 supports the Lean axiom signature — is a literature divergence.

### Finding 6 — `Brownian/SimplePredictableRefine.lean` houses Tier 1 axiom #5 but is named after a notion (`simplePredictableRefine`) that the axiom bypasses

- **Severity**: MEDIUM (naming + organization hygiene)
- **Location**: `LevyStochCalc/Brownian/SimplePredictableRefine.lean:2106` (axiom site)
- **Evidence**: The Tier 1 axiom #5 `itoIsometry_brownian_unified_existence` lives in a file named `SimplePredictableRefine.lean`, but the axiom statement makes no reference to simple-predictable refinement — it's the unified-existence statement for the L² Itô integral, in the same shape as the Compensated counterpart in `Poisson/Compensated.lean`. The shared-context override doc says `Brownian/Ito.lean` is "L² Itô integral chain (4000+ lines)" while `SimplePredictableRefine.lean` is the cited-axiom site. A Mathlib reviewer reading the layout in `README.md` (which says: "├── Ito.lean — L² Itô integral (4000+ lines) ├── SimplePredictableRefine.lean — Tier 1 #5 axiom") would expect `Ito.lean` to contain the canonical integral and `SimplePredictableRefine.lean` to be a supporting density-chain module. The Tier 1 axiom for the L² Itô isometry living there is naming-confusing.
- **Why this matters**: For a library wanting Mathlib acceptance, the file naming convention follows the module's purpose. `SimplePredictableRefine.lean` literally describes "refining the simple-predictable density chain" — but the file's load-bearing content is the unified-existence axiom that *bypasses* the density chain entirely (the cited-axiom approach was taken precisely because the density chain wasn't completed). The file would be more honestly named `UnifiedItoIsometry.lean` or `ItoIsometryAxiom.lean`. Mathlib reviewers care about file/module hygiene because it determines downstream import patterns.
- **Recommendation**: Rename `Brownian/SimplePredictableRefine.lean` to something that reflects its actual content (Tier 1 axiom + the `stochasticIntegral` definition via `Classical.choose`). Or move the axiom into `Brownian/Ito.lean` (which already imports SimplePredictableRefine.lean for the same Classical.choose chain) and delete the standalone file.

### Finding 7 — Top-level repo contains an `_mcp_snippet_*.lean` debris file that should never be committed

- **Severity**: MEDIUM (code-hygiene)
- **Location**: `D:\LevyStochCalc\_mcp_snippet_952bdcfd68b74942a7ef219170b0f2aa.lean`
- **Evidence**: An 18-line file with `example (g : ℝ → ℝ) (h_meas ...) : LocallyIntegrable g volume := by ...` sits at the project root. The filename starts with `_mcp_snippet_` and ends with a UUID — this is artifact debris from an MCP-tool session (`mcp__lean-lsp__lean_run_code` writes snippets to such files). It is present in the working tree at the project root.
- **Why this matters**: Mathlib reviewers run `ls D:/LevyStochCalc/` first to understand the project surface. An `_mcp_snippet_*.lean` file at the project root signals (a) the maintainer doesn't sweep MCP-generated debris, (b) the `.gitignore` patterns are not catching `_mcp_*` files, (c) the file may have been accidentally committed and forgotten. The file isn't imported by `LevyStochCalc.lean` so it's harmless to the build, but it's visible debris that should be swept.
- **Recommendation**: `rm _mcp_snippet_952bdcfd68b74942a7ef219170b0f2aa.lean; echo "_mcp_snippet_*.lean" >> .gitignore`.

### Finding 8 — `BSDEJ/MartingaleRepresentation.lean` module docstring (lines 34-43) claims "Signature HOLE still open" — but the signature was actually closed (canonical-integral pinning at lines 105-109)

- **Severity**: MEDIUM (stale docstring contradicting code; misleads a reviewer)
- **Location**: `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:35-43`
- **Evidence**:
  > **Signature HOLE still open**: the existential `∃ Z U BM_integral jump_integral, … ∧ ξ = 𝔼[ξ] + BM_integral + jump_integral` does NOT pin `BM_integral` to `∫ Z·dW` or `jump_integral` to `∫∫ U Ñ`. Per Rule 0, that pinning is required for the claim to match the content. Pinning `jump_integral` to `Compensated.stochasticIntegral N U T` is feasible immediately ... Pinning `BM_integral` to `∑_i ∫ Zⁱ dWⁱ` requires the multidim Brownian Itô integral, which is downstream work.
  >
  > The signature strengthening + proof completion is the next step.

  But the actual `jacodYor_representation` signature (lines 74-109, master HEAD) ALREADY pins both integrals: `MultidimBrownianMotion.stochasticIntegral W Z h_Z_meas h_Z_progMeas h_Z_sq_int T ω` and `Compensated.stochasticIntegral N (fun ω' s e => U s ω' e) T ω`. The shared-context override confirms: "jacodYor_representation signature: BM_integral pinned to `MultidimBrownianMotion.stochasticIntegral W Z`, jump_integral pinned to `Compensated.stochasticIntegral N U` (C4 fix)."
- **Why this matters**: A Mathlib reviewer reading the module docstring concludes the signature is still vacuous (trivial-witness exploitable). That contradicts the actual signature. The 1st-audit's C4 fix is complete in the Lean code but the narrative was not updated to match. This pattern of "code fixed, docstring stale" recurs elsewhere (Finding 2's STATUS.md inconsistency, Finding 1's stale top-level docstring).
- **Recommendation**: Update the module docstring to "Signature pinned 2026-05-21 (C4 closure): both `BM_integral` and `jump_integral` are now CANONICAL — `MultidimBrownianMotion.stochasticIntegral W Z ...` and `Compensated.stochasticIntegral N U`. The remaining work is the proof body (predictable-projection chaos decomposition)."

### Finding 9 — Empty `docs/` directory persists despite 1st audit Finding 8 explicit recommendation to delete or fill

- **Severity**: MEDIUM
- **Location**: `D:\LevyStochCalc\docs\` (verified empty by `ls -la`: 0 files)
- **Evidence**: 1st audit persona-10 Finding 8 said: "Add a `README.md` ... Also delete the empty `docs/` folder (or fill it)." The README was added — good — but the empty `docs/` folder persists with date `May 2 16:35` (untouched since project bootstrap).
- **Why this matters**: An empty `docs/` directory is a "documentation TODO" smell. A Mathlib reviewer reading the project layout sees the `docs/` directory in `ls D:/LevyStochCalc/` and expects content; opening it and finding nothing signals abandoned documentation effort. Either fill it (with the per-axiom long-form documentation referenced in `cited_axioms.md`) or delete it.
- **Recommendation**: `rmdir D:/LevyStochCalc/docs/` (empty directory should not be committed); add `docs/` ignore to `.gitignore` only if documentation is genuinely planned.

### Finding 10 — `STATUS.md` references a moved file path: `redteam_findings/_REDTEAM_SUMMARY.md` does not exist at that path (the file is in `redteam_findings/2026-05-20-archive/_REDTEAM_SUMMARY.md`)

- **Severity**: LOW
- **Location**: `STATUS.md:119-120`
- **Evidence**:
  - `STATUS.md:119`: `* `redteam_findings/_REDTEAM_SUMMARY.md` — 2026-05-20 red-team audit (meta-summary across 12 personas).`
  - Actual location: `redteam_findings/2026-05-20-archive/_REDTEAM_SUMMARY.md`
- **Why this matters**: Broken cross-reference in user-facing documentation. A reviewer trying to follow the link to understand the audit context gets a stale path.
- **Recommendation**: Update `STATUS.md:119` to the correct archive path.

### Finding 11 — `README.md`'s Tier 1 enumeration jumps from 6 to 9, with the deletion-explanation buried below — confusing on first read

- **Severity**: LOW
- **Location**: `README.md:63-73`
- **Evidence** (verbatim):
  ```
  1. `BrownianMotion.exists` — ...
  2. `PoissonRandomMeasure.exists_of_sigmaFinite` — ...
  3. `kolmogorovChentsov_modification` — ...
  4. `brownian_martingale_rightCont` — ...
  5. `itoIsometry_brownian_unified_existence` — ...
  6. `itoIsometry_compensated_unified_existence` — ...
  9. `continuousBSDEJ_exists_unique` — ...
  10. `bsdej_path_regularity` — ...
  11. `itoLevyFormula` — ...

  (Original Tier 1 #7 + #8 were deleted 2026-05-22 as dead post-refactor.)
  ```
- **Why this matters**: A reader scanning the headline list assumes "9 axioms total" (per the line 60 sentence), then sees the numbering 1..6, 9, 10, 11 and stops to wonder if axioms 7 and 8 were missed. The explanatory parenthetical comes AFTER the list — by then the reader has already lost the flow. Either renumber the live axioms 1..9 consecutively (and keep the historical numbering in `cited_axioms.md` for git-blame continuity), OR move the deletion note to BEFORE the list.
- **Recommendation**: Renumber to 1..9 consecutively in `README.md`; keep `cited_axioms.md`'s 11-slot numbering scheme as the canonical historical reference. Or invert: list axioms by name only (no numbers) in `README.md`, keeping the numbered scheme in `cited_axioms.md`.

### Finding 12 — `cited_axioms.md`'s fix log internally contradicts itself on M4 and M11

- **Severity**: LOW
- **Location**: `tools/cited_axioms.md:220-237`
- **Evidence**:
  - Lines 220-221 (`MEDIUM` section): "**M4** (Tier 1 #7 + #8 dead post-refactor): retained pending careful walk-up deletion of the intertwined dead chain (substantial follow-up)."
  - Lines 235-237 (`Open / deferred`): "**M11** (`IsBSDEJSolution` filtration trivial-constant): the natural-filtration-pin requires `joint_past_future_independent` exposure through the BSDEJSolution structure; deferred."

  Both claims are stale. M4 is closed (#7 and #8 are deleted per cited_axioms.md's own header line 10, per `audit_output.txt` showing only 9 cited axioms, per commit `123e32e Delete dead Tier 1 #7/#8 axiom chain — ~490 lines`). M11 is closed per commit `9b693c5 Close red-team L9, L10, M11`. The fix log doesn't reflect either closure.
- **Why this matters**: Same stale-narrative class as Findings 2, 8. A Mathlib reviewer reading the fix log to understand the project's red-team responsiveness sees "M4 retained pending..." and concludes that the dead chain is still present — then notices the cited_axioms.md elsewhere says it's deleted. The fix log lies about its own current state.
- **Recommendation**: Update lines 220-221 to "M4 closed by commit `123e32e` — Tier 1 #7 + #8 chain deleted, ~490 lines removed"; update lines 235-237 to "M11 closed by commit `9b693c5` — `IsBSDEJSolution` Filt now constrained by `naturalFiltration W ≤ Filt ∧ naturalFiltration N ≤ Filt`".

### Finding 13 — `CONTRIBUTING.md` Rule 0 list is good but omits the most important practical guidance: "How to add a new Tier 1 axiom citation"

- **Severity**: LOW (gap in the contributor guide)
- **Location**: `CONTRIBUTING.md:43-49`
- **Evidence**: The `Adding a new cited axiom` section reads:
  > 1. The axiom statement must match a published theorem citation precisely.
  > 2. Add a Tier 1 entry to `tools/cited_axioms.md` with paper reference, Mathlib status, and replacement plan.
  > 3. Update `_audit.lean` and `tools/full_audit.lean` to include it.
  > 4. Verify `bash tools/lint.sh` still passes.
- **Why this matters**: The checklist is good but doesn't specify *what counts as a precise citation match*. A new contributor adding `axiom myFavoriteTheorem` could correctly add a citation to `cited_axioms.md` and pass `lint.sh` — without anyone catching that the citation's Theorem 4.2.3 actually says something slightly different from the Lean axiom statement (the FIRST-audit citation defects were of this type: "Le Gall Thm 2.1" — no such theorem). The guidance "must match precisely" doesn't tell the contributor *how* to verify the match.
- **Recommendation**: Add a "Citation-verification checklist" subsection: "(a) Open the cited textbook/paper, locate the named theorem/proposition by exact number; (b) cross-check the Lean axiom's quantifier structure, hypotheses, and conclusion against the published statement; (c) for ambiguous cases (e.g., 'Definition + Theorem combo'), list all locations; (d) if the citation can't be cross-checked from a freely available source (open-access paper, author's webpage), also list a secondary citation from a different source confirming the same theorem; (e) ensure the citation has author + year + venue + page/theorem-number, not just 'Applebaum 2009'."

### Finding 14 — Positive verification — `Compensated.lean` per-T independent caveat from 1st audit Finding 13 is correctly resolved on master HEAD

- **Severity**: VERIFIED (1st-audit issue correctly closed)
- **Location**: `LevyStochCalc/Poisson/Compensated.lean:38-69` (module docstring)
- **Evidence**: The module docstring lines 44-69 honestly state the post-2026-05-10 unified-existence refactor and explicitly note that the previous per-T-independent caveat is now closed. Reading the docstring lines 60-69 confirms it discusses the historical state, not the current one. The `stochasticIntegral` definition at line 1825 uses the unified existence axiom.
- **Why this matters**: This is one of the few places where the docstring narrative is consistent with the code. Highlighting as a positive: shows the project CAN do this when attention is paid.

## Per-claim verdicts on the public API surface

Mapping the 9 live Tier 1 cited axioms + 11 honest-derivative theorems listed in `cited_axioms.md`:

| Theorem / axiom | Verdict | One-line note |
|---|---|---|
| **Tier 1 #1** `BrownianMotion.exists` | EARNED | Honest axiom; citation now correct (Definition 2.1 / 2.12 / Cor 2.11); replacement plan clear. |
| **Tier 1 #2** `PoissonRandomMeasure.exists_of_sigmaFinite` | EARNED | Honest axiom; integer_valued field added per L10; PRM structure honest. |
| **Tier 1 #3** `kolmogorovChentsov_modification` | EARNED | Honest axiom; `kolmogorov_modification_ae_eq` now proved (no sorryAx). |
| **Tier 1 #4** `brownian_martingale_rightCont` | EARNED | Honest axiom; citation now correctly Thm 2.13 (not Prop 2.10). |
| **Tier 1 #5** `itoIsometry_brownian_unified_existence` | EARNED | Honest axiom; correctly hypothesised (h_meas + h_progMeas + h_sq_int_global). |
| **Tier 1 #6** `itoIsometry_compensated_unified_existence` | **WEAK** | H6 documentation-only closure leaves the signature over-claiming on predictability vs measurability. See Finding 5. |
| **Tier 1 #9** `continuousBSDEJ_exists_unique` | EARNED | Now correctly hypothesised with Lipschitz + L²-terminal; `IsBSDEJSolution` predicate adaptedness-strengthened. |
| **Tier 1 #10** `bsdej_path_regularity` | EARNED | Citation fixed (Bouchard-Elie 2008 SPA 118(1)); constant C now (T, L, ‖ξ‖)-parameterised per M8. |
| **Tier 1 #11** `itoLevyFormula` | EARNED | All 4 terms pinned to literature integrals; no more trivial-witness escape. |
| `BrownianMotion.exists` derived: `MultidimBrownianMotion.exists` | EARNED | Honest derivative; joint_measurable field constructed in project_BM. |
| `kolmogorovChentsov_modification` derived: `brownian_continuous_modification` | EARNED | Honest derivative. |
| `brownian_martingale_rightCont` derived: `brownian_filtration_rightContinuous` | EARNED | Honest derivative. |
| `#5` derived: `Brownian.Ito.{itoIsometry,martingale_stochasticIntegral,quadVar_stochasticIntegral}` | EARNED | Conjunct extractions, honest. |
| `#6` derived: `Compensated.{itoLevyIsometry,martingale_stochasticIntegral,quadVar_stochasticIntegral,cadlag_modification_exists}` | EARNED (modulo Finding 5) | Conjunct extractions; inherit the H6 over-claim. |
| `L2Isometry.itoLevyIsometry` | EARNED | 1-line forwarder; stale "carries substantive sorry" docstring is now removed. |
| `JumpDiffusion.exists_unique` (baseline sorry) | EARNED (baseline) | `is_solution` field strengthened from `True` to real SDE integral equation; sorry'd proof; in baseline. |
| `jacodYor_representation` (baseline sorry) | EARNED (baseline modulo Finding 8) | Signature pinned to canonical integrals; sorry'd proof; in baseline. Module docstring stale (claims signature hole still open). |

## Mathlib-PR-acceptability assessment

Would this library be acceptable as a Mathlib PR? **No, and the reason is structural, not cosmetic.**

A Mathlib PR fundamentally cannot introduce user-facing axioms. The 9 Tier 1 axioms — even if each is a faithful encoding of a published theorem — must be reduced to `theorem`s built on Mathlib's existing primitives (`MeasureTheory.IsProjectiveLimit`, `ProbabilityTheory.gaussianReal`, `ProbabilityTheory.poissonMeasure`, `MeasureTheory.Filtration`, `MeasureTheory.IsKolmogorovProcess`, `MeasureTheory.condExpL2_continuous`) before any merger can happen. The project's own `cited_axioms.md` acknowledges this with explicit "Replacement plan" sections per axiom — but those are aspirational, not actionable today. The Degenne et al. `arXiv:2511.20118` work on Brownian-motion-in-Lean is the closest active push toward unblocking #1 / #3 / #5; the Poisson side has no equivalent active push (cited_axioms.md notes "No current Mathlib activity for Poisson random measures or general Lévy processes" under #2 and #6).

So the realistic Mathlib-acceptance path is: the LevyStochCalc library remains a *downstream consumer* of Mathlib, gradually replacing its Tier 1 axioms with theorem forwarders as Mathlib gains the corresponding infrastructure. The README correctly frames this. But there are several additional Mathlib-acceptability blockers that would apply even to the *derivative theorems*:

- **`BrownianMotion` structure design**: the project uses a bespoke `structure BrownianMotion (P : Measure Ω) [IsProbabilityMeasure P] where W : ℝ → Ω → ℝ; measurable_eval : ...; joint_measurable : ...; initial_zero : ...; increment_gaussian : ...; increment_independent : ...; continuous_paths : ...; negative_zero : ...; joint_increment_independent : ...`. Mathlib's typeclass-first style would prefer `class IsBrownianMotion (W : ℝ → Ω → ℝ) (P : Measure Ω) : Prop where ...` so the BM structure inherits / interacts with existing `IsGaussianProcess`, `IsMarkovKernel`, etc. The 8-field structure also bundles `joint_increment_independent` and `negative_zero` as auxiliary fields that smell of "added because the proof of X failed without them" — a Mathlib reviewer would push back on those.
- **`MultidimBrownianMotion`**: defined as `structure ... where W : Fin d → BrownianMotion P; components_independent : iIndepFun ...`. Mathlib's idiom would be: `def MultidimBrownianMotion P d := ∀ i : Fin d, IsBrownianMotion (Wi i) P ∧ iIndepFun (fun i => Wi i)`, or a typeclass extending the scalar one over a finite product. The current structure makes the multidim BM a *list* of independent BMs rather than a vector-valued process; downstream usage in BSDEJ requires the latter view.
- **`Compensated.stochasticIntegral` definition**: `noncomputable def stochasticIntegral N φ T := (Classical.choose ...) T` — Mathlib accepts `Classical.choose` definitions but reviewers usually push toward `Lp.toLinearMap` / `condExpL2`-style API that's compatible with the `Lp` typeclass machinery. The current definition returns `Ω → ℝ` rather than a `Lp ℝ 2 P` element, so downstream Lp-norm reasoning has to manually re-derive ENNReal forms.
- **Comparison to Mathlib's `MeasureTheory.IsProjectiveLimit`**: the BM construction story would naturally route through `IsProjectiveLimit` applied to the finite-dimensional Gaussian families. The project's `Brownian/Construction.lean` mentions this in the docstring (line 159-161: "Apply the Kolmogorov extension theorem (Mathlib: `MeasureTheory.IsProjectiveLimit`)") but doesn't actually invoke it — the axiom is bare. A Mathlib PR would have to do the actual `IsProjectiveLimit`-style construction.
- **Comparison to Mathlib's `ProbabilityTheory.poissonMeasure`**: this is the ℕ-valued Poisson distribution (one-dimensional). The PRM structure in this project wraps a different concept (random measure on `ℝ × E`). The connection is mentioned in cited_axioms.md but not exploited — `poissonMeasure` is used only in the `poisson_law` field as the *marginal* distribution. A Mathlib reviewer would ask for a clearer link.

Beyond the design issues, the items that would block PR acceptance even after axiom-replacement:

1. **Per-file copyright headers**: present and Mathlib-style (verified on 6 files). Good.
2. **Module docstrings**: most are present and substantive, though several are stale (per Findings 1, 8, 12).
3. **Naming conventions**: mostly Mathlib-style; some camelCase vs snake_case drift in private lemmas (visible by grepping `_` patterns in `Brownian/Ito.lean`).
4. **`Basic.lean` umbrella import**: the file does `import Mathlib` (a 2GB blob). Mathlib's contribution guidelines explicitly discourage this. The file's docstring acknowledges this is a known L3 finding and explains the trade-off. A PR reviewer would still flag it.
5. **No `set_option autoImplicit false`**: lakefile has `relaxedAutoImplicit = false`. Verified, good.
6. **No examples/tests demonstrating API**: see Finding 4.
7. **CI workflow exists**: see `.github/workflows/ci.yml`. Good, but it only runs `lake build` + `lint.sh` — no upstream-Mathlib-update test, no doc-gen check, no taintness test for the per-file axiom budget.

## Comparison to Mathlib's existing infrastructure (per the audit prompt)

| Mathlib API | LevyStochCalc's usage | Verdict |
|---|---|---|
| `MeasureTheory.IsProjectiveLimit` | Mentioned in docstrings (Brownian/Construction.lean:159-161) but not invoked; the BM axiom is bare. | Wraparound, not consumption. |
| `ProbabilityTheory.gaussianReal` | Used directly in `BrownianMotion.increment_gaussian` field (Construction.lean:54). | Consumed. |
| `ProbabilityTheory.poissonMeasure` (via `poissonMeasureENN`) | Used in `PoissonRandomMeasure.poisson_law` field (RandomMeasure.lean:98). | Consumed. |
| `MeasureTheory.Filtration` | Used everywhere (BSDEJ/Definition.lean, Compensated.lean, etc.). | Consumed. |
| `MeasureTheory.Filtration.natural` | Used in `Brownian.Martingale.naturalFiltration` (Martingale.lean:54). | Consumed. |
| `ProbabilityTheory.IsKolmogorovProcess` | Mentioned in `cited_axioms.md` #3 but the in-project `kolmogorovChentsov_modification` axiom does NOT take an `IsKolmogorovProcess` hypothesis — it states the conclusion directly. | Wraparound. |
| `MeasureTheory.Adapted` | Used in `IsBSDEJSolution` (Definition.lean:160). | Consumed. |
| `MeasureTheory.Martingale` | Used everywhere. | Consumed. |
| `MeasureTheory.condExpL2_continuous` | Mentioned in cited_axioms.md #5 but not invoked. | Wraparound. |
| `MeasureTheory.iIndepFun_pi` | Used in `MultidimBrownianMotion.exists` derivative (Multidim.lean). | Consumed. |
| `MeasureTheory.Measure.pi` | Used in `MultidimBrownianMotion.exists` derivative. | Consumed. |
| `Probability.Kernel.IonescuTulcea.trajMeasure` | Not used; bypassed by the Tier 1 #1 axiom. | Wraparound. |

The library consumes Mathlib measure-theory primitives in the right places, but the load-bearing axioms WRAP the gaps where Mathlib doesn't yet have BM / PRM / IsKolmogorovProcess-modification. The pattern is appropriate for a "downstream library waiting on Mathlib" — but is not yet ready to be merged INTO Mathlib.

## What you couldn't verify

- **Whether the H6 over-claim is actually exploitable by a malicious caller**: the docstring says "the over-claim is not exploited anywhere in the audited chain." I did not write a counter-example caller that constructs a non-progressive-measurable `φ`, calls `itoIsometry_compensated_unified_existence` to get an `F`, and uses the unconditional martingale + quadVar + càdlàg conjuncts to derive something mathematically false. P12 (adversarial hole hunter) should check this.
- **Whether the `_mcp_snippet_*.lean` debris file's content (a `LocallyIntegrable` lemma) is actually useful and should be promoted into the library**, or is truly debris.
- **Whether the dependency graph in `LevyStochCalc.lean` (the `import` order) is acyclic and minimal**: did not run `lean4-import-graph`.
- **Whether `tools/full_audit_output.txt` matches the live output of `tools/full_audit.lean`**: did not re-run; assumed the committed file is recent.
- **Whether the Mathlib version pinned in `lakefile.toml` (rev `0e208554a6143756c125878a8fe8b17a331d39f7`) is currently the master branch**: did not check upstream.
- **Whether the documented commits referenced in `cited_axioms.md`'s fix log (e.g. `2d9309e`, `1b1f69f`, `7d232bf`) are real commits**: spot-checked `123e32e`, `9b693c5`, `b065b7d`, `eb707a4`, `638b21d` against `git log --all --oneline` and confirmed those five exist; did not spot-check all 17 referenced commits.

## Recommendations for the project (≤ 5 bullets, prioritised)

- **Fix `LevyStochCalc.lean:44`'s fabricated citation (Finding 1)** as the highest-priority single-line edit. The top-level module docstring is the front door of the library; leaving the fabricated "Bouchard-Elie-Touzi 2009 Thm 2.1" there after the citation cleanup completely undermines the project's claim that the citation defects are closed.
- **Reconcile the 9 vs 11 Tier 1 axiom count across `README.md`, `STATUS.md`, `tools/full_audit.lean`, and `tools/cited_axioms.md` (Findings 2, 11, 12)**. The correct count is 9 (verified by `audit_output.txt`). STATUS.md is the most-stale; `full_audit.lean`'s docstring contradicts itself on lines 8 and 12. Run a `grep -rn '11 Tier 1\|axioms (11)\|^11\.'` sweep and fix everywhere.
- **Fix the README.md and STATUS.md "Layout" sections (Finding 3)** to reflect the actual `Brownian/` directory contents. `Brownian/BrownianMotion.lean` and `Brownian/NaturalFiltration.lean` do not exist; the contents live in `Brownian/Construction.lean` and `Brownian/Martingale.lean` respectively. This is a new-user blocker.
- **Add at least 4 `example` blocks demonstrating the public API (Finding 4)**, ideally as `LevyStochCalc/Examples.lean`. The examples double as smoke tests against upstream Mathlib API drift. Without any examples, the library reads as "a collection of axiom statements" rather than "a usable formalisation."
- **Decide on the H6 closure strategy (Finding 5)**: either commit to the multi-file ProgMeasurable refactor and actually close the gap in the axiom signature, or restate the cited axiom as "L²-Itô-Lévy integral for jointly-measurable integrands" with an honest scope note. The current "documentation-only" closure makes Tier 1 #6 the weakest link in the cited-axioms chain.

## Files read (selection — full traversal)

`D:\LevyStochCalc\README.md`, `D:\LevyStochCalc\LICENSE` (lines 1-30 + 175-201 verified Apache 2.0 boilerplate complete), `D:\LevyStochCalc\CONTRIBUTING.md`, `D:\LevyStochCalc\STATUS.md`, `D:\LevyStochCalc\LevyStochCalc.lean`, `D:\LevyStochCalc\_audit.lean`, `D:\LevyStochCalc\audit_output.txt`, `D:\LevyStochCalc\lakefile.toml`, `D:\LevyStochCalc\lake-manifest.json`, `D:\LevyStochCalc\.github\workflows\ci.yml`, `D:\LevyStochCalc\_mcp_snippet_952bdcfd68b74942a7ef219170b0f2aa.lean`, `D:\LevyStochCalc\tools\cited_axioms.md` (full), `D:\LevyStochCalc\tools\full_audit.lean`, `D:\LevyStochCalc\tools\full_audit_output.txt`, `D:\LevyStochCalc\tools\lint.sh`, `D:\LevyStochCalc\tools\sorry_baseline.txt`, `D:\LevyStochCalc\LevyStochCalc\Basic.lean`, `D:\LevyStochCalc\LevyStochCalc\Notation.lean`, `D:\LevyStochCalc\LevyStochCalc\Brownian\Construction.lean` (lines 1-173), `D:\LevyStochCalc\LevyStochCalc\Brownian\Continuity.lean` (lines 1-100), `D:\LevyStochCalc\LevyStochCalc\Brownian\Multidim.lean` (lines 1-180), `D:\LevyStochCalc\LevyStochCalc\Brownian\Martingale.lean` (axiom site grep), `D:\LevyStochCalc\LevyStochCalc\Brownian\SimplePredictableRefine.lean` (axiom site), `D:\LevyStochCalc\LevyStochCalc\Brownian\Ito.lean` (declaration count grep), `D:\LevyStochCalc\LevyStochCalc\Poisson\RandomMeasure.lean` (lines 70-205), `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean` (lines 1-80 + 1750-1834 axiom + diff vs master), `D:\LevyStochCalc\LevyStochCalc\Poisson\L2Isometry.lean`, `D:\LevyStochCalc\LevyStochCalc\Poisson\NaturalFiltration.lean` (existence confirmation only), `D:\LevyStochCalc\LevyStochCalc\Ito\Setting.lean` (lines 35-150), `D:\LevyStochCalc\LevyStochCalc\Ito\JumpFormula.lean` (lines 1-198 axiom site), `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean` (full), `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean` (axiom site), `D:\LevyStochCalc\LevyStochCalc\BSDEJ\PathRegularity.lean` (lines 1-150), `D:\LevyStochCalc\LevyStochCalc\BSDEJ\MartingaleRepresentation.lean` (full), `D:\LevyStochCalc\redteam_findings\shared_context_override.md` (full), `D:\LevyStochCalc\redteam_findings\2026-05-20-archive\10_dissertation_examiner.md` (full).

**Live build verification**: `cd D:/LevyStochCalc && git stash && lake build` → "Build completed successfully (8402 jobs)" with 2 sorry warnings (= baseline). Master HEAD `237cc19` builds clean. (Worktree-local uncommitted modifications to `Poisson/Compensated.lean` were observed BREAKING the build with two type errors at `Compensated.lean:1795` and `:1797`; this is a transient working-tree state, not master HEAD. The worktree's `Compensated.lean` attempt to mirror the Brownian-side hypothesis pattern as a strengthened axiom signature appears to be in-progress work that doesn't compile against the existing `naturalFiltration` namespace.)
