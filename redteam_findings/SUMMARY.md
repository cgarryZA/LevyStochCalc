# LevyStochCalc Red Team Audit — Meta-Summary

**Date**: 2026-05-20
**Target**: `D:\LevyStochCalc\` (commit `db582f9` on `master` + untracked working tree)
**Auditors**: 12 parallel personas, each independent, each writing to `redteam_findings/<persona>.md`
**Combined findings**: 12 reports, ~450KB, ~140 individual findings across personas
**Meta-summary author**: orchestrator (this file)

## Headline (one paragraph)

The library does NOT survive adversarial review. The 2026-05-11 "recursive audit" closed one of three structurally identical trivial-witness patterns and was reported as exhaustive — the red team found **two more trivial-witness theorems** (`Ito.Setting.JumpDiffusion.exists_unique`, `BSDEJ.MartingaleRepresentation.jacodYor_representation`) plus **a third in the axiom STATEMENT layer** (`Ito.JumpFormula.itoLevyFormula` was demoted from theorem to axiom but the axiom's existential is itself trivially satisfiable). The Tier 1 #9 axiom `BSDEJ.Existence.continuousBSDEJ_exists_unique` is **mathematically FALSE as stated** — Persona 12 exhibits a concrete counterexample (`Y = 0` and `Y = W₁_T − W₁_t` both satisfy the strengthened `IsBSDEJSolution` predicate for `(f=0, g=0)` data, so the uniqueness clause cannot be satisfied). On top of that, the citation inventory has **two outright wrong attributions** including one fabricated paper ("Gnoatto 2025 primer on BSDE with jumps in *Quantitative Finance*" does not exist per DBLP), four wrong Le Gall theorem numbers, and a 2009 Bouchard–Elie–Touzi paper that should be a 2008 Bouchard–Elie paper (no Touzi co-author). Persona 02 also found that **518 lines of source code + every build config file (`lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `tools/lint.sh`) are UNTRACKED in git** — `git log --all --diff-filter=A` returns empty for them — so a fresh clone does not build, and the "8401 jobs PASS at baseline" claim does not survive a clone because `tools/lint.sh` silently passes when `_audit.lean` (also gitignored) is missing. `cited_axioms.md`'s "No trivial-witness theorems remain" claim and `tools/full_audit.lean`'s "audit-clean" claim are both demonstrably false.

The library is **NOT Mathlib-PR-acceptable** and the dissertation-side forwarders that transitively surface these axioms inherit each defect.

## Severity-ranked deduplicated findings

### CRITICAL — the library is unsound or makes mathematically false claims

**C1. `BSDEJ.Existence.continuousBSDEJ_exists_unique` axiom is mathematically false as stated.** ★ Most important finding.
- *Detected by*: P05, P12 (constructive proofs); P04 (alternative construction); independently corroborated by P01, P03, P07, P10.
- *Construction*: For `(f=0, g=0, X` arbitrary`)`, the predicate `IsBSDEJSolution P ν W N bsdej X Y Z U T` is satisfiable by both `Y ≡ 0` (trivial constant) and `Y = W₁_T − W₁_t` (Brownian-integral). Both satisfy the strengthened predicate's joint measurability + L²-bounds + outer existential `∃ M_W M_N` with martingale + L²-isometry + M_N = `Compensated.stochasticIntegral N U`. The axiom's `∀ Y', IsBSDEJSolution Y' → Y =ᵃᵉ Y'` cannot be satisfied for both these Y's simultaneously, so `∃ Y, (sol Y ∧ ∀ Y', sol Y' → Y =ᵃᵉ Y')` is unsatisfiable.
- *Why the 2026-05-11 strengthening failed*: it closed the inner-real-existential route (`∃ BM_term jump_term : ℝ`) but did **not** add an adaptedness/predictability constraint on `(Y, Z, U)`, so the literature uniqueness — which relies on adaptedness — does not transfer.
- *Cross-repo impact*: dissertation theorem `Dissertation.Continuous.continuousBSDEJ_exists_unique` (`Dissertation/Continuous.lean`) forwards directly into this axiom; the unsoundness leaks across the repo boundary.
- *Recommendation*: either (a) add adaptedness conjuncts to `IsBSDEJSolution` and pin `M_W` to the actual `∫ Z·dW` (requires `h_progMeas` threaded through), OR (b) honestly acknowledge the predicate is weaker than the literature predicate and weaken the axiom's conclusion to "exists a solution in the predicate's weak sense" with no uniqueness clause.

**C2. `Ito.JumpFormula.itoLevyFormula` axiom STATEMENT is the trivial-witness pattern.**
- *Detected by*: P01, P04, P05, P07, P10, P12.
- *Statement*: `∃ (drift_term diff_mart jump_mart comp_drift : Ω → ℝ), ∀ᵐ ω, u(T, X_T ω) − u(0, X_0 ω) = drift_term ω + diff_mart ω + jump_mart ω + comp_drift ω`. The four reals are not pinned to any integral form, so `(change, 0, 0, 0)` satisfies it.
- *Why the 2026-05-11 demotion failed*: removing the proof body and re-declaring as `axiom` does not strengthen the statement. The Applebaum 4.4.7 citation in the docstring carries no formal weight when the statement itself is provable by triviality.
- *Recommendation*: rewrite the axiom statement to pin each term to its literature integral form (drift = `∫ (∂_t u + 𝓛u) ds`, diff_mart = Brownian Itô integral of `∇uᵀσ`, jump_mart = compensated-Poisson integral of `u(·+γ) − u`, comp_drift = `∫∫ (u(·+γ) − u − γᵀ∇u) ν ds`), OR demote to a documented "stub axiom" with explicit acknowledgement that it doesn't carry literature content.

**C3. `Ito.Setting.JumpDiffusion.exists_unique` is a trivial-witness theorem the recursive audit missed.**
- *Detected by*: P01, P02, P03, P04, P05, P07, P10, P12 (8 personas independently).
- *Mechanism*: the structure `JumpDiffusion W N coeffs x₀` has a field `is_solution : True`. Theorem proves only `Nonempty (JumpDiffusion …)` (no uniqueness despite the name) with `X t ω := x₀` (constant path).
- *File*: `LevyStochCalc/Ito/Setting.lean:85-112`. UNTRACKED in git (see C8).
- *Recommendation*: replace `is_solution : True` with a real SDE-solution predicate (Itô-with-jumps integral equation linking `X` to `μ, σ, γ, W, N`); remove "unique" from the theorem name; or demote to documented stub axiom.

**C4. `BSDEJ.MartingaleRepresentation.jacodYor_representation` is a trivial-witness theorem the recursive audit missed.**
- *Detected by*: P01, P02, P03, P04, P05, P07, P10, P12 (8 personas independently).
- *Mechanism*: proof body is `refine ⟨0, 0, 0, fun ω => ξ ω − ∫ ω', ξ ω' ∂P, …⟩; … ; ring` — three zero processes, the entire deviation stuffed into the fourth slot, ring identity closes it.
- *File*: `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:55-85`. UNTRACKED in git (see C8).
- *NOT* in `tools/cited_axioms.md` ledger despite carrying a paper citation in its docstring (P07).
- *Recommendation*: same options as C3 — pin the four processes to their literature integral forms (martingale representation against Brownian + compensated-Poisson), or demote.

**C5. Three public lemmas carry `sorryAx`, refuting `cited_axioms.md`'s "No `sorryAx` in public API" claim.**
- *Detected by*: P12.
- *Affected*: `Poisson.Compensated.simplePredictable_dense_L2`, `Brownian.Continuity.kolmogorov_modification_ae_eq`, `Poisson.poissonRandomMeasure_finite_exists`.
- *Why lint.sh misses them*: `lint.sh` runs `_audit.lean` (which lists specific theorems), not a project-wide `#print axioms` sweep. The three lemmas are reachable but not in the audit's enumerated list.
- *Recommendation*: add a project-wide axiom scan; OR list every public declaration in `_audit.lean`; OR fail lint.sh when any reachable theorem from `LevyStochCalc.lean` has `sorryAx` in its axiom set.

**C6. Tier 1 #9 citation "Gnoatto 2025, *Quantitative Finance*, primer on BSDEJ" is fabricated.**
- *Detected by*: P11.
- *Evidence*: DBLP verified — Gnoatto's 2025 publications are all "Deep solver…" papers in Math. Oper. Res. / SIAM J. Financial Math. / arXiv; none in *Quantitative Finance*; no "primer" title exists. Plausible real reference: Andersson–Gnoatto–Patacca–Picarelli 2025 arXiv:2211.04349 Thm 2.4 (per the user's 2026-05-20 in-progress fix to `Dissertation/Continuous/LevyStochCalcBridge.lean`).
- *Recommendation*: replace with the real reference + flag the misattribution in the project history.

**C7. Tier 1 #10 citation "Bouchard, Elie & Touzi 2009 SPA 119(11)" is wrong on every field.**
- *Detected by*: P06, P07, P10, P11 (4 personas).
- *Real paper*: **Bouchard & Elie 2008, SPA 118(1), pp 53–75**. Touzi was never an author; no SPA 119(11) 2009 paper exists. P11 verified via Bouchard's own slides + Kharroubi–Lim 2018 citing "Bouchard and Elie [4]". Likely conflation of Bouchard–Touzi 2004 SPA 111 (Brownian Monte Carlo) with Bouchard–Elie 2008 SPA 118 (jumps).
- *Recommendation*: fix `cited_axioms.md` #10, `BSDEJ/PathRegularity.lean:23-24,92-94`, and propagate to dissertation-side citations.

**C8. 518 lines of source code + every build config file are UNTRACKED in git.**
- *Detected by*: P02.
- *Files*: `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `tools/lint.sh`, and **5 source files** that the root `LevyStochCalc.lean` import chain depends on:
  - `LevyStochCalc/Notation.lean`
  - `LevyStochCalc/Brownian/Multidim.lean`
  - `LevyStochCalc/Ito/Setting.lean` (houses the trivial-witness `JumpDiffusion.exists_unique`)
  - `LevyStochCalc/Poisson/L2Isometry.lean` (the 1-line forwarder for the dissertation)
  - `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean` (houses the trivial-witness `jacodYor_representation`)
- *Verification*: `git log --all --diff-filter=A` returns empty for each.
- *Why this matters*: a fresh `git clone` produces a non-building repo; the dissertation's lake dependency on `../LevyStochCalc` would also fail to resolve from a clone.
- *Bonus catch*: the two trivial-witness theorems (C3, C4) sit in untracked files — they evaded `git log`–based audit workflows for exactly this reason. P02 calls this out explicitly.
- *Recommendation*: `git add` the 9 files and commit.

**C9. `tools/lint.sh` is silently broken on fresh checkout.**
- *Detected by*: P02.
- *Mechanism*: line 21 runs `lake env lean _audit.lean > audit_output.txt 2>&1 || true`. But `_audit.lean` is gitignored. On a fresh clone, the audit command fails, `|| true` swallows the error, the regex matches nothing, the script reports `PASS`.
- *Recommendation*: track `_audit.lean`, or change `|| true` to fail the script when audit_output.txt is empty/missing.

### HIGH — definition or axiom is strictly weaker than the literature

**H1. `IsBSDEJSolution` predicate has no adaptedness/predictability constraint on `(Y, Z, U)`.**
- *Detected by*: P04, P05, P10, P12.
- *Mechanism*: the 2026-05-11 strengthening added outer `∃ M_W M_N` with martingale + L²-isometry + direct pin of `M_N` to `Compensated.stochasticIntegral`, but `(Y, Z, U)` itself only needs joint measurability. The literature Tang–Li / Pardoux–Răşcanu solution space `S² × H² × H²_N` requires **predictable** `Z, U` and adapted càdlàg `Y`.
- *Combined with `M_W` slack*: P04's concrete construction (scale an independent BM `B'` by `√(𝔼[∫‖Z‖²]/T')`) shows uniqueness fails.
- *Recommendation*: add `Adapted Y F` + `Predictable Z F` + `Predictable U F` conjuncts; pin `M_W` to the actual sum `∑ᵢ ∫ Zⁱ dWⁱ` using a multidim Brownian stochastic-integral primitive (currently missing — see H6).

**H2. `IsBSDEJSolution`'s `M_W` is only L²-isometric to `Z`, not pinned to `∫Z·dW`.**
- *Detected by*: P04 (concrete construction), P05, P07, P12.
- *Mechanism*: the strengthening allows any martingale with the right L² norm; the literature requires `M_W = ∫ Z · dW` specifically.
- *Recommendation*: define a multidim Brownian stochastic-integral primitive (sum of 1D primitives over `Fin d`); pin `M_W` to it; thread `h_progMeas` through.

**H3. `bsdej_path_regularity` axiom's existential `∃ Z_avg U_avg` admits the trivial choice `Z_avg := Z`, `U_avg := U` that zeros the projection-error terms.**
- *Detected by*: P07, P12.
- *Mechanism*: the BET 2008 path-regularity content lives in the projection error against **conditional time-averages** specifically; the loose existential lets any choice serve, including ones that trivialize the bound.
- *Recommendation*: pin `Z_avg, U_avg` to the conditional-expectation projections defined in `LevyStochCalc/BSDEJ/PathRegularity.lean:62-83` (`conditionalTimeAverage_Z`, `conditionalTimeAverage_U`) — they are defined in the file but not used.

**H4. `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` axioms omit Lipschitz + L²-terminal + measurability hypotheses required by Tang–Li 1994 / Bouchard–Elie 2008.**
- *Detected by*: P01, P03, P04, P07, P10.
- *Mechanism*: the LevyStochCalc `Lipschitz` predicate is defined locally in `BSDEJ/Existence.lean:67-73` but never appears in any axiom signature. Both BSDEJ axioms quantify over arbitrary `bsdej : BSDEJData` and arbitrary `X : ℝ → Ω → (Fin n → ℝ)`.
- *Mathematical consequence*: for non-Lipschitz drivers (e.g., `f(s,x,y,z,u) = y²`), the BSDEJ can have multiple solutions or none — the axiom over-claims.
- *Recommendation*: add `(hL : Lipschitz bsdej ν L)`, `(hξ : Integrable (g ∘ X T) P)`, `(hX : Measurable (Function.uncurry X))` to both axiom signatures.

**H5. `itoIsometry_compensated_unified_existence` axiom binds `φ` with no `h_meas` / `h_sq_int_global` hypothesis; its Brownian counterpart does require these.**
- *Detected by*: P05, P07, P10, P12.
- *Mechanism*: `Compensated.lean:2748` declares `axiom itoIsometry_compensated_unified_existence … (φ : Ω → ℝ → E → ℝ) : ∃ F Filt, …` with no hypotheses. The L²-isometry conjunct then quantifies internally `∀ T (h_meas …) (h_sq_int …)`. Asymmetric vs. the Brownian axiom in `Brownian/SimplePredictableRefine.lean:2094` which takes `h_meas`, `h_progMeas`, `h_sq_int_global` as outer hypotheses.
- *Exploit (P12)*: Mathlib's `integral_undef`-defaults-to-0 convention can be used to make `F ≡ 0` satisfy the quadVar conjunct for non-L² `φ`, since `(F t ω)² − ∫∫ φ² ν ds` is `0 − 0 = 0` (constant martingale) when `∫ φ² = ∞` and the Bochner integral collapses to 0.
- *Recommendation*: add `h_meas`, `h_sq_int_global` as outer hypotheses to match the Brownian axiom signature.

**H6. `itoLevyIsometry` (Tier 1 derivative #5/#6) requires only `Measurable` instead of `Predictable`.**
- *Detected by*: P04, P07.
- *Mechanism*: the literature compensated-Poisson L²-Itô isometry requires `φ` to be predictable; the Lean signature uses joint measurability w.r.t. the product σ-algebra, which is strictly weaker.
- *Recommendation*: replace `Measurable` with `Predictable` (Mathlib's `MeasureTheory.ProgMeasurable` or the predictable σ-algebra construction).

**H7. Tier 1 #4 (Blumenthal 0-1 / right-continuous filtration) citation "Le Gall Proposition 2.10" is wrong.**
- *Detected by*: P11.
- *Real reference*: Le Gall 2016 p. 25 "Lemma 2.10" is a deterministic real-analysis Hölder lemma. Blumenthal is Le Gall **Theorem 2.13** (p. 30). Verified directly from the PDF.

**H8. Tier 1 #5 (Brownian unified existence) citation "Le Gall Theorem 5.13" is wrong.**
- *Detected by*: P11.
- *Real reference*: Le Gall 2016 p. 121 "Theorem 5.13" is Dambis–Dubins–Schwarz. L² Itô isometry is Le Gall Thm 5.4 + eq. (5.8).

**H9. Pardoux–Răşcanu 2014 (a continuous-BSDE textbook) is cited as a reference for the BSDEJ (jump) axioms #9 and #10.**
- *Detected by*: P11.
- *Mechanism*: the docstring's own "(continuous case)" parenthetical admits the scope mismatch.

**H10. `lake-manifest.json:94` mis-identifies project as `"name": "Dissertation"` and has `"fixedToolchain": false`.**
- *Detected by*: P02.
- *Mechanism*: likely copy-pasted from sister repo; `"fixedToolchain": false` means a future `lake update` would jump Mathlib SHAs unpredictably.

### MEDIUM — structural / hygiene defects

**M1. 7+ public `True := trivial` lemmas with substantive docstrings.**
- *Detected by*: P01, P05, P12.
- *Examples*: `brownian_dyadicTime_exists`, `picardMap_contraction` (in `BSDEJ/Existence.lean:80-91`), 3 "construction step" lemmas in `Brownian/Construction.lean:142-156`, `Poisson/RandomMeasure.lean:146-148`, marker theorems in `Continuous/LevyStochCalcBridge.lean`. Each has an elaborate docstring; the body is `True := trivial`.

**M2. 4 dead-code `sorry` declarations in private lemmas with zero callers.**
- *Detected by*: P01, P02, P10.
- *Locations*: `Continuity.lean:184`, `Ito.lean:3984`, `Compensated.lean:1893`, `RandomMeasure.lean:139`.
- *Why lint.sh misses them*: `lint.sh` only checks `_audit.lean`-listed (public) theorems; private dead lemmas are not enumerated.

**M3. 677-line orphan module `LevyStochCalc/Poisson/Martingale.lean` is never imported anywhere.**
- *Detected by*: P01, P02.

**M4. Tier 1 #7 and #8 axioms (`cauchySeq_simpleIntegralLp_compensated`, `adaptedSimple_dense_L2_compensated`) are dead in the load-bearing chain post-2026-05-10 unified-F refactor.**
- *Detected by*: P01.
- *Mechanism*: the unified-existence axioms (Tier 1 #5 + #6) replaced the per-step density / Cauchy chain. The two density axioms are still declared but no longer transitively reachable from the headline theorems.
- *Recommendation*: either remove them or restore them to a load-bearing role.

**M5. `adaptedSimple_dense_L2_compensated` docstring claims "progressively measurable" but signature only requires joint measurability.**
- *Detected by*: P12.
- *Strictly stronger claim than what Applebaum 4.2.2 proves.*

**M6. `tools/cited_axioms.md`'s "No trivial-witness theorems remain" status claim is documentation-defect FALSE.**
- *Detected by*: P05, P12.
- *The doc was updated after the 2026-05-11 recursive audit; it should be retracted now.*

**M7. STATUS.md / STATUS_strong_exists.md are 12+ days stale.**
- *Detected by*: P02.
- *Examples*: STATUS.md claims "19 entries in sorry_baseline.txt"; the file is 0 bytes.

**M8. Path-regularity constant `C` is purely existential.**
- *Detected by*: P06.
- *Mechanism*: `BSDEJ/PathRegularity.lean:111` states `∃ (C : ℝ), 0 < C ∧ …` with no `L : ℝ` (Lipschitz) or `‖ξ‖_{L²}` parameter despite the docstring acknowledging `C` should depend on `(T, L, ‖ξ‖_{L²})`. Downstream numerical work would have to re-derive constants.

**M9. No multidim Brownian stochastic-integral primitive.**
- *Detected by*: P03, P04, P07.
- *Mechanism*: only a 1D Brownian primitive exists. Multifactor finance / multidim BSDEJ would need to roll its own sum over `Fin d`.

**M10. `BSDEJData` is scalar-Y-only.**
- *Detected by*: P03.
- *Mechanism*: `Y : ℝ → Ω → ℝ`. No support for vector-Y BSDEJs (reflected BSDEJs, quadratic-growth, FBSDEJ couples).

**M11. `IsBSDEJSolution`'s inner `∃ Filt` allows trivial constant filtrations.**
- *Detected by*: P12.
- *Mechanism*: should be pinned to the natural filtration of `(W, N)` (or its augmentation).

**M12. The compensated Poisson `stochasticIntegral` definition + `integral_undef` convention is exploitable.**
- *Detected by*: P12.
- *Mechanism*: see H5 — `F ≡ 0` can satisfy conjunct 2 (quadVar) for non-L² φ via Mathlib's default-to-zero for non-integrable Bochner integrals.

**M13. `Le Gall Theorem 2.1` cited for BM existence does not exist; should be Definition 2.1 / Definition 2.12 / Corollary 2.11.**
- *Detected by*: P11.

### LOW — style / documentation drift

- **L1.** 198 `lake build` warnings: 59 `show`-tactic misuses, 29 deprecated `push_neg`, 8 deprecated symbol families, 19 undocumented `maxHeartbeats`, 21 long lines, 18 module-header issues. (P01)
- **L2.** Naming drift — multiple variants like `itoIsometry_brownian_general`, `_existence`, `itoIsometry`, `itoIsometry_compensated_existence`, `itoIsometry_compensatedPoisson_general`. (P01)
- **L3.** `Notation.lean` is 13 lines of `import Mathlib` + empty namespace. (P01)
- **L4.** `Basic.lean` also uses bare `import Mathlib` — slow build. (P01)
- **L5.** Stale docstrings in `L2Isometry.lean` and `Brownian/Ito.lean` still claim "transitively sorry'd". (P01, P10)
- **L6.** Empty `docs/` directory tracked at root; no README; no LICENSE; no CONTRIBUTING. (P02, P10)
- **L7.** No CI; `tools/lint.sh:12` recommends `cp tools/lint.sh .git/hooks/pre-commit` — not done; `.github/workflows/` does not exist. (P02, P10)
- **L8.** `.gitignore` is 4 lines; misses `.claude/`, `.codex/`, `.mcp.json`, `__pycache__/`, IDE folders. (P02)
- **L9.** Two `open Classical` style-linter violations. (P01)
- **L10.** Missing joint measurability on `BrownianMotion` structure; missing Applebaum 2.3.1(c) on `PoissonRandomMeasure`. (P04)
- **L11.** Dead `stochasticIntegral_isometry_only_compensated` lemma + stale module docstring caveat in `Compensated.lean`. (P10)
- **L12.** `cauchySeq_simpleIntegralLp_compensated` cites "Equation 4.3.1" rather than a theorem. (P10)

## Per-axiom verdict consensus (the 11 Tier 1 cited axioms)

Verdicts aggregated across personas that audited each axiom; "majority" verdict shown plus the cleanest objection if any.

| # | Axiom | Verdict | Note |
|---|---|---|---|
| 1 | `Brownian.BrownianMotion.exists` | **EARNED** | Missing joint measurability flag (P04 LOW) |
| 2 | `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | **EARNED** | Missing Applebaum 2.3.1(c) clause (P04 LOW) |
| 3 | `Brownian.Continuity.kolmogorovChentsov_modification` | **EARNED** | Citation consistent (P11) |
| 4 | `Brownian.Martingale.brownian_martingale_rightCont` | **WEAK** | Le Gall Prop 2.10 citation wrong → Thm 2.13 (P11 HIGH) |
| 5 | `Brownian.Ito.itoIsometry_brownian_unified_existence` | **WEAK** | Le Gall Thm 5.13 citation wrong → Thm 5.4 (P11 HIGH); existential filtration (P01 HIGH) |
| 6 | `Poisson.Compensated.itoIsometry_compensated_unified_existence` | **WEAK** | Asymmetric vs. Brownian sister (no `h_meas`/`h_sq_int`); exploitable via `integral_undef` (P05, P07, P10, P12) |
| 7 | `Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` | **DEAD** | No longer load-bearing post-2026-05-10 (P01 MEDIUM) |
| 8 | `Poisson.Compensated.adaptedSimple_dense_L2_compensated` | **DEAD/WEAK** | No longer load-bearing; docstring claims progressively-measurable, signature only joint-measurable (P01, P12) |
| 9 | `BSDEJ.Existence.continuousBSDEJ_exists_unique` | **TRIVIAL (unsound)** | Mathematically false (P05, P12 constructions); missing Lipschitz / L² / measurability (P01, P03, P04, P07, P10); citation fabricated (P11) |
| 10 | `BSDEJ.PathRegularity.bsdej_path_regularity` | **TRIVIAL** | Z_avg/U_avg loose existential trivializes the bound (P07, P12); missing Lipschitz; citation wrong (P06, P07, P10, P11) |
| 11 | `Ito.JumpFormula.itoLevyFormula` | **TRIVIAL** | Statement is the trivial-witness pattern; demotion was cosmetic (P01, P04, P05, P07, P10, P12) |

Of the 11 Tier 1 axioms: **3 EARNED, 2 WEAK (citation), 1 WEAK (asymmetric hypotheses), 2 DEAD, 3 TRIVIAL/UNSOUND.**

## Per-axiom verdict consensus (the honest derivative theorems)

| Theorem | Verdict |
|---|---|
| `MultidimBrownianMotion.exists` | **UNVERIFIABLE** (file untracked, P02) |
| `Brownian.Continuity.brownian_continuous_modification` | EARNED |
| `Brownian.Martingale.brownian_martingale` | EARNED |
| `Brownian.Martingale.brownian_quadVar` | EARNED |
| `Brownian.Martingale.brownian_filtration_rightContinuous` | EARNED |
| `Brownian.Ito.itoIsometry` | WEAK — only Measurable, not Predictable (P04, P07) |
| `Brownian.Ito.martingale_stochasticIntegral` | EARNED (conjunct extraction) |
| `Brownian.Ito.quadVar_stochasticIntegral` | EARNED (conjunct extraction) |
| `Poisson.Compensated.itoLevyIsometry` | WEAK — inherits H5 |
| `Poisson.Compensated.martingale_stochasticIntegral` | EARNED (conjunct extraction) |
| `Poisson.Compensated.quadVar_stochasticIntegral` | WEAK — `integral_undef` exploit (P12) |
| `Poisson.Compensated.cadlag_modification_exists` | EARNED (conjunct extraction) |
| `Poisson.L2Isometry.itoLevyIsometry` | **UNVERIFIABLE** (file untracked, P02) — but if file matches what's on disk, WEAK same as Compensated.itoLevyIsometry |
| `Ito.Setting.JumpDiffusion.exists_unique` | **TRIVIAL** (8 personas) |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` | **TRIVIAL** (8 personas); NOT in cited_axioms.md ledger (P07) |

## Per-persona finding counts

| Persona | Verdict | CRIT | HIGH | MED | LOW | Notes |
|---|---|---|---|---|---|---|
| 01 Lean formalisation | substantive | 3 | 3 | several | many | First catch of `jacodYor_representation` trivial-witness |
| 02 Software engineering | substantive | 2 | 2 | 5 | 5 | Discovered 518 lines of source UNTRACKED in git |
| 03 Financial mathematician | scope-limited | 1 | 2 | 5 | 0 | Confirms trivial-witnesses from finance lens |
| 04 Pure mathematician | substantive | 1 | 6 | 5 | 0 | Concrete BM-scaling construction breaking uniqueness |
| 05 Proof theorist | substantive | 3 | 1 | 2 | 0 | Adaptedness-gap analysis; `cited_axioms.md` claim is FALSE |
| 06 Numerical analyst | scope-limited | 0 | 0 | 2 | 3 | First catch of BET citation defect |
| 07 Stochastic analyst | substantive | 5 | 4 | several | 0 | Z_avg=Z exploit + Measurable-not-Predictable insight |
| 08 MFG specialist | scope-limited | 0 | 0 | 0 | 3 | Honest short report (out-of-scope) |
| 09 Deep learning | scope-limited | 0 | 0 | 0 | 1 | Honest short report (out-of-scope) |
| 10 Library quality | substantive | 2 | 5 | 4 | 2 | Mathlib-PR-acceptability analysis |
| 11 Citation verifier | substantive | 2 | 4 | 2 | 1 | Gnoatto 2025 fabrication; 4 Le Gall theorem-number errors |
| 12 Adversarial hole hunter | substantive | 5 | 4 | 3 | 1 | Concrete proof of `continuousBSDEJ_exists_unique` unsoundness; 3 public sorryAx; integral_undef exploit |

## Cross-checks performed

- Persona 05 ran `mcp__lean-lsp__lean_verify` on the 4 dissertation-forwarder targets + 3 key theorems. **No drift between actual axiom sets and `tools/full_audit_output.txt`.** Build still passes (8401 jobs).
- Personas 06, 07, 11 all independently caught the BET citation defect with primary-source verification.
- Personas 01, 02, 03, 04, 05, 07, 10, 12 all independently caught the two trivial-witness theorems (`jacodYor_representation`, `JumpDiffusion.exists_unique`) — strongest possible triangulation.
- Personas 04, 05, 12 all independently constructed counterexamples to `continuousBSDEJ_exists_unique`'s uniqueness clause (3 different constructions, same conclusion).

## Recommended action plan (5 phases, severity-ordered)

**Phase 1 — Soundness (P0, blocks everything else):**
1. Add adaptedness / predictability conjuncts to `IsBSDEJSolution` (fixes C1, H1).
2. Pin `M_W` to the actual `∫ Z · dW` (requires defining a multidim Brownian stochastic integral primitive). Alternatively, weaken the axiom's uniqueness clause to match the predicate's strength (fixes C1, H2).
3. Rewrite `itoLevyFormula` axiom statement to pin each of 4 terms to literature integral forms (fixes C2).
4. Replace `JumpDiffusion`'s `is_solution : True` field with the SDE integral equation (fixes C3).
5. Pin `jacodYor_representation`'s 4 processes to literature integral forms, OR demote to documented axiom (fixes C4).
6. Pin `bsdej_path_regularity`'s `Z_avg, U_avg` to the `conditionalTimeAverage_*` definitions already in the file (fixes H3).

**Phase 2 — Hypothesis hygiene (P1):**
7. Add Lipschitz + L²-terminal + measurability hypotheses to `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` axioms (fixes H4).
8. Add `h_meas` + `h_sq_int_global` outer hypotheses to `itoIsometry_compensated_unified_existence` (fixes H5).
9. Use `Predictable` instead of `Measurable` in `itoLevyIsometry` and its derivatives (fixes H6).

**Phase 3 — Citations (P1):**
10. Replace Tier 1 #9 citation ("Gnoatto 2025 primer") with the real reference (fixes C6).
11. Replace Tier 1 #10 citation ("BET 2009 SPA 119(11)") with Bouchard & Elie 2008 SPA 118(1) (fixes C7).
12. Fix Le Gall theorem numbers for #1, #4, #5 (fixes H7, H8, M13).
13. Either remove Pardoux–Răşcanu 2014 from BSDEJ citations or honestly mark it as "continuous-case reference" (fixes H9).

**Phase 4 — Git hygiene (P1, blocks reproducibility):**
14. `git add` the 9 untracked files (3 build configs + 5 source + lint.sh) and commit (fixes C8).
15. Fix `lake-manifest.json` project name and pin toolchain (fixes H10).
16. Make `tools/lint.sh` fail when `audit_output.txt` is empty or `_audit.lean` is missing (fixes C9).
17. Add a project-wide reachable-axiom scan to lint (fixes C5).

**Phase 5 — Documentation / structural cleanup (P2):**
18. Retract `cited_axioms.md`'s "No trivial-witness theorems remain" claim and update with the red-team findings (fixes M6).
19. Remove dead `True := trivial` lemmas with substantive docstrings (M1).
20. Remove 4 dead-code `sorry` private lemmas (M2).
21. Decide whether to keep, remove, or reactivate the orphan `Poisson/Martingale.lean` (M3).
22. Decide whether Tier 1 #7, #8 should be removed (dead post-refactor) or restored to load-bearing (M4).
23. Resolve 198 lake build warnings (L1).
24. Add README, LICENSE, CONTRIBUTING; populate `docs/`; add basic CI (L6, L7).

## What this audit DOES NOT cover

- **Mathematical correctness of cited papers** (P11 verified bibliographic facts but did NOT re-derive theorems).
- **Dissertation-side audit** — the dissertation repo has its own red-team findings dir; cross-references in this summary only.
- **Run-time / performance** of the library (no timing data collected; only `lake build` job count).
- **Future Mathlib stochastic-integration arc** (`arXiv:2511.20118` / Degenne et al) — referenced in axiom replacement plans but not formally verified to land.

## Files

Individual persona reports (all in `D:\LevyStochCalc\redteam_findings\`):
- `01_lean_formalisation.md` (45 KB, 16 findings)
- `02_software_engineering.md` (40 KB, 14 findings)
- `03_financial_mathematician.md` (39 KB, 10 findings)
- `04_pure_mathematician.md` (50 KB, 12 findings)
- `05_proof_theorist.md` (35 KB, 6 findings, all sharply focused)
- `06_numerical_analyst.md` (23 KB, 5 findings)
- `07_stochastic_analyst.md` (49 KB, 15 findings)
- `08_mfg_specialist.md` (16 KB, 3 LOW findings)
- `09_deep_learning_specialist.md` (10 KB, 2 LOW findings)
- `10_dissertation_examiner.md` (45 KB, 13 findings)
- `11_citation_verifier.md` (44 KB, 15 findings)
- `12_adversarial_hole_hunter.md` (53 KB, 13 findings)
- `shared_context_override.md` (15 KB, context calibration)

Setup pack (read-only at audit time, do not modify): `D:\LeanRedTeam\`.
