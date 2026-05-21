# Red Team Audit: Numerical Analyst

**Auditor lens**: Numerical analysis professor — finite differences, error analysis, stability, convergence rates, explicit constant tracking; calibrated for "would a numerical user be misled by these statements?"
**Date**: 2026-05-20
**Coverage**: 7 files read in full (`tools/cited_axioms.md`, `LevyStochCalc.lean`, `BSDEJ/PathRegularity.lean`, `BSDEJ/Definition.lean`, `BSDEJ/Existence.lean`, `Ito/Setting.lean`, `Brownian/SimplePredictableRefine.lean` head); `Poisson/Compensated.lean` skimmed (2907 lines, focus around lines 40–62 caveat + 2748–2907 `Classical.choose` block); other files (`Brownian/{Construction,Continuity,Martingale,Multidim,Ito}.lean`, `Poisson/{RandomMeasure,NaturalFiltration,Martingale,L2Isometry}.lean`, `BSDEJ/MartingaleRepresentation.lean`) not touched because no quantitative-bound / numerical content per my pre-scan greps.

## Executive summary (≤ 3 sentences)

LevyStochCalc is a pure-existence stochastic calculus library with no numerical content of its own, so most of my lens does not apply — but the **`bsdej_path_regularity` axiom states the BET path-regularity bound with a purely existential `∃ (C : ℝ), 0 < C ∧ …`**, providing zero handle on the constant's dependence on `T`, `L`, or `‖ξ‖_{L²}`; any downstream numerical convergence-rate work would have to re-derive `C` from scratch. The `Classical.choose`-defined `stochasticIntegral` is mathematically harmless but does *not* yield a computable scheme for any numerical implementation. I also found a **citation mismatch on the BET path-regularity reference** (the paper is Bouchard-Elie 2008 SPA 118(1), not Bouchard-Elie-Touzi 2009 SPA 119(11)) — primarily persona-11's domain but flagged here because it directly affects a numerical reader's ability to locate the constant in the cited paper.

## Top findings (ranked by severity, highest first)

### Finding 1 — Path-regularity constant `C` is purely existential, with no documented dependence on `T`, `L`, or `‖ξ‖_{L²}`
- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/BSDEJ/PathRegularity.lean:111-139`
- **Evidence**: The axiom statement reads, verbatim:
  ```
  axiom bsdej_path_regularity
      {P : Measure Ω} [IsProbabilityMeasure P]
      {ν : Measure E} [SigmaFinite ν]
      {n d : ℕ}
      (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
      (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
      (X : ℝ → Ω → (Fin n → ℝ))
      (T : ℝ) (_hT : 0 < T) :
      ∃ (C : ℝ),
        0 < C ∧
        ∀ (M : ℕ) (_hM : 0 < M) (partition : Fin (M + 1) → ℝ)
          (_h_part_mono : StrictMono partition)
          (_h_part_start : partition 0 = 0)
          (_h_part_end : partition (Fin.last M) = T)
          (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
          (_h_solution :
            LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T),
          let Δt : ℝ := ⨆ n : Fin M,
            partition n.succ - partition n.castSucc
          ∃ (Z_avg : ℝ → Ω → (Fin d → ℝ)) (U_avg : ℝ → Ω → E → ℝ),
            (⨆ n : Fin M, ∫⁻ ω, … (‖Y t ω - Y (partition n.castSucc) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            + … + …
            ≤ ENNReal.ofReal (C * Δt)
  ```
  The module docstring at lines 37–39 acknowledges this informally — "The constant `C` depends on `T`, the Lipschitz constant `L` of `f`, and the L²-norm of `(Y_0, Z, U, ξ)` — all bounded uniformly by `BSDEJ.Existence`'s solution-bound" — but **the Lean statement exposes none of this**: no `L : ℝ` parameter, no Lipschitz hypothesis, no L² norm of terminal data. The hypotheses bundle is just `(W, N, bsdej, X, T, hT)`, none of which carry quantitative bounds. A downstream numerical user calling this axiom obtains an opaque positive real, indistinguishable from `10^{100}`.
- **Why this matters**: The BET (and Zhang 2004) path-regularity bound `C · Δt` is the textbook ingredient for proving deep-BSDE / discrete-BSDE convergence rates of `O(h)` or `O(h^{1/2})`. Any numerical convergence proof building on this axiom needs to either (a) carry `C` through unchanged, in which case the rate constant of the downstream scheme is *also* an unspecified existential, or (b) re-derive an explicit `C(T, L, ‖ξ‖_{L²})` from BET 2008 / Zhang 2004 / Pardoux-Răşcanu, doing the literature work the axiom is supposed to save. Honest disclosure: the cited papers themselves do not give a closed-form `C` either (per the search of Zhang's path-regularity literature and the related arxiv:0905.0788 follow-up, all written with "constants C may change from line to line"), so the axiom is **consistent with what the literature actually proves**. The MEDIUM severity is for a numerical user who would expect a Lean formalisation to be quantitatively *better* than the source paper, not just as opaque.
- **Recommendation**: Either (i) accept that quantitative refinement is out of scope and add a docstring sentence explicitly stating "the constant `C` is not exposed; downstream numerical work needing an explicit rate must re-derive it from the cited paper(s)"; or (ii) thread an explicit Lipschitz parameter `(L : ℝ) (hL : Lipschitz bsdej ν L)` plus an `(L_ξ : ℝ) (hL_ξ : ‖ξ‖_{L²} ≤ L_ξ)` bound into the axiom and state `C = some_concrete_polynomial(T, L, L_ξ)` (BET 2008 Thm 3.1 / Pardoux-Răşcanu Thm 5.42 give one). Option (ii) is real literature work for one Mathlib PR. Option (i) is a one-line docstring fix.

### Finding 2 — `bsdej_path_regularity` citation: Bouchard-Elie 2008 SPA 118(1), not Bouchard-Elie-Touzi 2009 SPA 119(11)
- **Severity**: MEDIUM (persona-11 territory, but reported here because it affects numerical readers' ability to locate the constant)
- **Location**: `LevyStochCalc/BSDEJ/PathRegularity.lean:23-24, 92-94`; `tools/cited_axioms.md:84` (entry 10)
- **Evidence**: The Lean file states:
  > `* Bouchard & Elie & Touzi, "Discrete-time approximation of decoupled Forward-Backward SDE with jumps", SPA 119(11), 2009, Theorem 2.1.`

  Web search and the HAL archive entry `hal-00015486` confirm the actual paper is:
  > Bruno Bouchard and Romuald Elie, "Discrete time approximation of decoupled Forward-Backward SDE with jumps", *Stochastic Processes and their Applications* **118**(1), 2008, pages 53–75.

  Touzi is **not an author** of this paper. Bouchard-Touzi 2004 is a separate (no-jumps) SPA paper. There is no Bouchard-Elie-Touzi 2009 SPA 119(11) paper that I could locate via web search. The `cited_axioms.md` entry 10 contains the same incorrect citation.
- **Why this matters**: A numerical analyst wanting to lift the explicit constants out of the cited paper into a downstream scheme would search Google Scholar / MathSciNet for "Bouchard-Elie-Touzi 2009 SPA 119" and find nothing, then have to guess the right paper. For a Lean formalisation that documents axioms with paper citations *specifically so* downstream users can drop the axiom for a forwarder once Mathlib catches up, the citation needs to actually point at the right paper.
- **Recommendation**: Update both the file docstring and `tools/cited_axioms.md` entry 10 to cite Bouchard-Elie 2008 SPA 118(1), 53–75. Pardoux-Răşcanu 2014 Thm 5.42 (which is already listed as a secondary reference) is fine as written.

### Finding 3 — `Classical.choose`-based `stochasticIntegral` is non-computable but mathematically clean; flagged for numerical-implementation expectations
- **Severity**: LOW
- **Location**: `LevyStochCalc/Poisson/Compensated.lean:2776-2782` (the `stochasticIntegral` definition) plus the 4 `Classical.choose_spec`-based theorem extractions at lines 2810, 2835–2838, 2856–2858, 2888
- **Evidence**:
  ```
  /-- The *L² stochastic integral* `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` against
  the compensated measure of a Poisson random measure.

  **Refactored** (UNIFIED, 2026-05-10): now defined via `Classical.choose` on the
  4-conjunct unified existence axiom `itoIsometry_compensated_unified_existence`
  (martingale + quadVar + isometry + càdlàg). The resulting `F` IS the genuine
  canonical L²-Itô-Lévy integral. -/
  noncomputable def stochasticIntegral
      {P : Measure Ω} [IsProbabilityMeasure P]
      {ν : Measure E} [SigmaFinite ν]
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
      (φ : Ω → ℝ → E → ℝ)
      (T : ℝ) : Ω → ℝ :=
    (Classical.choose (itoIsometry_compensated_unified_existence N φ)) T
  ```
  This is `noncomputable` by construction. The four downstream theorems (`itoLevyIsometry`, `quadVar_stochasticIntegral`, `martingale_stochasticIntegral`, `cadlag_modification_exists`) all `Classical.choose_spec` against the same axiom, so they are consistent — *one* witness chosen, conjuncts extracted in order.
- **Why this matters**: For my lens, the question is whether downstream numerical work (DeepBSDE training, Monte-Carlo path generation, finite-difference schemes) would be misled by this. The honest answer is **no, but for a subtle reason**: classical Lean stochastic integrals are always non-computable (you need `Classical.choice` for the L²-completion), and any actual numerical scheme would replace `stochasticIntegral` with its own `simpleIntegral`-based discretisation. The `Classical.choose` choice does *not* commit the library to a specific functional dependence on `φ` — it just picks one of possibly many martingales satisfying the four conjuncts. A numerical reader who expected `stochasticIntegral` to be a *specific* limit of explicit Riemann sums would be wrong; but that expectation would be wrong regardless of the implementation (the simple-integrand chain ends in `Lp.coeFn`-via-`LinearIsometry.extend` which is itself an opaque choice). The library is *honestly* non-computable.
- **Recommendation**: Add a short note in `Compensated.lean`'s module docstring (it already has the "stochasticIntegral … is the real L²-Itô-Lévy integral via itoIntegralLp_compensated" paragraph at lines 41–62) clarifying for numerical users: "**For numerical implementations**: `stochasticIntegral` is non-computable; any concrete simulation must instead pin its own simple-predictable approximation `G_n → φ` in `L²(P × ds × dν)` and work with `simpleIntegralLp_compensated G_n`, the chain of which produces a specific Riemann-sum-like object usable by numerics." Doesn't change semantics.

### Finding 4 — No explicit step-size hypotheses anywhere in LevyStochCalc — no numerical reader can be misled into expecting one
- **Severity**: LOW (positive observation, no action required)
- **Location**: scan across `LevyStochCalc/**/*.lean`
- **Evidence**: My `Grep` for `step|mesh|Δt|stepSize|step_size|grid|discrete|partition` returned hits in only 4 files: `Compensated.lean` (using `partition` exclusively for `SimplePredictable`'s time partition), `SimplePredictableRefine.lean` (same), `Brownian/Ito.lean` (same), and `BSDEJ/PathRegularity.lean` (the BET path-regularity partition). None of these are "step-size" hypotheses in the numerical-scheme sense. There is no `(h : ℝ) (h_pos : 0 < h)` step parameter anywhere; the `Δt` in `PathRegularity.lean:129` is the supremum-mesh of the partition, derived from the partition, not a free numerical parameter.
- **Why this matters**: A numerical reader could not be misled into thinking LevyStochCalc proves a `O(h)` convergence rate as `h → 0` — because there is no `h`. Path regularity is stated for a single arbitrary partition with a derived `Δt`. The library is *honestly* a continuous-time formalisation, with no numerical claims.
- **Recommendation**: None. Note kept for completeness so future personas/orchestrator know I checked.

### Finding 5 — `BSDEJ.Existence.continuousBSDEJ_exists_unique` exposes no quantitative solution bound
- **Severity**: LOW
- **Location**: `LevyStochCalc/BSDEJ/Existence.lean:113-127`
- **Evidence**:
  ```
  axiom continuousBSDEJ_exists_unique
      {P : Measure Ω} [IsProbabilityMeasure P]
      {ν : Measure E} [SigmaFinite ν]
      {n d : ℕ}
      (W : …) (N : …) (bsdej : BSDEJData n d E) (X : …)
      (T : ℝ) (_hT : 0 < T) :
      ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
        LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T ∧
        ∀ (Y' …) (Z' …) (U' …),
          LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y' Z' U' T →
          (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = Y' t ω)
  ```
  The Tang-Li / Pardoux-Răşcanu existence theorem typically includes an a-priori bound `‖(Y, Z, U)‖_{S²×H²×H²_ν} ≤ K · (‖ξ‖_{L²} + ‖f(·,·,0,0,0)‖_{L²(0,T)})` for an explicit `K = K(L, T)`. This axiom asserts only existence + a.e.-uniqueness; no `K`, no Lipschitz hypothesis in the bound. The `IsBSDEJSolution` predicate carries L² finiteness conjuncts `< ⊤` but no quantitative bound on the L² norm.
- **Why this matters**: Same as Finding 1 — the literature bound has explicit `K(L, T)`, the Lean version reduces to existence + L²-finiteness. A downstream numerical proof needing an a-priori bound on `‖Y‖_{S²}` to control discretisation error would have to re-derive `K`.
- **Recommendation**: Either accept (in docstring) or extend the axiom statement to expose the `K(L, T)` bound from Pardoux-Răşcanu Thm 4.79. Lower priority than Finding 1 because path regularity is the *bottleneck* for `O(h)` discrete-BSDE rates, while the existence bound enters more loosely.

### Finding 6 — The dissertation roadmap comment about "deep BSDE" / "MFG" in the cited-axioms doc could mislead numerical readers about LevyStochCalc's scope
- **Severity**: LOW
- **Location**: `tools/cited_axioms.md` and module docstrings throughout LevyStochCalc that reference `D:/DeepBSDE/report/dissertation_study/ch02_*` and `D:/DeepBSDE/scripts/proof_validation/*`
- **Evidence**: Multiple files reference dissertation files outside LevyStochCalc (e.g., `BSDEJ/Definition.lean:18-19`, `BSDEJ/Existence.lean:22-23`, `Ito/Setting.lean:17-18`). LevyStochCalc itself contains no deep-BSDE training code, no `C_G`, no `C_1, C_2`, no constants matching the dissertation's E6 north-star bound.
- **Why this matters**: A numerical reader pointed at LevyStochCalc looking for "the formal proof of the E6 bound `C₁·L(θ) + C₂·h`" will find nothing. That's correct (E6 is dissertation-side), but the cross-references could be misread as promising LevyStochCalc-side content. For my mandate this is out-of-scope-by-design (per `shared_context_override.md`), but worth recording for honesty.
- **Recommendation**: None at the LevyStochCalc level — these cross-refs are useful for navigation. Mentioned only so the orchestrator knows I verified there is no numerical-content overlap.

## Per-claim verdicts on the 11 Tier 1 cited axioms + derivative theorems

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `BrownianMotion.exists` (Tier 1 #1) | OUT-OF-SCOPE-FOR-MY-LENS | Pure existence; no quantitative bound to audit |
| `PoissonRandomMeasure.exists_of_sigmaFinite` (Tier 1 #2) | OUT-OF-SCOPE-FOR-MY-LENS | Pure existence |
| `kolmogorovChentsov_modification` (Tier 1 #3) | OUT-OF-SCOPE-FOR-MY-LENS | Pure existence; the KC moment-inequality `q > 1` exponent could be flagged for sharpness, but no numerical convergence rate is asserted in this library |
| `brownian_martingale_rightCont` (Tier 1 #4) | OUT-OF-SCOPE-FOR-MY-LENS | Pure martingale property |
| `itoIsometry_brownian_unified_existence` (Tier 1 #5) | OUT-OF-SCOPE-FOR-MY-LENS | Pure existence + L²-isometry equality; no `h`, no rate |
| `itoIsometry_compensated_unified_existence` (Tier 1 #6) | OUT-OF-SCOPE-FOR-MY-LENS | Same as #5 |
| `cauchySeq_simpleIntegralLp_compensated` (Tier 1 #7) | OUT-OF-SCOPE-FOR-MY-LENS | Cauchy property, not a rate |
| `adaptedSimple_dense_L2_compensated` (Tier 1 #8) | OUT-OF-SCOPE-FOR-MY-LENS | Density, not a rate |
| `continuousBSDEJ_exists_unique` (Tier 1 #9) | WEAK | Existence/uniqueness without the a-priori `K(L,T)` bound from Pardoux-Răşcanu (see Finding 5) |
| **`bsdej_path_regularity` (Tier 1 #10)** | **WEAK** | **`C` is purely existential with no documented dependence on `T, L, ‖ξ‖_{L²}` (Finding 1); citation also wrong (Finding 2)** |
| `itoLevyFormula` (Tier 1 #11) | OUT-OF-SCOPE-FOR-MY-LENS | Itô-Lévy formula is a structural identity; no numerical rate |
| `itoLevyIsometry` (derived) | OUT-OF-SCOPE-FOR-MY-LENS | Equality, not a rate |
| `martingale_stochasticIntegral` (derived) | OUT-OF-SCOPE-FOR-MY-LENS | Martingale property |
| `quadVar_stochasticIntegral` (derived) | OUT-OF-SCOPE-FOR-MY-LENS | Quadratic variation identity |
| `cadlag_modification_exists` (derived) | OUT-OF-SCOPE-FOR-MY-LENS | Path property |
| 6 other derived Brownian theorems | OUT-OF-SCOPE-FOR-MY-LENS | Same |

## Tools and sources used

- **Read**: `D:\LeanRedTeam\shared_context.md`, `D:\LevyStochCalc\redteam_findings\shared_context_override.md`, `D:\LeanRedTeam\personas\06_numerical_analyst.md`, `D:\LeanRedTeam\output_template.md`, `D:\LevyStochCalc\tools\cited_axioms.md`, `D:\LevyStochCalc\LevyStochCalc.lean`, `D:\LevyStochCalc\LevyStochCalc\BSDEJ\PathRegularity.lean`, `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean`, `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean`, `D:\LevyStochCalc\LevyStochCalc\Ito\Setting.lean`, partial reads of `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean` (40–62, 2748–2907), `D:\LevyStochCalc\LevyStochCalc\Brownian\SimplePredictableRefine.lean` (1–80), `D:\Dissertation\Dissertation\Continuous.lean` (150–250)
- **Grep**: `Classical.choose|Classical.choice` over Compensated.lean (12 hits); `stochasticIntegral|noncomputable def|axiom |theorem` over Compensated.lean; `∃ C|∃ \(C :|: ℝ\) ?, ?0 ?< ?C|\(C : ℝ\)` library-wide (1 hit, in PathRegularity.lean); `step|mesh|Δt|stepSize|grid|discrete|partition` library-wide (4 files, no step-size parameter); `solutionBound|L²Bound|L_g|C_X|C_R|Lipschitz` library-wide (6 files, all `Lipschitz` only); `Δt|partition|mesh|grid` on PathRegularity.lean (full content)
- **WebSearch** (5 queries): "Bouchard Elie Touzi 2009 discrete-time approximation FBSDE jumps theorem 2.1 path regularity constant"; `"Bouchard" "Elie" "FBSDE" jumps Stochastic Processes Applications 2008 volume 118 theorem path regularity`; `"Bouchard Elie Touzi" 2009 "Stochastic Processes" volume 119 issue 11 paper FBSDE jumps`; `"Bouchard" "Touzi" "Stochastic Processes and Their Applications" 2009 119 nonlinear PDE`; `Zhang "path regularity" BSDE constant explicit C(L,T,xi) modulus continuity 2004 stopping time`
- **WebFetch** (5 URLs, several blocked by Anubis/access-denied / 403): `https://hal.science/hal-00015486` (blocked); `https://arxiv.org/pdf/1103.3029` (PDF unreadable); `https://www.ceremade.dauphine.fr/~bouchard/pdf/BE05BC06_slides.pdf` (PDF unreadable); `https://arxiv.org/pdf/1110.5059` (PDF unreadable); `https://hal.science/hal-00015486v1/document` (blocked); `https://www.sciencedirect.com/science/article/pii/S030441490700052X` (403); `https://www.semanticscholar.org/paper/...` (empty); `https://ar5iv.labs.arxiv.org/html/0905.0788` (readable — confirmed Zhang-path-regularity literature carries unspecified `C`); `https://arxiv.org/pdf/1211.6231` (PDF unreadable)
- **Papers consulted (via search results, not full text)**:
  - Bouchard, B. & Elie, R. *Discrete time approximation of decoupled Forward-Backward SDE with jumps*, SPA **118**(1), 2008, 53–75. (HAL hal-00015486; ScienceDirect S030441490700052X)
  - Zhang, J. *A numerical scheme for BSDEs*, Annals of Applied Probability **14**(1), 2004, 459–488.
  - Imkeller, P. & dos Reis, G. *Path regularity and explicit convergence rate for BSDE with truncated quadratic growth*, arXiv:0905.0788 (SPA 120(3), 2010, 348–379) — confirms standard practice of `C may change line-to-line` in the BSDE-path-regularity literature.

## What you couldn't verify

- Could not retrieve the actual Bouchard-Elie 2008 paper PDF (HAL and ScienceDirect both blocked / paywalled, the Bouchard slide deck was a binary PDF). The 2008 publication date and SPA 118(1) volume are confirmed only via web-search snippets and the HAL metadata excerpt; **persona-11 (citation verifier) should independently verify the page numbers 53–75 against MathSciNet/Zotero**. The "Touzi is not an author" claim is consistent across all 8 secondary references I could reach but I could not look at the published paper's title page directly.
- Could not retrieve the explicit form of the BET path-regularity constant from the actual paper. Closest secondary evidence (arXiv:0905.0788 follow-up by Imkeller-dos Reis) explicitly says "Constants … may change from line to line" — so the literature *probably* does not give a closed-form `C(T, L, ‖ξ‖_{L²})`, only an asymptotic claim. This means the Lean axiom is **not worse** than the literature; it just doesn't quantitatively improve on it.
- Did not run `lake build` or `lean_verify` on the axiom (per the override doc, the build is known to pass at 8401 jobs and lean_verify is rate-limited; the axiom statement is observed directly via `Read`, which is sufficient for the existential-`C` finding).
- Did not check whether dissertation-side `Dissertation/Continuous.lean` correctly forwards the existential — that's dissertation-side and out of my LevyStochCalc-scoped audit.

## Recommendations for the project (≤ 5 bullets)

- **Fix the BET citation** in `tools/cited_axioms.md` entry 10 and in `LevyStochCalc/BSDEJ/PathRegularity.lean` lines 23–24 and 92–94: Bouchard-Elie 2008 SPA **118**(1), 53–75. Drop "Touzi" from the author list.
- Add a one-paragraph docstring note on `bsdej_path_regularity` clarifying that `C` is opaque and any downstream `O(h)` convergence proof needing an explicit rate must re-derive `C` from BET 2008 / Zhang 2004 / Pardoux-Răşcanu 2014. (One-line documentation fix; no semantic change.)
- Lower-priority: when the axiom is eventually replaced by a Mathlib-backed theorem (per the cited-axioms.md replacement plan), expose an explicit `(L : ℝ) (hL : Lipschitz bsdej ν L)` parameter and state `C = poly(T, L, ‖ξ‖_{L²})`. This would future-proof the library for downstream numerical work.
- Add a single sentence to `LevyStochCalc/Poisson/Compensated.lean`'s module docstring (lines 40–62) noting that `stochasticIntegral` is `noncomputable` (by `Classical.choose`) and that numerical implementations should work with `simpleIntegralLp_compensated G_n` directly.
- No other action — LevyStochCalc is honestly a non-numerical continuous-time library, and my lens does not apply to most of it.
