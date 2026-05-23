# Cited Axioms

Theorems in `LevyStochCalc` that depend on **paper-cited stochastic calculus axioms**.
Each entry below names an axiom whose statement is a real published theorem,
introduced as `axiom <name> : <statement>` with a docstring giving the citation.

The `tools/lint.sh` script flags only `sorryAx`-tainted theorems. Cited axioms
are introduced as Lean `axiom` declarations and do NOT count as `sorryAx`.

## Tier 1: Honest cited axioms (9 currently live; #7 and #8 deleted 2026-05-22)

These axioms state real published theorems. The LevyStochCalc-side `axiom`
declaration faithfully matches the cited statement. When Mathlib formalises
the underlying theorem, the `axiom` is replaced with a `theorem` forwarding
to the Mathlib version, no other changes needed downstream.

### 1. `LevyStochCalc.Brownian.BrownianMotion.exists`

* **Statement**: There exists a probability space carrying a 1-dimensional Brownian motion.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 2.2.2** (Daniell-Kolmogorov consistency) + **Theorem 2.2.8** (Kolmogorov-Čentsov continuous-modification existence) — Chapter 2 §2.2 "First Construction of Brownian Motion" pp. 49-56 (correcting the previous "Theorem 2.1.5" citation flagged by red-team P11 2nd audit — §2.1 of K-S is the chapter Introduction, no theorem 2.1.5 exists); Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Definition 2.1** / **Definition 2.12** / **Corollary 2.11** (the Brownian-motion construction; correcting the previous "Theorem 2.1" citation flagged by red-team P11 — Le Gall 2016 has no "Theorem 2.1"; the existence statement combines the definition + the explicit Wiener-measure construction in Chapter 2). Wiener measure construction via Kolmogorov extension + KC modification.
* **Mathlib status (May 2026)**: No current `MeasureTheory.WienerMeasure` or `BrownianMotion` definition. Adjacent infrastructure exists: `ProbabilityTheory.gaussianReal` (Real Gaussian distribution), `ProbabilityTheory.IsGaussianProcess`, `MeasureTheory.IsProjectiveLimit`, `Probability.Kernel.IonescuTulcea.trajMeasure` (dyadic-time Markov chains). The "Degenne et al stochastic integration" effort (arXiv:2511.20118, late 2025) is the most active push toward Mathlib-Brownian; no Mathlib PR merged at time of writing.
* **Replacement plan**: `theorem BrownianMotion.exists := <Mathlib forwarder>` when `MeasureTheory.WienerMeasure` lands.

### 2. `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite`

* **Statement**: For σ-finite intensity ν on standard Borel E, ∃ probability space carrying a Poisson random measure with intensity `vol[0,∞) ⊗ ν`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 2.3.1**; Kallenberg, *Random Measures, Theory and Applications*, Springer 2017, **Proposition 3.6**.
* **Mathlib status (May 2026)**: `ProbabilityTheory.poissonMeasure` exists (ℕ-valued Poisson distribution), but no Poisson random measure construction. No current Mathlib activity for Poisson random measures or general Lévy processes.
* **Replacement plan**: `theorem PoissonRandomMeasure.exists_of_sigmaFinite := <Mathlib forwarder>` when `MeasureTheory.PoissonRandomMeasure` lands.

### 3. `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification`

* **Statement**: A real-valued process satisfying the Kolmogorov moment condition with `q > 1` admits a modification with continuous paths.
* **Reference**: Karatzas–Shreve **Theorem 2.2.8**; Le Gall **Theorem 2.9**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Springer 1999, **Theorem I.2.1**.
* **Mathlib status (May 2026)**: `ProbabilityTheory.IsKolmogorovProcess` is defined (the *condition*) with `mk_of_secondCountableTopology` constructor and various API lemmas (measurable, edist_eq_zero, stronglyMeasurable_edist). The modification *theorem* (existence of continuous version) is NOT yet present. Active partial work in `Mathlib.Probability.Process.Kolmogorov`.
* **Replacement plan**: `theorem kolmogorovChentsov_modification := IsKolmogorovProcess.exists_continuous_modification` (or equivalent) when the modification theorem is added.

### 4. `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont`

* **Statement**: Brownian motion is a martingale w.r.t. the right-continuous augmentation of its natural filtration (consequence of Blumenthal 0-1 law).
* **Reference**: Karatzas–Shreve **Theorem 2.7.7** (Blumenthal 0-1) + **Theorem 2.7.9** (right-continuity of augmented filtration); Le Gall **Theorem 2.13** (Blumenthal 0-1 for Brownian motion; correcting the previous "Proposition 2.10" citation flagged by red-team P11 — Le Gall 2016 p. 25 "Lemma 2.10" is a deterministic real-analysis Hölder lemma; Blumenthal is Le Gall p. 30 Theorem 2.13).
* **Mathlib status (May 2026)**: `MeasureTheory.Filtration.rightCont` is defined; `MeasureTheory.Filtration.IsRightContinuous` predicate available. Blumenthal 0-1 law is NOT in Mathlib for Brownian motion (waits on BM construction). No current activity.
* **Replacement plan**: `theorem brownian_martingale_rightCont := <Blumenthal 0-1 corollary>` when Blumenthal 0-1 for BM lands.

### 5. `LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence`

* **Statement**: For predictable square-integrable `H`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t H² ds` is a `Filt`-martingale (quadratic variation identity), and the L²-isometry `∫⁻ ‖F T‖₊² = ∫⁻ ∫⁻ ‖H‖² over [0,T]` holds at every `T > 0`.
* **Reference**: Karatzas–Shreve **Theorem 3.2.6** (unified martingale + quadratic variation + L²-isometry); Le Gall **Theorem 5.4** + equation **(5.8)** (Itô isometry; correcting the previous "Theorem 5.13" citation flagged by red-team P11 — Le Gall 2016 p. 121 "Theorem 5.13" is Dambis–Dubins–Schwarz, not Itô isometry; L² Itô isometry is Le Gall Thm 5.4 with the explicit norm-equality at eq. (5.8)).
* **Mathlib status (May 2026)**: No general L²-Itô integral against Brownian motion in Mathlib (waits on BM construction). `MeasureTheory.condExpL2_continuous` and `MeasureTheory.Martingale` provide the analytic glue for the L²-limit-of-martingales argument; the simple-level martingale + quadVar + L²-isometry combine via that glue. arXiv:2511.20118 (Degenne et al, late 2025) is targeting this.
* **Replacement plan**: `theorem itoIsometry_brownian_unified_existence := <Mathlib forwarder>` when Mathlib gains the L²-Itô integral with these properties.

### 6. `LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence`

* **Statement**: For predictable square-integrable `φ`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t ∫_E φ² ν(de) ds` is a `Filt`-martingale, the L²-isometry holds at every `T > 0`, and `F` has càdlàg paths.
* **Reference**: Applebaum 2009 **Theorem 4.2.3** (martingale + quadVar + L²-isometry) + **Theorem 4.2.4** (càdlàg modification); Ikeda–Watanabe **Section II.3**.
* **Mathlib status (May 2026)**: No compensated-Poisson L² integral in Mathlib (waits on Poisson random measure construction). No current activity.
* **Replacement plan**: `theorem itoIsometry_compensated_unified_existence := <Mathlib forwarder>` when Mathlib gains compensated-Poisson L² integration.

### 7. `LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` (DELETED 2026-05-22)

This axiom was deleted on 2026-05-22 as dead code. It was the Compensated
Cauchy-completion step in the L² Itô-Lévy construction route that was
superseded by the 2026-05-10 unified-existence axiom refactor. Per
red-team finding M4, neither this axiom nor its downstream chain
(`simpleIntegralLp_compensated` → `itoIntegralLp_compensated` →
`exists_itoIntegralL2_compensated` → `itoIsometry_compensated_existence`
→ `stochasticIntegral_isometry_only_compensated`) was reachable from any
audited load-bearing theorem; the public `Compensated.stochasticIntegral`
is built directly from `itoIsometry_compensated_unified_existence`
(Tier 1 #6).

Original statement (recoverable from git history before commit deleting
the chain): for an adapted sequence `(G n)` of `SimplePredictable Ω E ν T`
with shared endpoint and `(G n).eval` Cauchy in `L²(P × ds × dν)`, the
lifted `simpleIntegralLp_compensated (G n)` is Cauchy in `Lp ℝ 2 P`
(Applebaum 2009 Equation 4.3.1 + Lemma 4.2.5).

### 8. `LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated` (DELETED 2026-05-22)

This axiom was deleted on 2026-05-22 as dead code, alongside #7. It was
the Compensated L²-density-of-adapted-simple-predictables step in the
same superseded chain. Per red-team finding M4, not reachable from any
audited load-bearing theorem.

Original statement (recoverable from git history): for progressively-
measurable `φ : Ω → ℝ → E → ℝ` with finite L² norm on `[0, T]`, there
exists a sequence of adapted simple predictables `G n` with `(G n).eval`
converging to `φ` in `L²(P × ds × dν)` plus the shared endpoint + joint
measurability properties needed downstream (Applebaum 2009 Lemma 4.2.2).

### 9. `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique`

* **Statement**: Under Lipschitz hypotheses on `(f, g)` and L² integrability of terminal data, the continuous BSDEJ has a unique adapted solution triple `(Y, Z, U) ∈ S² × H² × H²_N` satisfying the strengthened `IsBSDEJSolution` predicate.
* **Reference**: Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, **Theorem 3.1**; Andersson, Gnoatto, Patacca & Picarelli, *A deep solver for BSDEs with jumps*, SIAM J. Financial Math. / arXiv:2211.04349, 2025, **Theorem 2.4** (correcting the previous fabricated citation "Gnoatto 2025 *Quantitative Finance* primer" flagged by red-team P11 — no such paper exists per DBLP); Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer EAA 2013 (first edition, DOI 10.1007/978-1-4471-5331-3), **Theorem 4.1.3** (jumps case, directly applicable). For continuous-only background see also Pardoux & Răşcanu, *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*, Springer 2014, **Theorem 4.79** — but note Pardoux-Răşcanu does NOT cover the BSDEJ (jump) case per red-team P11 2nd audit 2026-05-23; the jump-case authority is Tang-Li + Delong + AGPP.
* **Predicate state (2026-05-11)**: The `IsBSDEJSolution` predicate was tightened on 2026-05-11 — the previous vacuous per-`(t, ω)` existential `∃ BM_term jump_term : ℝ, …` (which made the axiom mathematically false as written, since multiple distinct `Y` could trivially satisfy it) was replaced with an outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to `Z, U` via L²-isometry (for `M_W` vs `Z`) and direct equality to `Compensated.stochasticIntegral` (for `M_N` vs `U`). The strengthened predicate is no longer vacuously satisfiable by constant `Y` for generic `(f, g)`. Documented in `BSDEJ/Definition.lean` module docstring.
* **Mathlib status (May 2026)**: No BSDEJ in Mathlib. `Mathlib.Analysis.SpecificLimits.Basic` has Picard / contraction-mapping infrastructure (`ContractingWith.fixedPoint`) usable for the proof body once the L² Itô-Lévy + martingale representation pieces land.
* **Replacement plan**: `theorem continuousBSDEJ_exists_unique := <Picard contraction proof>` when the L² Itô-Lévy chain is fully formalized (after items 5 + 6 above). Further predicate-tightening (pinning `M_W` to the actual multidim Brownian stochastic integral, not just an isometric martingale) is a separate downstream item — needs `h_progMeas` threaded through `IsBSDEJSolution`.

### 10. `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity`

* **Statement**: For the unique BSDEJ solution (satisfying the strengthened `IsBSDEJSolution` predicate from item 9), the L²-time modulus + projection errors of `(Z, U)` over a partition with mesh `Δt` are bounded by `C · Δt`.
* **Reference**: Bouchard & Elie, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, Stochastic Processes Appl. **118(1)**, **2008**, pp. 53–75, **Theorem 2.1** (correcting the previous misattribution to "Bouchard, Elie & Touzi 2009 SPA 119(11)" — Touzi is not an author and no such 2009 paper exists; flagged by red-team P06/P07/P10/P11, verified via Bouchard's slides + HAL hal-00015486 + Kharroubi–Lim 2018 citing "Bouchard and Elie [4]"). For continuous-only background see also Pardoux & Răşcanu, Springer 2014, **Theorem 5.42** (continuous case, NOT BSDEJ) — Pardoux-Răşcanu does NOT cover the jump case per red-team P11 2nd audit 2026-05-23.
* **Predicate state**: Same strengthening note as item 9.
* **Mathlib status (May 2026)**: `MeasureTheory.Submartingale.upcrossingsBefore_le` and adjacent Doob's L²-maximal inequality infrastructure exists in `Mathlib.Probability.Martingale`. The Grönwall integral lemma `Mathlib.Analysis.Gronwall` is also available. Combining these into the path regularity bound is mechanical once items 5 + 6 + 9 land.
* **Replacement plan**: `theorem bsdej_path_regularity := <Doob + Grönwall combination>` when items 5, 6, 9 are theorems.

### 11. `LevyStochCalc.Ito.JumpFormula.itoLevyFormula`

* **Statement**: For a `C^{1,2}` function `u` and a jump diffusion `X = (μ, σ, γ)`-driven by `(W, N)`, the chain-rule decomposition (Applebaum 2009 Thm 4.4.7) — `u(T, X_T) − u(0, X_0) = drift + diff_mart + jump_mart + comp_drift` — with ALL FOUR terms pinned to their literature integral forms:
  * `drift = ∫_0^T (∂_t u + 𝓛u)(s, X_s) ds` using `driftIntegrand` (which uses `timeDeriv`, `gradient`, `hessian`, `levyGenerator` helpers).
  * `diff_mart = MultidimBrownianMotion.stochasticIntegral W (diffusionIntegrand := ∇uᵀσ along X) T` (multidim Brownian Itô integral).
  * `jump_mart = Compensated.stochasticIntegral N (jump increment u(·+γ) − u along X) T`.
  * `comp_drift = ∫_0^T ∫_E [u(·+γ) − u − γᵀ∇u](s, X_s, e) ∂ν(de) ds` using `compensatorDriftIntegrand`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.4.7**; Cont & Tankov, *Financial Modelling with Jump Processes*, Chapman & Hall/CRC 2003, **Proposition 8.18**.
* **Predicate state (2026-05-22 — fully pinned)**: Originally a `theorem` with the trivial-witness proof body `refine ⟨0, 0, 0, change, ?_⟩; simp`. Demoted to `axiom` on 2026-05-11 (commit db582f9). Statement then fully pinned in 4 commits today (2026-05-22): `jump_mart` pinned 7d232bf, `diff_mart` pinned 09687cf, `comp_drift` pinned 9675e44, `drift_term` pinned 94f0155. No existential reals remain. Axiom asserts the exact Applebaum identity.
* **Transitive axiom dependency**: now surfaces Tier 1 #5 (`itoIsometry_brownian_unified_existence`, via multidim Brownian integral) and Tier 1 #6 (`itoIsometry_compensated_unified_existence`, via Compensated.stochasticIntegral).
* **Mathlib status (May 2026)**: No general Itô-with-jumps formula in Mathlib (waits on the full jump-SDE apparatus). `Mathlib.Probability.IteFormula`-style infrastructure exists for the continuous (Brownian-only) case, but not for the jump case.
* **Replacement plan**: `theorem itoLevyFormula := <Applebaum 4.4.7 derivation>` when (a) the multidim Brownian + compensated-Poisson integrals along the X-path are usable on the right hypothesis class, and (b) the Bochner integrals of the time-derivative + Lévy generator can be controlled (Sobolev estimates on u). Multi-session work.

## Honest derivative theorems (proven from cited axioms)

| Theorem | Forwards via |
|---|---|
| `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` | `BrownianMotion.exists` |
| `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification` | `kolmogorovChentsov_modification` |
| `LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous` | `brownian_martingale_rightCont` |
| `LevyStochCalc.Brownian.Ito.itoIsometry` | `itoIsometry_brownian_unified_existence` (extracts conjunct 3) |
| `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 1) |
| `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 2) |
| `LevyStochCalc.Poisson.Compensated.itoLevyIsometry` | `itoIsometry_compensated_unified_existence` (extracts conjunct 3) |
| `LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral` | `itoIsometry_compensated_unified_existence` (extracts conjunct 1) |
| `LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral` | `itoIsometry_compensated_unified_existence` (extracts conjunct 2) |
| `LevyStochCalc.Poisson.Compensated.cadlag_modification_exists` | `itoIsometry_compensated_unified_existence` (extracts conjunct 4) |
| `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry` | 1-line forwarder over `Compensated.itoLevyIsometry` |

## Status snapshot (2026-05-22, post-red-team cleanup)

`tools/sorry_baseline.txt` contains **2 entries** for theorems whose proofs
are deferred to substantial classical infrastructure (Picard iteration for
SDE existence, predictable-projection chaos decomposition for martingale
representation). Every other previously sorry'd theorem is either:
* Proven from Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
  plus possibly one or more Tier 1 cited axioms documented here, OR
* A Tier 1 cited axiom itself.

Baseline entries (the two genuinely-deferred classical theorems):
* `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` — Picard
  iteration in `S²([0,T]; ℝⁿ)` for the jump-diffusion SDE
  (Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV). Real theorem statement
  with sorry'd proof body.
* `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation`
  — Jacod 1976 martingale representation theorem for `(W, Ñ)` filtrations
  (Jacod-Shiryaev Thm III.4.34). Real theorem statement with sorry'd proof
  body. The integrand pinning to `MultidimBrownianMotion.stochasticIntegral`
  and `Compensated.stochasticIntegral` (canonical integrals) is at the
  statement level — no trivial-witness leakage.

### Recursive audit (2026-05-11) — internal classification

Per the user's recursive-audit standard (trivial-witness theorems = worse
than documented axioms), the 4 LevyStochCalc theorems the dissertation
forwards into were classified:

| Theorem | Classification | Action taken |
|---|---|---|
| `Poisson.L2Isometry.itoLevyIsometry` | (R) Real | Leave alone (extracts from Tier 1 unified-existence axiom with non-trivial quadVar conjunct that rules out constant witnesses) |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` | (C) Cosmetic predicate | `IsBSDEJSolution` strengthened: replaced vacuous per-`(t, ω)` existential `∃ BM jump : ℝ` with outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to Z (L²-isometry) and U (direct `=` to `Compensated.stochasticIntegral`); adaptedness layer added 2026-05-21 (closes red-team C1); `M_W` pinned to canonical multidim Brownian Itô integral 2026-05-22 (closes red-team H2). |
| `Ito.JumpFormula.itoLevyFormula` | (C) Cosmetic theorem | DEMOTED from `theorem` (trivial-witness proof) to `axiom`; all 4 terms pinned to literature integral forms 2026-05-22 (closes red-team C2) |
| `BSDEJ.PathRegularity.bsdej_path_regularity` | (C) Cosmetic predicate | Same as `continuousBSDEJ_exists_unique` — fixed by the `IsBSDEJSolution` strengthening; `Z_avg`/`U_avg` pinned to `conditionalTimeAverage_*` 2026-05-22 (closes red-team H3) |

### Red-team audit fix log (2026-05-20 audit, fixes through 2026-05-22)

The 12-persona red-team audit ran on commit db582f9. Per-finding fix status:

**CRITICAL (all closed):**
* **C1** (BSDEJ unsoundness): closed by `IsBSDEJSolution` adaptedness +
  `M_W` canonical-integral pinning (commits 2d9309e, 1b1f69f).
* **C2** (itoLevyFormula trivial-witness statement): closed by pinning
  all 4 terms (commits 7d232bf, 09687cf, 9675e44, 94f0155).
* **C3** (JumpDiffusion trivial-witness): closed — `is_solution` field
  strengthened from `True` to real SDE integral equation; proof now
  honestly sorry'd in baseline (commit 62e124a).
* **C4** (jacodYor trivial-witness): closed — signature strengthened to
  pin BM/jump integrals to canonical forms; proof now honestly sorry'd
  in baseline.
* **C5** (3 public sorryAx hidden from audit): closed — `kolmogorov_modification_ae_eq`
  fully proved (commit 259d2d2); `poissonRandomMeasure_finite_exists`
  forwarded to σ-finite axiom (commit 2a88b87); `simplePredictable_dense_L2`
  deleted as dead code (commit 6b25dfc).
* **C6** (Gnoatto 2025 fabrication): closed — replaced with real
  Andersson-Gnoatto-Patacca-Picarelli 2025 citation.
* **C7** (BET 2009 misattribution): closed — replaced with Bouchard-Elie
  2008 SPA 118(1).
* **C8** (518 lines untracked): closed by `git add` of all source +
  build configs.
* **C9** (lint.sh silently passing): closed — hardened to fail when audit
  output is missing/empty.

**HIGH (all closed):**
* **H1, H2** (BSDEJ adaptedness / M_W pinning): closed (see C1).
* **H3** (Z_avg/U_avg loose existential): closed by pinning to
  `conditionalTimeAverage_*`.
* **H4** (missing Lipschitz / L² / measurability on BSDEJ axioms): closed.
* **H5** (Compensated unified-existence asymmetric vs Brownian): closed
  by adding `h_meas` + `h_sq_int` outer hypotheses (commit 359beda).
* **H7, H8** (Le Gall citation theorem-number errors): closed (commit b065b7d).
* **H9** (Pardoux-Răşcanu continuous-case in BSDEJ citations): retained
  with explicit `(continuous case)` parenthetical to honestly mark the
  scope.
* **H10** (lake-manifest project-name + toolchain): closed.

**MEDIUM:**
* **M1** (7+ `True := trivial` lemmas): closed — all 8 stubs deleted
  (commit 638b21d).
* **M2** (4 dead-code `sorry` privates): closed by direct proof
  (`kolmogorov_modification_ae_eq`, `poissonRandomMeasure_finite_exists`)
  or deletion (`quadVar_simpleIntegral_brownian`,
  `simplePredictable_dense_L2_bounded`).
* **M3** (677-line orphan `Poisson/Martingale.lean`): closed (commit eb707a4).
* **M4** (Tier 1 #7 + #8 dead post-refactor): retained pending careful
  walk-up deletion of the intertwined dead chain (substantial follow-up).
* **M6** (this file's "No trivial-witness theorems remain" claim): closed
  by this update.
* **M13** (Le Gall Thm 2.1 citation for BM existence): closed (commit b065b7d).

**Open / deferred:**
* **H6** (Predictable vs. Measurable hypothesis): predictable σ-algebra
  scaffolding not yet built; deferred.
* **M5** (`adaptedSimple_dense_L2_compensated` docstring vs signature):
  paired with M4 (the axiom itself is candidate for deletion).
* **M8** (path-regularity constant parameterization): style; deferred.
* **M9** (multidim Brownian primitive): closed in spirit — built as
  `Brownian/MultidimIto.lean`.
* **M10** (scalar-Y BSDEJData): scope; not a defect, generalization.
* **M11** (`IsBSDEJSolution` filtration trivial-constant): the natural-
  filtration-pin requires `joint_past_future_independent` exposure
  through the BSDEJSolution structure; deferred.
* **M12** (`integral_undef` exploit on Compensated quadVar): closed
  alongside H5.

### Net audit (verifiable via `tools/lint.sh` + `_audit.lean`)

* **11 Tier 1 cited axioms** total, each with paper reference + Mathlib status + replacement plan.
* **Honest derivative theorems**, axiom-clean modulo Lean std + Tier 1 cited.
* No `sorryAx` in the public API outside the 2 baseline-acknowledged entries.
* No `True := trivial` stub lemmas remain in the project.
* Dissertation forwarders transitively surface only real Tier 1 cited axioms
  in their audit, including the now-fully-pinned #11 `itoLevyFormula`.

## Convention

* `tools/sorry_baseline.txt` — sorry-blocked theorems (currently 2: see
  status snapshot above).
* `tools/cited_axioms.md` (this file) — Tier 1 cited axioms with citations + Mathlib status + replacement plans.
* `tools/lint.sh` — runs `_audit.lean` and fails on new sorryAx beyond
  the baseline.
* `_audit.lean` — `#print axioms` on every load-bearing theorem; runs as
  part of CI to verify the axiom budget.
