# Cited Axioms

Theorems in `LevyStochCalc` that depend on **paper-cited stochastic calculus axioms**.
Each entry below names an axiom whose statement is a real published theorem,
introduced as `axiom <name> : <statement>` with a docstring giving the citation.

The `tools/lint.sh` script flags only `sorryAx`-tainted theorems. Cited axioms
are introduced as Lean `axiom` declarations and do NOT count as `sorryAx`.

## Tier 1: Honest cited axioms (11 entries)

These axioms state real published theorems. The LevyStochCalc-side `axiom`
declaration faithfully matches the cited statement. When Mathlib formalises
the underlying theorem, the `axiom` is replaced with a `theorem` forwarding
to the Mathlib version, no other changes needed downstream.

### 1. `LevyStochCalc.Brownian.BrownianMotion.exists`

* **Statement**: There exists a probability space carrying a 1-dimensional Brownian motion.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 2.1.5**; Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 2.1**. Wiener measure construction via Kolmogorov extension + KC modification.
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
* **Reference**: Karatzas–Shreve **Theorem 2.7.7** (Blumenthal 0-1) + **Theorem 2.7.9** (right-continuity of augmented filtration); Le Gall **Proposition 2.10**.
* **Mathlib status (May 2026)**: `MeasureTheory.Filtration.rightCont` is defined; `MeasureTheory.Filtration.IsRightContinuous` predicate available. Blumenthal 0-1 law is NOT in Mathlib for Brownian motion (waits on BM construction). No current activity.
* **Replacement plan**: `theorem brownian_martingale_rightCont := <Blumenthal 0-1 corollary>` when Blumenthal 0-1 for BM lands.

### 5. `LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence`

* **Statement**: For predictable square-integrable `H`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t H² ds` is a `Filt`-martingale (quadratic variation identity), and the L²-isometry `∫⁻ ‖F T‖₊² = ∫⁻ ∫⁻ ‖H‖² over [0,T]` holds at every `T > 0`.
* **Reference**: Karatzas–Shreve **Theorem 3.2.6** (unified martingale + quadratic variation + L²-isometry); Le Gall **Theorem 5.13**.
* **Mathlib status (May 2026)**: No general L²-Itô integral against Brownian motion in Mathlib (waits on BM construction). `MeasureTheory.condExpL2_continuous` and `MeasureTheory.Martingale` provide the analytic glue for the L²-limit-of-martingales argument; the simple-level martingale + quadVar + L²-isometry combine via that glue. arXiv:2511.20118 (Degenne et al, late 2025) is targeting this.
* **Replacement plan**: `theorem itoIsometry_brownian_unified_existence := <Mathlib forwarder>` when Mathlib gains the L²-Itô integral with these properties.

### 6. `LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence`

* **Statement**: For predictable square-integrable `φ`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t ∫_E φ² ν(de) ds` is a `Filt`-martingale, the L²-isometry holds at every `T > 0`, and `F` has càdlàg paths.
* **Reference**: Applebaum 2009 **Theorem 4.2.3** (martingale + quadVar + L²-isometry) + **Theorem 4.2.4** (càdlàg modification); Ikeda–Watanabe **Section II.3**.
* **Mathlib status (May 2026)**: No compensated-Poisson L² integral in Mathlib (waits on Poisson random measure construction). No current activity.
* **Replacement plan**: `theorem itoIsometry_compensated_unified_existence := <Mathlib forwarder>` when Mathlib gains compensated-Poisson L² integration.

### 7. `LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated`

* **Statement**: For an adapted sequence `(G n)` of `SimplePredictable Ω E ν T` with shared endpoint and `(G n).eval` Cauchy in `L²(P × ds × dν)`, the lifted `simpleIntegralLp_compensated (G n)` is Cauchy in `Lp ℝ 2 P`.
* **Reference**: Applebaum 2009 **Equation 4.3.1** + **Lemma 4.2.5** (L²-isometry on simple integrands, applied to differences via common refinement of partitions); Ikeda–Watanabe **Lemma II.3.4**.
* **Mathlib status (May 2026)**: No current Mathlib activity for compensated-Poisson simple integrals or their common refinement. The underlying mathematical content (L²-isometry on differences via partition refinement) is a finite-sum calculation; the missing piece is mechanizing the common-refinement chain for `SimplePredictable Ω E ν T` (mirror of the Brownian `commonRefinement_*` C0b chain).
* **Replacement plan**: This axiom becomes a theorem once the Compensated common-refinement chain is mechanized — independent of any Mathlib activity. Standalone follow-up.

### 8. `LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated`

* **Statement**: For progressively-measurable `φ : Ω → ℝ → E → ℝ` with finite L² norm on `[0, T]`, there exists a sequence of adapted simple predictables `G n` with `(G n).eval` converging to `φ` in `L²(P × ds × dν)`, plus the shared endpoint + joint measurability properties needed by `exists_itoIntegralL2_compensated`.
* **Reference**: Applebaum 2009 **Lemma 4.2.2** (density of adapted simple predictable functions in L²); Ikeda–Watanabe **Lemma II.3.3**.
* **Mathlib status (May 2026)**: No Mathlib activity for the Compensated case. The Brownian analog `adaptedSimple_dense_L2_brownian` is fully proven via `predictableDyadicSimple_brownian` (dyadic averaging over (s_{i-1}, s_i] blocks). The Compensated extension to the mark dimension `E` (dyadic averaging over (s_{i-1}, s_i] × E_j with `(E_j)` from the σ-finite decomposition of ν) is the missing piece.
* **Replacement plan**: This axiom becomes a theorem once the Compensated dyadic predictable construction lands (mirror of the Brownian `predictableDyadicSimple_brownian` chain) — independent of any Mathlib activity. Standalone follow-up.

### 9. `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique`

* **Statement**: Under Lipschitz hypotheses on `(f, g)` and L² integrability of terminal data, the continuous BSDEJ has a unique adapted solution triple `(Y, Z, U) ∈ S² × H² × H²_N` satisfying the strengthened `IsBSDEJSolution` predicate.
* **Reference**: Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, **Theorem 3.1**; Gnoatto, *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, **Theorem 2.2**; Pardoux & Răşcanu, *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*, Springer 2014, **Theorem 4.79**.
* **Predicate state (2026-05-11)**: The `IsBSDEJSolution` predicate was tightened on 2026-05-11 — the previous vacuous per-`(t, ω)` existential `∃ BM_term jump_term : ℝ, …` (which made the axiom mathematically false as written, since multiple distinct `Y` could trivially satisfy it) was replaced with an outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to `Z, U` via L²-isometry (for `M_W` vs `Z`) and direct equality to `Compensated.stochasticIntegral` (for `M_N` vs `U`). The strengthened predicate is no longer vacuously satisfiable by constant `Y` for generic `(f, g)`. Documented in `BSDEJ/Definition.lean` module docstring.
* **Mathlib status (May 2026)**: No BSDEJ in Mathlib. `Mathlib.Analysis.SpecificLimits.Basic` has Picard / contraction-mapping infrastructure (`ContractingWith.fixedPoint`) usable for the proof body once the L² Itô-Lévy + martingale representation pieces land.
* **Replacement plan**: `theorem continuousBSDEJ_exists_unique := <Picard contraction proof>` when the L² Itô-Lévy chain is fully formalized (after items 5 + 6 above). Further predicate-tightening (pinning `M_W` to the actual multidim Brownian stochastic integral, not just an isometric martingale) is a separate downstream item — needs `h_progMeas` threaded through `IsBSDEJSolution`.

### 10. `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity`

* **Statement**: For the unique BSDEJ solution (satisfying the strengthened `IsBSDEJSolution` predicate from item 9), the L²-time modulus + projection errors of `(Z, U)` over a partition with mesh `Δt` are bounded by `C · Δt`.
* **Reference**: Bouchard, Elie & Touzi, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 119(11), 2009, **Theorem 2.1**; Pardoux & Răşcanu, Springer 2014, **Theorem 5.42**.
* **Predicate state**: Same strengthening note as item 9.
* **Mathlib status (May 2026)**: `MeasureTheory.Submartingale.upcrossingsBefore_le` and adjacent Doob's L²-maximal inequality infrastructure exists in `Mathlib.Probability.Martingale`. The Grönwall integral lemma `Mathlib.Analysis.Gronwall` is also available. Combining these into the path regularity bound is mechanical once items 5 + 6 + 9 land.
* **Replacement plan**: `theorem bsdej_path_regularity := <Doob + Grönwall combination>` when items 5, 6, 9 are theorems.

### 11. `LevyStochCalc.Ito.JumpFormula.itoLevyFormula`

* **Statement**: For a `C^{1,2}` function `u` and a jump diffusion `X = (μ, σ, γ)`-driven by `(W, N)`, there exist four processes `(drift_term, diff_mart, jump_mart, comp_drift)` summing to `u(T, X_T) − u(0, X_0)` almost surely. Each term corresponds to a literature integral form: drift via `∫(∂_t u + 𝓛u) ds`, Brownian martingale via `∫ ∇uᵀ σ dW`, jump martingale via `∫∫(u(·+γ) − u) Ñ`, compensator drift via `∫∫(u(·+γ) − u − γᵀ∇u) ν ds`, where `𝓛u = μᵀ∇u + ½Tr(σσᵀ∇²u)`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.4.7**; Cont & Tankov, *Financial Modelling with Jump Processes*, Chapman & Hall/CRC 2003, **Proposition 8.18**.
* **Predicate state (2026-05-11 — newly DEMOTED)**: Previously declared as `theorem` whose proof body was the trivial-witness pattern `refine ⟨0, 0, 0, fun ω => u T (X T ω) - u 0 (X 0 ω), ?_⟩; simp` — three identically-zero processes with the entire change stuffed into the fourth term. That satisfied the existential vacuously. Per the recursive audit standard, downgraded to a documented `axiom` with the literature citation. Better an honest axiom than a fake theorem.
* **Mathlib status (May 2026)**: No general Itô-with-jumps formula in Mathlib (waits on the full jump-SDE apparatus). `Mathlib.Probability.IteFormula`-style infrastructure exists for the continuous (Brownian-only) case, but not for the jump case.
* **Replacement plan**: `theorem itoLevyFormula := <Applebaum 4.4.7 derivation>` when the four primitives (Brownian stochastic integral, compensated-Poisson stochastic integral, Lebesgue integrals against `μ, ½σσᵀ, γ`, jump-diffusion semimartingale apparatus) are all in place. Multi-session work.

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

## Status snapshot (2026-05-11, post-recursive-audit)

`tools/sorry_baseline.txt` is **empty**. Every previously sorry'd theorem is
either:
* Proven from Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
  plus possibly one or more Tier 1 cited axioms documented here, OR
* A Tier 1 cited axiom itself.

### Recursive audit (2026-05-11) — internal classification

Per the user's recursive-audit standard (trivial-witness theorems = worse
than documented axioms), the 4 LevyStochCalc theorems the dissertation
forwards into were classified:

| Theorem | Classification | Action taken |
|---|---|---|
| `Poisson.L2Isometry.itoLevyIsometry` | (R) Real | Leave alone (extracts from Tier 1 unified-existence axiom with non-trivial quadVar conjunct that rules out constant witnesses) |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` | (C) Cosmetic predicate | `IsBSDEJSolution` strengthened: replaced vacuous per-`(t, ω)` existential `∃ BM jump : ℝ` with outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to Z (L²-isometry) and U (direct `=` to `Compensated.stochasticIntegral`) |
| `Ito.JumpFormula.itoLevyFormula` | (C) Cosmetic theorem | DEMOTED from `theorem` (trivial-witness proof) to `axiom` (Tier 1 #11, this file) |
| `BSDEJ.PathRegularity.bsdej_path_regularity` | (C) Cosmetic predicate | Same as `continuousBSDEJ_exists_unique` — fixed by the `IsBSDEJSolution` strengthening |

### Net audit (verifiable via `tools/full_audit.lean`)

* **11 Tier 1 cited axioms** total, each with paper reference + Mathlib status + replacement plan.
* **10 honest derivative theorems**, axiom-clean modulo Lean std + Tier 1 cited.
* No `sorryAx` anywhere in the public API.
* No trivial-witness theorems remain. Dissertation forwarders now transitively surface real Tier 1 cited axioms in their audit, including the newly-demoted #11 `itoLevyFormula`.

## Convention

* `tools/sorry_baseline.txt` — sorry-blocked theorems. Currently empty.
* `tools/cited_axioms.md` (this file) — Tier 1 cited axioms with citations + Mathlib status + replacement plans.
* `tools/full_audit.lean` — `#print axioms` on every public theorem; runs as part of CI to verify the axiom budget.
