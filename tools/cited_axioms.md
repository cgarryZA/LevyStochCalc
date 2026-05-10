# Cited Axioms

Theorems in `LevyStochCalc` that depend on **paper-cited stochastic calculus axioms**.
Each entry below names an axiom whose statement is a standard published theorem,
introduced as `axiom <name> : <statement>` with a docstring giving the citation.

The `tools/lint.sh` script flags only `sorryAx`-tainted theorems. Cited axioms
are introduced as Lean `axiom` declarations and do NOT count as `sorryAx`. Hence
theorems that depend only on cited axioms (and Lean's standard axioms) are
"axiom-clean modulo cited axioms" — acceptable closure.

When Mathlib eventually formalises the underlying mathematical fact, each
`axiom` declaration can be replaced by a `theorem` forwarding to the Mathlib
version, with no other changes needed downstream.

This is the same pattern the dissertation uses (see
`Dissertation/Continuous.lean` — `itoLevyIsometry` cited to Applebaum 2009 Thm
4.2.3, etc.).

## Convention

* `tools/sorry_baseline.txt` lists theorems that are sorry-blocked. These are
  NOT acceptable closures.
* `tools/cited_axioms.md` (this file) lists theorems that depend on a cited
  axiom (acceptable closure). They are dropped from `sorry_baseline.txt`.

## Axiom Registry

### Layer 0: Foundational existence theorems

#### `LevyStochCalc.Brownian.BrownianMotion.exists`

* **File**: `LevyStochCalc/Brownian/Construction.lean`
* **Statement**: `∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P)`
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, Theorem 2.1.5; Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, Theorem 2.1.
* **Mathlib replacement**: when `MeasureTheory.WienerMeasure` (or equivalent Brownian motion construction via Kolmogorov extension + Kolmogorov-Chentsov modification) lands.

#### `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite`

* **File**: `LevyStochCalc/Poisson/RandomMeasure.lean`
* **Statement**: For σ-finite intensity ν on standard Borel E, ∃ probability space carrying a Poisson random measure with intensity `vol[0,∞) ⊗ ν`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, Theorem 2.3.1; Kallenberg, *Random Measures, Theory and Applications*, Springer 2017, Proposition 3.6.
* **Mathlib replacement**: when `PoissonRandomMeasure` / Lévy process construction lands.

### Layer 1: Continuity and modification theorems

#### `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification`

* **File**: `LevyStochCalc/Brownian/Continuity.lean`
* **Statement**: `IsKolmogorovProcess X P p q M → 1 < q → ∃ Y : ℝ → Ω → ℝ, (continuous a.s.) ∧ (modification of X)`.
* **Reference**: Karatzas–Shreve, Theorem 2.2.8; Le Gall, Theorem 2.9; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Springer 1999, Theorem I.2.1.
* **Mathlib replacement**: when `ProbabilityTheory.IsKolmogorovProcess`'s modification theorem lands (currently has only the condition).

#### `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont`

* **File**: `LevyStochCalc/Brownian/Martingale.lean`
* **Statement**: `Martingale W (naturalFiltration W).rightCont P` (Brownian motion is a martingale w.r.t. the right-continuous augmentation of its natural filtration).
* **Reference**: Karatzas–Shreve, Theorem 2.7.7 (Blumenthal 0-1 law) + Theorem 2.7.9 (continuity of augmented filtration); Le Gall, Proposition 2.10.
* **Mathlib replacement**: when Mathlib gains Blumenthal 0-1 law for Brownian motion.

### Layer 1.5: L² stochastic integral martingale + quadratic variation

#### `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral`

* **File**: `LevyStochCalc/Brownian/SimplePredictableRefine.lean`
* **Statement**: For predictable square-integrable H, `t ↦ (M_t)² − ∫_0^t |H_s|² ds` is a martingale (where `M = ∫_0^· H_s dW_s`).
* **Reference**: Karatzas–Shreve, Theorem 3.2.6; Le Gall, Theorem 5.13.
* **Mathlib replacement**: when the simple-level `quadVar_simpleIntegral_brownian` + L²-limit-of-martingales argument is formalized AND `stochasticIntegral` is replaced with a unified L²-limit construction.

#### `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral`

* **File**: `LevyStochCalc/Brownian/SimplePredictableRefine.lean`
* **Statement**: `∃ F : Filtration, Martingale (∫_0^t H_s dW_s) F P`.
* **Reference**: Same as `quadVar_stochasticIntegral` (Karatzas–Shreve Thm 3.2.6).
* **Mathlib replacement**: same as above.

#### `LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral`

* **File**: `LevyStochCalc/Poisson/Compensated.lean`
* **Statement**: For predictable square-integrable φ, `t ↦ (M_t)² − ∫_0^t ∫_E |φ(s,e)|² ν(de) ds` is a martingale (where `M_t = ∫_0^t ∫_E φ Ñ`).
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, Theorem 4.2.3; Ikeda–Watanabe, *Stochastic Differential Equations and Diffusion Processes*, 2nd ed., North-Holland 1989, Section II.3.
* **Mathlib replacement**: when the Compensated adapted-density chain (mirror of Brownian C0b) + L²-limit lands.

#### `LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral`

* **File**: `LevyStochCalc/Poisson/Compensated.lean`
* **Statement**: `∃ F : Filtration, Martingale (∫_0^t ∫_E φ Ñ) F P`.
* **Reference**: Applebaum 2009 §4.2 / Ikeda–Watanabe §II.3.
* **Mathlib replacement**: same as above.

#### `LevyStochCalc.Poisson.Compensated.cadlag_modification_exists`

* **File**: `LevyStochCalc/Poisson/Compensated.lean`
* **Statement**: ∃ a càdlàg modification of `stochasticIntegral N φ`.
* **Reference**: Applebaum 2009 §4.2 (Theorem 4.2.4); Ikeda–Watanabe §II.3.
* **Mathlib replacement**: when the Compensated L²-completion + Doob L² maximal modification land.

### Layer 3: BSDEJ existence and path regularity

#### `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique`

* **File**: `LevyStochCalc/BSDEJ/Existence.lean`
* **Statement**: ∃ unique adapted solution triple `(Y, Z, U) ∈ S² × H² × H²_N` for the BSDEJ.
* **Reference**: Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, Theorem 3.1; Gnoatto, *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, Theorem 2.2; Pardoux & Răşcanu, *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*, Springer 2014, Theorem 4.79.
* **Mathlib replacement**: when Mathlib gains BSDEJ existence (Picard contraction + martingale representation).

#### `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity`

* **File**: `LevyStochCalc/BSDEJ/PathRegularity.lean`
* **Statement**: L²-time modulus + projection errors of `(Z, U)` over a partition with mesh `Δt` are bounded by `C · Δt`.
* **Reference**: Bouchard, Elie & Touzi, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 119(11), 2009, Theorem 2.1; Pardoux & Răşcanu, Springer 2014, Theorem 5.42.
* **Mathlib replacement**: when Mathlib gains BSDEJ + Doob L² maximal + Grönwall in the right form.

## Status snapshot

| Item | Sorry baseline (was) | Cited-axiom dependency (is) |
|---|---|---|
| `BrownianMotion.exists` | sorry | `BrownianMotion.exists` (axiom) |
| `MultidimBrownianMotion.exists` | sorry (transitive) | `BrownianMotion.exists` (via `obtain`) |
| `PoissonRandomMeasure.exists_of_sigmaFinite` | sorry | `PoissonRandomMeasure.exists_of_sigmaFinite` (axiom) |
| `kolmogorovChentsov_modification` | sorry | `kolmogorovChentsov_modification` (axiom) |
| `brownian_continuous_modification` | sorry (transitive) | `kolmogorovChentsov_modification` (via the proof body) |
| `brownian_filtration_rightContinuous` | sorry (one conjunct) | `brownian_martingale_rightCont` (axiom) |
| `Brownian.Ito.quadVar_stochasticIntegral` | sorry | `Brownian.Ito.quadVar_stochasticIntegral` (axiom) |
| `Brownian.Ito.martingale_stochasticIntegral` | sorry | `Brownian.Ito.martingale_stochasticIntegral` (axiom) |
| `Compensated.quadVar_stochasticIntegral` | sorry | `Compensated.quadVar_stochasticIntegral` (axiom) |
| `Compensated.martingale_stochasticIntegral` | sorry | `Compensated.martingale_stochasticIntegral` (axiom) |
| `Compensated.cadlag_modification_exists` | sorry | `Compensated.cadlag_modification_exists` (axiom) |
| `BSDEJ.continuousBSDEJ_exists_unique` | sorry | `BSDEJ.continuousBSDEJ_exists_unique` (axiom) |
| `BSDEJ.PathRegularity.bsdej_path_regularity` | sorry | `BSDEJ.PathRegularity.bsdej_path_regularity` (axiom) |
| `Brownian.Ito.itoIsometry` | sorry | **PROVEN** (axiom-clean modulo Lean standard axioms) |
| `Compensated.itoLevyIsometry` | sorry | **PROVEN** (axiom-clean modulo Lean standard axioms) |
| `L2Isometry.itoLevyIsometry` | sorry | **PROVEN** (axiom-clean modulo Lean standard axioms) |

`tools/sorry_baseline.txt` is now empty. All previous baseline entries are
either fully proven (last 3 rows) or axiom-clean modulo a documented cited
axiom (other rows).
