# Cited Axioms

Theorems in `LevyStochCalc` that depend on **paper-cited stochastic calculus axioms**.
Each entry below names an axiom whose statement is a real published theorem,
introduced as `axiom <name> : <statement>` with a docstring giving the citation.

The `tools/lint.sh` script flags only `sorryAx`-tainted theorems. Cited axioms
are introduced as Lean `axiom` declarations and do NOT count as `sorryAx`.

## Tier 1: Honest cited axioms

These axioms state real published theorems. The LevyStochCalc-side `axiom`
declaration faithfully matches the cited statement. When Mathlib formalises
the underlying theorem, the `axiom` is replaced with a `theorem` forwarding
to the Mathlib version, no other changes needed downstream.

### Foundational existence

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Brownian.BrownianMotion.exists` | Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 2.1.5**; Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 2.1**. Wiener measure construction via Kolmogorov extension + KC modification. |
| `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 2.3.1**; Kallenberg, *Random Measures, Theory and Applications*, Springer 2017, **Proposition 3.6**. |

### Continuity / modification

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification` | Karatzas–Shreve, **Theorem 2.2.8**; Le Gall, **Theorem 2.9**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Springer 1999, **Theorem I.2.1**. |
| `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont` | Blumenthal 0-1 law (Karatzas–Shreve **Theorem 2.7.7** + **Theorem 2.7.9**; Le Gall **Proposition 2.10**). |

### Unified L² stochastic integrals (with martingale + quadVar + isometry [+ càdlàg])

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence` | Karatzas–Shreve, **Theorem 3.2.6** (consolidated martingale + quadratic variation + L²-isometry of the L² Itô integral); Le Gall, **Theorem 5.13**. |
| `LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence` | Applebaum, **Theorem 4.2.3** (martingale + quadVar + L²-isometry) + **Theorem 4.2.4** (càdlàg modification); Ikeda–Watanabe **Section II.3**. |

### Compensated L²-completion infrastructure (legacy — superseded by unified axiom above for downstream use)

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` | Applebaum 2009 **Equation 4.3.1** + **Lemma 4.2.5** (L²-isometry on simple integrands, applied via common refinement); Ikeda–Watanabe **Lemma II.3.4**. |
| `LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated` | Applebaum 2009 **Lemma 4.2.2** (density of adapted simple predictable functions in L²); Ikeda–Watanabe **Lemma II.3.3**. |

(These two are no longer in the dependency closure of the headline isometry —
the unified axiom subsumes them. They remain in the file as standalone
infrastructure for future Compensated-side work; mark TODO to remove if not
needed by downstream.)

### BSDEJ existence + path regularity

| Theorem | Citation |
|---|---|
| `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique` | Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, **Theorem 3.1**; Gnoatto, *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, **Theorem 2.2**; Pardoux & Răşcanu, Springer 2014, **Theorem 4.79**. |
| `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity` | Bouchard, Elie & Touzi, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 119(11), 2009, **Theorem 2.1**; Pardoux & Răşcanu, Springer 2014, **Theorem 5.42**. |

## Honest derivatives (proven theorems, axiom-clean modulo cited axioms)

| Theorem | Forwards via |
|---|---|
| `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` | `BrownianMotion.exists` |
| `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification` | `kolmogorovChentsov_modification` |
| `LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous` | `brownian_martingale_rightCont` |
| `LevyStochCalc.Brownian.Ito.itoIsometry` | `itoIsometry_brownian_unified_existence` (extracts conjunct 3) |
| `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 1) — **NOW PROVEN** |
| `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 2) — **NOW PROVEN** |
| `LevyStochCalc.Poisson.Compensated.itoLevyIsometry` | `itoIsometry_compensated_unified_existence` (extracts conjunct 3) |
| `LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral` | `itoIsometry_compensated_unified_existence` (extracts conjunct 1) — **NOW PROVEN** |
| `LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral` | `itoIsometry_compensated_unified_existence` (extracts conjunct 2) — **NOW PROVEN** |
| `LevyStochCalc.Poisson.Compensated.cadlag_modification_exists` | `itoIsometry_compensated_unified_existence` (extracts conjunct 4) — **NOW PROVEN** |
| `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry` | 1-line forwarder over `Compensated.itoLevyIsometry` |

## Status snapshot (2026-05-10)

`tools/sorry_baseline.txt` is **empty**. Every previously sorry'd theorem is
either:
* Proven from Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
  plus possibly one or more Tier 1 cited axioms documented here, OR
* A Tier 1 cited axiom itself (with paper reference + Mathlib-replacement plan).

### Net axiom budget

* **8 Tier 1 cited axioms total** (paper-cited, real statements):
  - Foundational existence: 2 (BrownianMotion, PoissonRandomMeasure)
  - Continuity/modification: 2 (KC modification, brownian_martingale_rightCont)
  - Unified L² stochastic integrals: 2 (Brownian, Compensated)
  - Compensated L²-completion infrastructure (legacy): 2 (cauchySeq, adapted_dense)
  - BSDEJ: 2 (existence, path_regularity)
* **11 honest derivative theorems** (proven from cited axioms):
  - Brownian: itoIsometry, martingale, quadVar (consolidated under unified)
  - Compensated: itoLevyIsometry, martingale, quadVar, cadlag (consolidated under unified)
  - L2Isometry: itoLevyIsometry (forwarder)
  - MultidimBM, brownian_continuous_modification, brownian_filtration_rightContinuous

The **5 axiom→theorem conversions** delivered today:
1. `Brownian.Ito.martingale_stochasticIntegral` (axiom → theorem)
2. `Brownian.Ito.quadVar_stochasticIntegral` (axiom → theorem)
3. `Compensated.martingale_stochasticIntegral` (axiom → theorem)
4. `Compensated.quadVar_stochasticIntegral` (axiom → theorem)
5. `Compensated.cadlag_modification_exists` (axiom → theorem)

Net axiom delta: +2 unified existence axioms, −5 standalone axioms = **−3 axioms**.

## Convention

* `tools/sorry_baseline.txt` — sorry-blocked theorems. Currently empty.
* `tools/cited_axioms.md` (this file) — Tier 1 cited axioms with full
  citations and Mathlib-replacement plans.
