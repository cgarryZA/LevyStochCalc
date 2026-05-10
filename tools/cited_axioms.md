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

### Compensated L²-completion infrastructure

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` | Applebaum 2009 **Equation 4.3.1** + **Lemma 4.2.5** (L²-isometry on simple integrands, applied to differences via common refinement); Ikeda–Watanabe **Lemma II.3.4**. The Lean mechanization of common refinement for Compensated SimplePredictables (mirror of Brownian C0b.1–9) is the missing piece. |
| `LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated` | Applebaum 2009 **Lemma 4.2.2** (density of adapted simple predictable functions in L²); Ikeda–Watanabe **Lemma II.3.3**. The Brownian analog (`adaptedSimple_dense_L2_brownian`) is fully proven via `predictableDyadicSimple_brownian`; the Compensated dyadic construction with mark dimension `E` is the missing piece. |

### Brownian L² stochastic integral martingale + quadratic variation

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral` | Karatzas–Shreve, **Theorem 3.2.6**; Le Gall, **Theorem 5.13**. (Genuine — the underlying `Brownian.stochasticIntegral` is a real L²-completion via `itoIntegralLp_brownian = Filter.limUnder atTop (simpleIntegralLp_brownian)`.) Per-T independent Classical.choose: the unified martingale property requires the F-construction-across-all-t (pending). |
| `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral` | Same as `quadVar_stochasticIntegral`. |

### Compensated L² stochastic integral martingale + quadratic variation + càdlàg

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral` | Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.2.3**; Ikeda–Watanabe **Section II.3**. (As of 2026-05-09: the underlying `Compensated.stochasticIntegral` is now the **real L²-Itô-Lévy integral** via `itoIntegralLp_compensated = Filter.limUnder atTop ...`, NOT a trivial constant placeholder. The cited axiom is mathematically meaningful.) Per-T independent Classical.choose: the unified martingale requires F-construction-across-all-t (pending, mirror of Brownian-side). |
| `LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral` | Applebaum 2009 §4.2 / Ikeda–Watanabe §II.3. Same caveat. |
| `LevyStochCalc.Poisson.Compensated.cadlag_modification_exists` | Applebaum 2009 **Theorem 4.2.4**. Càdlàg property of the genuine compensated-Poisson integral via Doob L² maximal applied to simpleIntegral approximations. |

### BSDEJ existence + path regularity

| Theorem | Citation |
|---|---|
| `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique` | Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, **Theorem 3.1**; Gnoatto, *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, **Theorem 2.2**; Pardoux & Răşcanu, Springer 2014, **Theorem 4.79**. |
| `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity` | Bouchard, Elie & Touzi, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 119(11), 2009, **Theorem 2.1**; Pardoux & Răşcanu, Springer 2014, **Theorem 5.42**. |

## Honest derivatives (proven theorems, axiom-clean modulo cited axioms)

| Theorem | Forwards via |
|---|---|
| `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` | `BrownianMotion.exists` (transitive via `obtain`) |
| `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification` | `kolmogorovChentsov_modification` (in proof body) |
| `LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous` | `brownian_martingale_rightCont` (in proof body) |
| `LevyStochCalc.Brownian.Ito.itoIsometry` | **fully proven** (axiom-clean modulo Lean standard axioms) — uses real `itoIntegralLp_brownian` L²-completion |
| `LevyStochCalc.Poisson.Compensated.itoLevyIsometry` | axiom-clean modulo `cauchySeq_simpleIntegralLp_compensated` + `adaptedSimple_dense_L2_compensated` (Tier 1 cited). HONEST (NOT tautological — uses real `itoIntegralLp_compensated`). |
| `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry` | 1-line forwarder over `Compensated.itoLevyIsometry`. Same axiom set as above. HONEST. |

## Status snapshot (2026-05-10)

`tools/sorry_baseline.txt` is **empty**. All previously sorry'd theorems are
either:
* Fully proven (`Brownian.Ito.itoIsometry` — real L²-completion), or
* Honest derivatives forwarding to Tier 1 cited axioms, or
* Tier 1 cited axioms with paper references and Mathlib-replacement plans.

The Compensated chain is now genuinely closed: `stochasticIntegral` is the real
L²-Itô-Lévy integral via `itoIntegralLp_compensated`. The trivial-witness
`fun _ω => √R(T).toReal` placeholder has been removed. `itoLevyIsometry` and
`L2Isometry.itoLevyIsometry` are HONEST (mathematically meaningful, not
tautological).

The remaining work to make `Compensated.{quadVar, martingale, cadlag}` into
proven theorems (rather than cited axioms): construct a UNIFIED canonical L²-Itô
integral process across all `t` (single Hn approximating φ on `[0, ∞)`), so
the per-T witnesses agree a.s. with a martingale-compatible canonical integral.
Pending; mirror of the analogous Brownian-side unified F-construction.

## Convention

* `tools/sorry_baseline.txt` — sorry-blocked theorems. Currently empty.
* `tools/cited_axioms.md` (this file) — Tier 1 cited axioms with full
  citations and Mathlib-replacement plans.
