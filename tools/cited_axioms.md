# Cited Axioms

Theorems in `LevyStochCalc` that depend on **paper-cited stochastic calculus axioms**
or on **placeholder definitions** awaiting a real construction.

The `tools/lint.sh` script flags only `sorryAx`-tainted theorems. Cited axioms
are introduced as Lean `axiom` declarations and do NOT count as `sorryAx`. This
makes the dependency on external math VISIBLE rather than hidden behind sorryAx.

This file is split into **two tiers** to be honest about what is closed and what
is shell-closed:

* **Tier 1** entries are **honest closures**: the axiom states a real, paper-cited
  theorem; the LevyStochCalc-side `axiom` declaration faithfully matches the
  cited statement. When Mathlib formalises the underlying theorem, the `axiom`
  is replaced with a `theorem` forwarding to the Mathlib version, no other
  changes needed downstream.
* **Tier 2** entries are **placeholder closures**: the LevyStochCalc-side
  definition is a trivial witness (constant-in-ω function or similar); axioms
  about it are either tautologically true under the placeholder OR morally
  false but unprovable to-the-contrary in Lean given the spec's existential
  shape. These are NOT real closures. They are gated on replacing the
  placeholder definition with a real construction. Do NOT cite Tier 2 entries
  in publications.

## Tier 1: Honest cited axioms

| Theorem | Citation |
|---|---|
| `LevyStochCalc.Brownian.BrownianMotion.exists` | Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 2.1.5**; Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 2.1**. Wiener measure construction via Kolmogorov extension + KC modification. |
| `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 2.3.1**; Kallenberg, *Random Measures, Theory and Applications*, Springer 2017, **Proposition 3.6**. |
| `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification` | Karatzas–Shreve, **Theorem 2.2.8**; Le Gall, **Theorem 2.9**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Springer 1999, **Theorem I.2.1**. |
| `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont` | Blumenthal 0-1 law (Karatzas–Shreve **Theorem 2.7.7** + **Theorem 2.7.9**; Le Gall **Proposition 2.10**). |
| `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral` | Karatzas–Shreve, **Theorem 3.2.6**; Le Gall, **Theorem 5.13**. (Genuine — the underlying `stochasticIntegral_brownian` is a real L²-completion via `itoIntegralLp_brownian = Filter.limUnder atTop (simpleIntegralLp_brownian)`.) |
| `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral` | Karatzas–Shreve, **Theorem 3.2.6**; Le Gall, **Theorem 5.13**. |
| `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique` | Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, **Theorem 3.1**; Gnoatto, *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, **Theorem 2.2**; Pardoux & Răşcanu, Springer 2014, **Theorem 4.79**. |
| `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity` | Bouchard, Elie & Touzi, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 119(11), 2009, **Theorem 2.1**; Pardoux & Răşcanu, Springer 2014, **Theorem 5.42**. |

**Honest derivatives** (proven theorems whose proofs forward to a Tier 1 axiom):

| Theorem | Forwards via |
|---|---|
| `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` | `BrownianMotion.exists` (transitive via `obtain`) |
| `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification` | `kolmogorovChentsov_modification` (in proof body) |
| `LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous` | `brownian_martingale_rightCont` (in proof body) |
| `LevyStochCalc.Brownian.Ito.itoIsometry` | **fully proven** (axiom-clean modulo Lean standard axioms) — uses real `itoIntegralLp_brownian` L²-completion |

## Tier 2: Placeholder closures (NOT yet honest — gated on real construction)

The Compensated chain currently uses a **trivial-witness placeholder** for
`Compensated.stochasticIntegral`:

```lean
noncomputable def stochasticIntegral
    (_N : PoissonRandomMeasure P ν) (φ : Ω → ℝ → E → ℝ) (T : ℝ) : Ω → ℝ :=
  fun _ω => Real.sqrt
    ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal)
```

This is a **deterministic constant in ω**, not a real Itô-Lévy integral.
Consequences:

| Theorem | Status under placeholder |
|---|---|
| `Compensated.itoLevyIsometry` | **TAUTOLOGY** — `M = √∫⁻∫⁻∫⁻‖φ‖²` makes `E[M²] = ∫⁻∫⁻∫⁻‖φ‖²` hold by construction. Provides no probabilistic content. |
| `L2Isometry.itoLevyIsometry` | **1-line forwarder over the tautology** — same issue. |
| `Compensated.quadVar_stochasticIntegral` | **MORALLY FALSE under placeholder** — axiom asserts `∃ F, Martingale (M² − ∫₀^t ∫_E φ²) F P` but the trivial-witness `M` (deterministic in ω, monotone in T, square root of a cumulative integral) yields a process that is generically not a martingale w.r.t. any filtration. Asserting it as an axiom introduces in-principle inconsistency at the LevyStochCalc level (though no dissertation theorem currently uses it). |
| `Compensated.martingale_stochasticIntegral` | **MORALLY FALSE under placeholder** — same failure mode. |
| `Compensated.cadlag_modification_exists` | **VACUOUSLY TRIVIAL under placeholder** — a deterministic continuous function of t is càdlàg trivially; provides no content. |

### Required punch list to make Tier 2 → Tier 1

1. **Replace `Compensated.stochasticIntegral`** with the real L²-completion:
   define `simpleIntegralLp_compensated` (mirror of Brownian's `simpleIntegralLp_brownian`),
   show L²-Cauchy of `simpleIntegralLp_compensated (G n)` for adapted Cauchy sequences,
   define `itoIntegralLp_compensated = Filter.limUnder atTop (...)`,
   refactor `stochasticIntegral` to take `Classical.choose` of an existence statement using `itoIntegralLp_compensated`.

2. **Re-prove `Compensated.itoLevyIsometry` honestly** by passing the simple-level
   isometry through `Filter.limUnder` (mirror `Brownian.itoIsometry`).

3. **Convert axioms 3, 4, 5 (quadVar, martingale, cadlag) to theorems** via
   L²-limit-of-martingales + Doob L² maximal arguments at the L²-completion level.

4. **Stage the simple-level quadVar identity** as a NESTED Tier 1 cited axiom
   (Applebaum 2009 Eq 4.3.1 / Ikeda–Watanabe Eq II.3.5) if the orthogonal-increments
   computation is not landed within the time budget — the L²-limit step is the
   structural piece for which infrastructure already exists.

5. **`L2Isometry.itoLevyIsometry`** auto-becomes real once `Compensated.itoLevyIsometry`
   does (1-line forwarder).

After items 1–5 land, Tier 2 is empty and the closure count is genuinely 16/16.

## Convention

* `tools/sorry_baseline.txt` — sorry-blocked theorems. Currently empty.
* `tools/cited_axioms.md` (this file) — Tier 1 (honest) + Tier 2 (placeholder).
  When Tier 2 items are reduced to Tier 1 (or fully proven), update this file.
