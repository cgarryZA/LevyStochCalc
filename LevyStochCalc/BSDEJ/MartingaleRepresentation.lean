/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.Definition
import LevyStochCalc.Brownian.MultidimIto

/-!
# Martingale representation for `(W, Ñ)`: the conditional-expectation bridge

Every square-integrable random variable `ξ` measurable for the joint right-continuous
filtration of a Brownian motion `W` and a Poisson random measure `N` is the terminal value of a
càdlàg square-integrable martingale on that filtration starting from `𝔼 ξ`
(`condExp_to_PRP_martingale_form_axiom`, cited result #13b: Doob's càdlàg regularisation,
Karatzas–Shreve I.3.13, and the 0-1 law for the joint filtration).

The predictable representation property itself (Jacod 1975; Jacod–Shiryaev III.4.34) is not
stated here. Its previous formulation `jacodYor_PRP_martingale_axiom` (#13a) asked for
representing integrands adapted to the natural filtration of a single driver — the class the
`L²` integrals of this library are built on — while the martingale was one of the joint
filtration; the martingale `W_t · Ñ_t` is not representable in that class, so the statement was
refutable and was retired on 2026-09-06 together with the derived `jacodYor_representation`.
The property will be restated once the integrals are built over a common filtration
(`Plan.md`, work package X2).

## Source

* Jacod, J. "Multivariate point processes: predictable projection,
  Radon-Nikodym derivatives, representation of martingales",
  Z. Wahrsch. Verw. Gebiete 31(3), 1975, pp 235–253.
* Jacod–Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed.,
  Springer 2003, Theorem III.4.34.
* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, Theorem I.3.13.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.MartingaleRepresentation

universe u v

section PRP
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Abbreviation for the joint right-continuous (W, N) filtration appearing
in every statement below. Locally bound to keep statements legible. -/
noncomputable abbrev jointFiltration
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) :
    MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω› :=
  ((⨆ i : Fin d, LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i))
    ⊔ LevyStochCalc.Poisson.naturalFiltration N).rightCont

end PRP

section Representation
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Conditional-expectation martingale càdlàg modification + endpoint
identification — Tier 1 cited axiom #13b.**

For every L² random variable `ξ : Ω → ℝ` that is `ℱ_T`-measurable on the
joint right-continuous (W, N) filtration, there exists a càdlàg
L²-bounded `ℱ`-martingale `M` with `M_0 = ∫ ξ ∂P` a.s. (i.e. `M_0` is
the deterministic expectation, NOT just `E[ξ | ℱ_0]`) and `M_T = ξ`
a.s.

This packages THREE standard classical results:

1. **Doob L² càdlàg regularization** (Karatzas-Shreve, *Brownian Motion
   and Stochastic Calculus*, Springer 1991, **Theorem I.3.13**): for a
   right-continuous filtration, every L¹ martingale admits a càdlàg
   modification.
2. **Blumenthal 0-1 law for the joint (W, N) filtration** (Karatzas-
   Shreve **Theorem 2.7.17** for the Brownian factor; analog for
   Poisson random measures via Itô-Nisio / Applebaum 2.3.7): the right-
   continuous augmentation `ℱ_0+` is P-trivial, hence
   `𝔼[ξ | ℱ_0] = ∫ ξ ∂P` a.s.
3. **Conditional-expectation reproducibility** (Mathlib's
   `MeasureTheory.condExp_of_stronglyMeasurable`): `𝔼[ξ | ℱ_T] = ξ`
   a.s. when ξ is ℱ_T-measurable and integrable.

The bundle is strictly narrower than the former `jacodYor_representation_axiom` (retired
2026-09-06):
no chaos decomposition / predictable projection is required, only
classical martingale + filtration machinery. Each of items 1, 2, 3
above has independent Mathlib activity (Doob regularization is on the
roadmap, Blumenthal-for-BM gets axiom-replaced when BM lands, condExp
is already there). When all three are usable in Mathlib, this axiom
collapses to a 3-line composite.

**Reference**: Karatzas-Shreve **Theorem I.3.13** (Doob L² càdlàg
regularization); Karatzas-Shreve **Theorem 2.7.17** (Blumenthal 0-1
for Brownian); Mathlib's `MeasureTheory.condExp_of_stronglyMeasurable`
(condExp reproducibility — not citable, library lemma). -/
axiom condExp_to_PRP_martingale_form_axiom
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (T : ℝ) (_hT : 0 < T)
    (ξ : Ω → ℝ)
    (_h_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((jointFiltration W N).seq T) ξ)
    (_h_sq_int : ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
    ∃ (M : ℝ → Ω → ℝ),
      MeasureTheory.Martingale M (jointFiltration W N) P
      ∧ (∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤)
      ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
          Filter.Tendsto (fun s => M s ω)
            (nhdsWithin t (Set.Ioi t)) (nhds (M t ω))
            ∧ ∃ L : ℝ,
                Filter.Tendsto (fun s => M s ω)
                  (nhdsWithin t (Set.Iio t)) (nhds L))
      ∧ (∀ᵐ ω ∂P, M 0 ω = (∫ ω', ξ ω' ∂P))
      ∧ (∀ᵐ ω ∂P, M T ω = ξ ω)

end Representation

end LevyStochCalc.BSDEJ.MartingaleRepresentation
