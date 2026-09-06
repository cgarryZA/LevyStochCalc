/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.Definition
import LevyStochCalc.Driver.CadlagMartingale
import LevyStochCalc.Brownian.MultidimIto

/-!
# Martingale representation for `(W, Ñ)`: the conditional-expectation bridge

Every square-integrable random variable `ξ` measurable for the joint right-continuous
filtration of a Brownian motion `W` and a Poisson random measure `N` is the terminal value of a
càdlàg square-integrable martingale on that filtration starting from `𝔼 ξ`
(`condExp_to_PRP_martingale_form`, formerly cited result #13b: Doob's càdlàg regularisation,
Karatzas–Shreve I.3.13, and Blumenthal's 0-1 law for the joint filtration). The martingale is
`LevyDriver.cadlagCondExp`, built in `Driver/CadlagMartingale.lean`.

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

/-- The right-continuous joint filtration of a Lévy driver `D = (W, N)`, i.e. `ℱ₊`
for `ℱ = (⨆ i, ℱ^{Wⁱ}) ⊔ ℱ^N`. Every coordinate of `D.W` is a Brownian motion for
it and `D.N` a Poisson random measure (`LevyDriver.isBrownianFiltration`,
`.isPoissonFiltration`, lifted by `.rightCont`), and `D` carries the independence
`σ(W) ⟂ σ(N)` that the `M₀ = 𝔼 ξ` clause below needs. -/
noncomputable abbrev jointFiltration
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {d : ℕ}
    (D : LevyStochCalc.Driver.LevyDriver P d ν) :
    MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω› :=
  D.filtration.rightCont

end PRP

section Representation
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Every square-integrable random variable measurable for the joint right-continuous filtration
of a Lévy driver at time `T` is the terminal value of a càdlàg square-integrable martingale for
that filtration whose value at time `0` is its mean. -/
theorem condExp_to_PRP_martingale_form
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {d : ℕ}
    (D : LevyStochCalc.Driver.LevyDriver P d ν)
    (T : ℝ) (_hT : 0 < T)
    (ξ : Ω → ℝ)
    (h_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((jointFiltration D).seq T) ξ)
    (h_sq_int : ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
    ∃ (M : ℝ → Ω → ℝ),
      MeasureTheory.Martingale M (jointFiltration D) P
      ∧ (∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤)
      ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
          Filter.Tendsto (fun s => M s ω)
            (nhdsWithin t (Set.Ioi t)) (nhds (M t ω))
            ∧ ∃ L : ℝ,
                Filter.Tendsto (fun s => M s ω)
                  (nhdsWithin t (Set.Iio t)) (nhds L))
      ∧ (∀ᵐ ω ∂P, M 0 ω = (∫ ω', ξ ω' ∂P))
      ∧ (∀ᵐ ω ∂P, M T ω = ξ ω) := by
  have hSM : MeasureTheory.StronglyMeasurable ξ :=
    h_meas.mono ((jointFiltration D).le T)
  have hξ : MeasureTheory.MemLp ξ 2 P := by
    refine ⟨hSM.aestronglyMeasurable, ?_⟩
    have heq : ∀ ω, ‖ξ ω‖ₑ ^ ENNReal.toReal 2 = (‖ξ ω‖₊ : ℝ≥0∞) ^ (2 : ℕ) := fun ω => by
      rw [show ENNReal.toReal 2 = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    simp_rw [heq]
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt h_sq_int)
  have hterm := LevyStochCalc.Driver.LevyDriver.cadlagCondExp_terminal_ae_eq
    (D := D) (ξ := ξ) hξ hSM h_meas
  refine ⟨D.cadlagCondExp ξ,
    LevyStochCalc.Driver.LevyDriver.martingale_cadlagCondExp (D := D) (ξ := ξ) hξ hSM,
    ?_, ?_, LevyStochCalc.Driver.LevyDriver.cadlagCondExp_zero_ae_eq (D := D) (ξ := ξ) hξ hSM,
    hterm⟩
  · rw [MeasureTheory.lintegral_congr_ae (hterm.mono fun ω h => by rw [h])]
    exact h_sq_int
  · filter_upwards [LevyStochCalc.Driver.LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT
      (D := D) (ξ := ξ)] with ω hω t
    exact ⟨LevyStochCalc.Driver.LevyDriver.tendsto_cadlagCondExp_nhdsGT
      (D := D) (ξ := ξ) t ω, hω t⟩

end Representation

end LevyStochCalc.BSDEJ.MartingaleRepresentation
