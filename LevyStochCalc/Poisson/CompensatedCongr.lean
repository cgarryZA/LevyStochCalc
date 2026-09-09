/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Compensated
import LevyStochCalc.Poisson.CompensatedIntegrandComplete
import LevyStochCalc.Poisson.CompensatedLinear

/-!
# The compensated integral depends only on the class of its integrand

Two admissible marked integrands that agree almost everywhere for the product of the sample
measure, Lebesgue measure on the horizon and the mark measure have almost surely equal
compensated integrals: the energy of their difference vanishes, and the difference isometry
turns that into an almost sure identity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The compensated integral depends only on the `P ⊗ ds ⊗ ν`-class of its integrand.** -/
theorem stochasticIntegral_congr_ae (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (φ ψ : Ω → ℝ → E → ℝ)
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hψp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) :
    stochasticIntegral N ℱ hℱ φ hφm hφp hφq T
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T := by
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P = 0 := by
    have hdiff : (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2)
        =ᵐ[markedEnergyMeasure P ν T] fun _ => (0 : ℝ) := by
      filter_upwards [h] with p hp
      rw [hp, sub_self]
    have hE : markedEnergy P ν T (fun ω s e => φ ω s e - ψ ω s e)
        = eLpNorm (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2) 2
          (markedEnergyMeasure P ν T) ^ 2 :=
      markedEnergy_eq_eLpNorm_sq (hφm.sub hψm) T
    have hz : markedEnergy P ν T (fun ω s e => φ ω s e - ψ ω s e) = 0 := by
      rw [hE, eLpNorm_congr_ae hdiff]
      simp
    exact hz
  have hiso := itoIsometry_diff_compensated N ℱ hℱ φ ψ hφm hψm hφp hψp hφq hψq T hT
  rw [hzero] at hiso
  have hL1 : MemLp (stochasticIntegral N ℱ hℱ φ hφm hφp hφq T) 2 P :=
    stochasticIntegral_memLp N ℱ hℱ φ hφm hφp hφq T
  have hL2 : MemLp (stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T) 2 P :=
    stochasticIntegral_memLp N ℱ hℱ ψ hψm hψp hψq T
  have hae : AEMeasurable (fun ω => (‖stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hL1.sub hL2).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω = 0 := by simpa using h2
  linarith

end LevyStochCalc.Poisson.Compensated
