/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CrossSimple
import LevyStochCalc.Poisson.CompensatedProcess
import LevyStochCalc.Poisson.Compensated

/-!
# The Brownian and compensated ranges are orthogonal

Both integrals are `L²` limits of elementary ones — the Brownian integral of the master
approximants, the compensated integral of the mark-step stages — and the elementary pairings all
vanish, so the pairing of the limits vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **Orthogonality of a Brownian Itô integral and a compensated integral.** -/
theorem integral_stochasticIntegral_mul_compensated_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d}
    (hℱW : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : Ω → ℝ → E → ℝ} (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs t ω
      * Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs t ω ∂P = 0 := by
  have hu : MemLp (Brownian.Ito.stochasticIntegral (D.W.W i) ℱ (hℱW i) H hHm hHp hHs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (Brownian.Ito.stochasticIntegralBrownian_ae_eq (D.W.W i)
      ℱ (hℱW i) H hHm hHp hHs t).symm
  have hv : MemLp (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs t) 2 P :=
    (Poisson.Compensated.process_memLp D.N ℱ hℱN φ hφm hφp hφs t).ae_eq
      (Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN φ hφm hφp hφs t).symm
  have hcv : Tendsto (fun n => eLpNorm (fun ω =>
      Poisson.Compensated.stageIntegral D.N ℱ hℱN φ hφm hφp hφs n t ω
        - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs t ω) 2 P)
      atTop (nhds 0) := by
    refine Tendsto.congr (fun n => ?_)
      (Poisson.Compensated.stageIntegral_tendsto_process D.N ℱ hℱN φ hφm hφp hφs t)
    refine eLpNorm_congr_ae ?_
    filter_upwards [Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN φ hφm hφp
      hφs t] with ω hω
    rw [hω]
  exact Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm
    (un := fun n ω => Brownian.Ito.simpleIntegral (D.W.W i)
      (Brownian.Ito.masterApprox ℱ H hHm hHp hHs n) t ω)
    (vn := fun n ω => Poisson.Compensated.stageIntegral D.N ℱ hℱN φ hφm hφp hφs n t ω)
    hu hv (fun _ => Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral _ _ t)
    (fun n => Poisson.Compensated.memLp_stageIntegral D.N ℱ hℱN φ hφm hφp hφs n t)
    (fun n => integral_simpleIntegral_mul_markStep_eq_zero 𝒲
      (Brownian.Ito.masterApprox ℱ H hHm hHp hHs n)
      (Brownian.Ito.masterApprox_adapt ℱ H hHm hHp hHs n)
      (Poisson.Compensated.master D.N ℱ hℱN φ hφm hφp hφs n).2
      (Poisson.Compensated.master_adapted D.N ℱ hℱN φ hφm hφp hφs n) t t)
    (Brownian.Ito.masterApprox_tendsto_L2 (D.W.W i) ℱ (hℱW i) H hHm hHp hHs ht) hcv

end LevyDriver

end LevyStochCalc.Driver
