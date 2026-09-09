/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointRange
import LevyStochCalc.Driver.JointComplement
import LevyStochCalc.Brownian.PRPPerpBridge

/-!
# The predictable representation property of a Lévy driver

Over the augmented joint filtration, a square-integrable weight of mean zero that is measurable
before the horizon is the sum of Itô integrals against the Brownian coordinates and a compensated
integral against the Poisson random measure: the joint range is closed, the orthogonal remainder
is a weight of the same kind orthogonal to both ranges, and such a weight vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

/-- **The predictable representation property of a Lévy driver.** -/
theorem exists_jointIntegral_augFiltration [Nonempty E] (D : LevyDriver.{u, v, w} P d ν)
    (hd : 0 < d) {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  refine exists_jointIntegral_of_mean_zero (fun k => D.isBrownianFiltration_aug k)
    D.isPoissonFiltration_aug (fun k => (D.coordCrossWitness k).aug)
    (LevyDriver.crossWitness D).aug hT ?_ hZ2 hZm hZ0
  intro r hr2 hrm hr0 hrB hrN
  have hperp : ∀ i : Fin d, PerpItoIntegrals (D.W.W i) (Brownian.augFiltration D.filtration P)
      (D.isBrownianFiltration_aug i) fun ω => ((r ω : ℝ) : ℂ) := by
    intro i
    refine ⟨fun K hm hp hq t ht => ?_⟩
    have hreal := integral_mul_stochasticIntegral_eq_zero (D.W.W i)
      (D.isBrownianFiltration_aug i) hT hr2 hrm (hrB i) K hm hp hq ht
    have hcast : (fun ω => ((r ω : ℝ) : ℂ) * ((stochasticIntegralBrownian (D.W.W i)
          (Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ))
        = fun ω => ((r ω * stochasticIntegralBrownian (D.W.W i)
          (Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ) := by
      funext ω
      rw [Complex.ofReal_mul]
    rw [hcast, integral_complex_ofReal, hreal, Complex.ofReal_zero]
  exact ae_eq_zero_of_perp_joint D hd hT hr2 hrm hperp hrN hr0

end LevyDriver

end LevyStochCalc.Driver
