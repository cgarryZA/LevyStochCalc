/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.PRPMultidimRange
import LevyStochCalc.Brownian.PRPPerpBridge
import LevyStochCalc.Brownian.PRPBrownian

/-!
# The multidimensional Brownian predictable representation property

Over the augmented joint natural filtration of a multidimensional Brownian motion, every
square-integrable weight of mean zero that is measurable before the horizon is a sum of coordinate
Itô integrals. The range is closed and the coordinate ranges are orthogonal, so the weight splits
into a representable part and a remainder orthogonal to every horizon integral; the perp bridge
turns that orthogonality into orthogonality against every Itô integral at every positive time,
which is what the separation theorem consumes, and the remainder vanishes.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- **The multidimensional Brownian predictable representation property.** -/
theorem exists_vectorIntegral_augFiltration (W : MultidimBrownianMotion P d) {T : ℝ} (hT : 0 < T)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[augFiltration W.naturalFiltration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : ∀ _ : Fin d, HorizonIntegrand P (augFiltration W.naturalFiltration P) T,
      Z =ᵐ[P] vectorIntegral W (isBrownianFiltration_augNatural W) G := by
  refine exists_vectorIntegral_of_mean_zero W (isBrownianFiltration_augNatural W)
    (crossWitnessAugNatural W) hT ?_ hZ2 hZm hZ0
  intro r hr2 hrm hr0 hrperp
  obtain ⟨y, hym, hyae⟩ := hrm
  have hy2 : MemLp y 2 P := hr2.ae_eq hyae
  have hy0 : ∫ ω, y ω ∂P = 0 := by rw [← integral_congr_ae hyae]; exact hr0
  have hyperp : ∀ (i : Fin d) (G : HorizonIntegrand P (augFiltration W.naturalFiltration P) T),
      ∫ ω, y ω * G.integral (W.W i) (isBrownianFiltration_augNatural W i) ω ∂P = 0 := by
    intro i G
    rw [← hrperp i G]
    refine integral_congr_ae ?_
    filter_upwards [hyae] with ω e
    rw [e]
  have hZc2 : MemLp (fun ω => ((y ω : ℂ))) 2 P := by
    refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hy2.1, ?_⟩
    rw [eLpNorm_congr_norm_ae
      (Filter.Eventually.of_forall fun ω => Complex.norm_real (y ω))]
    exact hy2.2
  have hZc0 : ∫ ω, ((y ω : ℂ)) ∂P = 0 := by
    rw [integral_complex_ofReal, hy0, Complex.ofReal_zero]
  have hZcT : StronglyMeasurable[augFiltration W.naturalFiltration P T]
      fun ω => ((y ω : ℂ)) := Complex.continuous_ofReal.comp_stronglyMeasurable hym
  have hperp : ∀ i : Fin d, PerpItoIntegrals (W.W i) (augFiltration W.naturalFiltration P)
      (isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural i))
      fun ω => ((y ω : ℂ)) := by
    intro i
    refine ⟨fun K hm hp hq t ht => ?_⟩
    have hreal := integral_mul_stochasticIntegral_eq_zero (W.W i)
      (isBrownianFiltration_augNatural W i) hT hy2 hym.aestronglyMeasurable (hyperp i)
      K hm hp hq ht
    have hcast : (fun ω => ((y ω : ℂ)) * ((stochasticIntegralBrownian (W.W i)
          (augFiltration W.naturalFiltration P)
          (isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural i))
          K hm hp hq t ω : ℝ) : ℂ))
        = fun ω => ((y ω * stochasticIntegralBrownian (W.W i)
          (augFiltration W.naturalFiltration P)
          (isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural i))
          K hm hp hq t ω : ℝ) : ℂ) := by
      funext ω
      rw [Complex.ofReal_mul]
    rw [hcast, integral_complex_ofReal, hreal, Complex.ofReal_zero]
  have hzero := ae_eq_zero_of_perpItoIntegrals_augFiltration W hZc2 hperp hZc0 hT.le hZcT
  refine hyae.trans ?_
  filter_upwards [hzero] with ω e
  have he : ((y ω : ℂ)) = 0 := e
  exact_mod_cast he

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
