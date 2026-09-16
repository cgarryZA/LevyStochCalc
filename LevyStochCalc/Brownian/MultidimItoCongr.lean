/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Brownian.ItoLocalityStrict

/-!
# The multidimensional Itô integral depends only on the class of its integrand

The multidimensional Itô integral is the sum over the coordinates of the one-dimensional
integrals against the coordinate Brownian motions, and each of those depends only on the
almost-everywhere class of its integrand on the window. Two vector integrands agreeing for almost
every time of a window, at almost every sample point, therefore have almost surely equal
multidimensional integrals at the end of that window.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}
  (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ)
  {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}

/-- Two integrands agreeing almost everywhere on a window have almost surely equal
multidimensional Itô integrals at the end of that window. -/
theorem stochasticIntegral_congr_ae
    (hm₁ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω i))
    (hp₁ : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω i)
    (hq₁ : ∀ i : Fin d, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω i))
    (hp₂ : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω i)
    (hq₂ : ∀ i : Fin d, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T), Z₁ s ω = Z₂ s ω) :
    stochasticIntegral W ℱ hℱ Z₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegral W ℱ hℱ Z₂ hm₂ hp₂ hq₂ T := by
  have hcomp : ∀ i : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱ i)
          (fun ω' s => Z₁ s ω' i) (hm₁ i) (hp₁ i) (hq₁ i) T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱ i)
          (fun ω' s => Z₂ s ω' i) (hm₂ i) (hp₂ i) (hq₂ i) T ω := by
    intro i
    refine LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_ae (W.W i) ℱ (hℱ i)
      (hm₁ i) (hp₁ i) (hq₁ i) (hm₂ i) (hp₂ i) (hq₂ i) hT ?_
    filter_upwards [hae] with ω hω
    filter_upwards [hω] with s hs
    rw [hs]
  filter_upwards [Filter.eventually_all.2 hcomp] with ω hω
  exact Finset.sum_congr rfl fun i _ => hω i

end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim
