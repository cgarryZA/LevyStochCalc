/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoFormulaGrid
import LevyStochCalc.Brownian.ItoRiemannIntegrand

/-!
# Grid Riemann sums of the Itô integral

The weighted sum of the Itô integral's increments across a uniform grid is itself an Itô
integral — that of the grid's step weight against the integrand — and replacing the step weight
by a general one costs the `L²` distance between them times the bound on the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae` — the grid-weighted sum of increments as
  an Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section GridSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in
/-- **The grid-weighted sum of the Itô integral's increments is an Itô integral.** For
coefficients `ξ i` measurable at the left endpoint of cell `i` of the uniform grid,

  `∑ᵢ ξᵢ · (M_{tᵢ₊₁} − M_{tᵢ}) = ∫_0^T G_m(s)·H_s dW_s`

almost surely, where `G_m` is the step process with value `ξ i` on `(tᵢ, tᵢ₊₁]`. -/
theorem sum_unifGrid_mul_sub_ae {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    (fun ω => ∑ i : Fin m, ξ i ω
        * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m ((i : ℕ) + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i : ℕ)) ω))
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).eval s ω * H ω s)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).measurable_uncurry_eval_mul hm)
        ((SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).progressivelyMeasurable_eval_mul ℱ
          (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) hp)
        (fun T' hT' =>
          (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).lintegral_eval_mul_sq_lt_top
            hq T' hT') T := by
  have hlast : (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition
      (Fin.last (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).N) ≤ T :=
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas).partition_le_T
  exact sum_xi_mul_stochasticIntegral_sub_ae W ℱ hℱ
    (SimplePredictable.ofUnifGrid hT hm0 ξ hbdd hmeas)
    (SimplePredictable.ofUnifGrid_adapt ℱ hT hm0 ξ hbdd hmeas hadapt) H hm hp hq _ _ _ hT hlast

end GridSum

end LevyStochCalc.Brownian.Ito
