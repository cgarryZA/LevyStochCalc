/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoAlgebra

/-!
# The Itô integral of an indicator is a Brownian increment

The integrand `1_{(a, b]}` is simple, so its `L²` Itô integral up to a time `t` is the elementary
integral `W_{b ∧ t} − W_{a ∧ t}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Indicator

/-- The indicator integrand of a time window, as a process constant in the sample point. -/
noncomputable def indIoc (Ω) [MeasurableSpace Ω] (a b : ℝ) : Ω → ℝ → ℝ :=
  fun _ s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s

theorem indIoc_le_one (a b : ℝ) (ω : Ω) (s : ℝ) : |indIoc Ω a b ω s| ≤ 1 := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

theorem measurable_uncurry_indIoc (a b : ℝ) :
    Measurable (Function.uncurry (indIoc Ω a b)) :=
  ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd)

theorem progressivelyMeasurable_indIoc (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) := by
  have hfun : indIoc Ω a b = fun ω s => (stepIoc Ω ha hab).eval s ω := by
    funext ω s; rw [stepIoc_eval]; rfl
  rw [hfun]
  exact (stepIoc Ω ha hab).progressivelyMeasurable_eval ℱ (stepIoc_adapt ℱ ha hab)

theorem progressivelyMeasurable_indIoc₀ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ}
    (hb : 0 < b) : Probability.ProgressivelyMeasurable ℱ (indIoc Ω 0 b) := by
  have hfun : indIoc Ω 0 b = fun ω s => (stepIoc₀ Ω hb).eval s ω := by
    funext ω s; rw [stepIoc₀_eval]; rfl
  rw [hfun]
  exact (stepIoc₀ Ω hb).progressivelyMeasurable_eval ℱ (stepIoc₀_adapt ℱ hb)

theorem lintegral_sq_indIoc_lt_top (P : Measure Ω) [IsProbabilityMeasure P] (a b : ℝ)
    (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ≤ 1 := by
    intro ω s
    have hx : ‖indIoc Ω a b ω s‖ ≤ 1 := (Real.norm_eq_abs _).le.trans (indIoc_le_one a b ω s)
    have : (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ≤ 1 := by
      rw [← ENNReal.coe_one, ENNReal.coe_le_coe, ← NNReal.coe_le_coe]
      simpa using hx
    simpa using pow_le_pow_left' this 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Icc (0 : ℝ) T, (1 : ℝ≥0∞) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [lintegral_one, Measure.restrict_apply_univ, Real.volume_Icc,
          lintegral_const, measure_univ, mul_one]
        exact ENNReal.ofReal_lt_top

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral of an indicator is a Brownian increment.** -/
theorem stochasticIntegralBrownian_indIoc {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hm : Measurable (Function.uncurry (indIoc Ω a b)))
    (hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b))
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq t
      =ᵐ[P] fun ω => W.W (min b t) ω - W.W (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : indIoc Ω 0 b = fun ω s => (stepIoc₀ Ω hab).eval s ω := by
      funext ω s; rw [stepIoc₀_eval]; rfl
    have hm' : Measurable (Function.uncurry fun ω s => (stepIoc₀ Ω hab).eval s ω) := by
      rw [← hfun]; exact hm
    have hp' : Probability.ProgressivelyMeasurable ℱ fun ω s => (stepIoc₀ Ω hab).eval s ω := by
      rw [← hfun]; exact hp
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc₀ Ω hab).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hq T hT
      rwa [hfun] at this
    have hkey := stochasticIntegralBrownian_eval_simple W ℱ hℱ (stepIoc₀ Ω hab)
      (stepIoc₀_adapt ℱ hab) hm' hp' hq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun.symm hm' hp' hq' hm hp hq t] at hkey
    exact hkey.trans (Filter.Eventually.of_forall fun ω => stepIoc₀_integralAgainst hab W.W t ω)
  · have hfun : indIoc Ω a b = fun ω s => (stepIoc Ω ha' hab).eval s ω := by
      funext ω s; rw [stepIoc_eval]; rfl
    have hm' : Measurable (Function.uncurry fun ω s => (stepIoc Ω ha' hab).eval s ω) := by
      rw [← hfun]; exact hm
    have hp' : Probability.ProgressivelyMeasurable ℱ fun ω s => (stepIoc Ω ha' hab).eval s ω := by
      rw [← hfun]; exact hp
    have hq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc Ω ha' hab).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hq T hT
      rwa [hfun] at this
    have hkey := stochasticIntegralBrownian_eval_simple W ℱ hℱ (stepIoc Ω ha' hab)
      (stepIoc_adapt ℱ ha' hab) hm' hp' hq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun.symm hm' hp' hq' hm hp hq t] at hkey
    exact hkey.trans
      (Filter.Eventually.of_forall fun ω => stepIoc_integralAgainst ha' hab W.W t ω)

end Indicator

end LevyStochCalc.Brownian.Ito
