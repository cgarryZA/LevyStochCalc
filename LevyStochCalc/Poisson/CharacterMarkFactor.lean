/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterStrictProcess

/-!
# The deterministic mark factor of the chain rule's integrand

At each time and mark the chain rule's integrand is the product of a deterministic factor,
carrying the indicator of the family and the jump `e^{i m} - 1` that a point there contributes,
with the exponential of the strict past. Inside the window the second factor agrees almost
surely with the character at that time, and so does the predictable representative of the
strict-past character.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section MarkFactor

/-- The deterministic factor of the chain rule's integrand at a time and a mark. -/
noncomputable def markFactor (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (q : ℝ × E) : ℂ :=
  (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)
    * (Complex.exp (Complex.I * (simpleMark w Bfam q : ℂ)) - 1)

variable (N : PoissonRandomMeasure P ν)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The chain rule's integrand is the mark factor times the exponential of the strict past. -/
theorem charIntegrand_eq_markFactor_mul (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E)
    (T : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    charIntegrand N w Bfam A T ω s e
      = markFactor w Bfam (s, e)
        * Complex.exp (Complex.I * (predStrict N w Bfam A T ω s e : ℂ)) := by
  rw [charIntegrand, markFactor]
  ring

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] in
/-- The mark factor is bounded by `2`. -/
theorem norm_markFactor_le (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (q : ℝ × E) :
    ‖markFactor w Bfam q‖ ≤ 2 := by
  classical
  rw [markFactor, norm_mul]
  have hind : ‖(((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hq : q ∈ ⋃ j, Bfam j
    · rw [Set.indicator_of_mem hq]; norm_num
    · rw [Set.indicator_of_notMem hq]; norm_num
  have hexp : ‖Complex.exp (Complex.I * (simpleMark w Bfam q : ℂ)) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]
    norm_num
  calc ‖(((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)‖
        * ‖Complex.exp (Complex.I * (simpleMark w Bfam q : ℂ)) - 1‖
      ≤ 1 * 2 := mul_le_mul hind hexp (norm_nonneg _) zero_le_one
    _ = 2 := one_mul 2

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The measurability of the mark factor. -/
theorem measurable_markFactor (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) : Measurable (markFactor w Bfam) := by
  classical
  refine Measurable.mul ?_ ?_
  · exact Complex.measurable_ofReal.comp (measurable_const.indicator (MeasurableSet.iUnion hBm))
  · exact (Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (measurable_simpleMark w hBm)))).sub measurable_const

/-- Inside the window the exponential of the strict past agrees almost surely with the character
at that time. -/
theorem ae_exp_predStrict_eq_charAt (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) :
    ∀ᵐ ω ∂P, Complex.exp (Complex.I * (predStrict N w Bfam A T ω s e : ℂ))
      = charAt N w Bfam s ω := by
  filter_upwards [ae_charAt_eq_charStrict N w hBm hs] with ω hω
  rw [predStrict_eq N w Bfam hs hsT he ω, hω]
  rfl

/-- At a positive time the predictable representative of the strict-past character agrees almost
surely with the character. -/
theorem ae_charStrictPred_eq_charAt (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} {b T : ℝ} (hT : 0 < T) (hbT : b < T)
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A) {s : ℝ}
    (hs : 0 < s) :
    ∀ᵐ ω ∂P, charStrictPred N w Bfam A T e₀ s ω = charAt N w Bfam s ω := by
  filter_upwards [ae_charAt_eq_charStrict N w hBm hs] with ω hω
  rw [charStrictPred_eq N w hT hbT hBsub he₀ s ω, hω]

/-- Inside the window the pairing against the chain rule's integrand is the mark factor times the
pairing against the character at that time. -/
theorem integral_mul_charIntegrand {r : Ω → ℝ} (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T)
    {e : E} (he : e ∈ A) :
    ∫ ω, (r ω : ℂ) * charIntegrand N w Bfam A T ω s e ∂P
      = markFactor w Bfam (s, e) * ∫ ω, (r ω : ℂ) * charAt N w Bfam s ω ∂P := by
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [ae_exp_predStrict_eq_charAt N w hBm hs hsT he] with ω hω
  rw [charIntegrand_eq_markFactor_mul N w Bfam A T ω s e, hω]
  ring

end MarkFactor

end LevyStochCalc.Poisson
