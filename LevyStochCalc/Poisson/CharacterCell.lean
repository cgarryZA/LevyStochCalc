/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterStrict
import LevyStochCalc.Poisson.ChainRule

/-!
# The character of a window family as a pure-jump process

For a finite family of window sets inside `(a, b] × A`, the real and imaginary parts of the
character `charAt` of the counts up to `s` are bounded by one, are measurable at time `s` for a
Poisson filtration, and, outside one null set, satisfy at every time the jump identity
`Y s = Y a + ∫_{(a, s] × A} g dN` whose weight `g` is the corresponding part of
`exp (i · windowSumStrict) (exp (i · mark) − 1)`, bounded by two. This is the shape the product
rule for a continuous Itô process and a pure-jump process asks for.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Jump

/-- The jump weight of the character at a time–mark point: the strict-past character times the
increment of the mark's exponential. -/
noncomputable def charJump (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (ω : Ω) (p : ℝ × E) : ℂ :=
  Complex.exp (Complex.I *
      (windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) p.1 ω : ℂ))
    * (Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_charJump_le (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (ω : Ω) (p : ℝ × E) : ‖charJump N w Bfam ω p‖ ≤ 2 := by
  rw [charJump, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  calc ‖Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1‖
      ≤ ‖Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [Complex.norm_exp_I_mul_ofReal, norm_one]; norm_num

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The character of the counts up to `s` is measurable at time `s` for a Poisson filtration. -/
theorem stronglyMeasurable_charAt (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (s : ℝ) :
    StronglyMeasurable[ℱ s] (charAt N w Bfam s) := by
  have hcount : ∀ j, Measurable[ℱ s] fun ω => N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ) :=
    fun j => hℱ.measurable (fun p hp => ⟨hp.2.1.2, Set.mem_univ _⟩)
      ((hBm j).inter (measurableSet_Ioc.prod MeasurableSet.univ))
  refine Measurable.stronglyMeasurable ?_
  unfold charAt
  refine Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp ?_))
  exact Finset.measurable_sum _ fun j _ =>
    (ENNReal.measurable_toReal.comp (hcount j)).const_mul (w j)

/-- **The character as a pure-jump process.** Outside one null set the character of the counts up
to `s` is, at every time, its value at `a` plus the integral of the jump weight over the window
of the times in `(a, s]`. -/
theorem ae_forall_charAt_sub (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, charAt N w Bfam s ω
      = 1 + ∫ p in (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          charJump N w Bfam ω p ∂(N.N ω) := by
  have hBUm : MeasurableSet (⋃ j, Bfam j) := MeasurableSet.iUnion hBm
  have hBUfin : referenceIntensity ν (⋃ j, Bfam j) ≠ ⊤ :=
    ne_top_of_le_ne_top (referenceIntensity_Ioc_prod_ne_top hAν T)
      (measure_mono (Set.iUnion_subset hBsub))
  filter_upwards [ae_forall_exp_windowSum_sub_one N hBUm hBUfin (simpleMark w Bfam),
    ae_windowSum_simple N hAν w hBm hBsub] with ω hchain hsum s
  have h1 : charAt N w Bfam s ω
      = Complex.exp (Complex.I * (windowSum N (⋃ j, Bfam j) (simpleMark w Bfam) s ω : ℂ)) := by
    rw [charAt, (hsum s).1]
  rw [h1]
  have h2 := (hchain s).1
  have hint : (∫ p in (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
        charJump N w Bfam ω p ∂(N.N ω))
      = ∫ p in (⋃ j, Bfam j) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          Complex.exp (Complex.I *
              (windowSumStrict N (⋃ j, Bfam j) (simpleMark w Bfam) p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (simpleMark w Bfam p : ℂ)) - 1) ∂(N.N ω) := rfl
  rw [hint, ← h2]
  ring

end Jump

end LevyStochCalc.Poisson
