/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaLimit
import LevyStochCalc.Ito.JumpFormulaDictionary
import LevyStochCalc.Brownian.ItoFiltrationChange

/-!
# Exhausting a σ-finite mark space by finite-activity complements

A σ-finite intensity has a monotone family of measurable sets of finite measure covering the mark
space, so the complements of that family are antitone, have empty intersection, and carry finite
intensity on their own complements. Truncating a jump coefficient to the complement of a member
therefore leaves finite activity, and the members shrink to a null set.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.smallMarks` — the complements of a spanning family of the
  intensity.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurableSet_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.antitone_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_compl_smallMarks_lt_top`,
  `LevyStochCalc.Ito.JumpFormula.iInter_smallMarks`,
  `LevyStochCalc.Ito.JumpFormula.measure_iInter_smallMarks` — the four properties the small-jump
  truncation asks of a family of mark sets.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

variable {E : Type v} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]

/-- The complements of a spanning family of the intensity, used as the small-mark sets of the
truncation. -/
def smallMarks (m : ℕ) : Set E := (spanningSets ν m)ᶜ

theorem measurableSet_smallMarks (m : ℕ) : MeasurableSet (smallMarks ν m) :=
  (measurableSet_spanningSets ν m).compl

theorem compl_smallMarks (m : ℕ) : (smallMarks ν m)ᶜ = spanningSets ν m :=
  compl_compl _

theorem antitone_smallMarks : Antitone (smallMarks ν) := fun _ _ h =>
  Set.compl_subset_compl.mpr (monotone_spanningSets ν h)

theorem measure_compl_smallMarks_lt_top (m : ℕ) : ν (smallMarks ν m)ᶜ < ⊤ := by
  rw [compl_smallMarks]
  exact measure_spanningSets_lt_top ν m

theorem measure_compl_smallMarks_ne_top (m : ℕ) : ν (smallMarks ν m)ᶜ ≠ ⊤ :=
  (measure_compl_smallMarks_lt_top ν m).ne

theorem iInter_smallMarks : (⋂ m, smallMarks ν m) = (∅ : Set E) := by
  simp only [smallMarks, ← Set.compl_iUnion, iUnion_spanningSets ν, Set.compl_univ]

theorem measure_iInter_smallMarks : ν (⋂ m, smallMarks ν m) = 0 := by
  rw [iInter_smallMarks ν]
  exact measure_empty

/-- Almost every mark eventually leaves the small-mark sets. -/
theorem ae_eventually_notMem_smallMarks :
    ∀ᵐ e ∂ν, ∀ᶠ m in Filter.atTop, e ∉ smallMarks ν m :=
  ae_eventually_notMem_of_antitone (antitone_smallMarks ν) (measure_iInter_smallMarks ν)

section Augmentation

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The multidimensional Brownian integral over a filtration agrees almost everywhere with the
integral over its augmentation. -/
theorem multidimStochasticIntegral_augFiltration
    (W : MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ) (Z : ℝ → Ω → Fin d → ℝ)
    (hm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hp' : ∀ i : Fin d,
      Probability.ProgressivelyMeasurable (augFiltration ℱ P) fun ω s => Z s ω i)
    (hq : ∀ (i : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) :
    MultidimBrownianMotion.stochasticIntegral W ℱ hℱ Z hm hp hq T
      =ᵐ[P] MultidimBrownianMotion.stochasticIntegral W (augFiltration ℱ P)
        (fun i => isBrownianFiltration_augFiltration (hℱ i)) Z hm hp' hq T := by
  have hchan : ∀ i : Fin d,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱ i)
          (fun ω s => Z s ω i) (hm i) (hp i) (hq i) T
        =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i)
          (augFiltration ℱ P) (isBrownianFiltration_augFiltration (hℱ i))
          (fun ω s => Z s ω i) (hm i) (hp' i) (hq i) T :=
    fun i => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration
      (W.W i) ℱ (hℱ i) _ (hm i) (hp i) (hp' i) (hq i) T
  filter_upwards [MeasureTheory.ae_all_iff.mpr hchan] with ω hω
  rw [multidimStochasticIntegral_eq_sum W ℱ hℱ Z hm hp hq T ω,
    multidimStochasticIntegral_eq_sum W (augFiltration ℱ P)
      (fun i => isBrownianFiltration_augFiltration (hℱ i)) Z hm hp' hq T ω]
  exact Finset.sum_congr rfl fun i _ => hω i

end Augmentation

end LevyStochCalc.Ito.JumpFormula
