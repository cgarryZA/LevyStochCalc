/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Increments of the integral of a bounded function

The drift part of an Itô process is `t ↦ ∫_0^t b_s ds`. Its increment across a cell is the
integral over that cell, and is bounded by the bound on `b` times the cell length.

## Main statements

* `LevyStochCalc.integrableOn_of_bounded_of_measurable` — a bounded measurable function is
  integrable on any set of finite measure.
* `LevyStochCalc.setIntegral_Icc_sub_Icc` — `∫_{[0,b]} − ∫_{[0,a]} = ∫_{(a,b]}`.
* `LevyStochCalc.abs_setIntegral_Ioc_le` — `|∫_{(a,b]} f| ≤ B·(b − a)`.
-/

namespace LevyStochCalc

open MeasureTheory

/-- A bounded measurable function is integrable on any set of finite measure. -/
theorem integrableOn_of_bounded_of_measurable {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {s : Set ℝ} (hs : volume s ≠ ⊤) :
    MeasureTheory.IntegrableOn f s volume := by
  refine MeasureTheory.Measure.integrableOn_of_bounded (M := B) hs hf.aestronglyMeasurable ?_
  exact Filter.Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hB u

/-- The increment of `t ↦ ∫_{[0,t]} f` across `(a, b]` is the integral over `(a, b]`. -/
theorem setIntegral_Icc_sub_Icc {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (∫ s in Set.Icc (0 : ℝ) b, f s ∂volume) - ∫ s in Set.Icc (0 : ℝ) a, f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsplit : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    rw [Set.Icc_union_Ioc_eq_Icc ha hab]
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) :=
    Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
  have hint1 : MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) a) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have hint2 : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  rw [hsplit, MeasureTheory.setIntegral_union hdisj measurableSet_Ioc hint1 hint2,
    add_sub_cancel_left]

/-- The integral of a function bounded by `B` over `(a, b]` is at most `B·(b − a)` in size. -/
theorem abs_setIntegral_Ioc_le {f : ℝ → ℝ} (hf : Measurable f) {B : ℝ}
    (hB : ∀ s, |f s| ≤ B) {a b : ℝ} (hab : a ≤ b) :
    |∫ s in Set.Ioc a b, f s ∂volume| ≤ B * (b - a) := by
  have hB0 : (0 : ℝ) ≤ B := (abs_nonneg (f a)).trans (hB a)
  have hint : MeasureTheory.IntegrableOn f (Set.Ioc a b) volume :=
    integrableOn_of_bounded_of_measurable hf hB (by simp)
  have habs : |∫ s in Set.Ioc a b, f s ∂volume| ≤ ∫ s in Set.Ioc a b, |f s| ∂volume := by
    simpa [Real.norm_eq_abs] using
      MeasureTheory.norm_integral_le_integral_norm (μ := volume.restrict (Set.Ioc a b)) f
  refine habs.trans ?_
  have hle : ∫ s in Set.Ioc a b, |f s| ∂volume ≤ ∫ _s in Set.Ioc a b, B ∂volume := by
    refine MeasureTheory.setIntegral_mono_on hint.abs
      (MeasureTheory.integrableOn_const (by simp [Real.volume_Ioc])) measurableSet_Ioc
      fun u _ => hB u
  refine hle.trans ?_
  rw [MeasureTheory.setIntegral_const, Real.volume_real_Ioc_of_le hab, smul_eq_mul]
  exact le_of_eq (mul_comm _ _)

end LevyStochCalc
