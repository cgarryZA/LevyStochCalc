/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Pairing an integrable weight against a time integral

For an integrable weight and a bounded jointly measurable process on a bounded time interval, the
expectation of the weight against the time integral of the process is the time integral of the
expectations.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- **Fubini for a pairing against a time integral.** -/
theorem integral_mul_setIntegral_Ioc {a t : ℝ} {Z : Ω → ℂ} (hZm : Measurable Z)
    (hZ : Integrable Z P) {Φ : Ω → ℝ → ℂ} (hΦ : Measurable (Function.uncurry Φ))
    {C : ℝ} (hC : ∀ ω u, ‖Φ ω u‖ ≤ C) :
    ∫ ω, Z ω * (∫ u in Set.Ioc a t, Φ ω u) ∂P
      = ∫ u in Set.Ioc a t, (∫ ω, Z ω * Φ ω u ∂P) := by
  have hmeas : Measurable (Function.uncurry fun ω u => Z ω * Φ ω u) :=
    (hZm.comp measurable_fst).mul hΦ
  have hmaj : Integrable (fun p : Ω × ℝ => ‖Z p.1‖ * C)
      (P.prod (volume.restrict (Set.Ioc a t))) :=
    hZ.norm.mul_prod (integrable_const C)
  have hprod : Integrable (Function.uncurry fun ω u => Z ω * Φ ω u)
      (P.prod (volume.restrict (Set.Ioc a t))) := by
    refine hmaj.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun p => ?_)
    calc ‖Z p.1 * Φ p.1 p.2‖ = ‖Z p.1‖ * ‖Φ p.1 p.2‖ := norm_mul _ _
      _ ≤ ‖Z p.1‖ * C := by
          exact mul_le_mul_of_nonneg_left (hC _ _) (norm_nonneg _)
  calc ∫ ω, Z ω * (∫ u in Set.Ioc a t, Φ ω u) ∂P
      = ∫ ω, (∫ u in Set.Ioc a t, Z ω * Φ ω u) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        exact (integral_const_mul (Z ω) fun u => Φ ω u).symm
    _ = ∫ u in Set.Ioc a t, (∫ ω, Z ω * Φ ω u ∂P) := integral_integral_swap hprod

section Swap

variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [SFinite μ]

/-- The pairing of an integrable weight and a bounded factor with a set integral of a bounded
jointly measurable kernel is the set integral of the pairings. -/
theorem integral_mul_setIntegral_swap {S : Set Y} (hSfin : μ S ≠ ⊤)
    {Z : Ω → ℝ} (hZ1 : Integrable Z P) {V : Ω → ℝ} (hVm : AEStronglyMeasurable V P)
    {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    {F : Ω → Y → ℝ} (hFm : Measurable (Function.uncurry F))
    {MF : ℝ} (hFb : ∀ ω y, |F ω y| ≤ MF) :
    ∫ ω, Z ω * V ω * (∫ y in S, F ω y ∂μ) ∂P
      = ∫ y in S, ∫ ω, Z ω * V ω * F ω y ∂P ∂μ := by
  haveI : IsFiniteMeasure (μ.restrict S) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hSfin⟩
  have hZVm : AEStronglyMeasurable (fun ω => Z ω * V ω) P :=
    hZ1.aestronglyMeasurable.mul hVm
  have hGm : AEStronglyMeasurable (Function.uncurry fun ω y => Z ω * V ω * F ω y)
      (P.prod (μ.restrict S)) := hZVm.comp_fst.mul hFm.aestronglyMeasurable
  have hFω : ∀ ω, Measurable (F ω) := fun ω => hFm.comp (measurable_prodMk_left (x := ω))
  have hZV : ∀ ω, |Z ω * V ω| ≤ Mv * |Z ω| := by
    intro ω
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hVb ω) (abs_nonneg _)
  have hG : Integrable (Function.uncurry fun ω y => Z ω * V ω * F ω y)
      (P.prod (μ.restrict S)) := by
    refine (integrable_prod_iff hGm).mpr ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
    · show Integrable (fun y => Z ω * V ω * F ω y) (μ.restrict S)
      refine Integrable.mono' (integrable_const (|Z ω * V ω| * MF))
        (((hFω ω).aestronglyMeasurable).const_mul _)
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_left (hFb ω y) (abs_nonneg _)
    · refine Integrable.mono'
        (((hZ1.norm.const_mul (MF * Mv)).mul_const ((μ.restrict S).real Set.univ)))
        hGm.norm.integral_prod_right' (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
      calc ∫ y, ‖Z ω * V ω * F ω y‖ ∂(μ.restrict S)
          ≤ ∫ _, MF * Mv * ‖Z ω‖ ∂(μ.restrict S) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall fun y => ?_)
            show ‖Z ω * V ω * F ω y‖ ≤ MF * Mv * ‖Z ω‖
            calc ‖Z ω * V ω * F ω y‖ = |Z ω * V ω| * |F ω y| := by
                  rw [Real.norm_eq_abs, abs_mul]
              _ ≤ Mv * |Z ω| * MF :=
                  mul_le_mul (hZV ω) (hFb ω y) (abs_nonneg _) (mul_nonneg hMv0 (abs_nonneg _))
              _ = MF * Mv * ‖Z ω‖ := by rw [Real.norm_eq_abs]; ring
        _ = MF * Mv * ‖Z ω‖ * ((μ.restrict S).real Set.univ) := by
            rw [integral_const, smul_eq_mul, mul_comm]
  have hL : ∫ ω, Z ω * V ω * (∫ y in S, F ω y ∂μ) ∂P
      = ∫ ω, ∫ y, Z ω * V ω * F ω y ∂(μ.restrict S) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    show Z ω * V ω * (∫ y in S, F ω y ∂μ) = ∫ y in S, Z ω * V ω * F ω y ∂μ
    rw [MeasureTheory.integral_const_mul]
  rw [hL, integral_integral_swap hG]

end Swap

end LevyStochCalc.Probability
