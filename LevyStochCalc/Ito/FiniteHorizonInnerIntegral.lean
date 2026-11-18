/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.FiniteHorizonDrift

/-!
# The pairing of two time integrals

For two integrable functions `u, v : ℝ → E` on `[0, T]` with values in a complete real inner
product space,

`⟪∫_0^T u, ∫_0^T v⟫ = ∫_0^T ⟪u_s, ∫_0^s v⟫ ds + ∫_0^T ⟪∫_0^s u, v_s⟫ ds`,

the integrated product rule for absolutely continuous paths. The square `[0, T]²` is cut along
the diagonal, which is null, and each triangle is sliced by Fubini's theorem.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- **The pairing of the integrals of two integrable functions over `[0, T]`.** -/
theorem inner_setIntegral_eq {u v : ℝ → E} {T : ℝ}
    (hu : IntegrableOn u (Set.Icc (0 : ℝ) T)) (hv : IntegrableOn v (Set.Icc (0 : ℝ) T)) :
    ⟪∫ s in Set.Icc (0 : ℝ) T, u s, ∫ s in Set.Icc (0 : ℝ) T, v s⟫
      = (∫ s in Set.Icc (0 : ℝ) T, ⟪u s, ∫ r in Set.Icc (0 : ℝ) s, v r⟫)
        + ∫ s in Set.Icc (0 : ℝ) T, ⟪∫ r in Set.Icc (0 : ℝ) s, u r, v s⟫ := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have hprod : Integrable (fun p : ℝ × ℝ => ⟪u p.1, v p.2⟫) (μ.prod μ) :=
    Integrable.mono' (hu.norm.mul_prod hv.norm)
      ((hu.aestronglyMeasurable.comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).inner
        (hv.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
      (Eventually.of_forall fun p => norm_inner_le_norm _ _)
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => ⟪u p.1, v p.2⟫ with hF
  set G : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun p => ⟪u p.1, v p.2⟫ with hG
  set Dg : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 = p.2}.indicator fun p => ⟪u p.1, v p.2⟫ with hDg
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hge : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hFint : Integrable F (μ.prod μ) := hprod.indicator hle
  have hGint : Integrable G (μ.prod μ) := hprod.indicator hge
  have hDint : Integrable Dg (μ.prod μ) := hprod.indicator hdiag
  have hsplit : ∀ p : ℝ × ℝ, ⟪u p.1, v p.2⟫ + Dg p = F p + G p := by
    intro p
    simp only [hF, hG, hDg, Set.indicator, Set.mem_setOf_eq]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h.le, h.ne, not_le.mpr h]
    · simp [h]
    · simp [h.le, h.ne', not_le.mpr h]
  have hDzero : ∫ p, Dg p ∂(μ.prod μ) = 0 := by
    rw [hDg, integral_indicator hdiag]
    refine setIntegral_measure_zero _ ?_
    rw [Measure.prod_apply hdiag]
    simp
  -- the lower triangle, sliced at the second coordinate
  have hinnerF : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ r, F (r, s) ∂μ = ⟪∫ r in Set.Icc (0 : ℝ) s, u r, v s⟫ := by
    intro s hs
    have h1 : (fun r => F (r, s)) = fun r => (Set.Iic s).indicator (fun r => ⟪u r, v s⟫) r := by
      funext r
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
    rw [h1, integral_indicator measurableSet_Iic, hμ,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Icc_eq hs]
    exact integral_inner_const_right (hu.mono_set (Set.Icc_subset_Icc le_rfl hs.2)) (v s)
  -- the upper triangle, sliced at the first coordinate
  have hinnerG : ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫ s, G (r, s) ∂μ = ⟪u r, ∫ s in Set.Icc (0 : ℝ) r, v s⟫ := by
    intro r hr
    have h1 : (fun s => G (r, s)) = fun s => (Set.Iic r).indicator (fun s => ⟪u r, v s⟫) s := by
      funext s
      simp only [hG, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
    rw [h1, integral_indicator measurableSet_Iic, hμ,
      Measure.restrict_restrict measurableSet_Iic, Iic_inter_Icc_eq hr]
    exact integral_inner (hv.mono_set (Set.Icc_subset_Icc le_rfl hr.2)) (u r)
  have hFeq : ∫ p, F p ∂(μ.prod μ)
      = ∫ s in Set.Icc (0 : ℝ) T, ⟪∫ r in Set.Icc (0 : ℝ) s, u r, v s⟫ := by
    rw [integral_prod_symm F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => hinnerF s hs
  have hGeq : ∫ p, G p ∂(μ.prod μ)
      = ∫ r in Set.Icc (0 : ℝ) T, ⟪u r, ∫ s in Set.Icc (0 : ℝ) r, v s⟫ := by
    rw [integral_prod G hGint]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hinnerG r hr
  have hsum : ∫ p, ⟪u p.1, v p.2⟫ ∂(μ.prod μ)
      = ∫ p, F p ∂(μ.prod μ) + ∫ p, G p ∂(μ.prod μ) := by
    have h1 : ∫ p, (⟪u p.1, v p.2⟫ + Dg p) ∂(μ.prod μ) = ∫ p, (F p + G p) ∂(μ.prod μ) :=
      integral_congr_ae (Eventually.of_forall hsplit)
    rw [integral_add hprod hDint, integral_add hFint hGint, hDzero, add_zero] at h1
    exact h1
  have hfull : ⟪∫ s in Set.Icc (0 : ℝ) T, u s, ∫ s in Set.Icc (0 : ℝ) T, v s⟫
      = ∫ p, ⟪u p.1, v p.2⟫ ∂(μ.prod μ) := by
    rw [integral_prod _ hprod, ← integral_inner_const_right hu]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    exact (integral_inner hv (u r)).symm
  rw [hfull, hsum, hFeq, hGeq, add_comm]

end LevyStochCalc.Ito.FiniteHorizon
