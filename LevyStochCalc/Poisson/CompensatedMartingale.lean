/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedSimple
import LevyStochCalc.Poisson.NaturalFiltration
import Mathlib.Probability.Process.Adapted

/-!
# Martingale property of the simple compensated-Poisson integral

`simpleIntegral N φ` is adapted to the natural filtration of `N`
(`simpleIntegral_stronglyAdapted_compensated`), the first step toward its
martingale property (the compensated analogue of `Brownian.Ito`'s
`martingale_simpleIntegral_brownian`). Each time-rectangle `timeRect i t` lies in
the past `Iic t ×ˢ univ`, so its compensated mass is `ℱ_t`-measurable
(`measurable_random_measure_of_le`); the coefficient `ξ_i` is `ℱ_t`-measurable
once `t` reaches the partition point (and the term vanishes before).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Per-term `ℱ_t`-adaptedness** of the compensated simple integral. For
`t ≥ tᵢ` the coefficient `ξᵢ` is `ℱ_t`-measurable and the time-rectangle's
compensated mass is `ℱ_t`-measurable (it lives in the past `Iic t ×ˢ univ`); for
`t < tᵢ` the time-rectangle is empty and the term is `0`. -/
lemma simpleIntegral_term_adapted_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  have hpre_lt_post : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  by_cases ht_pre : φ.partition i.castSucc ≤ t
  · -- `tᵢ ≤ t`: the rectangle is in the past and `ξᵢ` is `ℱ_t`-measurable.
    have h_rect_sub : φ.timeRect i t ⊆ Set.Iic t ×ˢ Set.univ := by
      intro p hp
      rw [SimplePredictable.timeRect, Set.mem_prod] at hp
      exact ⟨le_trans hp.1.2 (min_le_right _ _), Set.mem_univ _⟩
    have h_rect_meas : MeasurableSet (φ.timeRect i t) := by
      rw [SimplePredictable.timeRect]
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    have h_comp : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (N.compensated (φ.timeRect i t)) := by
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
      exact (((LevyStochCalc.Poisson.measurable_random_measure_of_le N h_rect_sub
        h_rect_meas).ennreal_toReal).sub measurable_const).stronglyMeasurable
    exact (h_adapt_i.mono (ℱ.mono ht_pre)).mul h_comp
  · -- `t < tᵢ`: the time-rectangle is empty, so the term is `0`.
    push_neg at ht_pre
    have h_min_pre : min (φ.partition i.castSucc) t = t := min_eq_right (le_of_lt ht_pre)
    have h_min_post : min (φ.partition i.succ) t = t :=
      min_eq_right (le_of_lt (lt_trans ht_pre hpre_lt_post))
    have h_rect_empty : φ.timeRect i t = ∅ := by
      rw [SimplePredictable.timeRect, h_min_pre, h_min_post, Set.Ioc_self, Set.empty_prod]
    have h_zero : (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) = fun _ => (0 : ℝ) := by
      funext ω
      rw [h_rect_empty]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
      simp
    rw [h_zero]; exact stronglyMeasurable_const

/-- **`ℱ`-adaptedness of the compensated simple integral.** For an adapted simple
integrand `φ`, the process `t ↦ simpleIntegral N φ t` is strongly adapted to the
natural filtration of `N`. -/
lemma simpleIntegral_stronglyAdapted_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.StronglyAdapted (LevyStochCalc.Poisson.naturalFiltration N)
      (fun t => simpleIntegral N φ t) := by
  intro t
  change @MeasureTheory.StronglyMeasurable Ω ℝ _
    ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
    (fun ω => ∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.timeRect i t) ω)
  exact Finset.stronglyMeasurable_fun_sum _
    (fun i _ => simpleIntegral_term_adapted_compensated N φ i t (h_adapt i))

end LevyStochCalc.Poisson.Compensated
