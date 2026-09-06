/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.NaturalFiltration
import LevyStochCalc.Probability.IndepLimit

/-!
# Poisson random measures with respect to a filtration

`IsPoissonFiltration N ℱ` says that the counts of the Poisson random measure `N` on regions
of the past `(-∞, t] × E` are `ℱ t`-measurable and that its counts on future strips
`(s, t] × A` of finite intensity are independent of `ℱ s`. The natural filtration of `N` is an
instance, a smaller filtration to which `N` is adapted is one, and so is the right-continuous
version `ℱ₊`: the counts `N((r, t] × A)`, independent of `ℱ r ⊇ ℱ₊ s`, increase to
`N((s, t] × A)` as `r ↓ s`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- `N` is a Poisson random measure for the filtration `ℱ`: its counts on measurable regions
of `(-∞, t] × E` are `ℱ t`-measurable, and its counts on `(s, t] × A`, for `0 ≤ s < t` and
`ν A < ∞`, are independent of `ℱ s`. -/
structure IsPoissonFiltration (N : PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) : Prop where
  measurable : ∀ ⦃t : ℝ⦄ ⦃B : Set (ℝ × E)⦄, B ⊆ Set.Iic t ×ˢ Set.univ → MeasurableSet B →
    Measurable[ℱ t] (fun ω => N.N ω B)
  indep : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s < t → ∀ ⦃A : Set E⦄, MeasurableSet A → ν A ≠ ⊤ →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc s t ×ˢ A)) inferInstance) P

/-- A Poisson random measure is one for its natural filtration. -/
theorem isPoissonFiltration_natural (N : PoissonRandomMeasure P ν) :
    IsPoissonFiltration N (naturalFiltration N) where
  measurable _ _ hB hBm := measurable_random_measure_of_le N hB hBm
  indep _ _ hs hst _ hA hAν := N.joint_past_future_independent hs hst hA hAν

/-- A Poisson random measure for `ℱ` is one for any smaller filtration to which it is adapted. -/
theorem IsPoissonFiltration.of_le {N : PoissonRandomMeasure P ν}
    {ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsPoissonFiltration N ℱ) (hle : 𝒢 ≤ ℱ)
    (hadapted : ∀ ⦃t : ℝ⦄ ⦃B : Set (ℝ × E)⦄, B ⊆ Set.Iic t ×ˢ Set.univ → MeasurableSet B →
      Measurable[𝒢 t] (fun ω => N.N ω B)) :
    IsPoissonFiltration N 𝒢 where
  measurable := hadapted
  indep _ _ hs hst _ hA hAν := indep_of_indep_of_le_left (h.indep hs hst hA hAν) (hle _)

/-- A Poisson random measure for `ℱ` is one for the right-continuous filtration `ℱ₊`. -/
theorem IsPoissonFiltration.rightCont {N : PoissonRandomMeasure P ν}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsPoissonFiltration N ℱ) :
    IsPoissonFiltration N ℱ.rightCont where
  measurable _ _ hB hBm := (h.measurable hB hBm).mono (ℱ.le_rightCont _) le_rfl
  indep := by
    intro s t hs hst A hA hAν
    obtain ⟨r, hr_anti, hr_mem, hr_tend⟩ := exists_seq_strictAnti_tendsto' hst
    have hle : ∀ n, ℱ.rightCont s ≤ ℱ (r n) := fun n => by
      rw [Filtration.rightCont_eq_of_neBot_nhdsGT ℱ s]
      exact iInf₂_le (r n) (hr_mem n).1
    have hmeasA : MeasurableSet (Set.Ioc s t ×ˢ A) := measurableSet_Ioc.prod hA
    refine Probability.indep_comap_of_tendsto_ae (ℱ.rightCont.le s)
      (X := fun n ω => N.N ω (Set.Ioc (r n) t ×ˢ A)) (Y := fun ω => N.N ω (Set.Ioc s t ×ˢ A))
      (fun n => N.measurable_eval (measurableSet_Ioc.prod hA)) (N.measurable_eval hmeasA)
      (fun n => indep_of_indep_of_le_left (h.indep (hs.trans (hr_mem n).1.le) (hr_mem n).2 hA hAν)
        (hle n)) (ae_of_all _ fun ω => ?_)
    have hmono : Monotone fun n => Set.Ioc (r n) t ×ˢ A := fun n m hnm =>
      Set.prod_mono (Set.Ioc_subset_Ioc_left (hr_anti.antitone hnm)) le_rfl
    have hU : (⋃ n, Set.Ioc (r n) t ×ˢ A) = Set.Ioc s t ×ˢ A := by
      rw [← Set.iUnion_prod_const]
      congr 1
      ext x
      simp only [Set.mem_iUnion, Set.mem_Ioc]
      constructor
      · rintro ⟨n, hn, hx⟩
        exact ⟨(hr_mem n).1.trans hn, hx⟩
      · rintro ⟨hsx, hxt⟩
        obtain ⟨n, hn⟩ := (hr_tend.eventually (gt_mem_nhds hsx)).exists
        exact ⟨n, hn, hxt⟩
    have := tendsto_measure_iUnion_atTop (μ := N.N ω) hmono
    rw [hU] at this
    exact this

end LevyStochCalc.Poisson
