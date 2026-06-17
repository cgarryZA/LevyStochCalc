/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedSimple
import LevyStochCalc.Poisson.CompensatedIsometry
import LevyStochCalc.Poisson.NaturalFiltration
import Mathlib.Probability.Process.Adapted
import Mathlib.Probability.ConditionalExpectation

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

/-- **First-moment integrability of a compensated mass.** For `B` with finite
reference intensity, `ω ↦ Ñ(B) = N(B) − referenceIntensity B` is `P`-integrable.
Pushforward through `poisson_law` to `poissonMeasure r`, where `n ↦ n − r` is
integrable (the Poisson law has a finite first moment). -/
lemma compensated_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => N.compensated B ω) P := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  rw [show (fun ω => N.compensated B ω)
        = (fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B) from rfl,
    ← MeasureTheory.integrable_map_measure
      (ENNReal.measurable_toReal.sub_const c).aestronglyMeasurable h_NB_meas.aemeasurable,
    N.poisson_law hB h_finite, LevyStochCalc.Poisson.poissonMeasureENN,
    MeasureTheory.integrable_map_measure
      (ENNReal.measurable_toReal.sub_const c).aestronglyMeasurable
      (measurable_from_nat).aemeasurable]
  have h_eq : ((fun x : ℝ≥0∞ => x.toReal - c) ∘ fun n : ℕ => (n : ℝ≥0∞))
      = fun n : ℕ => (n : ℝ) - c := by
    funext n; rw [Function.comp_apply, show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp]
  rw [h_eq]
  have h_int_id : MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
    simp_rw [h_norm, show ∀ n : ℕ, Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)
        * (↑n : ℝ) = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ))
      from fun n => by ring]
    exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
  exact h_int_id.sub (MeasureTheory.integrable_const c)

/-- The reference intensity of a clamped time-rectangle `timeRect i t` is finite:
it is `volume(Ioc …) · ν(Aᵢ)` with both factors finite (`Aᵢ` has finite `ν`-mass). -/
lemma referenceIntensity_timeRect_ne_top
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t) ≠ ⊤ := by
  rw [SimplePredictable.timeRect, LevyStochCalc.Poisson.referenceIntensity,
    MeasureTheory.Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)

/-- **Per-term integrability** of the compensated simple integral: each summand
`ξᵢ · Ñ(timeRect i t)` is `P`-integrable (`ξᵢ` bounded, the compensated mass
integrable by `compensated_integrable` since `timeRect i t` has finite intensity). -/
lemma simpleIntegral_term_integrable_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) :
    MeasureTheory.Integrable (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) P := by
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have h_rect_meas : MeasurableSet (φ.timeRect i t) := by
    rw [SimplePredictable.timeRect]; exact measurableSet_Ioc.prod (φ.A_measurable i)
  refine MeasureTheory.Integrable.bdd_mul
    (compensated_integrable N h_rect_meas (referenceIntensity_timeRect_ne_top φ i t))
    (φ.ξ_measurable i).aestronglyMeasurable (c := |M|) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self _)

/-- **Conditional mean-zero of a future compensated increment.** For `0 ≤ s < t'`
and a finite-mass mark set `A`, the compensated mass of the future time-rectangle
`(s, t'] ×ˢ A` has zero conditional expectation given `ℱ_s`: it is independent of
`ℱ_s` (`joint_past_future_independent`) with mean `0` (`compensated_mean_zero`), so
`condExp_indep_eq` collapses the conditional expectation to the (zero) mean. -/
lemma compensated_condExp_future_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {s t' : ℝ} (hs : 0 ≤ s) (hst : s < t') {A : Set E} (hA : MeasurableSet A)
    (hA_fin : ν A ≠ ⊤) :
    P[fun ω => N.compensated (Set.Ioc s t' ×ˢ A) ω
        | (LevyStochCalc.Poisson.naturalFiltration N).seq s]
      =ᵐ[P] fun _ => (0 : ℝ) := by
  set B : Set (ℝ × E) := Set.Ioc s t' ×ˢ A with hB
  have hB_meas : MeasurableSet B := measurableSet_Ioc.prod hA
  have h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ := by
    rw [hB, LevyStochCalc.Poisson.referenceIntensity, MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ hA_fin
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top
  have hle₁ := (N.measurable_eval hB_meas).comap_le
  have hle₂ := (LevyStochCalc.Poisson.naturalFiltration N).le' s
  have hg : @Measurable Ω ℝ≥0∞ (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) _
      (fun ω => N.N ω B) := fun u hu => ⟨u, hu, rfl⟩
  have hf : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (fun ω => N.compensated B ω) :=
    ((hg.ennreal_toReal).sub_const _).stronglyMeasurable
  have hindep : ProbabilityTheory.Indep (MeasurableSpace.comap (fun ω => N.N ω B) inferInstance)
      ((LevyStochCalc.Poisson.naturalFiltration N).seq s) P := by
    rw [LevyStochCalc.Poisson.naturalFiltration_seq_eq]
    exact (N.joint_past_future_independent hs hst hA hA_fin).symm
  refine (MeasureTheory.condExp_indep_eq hle₁ hle₂ hf hindep).trans ?_
  filter_upwards with ω
  exact compensated_mean_zero N hB_meas h_finite

/-- **a.e.-additivity of the compensated mass on disjoint finite-intensity sets.**
`Ñ(B ∪ C) =ᵐ Ñ(B) + Ñ(C)`. The reference intensity is a measure (additive
everywhere), and `N(B), N(C)` are a.e. finite (`integer_valued`), so the `toReal`
of the `N`-sum splits a.e. -/
lemma compensated_union_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C) (hBC : Disjoint B C)
    (hB_fin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hC_fin : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤) :
    (fun ω => N.compensated (B ∪ C) ω)
      =ᵐ[P] fun ω => N.compensated B ω + N.compensated C ω := by
  filter_upwards [N.integer_valued hB hB_fin, N.integer_valued hC hC_fin] with ω hnB hnC
  obtain ⟨nB, hnB⟩ := hnB
  obtain ⟨nC, hnC⟩ := hnC
  unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
  rw [MeasureTheory.measure_union hBC hC, MeasureTheory.measure_union hBC hC,
    ENNReal.toReal_add (by rw [hnB]; exact ENNReal.natCast_ne_top nB)
      (by rw [hnC]; exact ENNReal.natCast_ne_top nC),
    ENNReal.toReal_add hB_fin hC_fin]
  ring

end LevyStochCalc.Poisson.Compensated
