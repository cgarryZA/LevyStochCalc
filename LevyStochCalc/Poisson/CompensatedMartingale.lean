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
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

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

/-- **Conditional mean-zero of a time-rectangle increment `(a, b] ×ˢ A`** whose
lower endpoint dominates the conditioning time when non-degenerate. Degenerate
(`a = b`) increments are `0`; for `a = s` it is the base future increment; for
`s < a` the tower property reduces it to the base case at `ℱ_a`. -/
lemma compensated_condExp_Ioc_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {s a b : ℝ} (hs : 0 ≤ s) (hab : a ≤ b) (hlow : a < b → s ≤ a)
    {A : Set E} (hA : MeasurableSet A) (hA_fin : ν A ≠ ⊤) :
    P[fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω
        | (LevyStochCalc.Poisson.naturalFiltration N).seq s]
      =ᵐ[P] fun _ => (0 : ℝ) := by
  rcases eq_or_lt_of_le hab with hab_eq | hab_lt
  · have hemp : (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) = fun _ => (0 : ℝ) := by
      funext ω
      rw [← hab_eq, Set.Ioc_self, Set.empty_prod]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp
    rw [hemp]
    exact Filter.EventuallyEq.of_eq
      (MeasureTheory.condExp_const ((LevyStochCalc.Poisson.naturalFiltration N).le' s) (0 : ℝ))
  · have hsa := hlow hab_lt
    rcases eq_or_lt_of_le hsa with hsa_eq | hsa_lt
    · rw [← hsa_eq]
      exact compensated_condExp_future_eq_zero N hs (hsa_eq ▸ hab_lt) hA hA_fin
    · have h_base := compensated_condExp_future_eq_zero N (le_trans hs hsa) hab_lt hA hA_fin
      have hm₂a := (LevyStochCalc.Poisson.naturalFiltration N).le' a
      haveI : SigmaFinite (P.trim hm₂a) := inferInstance
      have h_tower := MeasureTheory.condExp_condExp_of_le (μ := P)
        (f := fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω)
        ((LevyStochCalc.Poisson.naturalFiltration N).mono hsa) hm₂a
      refine h_tower.symm.trans ((MeasureTheory.condExp_congr_ae h_base).trans ?_)
      exact Filter.EventuallyEq.of_eq
        (MeasureTheory.condExp_const ((LevyStochCalc.Poisson.naturalFiltration N).le' s) (0 : ℝ))

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

/-- General finiteness of the reference intensity of a time-rectangle `(a, b] ×ˢ A`
when `A` has finite `ν`-mass. -/
lemma referenceIntensity_Ioc_prod_ne_top
    {ν : Measure E} [SigmaFinite ν] {a b : ℝ} {A : Set E} (hA_fin : ν A ≠ ⊤) :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ := by
  rw [LevyStochCalc.Poisson.referenceIntensity, MeasureTheory.Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ hA_fin
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)

set_option maxHeartbeats 1000000 in
-- The Case-B tower-property chain (`condExp_mul` + `condExp_condExp_of_le`) is
-- heartbeat-heavy; raise the budget for this single proof.
/-- **Per-term conditional-expectation identity** for the compensated simple integral:
`𝔼[ξᵢ·Ñ(timeRect i t) | ℱ_s] =ᵐ ξᵢ·Ñ(timeRect i s)` (for `0 ≤ s ≤ t`). Case A
(`tᵢ ≤ s`): `ξᵢ` is `ℱ_s`-measurable; split `Ñ(timeRect i t) = Ñ(timeRect i s) +
Ñ(future)`, pull out `ξᵢ`, and the future increment's conditional mean is `0`. Case B
(`s < tᵢ`): `timeRect i s = ∅`, so the RHS is `0`; pull out `ξᵢ` at `ℱ_{tᵢ}`, use the
future conditional mean-zero, then the tower property to `ℱ_s`. -/
lemma simpleIntegral_term_condExp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω
        | (LevyStochCalc.Poisson.naturalFiltration N).seq s]
      =ᵐ[P] fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have hξmeas : Measurable (φ.ξ i) := φ.ξ_measurable i
  have hpc_lt_ps : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  have hAfin := φ.A_finite i
  have hAmeas := φ.A_measurable i
  have hξÑ_int : ∀ B : Set (ℝ × E), MeasurableSet B →
      LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ →
      MeasureTheory.Integrable ((φ.ξ i) * fun ω => N.compensated B ω) P := by
    intro B hBmeas hBfin
    refine MeasureTheory.Integrable.bdd_mul (compensated_integrable N hBmeas hBfin)
      hξmeas.aestronglyMeasurable (c := |M|) ?_
    filter_upwards with ω; rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self _)
  change P[(φ.ξ i) * fun ω => N.compensated (φ.timeRect i t) ω | ℱ.seq s]
    =ᵐ[P] (φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω
  by_cases hpc_s : φ.partition i.castSucc ≤ s
  · -- Case A
    have hs_nn : 0 ≤ s := hpc_nn.trans hpc_s
    have hξ_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (φ.ξ i) :=
      h_adapt_i.mono (ℱ.mono hpc_s)
    have h_min_pc_s : min (φ.partition i.castSucc) s = φ.partition i.castSucc := min_eq_left hpc_s
    have h_min_pc_t : min (φ.partition i.castSucc) t = φ.partition i.castSucc :=
      min_eq_left (hpc_s.trans hst)
    set bs := min (φ.partition i.succ) s with hbs
    set bt := min (φ.partition i.succ) t with hbt
    have hpc_le_bs : φ.partition i.castSucc ≤ bs := le_min hpc_lt_ps.le hpc_s
    have hbs_le_bt : bs ≤ bt := min_le_min (le_refl _) hst
    set newset : Set (ℝ × E) := Set.Ioc bs bt ×ˢ φ.A i with hnew
    have h_rect_s : φ.timeRect i s = Set.Ioc (φ.partition i.castSucc) bs ×ˢ φ.A i := by
      rw [SimplePredictable.timeRect, h_min_pc_s]
    have h_rect_t : φ.timeRect i t = Set.Ioc (φ.partition i.castSucc) bt ×ˢ φ.A i := by
      rw [SimplePredictable.timeRect, h_min_pc_t]
    have h_union : φ.timeRect i t = φ.timeRect i s ∪ newset := by
      rw [h_rect_t, h_rect_s, hnew, ← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc hpc_le_bs hbs_le_bt]
    have hrect_s_meas : MeasurableSet (φ.timeRect i s) := by
      rw [h_rect_s]; exact measurableSet_Ioc.prod hAmeas
    have hnew_meas : MeasurableSet newset := by rw [hnew]; exact measurableSet_Ioc.prod hAmeas
    have h_disj : Disjoint (φ.timeRect i s) newset := by
      rw [h_rect_s, hnew]
      exact Set.disjoint_left.mpr (fun p hp1 hp2 => absurd hp2.1.1 (not_lt.mpr hp1.1.2))
    have hrect_s_fin : LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i s) ≠ ⊤ :=
      h_rect_s ▸ referenceIntensity_Ioc_prod_ne_top hAfin
    have hnew_fin : LevyStochCalc.Poisson.referenceIntensity ν newset ≠ ⊤ := by
      rw [hnew]; exact referenceIntensity_Ioc_prod_ne_top hAfin
    have hcompadd : (fun ω => N.compensated (φ.timeRect i t) ω) =ᵐ[P]
        (fun ω => N.compensated (φ.timeRect i s) ω) + fun ω => N.compensated newset ω :=
      h_union ▸ compensated_union_ae N hrect_s_meas hnew_meas h_disj hrect_s_fin hnew_fin
    have hsplit : ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i t) ω) =ᵐ[P]
        ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω)
          + (φ.ξ i) * fun ω => N.compensated newset ω := by
      filter_upwards [hcompadd] with ω hω
      simp only [Pi.mul_apply, Pi.add_apply] at hω ⊢
      rw [hω]; ring
    refine (MeasureTheory.condExp_congr_ae hsplit).trans ?_
    have hint_s := hξÑ_int (φ.timeRect i s) hrect_s_meas hrect_s_fin
    have hint_new := hξÑ_int newset hnew_meas hnew_fin
    refine (MeasureTheory.condExp_add hint_s hint_new (ℱ.seq s)).trans ?_
    have hself := MeasureTheory.condExp_of_stronglyMeasurable (ℱ.le' s)
      (show @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω) from
        simpleIntegral_term_adapted_compensated N φ i s h_adapt_i) hint_s
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
      (m := ℱ.seq s) hξ_Fs hint_new (compensated_integrable N hnew_meas hnew_fin)
    have hnew_zero : P[fun ω => N.compensated newset ω | ℱ.seq s] =ᵐ[P] fun _ => (0 : ℝ) := by
      refine compensated_condExp_Ioc_eq_zero N hs_nn hbs_le_bt (fun hlt => ?_) hAmeas hAfin
      have hps_gt : s < φ.partition i.succ := by
        by_contra hle; push_neg at hle
        rw [hbs, hbt, min_eq_left hle, min_eq_left (hle.trans hst)] at hlt
        exact lt_irrefl _ hlt
      rw [hbs]; exact (min_eq_right hps_gt.le).ge
    rw [hself]
    filter_upwards [hpull, hnew_zero] with ω hp hz
    simp only [Pi.add_apply, Pi.mul_apply] at hp ⊢
    rw [hp, hz]; ring
  · -- Case B
    push_neg at hpc_s
    have h_rect_s_empty : φ.timeRect i s = ∅ := by
      rw [SimplePredictable.timeRect, min_eq_right hpc_s.le,
        min_eq_right (hpc_s.le.trans hpc_lt_ps.le), Set.Ioc_self, Set.empty_prod]
    have h_rhs_zero : ((φ.ξ i) * fun ω => N.compensated (φ.timeRect i s) ω) = fun _ => (0 : ℝ) := by
      funext ω; simp only [Pi.mul_apply]; rw [h_rect_s_empty]
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated; simp
    rw [h_rhs_zero]
    have hrect_t_meas : MeasurableSet (φ.timeRect i t) := by
      rw [SimplePredictable.timeRect]; exact measurableSet_Ioc.prod hAmeas
    have hrect_t_fin := referenceIntensity_timeRect_ne_top φ i t
    set gt : Ω → ℝ := fun ω => N.compensated (φ.timeRect i t) ω with hgt
    set ft : Ω → ℝ := (φ.ξ i) * gt with hft
    have hpull : P[ft | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P]
        (φ.ξ i) * P[gt | ℱ.seq (φ.partition i.castSucc)] :=
      MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := ℱ.seq (φ.partition i.castSucc)) h_adapt_i
        (hξÑ_int (φ.timeRect i t) hrect_t_meas hrect_t_fin)
        (compensated_integrable N hrect_t_meas hrect_t_fin)
    have ht_zero : P[gt | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P] fun _ => (0 : ℝ) := by
      rw [hgt, SimplePredictable.timeRect]
      refine compensated_condExp_Ioc_eq_zero N hpc_nn
        (min_le_min hpc_lt_ps.le (le_refl t)) (fun hlt => ?_) hAmeas hAfin
      have hpct : φ.partition i.castSucc ≤ t := by
        by_contra h; push_neg at h
        rw [min_eq_right h.le, min_eq_right (h.le.trans hpc_lt_ps.le)] at hlt
        exact lt_irrefl _ hlt
      exact le_min (le_refl _) hpct
    have hpc_eq_zero : P[ft | ℱ.seq (φ.partition i.castSucc)] =ᵐ[P] fun _ => (0 : ℝ) := by
      filter_upwards [hpull, ht_zero] with ω hp hz
      rw [hp]; simp only [Pi.mul_apply]; rw [hz]; ring
    have hm₂pc := ℱ.le' (φ.partition i.castSucc)
    haveI : SigmaFinite (P.trim hm₂pc) := inferInstance
    have htower := MeasureTheory.condExp_condExp_of_le (μ := P) (f := ft)
      (ℱ.mono hpc_s.le) hm₂pc
    refine htower.symm.trans ((MeasureTheory.condExp_congr_ae hpc_eq_zero).trans ?_)
    exact Filter.EventuallyEq.of_eq (MeasureTheory.condExp_const (ℱ.le' s) (0 : ℝ))

/-- **Martingale property of `simpleIntegral` (compensated Poisson).** For an
adapted simple predictable integrand `φ`, the process `t ↦ simpleIntegral N φ t`
is a martingale wrt the natural filtration of `N`.

Proof: `simpleIntegral N φ t = ∑_i ξ_i · Ñ(timeRect i t)`. Adaptedness is
`simpleIntegral_stronglyAdapted_compensated`; the cond-exp identity reduces to the
per-term identity `simpleIntegral_term_condExp_compensated` via `condExp_finsetSum`
+ `eventuallyEq_sum`. -/
lemma martingale_simpleIntegral_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral N φ t)
      (LevyStochCalc.Poisson.naturalFiltration N) P := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  refine ⟨simpleIntegral_stronglyAdapted_compensated N φ h_adapt, ?_⟩
  intro s t hst
  have h_unfold_pi : ∀ u : ℝ, (fun ω => simpleIntegral N φ u ω) =
      ∑ i : Fin φ.N, (fun ω : Ω => φ.ξ i ω * N.compensated (φ.timeRect i u) ω) := by
    intro u; ext ω; rw [Finset.sum_apply]; rfl
  change P[fun ω => simpleIntegral N φ t ω | ℱ.seq s] =ᵐ[P]
    fun ω => simpleIntegral N φ s ω
  rw [h_unfold_pi t, h_unfold_pi s]
  have h_int : ∀ i ∈ (Finset.univ : Finset (Fin φ.N)),
      MeasureTheory.Integrable
        (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) P :=
    fun i _ => simpleIntegral_term_integrable_compensated N φ i t
  refine (MeasureTheory.condExp_finsetSum h_int (m := ℱ.seq s)).trans ?_
  refine eventuallyEq_sum ?_
  intro i _
  exact simpleIntegral_term_condExp_compensated N φ i (h_adapt i) hst

/-! ### Clamped compensator

The compensator of the quadratic variation, `∫₀ᵗ ∫_E |φ(s,e)|² ν(de) ds`, in its
explicit clamped form `∑_i (referenceIntensity ν (timeRect i t)) · ξᵢ²`. -/

/-- The clamped time-interval `Ioc pc ps ∩ Icc 0 t` (the part of a full
time-interval visible up to running time `t`) equals `Ioc (min pc t) (min ps t)`,
when `0 ≤ pc`. -/
lemma Ioc_inter_Icc_eq_Ioc_min {pc ps t : ℝ} (hpc : 0 ≤ pc) :
    Set.Ioc pc ps ∩ Set.Icc 0 t = Set.Ioc (min pc t) (min ps t) := by
  ext x
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
  constructor
  · rintro ⟨⟨hpcx, hxps⟩, _, hxt⟩
    exact ⟨lt_of_le_of_lt (min_le_left _ _) hpcx, le_min hxps hxt⟩
  · rintro ⟨hmin, hx_min⟩
    have hxt : x ≤ t := hx_min.trans (min_le_right _ _)
    have hpcx : pc < x := (min_lt_iff.mp hmin).resolve_right (not_lt.mpr hxt)
    exact ⟨⟨hpcx, hx_min.trans (min_le_left _ _)⟩, le_of_lt (lt_of_le_of_lt hpc hpcx), hxt⟩

/-- The reference intensity of a clamped time-rectangle, evaluated explicitly:
`referenceIntensity ν (timeRect i t) = ENNReal.ofReal (min tᵢ₊₁ t − min tᵢ t) · ν(Aᵢ)`
for `0 ≤ t` (so both clamp points are `≥ 0`). -/
lemma referenceIntensity_timeRect_eq
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) {t : ℝ} (ht : 0 ≤ t) :
    LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t)
      = ENNReal.ofReal (min (φ.partition i.succ) t - min (φ.partition i.castSucc) t)
          * ν (φ.A i) := by
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  unfold SimplePredictable.timeRect LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod]
  congr 1
  have h_subset : Set.Ioc (min (φ.partition i.castSucc) t) (min (φ.partition i.succ) t)
      ⊆ Set.Ici (0 : ℝ) :=
    fun x hx => (le_min hpc_nn ht).trans (le_of_lt hx.1)
  rw [MeasureTheory.Measure.restrict_apply measurableSet_Ioc, Set.inter_eq_left.mpr h_subset,
    Real.volume_Ioc]

/-- The clamped double-lintegral of the constant-indicator on `fullRect i` over
`[0, t] × E` equals `c · referenceIntensity ν (timeRect i t)`. Clamped analogue of
`SimplePredictable.lintegral_indicator_fullRect`. -/
lemma lintegral_indicator_fullRect_clamped
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (c : ℝ≥0∞) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e) ∂ν ∂volume
      = c * LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t) := by
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  rw [MeasureTheory.lintegral_lintegral
    (f := fun s e => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (s, e))
    (Measurable.indicator measurable_const h_meas_fullRect).aemeasurable]
  rw [show (fun (z : ℝ × E) => (φ.fullRect i).indicator (fun _ : ℝ × E => c) (z.1, z.2))
        = (φ.fullRect i).indicator (fun _ : ℝ × E => c) from by funext z; rfl]
  rw [MeasureTheory.lintegral_indicator_const h_meas_fullRect]
  rw [referenceIntensity_timeRect_eq φ i ht]
  unfold SimplePredictable.fullRect
  rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.restrict_apply measurableSet_Ioc,
    Ioc_inter_Icc_eq_Ioc_min hpc_nn, Real.volume_Ioc]

/-- **Clamped inner double-lintegral of `‖φ.eval‖²`** over `[0, t] × E`:
`∫₀ᵗ ∫_E ‖φ.eval s e ω‖² ∂ν ∂s = ∑_i ‖ξᵢ ω‖² · referenceIntensity ν (timeRect i t)`.
Clamped analogue of `SimplePredictable.lintegral_eval_sq`. -/
lemma lintegral_eval_sq_clamped
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∑ i : Fin φ.N,
        (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2
          * LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t) := by
  simp_rw [SimplePredictable.eval_sq_eq_sum_indicator φ _ _ ω]
  have h_inner_meas : ∀ s : ℝ, ∀ i : Fin φ.N,
      Measurable (fun e : E =>
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e)) := by
    intro s i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    exact (Measurable.indicator measurable_const h_meas_fullRect).comp measurable_prodMk_left
  rw [show (fun s : ℝ => ∫⁻ e, ∑ i : Fin φ.N,
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν)
        = (fun s : ℝ => ∑ i : Fin φ.N, ∫⁻ e,
            (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν) from by
    funext s
    exact MeasureTheory.lintegral_finsetSum _ (fun i _ => h_inner_meas s i)]
  have h_outer_meas : ∀ i : Fin φ.N,
      Measurable (fun s : ℝ => ∫⁻ e,
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e) ∂ν) := by
    intro i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    exact (Measurable.indicator measurable_const h_meas_fullRect).lintegral_prod_right'
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => h_outer_meas i)]
  exact Finset.sum_congr rfl (fun i _ => lintegral_indicator_fullRect_clamped φ i _ ht)

/-- The simple integrand `eval`, as a function of the mark `e` (with `s`, `ω`
fixed), is measurable: it is a finite sum of indicators of the measurable mark
sets `Aᵢ` (cut by whether `s` lies in the `i`-th time interval). -/
lemma eval_mark_measurable
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (ω : Ω) :
    Measurable (fun e : E => φ.eval s e ω) := by
  simp_rw [SimplePredictable.eval_eq_sum_indicator φ s _ ω]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  exact (Measurable.indicator measurable_const h_meas_fullRect).comp measurable_prodMk_left

/-- The inner mark-integral `∫⁻_E ‖φ.eval s e ω‖² ∂ν`, as an explicit function of
the running time `s`: `∑_i 1_{(tᵢ, tᵢ₊₁]}(s) · ‖ξᵢ ω‖² · ν(Aᵢ)`. Measurable in `s`
and finite at each `s`. -/
lemma inner_lintegral_eval_sq_eq
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (ω : Ω) :
    ∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν
      = ∑ i : Fin φ.N,
        (Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ)).indicator
          (fun _ => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 * ν (φ.A i)) s := by
  simp_rw [SimplePredictable.eval_sq_eq_sum_indicator φ s _ ω]
  have h_inner_meas : ∀ i : Fin φ.N,
      Measurable (fun e : E =>
        (φ.fullRect i).indicator (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e)) := by
    intro i
    have h_meas_fullRect : MeasurableSet (φ.fullRect i) := by
      unfold SimplePredictable.fullRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    exact (Measurable.indicator measurable_const h_meas_fullRect).comp measurable_prodMk_left
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => h_inner_meas i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases hs : s ∈ Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ)
  · rw [Set.indicator_of_mem hs]
    rw [show (fun e : E => (φ.fullRect i).indicator
          (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e))
        = (φ.A i).indicator (fun _ : E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) from by
      funext e
      by_cases he : e ∈ φ.A i
      · rw [Set.indicator_of_mem he, Set.indicator_of_mem
          (show (s, e) ∈ φ.fullRect i from Set.mem_prod.mpr ⟨hs, he⟩)]
      · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem
          (show (s, e) ∉ φ.fullRect i from fun hmem => he (Set.mem_prod.mp hmem).2)]]
    rw [MeasureTheory.lintegral_indicator_const (φ.A_measurable i)]
  · rw [Set.indicator_of_notMem hs]
    rw [show (fun e : E => (φ.fullRect i).indicator
          (fun _ : ℝ × E => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2) (s, e)) = fun _ => 0 from by
      funext e
      rw [Set.indicator_of_notMem (show (s, e) ∉ φ.fullRect i from
        fun hmem => hs (Set.mem_prod.mp hmem).1)]]
    simp

/-- The inner mark-integral `∫⁻_E ‖φ.eval s e ω‖² ∂ν` is finite at each `s`
(each summand is bounded by `‖ξᵢ ω‖² · ν(Aᵢ) < ⊤`). -/
lemma inner_lintegral_eval_sq_ne_top
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (s : ℝ) (ω : Ω) :
    ∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤ := by
  rw [inner_lintegral_eval_sq_eq φ s ω]
  refine (ENNReal.sum_lt_top.mpr (fun i _ => ?_)).ne
  refine lt_of_le_of_lt (Set.indicator_le_self _ _ s) ?_
  exact ENNReal.mul_lt_top (by simp) (lt_top_iff_ne_top.mpr (φ.A_finite i))

/-- Measurability of the inner mark-integral as a function of running time `s`. -/
lemma measurable_inner_lintegral_eval_sq
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    Measurable (fun s : ℝ => ∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
  simp_rw [inner_lintegral_eval_sq_eq φ _ ω]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (measurable_const.indicator measurableSet_Ioc)

/-- **Clamped compensator, Bochner form.** For `0 ≤ t`,
`∫₀ᵗ ∫_E (φ.eval s e ω)² ∂ν ∂s = ∑_i (referenceIntensity ν (timeRect i t)).toReal · ξᵢ²`.
Bochner analogue of `lintegral_eval_sq_clamped`: convert both the inner mark-integral
and the outer time-integral to lintegrals (both integrands are nonnegative; the inner
mark-lintegral is finite by `inner_lintegral_eval_sq_ne_top`), apply
`lintegral_eval_sq_clamped`, and take `toReal`. This is the explicit form of the
quadratic-variation compensator. -/
lemma setIntegral_eval_sq_Icc_clamped
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (ω : Ω) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ.eval s e ω) ^ 2 ∂ν ∂volume
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i t)).toReal
          * (φ.ξ i ω) ^ 2 := by
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm_eq_enorm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  -- Inner mark-integral as a `toReal` of the inner lintegral.
  have hg_eq : ∀ s : ℝ, ∫ e, (φ.eval s e ω) ^ 2 ∂ν
      = (∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal := by
    intro s
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall (fun e => sq_nonneg _))
      ((eval_mark_measurable φ s ω).pow_const 2).aestronglyMeasurable]
    congr 1
    exact lintegral_congr (fun e => (h_norm_sq _).symm)
  -- Outer time-integral as a `toReal` of the outer lintegral.
  rw [show (fun s : ℝ => ∫ e, (φ.eval s e ω) ^ 2 ∂ν)
        = (fun s : ℝ => (∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) from funext hg_eq]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall (fun s => ENNReal.toReal_nonneg))
    (measurable_inner_lintegral_eval_sq φ ω).ennreal_toReal.aestronglyMeasurable.restrict]
  rw [show (fun s : ℝ => ENNReal.ofReal (∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal)
        = (fun s : ℝ => ∫⁻ e, (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν) from funext (fun s =>
      ENNReal.ofReal_toReal (inner_lintegral_eval_sq_ne_top φ s ω))]
  rw [lintegral_eval_sq_clamped φ ω ht]
  rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top (by simp)
    (referenceIntensity_timeRect_ne_top φ i t))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ENNReal.toReal_mul, mul_comm]
  congr 1
  rw [h_norm_sq, ENNReal.toReal_ofReal (sq_nonneg _)]

/-! ### Increment decomposition

The increment `simpleIntegral t − simpleIntegral s` decomposes (a.e.) over the
increment rectangles `timeRect i t \ timeRect i s`, the basis for the set-level
quadratic-variation isometry. -/

/-- For `s ≤ t`, the clamped time-rectangle at `s` is contained in the one at `t`.
(Whenever the `s`-rectangle is non-empty in time, `tᵢ ≤ s`, so the lower clamp
points coincide.) -/
lemma timeRect_subset
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) {s t : ℝ} (hst : s ≤ t) :
    φ.timeRect i s ⊆ φ.timeRect i t := by
  unfold SimplePredictable.timeRect
  refine Set.prod_mono ?_ (Set.Subset.refl _)
  intro x hx
  obtain ⟨hlo, hhi⟩ := Set.mem_Ioc.mp hx
  refine Set.mem_Ioc.mpr ⟨?_, hhi.trans (min_le_min (le_refl _) hst)⟩
  by_cases hpc_s : φ.partition i.castSucc ≤ s
  · rw [min_eq_left (hpc_s.trans hst)]
    rwa [min_eq_left hpc_s] at hlo
  · push_neg at hpc_s
    exfalso
    have hps : φ.partition i.castSucc < φ.partition i.succ :=
      φ.partition_strictMono Fin.castSucc_lt_succ
    rw [min_eq_right hpc_s.le] at hlo
    rw [min_eq_right (hpc_s.trans hps).le] at hhi
    exact absurd (lt_of_lt_of_le hlo hhi) (lt_irrefl s)

/-- **Increment decomposition (a.e.).** For `s ≤ t`,
`simpleIntegral N φ t − simpleIntegral N φ s =ᵐ ∑_i ξᵢ · Ñ(timeRect i t \ timeRect i s)`.
The compensated mass of `timeRect i t` splits (a.e.) over the disjoint union
`timeRect i s ∪ (timeRect i t \ timeRect i s)` (`compensated_union_ae`); the `ξᵢ`-weighted
telescoping then leaves the increment-rectangle masses. -/
lemma simpleIntegral_sub_eq_increment_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {s t : ℝ} (hst : s ≤ t) :
    (fun ω => simpleIntegral N φ t ω - simpleIntegral N φ s ω)
      =ᵐ[P] fun ω => ∑ i : Fin φ.N,
        φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω := by
  have h_per_term : ∀ i : Fin φ.N,
      (fun ω => N.compensated (φ.timeRect i t) ω) =ᵐ[P]
        fun ω => N.compensated (φ.timeRect i s) ω
          + N.compensated (φ.timeRect i t \ φ.timeRect i s) ω := by
    intro i
    have hsub := timeRect_subset φ i hst
    have hmeas_s : MeasurableSet (φ.timeRect i s) := by
      rw [SimplePredictable.timeRect]; exact measurableSet_Ioc.prod (φ.A_measurable i)
    have hmeas_t : MeasurableSet (φ.timeRect i t) := by
      rw [SimplePredictable.timeRect]; exact measurableSet_Ioc.prod (φ.A_measurable i)
    have hmeas_d : MeasurableSet (φ.timeRect i t \ φ.timeRect i s) := hmeas_t.diff hmeas_s
    have hunion : φ.timeRect i s ∪ (φ.timeRect i t \ φ.timeRect i s) = φ.timeRect i t :=
      Set.union_diff_cancel hsub
    have hdisj : Disjoint (φ.timeRect i s) (φ.timeRect i t \ φ.timeRect i s) :=
      Set.disjoint_left.mpr (fun x hx hxd => hxd.2 hx)
    have hfin_d : LevyStochCalc.Poisson.referenceIntensity ν
        (φ.timeRect i t \ φ.timeRect i s) ≠ ⊤ :=
      ne_top_of_le_ne_top (referenceIntensity_timeRect_ne_top φ i t) (measure_mono Set.diff_subset)
    have h := compensated_union_ae N hmeas_s hmeas_d hdisj
      (referenceIntensity_timeRect_ne_top φ i s) hfin_d
    rwa [hunion] at h
  have h_all : ∀ᵐ ω ∂P, ∀ i : Fin φ.N,
      N.compensated (φ.timeRect i t) ω = N.compensated (φ.timeRect i s) ω
        + N.compensated (φ.timeRect i t \ φ.timeRect i s) ω :=
    (MeasureTheory.ae_all_iff).mpr h_per_term
  filter_upwards [h_all] with ω hω
  unfold simpleIntegral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hω i]; ring

/-- `Ioc a B \ Ioc a c = Ioc c B` when `a ≤ c`. -/
lemma Ioc_diff_Ioc_left_eq {a c B : ℝ} (hac : a ≤ c) :
    Set.Ioc a B \ Set.Ioc a c = Set.Ioc c B := by
  ext x
  simp only [Set.mem_diff, Set.mem_Ioc, not_and, not_le]
  constructor
  · rintro ⟨⟨hax, hxB⟩, h2⟩
    exact ⟨h2 hax, hxB⟩
  · rintro ⟨hcx, hxB⟩
    exact ⟨⟨lt_of_le_of_lt hac hcx, hxB⟩, fun _ => hcx⟩

/-- **The increment rectangle is a clean box.** For `0 ≤ s ≤ t`,
`timeRect i t \ timeRect i s = Ioc (max s (min tᵢ t)) (max s (min tᵢ₊₁ t)) ×ˢ Aᵢ`.
This is the compensated analogue of the Brownian clamped increment
`W(max s (min tᵢ₊₁ t)) − W(max s (min tᵢ t))`; expressing the set-difference as a
box lets the future-increment independence (`joint_past_future_independent`) apply. -/
lemma timeRect_sdiff_eq_box
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    φ.timeRect i t \ φ.timeRect i s
      = Set.Ioc (max s (min (φ.partition i.castSucc) t))
          (max s (min (φ.partition i.succ) t)) ×ˢ φ.A i := by
  have hpc_nn : 0 ≤ φ.partition i.castSucc := by
    have := φ.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [φ.partition_zero] at this
  have hpc_ps : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  rw [SimplePredictable.timeRect, SimplePredictable.timeRect, Set.prod_diff_prod,
    Set.diff_self, Set.prod_empty, Set.empty_union]
  congr 1
  set pc := φ.partition i.castSucc
  set ps := φ.partition i.succ
  by_cases hpc_s : pc ≤ s
  · -- `tᵢ ≤ s`: lower clamps coincide at `tᵢ`; the `s`-rectangle's top is `min ps s`.
    rw [min_eq_left hpc_s, min_eq_left (hpc_s.trans hst), max_eq_left hpc_s]
    by_cases hsps : s ≤ ps
    · rw [min_eq_right hsps, max_eq_right (le_min hsps hst),
        Ioc_diff_Ioc_left_eq hpc_s]
    · push_neg at hsps
      rw [min_eq_left hsps.le, min_eq_left (hsps.le.trans hst), max_eq_left hsps.le,
        Set.diff_self, Set.Ioc_self]
  · -- `s < tᵢ`: the `s`-rectangle is empty; clamps reduce to the `t`-rectangle.
    push_neg at hpc_s
    rw [min_eq_right hpc_s.le, min_eq_right (hpc_s.le.trans hpc_ps.le),
      Set.Ioc_self, Set.diff_empty,
      max_eq_right (le_min hpc_s.le hst),
      max_eq_right (le_min (hpc_s.trans hpc_ps).le hst)]

/-! ### Set-level quadratic-variation isometry

The increment squares onto the increment boxes; off-diagonal cross terms vanish
(independence + zero mean), and diagonal terms give the box intensities
(independence + `compensated_second_moment`). -/

/-- **Past-independence of a future box increment.** For a box `B = Ioc a b ×ˢ A`
(`0 ≤ a`, `A` measurable with finite `ν`-mass) and any `f` measurable w.r.t. the
"past at `a`" σ-algebra, `f` and `Ñ(B)` are independent. Repackages
`joint_past_future_independent` at the level of `IndepFun`. -/
lemma indepFun_past_compensated_box
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAf : ν A ≠ ⊤)
    {f : Ω → ℝ}
    (hf : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic a ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) f) :
    ProbabilityTheory.IndepFun f (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) P := by
  have h_box_meas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hf_comap_le :
      MeasurableSpace.comap f inferInstance ≤
        ⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic a ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N.N ω B) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact hf.measurable hv
  have hÑ_comap_le :
      MeasurableSpace.comap (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc a b ×ˢ A)) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨(fun x : ℝ≥0∞ => x.toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal) ⁻¹' v, ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · ext ω; rfl
  rw [ProbabilityTheory.IndepFun_iff]
  intro u v hu hv
  have h_indep := N.joint_past_future_independent ha hab hA hAf
  rw [ProbabilityTheory.Indep_iff] at h_indep
  exact h_indep u v (hf_comap_le u hu) (hÑ_comap_le v hv)

/-- **Diagonal increment second moment (weighted).** For an adapted `ξᵢ`, an
`ℱ_s`-measurable weight `g`, and `0 ≤ s ≤ t` in the genuine case (the clamped
increment box is non-degenerate), `∫ (g·ξᵢ²)·Ñ(Rᵢ)² = (∫ g·ξᵢ²)·ν̂(Rᵢ).toReal`,
where `Rᵢ = timeRect i t \ timeRect i s`. By `timeRect_sdiff_eq_box` the increment
is a box in the future of its lower clamp `a = max s (min tᵢ t)`; `g·ξᵢ²` is
`ℱ_a`-measurable, so it is independent of `Ñ(Rᵢ)²`; the mean of `Ñ(Rᵢ)²` is
`ν̂(Rᵢ).toReal` (`compensated_second_moment`). -/
lemma diagonal_increment_sq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i))
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq s) g)
    (h_genuine : max s (min (φ.partition i.castSucc) t) < max s (min (φ.partition i.succ) t)) :
    ∫ ω, (g ω * (φ.ξ i ω) ^ 2) * (N.compensated (φ.timeRect i t \ φ.timeRect i s) ω) ^ 2 ∂P
      = (∫ ω, g ω * (φ.ξ i ω) ^ 2 ∂P)
          * (LevyStochCalc.Poisson.referenceIntensity ν
              (φ.timeRect i t \ φ.timeRect i s)).toReal := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  set pc := φ.partition i.castSucc with hpc
  set ps := φ.partition i.succ with hps
  set a := max s (min pc t) with ha_def
  set b := max s (min ps t) with hb_def
  have ha_nn : 0 ≤ a := hs.trans (le_max_left _ _)
  -- genuine ⟹ pc ≤ t ⟹ pc ≤ a.
  have hpc_le_t : pc ≤ t := by
    by_contra h; push_neg at h
    have hps_gt : pc < ps := φ.partition_strictMono Fin.castSucc_lt_succ
    rw [ha_def, hb_def, min_eq_right h.le, min_eq_right (h.le.trans hps_gt.le)] at h_genuine
    exact lt_irrefl _ h_genuine
  have hpc_le_a : pc ≤ a := by rw [ha_def, min_eq_left hpc_le_t]; exact le_max_right _ _
  have hbox : φ.timeRect i t \ φ.timeRect i s = Set.Ioc a b ×ˢ φ.A i :=
    timeRect_sdiff_eq_box φ i hs hst
  have hbox_meas : MeasurableSet (Set.Ioc a b ×ˢ φ.A i) := measurableSet_Ioc.prod (φ.A_measurable i)
  have hbox_fin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ φ.A i) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top (φ.A_finite i)
  -- `g·ξᵢ²` is `ℱ_a`-measurable.
  have hf_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq a)
      (fun ω => g ω * (φ.ξ i ω) ^ 2) := by
    have hg_a := hg.mono (ℱ.mono (le_max_left s (min pc t)))
    have hξ_a := h_adapt_i.mono (ℱ.mono hpc_le_a)
    exact hg_a.mul (by simpa [pow_two] using hξ_a.mul hξ_a)
  -- Independence of `g·ξᵢ²` and `Ñ(box)`.
  have h_indep : ProbabilityTheory.IndepFun (fun ω => g ω * (φ.ξ i ω) ^ 2)
      (fun ω => N.compensated (Set.Ioc a b ×ˢ φ.A i) ω) P :=
    indepFun_past_compensated_box N ha_nn h_genuine (φ.A_measurable i) (φ.A_finite i) hf_meas
  have h_indep_sq : ProbabilityTheory.IndepFun (fun ω => g ω * (φ.ξ i ω) ^ 2)
      (fun ω => (N.compensated (Set.Ioc a b ×ˢ φ.A i) ω) ^ 2) P :=
    h_indep.comp measurable_id (measurable_id.pow_const 2)
  rw [hbox]
  rw [h_indep_sq.integral_fun_mul_eq_mul_integral
    (by
      have hg_m : Measurable g := (hg.mono (ℱ.le' s)).measurable
      exact (hg_m.mul ((φ.ξ_measurable i).pow_const 2)).aestronglyMeasurable)
    (((ENNReal.measurable_toReal.comp
      (N.measurable_eval hbox_meas)).sub_const _).pow_const 2).aestronglyMeasurable]
  rw [compensated_second_moment N hbox_meas hbox_fin]

/-- **Off-diagonal increment vanishing (weighted).** For `i < j`, an `ℱ_s`-measurable
weight `g`, and `0 ≤ s ≤ t` in the genuine case for `j`,
`∫ g·(ξᵢ·Ñ(Rᵢ))·(ξⱼ·Ñ(Rⱼ)) = 0`. The factor `g·ξᵢ·Ñ(Rᵢ)·ξⱼ` is measurable w.r.t. the
past at `aⱼ = max s (min tⱼ t)` (since `Rᵢ`'s times are `≤ tⱼ ≤ aⱼ`), hence independent
of the future increment `Ñ(Rⱼ)`, whose mean is `0` (`compensated_mean_zero`). -/
lemma offDiagonal_increment_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {i j : Fin φ.N} (hij : i < j)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (φ.partition j.castSucc)) (φ.ξ j))
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq s) g)
    (h_genuine_j :
      max s (min (φ.partition j.castSucc) t) < max s (min (φ.partition j.succ) t)) :
    ∫ ω, g ω * ((φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω)
        * (φ.ξ j ω * N.compensated (φ.timeRect j t \ φ.timeRect j s) ω)) ∂P = 0 := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  set pcj := φ.partition j.castSucc with hpcj
  set psj := φ.partition j.succ with hpsj
  set aj := max s (min pcj t) with haj_def
  set bj := max s (min psj t) with hbj_def
  have haj_nn : 0 ≤ aj := hs.trans (le_max_left _ _)
  have hpcj_le_t : pcj ≤ t := by
    by_contra h; push_neg at h
    have hps_gt : pcj < psj := φ.partition_strictMono Fin.castSucc_lt_succ
    rw [haj_def, hbj_def, min_eq_right h.le, min_eq_right (h.le.trans hps_gt.le)] at h_genuine_j
    exact lt_irrefl _ h_genuine_j
  have hpcj_le_aj : pcj ≤ aj := by rw [haj_def, min_eq_left hpcj_le_t]; exact le_max_right _ _
  -- ps_i ≤ pc_j ≤ a_j, so R_i lies in the past of a_j.
  have hpsi_le_pcj : φ.partition i.succ ≤ pcj :=
    φ.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
  have hboxj : φ.timeRect j t \ φ.timeRect j s = Set.Ioc aj bj ×ˢ φ.A j :=
    timeRect_sdiff_eq_box φ j hs hst
  have hboxj_meas : MeasurableSet (Set.Ioc aj bj ×ˢ φ.A j) :=
    measurableSet_Ioc.prod (φ.A_measurable j)
  have hboxj_fin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc aj bj ×ˢ φ.A j) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top (φ.A_finite j)
  -- R_i ⊆ Iic a_j ×ˢ univ.
  have hsub_i : φ.timeRect i t \ φ.timeRect i s ⊆ Set.Iic aj ×ˢ Set.univ := by
    intro x hx
    have hx_t : x ∈ φ.timeRect i t := hx.1
    rw [SimplePredictable.timeRect, Set.mem_prod] at hx_t
    refine Set.mem_prod.mpr ⟨?_, Set.mem_univ _⟩
    exact (hx_t.1.2.trans (min_le_left _ _)).trans (hpsi_le_pcj.trans hpcj_le_aj)
  have hRi_meas : MeasurableSet (φ.timeRect i t \ φ.timeRect i s) :=
    (measurableSet_Ioc.prod (φ.A_measurable i)).diff (measurableSet_Ioc.prod (φ.A_measurable i))
  have hÑRi_a : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq aj)
      (fun ω => N.compensated (φ.timeRect i t \ φ.timeRect i s) ω) := by
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    exact (((LevyStochCalc.Poisson.measurable_random_measure_of_le N hsub_i
      hRi_meas).ennreal_toReal).sub measurable_const).stronglyMeasurable
  -- f := g·ξᵢ·Ñ(Rᵢ)·ξⱼ is past-at-aⱼ measurable.
  set f : Ω → ℝ := fun ω => g ω * φ.ξ i ω
      * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω * φ.ξ j ω with hf_def
  have hpci_le_aj : φ.partition i.castSucc ≤ aj :=
    (le_of_lt (φ.partition_strictMono Fin.castSucc_lt_succ)).trans (hpsi_le_pcj.trans hpcj_le_aj)
  have hf_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq aj) f := by
    have hg_a := hg.mono (ℱ.mono (le_max_left s (min pcj t)))
    have hξi_a := h_adapt_i.mono (ℱ.mono hpci_le_aj)
    have hξj_a := h_adapt_j.mono (ℱ.mono hpcj_le_aj)
    exact ((hg_a.mul hξi_a).mul hÑRi_a).mul hξj_a
  have h_indep : ProbabilityTheory.IndepFun f
      (fun ω => N.compensated (Set.Ioc aj bj ×ˢ φ.A j) ω) P :=
    indepFun_past_compensated_box N haj_nn h_genuine_j (φ.A_measurable j) (φ.A_finite j) hf_meas
  -- Factor the integrand as `f · Ñ(boxⱼ)` and apply independence.
  rw [hboxj]
  rw [show (fun ω => g ω * ((φ.ξ i ω * N.compensated (φ.timeRect i t \ φ.timeRect i s) ω)
        * (φ.ξ j ω * N.compensated (Set.Ioc aj bj ×ˢ φ.A j) ω)))
      = fun ω => f ω * N.compensated (Set.Ioc aj bj ×ˢ φ.A j) ω from by
    funext ω; rw [hf_def]; ring]
  have hf_m : Measurable f := by
    have hg_m : Measurable g := (hg.mono (ℱ.le' s)).measurable
    have hÑRi_m : Measurable (fun ω => N.compensated (φ.timeRect i t \ φ.timeRect i s) ω) := by
      unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
      exact (ENNReal.measurable_toReal.comp (N.measurable_eval hRi_meas)).sub_const _
    exact ((hg_m.mul (φ.ξ_measurable i)).mul hÑRi_m).mul (φ.ξ_measurable j)
  rw [h_indep.integral_fun_mul_eq_mul_integral hf_m.aestronglyMeasurable
    (((ENNReal.measurable_toReal.comp
      (N.measurable_eval hboxj_meas)).sub_const _).aestronglyMeasurable)]
  rw [compensated_mean_zero N hboxj_meas hboxj_fin, mul_zero]

end LevyStochCalc.Poisson.Compensated
