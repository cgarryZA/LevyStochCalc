import LevyStochCalc.Poisson.NaturalFiltration
import LevyStochCalc.Poisson.Compensated

/-!
# Martingale property of `simpleIntegral` against compensated Poisson

For a `PoissonRandomMeasure N` and an adapted `SimplePredictable` integrand
`φ`, the simple integral

  `t ↦ simpleIntegral N φ t = ∑_i ξ_i · Ñ(timeRect i t)`

is a martingale with respect to `naturalFiltration N`. Mirrors
`LevyStochCalc.Brownian.Ito.martingale_simpleIntegral_brownian`.

## Roadmap

* `compensated_integrable`: each `Ñ(B)` is `L¹(P)` for `B` with finite intensity.
* `condExp_compensated_increment_eq_zero`: `E[Ñ((s, t] × A) | F_s] = 0`
  via `condExp_indep_eq` + `compensated_mean_zero`.
* Per-term integrability / adaptedness / cond-exp identity, mirroring the
  Brownian B2 proof.
* `martingale_simpleIntegral_compensatedPoisson`: the headline.
-/

namespace LevyStochCalc.Poisson

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u v
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Summability of `r^n / n! · n` for `r ≥ 0`**, used for integrability of
`(n : ℝ)` w.r.t. `poissonMeasure r`. Re-proved here to keep this file
self-contained from `Compensated.lean`'s private helpers. -/
private lemma summable_pow_div_factorial_mul_nat_aux (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) := by
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    have h_eq : ∀ n : ℕ,
        r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)
          = r * (r ^ n / (n.factorial : ℝ)) := by
      intro n
      have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      rw [Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))
            = fun n => r * (r ^ n / (n.factorial : ℝ)) from funext h_eq]
    exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ

/-- **Integrability of `N.compensated B`** for `B` of finite reference intensity.
Pushforward to `poissonMeasure` + `integrable_poissonMeasure_iff` +
`summable_pow_div_factorial_mul_nat_aux`. -/
lemma compensated_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => N.compensated B ω) P := by
  set c : ℝ := (referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  -- Reduce to integrability of (N.N · B).toReal.
  show MeasureTheory.Integrable (fun ω => (N.N ω B).toReal - c) P
  refine MeasureTheory.Integrable.sub ?_ (MeasureTheory.integrable_const _)
  -- Pushforward through (N.N · B) and then through Nat.cast.
  rw [show (fun ω => (N.N ω B).toReal)
      = (fun x : ℝ≥0∞ => x.toReal) ∘ (fun ω => N.N ω B) from rfl]
  rw [← MeasureTheory.integrable_map_measure
    (μ := P) (f := fun ω => N.N ω B)
    ENNReal.measurable_toReal.aestronglyMeasurable h_NB_meas.aemeasurable]
  rw [N.poisson_law hB h_finite]
  change MeasureTheory.Integrable (fun x : ℝ≥0∞ => x.toReal)
    ((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞)))
  rw [MeasureTheory.integrable_map_measure
      (μ := ProbabilityTheory.poissonMeasure r) (f := fun n : ℕ => (n : ℝ≥0∞))
      ENNReal.measurable_toReal.aestronglyMeasurable measurable_from_nat.aemeasurable]
  have h_simp : ((fun x : ℝ≥0∞ => x.toReal) ∘ (fun n : ℕ => (n : ℝ≥0∞)))
              = fun n : ℕ => (n : ℝ) := by
    funext n; show ((n : ℝ≥0∞)).toReal = (n : ℝ); simp
  rw [h_simp]
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ, Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat_aux (↑r)).mul_left _

/-- **Cond-exp of a compensated-Poisson increment is zero.** For
`B = (s, t] × A` with `0 ≤ s < t` and `ν A < ∞`,
`E[Ñ(B) | F_s] =ᵐ 0`. Mirror of `condExp_increment_eq_zero_aux` for Brownian.

Combines `joint_past_future_independent` (σ-algebra independence) with
`compensated_mean_zero` (mean zero of the compensated measure) via
`condExp_indep_eq`. -/
lemma condExp_compensated_increment_eq_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {s t : ℝ} (hs_nn : 0 ≤ s) (hst : s < t)
    {A : Set E} (hA_meas : MeasurableSet A) (hA_finite : ν A ≠ ⊤) :
    P[fun ω => N.compensated (Set.Ioc s t ×ˢ A) ω | (naturalFiltration N).seq s]
      =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
  set B : Set (ℝ × E) := Set.Ioc s t ×ˢ A with hB_def
  have h_B_meas : MeasurableSet B := measurableSet_Ioc.prod hA_meas
  have h_B_finite : referenceIntensity ν B ≠ ⊤ := by
    unfold referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ hA_finite
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  -- Measurabilities.
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval h_B_meas
  have h_compensated_meas : Measurable (fun ω => N.compensated B ω) := by
    show Measurable (fun ω => (N.N ω B).toReal - (referenceIntensity ν B).toReal)
    exact (ENNReal.measurable_toReal.comp h_NB_meas).sub_const _
  -- σ(Ñ(B)) ≤ σ(N(B)).
  have h_compensated_comap_le_N_comap :
      MeasurableSpace.comap (fun ω => N.compensated B ω) inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance := by
    intro u hu
    obtain ⟨v, hv, hvu⟩ := hu
    refine ⟨(fun x : ℝ≥0∞ => x.toReal - (referenceIntensity ν B).toReal) ⁻¹' v, ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · rw [← hvu]; rfl
  -- σ(N(B)) ⊥ seq s = ⨆_{C ⊆ Iic s × univ} σ(N C).
  have h_indep_struct := N.joint_past_future_independent hs_nn hst hA_meas hA_finite
  -- Lift to σ(Ñ(B)) ⊥ seq s by mono_right.
  have h_indep_compensated : ProbabilityTheory.Indep
      ((naturalFiltration N).seq s)
      (MeasurableSpace.comap (fun ω => N.compensated B ω) inferInstance) P := by
    rw [ProbabilityTheory.Indep_iff] at h_indep_struct ⊢
    intro u v hu hv
    exact h_indep_struct u v hu (h_compensated_comap_le_N_comap v hv)
  -- Integrability and mean zero.
  have h_int : MeasureTheory.Integrable (fun ω => N.compensated B ω) P :=
    compensated_integrable N h_B_meas h_B_finite
  have h_mean : ∫ ω, N.compensated B ω ∂P = 0 :=
    LevyStochCalc.Poisson.Compensated.compensated_mean_zero N h_B_meas h_B_finite
  -- Apply condExp_indep_eq.
  have h_le_compensated : MeasurableSpace.comap (fun ω => N.compensated B ω) inferInstance
      ≤ ‹MeasurableSpace Ω› := by
    intro u hu
    obtain ⟨v, hv, hvu⟩ := hu
    rw [← hvu]
    exact h_compensated_meas hv
  have h_le_seq := (naturalFiltration N).le' s
  have h_compensated_sm : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (MeasurableSpace.comap (fun ω => N.compensated B ω) inferInstance)
      (fun ω => N.compensated B ω) := by
    apply Measurable.stronglyMeasurable
    exact Measurable.of_comap_le le_rfl
  have h := MeasureTheory.condExp_indep_eq h_le_compensated h_le_seq h_compensated_sm
    h_indep_compensated.symm
  filter_upwards [h] with ω hω
  rw [hω]
  exact h_mean

/-- **`N(·, B)` is a.s. finite** for `B` of finite reference intensity:
the Poisson law is supported on `ℕ ⊊ ℝ≥0∞`. -/
lemma N_finite_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, N.N ω B ≠ ⊤ := by
  set r : ℝ≥0 := (referenceIntensity ν B).toNNReal
  have h_law := N.poisson_law hB h_finite
  have h_top_meas : MeasurableSet ({⊤} : Set ℝ≥0∞) := measurableSet_singleton _
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_preimage_empty : (fun n : ℕ => (n : ℝ≥0∞)) ⁻¹' {⊤} = ∅ := by
    ext n; simp [ENNReal.natCast_ne_top]
  have h_NB_meas_to_ENN : Measurable (fun n : ℕ => (n : ℝ≥0∞)) := by fun_prop
  have h_map_top : (P.map (fun ω => N.N ω B)) {⊤} = 0 := by
    rw [h_law]
    show ((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞))) {⊤} = 0
    rw [MeasureTheory.Measure.map_apply h_NB_meas_to_ENN h_top_meas]
    rw [h_preimage_empty]
    exact MeasureTheory.measure_empty
  rw [MeasureTheory.Measure.map_apply h_NB_meas h_top_meas] at h_map_top
  rw [MeasureTheory.ae_iff]
  convert h_map_top using 2
  ext ω
  exact not_not

/-- **A.e. additivity of the compensated measure on disjoint sets.** For
measurable disjoint `B C` with finite intensities,
`Ñ(B ∪ C) = Ñ(B) + Ñ(C)` a.e. The exceptional set is the union of the
`{ω | N(ω, B) = ⊤}` and `{ω | N(ω, C) = ⊤}` sets, both `P`-null. -/
lemma compensated_add_disjoint_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hC : MeasurableSet C)
    (h_disj : Disjoint B C)
    (hB_fin : referenceIntensity ν B ≠ ⊤) (hC_fin : referenceIntensity ν C ≠ ⊤)
    (hB_meas : MeasurableSet B) :
    ∀ᵐ ω ∂P, N.compensated (B ∪ C) ω = N.compensated B ω + N.compensated C ω := by
  have h_NB_finite : ∀ᵐ ω ∂P, N.N ω B ≠ ⊤ := N_finite_ae N hB_meas hB_fin
  have h_NC_finite : ∀ᵐ ω ∂P, N.N ω C ≠ ⊤ := N_finite_ae N hC hC_fin
  filter_upwards [h_NB_finite, h_NC_finite] with ω h_NB h_NC
  show (N.N ω (B ∪ C)).toReal - (referenceIntensity ν (B ∪ C)).toReal
    = ((N.N ω B).toReal - (referenceIntensity ν B).toReal)
      + ((N.N ω C).toReal - (referenceIntensity ν C).toReal)
  have h_NN_add : N.N ω (B ∪ C) = N.N ω B + N.N ω C :=
    MeasureTheory.measure_union h_disj hC
  have h_int_add : referenceIntensity ν (B ∪ C)
      = referenceIntensity ν B + referenceIntensity ν C :=
    MeasureTheory.measure_union h_disj hC
  rw [h_NN_add, h_int_add]
  rw [ENNReal.toReal_add h_NB h_NC, ENNReal.toReal_add hB_fin hC_fin]
  ring

open LevyStochCalc.Poisson.Compensated in
/-- **Per-term integrability** for the compensated-Poisson `simpleIntegral`.
Bounded `ξ` × integrable `Ñ(timeRect i t)`. -/
lemma simpleIntegral_term_integrable_compensatedPoisson
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ) :
    MeasureTheory.Integrable
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) P := by
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have h_timeRect_meas : MeasurableSet (φ.timeRect i t) := by
    unfold SimplePredictable.timeRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_intensity_finite : referenceIntensity ν (φ.timeRect i t) ≠ ⊤ := by
    unfold SimplePredictable.timeRect referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have h_int_compensated : MeasureTheory.Integrable
      (fun ω => N.compensated (φ.timeRect i t) ω) P :=
    compensated_integrable N h_timeRect_meas h_intensity_finite
  refine MeasureTheory.Integrable.bdd_mul h_int_compensated
    (φ.ξ_measurable i).aestronglyMeasurable (c := |M|) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (hM ω).trans (le_abs_self _)

open LevyStochCalc.Poisson.Compensated in
/-- **Per-term `ℱ_t`-adaptedness** for the compensated-Poisson `simpleIntegral`.
For `t ≥ pre_t`, both factors are `ℱ_t`-meas; for `t < pre_t`,
`φ.timeRect i t = ∅` and the term collapses to `0`. -/
lemma simpleIntegral_term_adapted_compensatedPoisson
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) (t : ℝ)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((naturalFiltration N).seq t)
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) := by
  set ℱ := naturalFiltration N
  have hpre_lt_post : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  by_cases ht_pre : φ.partition i.castSucc ≤ t
  · -- pre_t ≤ t.
    have h_xi_Ft : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t) (φ.ξ i) :=
      h_adapt_i.mono (ℱ.mono ht_pre)
    have h_timeRect_meas : MeasurableSet (φ.timeRect i t) := by
      unfold SimplePredictable.timeRect
      exact measurableSet_Ioc.prod (φ.A_measurable i)
    have h_timeRect_subset : φ.timeRect i t ⊆ Set.Iic t ×ˢ Set.univ := by
      unfold SimplePredictable.timeRect
      intro x hx
      obtain ⟨hxt, _⟩ := Set.mem_prod.mp hx
      refine Set.mem_prod.mpr ⟨?_, Set.mem_univ _⟩
      exact (Set.mem_Ioc.mp hxt).2.trans (min_le_right _ _)
    have h_NN_meas : Measurable[ℱ.seq t] (fun ω => N.N ω (φ.timeRect i t)) :=
      measurable_random_measure_of_le N h_timeRect_subset h_timeRect_meas
    have h_compensated_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (fun ω => N.compensated (φ.timeRect i t) ω) := by
      show @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (fun ω => (N.N ω (φ.timeRect i t)).toReal
          - (referenceIntensity ν (φ.timeRect i t)).toReal)
      apply Measurable.stronglyMeasurable
      exact (ENNReal.measurable_toReal.comp h_NN_meas).sub_const _
    exact h_xi_Ft.mul h_compensated_meas
  · -- t < pre_t: timeRect = ∅, term = 0.
    push_neg at ht_pre
    have h_t_lt_post : t < φ.partition i.succ := lt_trans ht_pre hpre_lt_post
    have h_min_pre_t : min (φ.partition i.castSucc) t = t := min_eq_right (le_of_lt ht_pre)
    have h_min_post_t : min (φ.partition i.succ) t = t := min_eq_right (le_of_lt h_t_lt_post)
    have h_empty : φ.timeRect i t = ∅ := by
      unfold SimplePredictable.timeRect
      rw [h_min_pre_t, h_min_post_t]
      ext ⟨s, e⟩
      simp [Set.mem_Ioc]
    have h_zero : (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω)
        = (fun _ : Ω => (0 : ℝ)) := by
      funext ω
      rw [h_empty]
      show φ.ξ i ω * ((N.N ω ∅).toReal - (referenceIntensity ν ∅).toReal) = 0
      simp
    rw [h_zero]
    exact MeasureTheory.stronglyMeasurable_const

open LevyStochCalc.Poisson.Compensated in
/-- **Per-term cond-exp identity, `pre_t ≤ s` case (Case A).**
For `pre_t ≤ s ≤ t`,
`E[ξ_i · Ñ(timeRect i t) | F_s] =ᵐ ξ_i · Ñ(timeRect i s)`.

Proof: write `timeRect i t = timeRect i s ∪ ((s ∧ post_t, t ∧ post_t] × A_i)`
(disjoint). Apply `compensated_add_disjoint_ae` to get
`Ñ(timeRect i t) = Ñ(timeRect i s) + Ñ(increment) a.e`.
Then pull out `ξ_i` (`F_s`-meas since `pre_t ≤ s`); the increment cond-exp
is `0` either trivially (when `s ≥ post_t` so the increment is empty)
or by `condExp_compensated_increment_eq_zero` (when `s ≤ post_t` so
`s = s ∧ post_t`). -/
private lemma simpleIntegral_term_condExp_compensatedPoisson_main
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hpre_le_s : φ.partition i.castSucc ≤ s) (hst : s ≤ t) :
    P[fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω
        | (naturalFiltration N).seq s]
      =ᵐ[P] fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω := by
  set ℱ := naturalFiltration N
  have hpre_lt_post : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  have hpre_nn : 0 ≤ φ.partition i.castSucc := by
    have : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at this; exact this
  have hs_nn : 0 ≤ s := hpre_nn.trans hpre_le_s
  have hpre_le_t : φ.partition i.castSucc ≤ t := hpre_le_s.trans hst
  set s' : ℝ := min (φ.partition i.succ) s
  set t' : ℝ := min (φ.partition i.succ) t
  have hs'_le_s : s' ≤ s := min_le_right _ _
  have hs'_le_t' : s' ≤ t' := min_le_min (le_refl _) hst
  have hpre_le_s' : φ.partition i.castSucc ≤ s' := le_min hpre_lt_post.le hpre_le_s
  have hpre_le_t' : φ.partition i.castSucc ≤ t' := le_min hpre_lt_post.le hpre_le_t
  have h_timeRect_t_eq : φ.timeRect i t = Set.Ioc (φ.partition i.castSucc) t' ×ˢ φ.A i := by
    show Set.Ioc (min (φ.partition i.castSucc) t) (min (φ.partition i.succ) t) ×ˢ φ.A i = _
    rw [min_eq_left hpre_le_t]
  have h_timeRect_s_eq : φ.timeRect i s = Set.Ioc (φ.partition i.castSucc) s' ×ˢ φ.A i := by
    show Set.Ioc (min (φ.partition i.castSucc) s) (min (φ.partition i.succ) s) ×ˢ φ.A i = _
    rw [min_eq_left hpre_le_s]
  set B_inc : Set (ℝ × E) := Set.Ioc s' t' ×ˢ φ.A i
  have h_decomp : φ.timeRect i t = φ.timeRect i s ∪ B_inc := by
    rw [h_timeRect_t_eq, h_timeRect_s_eq]
    rw [show (Set.Ioc (φ.partition i.castSucc) t' ×ˢ φ.A i : Set (ℝ × E))
        = (Set.Ioc (φ.partition i.castSucc) s' ∪ Set.Ioc s' t') ×ˢ φ.A i from by
      rw [Set.Ioc_union_Ioc_eq_Ioc hpre_le_s' hs'_le_t']]
    rw [Set.union_prod]
  have h_disj : Disjoint (φ.timeRect i s) B_inc := by
    rw [h_timeRect_s_eq]
    refine Set.disjoint_iff.mpr ?_
    intro x ⟨hx1, hx2⟩
    obtain ⟨hxt1, _⟩ := Set.mem_prod.mp hx1
    obtain ⟨hxt2, _⟩ := Set.mem_prod.mp hx2
    obtain ⟨_, hxs⟩ := Set.mem_Ioc.mp hxt1
    obtain ⟨hxs', _⟩ := Set.mem_Ioc.mp hxt2
    exact absurd (lt_of_le_of_lt hxs hxs') (lt_irrefl _)
  have h_timeRect_t_meas : MeasurableSet (φ.timeRect i t) := by
    unfold SimplePredictable.timeRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_timeRect_s_meas : MeasurableSet (φ.timeRect i s) := by
    unfold SimplePredictable.timeRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_B_inc_meas : MeasurableSet B_inc := measurableSet_Ioc.prod (φ.A_measurable i)
  have h_intensity_finite_aux : ∀ {A : Set (ℝ × E)},
      A ⊆ Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ×ˢ φ.A i →
      referenceIntensity ν A ≠ ⊤ := by
    intro A hA_subset
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.measure_mono hA_subset)
    unfold referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have h_int_t_subset : φ.timeRect i t
      ⊆ Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ×ˢ φ.A i := by
    rw [h_timeRect_t_eq]
    exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl (min_le_left _ _)) Set.Subset.rfl
  have h_int_s_subset : φ.timeRect i s
      ⊆ Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ×ˢ φ.A i := by
    rw [h_timeRect_s_eq]
    exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl (min_le_left _ _)) Set.Subset.rfl
  have h_B_inc_subset : B_inc
      ⊆ Set.Ioc (φ.partition i.castSucc) (φ.partition i.succ) ×ˢ φ.A i := by
    refine Set.prod_mono ?_ Set.Subset.rfl
    refine Set.Ioc_subset_Ioc ?_ (min_le_left _ _)
    exact hpre_le_s'
  have h_int_t_finite := h_intensity_finite_aux h_int_t_subset
  have h_int_s_finite := h_intensity_finite_aux h_int_s_subset
  have h_B_inc_finite := h_intensity_finite_aux h_B_inc_subset
  -- Additivity (a.e.).
  have h_add_ae := compensated_add_disjoint_ae N h_B_inc_meas h_disj
    h_int_s_finite h_B_inc_finite h_timeRect_s_meas
  -- g_i(t) decomposition (a.e.).
  have h_g_decomp_ae : (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω)
        =ᵐ[P] (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω
                + φ.ξ i ω * N.compensated B_inc ω) := by
    filter_upwards [h_add_ae] with ω hω
    rw [h_decomp, hω]
    ring
  -- F_s-measurability of pieces.
  have h_xi_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (φ.ξ i) :=
    h_adapt_i.mono (ℱ.mono hpre_le_s)
  have h_timeRect_s_past : φ.timeRect i s ⊆ Set.Iic s ×ˢ Set.univ := by
    rw [h_timeRect_s_eq]
    intro x hx
    obtain ⟨hxt, _⟩ := Set.mem_prod.mp hx
    refine Set.mem_prod.mpr ⟨?_, Set.mem_univ _⟩
    exact (Set.mem_Ioc.mp hxt).2.trans hs'_le_s
  have h_NN_timeRect_s_Fs_meas :
      Measurable[ℱ.seq s] (fun ω => N.N ω (φ.timeRect i s)) :=
    measurable_random_measure_of_le N h_timeRect_s_past h_timeRect_s_meas
  have h_compensated_s_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
      (fun ω => N.compensated (φ.timeRect i s) ω) := by
    show @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
      (fun ω => (N.N ω (φ.timeRect i s)).toReal
        - (referenceIntensity ν (φ.timeRect i s)).toReal)
    apply Measurable.stronglyMeasurable
    exact (ENNReal.measurable_toReal.comp h_NN_timeRect_s_Fs_meas).sub_const _
  have h_g_s_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω) :=
    h_xi_Fs.mul h_compensated_s_Fs
  -- Integrabilities.
  have h_int_xi_meas : Measurable (φ.ξ i) := φ.ξ_measurable i
  have h_int_compensated_t : MeasureTheory.Integrable
      (fun ω => N.compensated (φ.timeRect i t) ω) P :=
    compensated_integrable N h_timeRect_t_meas h_int_t_finite
  have h_int_compensated_s : MeasureTheory.Integrable
      (fun ω => N.compensated (φ.timeRect i s) ω) P :=
    compensated_integrable N h_timeRect_s_meas h_int_s_finite
  have h_int_compensated_B_inc : MeasureTheory.Integrable
      (fun ω => N.compensated B_inc ω) P :=
    compensated_integrable N h_B_inc_meas h_B_inc_finite
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have h_xi_bound : ∀ᵐ ω ∂P, ‖φ.ξ i ω‖ ≤ |M| := by
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    exact (hM ω).trans (le_abs_self _)
  have h_int_g_s : MeasureTheory.Integrable
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω) P :=
    h_int_compensated_s.bdd_mul h_int_xi_meas.aestronglyMeasurable h_xi_bound
  have h_int_g_inc : MeasureTheory.Integrable
      (fun ω => φ.ξ i ω * N.compensated B_inc ω) P :=
    h_int_compensated_B_inc.bdd_mul h_int_xi_meas.aestronglyMeasurable h_xi_bound
  -- Cond-exp arithmetic.
  have h_le_F : ℱ.seq s ≤ ‹MeasurableSpace Ω› := ℱ.le' s
  have h_self_g_s := MeasureTheory.condExp_of_stronglyMeasurable h_le_F h_g_s_Fs h_int_g_s
  have h_condExp_t_eq := MeasureTheory.condExp_congr_ae (m := ℱ.seq s) (μ := P) h_g_decomp_ae
  have h_condExp_add := MeasureTheory.condExp_add h_int_g_s h_int_g_inc (ℱ.seq s)
  have h_pull_inc := MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
    (m := ℱ.seq s) (μ := P) (f := φ.ξ i) (g := fun ω => N.compensated B_inc ω)
    h_xi_Fs.aestronglyMeasurable h_int_g_inc h_int_compensated_B_inc
  -- E[Ñ(B_inc) | F_s] = 0.
  have h_inc_zero : P[fun ω => N.compensated B_inc ω | ℱ.seq s]
      =ᵐ[P] (fun _ : Ω => (0 : ℝ)) := by
    by_cases h_eq : s' = t'
    · -- Trivial case: B_inc = ∅.
      have h_empty : B_inc = ∅ := by
        show Set.Ioc s' t' ×ˢ φ.A i = ∅
        rw [h_eq, Set.Ioc_self]
        exact Set.empty_prod
      have h_zero_fun : (fun ω => N.compensated B_inc ω) = (fun _ : Ω => (0 : ℝ)) := by
        funext ω
        rw [h_empty]
        show (N.N ω ∅).toReal - (referenceIntensity ν ∅).toReal = 0
        simp
      rw [h_zero_fun]
      have h_le := ℱ.le' s
      rw [MeasureTheory.condExp_const h_le 0]
    · -- s' < t'. Apply condExp_compensated_increment_eq_zero.
      have hs'_lt_t' : s' < t' := lt_of_le_of_ne hs'_le_t' h_eq
      have hs_le_post : s ≤ φ.partition i.succ := by
        by_contra h_not
        push_neg at h_not
        have hs'_post : s' = φ.partition i.succ := min_eq_left h_not.le
        have hpost_le_t : φ.partition i.succ ≤ t := h_not.le.trans hst
        have ht'_post : t' = φ.partition i.succ := min_eq_left hpost_le_t
        exact h_eq (by rw [hs'_post, ht'_post])
      have h_s'_eq_s : s' = s := min_eq_right hs_le_post
      have h_B_inc_eq : B_inc = Set.Ioc s t' ×ˢ φ.A i := by
        show Set.Ioc s' t' ×ˢ φ.A i = _
        rw [h_s'_eq_s]
      rw [h_B_inc_eq]
      have hs_lt_t' : s < t' := h_s'_eq_s ▸ hs'_lt_t'
      exact condExp_compensated_increment_eq_zero N hs_nn hs_lt_t'
        (φ.A_measurable i) (φ.A_finite i)
  -- Combine: E[g_i(t) | F_s] =ᵐ E[g_i(s) + ξ · Ñ(B_inc) | F_s] =ᵐ g_i(s) + 0 =ᵐ g_i(s).
  refine h_condExp_t_eq.trans (h_condExp_add.trans ?_)
  filter_upwards [h_pull_inc, h_inc_zero] with ω h_pull_ω h_zero_ω
  show (P[fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω | ℱ.seq s]
      + P[fun ω => φ.ξ i ω * N.compensated B_inc ω | ℱ.seq s]) ω
    = φ.ξ i ω * N.compensated (φ.timeRect i s) ω
  rw [Pi.add_apply, h_self_g_s]
  -- Pull out ξ_i in the increment cond-exp.
  change φ.ξ i ω * N.compensated (φ.timeRect i s) ω
    + P[φ.ξ i * (fun ω => N.compensated B_inc ω) | ℱ.seq s] ω
    = φ.ξ i ω * N.compensated (φ.timeRect i s) ω
  rw [h_pull_ω, Pi.mul_apply, h_zero_ω, mul_zero, add_zero]

open LevyStochCalc.Poisson.Compensated in
/-- **Per-term cond-exp identity (full)** for compensated-Poisson `simpleIntegral`.
Dispatches to the `pre_t ≤ s` helper, with tower argument when
`s < pre_t ≤ t` and a `g_t = 0` argument when `t < pre_t`. -/
private lemma simpleIntegral_term_condExp_compensatedPoisson
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω
        | (naturalFiltration N).seq s]
      =ᵐ[P] fun ω => φ.ξ i ω * N.compensated (φ.timeRect i s) ω := by
  set ℱ := naturalFiltration N
  have hpre_lt_post : φ.partition i.castSucc < φ.partition i.succ :=
    φ.partition_strictMono Fin.castSucc_lt_succ
  have h_g_zero_le_pre : ∀ u, u ≤ φ.partition i.castSucc →
      (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i u) ω) = (fun _ : Ω => (0 : ℝ)) := by
    intro u hu
    have h_min_pre_u : min (φ.partition i.castSucc) u = u := min_eq_right hu
    have h_min_post_u : min (φ.partition i.succ) u = u :=
      min_eq_right (hu.trans hpre_lt_post.le)
    have h_empty : φ.timeRect i u = ∅ := by
      unfold SimplePredictable.timeRect
      rw [h_min_pre_u, h_min_post_u]
      ext ⟨s, e⟩
      simp [Set.mem_Ioc]
    funext ω
    rw [h_empty]
    show φ.ξ i ω * ((N.N ω ∅).toReal - (referenceIntensity ν ∅).toReal) = 0
    simp
  by_cases hs_pre : φ.partition i.castSucc ≤ s
  · exact simpleIntegral_term_condExp_compensatedPoisson_main N φ i h_adapt_i hs_pre hst
  · push_neg at hs_pre
    have hs_lt_pre : s ≤ φ.partition i.castSucc := hs_pre.le
    have h_g_s_zero := h_g_zero_le_pre s hs_lt_pre
    by_cases ht_pre : φ.partition i.castSucc ≤ t
    · -- Case B: tower through F_{pre_t}.
      have h_main := simpleIntegral_term_condExp_compensatedPoisson_main N φ i h_adapt_i
        (le_refl (φ.partition i.castSucc)) ht_pre
      have h_g_pre_zero := h_g_zero_le_pre (φ.partition i.castSucc) (le_refl _)
      rw [h_g_pre_zero] at h_main
      have h_le_F_pre : ℱ.seq s ≤ ℱ.seq (φ.partition i.castSucc) := ℱ.mono hs_lt_pre
      have h_tower := MeasureTheory.condExp_condExp_of_le
        (μ := P)
        (f := fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω)
        h_le_F_pre (ℱ.le' (φ.partition i.castSucc))
      have h_outer_zero := MeasureTheory.condExp_congr_ae
        (m := ℱ.seq s) (μ := P) h_main
      have h_zero_const := MeasureTheory.condExp_const (μ := P) (ℱ.le' s) (0 : ℝ)
      rw [h_g_s_zero]
      filter_upwards [h_tower, h_outer_zero] with ω h_tower_ω h_outer_zero_ω
      rw [← h_tower_ω, h_outer_zero_ω, h_zero_const]
    · -- Case C: t < pre_t, both g_t and g_s are 0.
      push_neg at ht_pre
      have ht_lt_pre : t ≤ φ.partition i.castSucc := ht_pre.le
      have h_g_t_zero := h_g_zero_le_pre t ht_lt_pre
      rw [h_g_t_zero, h_g_s_zero]
      have h_const := MeasureTheory.condExp_const (μ := P) (ℱ.le' s) (0 : ℝ)
      rw [h_const]

open LevyStochCalc.Poisson.Compensated in
/-- **Martingale property of `simpleIntegral` (compensated Poisson)** — for an
adapted simple predictable integrand `φ`, `t ↦ simpleIntegral N φ t` is a
martingale wrt `naturalFiltration N`. Mirrors
`Brownian.Ito.martingale_simpleIntegral_brownian`.

Proof: per-term adaptedness via `Finset.stronglyMeasurable_fun_sum` +
`simpleIntegral_term_adapted_compensatedPoisson`; per-term cond-exp identity
via `condExp_finset_sum` + `eventuallyEq_sum` +
`simpleIntegral_term_condExp_compensatedPoisson`. -/
theorem martingale_simpleIntegral_compensatedPoisson
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((naturalFiltration N).seq (φ.partition i.castSucc)) (φ.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral N φ t)
      (naturalFiltration N) P := by
  set ℱ := naturalFiltration N
  refine ⟨?_, ?_⟩
  · intro t
    show @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
      (fun ω => ∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.timeRect i t) ω)
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact simpleIntegral_term_adapted_compensatedPoisson N φ i t (h_adapt i)
  · intro s t hst
    have h_unfold_pi : ∀ u : ℝ, (fun ω => simpleIntegral N φ u ω) =
        ∑ i : Fin φ.N, (fun ω : Ω => φ.ξ i ω * N.compensated (φ.timeRect i u) ω) := by
      intro u
      ext ω
      rw [Finset.sum_apply]
      rfl
    show P[fun ω => simpleIntegral N φ t ω | ℱ.seq s] =ᵐ[P]
      fun ω => simpleIntegral N φ s ω
    rw [h_unfold_pi t, h_unfold_pi s]
    have h_int : ∀ i ∈ (Finset.univ : Finset (Fin φ.N)),
        MeasureTheory.Integrable
          (fun ω => φ.ξ i ω * N.compensated (φ.timeRect i t) ω) P :=
      fun i _ => simpleIntegral_term_integrable_compensatedPoisson N φ i t
    have h_step1 := MeasureTheory.condExp_finset_sum h_int (m := ℱ.seq s)
    refine h_step1.trans ?_
    refine eventuallyEq_sum ?_
    intro i _
    exact simpleIntegral_term_condExp_compensatedPoisson N φ i (h_adapt i) hst

end LevyStochCalc.Poisson
