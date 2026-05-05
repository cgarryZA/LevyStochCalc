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

end LevyStochCalc.Poisson
