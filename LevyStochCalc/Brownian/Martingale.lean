/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Continuity

/-!
# Layer 1.5c: Natural filtration, martingale property, quadratic variation

Brownian motion `W` generates the *natural filtration*

  `ℱ_t := σ(W_s : s ≤ t)`,

w.r.t. which `W` is a martingale, and has *quadratic variation*

  `⟨W⟩_t = t`.

The quadratic-variation identity `(dW)² = dt` is the cornerstone of the Itô
formula; without it the second-order Taylor term in the diffusion case would
not produce the `½ σ² f''` correction.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §1.5 + §3.1.
* User's dissertation, ch02 §"Probability-space prerequisites", lines 22-23.

## Proof structure

1. Construct `naturalFiltration W` via `MeasureTheory.Filtration.natural`.
2. Adaptedness is automatic via `Filtration.stronglyAdapted_natural`.
3. Conditional-expectation identity: `𝔼[W_t | ℱ_s] = W_s` reduces to
   `𝔼[W_t − W_s | ℱ_s] = 0`. This requires:
   * **σ-algebra independence**: `σ(W_t − W_s) ⊥⊥ ℱ_s` under `P`. This is
     stronger than the `pairwise IndepFun` in `BrownianMotion.increment_independent`
     and follows from joint Gaussian independence of finite past tuples
     (provable by `ProbabilityTheory.IndepSets.indep` on the π-system of
     past-cylinders together with `BrownianMotion.increment_independent`).
   * **Mean zero of increment**: `𝔼[W_t − W_s] = ∫ x, x ∂(gaussianReal 0 ⟨t-s⟩) = 0`
     by `ProbabilityTheory.integral_id_gaussianReal`.
   * **`condExp_indep_eq`**: independence + measurability ⇒ `𝔼[X | ℱ] = 𝔼[X]` a.s.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The *natural filtration* of a Brownian motion `W`. -/
noncomputable def naturalFiltration
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω› :=
  MeasureTheory.Filtration.natural W.W (fun t => (W.measurable_eval t).stronglyMeasurable)

/-- **Integrability of a Brownian-motion value at any `s : ℝ`.** Uses the
Gaussian distribution of `W_s` (for `s ≥ 0`) or the `negative_zero` extension
(for `s < 0`). -/
lemma brownianMotion_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.Integrable (W.W s) P := by
  by_cases hs_neg : s < 0
  · -- s < 0: W_s = 0 a.s.
    refine ⟨(W.measurable_eval s).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have h_nn : ∀ᵐ ω ∂P, ‖W.W s ω‖ₑ = 0 := by
      filter_upwards [W.negative_zero s hs_neg] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  push Not at hs_neg
  -- s ≥ 0
  have hs := hs_neg
  by_cases hs_zero : s = 0
  · subst hs_zero
    refine ⟨(W.measurable_eval 0).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have h_nn : ∀ᵐ ω ∂P, ‖W.W 0 ω‖ₑ = 0 := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
    have h_eq : (fun ω => W.W s ω) =ᵐ[P] fun ω => W.W s ω - W.W 0 ω := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; ring
    have h_map : P.map (fun ω => W.W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩ := by
      rw [MeasureTheory.Measure.map_congr h_eq]
      have := W.increment_gaussian (le_refl 0) hs_pos
      simpa using this
    have h_int_id : MeasureTheory.Integrable (id : ℝ → ℝ)
        (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) :=
      MeasureTheory.memLp_one_iff_integrable.mp
        (ProbabilityTheory.IsGaussian.memLp_id _ 1 (by simp))
    have := (MeasureTheory.integrable_map_measure (g := (id : ℝ → ℝ))
      (by fun_prop : MeasureTheory.AEStronglyMeasurable id _)
      (W.measurable_eval s).aemeasurable).mp (h_map ▸ h_int_id)
    simpa using this

/-- **`W_s` is in `L²` for any `s : ℝ`.** Pushforward to `gaussianReal 0 v` +
`IsGaussian.memLp_id`, with the `negative_zero` field for `s < 0`. -/
lemma brownianMotion_memLp_2
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.MemLp (W.W s) 2 P := by
  by_cases hs_neg : s < 0
  · -- s < 0: W_s = 0 a.s.
    refine ⟨(W.measurable_eval s).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
    have h_zero : ∀ᵐ ω ∂P, ‖W.W s ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) = 0 := by
      filter_upwards [W.negative_zero s hs_neg] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_zero]
    simp
  push Not at hs_neg
  have hs := hs_neg
  by_cases hs_zero : s = 0
  · subst hs_zero
    refine ⟨(W.measurable_eval 0).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by simp)]
    have h_zero : ∀ᵐ ω ∂P, ‖W.W 0 ω‖ₑ ^ ((2 : ℝ≥0∞).toReal) = 0 := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_zero]
    simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
    have h_eq : (fun ω => W.W s ω) =ᵐ[P] fun ω => W.W s ω - W.W 0 ω := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; ring
    have h_map : P.map (fun ω => W.W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩ := by
      rw [MeasureTheory.Measure.map_congr h_eq]
      have := W.increment_gaussian (le_refl 0) hs_pos
      simpa using this
    have h_memLp_id : MeasureTheory.MemLp (id : ℝ → ℝ) 2
        (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) :=
      ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
    rw [show (W.W s : Ω → ℝ) = id ∘ W.W s from rfl]
    rw [← h_map] at h_memLp_id
    exact (MeasureTheory.memLp_map_measure_iff (by fun_prop)
      (W.measurable_eval s).aemeasurable).mp h_memLp_id

/-- **Integrability of `(W_s)^2` at any `s : ℝ`.** Uses the Gaussian
distribution of `W_s` (for `s ≥ 0`) or the `negative_zero` extension. -/
lemma brownianMotion_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (s : ℝ) :
    MeasureTheory.Integrable (fun ω => (W.W s ω)^2) P := by
  by_cases hs_neg : s < 0
  · -- s < 0
    refine ⟨((W.measurable_eval s).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have h_nn : ∀ᵐ ω ∂P, ‖(W.W s ω)^2‖ₑ = 0 := by
      filter_upwards [W.negative_zero s hs_neg] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  push Not at hs_neg
  have hs := hs_neg
  by_cases hs_zero : s = 0
  · subst hs_zero
    refine ⟨((W.measurable_eval 0).pow_const 2).aestronglyMeasurable, ?_⟩
    rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
    have h_nn : ∀ᵐ ω ∂P, ‖(W.W 0 ω)^2‖ₑ = 0 := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; simp
    rw [MeasureTheory.lintegral_congr_ae h_nn]
    simp
  · have hs_pos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs_zero)
    have h_eq : (fun ω => W.W s ω) =ᵐ[P] fun ω => W.W s ω - W.W 0 ω := by
      filter_upwards [W.initial_zero] with ω hω
      rw [hω]; ring
    have h_map : P.map (fun ω => W.W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩ := by
      rw [MeasureTheory.Measure.map_congr h_eq]
      have := W.increment_gaussian (le_refl 0) hs_pos
      simpa using this
    -- Integrability of x^2 under gaussianReal 0 ⟨s, hs⟩
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x^2)
        (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨s, hs⟩) :=
        ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1
      ext x
      change x^2 = ‖x‖^2
      rw [Real.norm_eq_abs, sq_abs]
    -- Pull back via map
    have := (MeasureTheory.integrable_map_measure
      (g := fun x : ℝ => x^2)
      (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x^2) _)
      (W.measurable_eval s).aemeasurable).mp (h_map ▸ h_int_sq)
    simpa [Function.comp_def] using this

/-- **σ-algebra-level increment independence.** The σ-algebra generated by the
increment `W_t − W_s` is independent (under `P`) of the natural filtration
`(naturalFiltration W) s`. Stronger than `BrownianMotion.increment_independent`
(which is pairwise); follows by π-system + `IndepSets.indep`. -/
lemma increment_indep_naturalFiltration_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    ProbabilityTheory.Indep
      ((naturalFiltration W) s)
      (MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance)
      P := by
  -- The natural filtration's σ-algebra at s equals `⨆ j ∈ Set.Iic s, σ(W j)`,
  -- which is exactly the structural `joint_increment_independent` field.
  have h_eq : ((naturalFiltration W) s : MeasurableSpace Ω)
      = ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W.W j) inferInstance := by
    show (naturalFiltration W).seq s = _
    unfold naturalFiltration MeasureTheory.Filtration.natural
    rfl
  rw [h_eq]
  exact W.joint_increment_independent hs hst

/-- **Conditional expectation of an increment is zero.** Combines:
* `increment_indep_naturalFiltration_aux`: σ-algebra independence of the
  increment from the natural filtration past.
* `IsGaussian.memLp_id`: `id` is `L^1` under `gaussianReal`, giving
  integrability of the increment via pushforward.
* `integral_id_gaussianReal`: the mean of `gaussianReal 0 v` is `0`.
* Mathlib `condExp_indep_eq`: if `f` is `m₁`-measurable and `m₁` is
  independent of `m₂`, then `𝔼[f | m₂] = 𝔼[f]` a.s. -/
lemma condExp_increment_eq_zero_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    P[(fun ω => W.W t ω - W.W s ω) | (naturalFiltration W) s] =ᵐ[P]
      fun _ => 0 := by
  have h_meas_diff : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  -- Integrability via Gaussian increment law.
  have h_int_id : MeasureTheory.Integrable (id : ℝ → ℝ)
      (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
    MeasureTheory.memLp_one_iff_integrable.mp
      (ProbabilityTheory.IsGaussian.memLp_id _ 1 (by simp))
  have h_int : MeasureTheory.Integrable (fun ω => W.W t ω - W.W s ω) P := by
    have h_map := W.increment_gaussian hs hst
    have := (MeasureTheory.integrable_map_measure (g := (id : ℝ → ℝ))
      (by fun_prop : MeasureTheory.AEStronglyMeasurable id _)
      h_meas_diff.aemeasurable).mp (h_map ▸ h_int_id)
    simpa using this
  -- Mean zero via Gaussian mean.
  have h_mean : ∫ ω, (W.W t ω - W.W s ω) ∂P = 0 := by
    rw [show ∫ ω, (W.W t ω - W.W s ω) ∂P
          = ∫ x, x ∂(P.map (fun ω => W.W t ω - W.W s ω)) from
      (MeasureTheory.integral_map h_meas_diff.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (id : ℝ → ℝ) _)).symm]
    rw [W.increment_gaussian hs hst]
    exact ProbabilityTheory.integral_id_gaussianReal
  -- σ-algebra independence.
  have h_indep := (increment_indep_naturalFiltration_aux W hs hst).symm
  -- Apply condExp_indep_eq.
  have hle₁ : MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance
      ≤ ‹MeasurableSpace Ω› := by
    intro u ⟨v, hv, hvu⟩
    rw [← hvu]
    exact h_meas_diff hv
  have hle₂ : (naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
    (naturalFiltration W).le' s
  have hf_sm : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance)
      (fun ω => W.W t ω - W.W s ω) := by
    apply Measurable.stronglyMeasurable
    exact Measurable.of_comap_le le_rfl
  have h := MeasureTheory.condExp_indep_eq hle₁ hle₂ hf_sm h_indep
  filter_upwards [h] with ω hω
  rw [hω]
  exact h_mean

/-- **Gaussian second moment.** `∫ x² ∂(gaussianReal 0 v) = v`. -/
lemma gaussianReal_second_moment (v : NNReal) :
    ∫ x : ℝ, x^2 ∂(ProbabilityTheory.gaussianReal 0 v) = v := by
  have h_var : ProbabilityTheory.variance (fun x : ℝ => x)
      (ProbabilityTheory.gaussianReal 0 v) = v :=
    ProbabilityTheory.variance_fun_id_gaussianReal
  rw [ProbabilityTheory.variance_eq_integral measurable_id'.aemeasurable] at h_var
  simp [ProbabilityTheory.integral_id_gaussianReal] at h_var
  exact h_var

/-- **Conditional expectation of squared increment is `t - s`.** Combines:
* σ-algebra independence of the increment with the past;
* `gaussianReal_second_moment`: variance of `gaussianReal 0 v` is `v`. -/
lemma condExp_increment_sq_eq_var_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    P[(fun ω => (W.W t ω - W.W s ω)^2) | (naturalFiltration W) s] =ᵐ[P]
      fun _ => t - s := by
  have h_meas_diff : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  have h_meas_sq : Measurable (fun ω => (W.W t ω - W.W s ω)^2) :=
    h_meas_diff.pow_const 2
  -- Integrability via Gaussian increment law (second moment).
  have h_int_id_sq : MeasureTheory.Integrable (fun x : ℝ => x^2)
      (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) := by
    have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
        (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
      ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
    have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
    convert h using 1
    ext x
    change x^2 = ‖x‖^2
    rw [Real.norm_eq_abs, sq_abs]
  have h_int : MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω)^2) P := by
    have h_map := W.increment_gaussian hs hst
    have := (MeasureTheory.integrable_map_measure
      (g := fun x : ℝ => x^2)
      (by fun_prop : MeasureTheory.AEStronglyMeasurable
        (fun x : ℝ => x^2) _)
      h_meas_diff.aemeasurable).mp (h_map ▸ h_int_id_sq)
    simpa [Function.comp_def] using this
  -- Mean = t - s via Gaussian second moment.
  have h_mean : ∫ ω, (W.W t ω - W.W s ω)^2 ∂P = t - s := by
    rw [show ∫ ω, (W.W t ω - W.W s ω)^2 ∂P
          = ∫ x, x^2 ∂(P.map (fun ω => W.W t ω - W.W s ω)) from
      (MeasureTheory.integral_map h_meas_diff.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable
          (fun x : ℝ => x^2) _)).symm]
    rw [W.increment_gaussian hs hst]
    rw [gaussianReal_second_moment]
    rfl
  -- σ-algebra independence: the squared increment is in σ(W_t - W_s).
  -- The σ-algebra generated by (W_t - W_s)^2 is contained in that of (W_t - W_s).
  -- Use the larger σ-algebra and apply Indep.symm.
  have h_indep := (increment_indep_naturalFiltration_aux W hs hst).symm
  have hle₁ :
      MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance
        ≤ ‹MeasurableSpace Ω› := by
    intro u ⟨v, hv, hvu⟩
    rw [← hvu]
    exact h_meas_diff hv
  have hle₂ : (naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
    (naturalFiltration W).le' s
  have hf_sm : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance)
      (fun ω => (W.W t ω - W.W s ω)^2) := by
    have h_id : @Measurable Ω ℝ
        (MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance) _
        (fun ω => W.W t ω - W.W s ω) := Measurable.of_comap_le le_rfl
    exact (h_id.pow_const 2).stronglyMeasurable
  have h := MeasureTheory.condExp_indep_eq hle₁ hle₂ hf_sm h_indep
  filter_upwards [h] with ω hω
  rw [hω]
  exact h_mean

/-- **Cross-term conditional expectation is zero.** For
`B := 2 W_s (W_t - W_s)`, the conditional expectation `E[B | F_s] = 0` a.s.,
because the increment factor has zero conditional expectation
(`condExp_increment_eq_zero_aux`) and `W_s` pulls out by
`condExp_mul_of_aestronglyMeasurable_left`. -/
lemma condExp_cross_increment_eq_zero_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    P[(fun ω => 2 * W.W s ω * (W.W t ω - W.W s ω))
      | (naturalFiltration W).seq s] =ᵐ[P] fun _ => 0 := by
  have hW_s_memLp : MeasureTheory.MemLp (W.W s) 2 P := brownianMotion_memLp_2 W s
  have h_inc_memLp : MeasureTheory.MemLp (fun ω => W.W t ω - W.W s ω) 2 P := by
    have h_int_id_2 : MeasureTheory.MemLp (id : ℝ → ℝ) 2
        (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
      ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
    rw [show (fun ω => W.W t ω - W.W s ω)
        = id ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
    rw [← W.increment_gaussian hs hst] at h_int_id_2
    exact (MeasureTheory.memLp_map_measure_iff (by fun_prop)
      ((W.measurable_eval t).sub (W.measurable_eval s)).aemeasurable).mp h_int_id_2
  have hW_s_sm : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((naturalFiltration W).seq s) (W.W s) :=
    MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
  have h_inc_zero := condExp_increment_eq_zero_aux W hs hst
  -- Rewrite 2 * W_s * (W_t - W_s) = 2 • (W_s * (W_t - W_s))
  have h_rw : (fun ω => 2 * W.W s ω * (W.W t ω - W.W s ω))
      = (2 : ℝ) • (fun ω => W.W s ω * (W.W t ω - W.W s ω)) := by
    funext ω; simp [Pi.smul_apply]; ring
  rw [h_rw]
  have h_smul := MeasureTheory.condExp_smul (μ := P)
    (m := (naturalFiltration W).seq s) (2 : ℝ)
    (fun ω => W.W s ω * (W.W t ω - W.W s ω))
  have h_int_prod : MeasureTheory.Integrable
      (W.W s * (fun ω => W.W t ω - W.W s ω)) P :=
    hW_s_memLp.integrable_mul h_inc_memLp
  have h_inc_int : MeasureTheory.Integrable
      (fun ω => W.W t ω - W.W s ω) P :=
    h_inc_memLp.integrable (by norm_num)
  have h_pull := MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
    (m := (naturalFiltration W).seq s) (μ := P) (f := W.W s)
    (g := fun ω => W.W t ω - W.W s ω)
    hW_s_sm.aestronglyMeasurable h_int_prod h_inc_int
  filter_upwards [h_smul, h_pull, h_inc_zero] with ω h_smul_ω h_pull_ω h_zero_ω
  rw [h_smul_ω, Pi.smul_apply]
  change (2 : ℝ) • P[fun ω => W.W s ω * (W.W t ω - W.W s ω)
    | (naturalFiltration W).seq s] ω = 0
  have h_eq : (fun ω => W.W s ω * (W.W t ω - W.W s ω))
      = W.W s * (fun ω => W.W t ω - W.W s ω) := rfl
  rw [h_eq, h_pull_ω, Pi.mul_apply, h_zero_ω]
  change (2 : ℝ) • (W.W s ω * 0) = 0
  ring

/-- **Auxiliary: `P[W_t | F_0] = 0` a.s. for `t ≥ 0`.**

Used to bridge the `s < 0 ≤ t` case of `brownian_martingale` via the tower
property `condExp_condExp_of_le`. -/
lemma brownian_martingale_zero_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {t : ℝ} (ht : 0 ≤ t) :
    P[W.W t | (naturalFiltration W).seq 0] =ᵐ[P] (fun _ => 0 : Ω → ℝ) := by
  by_cases ht_zero : t = 0
  · -- t = 0: P[W_0 | F_0] = W_0 =ᵐ[P] 0 (since W_0 = 0 a.s.)
    subst ht_zero
    have h_le : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
      (naturalFiltration W).le' 0
    have h_meas := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) 0
    have h_int : MeasureTheory.Integrable (W.W 0) P :=
      brownianMotion_integrable W 0
    have h_eq := MeasureTheory.condExp_of_stronglyMeasurable h_le h_meas h_int
    rw [h_eq]
    filter_upwards [W.initial_zero] with ω hω
    exact hω
  · -- 0 < t: use the s = 0 < t case via decomposition.
    have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
    have h_int_W0 : MeasureTheory.Integrable (W.W 0) P :=
      brownianMotion_integrable W 0
    have h_int_Wt : MeasureTheory.Integrable (W.W t) P :=
      brownianMotion_integrable W t
    have h_inc_int : MeasureTheory.Integrable (fun ω => W.W t ω - W.W 0 ω) P :=
      h_int_Wt.sub h_int_W0
    have h_inc_zero := condExp_increment_eq_zero_aux W (le_refl 0) ht_pos
    have h_le : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
      (naturalFiltration W).le' 0
    have h_adapt_W0 :=
      MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) 0
    have h_decomp : (W.W t : Ω → ℝ) = W.W 0 + (fun ω => W.W t ω - W.W 0 ω) := by
      funext ω; simp [Pi.add_apply]
    rw [h_decomp]
    have h_add := MeasureTheory.condExp_add h_int_W0 h_inc_int
      ((naturalFiltration W).seq 0)
    have h_self := MeasureTheory.condExp_of_stronglyMeasurable h_le h_adapt_W0 h_int_W0
    filter_upwards [h_add, h_inc_zero, W.initial_zero]
      with ω h_add_ω h_zero_ω hW0_ω
    rw [h_add_ω, Pi.add_apply, h_zero_ω, h_self]
    change W.W 0 ω + 0 = 0
    rw [hW0_ω]; ring

/-- Brownian motion `W` is a martingale w.r.t. its natural filtration.

Proof: decompose `W_t = W_s + (W_t − W_s)`. By linearity of conditional
expectation:
* `𝔼[W_s | ℱ_s] = W_s` (W_s is `ℱ_s`-measurable, hence its own conditional
  expectation).
* `𝔼[W_t − W_s | ℱ_s] = 0` by `condExp_increment_eq_zero_aux`.

Combined: `𝔼[W_t | ℱ_s] = W_s + 0 = W_s`. -/
theorem brownian_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale (fun t : ℝ => W.W t) F P := by
  refine ⟨naturalFiltration W, ?_, ?_⟩
  · -- StronglyAdapted: by Filtration.stronglyAdapted_natural
    exact MeasureTheory.Filtration.stronglyAdapted_natural _
  · -- Cond-exp identity: 𝔼[W_t | ℱ_s] = W_s for s ≤ t.
    intro s t hst
    by_cases hst_eq : s = t
    · -- s = t: 𝔼[W_t | ℱ_t] = W_t (W_t is `ℱ_t`-measurable).
      subst hst_eq
      -- Use condExp_of_stronglyMeasurable.
      have h_le : (naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
        (naturalFiltration W).le' s
      have h_meas := MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
      -- Integrability of W.W s under P (Gaussian moments).
      -- Using `s = t`, but we don't have `0 ≤ s`. The natural filtration is
      -- defined for all `t : ℝ`; we still need integrability.
      have h_int : MeasureTheory.Integrable (W.W s) P :=
        brownianMotion_integrable W s
      -- SigmaFinite trim instance derives from `IsFiniteMeasure P`.
      have h_eq := MeasureTheory.condExp_of_stronglyMeasurable h_le h_meas h_int
      -- Convert `=` to `=ᵐ[P]` (regular equality implies a.e. equality).
      rw [h_eq]
    · -- s < t: decompose W_t = W_s + (W_t − W_s).
      -- 𝔼[W_t | ℱ_s] = 𝔼[W_s | ℱ_s] + 𝔼[W_t − W_s | ℱ_s]
      -- = W_s (condExp_of_stronglyMeasurable) + 0 (condExp_increment_eq_zero_aux)
      -- = W_s.
      have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
      by_cases hs_nn : 0 ≤ s
      swap
      · -- s < 0: handle subcases on t.
        push Not at hs_nn
        by_cases ht_nn : 0 ≤ t
        · -- s < 0 ≤ t: tower through F_0.
          -- F_s ≤ F_0 (filtration monotone). P[P[W_t | F_0] | F_s] = P[W_t | F_s].
          -- P[W_t | F_0] = 0 a.s. (brownian_martingale_zero_aux).
          -- P[0 | F_s] = 0 a.s. So P[W_t | F_s] = 0 = W_s a.s.
          have h_le_F : (naturalFiltration W).seq s ≤ (naturalFiltration W).seq 0 :=
            (naturalFiltration W).mono hs_nn.le
          have h_le_F0 : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
            (naturalFiltration W).le' 0
          have h_tower := MeasureTheory.condExp_condExp_of_le
            (μ := P) (f := W.W t) h_le_F h_le_F0
          have h_inner_zero := brownian_martingale_zero_aux W ht_nn
          -- Apply condExp_congr_ae to inner equality
          have h_outer_zero :
              P[P[W.W t | (naturalFiltration W).seq 0] | (naturalFiltration W).seq s]
                =ᵐ[P] P[(fun _ => 0 : Ω → ℝ) | (naturalFiltration W).seq s] := by
            exact MeasureTheory.condExp_congr_ae h_inner_zero
          have h_zero_inner := MeasureTheory.condExp_const (μ := P)
            ((naturalFiltration W).le' s) (0 : ℝ)
          have hWs_zero : ∀ᵐ ω ∂P, W.W s ω = 0 := W.negative_zero s hs_nn
          filter_upwards [h_tower, h_outer_zero, hWs_zero]
            with ω h_tower_ω h_outer_ω hWs_ω
          rw [← h_tower_ω, h_outer_ω, h_zero_inner]
          change (0 : ℝ) = W.W s ω
          rw [hWs_ω]
        · -- s < t < 0: both W_s and W_t are 0 a.s.
          push Not at ht_nn
          have hWs_zero : ∀ᵐ ω ∂P, W.W s ω = 0 := W.negative_zero s hs_nn
          have hWt_zero : ∀ᵐ ω ∂P, W.W t ω = 0 := W.negative_zero t ht_nn
          have h_Wt_ae_zero : (W.W t : Ω → ℝ) =ᵐ[P] (fun _ => 0 : Ω → ℝ) := by
            filter_upwards [hWt_zero] with ω hω; exact hω
          have h_eq := MeasureTheory.condExp_congr_ae (m := (naturalFiltration W).seq s)
            (μ := P) h_Wt_ae_zero
          have h_const := MeasureTheory.condExp_const (μ := P)
            ((naturalFiltration W).le' s) (0 : ℝ)
          filter_upwards [h_eq, hWs_zero] with ω h_eq_ω hWs_ω
          rw [h_eq_ω, h_const]
          change (0 : ℝ) = W.W s ω
          rw [hWs_ω]
      -- Now 0 ≤ s < t.
      have h_int_s : MeasureTheory.Integrable (W.W s) P :=
        brownianMotion_integrable W s
      have h_int_t : MeasureTheory.Integrable (W.W t) P :=
        brownianMotion_integrable W t
      have h_inc_int : MeasureTheory.Integrable (fun ω => W.W t ω - W.W s ω) P :=
        h_int_t.sub h_int_s
      have h_inc_zero := condExp_increment_eq_zero_aux W hs_nn hst_lt
      have h_le : (naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
        (naturalFiltration W).le' s
      have h_adapt_s :=
        MeasureTheory.Filtration.stronglyAdapted_natural
          (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
      have h_decomp : (W.W t : Ω → ℝ) = W.W s + (fun ω => W.W t ω - W.W s ω) := by
        funext ω; simp [Pi.add_apply]
      change P[W.W t | (naturalFiltration W).seq s] =ᶠ[ae P] W.W s
      rw [h_decomp]
      have h_add := MeasureTheory.condExp_add h_int_s h_inc_int
        ((naturalFiltration W).seq s)
      have h_self := MeasureTheory.condExp_of_stronglyMeasurable h_le h_adapt_s h_int_s
      filter_upwards [h_add, h_inc_zero] with ω h_add_ω h_zero_ω
      rw [h_add_ω, Pi.add_apply, h_zero_ω, h_self]
      change W.W s ω + 0 = W.W s ω
      ring

/-- **Auxiliary: `P[(W_t)² - t | F_0] =ᵐ[P] 0` for `t ≥ 0`.**

Used to bridge the `s < 0 ≤ t` case of `brownian_quadVar` via the tower
property. For `t = 0`, this reduces to `(W_0)² = 0` a.s. via `initial_zero`.
For `t > 0`, the standard three-piece decomposition with `s := 0`. -/
lemma brownian_quadVar_zero_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {t : ℝ} (ht : 0 ≤ t) :
    P[(fun ω => (W.W t ω)^2 - t) | (naturalFiltration W).seq 0]
      =ᵐ[P] (fun _ => 0 : Ω → ℝ) := by
  by_cases ht_zero : t = 0
  · -- t = 0: integrand is (W_0)² - 0, F_0-measurable. condExp = identity =ᵐ 0.
    subst ht_zero
    have h_le : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
      (naturalFiltration W).le' 0
    have hW := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) 0
    have h_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((naturalFiltration W).seq 0) (fun ω => (W.W 0 ω)^2 - 0) := by
      have hsq := hW.pow 2
      have h_const : @MeasureTheory.StronglyMeasurable Ω ℝ _
          ((naturalFiltration W).seq 0) (fun _ : Ω => (0 : ℝ)) :=
        MeasureTheory.stronglyMeasurable_const
      exact hsq.sub h_const
    have h_int : MeasureTheory.Integrable (fun ω => (W.W 0 ω)^2 - 0) P :=
      (brownianMotion_sq_integrable W 0).sub (MeasureTheory.integrable_const _)
    have h_eq := MeasureTheory.condExp_of_stronglyMeasurable h_le h_meas h_int
    rw [h_eq]
    filter_upwards [W.initial_zero] with ω hω
    show (W.W 0 ω)^2 - 0 = 0
    rw [hω]; ring
  · -- 0 < t: three-piece decomposition with s = 0.
    have ht_pos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht_zero)
    -- Pieces (with s = 0):
    -- A_0 = (W_0)² - 0 (F_0-measurable, a.s. = 0)
    -- B_0 = 2 W_0 (W_t - W_0) (a.s. = 0)
    -- C_0 = (W_t - W_0)² - t
    let A : Ω → ℝ := fun ω => (W.W 0 ω)^2 - 0
    let B : Ω → ℝ := fun ω => 2 * W.W 0 ω * (W.W t ω - W.W 0 ω)
    let C : Ω → ℝ := fun ω => (W.W t ω - W.W 0 ω)^2 - (t - 0)
    have hW_0_memLp : MeasureTheory.MemLp (W.W 0) 2 P := brownianMotion_memLp_2 W 0
    have h_inc_memLp : MeasureTheory.MemLp
        (fun ω => W.W t ω - W.W 0 ω) 2 P := by
      have h_int_id_2 : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨t - 0, by linarith⟩) :=
        ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
      rw [show (fun ω => W.W t ω - W.W 0 ω)
          = id ∘ (fun ω => W.W t ω - W.W 0 ω) from rfl]
      rw [← W.increment_gaussian (le_refl 0) ht_pos] at h_int_id_2
      exact (MeasureTheory.memLp_map_measure_iff (by fun_prop)
        ((W.measurable_eval t).sub (W.measurable_eval 0)).aemeasurable).mp
        h_int_id_2
    have h_int_A : MeasureTheory.Integrable A P :=
      (brownianMotion_sq_integrable W 0).sub (MeasureTheory.integrable_const _)
    have h_int_W_0_mul_inc : MeasureTheory.Integrable
        (fun ω => W.W 0 ω * (W.W t ω - W.W 0 ω)) P :=
      hW_0_memLp.integrable_mul h_inc_memLp
    have h_int_B : MeasureTheory.Integrable B P := by
      have : (fun ω => 2 * W.W 0 ω * (W.W t ω - W.W 0 ω))
          = (fun ω => 2 * (W.W 0 ω * (W.W t ω - W.W 0 ω))) := by funext ω; ring
      change MeasureTheory.Integrable
        (fun ω => 2 * W.W 0 ω * (W.W t ω - W.W 0 ω)) P
      rw [this]
      exact h_int_W_0_mul_inc.const_mul 2
    have h_int_inc_sq : MeasureTheory.Integrable
        (fun ω => (W.W t ω - W.W 0 ω)^2) P := by
      have h_pow := h_inc_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h_pow using 1
      ext ω
      change (W.W t ω - W.W 0 ω)^2 = ‖W.W t ω - W.W 0 ω‖^2
      rw [Real.norm_eq_abs, sq_abs]
    have h_int_C : MeasureTheory.Integrable C P :=
      h_int_inc_sq.sub (MeasureTheory.integrable_const _)
    have h_int_BC : MeasureTheory.Integrable (B + C) P := h_int_B.add h_int_C
    -- Decomposition: (W_t)² - t = A + (B + C)
    have h_decomp : (fun ω => (W.W t ω)^2 - t) = A + (B + C) := by
      funext ω
      change (W.W t ω)^2 - t = (W.W 0 ω)^2 - 0
        + (2 * W.W 0 ω * (W.W t ω - W.W 0 ω)
          + ((W.W t ω - W.W 0 ω)^2 - (t - 0)))
      ring
    rw [h_decomp]
    have h_add1 := MeasureTheory.condExp_add h_int_A h_int_BC
      ((naturalFiltration W).seq 0)
    have h_add2 := MeasureTheory.condExp_add h_int_B h_int_C
      ((naturalFiltration W).seq 0)
    have h_le : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
      (naturalFiltration W).le' 0
    have h_adapt_W_0 := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) 0
    have h_adapt_A : @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((naturalFiltration W).seq 0) A :=
      (h_adapt_W_0.pow 2).sub MeasureTheory.stronglyMeasurable_const
    have h_self_A := MeasureTheory.condExp_of_stronglyMeasurable h_le h_adapt_A h_int_A
    have h_zero_B := condExp_cross_increment_eq_zero_aux W (le_refl 0) ht_pos
    have h_zero_C : P[C | (naturalFiltration W).seq 0] =ᵐ[P] fun _ => 0 := by
      have h_C_eq : C = (fun ω => (W.W t ω - W.W 0 ω)^2) - (fun _ : Ω => t - 0) := by
        funext ω; rfl
      change P[C | (naturalFiltration W).seq 0] =ᵐ[P] fun _ => 0
      rw [h_C_eq]
      have h_sub := MeasureTheory.condExp_sub h_int_inc_sq
        (MeasureTheory.integrable_const (t - 0))
        ((naturalFiltration W).seq 0)
      have h_inc_sq := condExp_increment_sq_eq_var_aux W (le_refl 0) ht_pos
      have h_const := MeasureTheory.condExp_const (μ := P) h_le (t - 0 : ℝ)
      filter_upwards [h_sub, h_inc_sq] with ω h_sub_ω h_sq_ω
      rw [h_sub_ω, Pi.sub_apply, h_sq_ω]
      change t - 0 - P[fun _ : Ω => t - 0 | (naturalFiltration W).seq 0] ω = 0
      rw [h_const]
      ring
    filter_upwards [h_add1, h_add2, h_zero_B, h_zero_C, W.initial_zero]
      with ω h_add1_ω h_add2_ω h_B_ω h_C_ω hW0_ω
    rw [h_add1_ω]
    change P[A | (naturalFiltration W).seq 0] ω
      + P[B + C | (naturalFiltration W).seq 0] ω = 0
    rw [h_self_A, h_add2_ω]
    change A ω + (P[B | (naturalFiltration W).seq 0] ω
                  + P[C | (naturalFiltration W).seq 0] ω) = 0
    rw [h_B_ω, h_C_ω]
    change (W.W 0 ω)^2 - 0 + (0 + 0) = 0
    rw [hW0_ω]; ring

/-- Quadratic variation of Brownian motion: `⟨W⟩_t = t`.

Proof structure: `(W_t)² − (W_s)² = 2 W_s (W_t − W_s) + (W_t − W_s)²`.
* `𝔼[(W_t − W_s)² | ℱ_s] = 𝔼[(W_t − W_s)²] = t − s` (Gaussian variance from
  `ProbabilityTheory.variance_id_gaussianReal`).
* `𝔼[2 W_s (W_t − W_s) | ℱ_s] = 2 W_s 𝔼[W_t − W_s | ℱ_s] = 0`
  (W_s is `ℱ_s`-measurable; increment cond-exp is 0).
* Combine: `𝔼[(W_t)² − t | ℱ_s] = (W_s)² − s`. -/
theorem brownian_quadVar
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω => (W.W t ω)^2 - max t 0) F P := by
  refine ⟨naturalFiltration W, ?_, ?_⟩
  · -- StronglyAdapted: (W_t)² − max t 0 is F_t-measurable since W_t is.
    intro t
    have hW := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun s => (W.measurable_eval s).stronglyMeasurable) t
    have hsq := hW.pow 2
    exact hsq.sub MeasureTheory.stronglyMeasurable_const
  · -- Cond-expectation identity (proof structure above).
    intro s t hst
    by_cases hst_eq : s = t
    · -- s = t: identity is trivial via condExp_of_stronglyMeasurable
      -- (the integrand is `(W_t)² − t` which is `ℱ_t`-measurable).
      subst hst_eq
      have h_le : (naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
        (naturalFiltration W).le' s
      have hW := MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
      have hsq := hW.pow 2
      have h_meas := hsq.sub
        (@MeasureTheory.stronglyMeasurable_const Ω ℝ ((naturalFiltration W).seq s)
          PseudoMetricSpace.toUniformSpace.toTopologicalSpace (max s 0))
      have h_int : MeasureTheory.Integrable (fun ω => (W.W s ω)^2 - max s 0) P :=
        (brownianMotion_sq_integrable W s).sub (MeasureTheory.integrable_const _)
      have h_eq := MeasureTheory.condExp_of_stronglyMeasurable h_le h_meas h_int
      -- Reconcile the two representations of `(W.W s)² − max s 0`.
      have h_funext :
          (fun t ω => W.W t ω ^ 2 - max t 0) s = W.W s ^ 2 - (fun _ => max s 0) := by
        funext ω; rfl
      rw [h_funext, h_eq]
    · -- s < t case: decompose (W_t)² - t = ((W_s)² - s) + 2 W_s (W_t - W_s)
      --   + ((W_t - W_s)² - (t - s)).
      -- Sum is `A + B + C`. By linearity of conditional expectation:
      -- E[A + B + C | F_s] = A + 0 + 0 = A.
      have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
      by_cases hs_nn : 0 ≤ s
      swap
      · -- s < 0: subcases on t. With the `max t 0` integrand, both subcases work.
        push Not at hs_nn
        have h_max_s_zero : max s 0 = 0 := max_eq_right hs_nn.le
        by_cases ht_nn : 0 ≤ t
        · -- s < 0 ≤ t: tower through F_0.
          -- M_t = (W_t)² - max t 0 = (W_t)² - t (since t ≥ 0).
          have h_max_t : max t 0 = t := max_eq_left ht_nn
          have h_le_F : (naturalFiltration W).seq s ≤ (naturalFiltration W).seq 0 :=
            (naturalFiltration W).mono hs_nn.le
          have h_le_F0 : (naturalFiltration W).seq 0 ≤ ‹MeasurableSpace Ω› :=
            (naturalFiltration W).le' 0
          have h_tower := MeasureTheory.condExp_condExp_of_le
            (μ := P) (f := fun ω => (W.W t ω)^2 - max t 0) h_le_F h_le_F0
          have h_inner_zero : P[(fun ω => (W.W t ω)^2 - max t 0)
              | (naturalFiltration W).seq 0] =ᵐ[P] fun _ => 0 := by
            rw [show (fun ω => (W.W t ω)^2 - max t 0)
              = (fun ω => (W.W t ω)^2 - t) from by funext ω; rw [h_max_t]]
            exact brownian_quadVar_zero_aux W ht_nn
          have h_outer_zero :
              P[P[(fun ω => (W.W t ω)^2 - max t 0)
                | (naturalFiltration W).seq 0] | (naturalFiltration W).seq s]
                =ᵐ[P] P[(fun _ => 0 : Ω → ℝ) | (naturalFiltration W).seq s] := by
            exact MeasureTheory.condExp_congr_ae h_inner_zero
          have h_zero_inner := MeasureTheory.condExp_const (μ := P)
            ((naturalFiltration W).le' s) (0 : ℝ)
          have hWs_zero : ∀ᵐ ω ∂P, W.W s ω = 0 := W.negative_zero s hs_nn
          filter_upwards [h_tower, h_outer_zero, hWs_zero]
            with ω h_tower_ω h_outer_ω hWs_ω
          rw [← h_tower_ω, h_outer_ω, h_zero_inner]
          change (0 : ℝ) = (W.W s ω)^2 - max s 0
          rw [hWs_ω, h_max_s_zero]; ring
        · -- s < t < 0: both W_s = 0 and W_t = 0 a.s., so M_s = M_t = 0.
          push Not at ht_nn
          have h_max_t_zero : max t 0 = 0 := max_eq_right ht_nn.le
          have hWs_zero : ∀ᵐ ω ∂P, W.W s ω = 0 := W.negative_zero s hs_nn
          have hWt_zero : ∀ᵐ ω ∂P, W.W t ω = 0 := W.negative_zero t ht_nn
          have h_Mt_ae_zero :
              (fun ω => (W.W t ω)^2 - max t 0) =ᵐ[P] (fun _ : Ω => 0) := by
            filter_upwards [hWt_zero] with ω hω
            rw [hω, h_max_t_zero]; ring
          have h_eq := MeasureTheory.condExp_congr_ae
            (m := (naturalFiltration W).seq s) (μ := P) h_Mt_ae_zero
          have h_const := MeasureTheory.condExp_const (μ := P)
            ((naturalFiltration W).le' s) (0 : ℝ)
          filter_upwards [h_eq, hWs_zero] with ω h_eq_ω hWs_ω
          rw [h_eq_ω, h_const]
          change (0 : ℝ) = (W.W s ω)^2 - max s 0
          rw [hWs_ω, h_max_s_zero]; ring
      -- Now 0 ≤ s < t.
      have ht_nn : 0 ≤ t := hs_nn.trans hst_lt.le
      -- Pieces.
      let A : Ω → ℝ := fun ω => (W.W s ω)^2 - s
      let B : Ω → ℝ := fun ω => 2 * W.W s ω * (W.W t ω - W.W s ω)
      let C : Ω → ℝ := fun ω => (W.W t ω - W.W s ω)^2 - (t - s)
      -- L²-membership.
      have hW_s_memLp : MeasureTheory.MemLp (W.W s) 2 P :=
        brownianMotion_memLp_2 W s
      have h_inc_memLp : MeasureTheory.MemLp
          (fun ω => W.W t ω - W.W s ω) 2 P := by
        have h_int_id_2 : MeasureTheory.MemLp (id : ℝ → ℝ) 2
            (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
          ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
        rw [show (fun ω => W.W t ω - W.W s ω)
            = id ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
        rw [← W.increment_gaussian hs_nn hst_lt] at h_int_id_2
        exact (MeasureTheory.memLp_map_measure_iff (by fun_prop)
          ((W.measurable_eval t).sub (W.measurable_eval s)).aemeasurable).mp
          h_int_id_2
      -- Integrability of each piece.
      have h_int_A : MeasureTheory.Integrable A P :=
        (brownianMotion_sq_integrable W s).sub (MeasureTheory.integrable_const _)
      have h_int_W_s_mul_inc : MeasureTheory.Integrable
          (fun ω => W.W s ω * (W.W t ω - W.W s ω)) P :=
        hW_s_memLp.integrable_mul h_inc_memLp
      have h_int_B : MeasureTheory.Integrable B P := by
        have : (fun ω => 2 * W.W s ω * (W.W t ω - W.W s ω))
            = (fun ω => 2 * (W.W s ω * (W.W t ω - W.W s ω))) := by
          funext ω; ring
        change MeasureTheory.Integrable
          (fun ω => 2 * W.W s ω * (W.W t ω - W.W s ω)) P
        rw [this]
        exact h_int_W_s_mul_inc.const_mul 2
      have h_int_inc_sq : MeasureTheory.Integrable
          (fun ω => (W.W t ω - W.W s ω)^2) P := by
        have h_pow := h_inc_memLp.integrable_norm_pow (p := 2) (by norm_num)
        convert h_pow using 1
        ext ω
        change (W.W t ω - W.W s ω)^2 = ‖W.W t ω - W.W s ω‖^2
        rw [Real.norm_eq_abs, sq_abs]
      have h_int_C : MeasureTheory.Integrable C P :=
        h_int_inc_sq.sub (MeasureTheory.integrable_const _)
      have h_int_BC : MeasureTheory.Integrable (B + C) P := h_int_B.add h_int_C
      -- Decomposition: (W_t)² - t = A + (B + C)
      have h_decomp : (fun ω => (W.W t ω)^2 - t) = A + (B + C) := by
        funext ω
        change (W.W t ω)^2 - t = (W.W s ω)^2 - s
          + (2 * W.W s ω * (W.W t ω - W.W s ω)
            + ((W.W t ω - W.W s ω)^2 - (t - s)))
        ring
      -- Reconcile representations. Since 0 ≤ s < t, max t 0 = t and max s 0 = s.
      have h_max_s : max s 0 = s := max_eq_left hs_nn
      have h_max_t : max t 0 = t := max_eq_left ht_nn
      change P[(fun ω => (W.W t ω)^2 - max t 0) | (naturalFiltration W).seq s]
        =ᶠ[ae P] fun ω => (W.W s ω)^2 - max s 0
      rw [h_max_s, h_max_t]
      rw [h_decomp]
      -- Apply linearity twice.
      have h_add1 := MeasureTheory.condExp_add h_int_A h_int_BC
        ((naturalFiltration W).seq s)
      have h_add2 := MeasureTheory.condExp_add h_int_B h_int_C
        ((naturalFiltration W).seq s)
      -- E[A | F_s] = A.
      have h_le : (naturalFiltration W).seq s ≤ ‹MeasurableSpace Ω› :=
        (naturalFiltration W).le' s
      have h_adapt_W_s := MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
      have h_adapt_A : @MeasureTheory.StronglyMeasurable Ω ℝ _
          ((naturalFiltration W).seq s) A :=
        (h_adapt_W_s.pow 2).sub MeasureTheory.stronglyMeasurable_const
      have h_self_A := MeasureTheory.condExp_of_stronglyMeasurable h_le h_adapt_A h_int_A
      -- E[B | F_s] = 0 (cross term).
      have h_zero_B := condExp_cross_increment_eq_zero_aux W hs_nn hst_lt
      -- E[C | F_s] = 0 (variance term: E[(W_t-W_s)² | F_s] - (t-s) = 0).
      have h_zero_C : P[C | (naturalFiltration W).seq s] =ᵐ[P] fun _ => 0 := by
        have h_C_eq : C = (fun ω => (W.W t ω - W.W s ω)^2) - (fun _ : Ω => t - s) := by
          funext ω; rfl
        change P[C | (naturalFiltration W).seq s] =ᵐ[P] fun _ => 0
        rw [h_C_eq]
        have h_sub := MeasureTheory.condExp_sub h_int_inc_sq
          (MeasureTheory.integrable_const (t - s))
          ((naturalFiltration W).seq s)
        have h_inc_sq := condExp_increment_sq_eq_var_aux W hs_nn hst_lt
        have h_const := MeasureTheory.condExp_const (μ := P) h_le (t - s)
        filter_upwards [h_sub, h_inc_sq] with ω h_sub_ω h_sq_ω
        rw [h_sub_ω, Pi.sub_apply, h_sq_ω]
        change t - s - P[fun _ : Ω => t - s | (naturalFiltration W).seq s] ω = 0
        rw [h_const]
        ring
      -- Combine
      filter_upwards [h_add1, h_add2, h_zero_B, h_zero_C]
        with ω h_add1_ω h_add2_ω h_B_ω h_C_ω
      change P[A + (B + C) | (naturalFiltration W).seq s] ω = A ω
      rw [h_add1_ω]
      change P[A | (naturalFiltration W).seq s] ω
        + P[B + C | (naturalFiltration W).seq s] ω = A ω
      rw [h_self_A, h_add2_ω]
      change A ω + (P[B | (naturalFiltration W).seq s] ω
                    + P[C | (naturalFiltration W).seq s] ω) = A ω
      rw [h_B_ω, h_C_ω]
      ring

/-- **CITED AXIOM: Brownian motion is a martingale w.r.t. the right-continuous
augmentation of its natural filtration.**

This is a consequence of Blumenthal's 0-1 law: events in the strict-future tail
σ-algebra `⋂_{s > 0} σ(W_u : u ≤ s)` are `P`-trivial, so the right-augmented
filtration adds no new information about the increments. Hence the martingale
property of `W` w.r.t. the natural filtration (already proven as
`brownian_martingale`) lifts to the right-augmentation.

**Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
Springer 1991, Theorem 2.7.7 (Blumenthal 0-1 law) + Theorem 2.7.9 (continuity
of the augmented filtration); Le Gall, J.-F. *Brownian Motion, Martingales and
Stochastic Calculus*, Springer 2016, Theorem 2.13 (correcting the previous
"Proposition 2.10" citation — Le Gall 2016 p. 25 "Lemma 2.10" is a deterministic
real-analysis Hölder lemma; Blumenthal 0-1 for Brownian motion is at Le Gall
p. 30 Theorem 2.13; see red-team finding H7 / P11).

**Replacement plan**: when Mathlib gains Blumenthal's 0-1 law for Brownian motion
(or the equivalent right-continuity theorem for the augmented filtration),
replace this `axiom` with a forwarder. Tracked in `tools/cited_axioms.md`. -/
axiom brownian_martingale_rightCont
    {Ω : Type u} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    MeasureTheory.Martingale (fun t : ℝ => W.W t)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont P

/-- The natural filtration of `W` (augmented by `P`-null sets) is
right-continuous. (Blumenthal 0-1 law follows as a corollary.)

Proof structure (Karatzas-Shreve 1991 Thm 2.7.7):
1. Define the augmented natural filtration `F̄_t := σ(F_t ∪ 𝓝)` where
   `𝓝` is the set of `P`-null sets.
2. Show `F̄_t = ⨅ s > t, F̄_s` by Blumenthal's 0-1 law: any event in the
   strict-future tail σ-algebra `⋂_{s > 0} σ(W_u : u ≤ s)` is `P`-trivial,
   implying right-continuity at `t = 0`. By translation invariance of BM
   the same holds at any `t`.
3. Verify `W` is a martingale w.r.t. the augmented filtration. -/
theorem brownian_filtration_rightContinuous
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale (fun t : ℝ => W.W t) F P
        ∧ ∀ t : ℝ, F t = ⨅ s : {s : ℝ // t < s}, F s.1 := by
  -- Take the right-continuous augmentation of the natural filtration of W.
  refine ⟨(naturalFiltration W).rightCont, ?_, ?_⟩
  · -- Martingale wrt rightCont via Blumenthal 0-1 (cited axiom).
    exact LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont W
  · intro t
    apply le_antisymm
    · refine le_iInf ?_
      intro s
      exact (naturalFiltration W).rightCont.mono' (le_of_lt s.2)
    · -- ⨅ s > t, F.rightCont s ≤ F.rightCont t  via IsRightContinuous.
      have h_RC : ((naturalFiltration W).rightCont).rightCont
          ≤ (naturalFiltration W).rightCont :=
        MeasureTheory.Filtration.IsRightContinuous.RC
      have h_le : (((naturalFiltration W).rightCont).rightCont : _ → _) t
          ≤ ((naturalFiltration W).rightCont : _ → _) t := h_RC t
      have h_iInf_eq : (((naturalFiltration W).rightCont).rightCont : _ → _) t
          = ⨅ s : {s : ℝ // t < s}, ((naturalFiltration W).rightCont : _ → _) s.1 := by
        classical
        conv_lhs => rw [MeasureTheory.Filtration.rightCont_def
          (naturalFiltration W).rightCont]
        simp only [iInf_subtype']
        split_ifs with h
        · rfl
        · exfalso
          apply h
          rw [show (Preorder.topology ℝ) =
              PseudoMetricSpace.toUniformSpace.toTopologicalSpace from
            (OrderTopology.topology_eq_generate_intervals).symm]
          exact nhdsGT_neBot t
      rw [← h_iInf_eq]
      exact h_le

end LevyStochCalc.Brownian.Martingale
