/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.MartingaleCondExp

/-!
# Brownian martingale property and quadratic variation

Brownian motion is a martingale for its natural filtration, hence for any filtration to which it
is adapted with independent increments, and its quadratic variation is `⟨W⟩_t = t`: the process
`W_t² − t` is again a martingale. The identity `(dW)² = dt` it records is the second-order term
of the Itô formula.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Martingale

universe u

section MartingaleAndQuadVar
variable {Ω : Type u} [MeasurableSpace Ω]

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
theorem brownian_martingale_natural
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    MeasureTheory.Martingale (fun t : ℝ => W.W t) (naturalFiltration W) P := by
  refine ⟨?_, ?_⟩
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

/-- Brownian motion is a martingale with respect to some filtration, namely its natural
filtration. -/
theorem brownian_martingale
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale (fun t : ℝ => W.W t) F P :=
  ⟨naturalFiltration W, brownian_martingale_natural W⟩

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

end MartingaleAndQuadVar

end LevyStochCalc.Brownian.Martingale
