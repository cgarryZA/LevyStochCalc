/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedSimple

/-!
# Second moments and L²-isometry of the simple compensated-Poisson integral

The mean-zero / second-moment (variance) identities for the compensated Poisson
measure `Ñ(B) = N(B) − ν̂(B)`, and the diagonal / off-diagonal computation for
`simpleIntegral` (orthogonality of disjoint compensated-Poisson increments) that
they feed, culminating in the simple-integrand L²-isometry `simpleIntegral_isometry`
and L²-membership `simpleIntegral_memLp_compensated`. Builds on the integrand
definitions in `Poisson/CompensatedSimple.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Per-term reduction:** `r^(n+1) / (n+1)! · (n+1) = r · (r^n / n!)`. -/
private lemma poisson_term_succ_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ)
    = r * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Series identity for Poisson mean.** `∑' n, r^n / n! · n = r · exp(r)`. -/
private lemma tsum_pow_div_factorial_mul_nat (r : ℝ) :
    ∑' n : ℕ, r ^ n / (n.factorial : ℝ) * (n : ℝ) = r * Real.exp r := by
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))
            = fun n => r * (r ^ n / (n.factorial : ℝ)) from
      funext (poisson_term_succ_eq r)]
    exact (Real.summable_pow_div_factorial r).mul_left r
  rw [tsum_eq_zero_add' h_summable_succ]
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Nat.cast_zero, mul_zero, zero_add]
  simp_rw [poisson_term_succ_eq r]
  rw [tsum_mul_left]
  congr 1
  rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Mean of `poissonMeasure r` is `r`.** Derived from `integral_poissonMeasure`
+ the series identity `∑' n, r^n / n! · n = r · exp(r)`. -/
private lemma poissonMeasure_integral_id (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  have h_smul_eq : ∀ n : ℕ,
      (Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)) • ((n : ℝ))
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n
    change Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ))
    ring
  simp_rw [h_smul_eq]
  rw [tsum_mul_left]
  rw [tsum_pow_div_factorial_mul_nat]
  rw [show Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) * Real.exp (↑r))
        = (↑r : ℝ) * (Real.exp (-(↑r : ℝ)) * Real.exp (↑r)) from by ring]
  rw [← Real.exp_add]
  rw [show (-(↑r : ℝ) + (↑r : ℝ)) = 0 from by ring]
  rw [Real.exp_zero, mul_one]

/-- **Summability of `r^n / n! · n` for r ≥ 0.** Used for integrability of `(n : ℝ)`
w.r.t. `poissonMeasure r`. -/
private lemma summable_pow_div_factorial_mul_nat (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) := by
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ))
            = fun n => r * (r ^ n / (n.factorial : ℝ)) from
      funext (poisson_term_succ_eq r)]
    exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Compensated-Poisson mean is zero.** For a measurable set `B` with finite
intensity, `∫ ω, Ñ(B, ω) ∂P = 0`. Follows from `E[N(B)] = ν̂(B)` (Poisson mean,
proved via `poissonMeasure_integral_id`). -/
lemma compensated_mean_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, N.compensated B ω ∂P = 0 := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  -- compensated B ω = (·.toReal - c) ∘ (N.N · B)
  have h_compensated_eq : (fun ω => N.compensated B ω) =
      (fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B) := by
    funext ω
    rfl
  rw [h_compensated_eq]
  -- Pushforward via integral_map
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => x.toReal - c) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c) ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable).symm]
  -- Apply poisson_law
  rw [N.poisson_law hB h_finite]
  -- Unfold poissonMeasureENN
  change ∫ x, (x.toReal - c) ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = 0
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    (ENNReal.measurable_toReal.sub_const _).aestronglyMeasurable]
  -- Simplify the cast (n : ℝ≥0∞).toReal = (n : ℝ)
  have h_phi_cast : ∀ n : ℕ, ((n : ℝ≥0∞)).toReal - c = (n : ℝ) - c := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp]
  simp_rw [h_phi_cast]
  -- Now goal: ∫ n, (n : ℝ) - c ∂(poissonMeasure r) = 0
  -- Establish integrability of (n : ℝ) w.r.t. poissonMeasure r
  have h_int_id : MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
    rw [ProbabilityTheory.integrable_poissonMeasure_iff]
    have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
      rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
    simp_rw [h_norm]
    have h_eq : ∀ n : ℕ, Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
        = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
      intro n; ring
    simp_rw [h_eq]
    exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => c) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  rw [MeasureTheory.integral_sub h_int_id h_int_const]
  rw [poissonMeasure_integral_id, MeasureTheory.integral_const]
  -- Goal: (↑r : ℝ) - (Measure.real (poissonMeasure r) Set.univ) • c = 0
  rw [show ((ProbabilityTheory.poissonMeasure r).real Set.univ : ℝ) = 1 from by
    rw [MeasureTheory.measureReal_def]
    simp [MeasureTheory.measure_univ]]
  rw [← h_c_eq_r]
  simp

/-- **Per-term reduction for `n²`:** `r^(n+1) / (n+1)! · (n+1)² = r · (n+1) · (r^n / n!)`. -/
private lemma poisson_term_succ_sq_eq (r : ℝ) (n : ℕ) :
    r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
    = r * ((n + 1 : ℕ) : ℝ) * (r ^ n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_pos n).ne'
  have hn1 : ((n + 1 : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
  rw [Nat.factorial_succ, pow_succ]
  push_cast
  field_simp

/-- **Summability of `r^n / n! · n²`** for any real `r`. -/
private lemma summable_pow_div_factorial_mul_nat_sq (r : ℝ) :
    Summable fun n : ℕ => r ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 := by
  have h_split : ∀ n : ℕ,
      r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
      = r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
        + r * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [poisson_term_succ_sq_eq r]
    push_cast
    ring
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)
            = fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
              + r * (r ^ n / (n.factorial : ℝ)) from
      funext h_split]
    refine Summable.add ?_ ?_
    · have h_eq : (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
              = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
        funext n; ring
      rw [h_eq]
      exact (summable_pow_div_factorial_mul_nat r).mul_left r
    · exact (Real.summable_pow_div_factorial r).mul_left r
  exact (summable_nat_add_iff 1).mp h_summable_succ

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Series identity:** `∑' n, r^n / n! · n² = (r² + r) · exp(r)`. -/
private lemma tsum_pow_div_factorial_mul_nat_sq (r : ℝ) :
    ∑' n : ℕ, r ^ n / (n.factorial : ℝ) * (n : ℝ) ^ 2 = (r ^ 2 + r) * Real.exp r := by
  have h_split : ∀ n : ℕ,
      r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2
      = r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
        + r * (r ^ n / (n.factorial : ℝ)) := by
    intro n
    rw [poisson_term_succ_sq_eq r]
    push_cast
    ring
  have h_summable_n : Summable fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)) := by
    have h_eq : (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
            = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) := by
      funext n; ring
    rw [h_eq]
    exact (summable_pow_div_factorial_mul_nat r).mul_left r
  have h_summable_const : Summable fun n : ℕ => r * (r ^ n / (n.factorial : ℝ)) :=
    (Real.summable_pow_div_factorial r).mul_left r
  have h_summable_succ : Summable
      fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2 := by
    rw [show (fun n : ℕ => r ^ (n + 1) / ((n + 1).factorial : ℝ) * ((n + 1 : ℕ) : ℝ) ^ 2)
            = fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ))
              + r * (r ^ n / (n.factorial : ℝ)) from
      funext h_split]
    exact h_summable_n.add h_summable_const
  rw [tsum_eq_zero_add' h_summable_succ]
  -- 0 term: r^0/0! * 0² = 0
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, zero_add]
  simp_rw [h_split]
  rw [Summable.tsum_add h_summable_n h_summable_const]
  -- Goal: (∑' n, r * n * (r^n/n!)) + (∑' n, r * (r^n/n!)) = (r² + r) * exp(r)
  rw [show (fun n : ℕ => r * (n : ℝ) * (r ^ n / (n.factorial : ℝ)))
          = fun n : ℕ => r * (r ^ n / (n.factorial : ℝ) * (n : ℝ)) from by
    funext n; ring]
  rw [tsum_mul_left, tsum_pow_div_factorial_mul_nat]
  rw [tsum_mul_left]
  have h_exp : ∑' n : ℕ, r ^ n / (n.factorial : ℝ) = Real.exp r := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [h_exp]
  ring

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Second moment of `poissonMeasure r`:** `∫ n, (n : ℝ)² ∂poissonMeasure r = r² + r`. -/
private lemma poissonMeasure_integral_id_sq (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (r : ℝ) ^ 2 + (r : ℝ) := by
  rw [ProbabilityTheory.integral_poissonMeasure]
  have h_smul_eq : ∀ n : ℕ,
      (Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ)) • ((n : ℝ) ^ 2)
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2) := by
    intro n
    change Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2
        = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ) ^ 2)
    ring
  simp_rw [h_smul_eq]
  rw [tsum_mul_left]
  rw [tsum_pow_div_factorial_mul_nat_sq]
  rw [show Real.exp (-(↑r : ℝ)) * (((↑r : ℝ) ^ 2 + (↑r : ℝ)) * Real.exp (↑r))
        = ((↑r : ℝ) ^ 2 + (↑r : ℝ)) * (Real.exp (-(↑r : ℝ)) * Real.exp (↑r)) from by ring]
  rw [← Real.exp_add]
  rw [show (-(↑r : ℝ) + (↑r : ℝ)) = 0 from by ring]
  rw [Real.exp_zero, mul_one]

/-- Integrability of `(n : ℝ)` w.r.t. `poissonMeasure r`. -/
private lemma integrable_id_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable (fun n : ℕ => (n : ℝ)) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ))‖ = (n : ℝ) := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (Nat.cast_nonneg n)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ, Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat (↑r)).mul_left _

/-- Integrability of `(n : ℝ)²` w.r.t. `poissonMeasure r`. -/
private lemma integrable_id_sq_poissonMeasure (r : ℝ≥0) :
    MeasureTheory.Integrable
      (fun n : ℕ => (n : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) := by
  rw [ProbabilityTheory.integrable_poissonMeasure_iff]
  have h_norm : ∀ n : ℕ, ‖((n : ℝ) ^ 2)‖ = (n : ℝ) ^ 2 := fun n => by
    rw [Real.norm_eq_abs]; exact abs_of_nonneg (sq_nonneg _)
  simp_rw [h_norm]
  have h_eq : ∀ n : ℕ, Real.exp (-(↑r : ℝ)) * (↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2
      = Real.exp (-(↑r : ℝ)) * ((↑r : ℝ) ^ n / (↑n.factorial : ℝ) * (↑n : ℝ)^2) := by
    intro n; ring
  simp_rw [h_eq]
  exact (summable_pow_div_factorial_mul_nat_sq (↑r)).mul_left _

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Variance of `poissonMeasure r`:** `∫ n, ((n:ℝ) − r)² ∂poissonMeasure r = r`.
Mean `r`, second moment `r²+r`, variance `(r²+r) − r² = r`. -/
private lemma poissonMeasure_variance (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) = (r : ℝ) := by
  have h_int_n := integrable_id_poissonMeasure r
  have h_int_nsq := integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ) ^ 2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  -- Expand (n - r)² = n² - 2rn + r², explicitly stated as ((n² - 2rn) + r²) for additivity.
  have h_expand : ∀ n : ℕ, ((n : ℝ) - (r : ℝ)) ^ 2
      = ((n : ℝ) ^ 2 - 2 * (r : ℝ) * (n : ℝ)) + (r : ℝ) ^ 2 := by
    intro n; ring
  simp_rw [h_expand]
  -- Use integral linearity step-by-step. To avoid Pi.sub_apply matching issues,
  -- compute each integral as a have-hypothesis and combine via calc.
  have h_e_nsq : ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
      = (↑r : ℝ) ^ 2 + (↑r : ℝ) := poissonMeasure_integral_id_sq r
  have h_e_2rn : ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r)
      = 2 * (↑r : ℝ) * (↑r : ℝ) := by
    rw [MeasureTheory.integral_const_mul]
    rw [poissonMeasure_integral_id]
  have h_e_csq : ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) = (↑r : ℝ) ^ 2 := by
    rw [MeasureTheory.integral_const]
    rw [show (ProbabilityTheory.poissonMeasure r).real Set.univ = 1 from by
      rw [MeasureTheory.measureReal_def]; simp [MeasureTheory.measure_univ]]
    rw [one_smul]
  -- ∫ ((n² - 2rn) + r²) = ∫ (n² - 2rn) + ∫ r²
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ)) + (↑r : ℝ) ^ 2
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
          ∂(ProbabilityTheory.poissonMeasure r)
        + ∫ _ : ℕ, (↑r : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_add (h_int_nsq.sub h_int_2rn) h_int_const]
  -- ∫ (n² - 2rn) = ∫ n² - ∫ 2rn
  rw [show
      ∫ n : ℕ, ((n : ℝ) ^ 2 - 2 * (↑r : ℝ) * (n : ℝ))
        ∂(ProbabilityTheory.poissonMeasure r)
      = ∫ n : ℕ, (n : ℝ) ^ 2 ∂(ProbabilityTheory.poissonMeasure r)
        - ∫ n : ℕ, 2 * (↑r : ℝ) * (n : ℝ) ∂(ProbabilityTheory.poissonMeasure r) from
    MeasureTheory.integral_sub h_int_nsq h_int_2rn]
  rw [h_e_nsq, h_e_2rn, h_e_csq]
  ring

set_option maxHeartbeats 400000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
lemma compensated_second_moment
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    ∫ ω, (N.compensated B ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (Ñ(B,ω))² = ((·).toReal - c)² ∘ (N.N · B)
  have h_compensated_sq_eq : (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) := by
    funext ω; rfl
  rw [h_compensated_sq_eq]
  rw [show (∫ ω, ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B)) ω ∂P)
      = ∫ x, (x.toReal - c)^2 ∂(P.map (fun ω => N.N ω B)) from
    (MeasureTheory.integral_map h_NB_meas.aemeasurable
      h_meas_phi.aestronglyMeasurable).symm]
  rw [N.poisson_law hB h_finite]
  change ∫ x, (x.toReal - c)^2 ∂((ProbabilityTheory.poissonMeasure r).map
    (fun n : ℕ => (n : ℝ≥0∞))) = c
  rw [MeasureTheory.integral_map measurable_from_nat.aemeasurable
    h_meas_phi.aestronglyMeasurable]
  have h_phi_cast : ∀ n : ℕ, (((n : ℝ≥0∞)).toReal - c) ^ 2 = ((n : ℝ) - (r : ℝ)) ^ 2 := by
    intro n
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  simp_rw [h_phi_cast]
  rw [poissonMeasure_variance r]
  exact h_c_eq_r.symm

/-- **Integrability of `(N.compensated B)²` w.r.t. P.** Follows from pushforward
through `poisson_law` + integrability of `(n − r)²` w.r.t. `poissonMeasure r`. -/
private lemma compensated_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B)
    (h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    MeasureTheory.Integrable (fun ω => (N.compensated B ω)^2) P := by
  set c : ℝ := (LevyStochCalc.Poisson.referenceIntensity ν B).toReal with hc_def
  set r : ℝ≥0 := (LevyStochCalc.Poisson.referenceIntensity ν B).toNNReal with hr_def
  have h_c_eq_r : c = (r : ℝ) := by
    rw [hc_def, hr_def, ENNReal.coe_toNNReal_eq_toReal]
  have h_NB_meas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have h_meas_phi_sq : Measurable (fun x : ℝ≥0∞ => (x.toReal - c)^2) :=
    (ENNReal.measurable_toReal.sub_const _).pow_const 2
  -- (compensated B)² = ((·).toReal - c)² ∘ (N.N · B). Lift through pushforwards.
  rw [show (fun ω => (N.compensated B ω)^2) =
      (fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun ω => N.N ω B) from rfl]
  -- Step 1: convert Integrable (g ∘ f) P → Integrable g (P.map f) via the iff.
  rw [← MeasureTheory.integrable_map_measure (μ := P) (f := fun ω => N.N ω B)
      h_meas_phi_sq.aestronglyMeasurable h_NB_meas.aemeasurable]
  -- Step 2: replace P.map with poissonMeasureENN via poisson_law.
  rw [N.poisson_law hB h_finite]
  -- Step 3: unfold poissonMeasureENN = (poissonMeasure r).map Nat.cast.
  change MeasureTheory.Integrable (fun x : ℝ≥0∞ => (x.toReal - c)^2)
    ((ProbabilityTheory.poissonMeasure r).map (fun n : ℕ => (n : ℝ≥0∞)))
  -- Step 4: convert Integrable g (μ.map f) → Integrable (g ∘ f) μ.
  rw [MeasureTheory.integrable_map_measure
      (μ := ProbabilityTheory.poissonMeasure r) (f := fun n : ℕ => (n : ℝ≥0∞))
      h_meas_phi_sq.aestronglyMeasurable measurable_from_nat.aemeasurable]
  -- Now goal: Integrable ((fun x => (x.toReal - c)^2) ∘ Nat.cast) (poissonMeasure r)
  -- Simplify (↑n : ℝ≥0∞).toReal = (n : ℝ); use c = (r : ℝ).
  have h_simp : ((fun x : ℝ≥0∞ => (x.toReal - c)^2) ∘ (fun n : ℕ => (n : ℝ≥0∞)))
              = fun n : ℕ => ((n : ℝ) - (r : ℝ))^2 := by
    funext n
    change (((n : ℝ≥0∞)).toReal - c)^2 = ((n : ℝ) - (r : ℝ))^2
    rw [show ((n : ℝ≥0∞)).toReal = (n : ℝ) from by simp, h_c_eq_r]
  rw [h_simp]
  -- Expand (n - r)² = (n² - 2rn) + r².
  have h_eq : (fun n : ℕ => ((n : ℝ) - (r : ℝ))^2)
            = fun n : ℕ => (((n : ℝ)^2) - (2 * (r : ℝ) * (n : ℝ))) + (r : ℝ)^2 := by
    funext n; ring
  rw [h_eq]
  have h_int_n := integrable_id_poissonMeasure r
  have h_int_nsq := integrable_id_sq_poissonMeasure r
  have h_int_const : MeasureTheory.Integrable
      (fun _ : ℕ => (r : ℝ)^2) (ProbabilityTheory.poissonMeasure r) :=
    MeasureTheory.integrable_const _
  have h_int_2rn : MeasureTheory.Integrable
      (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (ProbabilityTheory.poissonMeasure r) :=
    h_int_n.const_mul (2 * (r : ℝ))
  exact (h_int_nsq.sub h_int_2rn).add h_int_const

/-- **Diagonal contribution.** `∫⁻ ‖ξ_i · Ñ(B_i, ·)‖² ∂P
= referenceIntensity(B_i) · ∫⁻ ‖ξ_i‖² ∂P` where `B_i := (t_i, t_{i+1}] × A_i`.

Mirrors `Brownian.Ito.simpleIntegral_diagonal`. Uses
`joint_past_future_independent` for IndepFun ξ_i, Ñ(B_i) +
`compensated_second_moment` for the variance computation. -/
lemma simpleIntegral_diagonal
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_part_nn : 0 ≤ φ.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫⁻ ω, (‖φ.ξ i ω * N.compensated (φ.timeRect i T) ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)
          * ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set s := φ.partition i.castSucc with hs_def
  set t := φ.partition i.succ with ht_def
  set A := φ.A i with hA_def
  -- Reduce timeRect to (s, t] × A using partition_le_T.
  have h_t_le_T : t ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_s_le_T : s ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_timeRect_eq : φ.timeRect i T = Set.Ioc s t ×ˢ A := by
    unfold SimplePredictable.timeRect
    rw [min_eq_left h_s_le_T, min_eq_left h_t_le_T]
  rw [h_timeRect_eq]
  set B : Set (ℝ × E) := Set.Ioc s t ×ˢ A with hB_def
  set ÑB : Ω → ℝ := fun ω => N.compensated B ω with hÑB_def
  set ξi : Ω → ℝ := φ.ξ i with hξi_def
  have hst : s < t := φ.partition_strictMono Fin.castSucc_lt_succ
  have h_B_meas : MeasurableSet B :=
    measurableSet_Ioc.prod (φ.A_measurable i)
  have h_ξi_meas : Measurable ξi := φ.ξ_measurable i
  have h_ÑB_meas : Measurable ÑB := by
    change Measurable (fun ω => (N.N ω B).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
    refine Measurable.sub ?_ ?_
    · exact ENNReal.measurable_toReal.comp (N.measurable_eval h_B_meas)
    · exact measurable_const
  -- Step 1: Show IndepFun ξi ÑB.
  -- B = Set.Ioc s t ×ˢ A, so B ⊆ (s, t] × E type set.
  have h_indep_struct := N.joint_past_future_independent h_part_nn hst
    (φ.A_measurable i) (φ.A_finite i)
  have h_ξi_comap_le :
      MeasurableSpace.comap ξi inferInstance ≤
        ⨆ B' ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N.N ω B') inferInstance := by
    -- ξi is measurable w.r.t. the past σ-algebra (h_adapt).
    have h_ξi_past : @Measurable Ω ℝ
        (⨆ B' ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N.N ω B') inferInstance) _ ξi :=
      h_adapt.measurable
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact h_ξi_past hv
  have h_ÑB_comap_le :
      MeasurableSpace.comap ÑB inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc s t ×ˢ A)) inferInstance := by
    -- ÑB is a measurable function of N(B), so its σ-algebra is contained in σ(N(B)).
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    -- ÑB = N(B).toReal - ν̂(B).toReal, so ÑB⁻¹(v) = N(B)⁻¹((·.toReal - c)⁻¹(v))
    -- for c = ν̂(B).toReal
    refine ⟨(fun x : ℝ≥0∞ =>
        x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B).toReal) ⁻¹' v,
      ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · ext ω; rfl
  have h_indep_ξ_ÑB : ProbabilityTheory.IndepFun ξi ÑB P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : @MeasurableSet Ω
        (⨆ B' ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N.N ω B') inferInstance) u :=
      h_ξi_comap_le u hu
    have hv_F : @MeasurableSet Ω
        (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc s t ×ˢ A)) inferInstance) v :=
      h_ÑB_comap_le v hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_struct
    exact h_indep_struct u v hu_F hv_F
  -- Step 2: Compose with norm² to get IndepFun on ENNReal.
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2) (fun ω => (‖ÑB ω‖₊ : ℝ≥0∞)^2) P := by
    have := h_indep_ξ_ÑB.comp h_nn_meas h_nn_meas
    simpa [Function.comp] using this
  -- Step 3: ‖ξ · ÑB‖² = ‖ξ‖² · ‖ÑB‖² pointwise.
  have h_norm_mul : ∀ ω, (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞)^2
      = (‖ξi ω‖₊ : ℝ≥0∞)^2 * (‖ÑB ω‖₊ : ℝ≥0∞)^2 := by
    intro ω
    rw [show (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞)
        = (‖ξi ω‖₊ : ℝ≥0∞) * (‖ÑB ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞) = ((‖ξi ω * ÑB ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξi ω * ÑB ω‖₊ : ℝ≥0) = ‖ξi ω‖₊ * ‖ÑB ω‖₊ from nnnorm_mul _ _]
      push_cast; rfl]
    ring
  -- Step 4: Apply lintegral_mul.
  rw [show (∫⁻ ω, (‖ξi ω * ÑB ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξi ω‖₊ : ℝ≥0∞)^2 * (‖ÑB ω‖₊ : ℝ≥0∞)^2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2 * (‖ÑB ω‖₊ : ℝ≥0∞)^2)
      = (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2) * (fun ω => (‖ÑB ω‖₊ : ℝ≥0∞)^2) from rfl]
  have h_ξi_norm_sq_meas : Measurable (fun ω => (‖ξi ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_ÑB_norm_sq_meas : Measurable (fun ω => (‖ÑB ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξi_norm_sq_meas h_ÑB_norm_sq_meas h_indep_norm_sq]
  -- Step 5: Compute ∫⁻ ‖ÑB‖² ∂P = referenceIntensity ν B.
  have h_finite : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤ := by
    -- referenceIntensity ν B = (volume.restrict (Ici 0)).prod ν (Ioc s t ×ˢ A)
    --                       = volume.restrict (Ici 0) (Ioc s t) * ν A
    -- Both finite: time interval has length ≤ t-s < ⊤; ν A < ⊤ by hypothesis.
    unfold LevyStochCalc.Poisson.referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
    -- volume.restrict (Ici 0) (Ioc s t) ≤ volume (Ioc s t) = ENNReal.ofReal (t - s) < ⊤
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  rw [show (∫⁻ ω, (‖ÑB ω‖₊ : ℝ≥0∞)^2 ∂P)
        = LevyStochCalc.Poisson.referenceIntensity ν B from ?_]
  · ring
  · -- ∫⁻ ‖ÑB‖² = ENNReal.ofReal(∫ ÑB²) = ENNReal.ofReal(ν̂(B).toReal) = ν̂(B).
    have h_ÑB_int : MeasureTheory.Integrable (fun ω => (ÑB ω)^2) P :=
      compensated_sq_integrable N h_B_meas h_finite
    have h_nn_sq : 0 ≤ᵐ[P] fun ω => (ÑB ω)^2 := by
      filter_upwards with ω
      positivity
    have h_norm_eq : ∀ ω, (‖ÑB ω‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal ((ÑB ω)^2) := by
      intro ω
      rw [show (‖ÑB ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖ÑB ω‖ from
        ofReal_norm_eq_enorm (ÑB ω) |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖ÑB ω‖^2 = (ÑB ω)^2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ ω, (‖ÑB ω‖₊ : ℝ≥0∞)^2 ∂P)
            = ∫⁻ ω, ENNReal.ofReal ((ÑB ω)^2) ∂P from
      MeasureTheory.lintegral_congr (fun ω => h_norm_eq ω)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_ÑB_int h_nn_sq]
    rw [compensated_second_moment N h_B_meas h_finite]
    -- ENNReal.ofReal((ν̂ B).toReal) = ν̂ B (when ν̂ B is finite).
    exact ENNReal.ofReal_toReal h_finite

/-- **Off-diagonal vanishing.** For `i < j`,
`∫ ω, (ξ_i · Ñ(B_i))(ξ_j · Ñ(B_j)) ∂P = 0`.

Mirror of `Brownian.Ito.simpleIntegral_offDiagonal`. The key point: for
`i < j`, the time intervals `(t_i, t_{i+1}]` and `(t_j, t_{j+1}]` are
disjoint, with `t_{i+1} ≤ t_j`. So `f := ξ_i · Ñ(B_i) · ξ_j` is measurable
w.r.t. the past at time `t_j_pre`, independent of `Ñ(B_j)` (the future increment).
Since `E[Ñ(B_j)] = 0` (compensated mean), `E[f · Ñ(B_j)] = E[f] · 0 = 0`. -/
lemma simpleIntegral_offDiagonal
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {i j : Fin φ.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition j.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ j)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω) *
         (φ.ξ j ω * N.compensated (φ.timeRect j T) ω) ∂P = 0 := by
  set t_i_pre : ℝ := φ.partition i.castSucc with hti0_def
  set t_i : ℝ := φ.partition i.succ with hti_def
  set t_j_pre : ℝ := φ.partition j.castSucc with htj0_def
  set t_j : ℝ := φ.partition j.succ with htj_def
  set A_i := φ.A i with hAi_def
  set A_j := φ.A j with hAj_def
  -- Partition monotonicity
  have h_part_zero_le_i_pre : 0 ≤ t_i_pre := by
    have : φ.partition 0 ≤ φ.partition i.castSucc :=
      φ.partition_strictMono.monotone (Fin.zero_le _)
    rw [φ.partition_zero] at this; exact this
  have h_i_pre_lt : t_i_pre < t_i := φ.partition_strictMono Fin.castSucc_lt_succ
  have h_i_le_j_pre : t_i ≤ t_j_pre :=
    φ.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
  have h_j_pre_lt : t_j_pre < t_j := φ.partition_strictMono Fin.castSucc_lt_succ
  have h_j_pre_nn : 0 ≤ t_j_pre :=
    h_part_zero_le_i_pre.trans ((le_of_lt h_i_pre_lt).trans h_i_le_j_pre)
  have h_t_i_pre_le_t_j_pre : t_i_pre ≤ t_j_pre :=
    (le_of_lt h_i_pre_lt).trans h_i_le_j_pre
  -- Reduce timeRect to (t_i_pre, t_i] × A_i and (t_j_pre, t_j] × A_j.
  have h_t_i_le_T : t_i ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_t_i_pre_le_T : t_i_pre ≤ T := le_of_lt (h_i_pre_lt.trans_le h_t_i_le_T)
  have h_t_j_le_T : t_j ≤ T := by
    refine le_trans ?_ φ.partition_le_T
    exact φ.partition_strictMono.monotone (Fin.le_last _)
  have h_t_j_pre_le_T : t_j_pre ≤ T := le_of_lt (h_j_pre_lt.trans_le h_t_j_le_T)
  have h_timeRect_i : φ.timeRect i T = Set.Ioc t_i_pre t_i ×ˢ A_i := by
    unfold SimplePredictable.timeRect
    rw [min_eq_left h_t_i_pre_le_T, min_eq_left h_t_i_le_T]
  have h_timeRect_j : φ.timeRect j T = Set.Ioc t_j_pre t_j ×ˢ A_j := by
    unfold SimplePredictable.timeRect
    rw [min_eq_left h_t_j_pre_le_T, min_eq_left h_t_j_le_T]
  rw [h_timeRect_i, h_timeRect_j]
  set B_i : Set (ℝ × E) := Set.Ioc t_i_pre t_i ×ˢ A_i with hBi_def
  set B_j : Set (ℝ × E) := Set.Ioc t_j_pre t_j ×ˢ A_j with hBj_def
  set ÑB_i : Ω → ℝ := fun ω => N.compensated B_i ω with hÑBi_def
  set ÑB_j : Ω → ℝ := fun ω => N.compensated B_j ω with hÑBj_def
  set ξi : Ω → ℝ := φ.ξ i with hξi_def
  set ξj : Ω → ℝ := φ.ξ j with hξj_def
  -- Box measurability
  have h_B_i_meas : MeasurableSet B_i := measurableSet_Ioc.prod (φ.A_measurable i)
  have h_B_j_meas : MeasurableSet B_j := measurableSet_Ioc.prod (φ.A_measurable j)
  -- Standard-σ-algebra measurability of the building blocks
  have h_ξi_meas : Measurable ξi := φ.ξ_measurable i
  have h_ξj_meas : Measurable ξj := φ.ξ_measurable j
  have h_ÑB_i_meas : Measurable ÑB_i := by
    change Measurable (fun ω => (N.N ω B_i).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B_i).toReal)
    exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_i_meas)).sub_const _
  have h_ÑB_j_meas : Measurable ÑB_j := by
    change Measurable (fun ω => (N.N ω B_j).toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B_j).toReal)
    exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_j_meas)).sub_const _
  -- B_i ⊆ Set.Iic t_j_pre × Set.univ (since t_i ≤ t_j_pre)
  have h_B_i_in_past_j : B_i ⊆ Set.Iic t_j_pre ×ˢ Set.univ := by
    intro x hx
    obtain ⟨hx_time, _⟩ := Set.mem_prod.mp hx
    exact Set.mem_prod.mpr ⟨(Set.mem_Ioc.mp hx_time).2.trans h_i_le_j_pre, Set.mem_univ _⟩
  -- past-at-t_i_pre ≤ past-at-t_j_pre (since t_i_pre ≤ t_j_pre)
  have h_pastIp_le_pastJp :
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_i_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) ≤
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) := by
    refine iSup_le (fun B => iSup_le (fun hB => ?_))
    refine le_iSup_of_le B (le_iSup_of_le ⟨?_, hB.2⟩ le_rfl)
    refine hB.1.trans (Set.prod_mono ?_ Set.Subset.rfl)
    exact Set.Iic_subset_Iic.mpr h_t_i_pre_le_t_j_pre
  -- ξi is past-at-t_j_pre measurable (lift h_adapt_i via .mono)
  have h_ξi_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) ξi :=
    h_adapt_i.mono h_pastIp_le_pastJp
  -- σ(N(B_i)) ≤ past-at-t_j_pre (since B_i is in the past family)
  have h_NBi_in_pastJp :
      MeasurableSpace.comap (fun ω => N.N ω B_i) inferInstance ≤
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) :=
    le_iSup_of_le B_i (le_iSup_of_le ⟨h_B_i_in_past_j, h_B_i_meas⟩ le_rfl)
  -- N(B_i) is past-at-t_j_pre measurable
  have h_NBi_self : @Measurable Ω ℝ≥0∞
      (MeasurableSpace.comap (fun ω => N.N ω B_i) inferInstance) _
      (fun ω => N.N ω B_i) := fun u hu => ⟨u, hu, rfl⟩
  have h_NBi_pastJp_meas : @Measurable Ω ℝ≥0∞
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) _
      (fun ω => N.N ω B_i) :=
    h_NBi_self.mono h_NBi_in_pastJp le_rfl
  -- ÑB_i = (N(B_i)).toReal - c is past-at-t_j_pre measurable
  -- Stated in unfolded form to avoid `show` σ-algebra inference issues.
  have h_ÑB_i_pastJp_meas_unfolded : @Measurable Ω ℝ
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) _
      (fun ω => (N.N ω B_i).toReal -
        (LevyStochCalc.Poisson.referenceIntensity ν B_i).toReal) :=
    (ENNReal.measurable_toReal.sub_const _).comp h_NBi_pastJp_meas
  have h_ÑB_i_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) ÑB_i :=
    h_ÑB_i_pastJp_meas_unfolded.stronglyMeasurable
  -- ξj is past-at-t_j_pre measurable directly
  have h_ξj_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) ξj :=
    h_adapt_j
  -- f := ξi · ÑB_i · ξj is past-at-t_j_pre measurable
  set f : Ω → ℝ := fun ω => ξi ω * ÑB_i ω * ξj ω with hf_def
  have h_f_pastJp : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) f :=
    (h_ξi_pastJp.mul h_ÑB_i_pastJp).mul h_ξj_pastJp
  -- Factor (ξi · ÑB_i)(ξj · ÑB_j) = f · ÑB_j
  have h_factored : (fun ω => (ξi ω * ÑB_i ω) * (ξj ω * ÑB_j ω))
      = fun ω => f ω * ÑB_j ω := by
    funext ω
    change (ξi ω * ÑB_i ω) * (ξj ω * ÑB_j ω) = ξi ω * ÑB_i ω * ξj ω * ÑB_j ω
    ring
  rw [show (fun ω => (φ.ξ i ω * N.compensated (Set.Ioc t_i_pre t_i ×ˢ A_i) ω) *
              (φ.ξ j ω * N.compensated (Set.Ioc t_j_pre t_j ×ˢ A_j) ω))
        = fun ω => f ω * ÑB_j ω from h_factored]
  -- Step: σ(f) ⊥ σ(ÑB_j) under P (joint past/future independence)
  have h_indep_struct := N.joint_past_future_independent h_j_pre_nn h_j_pre_lt
    (φ.A_measurable j) (φ.A_finite j)
  have h_f_meas : Measurable f :=
    (h_ξi_meas.mul h_ÑB_i_meas).mul h_ξj_meas
  have h_f_comap_le :
      MeasurableSpace.comap f inferInstance ≤
        ⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N.N ω B) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact h_f_pastJp.measurable hv
  have h_ÑB_j_comap_le :
      MeasurableSpace.comap ÑB_j inferInstance ≤
        MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc t_j_pre t_j ×ˢ A_j)) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    refine ⟨(fun x : ℝ≥0∞ => x.toReal -
      (LevyStochCalc.Poisson.referenceIntensity ν B_j).toReal) ⁻¹' v, ?_, ?_⟩
    · exact (ENNReal.measurable_toReal.sub_const _) hv
    · ext ω; rfl
  have h_indep_f_ÑB_j : ProbabilityTheory.IndepFun f ÑB_j P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : @MeasurableSet Ω
        (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic t_j_pre ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) u :=
      h_f_comap_le u hu
    have hv_F : @MeasurableSet Ω
        (MeasurableSpace.comap (fun ω => N.N ω (Set.Ioc t_j_pre t_j ×ˢ A_j)) inferInstance) v :=
      h_ÑB_j_comap_le v hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_struct
    exact h_indep_struct u v hu_F hv_F
  -- ν̂(B_j) ≠ ⊤ (needed for compensated_mean_zero)
  have h_finite_j : LevyStochCalc.Poisson.referenceIntensity ν B_j ≠ ⊤ := by
    unfold LevyStochCalc.Poisson.referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite j)
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  -- E[ÑB_j] = 0 via compensated_mean_zero
  have h_ÑB_j_mean : ∫ ω, ÑB_j ω ∂P = 0 :=
    compensated_mean_zero N h_B_j_meas h_finite_j
  -- E[f · ÑB_j] = E[f] · E[ÑB_j] = E[f] · 0 = 0
  rw [show (fun ω => f ω * ÑB_j ω) = f * ÑB_j from rfl]
  rw [h_indep_f_ÑB_j.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ÑB_j_meas.aestronglyMeasurable]
  rw [h_ÑB_j_mean, mul_zero]

/-- **Bochner version of `simpleIntegral_diagonal`.** Converts the lintegral form to
the Bochner form via `ofReal_integral_eq_lintegral_ofReal`. -/
private lemma simpleIntegral_diagonal_bochner
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_part_nn : 0 ≤ φ.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal *
        ∫ ω, (φ.ξ i ω)^2 ∂P := by
  -- Common identity: (‖x‖₊ : ℝ≥0∞)² = ENNReal.ofReal(x²) for x : ℝ.
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm_eq_enorm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  -- Get the lintegral version of diagonal.
  have h_lint := simpleIntegral_diagonal N φ i h_part_nn h_adapt
  -- Rewrite (‖·‖)² to ENNReal.ofReal(·²) on both sides.
  rw [show (∫⁻ ω, (‖φ.ξ i ω * N.compensated (φ.timeRect i T) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((φ.ξ i ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  -- Establish integrability of ξ_i² and (ξ_i · Ñ_i)².
  have h_xi_bound : ∃ M : ℝ, ∀ ω : Ω, |φ.ξ i ω| ≤ M := φ.ξ_bounded i
  obtain ⟨M, hM⟩ := h_xi_bound
  have h_xi_sq_bound : ∀ ω : Ω, (φ.ξ i ω)^2 ≤ M^2 := by
    intro ω
    have := sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
    exact this
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (φ.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_B_meas : MeasurableSet (φ.timeRect i T) := by
    unfold SimplePredictable.timeRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_finite : LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T) ≠ ⊤ := by
    unfold SimplePredictable.timeRect LevyStochCalc.Poisson.referenceIntensity
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (φ.A_finite i)
    refine ne_top_of_le_ne_top ?_ (MeasureTheory.Measure.restrict_le_self _)
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have h_int_compensated_sq : MeasureTheory.Integrable
      (fun ω => (N.compensated (φ.timeRect i T) ω)^2) P :=
    compensated_sq_integrable N h_B_meas h_finite
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2) P := by
    -- (ξ_i · Ñ)² = ξ_i² · Ñ². Bounded × integrable.
    have h_eq : ∀ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2
              = (φ.ξ i ω)^2 * (N.compensated (φ.timeRect i T) ω)^2 := fun ω => by ring
    rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2)
            = fun ω => (φ.ξ i ω)^2 * (N.compensated (φ.timeRect i T) ω)^2 from
      funext h_eq]
    refine MeasureTheory.Integrable.bdd_mul (c := M^2) h_int_compensated_sq
      ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (φ.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2 := by
    filter_upwards with ω; positivity
  -- Apply ofReal_integral_eq_lintegral_ofReal to convert lintegral to ENNReal.ofReal of Bochner.
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  -- h_lint : ofReal(∫ (ξ_i · Ñ)²) = ν̂ * ofReal(∫ ξ_i²)
  -- Combine ν̂ * ofReal(...) into ofReal of product.
  have h_xi_int_nn : 0 ≤ ∫ ω, (φ.ξ i ω)^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_aN_int_nn : 0 ≤ ∫ ω, (φ.ξ i ω * N.compensated (φ.timeRect i T) ω)^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  rw [show LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T) *
          ENNReal.ofReal (∫ ω, (φ.ξ i ω)^2 ∂P)
          = ENNReal.ofReal
              ((LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal *
                ∫ ω, (φ.ξ i ω)^2 ∂P) from by
    conv_lhs =>
      rw [show LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)
            = ENNReal.ofReal
                (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal from
        (ENNReal.ofReal_toReal h_finite).symm]
    rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]] at h_lint
  -- h_lint: ENNReal.ofReal(∫ (ξ_i · Ñ)²) = ENNReal.ofReal(ν̂.toReal · ∫ ξ_i²)
  -- Apply ENNReal.ofReal injective on ≥ 0.
  have h_rhs_nn : 0 ≤ (LevyStochCalc.Poisson.referenceIntensity ν (φ.timeRect i T)).toReal *
                      ∫ ω, (φ.ξ i ω)^2 ∂P :=
    mul_nonneg ENNReal.toReal_nonneg h_xi_int_nn
  exact (ENNReal.ofReal_eq_ofReal_iff h_aN_int_nn h_rhs_nn).mp h_lint

/-- **`simpleIntegral` as a sum over `fullRect i` (drops the `min` in `timeRect`).** -/
lemma simpleIntegral_eq_sum_fullRect
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (ω : Ω) :
    simpleIntegral N φ T ω
      = ∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω := by
  unfold simpleIntegral SimplePredictable.timeRect SimplePredictable.fullRect
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 2
  have h_t_i_succ_le_T : φ.partition i.succ ≤ T :=
    le_trans (φ.partition_strictMono.monotone (Fin.le_last _)) φ.partition_le_T
  have h_t_i_pre_le_T : φ.partition i.castSucc ≤ T := by
    refine le_of_lt ?_
    exact (φ.partition_strictMono Fin.castSucc_lt_succ).trans_le h_t_i_succ_le_T
  rw [min_eq_left h_t_i_pre_le_T, min_eq_left h_t_i_succ_le_T]

/-- **Bochner integrability of `ξ_i² · Ñ_j²` (cross product of squares).**
For pairs of compensated Poisson increments, the squared product is integrable
because each compensated value has finite second moment and ξ's are bounded. -/
private lemma cross_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i j : Fin φ.N) :
    MeasureTheory.Integrable
      (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                (φ.ξ j ω * N.compensated (φ.fullRect j) ω)) P := by
  have h_B_i_meas : MeasurableSet (φ.fullRect i) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable i)
  have h_B_j_meas : MeasurableSet (φ.fullRect j) := by
    unfold SimplePredictable.fullRect
    exact measurableSet_Ioc.prod (φ.A_measurable j)
  have h_finite_i : LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) ≠ ⊤ := by
    rw [φ.referenceIntensity_fullRect i]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite i)
  have h_finite_j : LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect j) ≠ ⊤ := by
    rw [φ.referenceIntensity_fullRect j]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite j)
  have h_int_i_sq : MeasureTheory.Integrable
      (fun ω => (N.compensated (φ.fullRect i) ω)^2) P :=
    compensated_sq_integrable N h_B_i_meas h_finite_i
  have h_int_j_sq : MeasureTheory.Integrable
      (fun ω => (N.compensated (φ.fullRect j) ω)^2) P :=
    compensated_sq_integrable N h_B_j_meas h_finite_j
  -- |Ñ_i · Ñ_j| ≤ ½(Ñ_i² + Ñ_j²) — Cauchy-Schwarz / AM-GM.
  -- So Ñ_i · Ñ_j is integrable.
  have h_int_NN : MeasureTheory.Integrable
      (fun ω => N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω) P := by
    have h_meas_i : Measurable (fun ω => N.compensated (φ.fullRect i) ω) := by
      change Measurable (fun ω => (N.N ω (φ.fullRect i)).toReal -
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal)
      exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_i_meas)).sub_const _
    have h_meas_j : Measurable (fun ω => N.compensated (φ.fullRect j) ω) := by
      change Measurable (fun ω => (N.N ω (φ.fullRect j)).toReal -
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect j)).toReal)
      exact (ENNReal.measurable_toReal.comp (N.measurable_eval h_B_j_meas)).sub_const _
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1/2 : ℝ))
        (h_int_j_sq.const_mul (1/2 : ℝ))) (h_meas_i.mul h_meas_j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]
    have h_amgm : |N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω|
              ≤ (1/2) * (N.compensated (φ.fullRect i) ω)^2 +
                (1/2) * (N.compensated (φ.fullRect j) ω)^2 := by
      rw [abs_mul]
      have := sq_nonneg (|N.compensated (φ.fullRect i) ω| - |N.compensated (φ.fullRect j) ω|)
      nlinarith [sq_abs (N.compensated (φ.fullRect i) ω),
                 sq_abs (N.compensated (φ.fullRect j) ω)]
    exact h_amgm
  -- (ξ_i · Ñ_i)(ξ_j · Ñ_j) = (ξ_i · ξ_j) · (Ñ_i · Ñ_j). Bounded × integrable.
  obtain ⟨M_i, hM_i⟩ := φ.ξ_bounded i
  obtain ⟨M_j, hM_j⟩ := φ.ξ_bounded j
  have h_eq : ∀ ω, (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                   (φ.ξ j ω * N.compensated (φ.fullRect j) ω)
            = (φ.ξ i ω * φ.ξ j ω) *
              (N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω) :=
    fun ω => by ring
  rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                     (φ.ξ j ω * N.compensated (φ.fullRect j) ω))
        = fun ω => (φ.ξ i ω * φ.ξ j ω) *
                   (N.compensated (φ.fullRect i) ω * N.compensated (φ.fullRect j) ω) from
    funext h_eq]
  refine MeasureTheory.Integrable.bdd_mul (c := |M_i| * |M_j|) h_int_NN
    ((φ.ξ_measurable i).mul (φ.ξ_measurable j)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hM_i ω) (le_abs_self _))
    (le_trans (hM_j ω) (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

/-- `timeRect i T = fullRect i` (under the partition's `partition_le_T` constraint). -/
lemma SimplePredictable.timeRect_eq_fullRect
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : SimplePredictable Ω E ν T) (i : Fin φ.N) :
    φ.timeRect i T = φ.fullRect i := by
  unfold SimplePredictable.timeRect SimplePredictable.fullRect
  have h_t_i_succ_le_T : φ.partition i.succ ≤ T :=
    le_trans (φ.partition_strictMono.monotone (Fin.le_last _)) φ.partition_le_T
  have h_t_i_pre_le_T : φ.partition i.castSucc ≤ T :=
    le_of_lt ((φ.partition_strictMono Fin.castSucc_lt_succ).trans_le h_t_i_succ_le_T)
  rw [min_eq_left h_t_i_pre_le_T, min_eq_left h_t_i_succ_le_T]

/-- Bochner diagonal restated in `fullRect` form. -/
private lemma simpleIntegral_diagonal_bochner_fullRect
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (i : Fin φ.N)
    (h_part_nn : 0 ≤ φ.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
        ∫ ω, (φ.ξ i ω)^2 ∂P := by
  rw [← φ.timeRect_eq_fullRect i]
  exact simpleIntegral_diagonal_bochner N φ i h_part_nn h_adapt

/-- OffDiagonal restated in `fullRect` form. -/
private lemma simpleIntegral_offDiagonal_fullRect
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) {i j : Fin φ.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition j.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ j)) :
    ∫ ω, (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
         (φ.ξ j ω * N.compensated (φ.fullRect j) ω) ∂P = 0 := by
  rw [← φ.timeRect_eq_fullRect i, ← φ.timeRect_eq_fullRect j]
  exact simpleIntegral_offDiagonal N φ hij h_adapt_i h_adapt_j

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Bochner LHS reduction.** Expand `(∑ a_i)² = ∑_{i,j} a_i a_j` via `Finset.sum_mul_sum`,
apply linearity, then split into diagonal (i = j) and off-diagonal (i ≠ j) terms. -/
private lemma simpleIntegral_sq_bochner_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫ ω, (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 ∂P
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
        ∫ ω, (φ.ξ i ω)^2 ∂P := by
  -- Expand (∑ a_i)² = ∑_{i,j} a_i a_j via Finset.sum_mul_sum.
  have h_expand : ∀ ω,
      (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2
      = ∑ i : Fin φ.N, ∑ j : Fin φ.N,
          (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
          (φ.ξ j ω * N.compensated (φ.fullRect j) ω) := by
    intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
  rw [show (fun ω => (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2)
        = fun ω => ∑ i : Fin φ.N, ∑ j : Fin φ.N,
            (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
            (φ.ξ j ω * N.compensated (φ.fullRect j) ω) from funext h_expand]
  -- Pull out outer sum (by linearity of Bochner integral over finite sums)
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun j _ => cross_sq_integrable N φ i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  -- Pull out inner sum
  rw [MeasureTheory.integral_finsetSum _
    (fun j _ => cross_sq_integrable N φ i j)]
  -- Now: ∑ j, ∫ (a_i a_j) ∂P. Split via Finset.sum_eq_single i.
  rw [Finset.sum_eq_single i]
  · -- Term at j = i: ∫ (a_i)² ∂P = ν̂(fullRect i).toReal · ∫ ξ_i²
    have h_part_nn : 0 ≤ φ.partition i.castSucc := by
      have : φ.partition 0 ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone (Fin.zero_le _)
      rw [φ.partition_zero] at this; exact this
    rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                       (φ.ξ i ω * N.compensated (φ.fullRect i) ω))
          = fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 from by
      funext ω; ring]
    exact simpleIntegral_diagonal_bochner_fullRect N φ i h_part_nn (h_adapt i)
  · -- Terms at j ≠ i: vanish via offDiagonal (with symmetry).
    intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · -- j < i: rearrange via mul_comm, apply offDiagonal with j < i.
      rw [show (fun ω => (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                         (φ.ξ j ω * N.compensated (φ.fullRect j) ω))
            = fun ω => (φ.ξ j ω * N.compensated (φ.fullRect j) ω) *
                       (φ.ξ i ω * N.compensated (φ.fullRect i) ω) from by
        funext ω; ring]
      exact simpleIntegral_offDiagonal_fullRect N φ h_lt (h_adapt j) (h_adapt i)
    · -- i < j: direct offDiagonal.
      exact simpleIntegral_offDiagonal_fullRect N φ h_gt (h_adapt i) (h_adapt j)
  · intro h_not; exact absurd (Finset.mem_univ _) h_not

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **LHS reduction for the Itô-Lévy isometry on simples.** The L²-norm-squared
of the simple integral equals the canonical sum form. Combines diagonal +
offDiagonal via Bochner expansion. -/
lemma simpleIntegral_sq_lintegral_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (_hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) *
        ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Step 1: rewrite simpleIntegral as sum over fullRect.
  simp_rw [simpleIntegral_eq_sum_fullRect N φ]
  -- Step 2: convert (‖x‖)² to ENNReal.ofReal(x²).
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm_eq_enorm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [show (∫⁻ ω, (‖∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal
            ((∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)]
  -- Step 3: integrability and nonnegativity for ofReal_integral_eq_lintegral_ofReal.
  have h_int_sum_sq : MeasureTheory.Integrable
      (fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2) P := by
    -- (∑ a)² = ∑∑ a_i a_j; sum of integrables.
    have h_eq : ∀ ω, (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2
                = ∑ i : Fin φ.N, ∑ j : Fin φ.N,
                  (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
                  (φ.ξ j ω * N.compensated (φ.fullRect j) ω) := by
      intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
    rw [show (fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2)
          = fun ω => ∑ i : Fin φ.N, ∑ j : Fin φ.N,
              (φ.ξ i ω * N.compensated (φ.fullRect i) ω) *
              (φ.ξ j ω * N.compensated (φ.fullRect j) ω) from funext h_eq]
    refine MeasureTheory.integrable_finsetSum _ (fun i _ => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact cross_sq_integrable N φ i j
  have h_nn_sum_sq :
      0 ≤ᵐ[P] fun ω => (∑ i, φ.ξ i ω * N.compensated (φ.fullRect i) ω)^2 := by
    filter_upwards with ω; exact sq_nonneg _
  -- Step 4: apply ofReal_integral_eq_lintegral_ofReal
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sum_sq h_nn_sum_sq]
  -- Step 5: apply Bochner LHS reduction.
  rw [simpleIntegral_sq_bochner_eq N φ h_adapt]
  -- Step 6: convert ENNReal.ofReal of finite sum to finite sum of ENNReal terms.
  rw [show
        ENNReal.ofReal (∑ i : Fin φ.N,
          (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
          ∫ ω, (φ.ξ i ω)^2 ∂P)
        = ∑ i : Fin φ.N,
          ENNReal.ofReal
            ((LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
            ∫ ω, (φ.ξ i ω)^2 ∂P) from by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    refine mul_nonneg ENNReal.toReal_nonneg ?_
    exact MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)]
  -- Step 7: each term: ofReal(ν̂.toReal · ∫ ξ²) = ν̂ · ofReal(∫ ξ²) = ν̂ · ∫⁻ ‖ξ‖².
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_finite_i : LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i) ≠ ⊤ := by
    rw [φ.referenceIntensity_fullRect i]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (φ.A_finite i)
  -- Bound ξ_i² by M_i² to get integrability.
  obtain ⟨M, hM⟩ := φ.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (φ.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (φ.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((φ.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (φ.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  -- ofReal(ν̂.toReal · ∫ ξ²) = ofReal(ν̂.toReal) · ofReal(∫ ξ²)
  rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]
  -- ofReal(ν̂.toReal) = ν̂
  rw [ENNReal.ofReal_toReal h_finite_i]
  -- ofReal(∫ ξ²) = ∫⁻ ENNReal.ofReal(ξ²)
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq]
  -- ∫⁻ ENNReal.ofReal(ξ²) = ∫⁻ (‖ξ‖)² (by h_norm_sq_eq backwards)
  rw [show (fun ω => ENNReal.ofReal ((φ.ξ i ω)^2))
        = fun ω => (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => (h_norm_sq_eq _).symm)]

lemma simpleIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [simpleIntegral_sq_lintegral_eq N hT φ h_adapt]
  rw [SimplePredictable.lintegral_eval_sq_outer φ]

/-- **B3 sum form: L² isometry (Bochner) for the compensated-Poisson simple
integral.** For an adapted simple `φ`,
`E[(simpleIntegral N φ T)²] = Σ_i ν̂(fullRect i).toReal · E[ξ_i²]`.

Combines `simpleIntegral_eq_sum_fullRect` (sum decomposition of the
integral at time `T`) with the existing private `simpleIntegral_sq_bochner_eq`. -/
theorem simpleIntegral_L2_isometry_compensatedPoisson_sumForm
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫ ω, (simpleIntegral N φ T ω) ^ 2 ∂P
      = ∑ i : Fin φ.N,
        (LevyStochCalc.Poisson.referenceIntensity ν (φ.fullRect i)).toReal *
        ∫ ω, (φ.ξ i ω) ^ 2 ∂P := by
  have h_eq : ∀ ω, (simpleIntegral N φ T ω) ^ 2
      = (∑ i : Fin φ.N, φ.ξ i ω * N.compensated (φ.fullRect i) ω) ^ 2 := by
    intro ω; rw [simpleIntegral_eq_sum_fullRect]
  simp_rw [h_eq]
  exact simpleIntegral_sq_bochner_eq N φ h_adapt

/-! ## C0b-Compensated mirror chain (in progress)

The `simpleIntegral N φ T` lifted into `Lp ℝ 2 P` framework, mirroring
`Brownian.SimplePredictableRefine.simpleIntegralLp_brownian` etc. -/

/-- **Finite L²-norm of `simpleIntegral N φ T`.** Combines `simpleIntegral_isometry`
(which gives `∫⁻ ‖simpleIntegral‖² = ∑_i ν̂(rect_i) · ∫⁻ ξ_i²`) with the
boundedness of `ξ_i` and finiteness of `ν̂(rect_i) = (t_{i+1} - t_i) · ν(A_i)`. -/
lemma simpleIntegral_lintegral_sq_finite_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [simpleIntegral_isometry N hT φ h_adapt]
  rw [SimplePredictable.lintegral_eval_sq_outer φ]
  -- Goal: ∑ i, ν̂(fullRect i) * ∫⁻ ‖ξ i‖₊² ∂P < ⊤
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  refine ENNReal.mul_lt_top ?_ ?_
  · -- ν̂(fullRect i) < ⊤. fullRect i = (partition i.castSucc, partition i.succ] × A_i.
    -- referenceIntensity = vol.restrict [0, ∞) ⊗ ν.
    -- ν̂(rect) = (length of time interval) · ν(A_i). Both finite.
    unfold LevyStochCalc.Poisson.referenceIntensity SimplePredictable.fullRect
    rw [MeasureTheory.Measure.prod_prod]
    refine ENNReal.mul_lt_top ?_ ?_
    · -- vol.restrict [0,∞) (Ioc s t) ≤ vol (Ioc s t) = ENNReal.ofReal (t - s) < ⊤.
      refine lt_of_le_of_lt
        (MeasureTheory.Measure.restrict_apply_le (Set.Ici (0 : ℝ)) _) ?_
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_lt_top
    · exact lt_of_le_of_ne le_top (φ.A_finite i)
  · -- ∫⁻ ω, ‖ξ i ω‖₊² ∂P < ⊤. ξ_i bounded ⟹ integrand bounded ⟹ finite on probability.
    obtain ⟨M, hM⟩ := φ.ξ_bounded i
    have h_bound : ∀ ω, |φ.ξ i ω| ≤ max M 0 :=
      fun ω => le_trans (hM ω) (le_max_left _ _)
    have h_M_nn : 0 ≤ max M 0 := le_max_right _ _
    have h_norm_le : ∀ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (max M 0) := by
      intro ω
      rw [show (‖φ.ξ i ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖φ.ξ i ω‖
            from (ofReal_norm_eq_enorm _).symm]
      exact ENNReal.ofReal_le_ofReal (Real.norm_eq_abs _ ▸ h_bound ω)
    calc ∫⁻ ω, (‖φ.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ _ω, (ENNReal.ofReal (max M 0)) ^ 2 ∂P := by
          refine MeasureTheory.lintegral_mono (fun ω => ?_)
          exact pow_le_pow_left' (h_norm_le ω) 2
      _ = (ENNReal.ofReal (max M 0)) ^ 2 * P Set.univ := by
          rw [MeasureTheory.lintegral_const]
      _ < ⊤ := by
          rw [MeasureTheory.measure_univ, mul_one]
          exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/-- **`simpleIntegral N φ T` is in `L²(P)`.** Combines AEStronglyMeasurability
(via `Finset.sum` of measurable terms) with `simpleIntegral_lintegral_sq_finite_compensated`
to produce a `MemLp 2 P` witness. Lifts the simple integral into Mathlib's `Lp`
framework, needed for L²-Cauchy completion. -/
lemma simpleIntegral_memLp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (hT : 0 < T) (φ : SimplePredictable Ω E ν T)
    (h_adapt : ∀ i : Fin φ.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic (φ.partition i.castSucc) ×ˢ Set.univ
                                  ∧ MeasurableSet C },
        MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) (φ.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral N φ T ω) 2 P := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable.
    refine Measurable.aestronglyMeasurable ?_
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul (φ.ξ_measurable i) ?_
    -- N.compensated B = (N.N · B).toReal - ν̂(B).toReal. Measurable in ω.
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    refine Measurable.sub ?_ measurable_const
    have h_meas_NB : Measurable (fun ω => N.N ω (φ.timeRect i T)) := by
      apply N.measurable_eval
      -- timeRect i T is measurable (Ioc × A_i with A_i measurable).
      unfold SimplePredictable.timeRect
      exact MeasurableSet.prod measurableSet_Ioc (φ.A_measurable i)
    exact ENNReal.measurable_toReal.comp h_meas_NB
  · -- eLpNorm < ⊤.
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h_two_toReal]
    have h_pre := simpleIntegral_lintegral_sq_finite_compensated N hT φ h_adapt
    have h_rewrite : ∀ ω : Ω,
        (‖simpleIntegral N φ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          = (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [show (fun ω => (‖simpleIntegral N φ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖simpleIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2) from
        funext h_rewrite]
    exact h_pre

/-- **B1: Simple integral against compensated Poisson `Ñ` (renamed alias).**

This is the standard `simpleIntegral` in this namespace, exposed under the
roadmap's explicit name `simpleIntegral_compensatedPoisson`. Mathematical
content:
`∫ g dÑ := ∑_i ξ_i · Ñ((t_i, t_{i+1}] × A_i)`
where `Ñ(B) := N(B) − ν̂(B)` is the compensated random measure
(`PoissonRandomMeasure.compensated`); equivalently
`∫ g dÑ = ∫ g dN − ∫ g(z) ν(dz) dt` for simple `g`. -/
@[reducible] noncomputable def simpleIntegral_compensatedPoisson
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (φ : SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  simpleIntegral N φ t ω

end LevyStochCalc.Poisson.Compensated
