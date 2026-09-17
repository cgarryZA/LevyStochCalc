/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Moments of a Poisson law and Poisson integration by parts

The law `poissonMeasure r` on `ℕ` gives the atom `n` the mass `exp (-r) * r ^ n / n !`, so it is
the Poisson law of mean `r`. Every polynomial function is integrable for it, and the Stein
identity `E[N p(N)] = r E[p(N + 1)]` holds for every real polynomial `p`, with the forward shift
in place of the derivative of the Gaussian identity. Mean and variance are both `r`.

## Main statements

* `LevyStochCalc.Probability.integrable_eval_poissonMeasure` — `p(N)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_poissonMeasure` — `E[N p(N)] = r E[p(N + 1)]`.
* `LevyStochCalc.Probability.integral_id_poissonMeasure` — `E[N] = r`.
* `LevyStochCalc.Probability.integral_id_sq_poissonMeasure` — `E[N ^ 2] = r ^ 2 + r`.
* `LevyStochCalc.Probability.integral_sub_sq_poissonMeasure` — `E[(N - r) ^ 2] = r`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat

/-- Every power is integrable for a Poisson law. -/
theorem integrable_pow_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    Integrable (fun n : ℕ => (n : ℝ) ^ k) (poissonMeasure r) := by
  rw [integrable_poissonMeasure_iff]
  have hbd : ∀ n : ℕ, Real.exp (-r) * (r : ℝ) ^ n / n ! * ‖(n : ℝ) ^ k‖
      ≤ Real.exp (-r) * (k ! : ℝ) * (((r : ℝ) * Real.exp 1) ^ n / n !) := by
    intro n
    have h1 : (n : ℝ) ^ k / k ! ≤ Real.exp n :=
      Real.pow_div_factorial_le_exp (x := (n : ℝ)) (by positivity) k
    have hk : (0 : ℝ) < k ! := by positivity
    have h2 : (n : ℝ) ^ k ≤ (k ! : ℝ) * Real.exp n := by
      rw [div_le_iff₀ hk] at h1; linarith [h1]
    have h3 : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      rw [← Real.exp_nat_mul]; ring_nf
    have hnorm : ‖(n : ℝ) ^ k‖ = (n : ℝ) ^ k := by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hfac : (0 : ℝ) < n ! := by positivity
    rw [hnorm]
    rw [h3] at h2
    have hrn : (0 : ℝ) ≤ Real.exp (-r) * (r : ℝ) ^ n / n ! := by positivity
    have key : Real.exp (-r) * (r : ℝ) ^ n / n ! * (n : ℝ) ^ k
        ≤ Real.exp (-r) * (r : ℝ) ^ n / n ! * ((k ! : ℝ) * Real.exp 1 ^ n) :=
      mul_le_mul_of_nonneg_left h2 hrn
    refine key.trans_eq ?_
    field_simp
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) hbd ?_
  exact ((Real.summable_pow_div_factorial ((r : ℝ) * Real.exp 1)).mul_left _)

/-- The identity is integrable for a Poisson law. -/
theorem integrable_id_poissonMeasure (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  simpa using integrable_pow_poissonMeasure r 1

/-- Every polynomial function is integrable for a Poisson law. -/
theorem integrable_eval_poissonMeasure (r : ℝ≥0) (p : ℝ[X]) :
    Integrable (fun n : ℕ => p.eval (n : ℝ)) (poissonMeasure r) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact hp.add hq
  | monomial n a =>
    simpa [eval_monomial] using (integrable_pow_poissonMeasure r n).const_mul a

/-- Every polynomial function of the forward shift is integrable for a Poisson law. -/
theorem integrable_eval_add_one_poissonMeasure (r : ℝ≥0) (p : ℝ[X]) :
    Integrable (fun n : ℕ => p.eval ((n : ℝ) + 1)) (poissonMeasure r) := by
  have h := integrable_eval_poissonMeasure r (p.comp (X + C 1))
  simpa [eval_comp] using h

/-- Poisson integration by parts on polynomials: `E[N p(N)] = r E[p(N + 1)]` under
`poissonMeasure r`. -/
theorem integral_mul_eval_poissonMeasure (r : ℝ≥0) (p : ℝ[X]) :
    ∫ n : ℕ, (n : ℝ) * p.eval (n : ℝ) ∂poissonMeasure r
      = (r : ℝ) * ∫ n : ℕ, p.eval ((n : ℝ) + 1) ∂poissonMeasure r := by
  have hsum : Summable
      (fun n : ℕ => (Real.exp (-r) * (r : ℝ) ^ n / n !) • ((n : ℝ) * p.eval (n : ℝ))) := by
    have h := integrable_eval_poissonMeasure r (X * p)
    simp only [eval_mul, eval_X] at h
    have := integrable_poissonMeasure_iff.1 h
    refine Summable.of_norm ?_
    refine this.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    rw [smul_eq_mul, norm_mul, Real.norm_eq_abs (Real.exp (-r) * (r : ℝ) ^ n / n !),
      abs_of_nonneg (by positivity)]
  rw [integral_poissonMeasure, integral_poissonMeasure, hsum.tsum_eq_zero_add]
  simp only [Nat.cast_zero, zero_mul, smul_eq_mul, mul_zero, zero_add]
  rw [← tsum_mul_left]
  refine tsum_congr fun m => ?_
  have hfac : ((m + 1)! : ℝ) = ((m : ℝ) + 1) * m ! := by
    rw [Nat.factorial_succ]; push_cast; ring
  push_cast [hfac]
  have h0 : ((m : ℝ) + 1) ≠ 0 := by positivity
  have h1 : ((m ! : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The mean of a Poisson law: `E[N] = r`. -/
theorem integral_id_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ∂poissonMeasure r = (r : ℝ) := by
  have h := integral_mul_eval_poissonMeasure r 1
  simpa using h

/-- The second moment of a Poisson law: `E[N ^ 2] = r ^ 2 + r`. -/
theorem integral_id_sq_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 2 ∂poissonMeasure r = (r : ℝ) ^ 2 + r := by
  have h := integral_mul_eval_poissonMeasure r X
  simp only [eval_X] at h
  rw [integral_add (integrable_id_poissonMeasure r) (integrable_const 1),
    integral_id_poissonMeasure] at h
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one] at h
  rw [show (fun n : ℕ => (n : ℝ) ^ 2) = fun n : ℕ => (n : ℝ) * (n : ℝ) from by
    funext n; ring]
  rw [h]
  ring

/-- The variance of a Poisson law: `E[(N - r) ^ 2] = r`. -/
theorem integral_sub_sq_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - r) ^ 2 ∂poissonMeasure r = (r : ℝ) := by
  have h1 := integrable_id_poissonMeasure r
  have h2 := integrable_pow_poissonMeasure r 2
  have hcm : Integrable (fun n : ℕ => 2 * (r : ℝ) * (n : ℝ)) (poissonMeasure r) :=
    h1.const_mul _
  have hsub : Integrable (fun n : ℕ => (n : ℝ) ^ 2 - 2 * (r : ℝ) * (n : ℝ))
      (poissonMeasure r) := h2.sub hcm
  rw [show (fun n : ℕ => ((n : ℝ) - r) ^ 2)
      = fun n : ℕ => ((n : ℝ) ^ 2 - 2 * (r : ℝ) * (n : ℝ)) + (r : ℝ) ^ 2 from by
    funext n; ring]
  rw [integral_add hsub (integrable_const _), integral_sub h2 hcm, integral_const_mul,
    integral_id_sq_poissonMeasure, integral_id_poissonMeasure]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

end LevyStochCalc.Probability
