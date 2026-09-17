/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import BrownianMotion.Gaussian.Moment
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Moments of a centred real Gaussian and Gaussian integration by parts

For the law `gaussianReal 0 v` on `ℝ` the even moments are `E[X^(2n)] = v^n (2n-1)!!`, the odd
moments vanish, and the two are tied together by the recursion `E[X^(k+2)] = (k+1) v E[X^k]`.
Every polynomial function is integrable for this law, and the Stein identity
`E[X p(X)] = v E[p'(X)]` holds for every real polynomial `p`.

## Main statements

* `LevyStochCalc.Probability.integral_pow_even_gaussianReal` — `E[X^(2n)] = v^n (2n-1)!!`.
* `LevyStochCalc.Probability.integral_pow_odd_gaussianReal` — `E[X^(2n+1)] = 0`.
* `LevyStochCalc.Probability.integral_pow_add_two_gaussianReal` — `E[X^(k+2)] = (k+1) v E[X^k]`.
* `LevyStochCalc.Probability.integrable_eval_gaussianReal` — `p(X)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_gaussianReal` — `E[X p(X)] = v E[p'(X)]`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal

variable (v : ℝ≥0)

/-- The even moments of a centred real Gaussian law. -/
theorem integral_pow_even_gaussianReal (n : ℕ) :
    ∫ x, x ^ (2 * n) ∂gaussianReal 0 v = (v : ℝ) ^ n * (2 * n - 1).doubleFactorial := by
  have hv : (NNReal.sqrt v) ^ 2 = v := NNReal.sq_sqrt v
  have h := centralMoment_two_mul_gaussianReal 0 (NNReal.sqrt v) n
  rw [hv] at h
  simp only [centralMoment, Pi.sub_apply, Pi.pow_apply, id_eq, integral_id_gaussianReal,
    sub_zero] at h
  rw [h, pow_mul, ← NNReal.coe_pow, hv]

/-- The odd moments of a centred real Gaussian law vanish. -/
theorem integral_pow_odd_gaussianReal (n : ℕ) :
    ∫ x, x ^ (2 * n + 1) ∂gaussianReal 0 v = 0 := by
  have h : ∫ x, x ^ (2 * n + 1) ∂((gaussianReal 0 v).map fun x => -x)
      = ∫ x, (-x) ^ (2 * n + 1) ∂gaussianReal 0 v :=
    integral_map measurable_neg.aemeasurable
      (measurable_id.pow_const (2 * n + 1)).aestronglyMeasurable
  rw [gaussianReal_map_neg, neg_zero] at h
  have h2 : ∫ x, (-x) ^ (2 * n + 1) ∂gaussianReal 0 v
      = -∫ x, x ^ (2 * n + 1) ∂gaussianReal 0 v := by
    rw [← integral_neg]
    congr 1
    funext x
    rw [Odd.neg_pow ⟨n, by ring⟩]
  linarith

/-- The moment recursion `E[X^(k+2)] = (k+1) v E[X^k]` of a centred real Gaussian law. -/
theorem integral_pow_add_two_gaussianReal (k : ℕ) :
    ∫ x, x ^ (k + 2) ∂gaussianReal 0 v
      = ((k : ℝ) + 1) * v * ∫ x, x ^ k ∂gaussianReal 0 v := by
  rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
  · subst hj
    have e1 : j + j + 2 = 2 * (j + 1) := by ring
    have e2 : j + j = 2 * j := by ring
    rw [e1, e2, integral_pow_even_gaussianReal, integral_pow_even_gaussianReal]
    have hd : (2 * (j + 1) - 1).doubleFactorial
        = (2 * j + 1) * (2 * j - 1).doubleFactorial := by
      rcases j with _ | j
      · simp
      · have hl : 2 * (j + 1 + 1) - 1 = (2 * (j + 1) - 1) + 2 := by omega
        have hr : 2 * (j + 1) + 1 = (2 * (j + 1) - 1) + 2 := by omega
        rw [hl, hr, Nat.doubleFactorial_add_two]
    rw [hd]
    push_cast
    ring
  · subst hj
    have e1 : 2 * j + 1 + 2 = 2 * (j + 1) + 1 := by ring
    rw [e1, integral_pow_odd_gaussianReal, integral_pow_odd_gaussianReal]
    ring

/-- Every power of the identity is integrable for a centred real Gaussian law. -/
theorem integrable_pow_gaussianReal_zero (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (gaussianReal 0 v) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [pow_zero]
    exact integrable_const 1
  have hf : MemLp id ((n : ℕ) : ℝ≥0∞) (gaussianReal 0 v) :=
    memLp_id_gaussianReal' ((n : ℕ) : ℝ≥0∞) (by simp)
  refine (hf.integrable_norm_pow hn.ne').mono'
    ((measurable_id.pow_const n).aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun x => (norm_pow _ _).le

/-- Every polynomial function is integrable for a centred real Gaussian law. -/
theorem integrable_eval_gaussianReal (p : ℝ[X]) :
    Integrable (fun x : ℝ => p.eval x) (gaussianReal 0 v) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add]
    exact hp.add hq
  | monomial n a =>
    simpa [eval_monomial] using (integrable_pow_gaussianReal_zero v n).const_mul a

/-- Gaussian integration by parts on polynomials: `E[X p(X)] = v E[p'(X)]` under
`gaussianReal 0 v`. -/
theorem integral_mul_eval_gaussianReal (p : ℝ[X]) :
    ∫ x, x * p.eval x ∂gaussianReal 0 v
      = (v : ℝ) * ∫ x, (derivative p).eval x ∂gaussianReal 0 v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have h1 : Integrable (fun x : ℝ => x * p.eval x) (gaussianReal 0 v) := by
      have h := integrable_eval_gaussianReal v (X * p)
      simpa only [eval_mul, eval_X] using h
    have h2 : Integrable (fun x : ℝ => x * q.eval x) (gaussianReal 0 v) := by
      have h := integrable_eval_gaussianReal v (X * q)
      simpa only [eval_mul, eval_X] using h
    have h3 : Integrable (fun x : ℝ => (derivative p).eval x) (gaussianReal 0 v) :=
      integrable_eval_gaussianReal v _
    have h4 : Integrable (fun x : ℝ => (derivative q).eval x) (gaussianReal 0 v) :=
      integrable_eval_gaussianReal v _
    simp only [eval_add, derivative_add, mul_add]
    rw [integral_add h1 h2, integral_add h3 h4, hp, hq]
    ring
  | monomial n a =>
    rcases n with _ | k
    · simp only [monomial_zero_left, eval_C, derivative_C, eval_zero, integral_zero, mul_zero]
      simp_rw [mul_comm _ a]
      rw [integral_const_mul, integral_id_gaussianReal, mul_zero]
    · have hev : ∀ x : ℝ, x * (monomial (k + 1) a).eval x = a * x ^ (k + 2) := by
        intro x; rw [eval_monomial]; ring
      have hdv : derivative (monomial (k + 1) a) = monomial k (((k : ℝ) + 1) * a) := by
        rw [derivative_monomial]
        congr 1
        push_cast
        ring
      simp_rw [hev, hdv, eval_monomial]
      rw [integral_const_mul, integral_const_mul, integral_pow_add_two_gaussianReal]
      ring

end LevyStochCalc.Probability
