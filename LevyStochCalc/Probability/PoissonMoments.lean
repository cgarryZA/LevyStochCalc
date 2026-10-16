/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer

/-!
# Moments of a Poisson law and Poisson integration by parts

The law `poissonMeasure r` on `ℕ` gives the atom `n` the mass `exp (-r) * r ^ n / n !`, so it is
the Poisson law of mean `r`. Every polynomial function is integrable for it, and the Stein
identity `E[N p(N)] = r E[p(N + 1)]` holds for every real polynomial `p`, with the forward shift
in place of the derivative of the Gaussian identity. Mean and variance are both `r`, the
factorial moments are `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`, the third central moment is `r` and
the fourth central moment is `3 r ^ 2 + r`. The identity has moments of every finite order.

## Main statements

* `LevyStochCalc.Probability.integrable_eval_poissonMeasure` — `p(N)` is integrable.
* `LevyStochCalc.Probability.integral_mul_eval_poissonMeasure` — `E[N p(N)] = r E[p(N + 1)]`.
* `LevyStochCalc.Probability.integral_id_poissonMeasure` — `E[N] = r`.
* `LevyStochCalc.Probability.integral_id_sq_poissonMeasure` — `E[N ^ 2] = r ^ 2 + r`.
* `LevyStochCalc.Probability.integral_sub_sq_poissonMeasure` — `E[(N - r) ^ 2] = r`.
* `LevyStochCalc.Probability.integral_descPochhammer_eval_poissonMeasure` — the factorial
  moments `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`.
* `LevyStochCalc.Probability.integral_sub_pow_three_poissonMeasure` — `E[(N - r) ^ 3] = r`.
* `LevyStochCalc.Probability.integral_sub_pow_four_poissonMeasure` —
  `E[(N - r) ^ 4] = 3 r ^ 2 + r`.
* `LevyStochCalc.Probability.memLp_natCast_poissonMeasure` — `N ∈ Lᵖ` for every finite `p`.
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

/-- The factorial moments of a Poisson law: `E[N (N - 1) ⋯ (N - k + 1)] = r ^ k`. -/
theorem integral_descPochhammer_eval_poissonMeasure (r : ℝ≥0) (k : ℕ) :
    ∫ n : ℕ, (descPochhammer ℝ k).eval (n : ℝ) ∂poissonMeasure r = (r : ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h := integral_mul_eval_poissonMeasure r ((descPochhammer ℝ k).comp (X - 1))
    simp only [eval_comp, eval_sub, eval_X, eval_one, add_sub_cancel_right] at h
    simp only [descPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_sub, eval_one]
    rw [h, ih, pow_succ]
    ring

/-- The third moment of a Poisson law: `E[N ^ 3] = r ^ 3 + 3 r ^ 2 + r`. -/
theorem integral_id_pow_three_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 3 ∂poissonMeasure r = (r : ℝ) ^ 3 + 3 * (r : ℝ) ^ 2 + r := by
  have h := integral_mul_eval_poissonMeasure r (X ^ 2)
  simp only [eval_pow, eval_X] at h
  have h1 : Integrable (fun n : ℕ => 2 * (n : ℝ)) (poissonMeasure r) :=
    (integrable_id_poissonMeasure r).const_mul 2
  have h2 := integrable_pow_poissonMeasure r 2
  have h21 : Integrable (fun n : ℕ => (n : ℝ) ^ 2 + 2 * (n : ℝ)) (poissonMeasure r) := h2.add h1
  rw [show (fun n : ℕ => (n : ℝ) ^ 3) = fun n : ℕ => (n : ℝ) * (n : ℝ) ^ 2 from by
      funext n; ring, h,
    show (fun n : ℕ => ((n : ℝ) + 1) ^ 2) = fun n : ℕ => (n : ℝ) ^ 2 + 2 * (n : ℝ) + 1 from by
      funext n; ring,
    integral_add h21 (integrable_const 1), integral_add h2 h1, integral_const_mul,
    integral_id_sq_poissonMeasure, integral_id_poissonMeasure]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

/-- The fourth moment of a Poisson law: `E[N ^ 4] = r ^ 4 + 6 r ^ 3 + 7 r ^ 2 + r`. -/
theorem integral_id_pow_four_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, (n : ℝ) ^ 4 ∂poissonMeasure r
      = (r : ℝ) ^ 4 + 6 * (r : ℝ) ^ 3 + 7 * (r : ℝ) ^ 2 + r := by
  have h := integral_mul_eval_poissonMeasure r (X ^ 3)
  simp only [eval_pow, eval_X] at h
  have h1 : Integrable (fun n : ℕ => 3 * (n : ℝ)) (poissonMeasure r) :=
    (integrable_id_poissonMeasure r).const_mul 3
  have h2 : Integrable (fun n : ℕ => 3 * (n : ℝ) ^ 2) (poissonMeasure r) :=
    (integrable_pow_poissonMeasure r 2).const_mul 3
  have h3 := integrable_pow_poissonMeasure r 3
  have h32 : Integrable (fun n : ℕ => (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2) (poissonMeasure r) :=
    h3.add h2
  have h321 : Integrable (fun n : ℕ => (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2 + 3 * (n : ℝ))
      (poissonMeasure r) := h32.add h1
  rw [show (fun n : ℕ => (n : ℝ) ^ 4) = fun n : ℕ => (n : ℝ) * (n : ℝ) ^ 3 from by
      funext n; ring, h,
    show (fun n : ℕ => ((n : ℝ) + 1) ^ 3)
        = fun n : ℕ => (n : ℝ) ^ 3 + 3 * (n : ℝ) ^ 2 + 3 * (n : ℝ) + 1 from by
      funext n; ring,
    integral_add h321 (integrable_const 1), integral_add h32 h1, integral_add h3 h2,
    integral_const_mul, integral_const_mul, integral_id_pow_three_poissonMeasure,
    integral_id_sq_poissonMeasure, integral_id_poissonMeasure]
  simp only [integral_const, probReal_univ, smul_eq_mul, mul_one]
  ring

/-- The third central moment of a Poisson law: `E[(N - r) ^ 3] = r`. -/
theorem integral_sub_pow_three_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - r) ^ 3 ∂poissonMeasure r = (r : ℝ) := by
  have h1 : Integrable (fun n : ℕ => 3 * (r : ℝ) ^ 2 * (n : ℝ)) (poissonMeasure r) :=
    (integrable_id_poissonMeasure r).const_mul _
  have h2 : Integrable (fun n : ℕ => 3 * (r : ℝ) * (n : ℝ) ^ 2) (poissonMeasure r) :=
    (integrable_pow_poissonMeasure r 2).const_mul _
  have h3 := integrable_pow_poissonMeasure r 3
  have hA : Integrable (fun n : ℕ => (n : ℝ) ^ 3 - 3 * (r : ℝ) * (n : ℝ) ^ 2)
      (poissonMeasure r) := h3.sub h2
  have hB : Integrable (fun n : ℕ => (n : ℝ) ^ 3 - 3 * (r : ℝ) * (n : ℝ) ^ 2
      + 3 * (r : ℝ) ^ 2 * (n : ℝ)) (poissonMeasure r) := hA.add h1
  rw [show (fun n : ℕ => ((n : ℝ) - r) ^ 3)
      = fun n : ℕ => (n : ℝ) ^ 3 - 3 * (r : ℝ) * (n : ℝ) ^ 2 + 3 * (r : ℝ) ^ 2 * (n : ℝ)
        - (r : ℝ) ^ 3 from by funext n; ring,
    integral_sub hB (integrable_const _), integral_add hA h1, integral_sub h3 h2,
    integral_const_mul, integral_const_mul, integral_id_pow_three_poissonMeasure,
    integral_id_sq_poissonMeasure, integral_id_poissonMeasure]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- The fourth central moment of a Poisson law: `E[(N - r) ^ 4] = 3 r ^ 2 + r`. -/
theorem integral_sub_pow_four_poissonMeasure (r : ℝ≥0) :
    ∫ n : ℕ, ((n : ℝ) - r) ^ 4 ∂poissonMeasure r = 3 * (r : ℝ) ^ 2 + r := by
  have h1 : Integrable (fun n : ℕ => 4 * (r : ℝ) ^ 3 * (n : ℝ)) (poissonMeasure r) :=
    (integrable_id_poissonMeasure r).const_mul _
  have h2 : Integrable (fun n : ℕ => 6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2) (poissonMeasure r) :=
    (integrable_pow_poissonMeasure r 2).const_mul _
  have h3 : Integrable (fun n : ℕ => 4 * (r : ℝ) * (n : ℝ) ^ 3) (poissonMeasure r) :=
    (integrable_pow_poissonMeasure r 3).const_mul _
  have h4 := integrable_pow_poissonMeasure r 4
  have hA : Integrable (fun n : ℕ => (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3)
      (poissonMeasure r) := h4.sub h3
  have hB : Integrable (fun n : ℕ => (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3
      + 6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2) (poissonMeasure r) := hA.add h2
  have hC : Integrable (fun n : ℕ => (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3
      + 6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2 - 4 * (r : ℝ) ^ 3 * (n : ℝ)) (poissonMeasure r) :=
    hB.sub h1
  rw [show (fun n : ℕ => ((n : ℝ) - r) ^ 4)
      = fun n : ℕ => (n : ℝ) ^ 4 - 4 * (r : ℝ) * (n : ℝ) ^ 3 + 6 * (r : ℝ) ^ 2 * (n : ℝ) ^ 2
        - 4 * (r : ℝ) ^ 3 * (n : ℝ) + (r : ℝ) ^ 4 from by funext n; ring,
    integral_add hC (integrable_const _), integral_sub hB h1, integral_add hA h2,
    integral_sub h4 h3, integral_const_mul, integral_const_mul, integral_const_mul,
    integral_id_pow_four_poissonMeasure, integral_id_pow_three_poissonMeasure,
    integral_id_sq_poissonMeasure, integral_id_poissonMeasure]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

/-- A Poisson count has moments of every finite order. -/
theorem memLp_natCast_poissonMeasure (r : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ∞) :
    MemLp (fun n : ℕ => (n : ℝ)) p (poissonMeasure r) := by
  obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt hp
  have hk0 : (k : ℝ≥0∞) ≠ 0 := (pos_of_gt hk).ne'
  refine MemLp.mono_exponent ?_ hk.le
  refine (integrable_norm_rpow_iff measurable_from_nat.aestronglyMeasurable hk0
    (ENNReal.natCast_ne_top k)).mp ?_
  refine (integrable_pow_poissonMeasure r k).congr (Filter.Eventually.of_forall fun n => ?_)
  simp only [ENNReal.toReal_natCast, Real.norm_eq_abs, Nat.abs_cast]
  exact (Real.rpow_natCast _ k).symm

end LevyStochCalc.Probability
