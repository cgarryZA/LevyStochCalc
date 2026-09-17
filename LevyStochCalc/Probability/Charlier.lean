/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.PoissonMoments
import Mathlib.Topology.Algebra.Polynomial

/-!
# Charlier polynomials of rate `lam` and their Poisson orthogonality

The Charlier polynomials of rate `lam` are given by the Appell-type recursion
`C_(s+1)(x) = x C_s(x - 1) - lam C_s(x)` from `C_0 = 1`, the backward-difference analogue of the
Hermite recursion `H_(n+1) = (x - v d/dx) H_n`. The forward difference plays the role the
derivative plays there, `C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`, and the degree-two member
is `C_2(x; lam) = (x - lam) ^ 2 - x`. Under the Poisson law of mean `r` the family of rate `r` is
orthogonal, with `E[C_s C_t] = δ_(s t) s! r ^ s`.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_succ` — the recursion at the level of values.
* `LevyStochCalc.Probability.charlierScaled_two` — `C_2(x; lam) = (x - lam) ^ 2 - x`.
* `LevyStochCalc.Probability.charlierScaled_forward_diff` —
  `C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`.
* `LevyStochCalc.Probability.integral_charlierPoly_mul` — `E[C_s C_t] = δ_(s t) s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_sq` — `E[C_s ^ 2] = s! r ^ s`.
* `LevyStochCalc.Probability.integral_charlierPoly_eq_zero` — `E[C_s] = 0` for `s ≠ 0`.
-/

namespace LevyStochCalc.Probability

open MeasureTheory ProbabilityTheory Polynomial
open scoped NNReal ENNReal Nat

/-- The Charlier polynomial of rate `lam` and degree `s`, given by the recursion
`C_(s+1)(x) = x C_s(x - 1) - lam C_s(x)`. -/
noncomputable def charlierPoly (lam : ℝ) : ℕ → ℝ[X]
  | 0 => 1
  | (s + 1) => X * (charlierPoly lam s).comp (X - C 1) - C lam * charlierPoly lam s

@[simp] theorem charlierPoly_zero (lam : ℝ) : charlierPoly lam 0 = 1 := rfl

theorem charlierPoly_succ (lam : ℝ) (s : ℕ) :
    charlierPoly lam (s + 1)
      = X * (charlierPoly lam s).comp (X - C 1) - C lam * charlierPoly lam s := rfl

/-- The value `C_s(x; lam)` of the Charlier polynomial of rate `lam` and degree `s`. -/
noncomputable def charlierScaled (s : ℕ) (lam x : ℝ) : ℝ := (charlierPoly lam s).eval x

@[simp] theorem charlierScaled_zero (lam x : ℝ) : charlierScaled 0 lam x = 1 := by
  simp [charlierScaled]

theorem charlierScaled_succ (s : ℕ) (lam x : ℝ) :
    charlierScaled (s + 1) lam x
      = x * charlierScaled s lam (x - 1) - lam * charlierScaled s lam x := by
  simp [charlierScaled, charlierPoly_succ, eval_comp]

@[simp] theorem charlierScaled_one (lam x : ℝ) : charlierScaled 1 lam x = x - lam := by
  rw [charlierScaled_succ]; simp

/-- The Charlier polynomial of degree two, `C_2(x; lam) = (x - lam) ^ 2 - x`. -/
theorem charlierScaled_two (lam x : ℝ) : charlierScaled 2 lam x = (x - lam) ^ 2 - x := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, charlierScaled_succ]
  simp only [charlierScaled_one]
  ring

/-- The Charlier polynomials are continuous in their argument. -/
theorem continuous_charlierScaled (s : ℕ) (lam : ℝ) : Continuous (charlierScaled s lam) :=
  (charlierPoly lam s).continuous

/-- The forward difference of the Charlier polynomials,
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)`. -/
theorem charlierScaled_forward_diff (s : ℕ) (lam x : ℝ) :
    charlierScaled (s + 1) lam (x + 1) - charlierScaled (s + 1) lam x
      = ((s : ℝ) + 1) * charlierScaled s lam x := by
  induction s generalizing x with
  | zero => simp
  | succ s ih =>
    have e1 : (x + 1) - 1 = x := by ring
    rw [charlierScaled_succ (s + 1) lam (x + 1), charlierScaled_succ (s + 1) lam x, e1]
    have ih1 := ih x
    have ih2 := ih (x - 1)
    have e2 : x - 1 + 1 = x := by ring
    rw [e2] at ih2
    have e3 : charlierScaled (s + 1) lam x
        = x * charlierScaled s lam (x - 1) - lam * charlierScaled s lam x :=
      charlierScaled_succ s lam x
    push_cast
    linear_combination (-lam) * ih1 + x * ih2 - ((s : ℝ) + 1) * e3

/-- One step of the Charlier recursion under a Poisson law: the backward difference against the
rate moves to the forward difference of the second factor. -/
theorem integral_charlier_step (r : ℝ≥0) (p q : ℝ[X]) :
    ∫ n : ℕ, ((n : ℝ) * p.eval ((n : ℝ) - 1) - (r : ℝ) * p.eval (n : ℝ)) * q.eval (n : ℝ)
        ∂poissonMeasure r
      = (r : ℝ) * ∫ n : ℕ, p.eval (n : ℝ) * (q.eval ((n : ℝ) + 1) - q.eval (n : ℝ))
        ∂poissonMeasure r := by
  have hA : Integrable (fun n : ℕ => (n : ℝ) * (p.comp (X - C 1) * q).eval (n : ℝ))
      (poissonMeasure r) := by
    have h := integrable_eval_poissonMeasure r (X * (p.comp (X - C 1) * q))
    simpa only [eval_mul, eval_X] using h
  have hB : Integrable (fun n : ℕ => (r : ℝ) * (p * q).eval (n : ℝ)) (poissonMeasure r) :=
    (integrable_eval_poissonMeasure r (p * q)).const_mul _
  have hC : Integrable (fun n : ℕ => p.eval (n : ℝ) * q.eval ((n : ℝ) + 1))
      (poissonMeasure r) := by
    have h := integrable_eval_poissonMeasure r (p * q.comp (X + C 1))
    simpa only [eval_mul, eval_comp, eval_add, eval_X, eval_C] using h
  have hD : Integrable (fun n : ℕ => p.eval (n : ℝ) * q.eval (n : ℝ)) (poissonMeasure r) := by
    have h := integrable_eval_poissonMeasure r (p * q)
    simpa only [eval_mul] using h
  have e : ∀ n : ℕ, ((n : ℝ) * p.eval ((n : ℝ) - 1) - (r : ℝ) * p.eval (n : ℝ)) * q.eval (n : ℝ)
      = (n : ℝ) * (p.comp (X - C 1) * q).eval (n : ℝ) - (r : ℝ) * (p * q).eval (n : ℝ) := by
    intro n; simp only [eval_mul, eval_comp, eval_sub, eval_X, eval_C]; ring
  simp_rw [e]
  rw [integral_sub hA hB, integral_mul_eval_poissonMeasure r (p.comp (X - C 1) * q),
    integral_const_mul]
  have e2 : ∀ n : ℕ, (p.comp (X - C 1) * q).eval ((n : ℝ) + 1)
      = p.eval (n : ℝ) * q.eval ((n : ℝ) + 1) := by
    intro n; simp only [eval_mul, eval_comp, eval_sub, eval_X, eval_C]; ring_nf
  simp_rw [e2]
  have e3 : ∀ n : ℕ, p.eval (n : ℝ) * (q.eval ((n : ℝ) + 1) - q.eval (n : ℝ))
      = p.eval (n : ℝ) * q.eval ((n : ℝ) + 1) - p.eval (n : ℝ) * q.eval (n : ℝ) := by
    intro n; ring
  simp_rw [e3]
  rw [integral_sub hC hD]
  have e4 : ∀ n : ℕ, (p * q).eval (n : ℝ) = p.eval (n : ℝ) * q.eval (n : ℝ) := by
    intro n; simp only [eval_mul]
  simp_rw [e4]
  ring

/-- The Charlier polynomials of rate `r` are orthogonal under the Poisson law of mean `r`, with
`E[C_s C_t] = δ_(s t) s! r ^ s`. -/
theorem integral_charlierPoly_mul (r : ℝ≥0) (s t : ℕ) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) * (charlierPoly (r : ℝ) t).eval (n : ℝ)
        ∂poissonMeasure r
      = if s = t then (s.factorial : ℝ) * (r : ℝ) ^ s else 0 := by
  induction s generalizing t with
  | zero =>
    simp only [charlierPoly_zero, eval_one, one_mul, Nat.factorial_zero, Nat.cast_one, pow_zero,
      mul_one]
    induction t with
    | zero => simp
    | succ t _ =>
      have h := integral_charlier_step r (charlierPoly (r : ℝ) t) 1
      simp only [eval_one, mul_one, sub_self, mul_zero, integral_zero, mul_zero] at h
      simp only [charlierPoly_succ, eval_sub, eval_mul, eval_X, eval_C, eval_comp]
      simpa using h
  | succ s ih =>
    have hstep := integral_charlier_step r (charlierPoly (r : ℝ) s) (charlierPoly (r : ℝ) t)
    simp only [charlierPoly_succ, eval_sub, eval_mul, eval_X, eval_C, eval_comp]
    rw [hstep]
    cases t with
    | zero => simp
    | succ u =>
      have hfd : ∀ n : ℕ, (charlierPoly (r : ℝ) (u + 1)).eval ((n : ℝ) + 1)
          - (charlierPoly (r : ℝ) (u + 1)).eval (n : ℝ)
          = ((u : ℝ) + 1) * (charlierPoly (r : ℝ) u).eval (n : ℝ) := by
        intro n
        simpa [charlierScaled] using charlierScaled_forward_diff u (r : ℝ) (n : ℝ)
      simp_rw [hfd]
      have e : ∀ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ)
          * (((u : ℝ) + 1) * (charlierPoly (r : ℝ) u).eval (n : ℝ))
          = ((u : ℝ) + 1) * ((charlierPoly (r : ℝ) s).eval (n : ℝ)
            * (charlierPoly (r : ℝ) u).eval (n : ℝ)) := by
        intro n; ring
      simp_rw [e]
      rw [integral_const_mul, ih u]
      by_cases hsu : s = u
      · subst hsu
        rw [if_pos rfl, if_pos rfl]
        simp only [Nat.factorial_succ]
        push_cast
        ring
      · rw [if_neg hsu, if_neg (by omega)]
        ring

/-- The `L²` norm of a Charlier polynomial under the Poisson law of its own rate,
`E[C_s ^ 2] = s! r ^ s`. -/
theorem integral_charlierPoly_sq (r : ℝ≥0) (s : ℕ) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) ^ 2 ∂poissonMeasure r
      = (s.factorial : ℝ) * (r : ℝ) ^ s := by
  simpa [pow_two] using integral_charlierPoly_mul r s s

/-- A Charlier polynomial of positive degree is centred under the Poisson law of its own rate. -/
theorem integral_charlierPoly_eq_zero (r : ℝ≥0) {s : ℕ} (hs : s ≠ 0) :
    ∫ n : ℕ, (charlierPoly (r : ℝ) s).eval (n : ℝ) ∂poissonMeasure r = 0 := by
  simpa [hs] using integral_charlierPoly_mul r s 0

end LevyStochCalc.Probability
