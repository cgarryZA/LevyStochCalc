/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.Charlier
import Mathlib.Analysis.SpecialFunctions.Exponential

/-!
# The generating function of the Charlier polynomials of rate `lam`

At a natural argument `n` the Charlier polynomials of rate `lam` are generated over `ℂ` by
`e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)`, obtained by induction on `n`: the value
`C_s(0; lam) = (-lam) ^ s` matches the exponential series at `n = 0`, and the forward difference
`C_(s+1)(x + 1) - C_(s+1)(x) = (s + 1) C_s(x)` turns the step into an index shift, which on the
generating side multiplies by `1 + t`. The same induction, run on the bound
`|T_(s+1)(n + 1)| ≤ |T_(s+1)(n)| + |t| |T_s(n)|` for the terms `T_s(n) = (t ^ s / s!) C_s(n; lam)`
and started from the exponential series at `n = 0`, shows that the series is absolutely summable
at every natural argument.

## Main statements

* `LevyStochCalc.Probability.charlierScaled_zero_arg` — `C_s(0; lam) = (-lam) ^ s`.
* `LevyStochCalc.Probability.hasSum_charlierScaled` —
  `e^(-lam t) (1 + t) ^ n = ∑_s (t ^ s / s!) C_s(n; lam)` for `t : ℂ`.
* `LevyStochCalc.Probability.summable_norm_charlierScaled` — absolute summability of
  `t ^ s / s! · C_s(n; lam)` at every natural argument.
-/

namespace LevyStochCalc.Probability

open Finset

/-- `C_s(0; lam) = (-lam)^s`. -/
theorem charlierScaled_zero_arg (lam : ℝ) (s : ℕ) :
    charlierScaled s lam 0 = (-lam) ^ s := by
  induction s with
  | zero => simp
  | succ s ih => rw [charlierScaled_succ, ih]; ring

/-- The successor shift is injective on the naturals. -/
private theorem add_one_injective : Function.Injective (fun s : ℕ => s + 1) := fun a b h => by
  simpa using h

/-- The Charlier generating function `e^(-lam t) (1 + t)^n = ∑_s (t^s / s!) C_s(n; lam)`. -/
theorem hasSum_charlierScaled (lam : ℝ) (n : ℕ) (t : ℂ) :
    HasSum (fun s : ℕ => t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ))
      (Complex.exp (-(lam * t)) * (1 + t) ^ n) := by
  induction n with
  | zero =>
    have h : ∀ s : ℕ, t ^ s / (s.factorial : ℂ) * (charlierScaled s lam ((0 : ℕ) : ℝ) : ℂ)
        = (-(lam : ℂ) * t) ^ s / (s.factorial : ℂ) := by
      intro s
      rw [Nat.cast_zero, charlierScaled_zero_arg]
      push_cast
      rw [mul_pow]
      ring
    rw [funext h]
    simp only [pow_zero, mul_one]
    rw [show -((lam : ℂ) * t) = -(lam : ℂ) * t by ring, Complex.exp_eq_exp_ℂ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  | succ n ih =>
    have hshift : HasSum
        (fun s : ℕ => t ^ s / (s.factorial : ℂ) * ((s : ℂ) * (charlierScaled (s - 1) lam n : ℂ)))
        (t * (Complex.exp (-(lam * t)) * (1 + t) ^ n)) := by
      refine (Function.Injective.hasSum_iff add_one_injective ?_).mp ?_
      · intro m hm
        have hm0 : m = 0 := by
          by_contra hne
          refine hm (Set.mem_range.mpr ⟨m - 1, ?_⟩)
          show m - 1 + 1 = m
          omega
        simp [hm0]
      · have key : ∀ s : ℕ,
            ((fun s : ℕ => t ^ s / (s.factorial : ℂ)
                * ((s : ℂ) * (charlierScaled (s - 1) lam n : ℂ)))
              ∘ (fun s : ℕ => s + 1)) s
              = t * (t ^ s / (s.factorial : ℂ) * (charlierScaled s lam n : ℂ)) := by
          intro s
          simp only [Function.comp_apply, Nat.add_sub_cancel]
          have hf : ((s + 1).factorial : ℂ) = ((s : ℂ) + 1) * (s.factorial : ℂ) := by
            rw [Nat.factorial_succ]; push_cast; ring
          have h0 : ((s.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr s.factorial_ne_zero
          have h1 : ((s : ℂ) + 1) ≠ 0 := by
            have : ((s : ℂ) + 1) = ((s + 1 : ℕ) : ℂ) := by push_cast; ring
            rw [this, Ne, Nat.cast_eq_zero]
            omega
          rw [hf]
          push_cast
          field_simp
          ring
        rw [funext key]
        exact ih.mul_left t
    have hsum := ih.add hshift
    have hterm : ∀ s : ℕ,
        t ^ s / (s.factorial : ℂ) * (charlierScaled s lam n : ℂ)
          + t ^ s / (s.factorial : ℂ) * ((s : ℂ) * (charlierScaled (s - 1) lam n : ℂ))
          = t ^ s / (s.factorial : ℂ) * (charlierScaled s lam ((n : ℝ) + 1) : ℂ) := by
      intro s
      cases s with
      | zero => simp
      | succ m =>
        have hd := charlierScaled_forward_diff m lam (n : ℝ)
        have : charlierScaled (m + 1) lam ((n : ℝ) + 1)
            = charlierScaled (m + 1) lam (n : ℝ)
              + ((m : ℝ) + 1) * charlierScaled m lam (n : ℝ) := by
          linarith [hd]
        rw [this]
        simp only [Nat.add_sub_cancel]
        push_cast
        ring
    rw [funext hterm] at hsum
    have hval : Complex.exp (-(lam * t)) * (1 + t) ^ n
        + t * (Complex.exp (-(lam * t)) * (1 + t) ^ n)
        = Complex.exp (-(lam * t)) * (1 + t) ^ (n + 1) := by
      rw [pow_succ]
      ring
    rw [hval] at hsum
    have hcast : ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hcast] at hsum
    exact hsum

/-- The sequence `t ^ s / s! * C_s(n; lam)` is absolutely summable at every natural
argument. -/
theorem summable_norm_charlierScaled (lam : ℝ) (n : ℕ) (t : ℂ) :
    Summable fun s : ℕ => ‖t ^ s / (s.factorial : ℂ) * (charlierScaled s lam (n : ℝ) : ℂ)‖ := by
  induction n with
  | zero =>
    have h : ∀ s : ℕ, ‖t ^ s / (s.factorial : ℂ) * (charlierScaled s lam ((0 : ℕ) : ℝ) : ℂ)‖
        = ‖-(lam : ℂ) * t‖ ^ s / (s.factorial : ℝ) := by
      intro s
      have hs : t ^ s / (s.factorial : ℂ) * (charlierScaled s lam ((0 : ℕ) : ℝ) : ℂ)
          = (-(lam : ℂ) * t) ^ s / (s.factorial : ℂ) := by
        rw [Nat.cast_zero, charlierScaled_zero_arg]
        push_cast
        rw [mul_pow]
        ring
      rw [hs, norm_div, norm_pow, Complex.norm_natCast]
    rw [funext h]
    exact (NormedSpace.expSeries_div_hasSum_exp ‖-(lam : ℂ) * t‖).summable
  | succ n ih =>
    have hshift : Summable fun s : ℕ =>
        ‖t‖ * (if s = 0 then 0 else ‖t ^ (s - 1) / ((s - 1).factorial : ℂ)
          * (charlierScaled (s - 1) lam (n : ℝ) : ℂ)‖) := by
      refine (Function.Injective.summable_iff add_one_injective ?_).mp ?_
      · intro m hm
        have hm0 : m = 0 := by
          by_contra hne
          refine hm (Set.mem_range.mpr ⟨m - 1, ?_⟩)
          show m - 1 + 1 = m
          omega
        subst hm0
        rw [if_pos rfl, mul_zero]
      · exact ih.mul_left ‖t‖
    refine Summable.of_nonneg_of_le (fun s => norm_nonneg _) (fun s => ?_) (ih.add hshift)
    cases s with
    | zero => simp
    | succ m =>
      have hd := charlierScaled_forward_diff m lam (n : ℝ)
      have hrec : charlierScaled (m + 1) lam ((n : ℝ) + 1)
          = charlierScaled (m + 1) lam (n : ℝ)
            + ((m : ℝ) + 1) * charlierScaled m lam (n : ℝ) := by linarith [hd]
      have hcast : (((n + 1 : ℕ) : ℝ)) = ((n : ℝ) + 1) := by push_cast; ring
      have hsplit : t ^ (m + 1) / ((m + 1).factorial : ℂ)
            * (charlierScaled (m + 1) lam ((n + 1 : ℕ) : ℝ) : ℂ)
          = t ^ (m + 1) / ((m + 1).factorial : ℂ)
              * (charlierScaled (m + 1) lam (n : ℝ) : ℂ)
            + t * (t ^ m / (m.factorial : ℂ) * (charlierScaled m lam (n : ℝ) : ℂ)) := by
        rw [hcast, hrec]
        have hf : (((m + 1).factorial : ℕ) : ℂ) = ((m : ℂ) + 1) * (m.factorial : ℂ) := by
          rw [Nat.factorial_succ]; push_cast; ring
        have h0 : ((m.factorial : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr m.factorial_ne_zero
        have h1 : ((m : ℂ) + 1) ≠ 0 := by
          have hc : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
          rw [hc, Ne, Nat.cast_eq_zero]
          omega
        rw [hf]
        push_cast
        field_simp
        ring
      rw [hsplit]
      refine (norm_add_le _ _).trans ?_
      simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero m), norm_mul]
      exact le_refl _

end LevyStochCalc.Probability
