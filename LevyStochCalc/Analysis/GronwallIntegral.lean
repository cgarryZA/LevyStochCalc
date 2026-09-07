/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Topology.Algebra.Order.Floor

/-!
# A Grönwall inequality in integral form

A nonnegative function bounded by a multiple of its own running integral is identically zero:
iterating the inequality bounds it by `B·(c(t−a))ᵐ/m!` for every `m`, and that tends to zero.
-/

open MeasureTheory

namespace LevyStochCalc.Analysis

/-- The iterated bound: a nonnegative function bounded by `B` and by `c` times its running
integral is bounded by `B·(c(t−a))ᵐ/m!` for every `m`. -/
theorem le_mul_pow_div_factorial_of_le_mul_setIntegral {a b c B : ℝ} (hc : 0 ≤ c)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (hB : ∀ t ∈ Set.Icc a b, f t ≤ B)
    (hineq : ∀ t ∈ Set.Icc a b, f t ≤ c * ∫ u in Set.Ioc a t, f u) (m : ℕ) :
    ∀ t ∈ Set.Icc a b, f t ≤ B * (c * (t - a)) ^ m / (m).factorial := by
  induction m with
  | zero => intro t ht; simpa using hB t ht
  | succ m ih =>
      intro t ht
      obtain ⟨hat, htb⟩ := ht
      have hfint : IntegrableOn f (Set.Ioc a t) := by
        refine Measure.integrableOn_of_bounded (M := B) (by simp) hf.aestronglyMeasurable ?_
        refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
        intro x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]
        exact hB x ⟨le_of_lt hx.1, hx.2.trans htb⟩
      have hgint : IntervalIntegrable
          (fun u => B * (c * (u - a)) ^ m / (m).factorial) volume a t :=
        (Continuous.intervalIntegrable (by fun_prop) a t)
      have hmono : ∫ u in a..t, f u
          ≤ ∫ u in a..t, B * (c * (u - a)) ^ m / (m).factorial := by
        refine intervalIntegral.integral_mono_on hat
          ((intervalIntegrable_iff_integrableOn_Ioc_of_le hat).mpr hfint) hgint ?_
        intro u hu
        exact ih u ⟨hu.1, hu.2.trans htb⟩
      have hcalc : ∫ u in a..t, B * (c * (u - a)) ^ m / (m).factorial
          = B * c ^ m / (m).factorial * ((t - a) ^ (m + 1) / (m + 1)) := by
        have hrw : ∀ u : ℝ, B * (c * (u - a)) ^ m / (m).factorial
            = B * c ^ m / (m).factorial * (u - a) ^ m := by
          intro u; rw [mul_pow]; ring
        simp only [hrw]
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_sub_right (fun x => x ^ m) a,
          integral_pow]
        simp
      have hstep : f t ≤ c * ∫ u in a..t, f u := by
        rw [intervalIntegral.integral_of_le hat]
        exact hineq t ⟨hat, htb⟩
      have hfin : c * ∫ u in a..t, f u
          ≤ B * (c * (t - a)) ^ (m + 1) / (m + 1).factorial := by
        refine le_trans (mul_le_mul_of_nonneg_left hmono hc) (le_of_eq ?_)
        rw [hcalc]
        have hfac : ((m + 1).factorial : ℝ) = (m + 1) * (m).factorial := by
          rw [Nat.factorial_succ]; push_cast; ring
        rw [hfac, mul_pow]
        have hm : (0 : ℝ) < (m).factorial := by exact_mod_cast (m).factorial_pos
        have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
        field_simp
        ring
      exact hstep.trans hfin

/-- **Grönwall in integral form.** A nonnegative measurable function bounded on `Set.Icc a b`
and dominated there by a constant multiple of its own running integral vanishes. -/
theorem eq_zero_of_le_mul_setIntegral {a b c B : ℝ} (hc : 0 ≤ c)
    {f : ℝ → ℝ} (hf : Measurable f) (hf0 : ∀ t, 0 ≤ f t)
    (hB : ∀ t ∈ Set.Icc a b, f t ≤ B)
    (hineq : ∀ t ∈ Set.Icc a b, f t ≤ c * ∫ u in Set.Ioc a t, f u) :
    ∀ t ∈ Set.Icc a b, f t = 0 := by
  intro t ht
  refine le_antisymm ?_ (hf0 t)
  have hlim : Filter.Tendsto (fun m : ℕ => B * ((c * (t - a)) ^ m / (m).factorial))
      Filter.atTop (nhds 0) := by
    simpa using (FloorSemiring.tendsto_pow_div_factorial_atTop (c * (t - a))).const_mul B
  refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun m => ?_)
  calc f t ≤ B * (c * (t - a)) ^ m / (m).factorial :=
        le_mul_pow_div_factorial_of_le_mul_setIntegral hc hf hf0 hB hineq m t ht
    _ = B * ((c * (t - a)) ^ m / (m).factorial) := by ring

end LevyStochCalc.Analysis
