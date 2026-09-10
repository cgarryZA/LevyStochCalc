/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormula
import LevyStochCalc.Brownian.CoordDerivative

/-!
# Taylor bounds for the state increments of a `C²` function

For a function `u : ℝ → (Fin n → ℝ) → ℝ` of time and state that is `C²` jointly, the increment
`u(s, y + v) − u(s, y)` at a fixed time is controlled by a bound on the gradient, and the
first-order Taylor remainder `u(s, y + v) − u(s, y) − vᵀ∇u(s, y)` by a bound on the Hessian.
Both are mean value bounds: the first for `u(s, ·)` on the whole state space, the second for
`z ↦ u(s, z) − ∇u(s, y)ᵀ z` on the ball of radius `‖v‖` about `y`, where its derivative
`∇u(s, z) − ∇u(s, y)` is at most the Lipschitz constant of the gradient times `‖v‖`.

The hypotheses are the coordinatewise bounds on `gradient` and `hessian`, and the state space
carries the supremum norm, so the constants pick up the dimension: the operator norm of a
functional on `Fin n → ℝ` is at most the sum of its `n` coordinates, and that of a bilinear form
at most the sum of its `n²` coordinates.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.fderiv_apply_eq_sum_gradient` — the state derivative applied to
  a vector is the coordinate pairing with the gradient.
* `LevyStochCalc.Ito.JumpFormula.hessian_eq_fderiv_fderiv` — the Hessian is the second state
  derivative on the standard basis.
* `LevyStochCalc.Ito.JumpFormula.norm_fderiv_le_of_gradient_le`,
  `LevyStochCalc.Ito.JumpFormula.norm_fderiv_fderiv_le_of_hessian_le` — operator norm bounds on
  the first and second state derivatives from the coordinatewise bounds.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_le_of_gradient_le` — the increment bound
  `|u(s, y + v) − u(s, y)| ≤ n K₁ ‖v‖`.
* `LevyStochCalc.Ito.JumpFormula.abs_sub_sub_le_of_hessian_le` — the remainder bound
  `|u(s, y + v) − u(s, y) − vᵀ∇u(s, y)| ≤ n² K₂ ‖v‖²`.
-/

namespace LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

section Derivatives

/-- The state section of a `C²` function of time and state is `C²`. -/
theorem contDiff_state_section (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ) :
    ContDiff ℝ 2 (u s) :=
  hu.comp (contDiff_const.prodMk contDiff_id)

/-- The state section of a `C²` function of time and state is differentiable, with derivative
its Fréchet derivative. -/
theorem hasFDerivAt_state_section (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (z : Fin n → ℝ) : HasFDerivAt (u s) (fderiv ℝ (u s) z) z :=
  ((contDiff_state_section hu s).differentiable (by norm_num) z).hasFDerivAt

/-- The state derivative of a `C²` function of time and state is differentiable, with derivative
the second Fréchet derivative. -/
theorem hasFDerivAt_fderiv_state_section (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (z : Fin n → ℝ) : HasFDerivAt (fderiv ℝ (u s)) (fderiv ℝ (fderiv ℝ (u s)) z) z :=
  (((contDiff_state_section hu s).fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num) z).hasFDerivAt

/-- The state derivative applied to a vector is the coordinate pairing of the vector with the
gradient. -/
theorem fderiv_apply_eq_sum_gradient (s : ℝ) (z v : Fin n → ℝ) :
    fderiv ℝ (u s) z v = ∑ i, v i * gradient u s z i :=
  clm_apply_pi_real (fderiv ℝ (u s) z) v

/-- The Hessian is the second state derivative evaluated on the standard basis, the direction of
the outer differentiation first. -/
theorem hessian_eq_fderiv_fderiv (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ)
    (z : Fin n → ℝ) (p q : Fin n) :
    hessian u s z p q = fderiv ℝ (fderiv ℝ (u s)) z (Pi.single q 1) (Pi.single p 1) := by
  have hap : HasFDerivAt (fun y : Fin n → ℝ => fderiv ℝ (u s) y (Pi.single p 1))
      ((ContinuousLinearMap.apply ℝ ℝ (Pi.single p 1 : Fin n → ℝ)).comp
        (fderiv ℝ (fderiv ℝ (u s)) z)) z :=
    (ContinuousLinearMap.apply ℝ ℝ (Pi.single p 1 : Fin n → ℝ)).hasFDerivAt.comp z
      (hasFDerivAt_fderiv_state_section hu s z)
  simp only [hessian, hap.fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply]

end Derivatives

section GradientBound

/-- The operator norm of the state derivative is at most `n` times a coordinatewise bound on
the gradient. -/
theorem norm_fderiv_le_of_gradient_le {K₁ : ℝ} (s : ℝ) (hK : ∀ z i, |gradient u s z i| ≤ K₁)
    (z : Fin n → ℝ) : ‖fderiv ℝ (u s) z‖ ≤ (n : ℝ) * K₁ := by
  refine (norm_le_sum_abs_apply (fderiv ℝ (u s) z)).trans ?_
  calc ∑ p, |fderiv ℝ (u s) z (Pi.single p 1)| = ∑ p, |gradient u s z p| := rfl
    _ ≤ ∑ _p : Fin n, K₁ := Finset.sum_le_sum fun p _ => hK z p
    _ = (n : ℝ) * K₁ := by simp

/-- **Increment bound from a gradient bound.** A coordinatewise bound `K₁` on the gradient of a
`C²` function of time and state bounds its state increments by `n K₁ ‖v‖`. -/
theorem abs_sub_le_of_gradient_le (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₁ : ℝ} (s : ℝ)
    (hK : ∀ z i, |gradient u s z i| ≤ K₁) (y v : Fin n → ℝ) :
    |u s (y + v) - u s y| ≤ (n : ℝ) * K₁ * ‖v‖ := by
  have h := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le (f := u s)
    (f' := fun z => fderiv ℝ (u s) z) (s := Set.univ) (C := (n : ℝ) * K₁)
    (fun z _ => (hasFDerivAt_state_section hu s z).hasFDerivWithinAt)
    (fun z _ => norm_fderiv_le_of_gradient_le s hK z) convex_univ (Set.mem_univ y)
    (Set.mem_univ (y + v))
  simpa [Real.norm_eq_abs] using h

/-- **Increment bound from a bound on the norm of the gradient.** -/
theorem abs_sub_le_of_norm_gradient_le (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₁ : ℝ}
    (s : ℝ) (hK : ∀ z, ‖gradient u s z‖ ≤ K₁) (y v : Fin n → ℝ) :
    |u s (y + v) - u s y| ≤ (n : ℝ) * K₁ * ‖v‖ :=
  abs_sub_le_of_gradient_le hu s (fun z i => by
    simpa [Real.norm_eq_abs] using (norm_le_pi_norm (gradient u s z) i).trans (hK z)) y v

end GradientBound

section HessianBound

/-- The operator norm of the second state derivative is at most `n²` times a coordinatewise
bound on the Hessian. -/
theorem norm_fderiv_fderiv_le_of_hessian_le (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₂ : ℝ}
    (s : ℝ) (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (z : Fin n → ℝ) :
    ‖fderiv ℝ (fderiv ℝ (u s)) z‖ ≤ (n : ℝ) ^ 2 * K₂ := by
  refine (norm_le_sum_abs_apply₂ (fderiv ℝ (fderiv ℝ (u s)) z)).trans ?_
  calc ∑ p, ∑ q, |fderiv ℝ (fderiv ℝ (u s)) z (Pi.single p 1) (Pi.single q 1)|
      = ∑ p, ∑ q, |hessian u s z q p| := by simp only [hessian_eq_fderiv_fderiv hu s]
    _ ≤ ∑ _p : Fin n, ∑ _q : Fin n, K₂ :=
        Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => hK z q p
    _ = (n : ℝ) ^ 2 * K₂ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The state derivative of a `C²` function of time and state is Lipschitz with constant `n²`
times a coordinatewise bound on the Hessian. -/
theorem norm_fderiv_sub_le_of_hessian_le (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₂ : ℝ}
    (s : ℝ) (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (z w : Fin n → ℝ) :
    ‖fderiv ℝ (u s) z - fderiv ℝ (u s) w‖ ≤ (n : ℝ) ^ 2 * K₂ * ‖z - w‖ :=
  norm_fderiv_sub_le (hasFDerivAt_fderiv_state_section hu s)
    (norm_fderiv_fderiv_le_of_hessian_le hu s hK) z w

/-- **First-order Taylor remainder bound from a Hessian bound.** A coordinatewise bound `K₂` on
the Hessian of a `C²` function of time and state bounds the remainder
`u(s, y + v) − u(s, y) − vᵀ∇u(s, y)` by `n² K₂ ‖v‖²`. -/
theorem abs_sub_sub_le_of_hessian_le (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₂ : ℝ}
    (s : ℝ) (hK : ∀ z p q, |hessian u s z p q| ≤ K₂) (y v : Fin n → ℝ) :
    |u s (y + v) - u s y - ∑ i, v i * gradient u s y i| ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ ^ 2 := by
  have hK0 : 0 ≤ (n : ℝ) ^ 2 * K₂ := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · exact mul_nonneg (by positivity) ((abs_nonneg _).trans (hK y ⟨0, hn⟩ ⟨0, hn⟩))
  have hg : ∀ z ∈ Metric.closedBall y ‖v‖,
      HasFDerivWithinAt (fun z => u s z - fderiv ℝ (u s) y z)
        (fderiv ℝ (u s) z - fderiv ℝ (u s) y) (Metric.closedBall y ‖v‖) z :=
    fun z _ => ((hasFDerivAt_state_section hu s z).sub
      (fderiv ℝ (u s) y).hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ z ∈ Metric.closedBall y ‖v‖,
      ‖fderiv ℝ (u s) z - fderiv ℝ (u s) y‖ ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ := by
    intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    exact (norm_fderiv_sub_le_of_hessian_le hu s hK z y).trans
      (mul_le_mul_of_nonneg_left hz hK0)
  have hmem : y + v ∈ Metric.closedBall y ‖v‖ := by
    rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left]
  have hmvt := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hg hbound
    (convex_closedBall y ‖v‖) (Metric.mem_closedBall_self (norm_nonneg v)) hmem
  have halg : u s (y + v) - fderiv ℝ (u s) y (y + v) - (u s y - fderiv ℝ (u s) y y)
      = u s (y + v) - u s y - ∑ i, v i * gradient u s y i := by
    rw [← fderiv_apply_eq_sum_gradient, map_add]
    ring
  rw [halg, Real.norm_eq_abs, add_sub_cancel_left] at hmvt
  calc |u s (y + v) - u s y - ∑ i, v i * gradient u s y i|
      ≤ (n : ℝ) ^ 2 * K₂ * ‖v‖ * ‖v‖ := hmvt
    _ = (n : ℝ) ^ 2 * K₂ * ‖v‖ ^ 2 := by ring

end HessianBound

end LevyStochCalc.Ito.JumpFormula
