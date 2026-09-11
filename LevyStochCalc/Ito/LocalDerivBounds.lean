/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaContinuity

/-!
# Local bounds on the derivatives of a `C²` state function

A `C²` function of time and state has continuous time derivative, gradient and Hessian, so on a
compact time–space box each of them is bounded. `exists_bound_on_box` packages the three bounds
as a single constant, and `exists_bound_on_box_of_le` reads it along a path confined to a ball.

These are the local replacements for the global derivative bounds of the bounded-derivative
Itô–Lévy formula: where that theorem asks `|∂ₜu| ≤ K₀`, `|∇u| ≤ K₁` and `|∇²u| ≤ K₂` everywhere,
a path stopped on leaving a ball only meets the state function on a compact box, where the same
bounds hold for free.

## Main statements

* `exists_bound_on_box` — on `[0, T] × closedBall 0 R` the time derivative, every gradient entry
  and every Hessian entry of a `C²` function are bounded by one constant.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Ito.JumpFormula

universe u

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The sum of the absolute values of the gradient entries is continuous. -/
theorem continuous_sum_abs_gradient (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ∑ i : Fin n, |gradient u p.1 p.2 i| :=
  continuous_finsetSum _ fun i _ => (continuous_gradient_uncurry hu i).abs

/-- The sum of the absolute values of the Hessian entries is continuous. -/
theorem continuous_sum_abs_hessian (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    Continuous fun p : ℝ × (Fin n → ℝ) => ∑ i : Fin n, ∑ j : Fin n, |hessian u p.1 p.2 i j| :=
  continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => (continuous_hessian hu i j).abs

/-- **On a compact time–space box the three derivative families of a `C²` function are
bounded by one constant.** -/
theorem exists_bound_on_box (hu : ContDiff ℝ 2 (Function.uncurry u)) (T R : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧
      (∀ s x, s ∈ Set.Icc (0 : ℝ) T → ‖x‖ ≤ R → |timeDeriv u s x| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc (0 : ℝ) T → ‖x‖ ≤ R → ∀ i, |gradient u s x i| ≤ K) ∧
      (∀ s x, s ∈ Set.Icc (0 : ℝ) T → ‖x‖ ≤ R → ∀ i j, |hessian u s x i j| ≤ K) := by
  classical
  set B : Set (ℝ × (Fin n → ℝ)) :=
    Set.Icc (0 : ℝ) T ×ˢ Metric.closedBall (0 : Fin n → ℝ) R with hBdef
  have hBc : IsCompact B := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨M₀, hM₀⟩ := hBc.exists_bound_of_continuousOn (continuous_timeDeriv hu).continuousOn
  obtain ⟨M₁, hM₁⟩ :=
    hBc.exists_bound_of_continuousOn (continuous_sum_abs_gradient hu).continuousOn
  obtain ⟨M₂, hM₂⟩ :=
    hBc.exists_bound_of_continuousOn (continuous_sum_abs_hessian hu).continuousOn
  refine ⟨max 0 (max M₀ (max M₁ M₂)), le_max_left _ _, ?_, ?_, ?_⟩
  · intro s x hs hx
    have hmem : (s, x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have := hM₀ (s, x) hmem
    rw [Real.norm_eq_abs] at this
    exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro s x hs hx i
    have hmem : (s, x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have hsum := hM₁ (s, x) hmem
    rw [Real.norm_eq_abs] at hsum
    have hle : |gradient u s x i| ≤ ∑ k : Fin n, |gradient u s x k| :=
      Finset.single_le_sum (f := fun k : Fin n => |gradient u s x k|)
        (fun k _ => abs_nonneg _) (Finset.mem_univ i)
    refine hle.trans (le_trans (le_abs_self _) (hsum.trans ?_))
    exact ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  · intro s x hs hx i j
    have hmem : (s, x) ∈ B := ⟨hs, by simpa [Metric.mem_closedBall, dist_zero_right] using hx⟩
    have hsum := hM₂ (s, x) hmem
    rw [Real.norm_eq_abs] at hsum
    have hle1 : |hessian u s x i j| ≤ ∑ l : Fin n, |hessian u s x i l| :=
      Finset.single_le_sum (f := fun l : Fin n => |hessian u s x i l|)
        (fun l _ => abs_nonneg _) (Finset.mem_univ j)
    have hle2 : (∑ l : Fin n, |hessian u s x i l|)
        ≤ ∑ k : Fin n, ∑ l : Fin n, |hessian u s x k l| :=
      Finset.single_le_sum (f := fun k : Fin n => ∑ l : Fin n, |hessian u s x k l|)
        (fun k _ => Finset.sum_nonneg fun l _ => abs_nonneg _) (Finset.mem_univ i)
    refine (hle1.trans hle2).trans (le_trans (le_abs_self _) (hsum.trans ?_))
    exact ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)

end LevyStochCalc.Ito.JumpFormula
