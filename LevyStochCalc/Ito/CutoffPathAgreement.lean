/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaCutoff
import LevyStochCalc.Probability.OpenExitTime

/-!
# Agreement of the continuous integrands with their cut-off, along a confined path

`JumpFormulaCutoff.integrands_cutoffFun₂_eq_of_mem` compares all five integrands of a state
function with those of its cut-off, and for the two jump integrands it needs the jump coefficient
itself bounded over the window, for every mark. That hypothesis is not available in general: the
jump coefficient is only square integrable against the intensity, so `x + γ(s, x, e)` leaves
every ball however large the cut-off radius.

The three *continuous* integrands need no such hypothesis. They are read at path values only, so
a path confined to a ball is enough. `integrands_cutoffFun₂_eq_of_boundedPath` records that,
adding the gradient, which the pathwise form of the jump part also reads at path values.

For the Brownian transfer the confinement has to come from a stopping time rather than an event,
so the same agreement is restated below `min (openExitTime …) T`: strictly below the exit time
the path is in the ball, and strictly below `T` the time cut-off is inactive. That is exactly the
hypothesis shape of `stochasticIntegralBrownian_congr_of_lt`.

## Main statements

* `integrands_cutoffFun₂_eq_of_boundedPath` — drift, diffusion, path value and gradient agree
  with their cut-off along a path confined to the ball, with no hypothesis on the jumps.
* `boundedPathSet_subset_le_openExitTime` — a path confined to the ball over the window has not
  exited by the end of it.
* `diffusionIntegrand_cutoffFun₂_eq_of_lt` — the agreement in the form the strict locality
  transfer consumes.
-/

open MeasureTheory Filter Topology

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Ito.JumpFormulaCutoff

universe u v

variable {Ω : Type u} {n d : ℕ} {E : Type v}

/-- **The continuous integrands agree with their cut-off along a path confined to the ball**, with
no hypothesis on the jump coefficient. The gradient is included: the pathwise form of the jump
part reads it at path values too. -/
theorem integrands_cutoffFun₂_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    JumpFormula.driftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs s (Xp s ω)
          = JumpFormula.driftIntegrand u coeffs s (Xp s ω)
      ∧ JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
          = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω)
      ∧ cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω) = u s (Xp s ω)
      ∧ JumpFormula.gradient (cutoffFun₂ u (2 * (m : ℝ))) s (Xp s ω)
          = JumpFormula.gradient u s (Xp s ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  have hsabs : |s| < 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hTm
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) := hb s hs
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  exact ⟨driftIntegrand_cutoffFun₂ u coeffs hR hsabs hx,
    diffusionIntegrand_cutoffFun₂ u coeffs.σ hR (le_of_lt hsabs) hx,
    cutoffFun₂_eq hR (le_of_lt hsabs) (le_of_lt hx),
    gradient_cutoffFun₂ u hR (le_of_lt hsabs) hx⟩

/-- **A path confined to the ball over the window has not exited by the end of it.** -/
theorem boundedPathSet_subset_le_openExitTime (Xp : ℝ → Ω → Fin n → ℝ) (T : ℝ) (m : ℕ) :
    Brownian.Ito.boundedPathSet Xp T m
      ⊆ {ω : Ω | ((T : ℝ) : WithTop ℝ)
          ≤ Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω} := by
  intro ω hω
  exact Probability.le_openExitTime_of_forall_norm_le fun s hs0 hsT => hω s ⟨hs0, hsT⟩

/-- **The diffusion integrand agrees with its cut-off strictly below the exit time**, in the
shape the strict locality transfer consumes. Strictly below the exit time the path is in the
ball; strictly below `T` the time cut-off is inactive. -/
theorem diffusionIntegrand_cutoffFun₂_eq_of_lt {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) (ω : Ω) (s : ℝ) (hs : 0 < s)
    (hlt : ((s : ℝ) : WithTop ℝ)
      < min (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω) ((T : ℝ) : WithTop ℝ)) :
    JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
      = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  obtain ⟨hltτ, hltT⟩ := lt_min_iff.mp hlt
  have hsT : s < T := by exact_mod_cast hltT
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) :=
    Probability.norm_le_of_lt_openExitTime hs.le hltτ
  have hsabs : |s| ≤ 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.le]
    exact le_of_lt (lt_trans hsT hTm)
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  exact diffusionIntegrand_cutoffFun₂ u coeffs.σ hR hsabs hx

end LevyStochCalc.Ito.CutoffPath
