/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolution
import LevyStochCalc.Ito.CutoffJumpTransfer
import LevyStochCalc.Ito.CutoffGlobalBounds
import LevyStochCalc.Ito.JumpSplittingRemainder

/-!
# The Itô–Lévy formula for a jump diffusion

The Itô–Lévy formula for a jointly `C²` state function of a jump diffusion, relative to the
filtration of the solution's SDE data, with no bound on the derivatives of the state function:
the only hypotheses beyond the SDE data are the joint measurability of the coefficients, the
window energy of the drift along the path, and the admissibility of the two derived integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` together with the integrability of the compensator drift.

The proof cuts the state function off outside a ball, applies the bounded-derivative formula to
the cut-off, and transfers every term back on the event that the path stays in the ball over the
window: the continuous side term by term, the jump side as a sum, through the arrival-time jump
relation of the solution. Almost every path stays in some ball.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim` —
  the residual form along a solution with càdlàg paths at every sample point.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Probability LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Ito.CutoffPath LevyStochCalc.Poisson.Compensated

universe u v

section Transfers

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {n : ℕ}

/-- A marked integrand read along the left limits of an almost surely càdlàg path has the same
window energy as read along the path. -/
theorem lintegral_sq_marked_leftLimPathAt_eq {X : ℝ → Ω → Fin n → ℝ}
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (F : ℝ → (Fin n → ℝ) → E → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖F s (leftLimPathAt X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖F s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPathAt X hcad] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  rw [hs]

/-- An integrand of the time and the state read along the left limits of an almost surely càdlàg
path has the same window energy as read along the path. -/
theorem lintegral_sq_leftLimPathAt_eq {X : ℝ → Ω → Fin n → ℝ}
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (f : ℝ → (Fin n → ℝ) → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (leftLimPathAt X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPathAt X hcad] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  rw [hs]

variable [SigmaFinite ν]

/-- A measurable marked function of the time whose iterated `L¹` bound on a closed window is
finite is integrable over the left-open window and all marks for the reference intensity. -/
theorem integrableOn_window_univ_of_lintegral_lt_top {g : ℝ × E → ℝ} (hg : Measurable g) {T : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    IntegrableOn g (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
      (LevyStochCalc.Poisson.referenceIntensity ν) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hm : Measurable fun q : ℝ × E => (‖g q‖₊ : ℝ≥0∞) :=
    hg.nnnorm.coe_nnreal_ennreal
  calc ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), ‖g q‖ₑ
          ∂(LevyStochCalc.Poisson.referenceIntensity ν)
        = ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), (‖g q‖₊ : ℝ≥0∞)
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
          simp only [enorm_eq_nnnorm]
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e in Set.univ, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume :=
          LevyStochCalc.Poisson.lintegral_referenceIntensity_window hm Set.univ T
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume := by
          simp only [Measure.restrict_univ]
      _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume :=
          lintegral_mono_set Set.Ioc_subset_Icc_self
      _ < ⊤ := hfin

end Transfers

end LevyStochCalc.Ito.JumpFormula
