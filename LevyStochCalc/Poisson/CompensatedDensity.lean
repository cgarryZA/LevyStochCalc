/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedMartingale

/-!
# Density of adapted simple predictable integrands (compensated Poisson)

Toward the L²-completion of the compensated-Poisson simple integral: adapted
`SimplePredictable` integrands are dense in `L²(P ⊗ ds ⊗ ν)`. The construction
reduces a general predictable square-integrable integrand `φ : Ω → ℝ → E → ℝ` to a
bounded one by truncation (this file's `truncation_L2_converges`), then discretizes
time and the mark space (subsequent steps). Compensated mirror of
`Brownian/ItoDensity.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Pointwise truncation tends to the value.** For the clip
`x ↦ max (-M) (min M x)`, `‖x − clip M x‖² → 0` as `M → ∞` (eventually `clip M x = x`). -/
private lemma truncation_pointwise_tendsto (x : ℝ) :
    Filter.Tendsto
      (fun M : ℕ => (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop ⌈|x|⌉₊] with M hM
  have hMx : |x| ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hM)
  have h_clip : max (-(M : ℝ)) (min (M : ℝ) x) = x := by
    rw [min_eq_right (le_trans (le_abs_self x) hMx)]
    exact max_eq_right (by linarith [neg_abs_le x])
  show (0 : ℝ≥0∞) = (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
  rw [h_clip, sub_self]; simp

/-- **Pointwise truncation dominated** by the value's square. -/
private lemma truncation_dominated (x : ℝ) (M : ℕ) :
    (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2 ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h_abs : |x - max (-(M : ℝ)) (min (M : ℝ) x)| ≤ |x| := by
    by_cases hx : 0 ≤ x
    · by_cases hxM : x ≤ M
      · rw [min_eq_right hxM, max_eq_right (by linarith)]; simp [abs_nonneg]
      · push Not at hxM
        rw [min_eq_left (le_of_lt hxM), max_eq_right (by linarith : -(M : ℝ) ≤ M)]
        rw [abs_of_nonneg (by linarith : 0 ≤ x - M), abs_of_nonneg hx]; linarith
    · push Not at hx
      by_cases hxM : -(M : ℝ) ≤ x
      · rw [min_eq_right (by linarith : x ≤ M), max_eq_right hxM]; simp
      · push Not at hxM
        rw [min_eq_right (by linarith : x ≤ M), max_eq_left (le_of_lt hxM)]
        rw [show x - -(M : ℝ) = x + M from by ring]
        rw [abs_of_nonpos (by linarith : x + (M : ℝ) ≤ 0), abs_of_neg hx]; linarith
  have h_nn : ‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ ≤ ‖x‖₊ := by
    rw [← NNReal.coe_le_coe]; simp only [coe_nnnorm, Real.norm_eq_abs]; exact h_abs
  exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr h_nn) 2

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: nested triple-lintegral dominated-convergence budget.
/-- **Truncation `L²` convergence (compensated).** For a jointly measurable
square-integrable `φ : Ω → ℝ → E → ℝ`, the clipped integrands `clip M ∘ φ` converge
to `φ` in `L²(P ⊗ ds ⊗ ν)`. Three nested applications of the dominated-convergence
theorem (over `ν`, then `ds`, then `P`), dominated by `‖φ‖²`, tending pointwise to `0`. -/
lemma truncation_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Filter.Tendsto
      (fun M : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - max (-(M : ℝ)) (min (M : ℝ) (φ ω s e))‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  set F : ℕ → Ω → ℝ → E → ℝ≥0∞ := fun M ω s e =>
    (‖φ ω s e - max (-(M : ℝ)) (min (M : ℝ) (φ ω s e))‖₊ : ℝ≥0∞) ^ 2 with hF
  set G : Ω → ℝ → E → ℝ≥0∞ := fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 with hG
  have hFmeas : ∀ M : ℕ, Measurable (fun p : Ω × ℝ × E => F M p.1 p.2.1 p.2.2) := by
    intro M
    have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (h_clip.comp h_meas)).nnnorm).pow_const 2
  have hGmeas : Measurable (fun p : Ω × ℝ × E => G p.1 p.2.1 p.2.2) :=
    (ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2
  -- `(ω, s) ↦ ∫⁻_E (·) ∂ν` is measurable for `F M` and `G` (reassociate `Ω×ℝ×E`).
  have hFstepA : ∀ M : ℕ, Measurable (fun q : Ω × ℝ => ∫⁻ e, F M q.1 q.2 e ∂ν) := fun M =>
    ((hFmeas M).comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  have hGstepA : Measurable (fun q : Ω × ℝ => ∫⁻ e, G q.1 q.2 e ∂ν) :=
    (hGmeas.comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, G ω s e ∂ν ∂volume) ?_ ?_ h_sq_int.ne ?_
  · intro M
    exact (hFstepA M).lintegral_prod_right'.aemeasurable
  · intro M
    refine Filter.Eventually.of_forall (fun ω => MeasureTheory.lintegral_mono (fun s => ?_))
    exact MeasureTheory.lintegral_mono (fun e => truncation_dominated _ _)
  · have h_finite_inner : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, G ω s e ∂ν ∂volume < ⊤ :=
      MeasureTheory.ae_lt_top hGstepA.lintegral_prod_right' h_sq_int.ne
    filter_upwards [h_finite_inner] with ω hω_fin
    rw [show (0 : ℝ≥0∞)
        = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => ∫⁻ e, G ω s e ∂ν) ?_ ?_ hω_fin.ne ?_
    · intro M
      exact ((hFmeas M).comp (by fun_prop :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right'.aemeasurable
    · intro M
      exact Filter.Eventually.of_forall
        (fun s => MeasureTheory.lintegral_mono (fun e => truncation_dominated _ _))
    · have h_fin_s : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫⁻ e, G ω s e ∂ν < ⊤ :=
        MeasureTheory.ae_lt_top
          ((hGmeas.comp (by fun_prop :
            Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right')
          hω_fin.ne
      filter_upwards [h_fin_s] with s hs_fin
      rw [show (0 : ℝ≥0∞) = ∫⁻ _ : E, (0 : ℝ≥0∞) ∂ν from by simp]
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun e => G ω s e) ?_ ?_ hs_fin.ne ?_
      · intro M
        exact ((hFmeas M).comp (by fun_prop :
          Measurable fun e : E => ((ω, s, e) : Ω × ℝ × E))).aemeasurable
      · intro M
        exact Filter.Eventually.of_forall (fun e => truncation_dominated _ _)
      · exact Filter.Eventually.of_forall (fun e => truncation_pointwise_tendsto (φ ω s e))

end LevyStochCalc.Poisson.Compensated
