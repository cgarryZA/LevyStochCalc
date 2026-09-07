/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.PRPPairing
import LevyStochCalc.Brownian.ItoVersionExists

/-!
# One window of the Brownian predictable representation

A square-integrable weight orthogonal to every Itô integral, multiplied by a bounded weight
measurable before a window and having mean zero, stays orthogonal to the character of the
Brownian increment across that window.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The zero process is progressively measurable. -/
theorem progressivelyMeasurable_zero (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) := by
  intro t
  have h : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun _ => (0 : ℝ)) p.2)
      = fun _ : Ω × ℝ => (0 : ℝ) := by
    funext p
    simp [Set.indicator_apply]
  rw [h]
  exact stronglyMeasurable_const

section Cell

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

include hℱ in
/-- **One window.** For a square-integrable weight orthogonal to every Itô integral and a bounded
weight measurable before the window whose product with it has mean zero, the pairing against the
character of the Brownian increment across the window vanishes. -/
theorem pairing_cell_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    (hZV : ∫ ω, Z ω * V ω ∂P = 0) (l : ℝ) :
    ∫ ω, Z ω * V ω * Complex.exp (((l * (W.W b ω - W.W a ω) : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
  classical
  have hb0 : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hm := measurable_uncurry_indIoc (Ω := Ω) a b
  have hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) := by
    rcases eq_or_lt_of_le ha with rfl | ha'
    · exact progressivelyMeasurable_indIoc₀ ℱ hb0
    · exact progressivelyMeasurable_indIoc ℱ ha' hab
  have hq := lintegral_sq_indIoc_lt_top (Ω := Ω) P a b
  obtain ⟨X, hX⟩ := exists_isItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq
    (C := 1) zero_le_one (indIoc_le_one a b) hℱ0 hnull
    (X₀ := fun _ => (0 : ℝ)) measurable_const
    (fun _ _ => (0 : ℝ)) measurable_const (progressivelyMeasurable_zero ℱ)
    (B := 0) le_rfl (fun ω s => by simp)
  have hZ1 : Integrable Z P := hZ2.integrable one_le_two
  have hYm : Measurable fun ω => Z ω * V ω := hZm.mul hVm
  have hY : Integrable (fun ω => Z ω * V ω) P :=
    integrable_mul_of_bounded hZ1 hVm.aestronglyMeasurable hVb
  have hXm := hX.measurable_uncurry
  have hX0 := ae_eq_zero_of_isItoVersion_indIoc ha hab hX
  have hXb := ae_eq_increment_of_isItoVersion_indIoc ha hab hX
  -- both trigonometric pairings vanish at the right end of the window
  have key : ∀ g g' : ℝ → ℝ, Continuous g → (∀ x, |g x| ≤ 1) → Continuous g' →
      (∀ x, |g' x| ≤ |l|) →
      (∀ T : ℝ, 0 < T →
        ∀ (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
          (hpg : Probability.ProgressivelyMeasurable ℱ
            fun ω s => g' (X s ω) * indIoc Ω a b ω s)
          (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
          (fun ω => g (X T ω) - g (X 0 ω)) =ᵐ[P] fun ω =>
            stochasticIntegralBrownian W ℱ hℱ
                (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T ω
              + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
                  -l ^ 2 * g (X s ω) * indIoc Ω a b ω s ^ 2 ∂volume) →
      ∫ ω, (fun ω => Z ω * V ω) ω * ((g (X b ω) : ℝ) : ℂ) ∂P = 0 := by
    intro g g' hgc hgb hg'c hg'b hito
    refine pairing_eq_zero_of_norm_le hXm hX0 hYm hY hZV l hgc hgb ?_ b ⟨hb0.le, le_rfl⟩
    intro t ht0 _
    have hmg := measurable_trig_integrand hX hg'c
    have hpg := progressivelyMeasurable_trig_integrand hX hg'c
    have hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      fun T' hT' => lintegral_sq_trig_integrand_lt_top hg'b (abs_nonneg l) T' hT'
    refine norm_pairing_le_setIntegral_norm hXm hX0 hYm hY hZV l hgc hgb
      (A := fun ω => stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg t ω) ?_ ht0 (hito t ht0 hmg hpg hqg)
    exact pairing_ito_eq_zero ha hab hZ2 hZp hVm hMv0 hVb hVa
      (K := fun ω s => g' (X s ω)) (hg'c.measurable.comp hXm)
      (hX.progressivelyMeasurable_comp hg'c) (abs_nonneg l) (fun ω s => hg'b _)
      hmg hpg hqg ht0
  have hcos := key (fun x => Real.cos (l * x)) (fun x => -l * Real.sin (l * x))
    (Real.continuous_cos.comp (continuous_const.mul continuous_id))
    (fun x => Real.abs_cos_le_one _)
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).const_mul _)
    (LevyStochCalc.Analysis.abs_neg_mul_sin_scaled_le l)
    (fun T hT hmg hpg hqg =>
      itoFormula_cos_scaled zero_le_one (indIoc_le_one a b) hX l hmg hpg hqg hT)
  have hsin := key (fun x => Real.sin (l * x)) (fun x => l * Real.cos (l * x))
    (Real.continuous_sin.comp (continuous_const.mul continuous_id))
    (fun x => Real.abs_sin_le_one _)
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).const_mul _)
    (LevyStochCalc.Analysis.abs_mul_cos_scaled_le l)
    (fun T hT hmg hpg hqg =>
      itoFormula_sin_scaled zero_le_one (indIoc_le_one a b) hX l hmg hpg hqg hT)
  -- assemble the character from its real and imaginary parts
  have hexp : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
      = ((Real.cos x : ℝ) : ℂ) + Complex.I * ((Real.sin x : ℝ) : ℂ) := by
    intro x
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  have hintc : Integrable (fun ω => (Z ω * V ω)
      * ((Real.cos (l * X b ω) : ℝ) : ℂ)) P := by
    refine integrable_mul_of_bounded hY ?_ (c := 1) (fun ω => ?_)
    · exact (Complex.measurable_ofReal.comp (Real.continuous_cos.measurable.comp
        ((hX.measurable b).const_mul l))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_cos_le_one _
  have hints : Integrable (fun ω => (Z ω * V ω)
      * ((Real.sin (l * X b ω) : ℝ) : ℂ)) P := by
    refine integrable_mul_of_bounded hY ?_ (c := 1) (fun ω => ?_)
    · exact (Complex.measurable_ofReal.comp (Real.continuous_sin.measurable.comp
        ((hX.measurable b).const_mul l))).aestronglyMeasurable
    · rw [Complex.norm_real, Real.norm_eq_abs]
      exact Real.abs_sin_le_one _
  have hrw : ∫ ω, Z ω * V ω
        * Complex.exp (((l * (W.W b ω - W.W a ω) : ℝ) : ℂ) * Complex.I) ∂P
      = ∫ ω, ((Z ω * V ω) * ((Real.cos (l * X b ω) : ℝ) : ℂ)
          + Complex.I * ((Z ω * V ω) * ((Real.sin (l * X b ω) : ℝ) : ℂ))) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hXb] with ω hω
    rw [← hω, hexp (l * X b ω)]
    ring
  rw [hrw, integral_add hintc (hints.const_mul Complex.I), hcos, integral_const_mul, hsin,
    mul_zero, add_zero]

end Cell

end LevyStochCalc.Brownian.Ito
