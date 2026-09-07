/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoIncrement
import LevyStochCalc.Brownian.ItoFormulaScalar
import LevyStochCalc.Analysis.ScaledTrig

/-!
# Itô's formula for the scaled cosine and sine of a Brownian increment

`x ↦ cos (l * x)` and `x ↦ sin (l * x)` satisfy the hypotheses of Itô's formula for a scalar Itô
process, so for a version of `∫ 1_{(a,b]} dW` they give

  `cos (l * X_T) − cos (l * X_0) = ∫ (−l sin (l X)) 1_{(a,b]} dW − (l²/2) ∫ cos (l X) 1_{(a,b]} ds`

and the companion identity for the sine.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A uniformly bounded process has finite `L²` mass over every time window. -/
theorem lintegral_sq_lt_top_of_bounded {P : Measure Ω} [IsProbabilityMeasure P]
    {F : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |F ω s| ≤ M) (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (ENNReal.ofReal (max M 0)) ^ 2 := by
    intro ω s
    refine pow_le_pow_left' ?_ 2
    calc (‖F ω s‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖F ω s‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal (max M 0) :=
          ENNReal.ofReal_le_ofReal
            (((Real.norm_eq_abs _).le.trans (hM ω s)).trans (le_max_left _ _))
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ : Ω, ∫⁻ _ in Set.Icc (0 : ℝ) T,
          (ENNReal.ofReal (max M 0)) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc,
          measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top) ENNReal.ofReal_lt_top

section Trig

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

/-- The integrand of the `dW` term is jointly measurable. -/
theorem measurable_trig_integrand
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry fun ω s => g (X s ω) * indIoc Ω a b ω s) :=
  (hg.measurable.comp hX.measurable_uncurry).mul hm

/-- The integrand of the `dW` term is progressively measurable. -/
theorem progressivelyMeasurable_trig_integrand
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => g (X s ω) * indIoc Ω a b ω s :=
  (hX.progressivelyMeasurable_comp hg).mul hp

/-- The integrand of the `dW` term has finite `L²` mass over every window. -/
theorem lintegral_sq_trig_integrand_lt_top {g : ℝ → ℝ} {M : ℝ} (hgM : ∀ x, |g x| ≤ M)
    (hM0 : 0 ≤ M) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  refine lintegral_sq_lt_top_of_bounded (M := M) (fun ω s => ?_) T hT
  rw [abs_mul]
  calc |g (X s ω)| * |indIoc Ω a b ω s| ≤ M * 1 :=
        mul_le_mul (hgM _) (indIoc_le_one a b ω s) (abs_nonneg _) hM0
    _ = M := mul_one M

variable (hC0 : (0 : ℝ) ≤ 1) (hCH : ∀ (ω : Ω) (s : ℝ), |indIoc Ω a b ω s| ≤ 1)

include hℱ hC0 hCH in
/-- **Itô's formula for the scaled cosine of a Brownian increment.** -/
theorem itoFormula_cos_scaled
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X) (l : ℝ)
    (hmg : Measurable (Function.uncurry fun ω s =>
      (-l * Real.sin (l * X s ω)) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (-l * Real.sin (l * X s ω)) * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(-l * Real.sin (l * X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => Real.cos (l * X T ω) - Real.cos (l * X 0 ω)) =ᵐ[P] fun ω =>
      stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (-l * Real.sin (l * X s ω)) * indIoc Ω a b ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
            (-l ^ 2 * Real.cos (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume := by
  have hbase := hX.itoFormula hC0 hCH (X₀ := fun _ => 0) measurable_const
    (bdrift := fun _ _ => 0) measurable_const (B := 0) le_rfl (fun ω s => by simp)
    (f := fun x => Real.cos (l * x)) (f' := fun x => -l * Real.sin (l * x))
    (f'' := fun x => -l ^ 2 * Real.cos (l * x))
    (LevyStochCalc.Analysis.hasDerivAt_cos_scaled l)
    (LevyStochCalc.Analysis.hasDerivAt_neg_sin_scaled l)
    (K₁ := |l|) (LevyStochCalc.Analysis.abs_neg_mul_sin_scaled_le l)
    (K₂ := l ^ 2) (sq_nonneg l) (LevyStochCalc.Analysis.abs_neg_sq_mul_cos_scaled_le l)
    (K := |l| ^ 3) (by positivity) (LevyStochCalc.Analysis.lipschitz_neg_sq_mul_cos_scaled l)
    hmg hpg hqg hT
  refine hbase.trans (Filter.Eventually.of_forall fun ω => ?_)
  simp

include hℱ hC0 hCH in
/-- **Itô's formula for the scaled sine of a Brownian increment.** -/
theorem itoFormula_sin_scaled
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X) (l : ℝ)
    (hmg : Measurable (Function.uncurry fun ω s =>
      (l * Real.cos (l * X s ω)) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (l * Real.cos (l * X s ω)) * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(l * Real.cos (l * X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => Real.sin (l * X T ω) - Real.sin (l * X 0 ω)) =ᵐ[P] fun ω =>
      stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (l * Real.cos (l * X s ω)) * indIoc Ω a b ω s) hmg hpg hqg T ω
        + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
            (-l ^ 2 * Real.sin (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume := by
  have hbase := hX.itoFormula hC0 hCH (X₀ := fun _ => 0) measurable_const
    (bdrift := fun _ _ => 0) measurable_const (B := 0) le_rfl (fun ω s => by simp)
    (f := fun x => Real.sin (l * x)) (f' := fun x => l * Real.cos (l * x))
    (f'' := fun x => -l ^ 2 * Real.sin (l * x))
    (LevyStochCalc.Analysis.hasDerivAt_sin_scaled l)
    (LevyStochCalc.Analysis.hasDerivAt_cos_scaled_mul l)
    (K₁ := |l|) (LevyStochCalc.Analysis.abs_mul_cos_scaled_le l)
    (K₂ := l ^ 2) (sq_nonneg l) (LevyStochCalc.Analysis.abs_neg_sq_mul_sin_scaled_le l)
    (K := |l| ^ 3) (by positivity) (LevyStochCalc.Analysis.lipschitz_neg_sq_mul_sin_scaled l)
    hmg hpg hqg hT
  refine hbase.trans (Filter.Eventually.of_forall fun ω => ?_)
  simp

end Trig

end LevyStochCalc.Brownian.Ito
