/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardIntegrand
import LevyStochCalc.Ito.PicardSpace

/-!
# The Picard step's output fields

`picardStepOnS2` takes the four fields of its own output — joint measurability, progressive
measurability, almost-sure càdlàg paths and a finite Bielecki norm — as hypotheses. This file
supplies the `L²` half: each of the three components of the step is bounded in `L²`, uniformly
over `[0, T]`, by data the step already carries.

## Main statements

* `LevyStochCalc.Ito.Picard.sq_nnnorm_sum_le` — Cauchy–Schwarz for a finite sum, in `ℝ≥0∞`.
* `LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_diffusion_le` — the second moment of the
  diffusion component, via the Itô isometry.
* `LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_jump_eq` — the second moment of the jump
  component, via the Itô–Lévy isometry.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Cauchy–Schwarz for a finite sum of reals, transported to `ℝ≥0∞`. -/
theorem sq_nnnorm_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2 ≤ (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : (∑ j ∈ s, f j) ^ 2 ≤ (s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc (‖∑ j ∈ s, f j‖₊ : ℝ≥0∞) ^ 2
      = ENNReal.ofReal ((∑ j ∈ s, f j) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal ((s.card : ℝ) * ∑ j ∈ s, (f j) ^ 2) := ENNReal.ofReal_le_ofReal h1
    _ = (s.card : ℝ≥0∞) * ∑ j ∈ s, (‖f j‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
          ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl fun j _ => (sq_coe_nnnorm_real (f j)).symm)

variable {n d : ℕ} {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]

omit [MeasurableSpace E] in
/-- **Second moment of the diffusion component**, by the Itô isometry applied to each of the
`d` component integrals. -/
theorem lintegral_sq_picardStep_diffusion_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set M : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j) t ω with hM
  have hM_meas : ∀ j : Fin d, Measurable (M j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j)
    exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
  have hunfold : ∀ ω : Ω,
      picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i
        = ∑ j : Fin d, M j ω := by
    intro ω
    simp only [picardStep_diffusion,
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, M]
  calc ∫⁻ ω, (‖picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (d : ℝ≥0∞) * ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        refine lintegral_mono fun ω => ?_
        simpa using sq_nnnorm_sum_le (Finset.univ : Finset (Fin d)) (fun j => M j ω)
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : (d : ℝ≥0∞) ≠ ⊤),
          MeasureTheory.lintegral_finsetSum]
        exact fun j _ => ((hM_meas j).nnnorm.coe_nnreal_ennreal).pow_const 2
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        exact LevyStochCalc.Brownian.Ito.itoIsometry (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j) t ht
          (h_meas i j) (h_progMeas i j) (h_sq i j)

/-- **Second moment of the jump component**, by the Itô–Lévy isometry. -/
theorem lintegral_sq_picardStep_jump_eq {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (h_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_progMeas : ∀ i : Fin n,
        Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (i : Fin n) {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i) t ht

/-- The extended norm of a square. -/
theorem enorm_sq_eq (x : ℝ) : ‖x ^ 2‖ₑ = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Second moment of a time-integral**, by Cauchy–Schwarz on `[0, t]`. -/
theorem lintegral_sq_setIntegral_le {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal t
        * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hinner_meas : Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  have hae : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    MeasureTheory.ae_lt_top hinner_meas hfin.ne
  have hpt : ∀ᵐ ω ∂P, (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    filter_upwards [hae] with ω hω
    have hslice : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
    -- `f ω` is `L²` on `[0, t]`
    have hL2 : MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) t)) := by
      refine (MeasureTheory.memLp_two_iff_integrable_sq hslice.aestronglyMeasurable).mpr ?_
      refine ⟨(hslice.pow_const 2).aestronglyMeasurable, ?_⟩
      rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => ?_)) hω
      exact enorm_sq_eq (f ω s)
    have hint : MeasureTheory.Integrable (f ω) (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      hL2.integrable (by norm_num)
    -- Cauchy–Schwarz against the constant `1`
    have hCS := integral_sq_le_mul_integral_sq_on_Icc (fun s => ‖f ω s‖) t ht
      (Filter.Eventually.of_forall fun _ => norm_nonneg _) hL2.norm
    have habs : |∫ s in Set.Icc (0 : ℝ) t, f ω s| ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
      MeasureTheory.abs_integral_le_integral_abs.trans_eq
        (MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun s => (Real.norm_eq_abs (f ω s)).symm))
    have hsq : ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ ^ 2
        = (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall fun s => by positivity)
        ((hslice.norm.pow_const 2).aestronglyMeasurable)]
      congr 1
      refine lintegral_congr fun s => ?_
      rw [← sq_coe_nnnorm_real ‖f ω s‖, nnnorm_norm]
    have hbound : (∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2
        ≤ t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal := by
      have hnn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖f ω s‖ :=
        MeasureTheory.integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun s => norm_nonneg (f ω s))
      rw [← hsq]
      refine le_trans ?_ hCS
      nlinarith [habs, abs_nonneg (∫ s in Set.Icc (0 : ℝ) t, f ω s),
        sq_abs (∫ s in Set.Icc (0 : ℝ) t, f ω s), hnn]
    calc (‖∫ s in Set.Icc (0 : ℝ) t, f ω s‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((∫ s in Set.Icc (0 : ℝ) t, f ω s) ^ 2) := sq_coe_nnnorm_real _
      _ ≤ ENNReal.ofReal
            (t * (∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume).toReal) :=
          ENNReal.ofReal_le_ofReal hbound
      _ = ENNReal.ofReal t * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
          rw [ENNReal.ofReal_mul ht, ENNReal.ofReal_toReal hω.ne]
  refine (lintegral_mono_ae hpt).trans ?_
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

/-- `‖a + b‖² ≤ 2‖a‖² + 2‖b‖²` for reals, in `ℝ≥0∞`. -/
theorem sq_nnnorm_add_le (a b : ℝ) :
    (‖a + b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by nlinarith [sq_nonneg (a - b)]
  calc (‖a + b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((a + b) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (2 * a ^ 2 + 2 * b ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat,
          ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real]

omit [MeasurableSpace E] in
/-- **Second moment of the drift component**, by Cauchy–Schwarz on `[0, t]`. -/
theorem lintegral_sq_picardStep_drift_le
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {t : ℝ} (ht : 0 ≤ t)
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
        + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
  have hunfold : ∀ ω : Ω, picardStep_drift coeffs X x₀ t ω i
      = x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := fun _ => rfl
  calc ∫⁻ ω, (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_congr fun ω => by rw [hunfold ω]
    _ ≤ ∫⁻ ω, (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2) ∂P :=
        lintegral_mono fun ω => sq_nnnorm_add_le _ _
    _ = 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * ∫⁻ ω, (‖∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [MeasureTheory.lintegral_add_left measurable_const, MeasureTheory.lintegral_const,
          measure_univ, mul_one,
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    _ ≤ 2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal t * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
        add_le_add le_rfl
          (mul_le_mul' le_rfl (lintegral_sq_setIntegral_le h_μ_meas ht hfin))

end LevyStochCalc.Ito.Picard
