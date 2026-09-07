/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardIntegrand
import LevyStochCalc.Probability.ProgressiveCadlag
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
/-- The Itô isometry at every nonnegative horizon, including `0`. -/
theorem itoIsometry_of_nonneg
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_lintegral_sq W ℱ hℱ H h_meas h_progMeas
    h_sq hT

/-- The Itô–Lévy isometry at every nonnegative horizon, including `0`. -/
theorem compensatedIsometry_of_nonneg {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas
      h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← LevyStochCalc.Poisson.Compensated.process_lintegral_sq' N ℱ hℱ φ h_meas h_progMeas
    h_sq hT]
  refine lintegral_congr_ae ?_
  filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ φ
    h_meas h_progMeas h_sq T] with ω hω
  rw [hω]

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
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
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
        exact itoIsometry_of_nonneg (W.W j) ℱ (hℱW j)
          (fun ω' s => coeffs.σ s (X s ω') i j)
          (h_meas i j) (h_progMeas i j) (h_sq i j) ht

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
    (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  compensatedIsometry_of_nonneg N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i) ht

/-- The extended norm of a square. -/
theorem enorm_sq_eq (x : ℝ) : ‖x ^ 2‖ₑ = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A function with finite energy on a bounded window is `L²` there. -/
theorem memLp_two_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {b : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MeasureTheory.MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  refine (MeasureTheory.memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ?_
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => enorm_sq_eq (f s))) hfin

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A function with finite energy on a bounded window is integrable there. -/
theorem integrableOn_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {b : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (memLp_two_of_lintegral_sq_lt_top hf hfin).integrable (by norm_num)

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
    have hL2 : MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) t)) :=
      memLp_two_of_lintegral_sq_lt_top hslice hω
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

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The time-integral of a jointly measurable process is measurable in the sample. -/
theorem measurable_setIntegral_slice {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) (t : ℝ) :
    Measurable fun ω => ∫ s in Set.Icc (0 : ℝ) t, f ω s := by
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (hf.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) t))).measurable

/-- `‖x + y + z‖² ≤ 3‖x‖² + 3‖y‖² + 3‖z‖²` for reals, in `ℝ≥0∞`. -/
theorem sq_nnnorm_add3_le (x y z : ℝ) :
    (‖x + y + z‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : (x + y + z) ^ 2 ≤ 3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2 := by
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (x - z)]
  calc (‖x + y + z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((x + y + z) ^ 2) := sq_coe_nnnorm_real _
    _ ≤ ENNReal.ofReal (3 * x ^ 2 + 3 * y ^ 2 + 3 * z ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 3 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖y‖₊ : ℝ≥0∞) ^ 2 + 3 * (‖z‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3), ENNReal.ofReal_ofNat,
          ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real, ← sq_coe_nnnorm_real]

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Enlarging the time window increases the doubly-integrated energy. -/
theorem lintegral_lintegral_Icc_mono {f : Ω → ℝ → ℝ≥0∞} {t T : ℝ} (h : t ≤ T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, f ω s ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P :=
  lintegral_mono fun _ =>
    lintegral_mono' (MeasureTheory.Measure.restrict_mono
      (Set.Icc_subset_Icc le_rfl h) le_rfl) le_rfl

omit [MeasurableSpace E] in
/-- Slice measurability of the drift component. -/
theorem measurable_picardStep_drift
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i)) (t : ℝ) :
    Measurable fun ω => picardStep_drift coeffs X x₀ t ω i :=
  (measurable_setIntegral_slice h_μ_meas t).const_add _

omit [MeasurableSpace E] in
/-- Slice measurability of the diffusion component. -/
theorem measurable_picardStep_diffusion
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
    (i : Fin n) (t : ℝ) :
    Measurable fun ω =>
      picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i := by
  have hcomp : ∀ j : Fin d, Measurable fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω' s => coeffs.σ s (X s ω') i j)
        (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) ℱ (hℱW j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_meas i j) (h_progMeas i j) (h_sq i j)
    exact (hMart.stronglyMeasurable t).measurable.mono (Filt.le t) le_rfl
  have hunfold : (fun ω => picardStep_diffusion W ℱ hℱW coeffs X h_meas h_progMeas h_sq t ω i)
      = fun ω => ∑ j : Fin d, LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω' s => coeffs.σ s (X s ω') i j)
        (h_meas i j) (h_progMeas i j) (h_sq i j) t ω := rfl
  rw [hunfold]
  exact Finset.measurable_sum _ fun j _ => hcomp j

/-- Slice measurability of the jump component. -/
theorem measurable_picardStep_jump {ν : MeasureTheory.Measure E}
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
    (i : Fin n) (t : ℝ) :
    Measurable fun ω => picardStep_jump N ℱ hℱN coeffs X h_meas h_progMeas h_sq t ω i :=
  ((LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN
    (fun ω s e => coeffs.γ s (X s ω) e i) (h_meas i) (h_progMeas i) (h_sq i)
      t).stronglyMeasurable).measurable.mono (ℱ.rightCont.le t) le_rfl

section Step

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- **Second moment of the Picard step at a time of `[0, T]`, bounded uniformly by data at the
horizon `T`.** -/
theorem lintegral_sq_picardStep_le
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∑ i, (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ i : Fin n,
          (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
              + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                  (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
            + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
            + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
                (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
  obtain ⟨ht0, htT⟩ := ht
  have hdr : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_drift coeffs X x₀ i (h_μ_meas i)
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hdf : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hjp : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    (((measurable_picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq i
      t).nnnorm).coe_nnreal_ennreal).pow_const 2
  -- pointwise three-term split
  have hpt : ∀ ω : Ω, ∑ i, (‖picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas
        h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ ∑ i : Fin n,
          (3 * (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2
            + 3 * (‖picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
                t ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine Finset.sum_le_sum fun i _ => ?_
    exact sq_nnnorm_add3_le _ _ _
  have hmeas2 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((hdr i).const_mul 3).add ((hdf i).const_mul 3)
  have hmeas3 : ∀ i : Fin n, Measurable fun ω =>
      3 * (‖picardStep_drift coeffs X x₀ t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2
        + 3 * (‖picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq
            t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (hmeas2 i).add ((hjp i).const_mul 3)
  refine (lintegral_mono hpt).trans ?_
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => hmeas3 i)]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [MeasureTheory.lintegral_add_left (hmeas2 i),
    MeasureTheory.lintegral_add_left ((hdr i).const_mul 3),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  have hμt : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_lintegral_Icc_mono htT) (hμT i)
  refine add_le_add (add_le_add (mul_le_mul' le_rfl ?_) (mul_le_mul' le_rfl ?_))
    (mul_le_mul' le_rfl ?_)
  · refine (lintegral_sq_picardStep_drift_le coeffs X x₀ i (h_μ_meas i) ht0 hμt).trans ?_
    exact add_le_add le_rfl (mul_le_mul' le_rfl
      (mul_le_mul' (ENNReal.ofReal_le_ofReal htT) (lintegral_lintegral_Icc_mono htT)))
  · refine (lintegral_sq_picardStep_diffusion_le W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas
      h_σ_sq i ht0).trans ?_
    exact mul_le_mul' le_rfl
      (Finset.sum_le_sum fun j _ => lintegral_lintegral_Icc_mono htT)
  · refine le_of_eq_of_le (lintegral_sq_picardStep_jump_eq N ℱ hℱN coeffs X h_γ_meas
      h_γ_progMeas h_γ_sq i ht0) ?_
    exact lintegral_lintegral_Icc_mono htT

/-- **The Picard step has finite Bielecki norm on `[0, T]`** — the `L²` output field that
`picardStepOnS2` takes as a hypothesis. -/
theorem bieleckiNorm_picardStep_lt_top
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    {T : ℝ}
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hσT : ∀ i : Fin n, ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤ := by
  have hKfin : (∑ i : Fin n,
      (3 * (2 * (‖x₀ i‖₊ : ℝ≥0∞) ^ 2
          + 2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        + 3 * ((d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 3 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)) < ⊤ := by
    refine ENNReal.sum_lt_top.mpr fun i _ => ?_
    refine ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨?_, ?_⟩, ?_⟩
    · refine ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
      · exact ENNReal.mul_lt_top (by simp) (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      · exact ENNReal.mul_lt_top (by simp)
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hμT i))
    · exact ENNReal.mul_lt_top (by simp) (ENNReal.mul_lt_top (by simp)
        (ENNReal.sum_lt_top.mpr fun j _ => hσT i j))
    · exact ENNReal.mul_lt_top (by simp) (hγT i)
  refine lt_of_le_of_lt (b := _ ^ ((1 : ℝ) / 2)) ?_
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKfin.ne)
  unfold bieleckiNorm
  refine iSup₂_le fun t ht => ?_
  rw [neg_zero, zero_mul, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  exact ENNReal.rpow_le_rpow
    (lintegral_sq_picardStep_le W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
      h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas ht hμT) (by norm_num)

end Step

omit [MeasurableSpace E] in
/-- **A càdlàg adapted modification of the Brownian Itô integral.** The `L²` integral is defined
separately at each time, so this is what supplies a path-regular representative. -/
theorem exists_cadlag_modification_itoIntegral
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : Probability.ProgressivelyMeasurable ℱ H)
    (h_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Y : ℝ → Ω → ℝ, MeasureTheory.Adapted ℱ.rightCont Y ∧
      (∀ t, Y t =ᵐ[P]
        LevyStochCalc.Brownian.Ito.stochasticIntegral W ℱ hℱ H h_meas h_progMeas h_sq t) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)) ∧
          ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L) :=
  LevyStochCalc.Martingale.exists_adapted_ae_cadlag_of_eLpNorm
    (LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H
      h_meas h_progMeas h_sq)
    (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eLpNorm_two_right_tendsto W ℱ hℱ H
      h_meas h_progMeas h_sq)
    (fun _ ht => LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_neg W ℱ hℱ H
      h_meas h_progMeas h_sq ht)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **The primitive of a locally integrable function is continuous.** The window `[0, t]` is
empty for `t < 0`, so the primitive is the constant `0` there and continuity at `0` glues. -/
theorem continuous_setIntegral_Icc_of_integrableOn {f : ℝ → ℝ}
    (h_int : ∀ b : ℝ, MeasureTheory.IntegrableOn f (Set.Icc (0 : ℝ) b) volume) :
    Continuous fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume := by
  classical
  set g : ℝ → ℝ := Set.indicator (Set.Ici (0 : ℝ)) f with hgdef
  have hgint : ∀ a b : ℝ, IntervalIntegrable g volume a b := by
    intro a b
    have hsub : Set.Ici (0 : ℝ) ∩ Set.uIoc a b ⊆ Set.Icc (0 : ℝ) (max a b) := by
      rintro x ⟨hx0, hx⟩
      exact ⟨hx0, hx.2⟩
    rw [intervalIntegrable_iff, MeasureTheory.IntegrableOn,
      MeasureTheory.integrable_indicator_iff measurableSet_Ici,
      MeasureTheory.IntegrableOn, MeasureTheory.Measure.restrict_restrict measurableSet_Ici]
    exact (h_int (max a b)).mono_set hsub
  have heq : (fun t => ∫ s in Set.Icc (0 : ℝ) t, f s ∂volume)
      = fun t => ∫ s in (0 : ℝ)..(max t 0), g s ∂volume := by
    funext t
    rcases le_or_gt 0 t with ht | ht
    · rw [max_eq_left ht, intervalIntegral.integral_of_le ht,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
      exact (Set.indicator_of_mem (Set.mem_Ici.mpr hx.1) f).symm
    · rw [max_eq_right ht.le, intervalIntegral.integral_same,
        Set.Icc_eq_empty (not_le.mpr ht), MeasureTheory.setIntegral_empty]
  rw [heq]
  exact (intervalIntegral.continuous_primitive hgint 0).comp
    (continuous_id.max continuous_const)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Almost every path of a process with locally finite energy is locally `L²`. -/
theorem ae_memLp_two_of_lintegral_sq {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ b : ℝ,
      MeasureTheory.MemLp (f ω) 2 (volume.restrict (Set.Icc (0 : ℝ) b)) := by
  have hstep : ∀ n : ℕ, ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1), (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
    intro n
    refine MeasureTheory.ae_lt_top ?_ (hfin ((n : ℝ) + 1) (by positivity)).ne
    exact (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  filter_upwards [MeasureTheory.ae_all_iff.mpr hstep] with ω hω b
  obtain ⟨n, hn⟩ := exists_nat_ge b
  have hsub : Set.Icc (0 : ℝ) b ⊆ Set.Icc (0 : ℝ) ((n : ℝ) + 1) :=
    Set.Icc_subset_Icc le_rfl (by linarith)
  have hslice : Measurable (f ω) := hf.comp (measurable_const.prodMk measurable_id)
  exact (memLp_two_of_lintegral_sq_lt_top hslice (hω n)).mono_measure
    (MeasureTheory.Measure.restrict_mono hsub le_rfl)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- Almost every path of a process with locally finite energy is locally integrable. -/
theorem ae_integrableOn_of_lintegral_sq {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f))
    (hfin : ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ b : ℝ, MeasureTheory.IntegrableOn (f ω) (Set.Icc (0 : ℝ) b) volume := by
  filter_upwards [ae_memLp_two_of_lintegral_sq hf hfin] with ω hω b
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) b)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  exact (hω b).integrable (by norm_num)

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Almost every drift path of the Picard step is continuous.** -/
theorem ae_continuous_picardStep_drift
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ) (i : Fin n)
    (h_μ_meas : Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, Continuous fun t => picardStep_drift coeffs X x₀ t ω i := by
  filter_upwards [ae_integrableOn_of_lintegral_sq h_μ_meas h_μ_sq] with ω hω
  have : (fun t => picardStep_drift coeffs X x₀ t ω i)
      = fun t => x₀ i + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i := rfl
  rw [this]
  exact continuous_const.add (continuous_setIntegral_Icc_of_integrableOn hω)

omit [MeasurableSpace E] in
/-- The Bielecki norm depends on the process only through its almost-everywhere class at each
time, so a modification has the same norm. -/
theorem bieleckiNorm_congr_ae (β T : ℝ) {Y Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t : ℝ, Y t =ᵐ[P] Z t) :
    bieleckiNorm (P := P) β T Y = bieleckiNorm (P := P) β T Z := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  have hinner : (∫⁻ ω, ∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [h t] with ω hω
    rw [hω]
  rw [hinner]

section Modification

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
variable (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
variable (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
variable (X : ℝ → Ω → (Fin n → ℝ))
variable (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
  Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
variable (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
  Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
variable (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- A càdlàg representative of the `(i, j)` Brownian integral along `X`. -/
noncomputable def sigmaMod (i : Fin n) (j : Fin d) : ℝ → Ω → ℝ :=
  Classical.choose (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j))

omit [MeasurableSpace E] in
theorem sigmaMod_adapted (i : Fin n) (j : Fin d) :
    MeasureTheory.Adapted ℱ.rightCont
      (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j) :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j))).1

omit [MeasurableSpace E] in
theorem sigmaMod_ae_eq (i : Fin n) (j : Fin d) (t : ℝ) :
    sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t
      =ᵐ[P] LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j) ℱ (hℱW j)
        (fun ω s => coeffs.σ s (X s ω) i j)
        (h_σ_meas i j) (h_σ_progMeas i j) (h_σ_sq i j) t :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j)
      (h_σ_sq i j))).2.1 t

omit [MeasurableSpace E] in
theorem sigmaMod_cadlag (i : Fin n) (j : Fin d) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Iio t)) (nhds L) :=
  (Classical.choose_spec (exists_cadlag_modification_itoIntegral (W.W j) ℱ (hℱW j)
    (fun ω s => coeffs.σ s (X s ω) i j) (h_σ_meas i j) (h_σ_progMeas i j)
      (h_σ_sq i j))).2.2

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
variable (x₀ : Fin n → ℝ)
variable (h_γ_meas : ∀ i : Fin n,
  Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
variable (h_γ_progMeas : ∀ i : Fin n,
  Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
variable (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- **The Picard step with a càdlàg representative of its Brownian component.**

`picardStep` is an `L²` limit taken separately at each time, so it is not jointly measurable as
it stands; this replaces its Brownian component by the càdlàg modification of C0d-2, which
changes it only on a null set at each time. -/
noncomputable def picardStepMod : ℝ → Ω → (Fin n → ℝ) :=
  fun t ω i => picardStep_drift coeffs X x₀ t ω i
    + (∑ j : Fin d, sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)
    + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i

/-- The modified step is a modification of the Picard step. -/
theorem picardStepMod_ae_eq (t : ℝ) :
    picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t
      =ᵐ[P] picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t := by
  have hall : ∀ᵐ ω ∂P, ∀ p : Fin n × Fin d,
      sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq p.1 p.2 t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W p.2) ℱ (hℱW p.2)
            (fun ω' s => coeffs.σ s (X s ω') p.1 p.2)
            (h_σ_meas p.1 p.2) (h_σ_progMeas p.1 p.2) (h_σ_sq p.1 p.2) t ω :=
    MeasureTheory.ae_all_iff.mpr fun p => sigmaMod_ae_eq W ℱ hℱW coeffs X h_σ_meas
      h_σ_progMeas h_σ_sq p.1 p.2 t
  filter_upwards [hall] with ω hω
  funext i
  change picardStep_drift coeffs X x₀ t ω i
      + (∑ j : Fin d, sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)
      + picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i
    = _
  simp only [picardStep, Pi.add_apply, picardStep_diffusion,
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral]
  exact congrArg₂ (· + ·)
    (congrArg₂ (· + ·) rfl (Finset.sum_congr rfl fun j _ => hω (i, j))) rfl

/-- The modified step has the same Bielecki norm as the Picard step. -/
theorem bieleckiNorm_picardStepMod (β T : ℝ) :
    bieleckiNorm (P := P) β T
        (picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
          h_γ_meas h_γ_progMeas h_γ_sq)
      = bieleckiNorm (P := P) β T
        (fun t ω => picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
          h_γ_meas h_γ_progMeas h_γ_sq t ω) :=
  bieleckiNorm_congr_ae β T fun t => picardStepMod_ae_eq W ℱ hℱW coeffs X h_σ_meas
    h_σ_progMeas h_σ_sq N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t

/-- The modified step is adapted to the right-continuous filtration. -/
theorem picardStepMod_adapted
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (X s ω) i))
    (i : Fin n) (t : ℝ) :
    Measurable[ℱ.rightCont t] fun ω =>
      picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
  have hdrift : Measurable[ℱ.rightCont t] fun ω => picardStep_drift coeffs X x₀ t ω i :=
    ((LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc
      (h_μ_progMeas i) t).mono (ℱ.le_rightCont t) le_rfl).const_add _
  have hσ : ∀ j : Fin d, Measurable[ℱ.rightCont t] fun ω =>
      sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω :=
    fun j => sigmaMod_adapted W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t
  have hγ : Measurable[ℱ.rightCont t] fun ω =>
      picardStep_jump N ℱ hℱN coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω i :=
    (LevyStochCalc.Poisson.Compensated.stochasticIntegral_adapted N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i)
        (h_γ_sq i) t).stronglyMeasurable.measurable
  exact (hdrift.add (Finset.measurable_sum _ fun j _ => hσ j)).add hγ

/-- Almost every path of the modified step is càdlàg. -/
theorem picardStepMod_cadlag
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq s ω i)
          (nhdsWithin t (Set.Ioi t))
          (nhds (picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t ω i)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq
            N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq s ω i)
          (nhdsWithin t (Set.Iio t)) (nhds L) := by
  have hσall : ∀ᵐ ω ∂P, ∀ j : Fin d, ∀ t : ℝ,
      Filter.Tendsto (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j t ω)) ∧
        ∃ L : ℝ, Filter.Tendsto
          (fun s => sigmaMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j s ω)
          (nhdsWithin t (Set.Iio t)) (nhds L) :=
    MeasureTheory.ae_all_iff.mpr fun j =>
      sigmaMod_cadlag W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq i j
  filter_upwards [ae_continuous_picardStep_drift coeffs X x₀ i (h_μ_meas i) (h_μ_sq i),
    hσall,
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N ℱ hℱN
      (fun ω s e => coeffs.γ s (X s ω) e i) (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i)]
    with ω hdr hσ hγ t
  have hright := ((hdr.continuousAt (x := t)).continuousWithinAt (s := Set.Ioi t)).tendsto
  refine ⟨((hright.add (tendsto_finsetSum _ fun j _ => (hσ j t).1)).add (hγ t).1), ?_⟩
  choose L hL using fun j : Fin d => (hσ j t).2
  obtain ⟨Lγ, hLγ⟩ := (hγ t).2
  refine ⟨picardStep_drift coeffs X x₀ t ω i + (∑ j : Fin d, L j) + Lγ, ?_⟩
  exact ((((hdr.continuousAt (x := t)).continuousWithinAt (s := Set.Iio t)).tendsto.add
    (tendsto_finsetSum _ fun j _ => hL j)).add hLγ)

/-- **The Picard step lands in the process space.**

Under the usual conditions — a right-continuous filtration whose `ℱ 0` contains the `P`-null
sets — the Picard step has a modification that is a member of the Bielecki process space, which
is what makes `picardStepOnS2` a self-map. -/
theorem exists_sBoundedProcess_picardStep [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (h_μ_meas : ∀ i : Fin n,
      Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_progMeas : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.μ s (X s ω) i))
    (h_μ_sq : ∀ i : Fin n, ∀ b : ℝ, 0 < b →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ}
    (hμT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hσT : ∀ i : Fin n, ∀ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγT : ∀ i : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ Y : SBoundedProcess (n := n) P ℱ T, ∀ t : ℝ,
      Y.X t =ᵐ[P] picardStep W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas h_σ_sq
        h_γ_meas h_γ_progMeas h_γ_sq t := by
  classical
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hadapt : ∀ (i : Fin n) (t : ℝ), Measurable[ℱ t] fun ω =>
      picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t ω i := by
    intro i t
    have h := picardStepMod_adapted W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
      h_γ_meas h_γ_progMeas h_γ_sq h_μ_progMeas i t
    rwa [hrc] at h
  have hex : ∀ i : Fin n, ∃ Z : ℝ → Ω → ℝ, (∀ t : ℝ, Measurable[ℱ t] (Z t)) ∧
      (∀ t : ℝ, Z t =ᵐ[P] fun ω =>
        picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
          h_γ_meas h_γ_progMeas h_γ_sq t ω i) ∧
      (∀ (ω : Ω) (t : ℝ),
        Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Z t ω))) ∧
      ∀ (ω : Ω) (t : ℝ), ∃ L : ℝ,
        Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Iio t)) (nhds L) := fun i =>
    LevyStochCalc.Probability.exists_everywhere_cadlag_modification hℱ0 hnull (hadapt i)
      (picardStepMod_cadlag W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas h_μ_sq i)
  choose Z hZmeas hZae hZright hZleft using hex
  have hstepae : ∀ t : ℝ, (fun ω i => Z i t ω) =ᵐ[P]
      picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq t := by
    intro t
    filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n => hZae i t] with ω hω
    exact funext fun i => hω i
  refine ⟨{
    X := fun t ω i => Z i t ω
    measurable_path := measurable_pi_lambda _ fun i =>
      LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous (hZmeas i)
        (hZright i)
    adapted := fun i =>
      LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous (hZmeas i)
        (hZright i)
    cadlag_paths := Filter.Eventually.of_forall fun ω t =>
      ⟨tendsto_pi_nhds.mpr fun i => hZright i ω t, fun i => hZleft i ω t⟩
    sup_L2 := ?_ }, ?_⟩
  · rw [bieleckiNorm_congr_ae 0 T hstepae,
      bieleckiNorm_picardStepMod W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas h_σ_sq N hℱN x₀
        h_γ_meas h_γ_progMeas h_γ_sq 0 T]
    exact bieleckiNorm_picardStep_lt_top W N ℱ hℱW hℱN coeffs X x₀ h_σ_meas h_σ_progMeas
      h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq h_μ_meas hμT hσT hγT
  · intro t
    exact (hstepae t).trans (picardStepMod_ae_eq W ℱ hℱW coeffs X h_σ_meas h_σ_progMeas
      h_σ_sq N hℱN x₀ h_γ_meas h_γ_progMeas h_γ_sq t)

end Modification

section SelfMap

variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]

/-- **The Picard self-map on the process space.**

Every hypothesis `picardStep` and `SBoundedProcess` ask for is supplied from `IsRegular` and
`IsLipschitz` along the frozen process, so this is a genuine map from the space to itself under
the usual conditions. -/
noncomputable def picardSelfMap
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    (Y : SBoundedProcess (n := n) P ℱ T) : SBoundedProcess (n := n) P ℱ T :=
  Classical.choose (exists_sBoundedProcess_picardStep W ℱ hℱW coeffs Y.stop.X
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    N hℱN x₀
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    hℱ0 hnull
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (fun i => progressivelyMeasurable_mu_stop coeffs hReg Y i)
    (fun i _ hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun i => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hT)
    (fun i j => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT)
    (fun i => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT))

/-- The self-map's path is a modification of the Picard step along the frozen process. -/
theorem picardSelfMap_ae_eq
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {T : ℝ} (hT : 0 < T)
    (Y : SBoundedProcess (n := n) P ℱ T) (t : ℝ) :
    (picardSelfMap W N ℱ hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t
      =ᵐ[P] picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t :=
  Classical.choose_spec (exists_sBoundedProcess_picardStep W ℱ hℱW coeffs Y.stop.X
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    N hℱN x₀
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    hℱ0 hnull
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (fun i => progressivelyMeasurable_mu_stop coeffs hReg Y i)
    (fun i _ hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun i => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hT)
    (fun i j => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT)
    (fun i => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT)) t

end SelfMap

section Weighting

omit [MeasurableSpace E] in
/-- The second moment at a single time of `[0, T]`, weighted back up from the Bielecki norm. -/
theorem lintegral_sq_le_bieleckiNorm_sq_weighted (β T : ℝ) (Z : ℝ → Ω → (Fin n → ℝ))
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (Real.exp (2 * β * s)) * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
  set A : ℝ≥0∞ := ∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P with hA
  have hle : ENNReal.ofReal (Real.exp (-β * s)) * A ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z := by
    unfold bieleckiNorm
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) s hs
  have hmul : A ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (β * s)) * bieleckiNorm (P := P) β T Z := by
    refine le_trans (le_of_eq ?_) (mul_le_mul' le_rfl hle)
    rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    simp
  calc A = (A ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) := by
        rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ (ENNReal.ofReal (Real.exp (β * s)) * bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) :=
        pow_le_pow_left' hmul 2
    _ = ENNReal.ofReal (Real.exp (2 * β * s)) * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
        rw [mul_pow, ← ENNReal.ofReal_pow (Real.exp_nonneg _), ← Real.exp_nat_mul]
        ring_nf

omit [MeasurableSpace E] in
/-- **The Bielecki weighting step.** The doubly-integrated energy over `[0, t]` is bounded by
`e^{2βt}/(2β)` times the squared Bielecki norm; the factor `1/(2β)` is what makes the Picard
rate small for large `β`. -/
theorem lintegral_lintegral_sq_le_bieleckiNorm_sq {β : ℝ} (hβ : 0 < β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P
      ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
          * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  -- the exponential window integral
  have hexp : ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s)) ∂volume
      ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β)) := by
    have hcont : Continuous fun s : ℝ => Real.exp (2 * β * s) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have hint : MeasureTheory.IntegrableOn (fun s : ℝ => Real.exp (2 * β * s))
        (Set.Icc (0 : ℝ) t) volume :=
      (hcont.continuousOn).integrableOn_compact isCompact_Icc
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun s => Real.exp_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hIcc : (∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) ∂volume)
        = ∫ s in (0 : ℝ)..t, Real.exp (2 * β * s) := by
      rw [intervalIntegral.integral_of_le ht.1,
        MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc]
    rw [hIcc, intervalIntegral.integral_comp_mul_left Real.exp (ne_of_gt hβ2),
      integral_exp, mul_zero, Real.exp_zero, smul_eq_mul]
    rw [div_eq_inv_mul]
    have hexp_pos : (0 : ℝ) < Real.exp (2 * β * t) := Real.exp_pos _
    have hinv : (0 : ℝ) < (2 * β)⁻¹ := by positivity
    nlinarith [hinv, hexp_pos]
  by_cases hB : bieleckiNorm (P := P) β T Z = ⊤
  · rw [hB]
    have hpos : ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β)) ≠ 0 := by
      simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      positivity
    rw [ENNReal.top_pow (by norm_num), ENNReal.mul_top hpos]
    exact le_top
  · have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) :=
      Finset.measurable_sum _ fun i _ =>
        ((((measurable_pi_apply i).comp hZ)).nnnorm.coe_nnreal_ennreal).pow_const 2
    rw [MeasureTheory.lintegral_lintegral_swap (μ := P)
      (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      (f := fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) hjoint.aemeasurable]
    calc ∫⁻ s in Set.Icc (0 : ℝ) t, (∫⁻ ω, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) ∂volume :=
          MeasureTheory.setLIntegral_mono' measurableSet_Icc fun s hs =>
            lintegral_sq_le_bieleckiNorm_sq_weighted β T Z ⟨hs.1, hs.2.trans ht.2⟩
      _ = (∫⁻ s in Set.Icc (0 : ℝ) t, ENNReal.ofReal (Real.exp (2 * β * s)) ∂volume)
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) :=
          MeasureTheory.lintegral_mul_const' _ _ (by simp [hB, ENNReal.pow_eq_top_iff])
      _ ≤ ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := mul_le_mul' hexp le_rfl

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- A Bochner integral of a nonnegative function is below the corresponding lower integral, with
no integrability hypothesis: when the integrand is not integrable the Bochner integral is `0`. -/
theorem ofReal_setIntegral_le_lintegral {f : ℝ → ℝ} (hf : ∀ x, 0 ≤ f x) (s : Set ℝ) :
    ENNReal.ofReal (∫ x in s, f x ∂volume) ≤ ∫⁻ x in s, ENNReal.ofReal (f x) ∂volume := by
  have h1 : ENNReal.ofReal (∫ x in s, f x ∂volume) ≤ ‖∫ x in s, f x ∂volume‖ₑ := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  refine h1.trans ((MeasureTheory.enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_))
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf x)]

omit [MeasurableSpace Ω] [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The window energy in the supremum norm is below the window energy in coordinates. -/
theorem lintegral_window_norm_le_sum {Z : ℝ → Ω → (Fin n → ℝ)} (t : ℝ) (ω : Ω) :
    ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖Z s ω‖ ^ 2 ∂volume)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume := by
  refine (ofReal_setIntegral_le_lintegral (fun x => by positivity) _).trans ?_
  exact lintegral_mono fun s => ofReal_sq_norm_le_sum (Z s ω)

omit [MeasurableSpace E] in
/-- **From a per-time Grönwall estimate to a Bielecki bound.** If the second moment of `U` at
each time of `[0, T]` is at most `C` times the window energy of `Z`, then the Bielecki norm of
`U` is at most `√(C / 2β)` times that of `Z`. The weight cancels exactly, which is why the
constant carries the `1/(2β)` that makes the Picard map a contraction for large `β`. -/
theorem bieleckiNorm_le_of_perTime {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z := by
  have hβ2 : (0 : ℝ) < 2 * β := by linarith
  refine iSup₂_le fun t ht => ?_
  have hcongr : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    exact Finset.sum_congr rfl fun i _ => sq_coe_nnnorm_real (U t ω i)
  have hA : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ ENNReal.ofReal (C / (2 * β)) * ENNReal.ofReal (Real.exp (2 * β * t))
          * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
    calc (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P := hcongr
      _ ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P := hbd t ht
      _ ≤ ENNReal.ofReal C * (ENNReal.ofReal (Real.exp (2 * β * t) / (2 * β))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ)) :=
          mul_le_mul' le_rfl (lintegral_lintegral_sq_le_bieleckiNorm_sq hβ T Z hZ ht)
      _ = ENNReal.ofReal (C / (2 * β)) * ENNReal.ofReal (Real.exp (2 * β * t))
            * (bieleckiNorm (P := P) β T Z) ^ (2 : ℕ) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hC,
            ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ C / (2 * β))]
          congr 2
          field_simp
  have hsqrt : (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * ENNReal.ofReal (Real.exp (β * t))
          * bieleckiNorm (P := P) β T Z := by
    refine le_trans (ENNReal.rpow_le_rpow hA (by norm_num)) (le_of_eq ?_)
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    congr 1
    · congr 1
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _), ← Real.exp_mul,
        show 2 * β * t * ((1 : ℝ) / 2) = β * t by ring]
    · rw [← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
      norm_num
  calc ENNReal.ofReal (Real.exp (-β * t))
        * (∫⁻ ω, ∑ i, (‖U t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ ENNReal.ofReal (Real.exp (-β * t))
          * ((ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
            * ENNReal.ofReal (Real.exp (β * t)) * bieleckiNorm (P := P) β T Z) :=
        mul_le_mul' le_rfl hsqrt
    _ = (ENNReal.ofReal (Real.exp (-β * t)) * ENNReal.ofReal (Real.exp (β * t)))
          * ((ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
            * bieleckiNorm (P := P) β T Z) := by ring
    _ = (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2)
          * bieleckiNorm (P := P) β T Z := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- The supremum norm is dominated by the coordinate sum, in `ℝ≥0∞`. -/
theorem sq_coe_nnnorm_le_sum (v : Fin n → ℝ) :
    (‖v‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ i, (‖v i‖₊ : ℝ≥0∞) ^ 2 :=
  (sq_coe_nnnorm v).le.trans (ofReal_sq_norm_le_sum v)

omit [MeasurableSpace E] in
/-- `bieleckiNorm_le_of_perTime` with the window energy measured in the supremum norm, which is
the form the per-component difference estimates of `Ito/Picard.lean` produce. -/
theorem bieleckiNorm_le_of_perTime_sup {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖Z s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z :=
  bieleckiNorm_le_of_perTime hβ hC U Z hZ fun t ht =>
    (hbd t ht).trans (mul_le_mul' le_rfl
      (lintegral_mono fun ω => lintegral_mono fun s => sq_coe_nnnorm_le_sum (Z s ω)))

omit [MeasurableSpace E] in
/-- `bieleckiNorm_le_of_perTime` with the window energy as a Bochner integral. -/
theorem bieleckiNorm_le_of_perTime_bochner {β : ℝ} (hβ : 0 < β) {T C : ℝ} (hC : 0 ≤ C)
    (U Z : ℝ → Ω → (Fin n → ℝ))
    (hZ : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Z s ω))
    (hbd : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i, (U t ω i) ^ 2) ∂P
        ≤ ENNReal.ofReal C
            * ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖Z s ω‖ ^ 2 ∂volume) ∂P) :
    bieleckiNorm (P := P) β T U
      ≤ (ENNReal.ofReal (C / (2 * β))) ^ ((1 : ℝ) / 2) * bieleckiNorm (P := P) β T Z :=
  bieleckiNorm_le_of_perTime hβ hC U Z hZ fun t ht =>
    (hbd t ht).trans (mul_le_mul' le_rfl
      (lintegral_mono fun ω => lintegral_window_norm_le_sum t ω))

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **The drift half of the per-time contraction estimate.** The per-component bound of
`picardStep_drift_diff_lipschitz_sq_componentwise` needs four integrability facts about the
path; local finiteness of the energies supplies all of them off one null set. -/
theorem ae_drift_diff_sq_bound
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ (n : ℝ) * L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume := by
  have hXYsq' : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(‖X s ω - Y s ω‖ : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro b hb
    refine lt_of_le_of_lt (le_of_eq ?_) (hXYsq b hb)
    exact lintegral_congr fun ω => lintegral_congr fun s => by rw [nnnorm_norm]
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
      ae_integrableOn_of_lintegral_sq (hμX i) (hμXsq i),
    MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
      ae_integrableOn_of_lintegral_sq (hμY i) (hμYsq i),
    ae_integrableOn_of_lintegral_sq hXYm hXYsq',
    ae_memLp_two_of_lintegral_sq hXYm hXYsq'] with ω hX hY hXY hXYL2
  calc ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ ∑ _i : Fin n, L_μ ^ 2 * t
          * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume :=
        Finset.sum_le_sum fun i _ =>
          picardStep_drift_diff_lipschitz_sq_componentwise coeffs hL_μ_nn h_μ_lip X Y x₀ t ht
            ω i (hX i t) (hY i t) (hXY t) (hXYL2 t)
    _ = (n : ℝ) * L_μ ^ 2 * t
          * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 ∂volume := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

omit [MeasurableSpace E] in
/-- **The drift half of the per-time contraction estimate, in lower-integral form.**
`picardStep_drift_diff_lintegral_sq_bound` with both of its almost-everywhere hypotheses
discharged. -/
theorem drift_diff_lintegral_sq_bound
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (x₀ : Fin n → ℝ)
    (hμX : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμY : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i))
    (hXYm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X s ω - Y s ω‖))
    (hμXsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hμYsq : ∀ i : Fin n, ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hXYsq : ∀ b : ℝ, 0 < b → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_drift (E := E) coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t)
          * ∫⁻ ω, ENNReal.ofReal
              (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
  picardStep_drift_diff_lintegral_sq_bound P coeffs hL_μ_nn h_μ_lip X Y x₀ t ht
    (ae_drift_diff_sq_bound coeffs hL_μ_nn h_μ_lip X Y x₀ hμX hμY hXYm hμXsq hμYsq hXYsq ht)
    (Filter.Eventually.of_forall fun _ =>
      MeasureTheory.integral_nonneg_of_ae (Filter.Eventually.of_forall fun _ => by positivity))

omit [MeasurableSpace E] in
/-- **The diffusion third of the per-time contraction estimate.** The per-component bound of
`picardStep_diffusion_diff_lipschitz_sq_componentwise`, summed over the `n` coordinates. -/
theorem diffusion_diff_lintegral_sq_bound
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_σ : ℝ} (hL_σ_nn : 0 ≤ L_σ)
    (h_σ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin d, (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
        ≤ L_σ ^ 2 * ‖x₁ - x₂‖ ^ 2)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (X s ω) i j))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Probability.ProgressivelyMeasurable ℱ (fun ω s => coeffs.σ s (Y s ω) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L_σ ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hmeas : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
        - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
        : ℝ≥0∞) ^ 2 := fun i =>
    ((((measurable_picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X i
      t).sub (measurable_picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y
        h_σ_sq_Y i t)).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeas i]
  calc ∑ i : Fin n, ∫⁻ ω,
        (‖picardStep_diffusion W ℱ hℱW coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω i
          - picardStep_diffusion W ℱ hℱW coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ _i : Fin n, ENNReal.ofReal ((d : ℝ) * L_σ ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        Finset.sum_le_sum fun i _ =>
          picardStep_diffusion_diff_lipschitz_sq_componentwise W ℱ hℱW coeffs hL_σ_nn h_σ_lip
            X Y i h_σ_meas_X h_σ_meas_Y h_σ_progMeas_X h_σ_progMeas_Y h_σ_sq_X h_σ_sq_Y t ht
    _ = ENNReal.ofReal ((n : ℝ) * ((d : ℝ) * L_σ ^ 2))
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ← mul_assoc]
        congr 2
        simp

omit [MeasurableSpace Ω] [MeasureTheory.IsProbabilityMeasure P] in
/-- The `γ` clause of `IsLipschitz`, read on a single coordinate along two processes. This is
where the `ℝ≥0∞` form of the clause is used: the `.toReal` form it replaced would give nothing
when the jump energy is infinite. -/
theorem gamma_lip_componentwise {ν : MeasureTheory.Measure E}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ)) (i : Fin n) (s : ℝ) (ω : Ω) :
    ∫⁻ e, (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal (L ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 := by
  calc ∫⁻ e, (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ∫⁻ e, (‖coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
        refine lintegral_mono fun e => ?_
        have hco : |coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i|
            ≤ ‖coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e‖ := by
          simpa [Real.norm_eq_abs, Pi.sub_apply] using
            norm_le_pi_norm (coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e) i
        rw [sq_coe_nnnorm_real, sq_coe_nnnorm]
        refine ENNReal.ofReal_le_ofReal ?_
        nlinarith [hco, abs_nonneg (coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i),
          sq_abs (coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i),
          norm_nonneg (coeffs.γ s (X s ω) e - coeffs.γ s (Y s ω) e)]
    _ ≤ ENNReal.ofReal (L ^ 2 * ‖X s ω - Y s ω‖ ^ 2) := hLip.2.2.2 s (X s ω) (Y s ω)
    _ = ENNReal.ofReal (L ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul (sq_nonneg L), sq_coe_nnnorm]

/-- **The jump third of the per-time contraction estimate.** The per-component bound of
`picardStep_jump_diff_lipschitz_sq_componentwise`, summed over the `n` coordinates. -/
theorem jump_diff_lintegral_sq_bound {ν : MeasureTheory.Measure E}
    [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (hX_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (X s ω) e i))
    (hX_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hY_meas : ∀ i : Fin n,
      Measurable (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hY_progMeas : ∀ i : Fin n,
      Probability.MarkedProgressivelyMeasurable ℱ (fun ω s e => coeffs.γ s (Y s ω) e i))
    (hY_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, ∑ i : Fin n,
        (‖picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
          - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hmeas : ∀ i : Fin n, Measurable fun ω =>
      (‖picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
        - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i =>
      ((((measurable_picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq i t).sub
        (measurable_picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq i
          t)).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_finsetSum _ fun i _ => hmeas i]
  calc ∑ i : Fin n, ∫⁻ ω,
        (‖picardStep_jump N ℱ hℱN coeffs X hX_meas hX_progMeas hX_sq t ω i
          - picardStep_jump N ℱ hℱN coeffs Y hY_meas hY_progMeas hY_sq t ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ _i : Fin n, ENNReal.ofReal (L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        Finset.sum_le_sum fun i _ =>
          picardStep_jump_diff_lipschitz_sq_componentwise N ℱ hℱN coeffs hLip.1 X Y i
            (gamma_lip_componentwise coeffs hLip X Y i)
            hX_meas hX_progMeas hX_sq hY_meas hY_progMeas hY_sq t ht
    _ = ENNReal.ofReal ((n : ℝ) * L ^ 2)
          * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg n), ← mul_assoc]
        congr 2
        simp

omit [MeasurableSpace E] [MeasureTheory.IsProbabilityMeasure P] in
/-- **Combining three per-time bounds with a common right-hand side.** For a process that splits
as a sum of three, `‖a + b + c‖² ≤ 3(‖a‖² + ‖b‖² + ‖c‖²)` turns three separate second-moment
bounds into one, with the constants added and tripled. -/
theorem lintegral_sq_sum3_le {U₁ U₂ U₃ : Ω → (Fin n → ℝ)} {c₁ c₂ c₃ R : ℝ≥0∞}
    (hm₁ : ∀ i : Fin n, Measurable fun ω => (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₂ : ∀ i : Fin n, Measurable fun ω => (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
    (hm₃ : ∀ i : Fin n, Measurable fun ω => (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2)
    (h₁ : ∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₁ * R)
    (h₂ : ∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₂ * R)
    (h₃ : ∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ c₃ * R) :
    ∫⁻ ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ 3 * (c₁ + c₂ + c₃) * R := by
  have hM₁ : Measurable fun ω => ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₁ i
  have hM₂ : Measurable fun ω => ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₂ i
  have hM₃ : Measurable fun ω => ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hm₃ i
  have hsum : ∀ ω : Ω, ∑ i, (‖U₁ ω i + U₂ ω i + U₃ ω i‖₊ : ℝ≥0∞) ^ 2
      ≤ 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2)
        + 3 * (∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω
    refine le_trans (Finset.sum_le_sum fun i _ => sq_nnnorm_add3_le _ _ _) (le_of_eq ?_)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum,
      Finset.mul_sum]
  have hM1' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₁.const_mul 3
  have hM2' : Measurable fun ω : Ω => 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM₂.const_mul 3
  have hM12 : Measurable fun ω : Ω =>
      3 * (∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2) + 3 * (∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2) := hM1'.add hM2'
  refine (lintegral_mono hsum).trans ?_
  rw [MeasureTheory.lintegral_add_left hM12,
    MeasureTheory.lintegral_add_left hM1',
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤),
    MeasureTheory.lintegral_const_mul' _ _ (by simp : (3 : ℝ≥0∞) ≠ ⊤)]
  calc 3 * (∫⁻ ω, ∑ i, (‖U₁ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₂ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + 3 * (∫⁻ ω, ∑ i, (‖U₃ ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      ≤ 3 * (c₁ * R) + 3 * (c₂ * R) + 3 * (c₃ * R) :=
        add_le_add (add_le_add (mul_le_mul' le_rfl h₁) (mul_le_mul' le_rfl h₂))
          (mul_le_mul' le_rfl h₃)
    _ = 3 * (c₁ + c₂ + c₃) * R := by ring

end Weighting

end LevyStochCalc.Ito.Picard
