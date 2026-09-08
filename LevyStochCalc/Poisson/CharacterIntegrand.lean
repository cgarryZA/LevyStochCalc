/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.SimpleCharacter

/-!
# The predictable integrand of the jump chain rule

For a simple integrand carried by a window of finite mark measure the integrand of the jump chain
rule has an exact predictable form: the strictly-past window sum is replaced by its predictable
representative and the deterministic factors are predictable because they are carried by the
window. The integrand is bounded by twice the indicator of the window, so its real and imaginary
parts are admissible for the compensated integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Integrand

variable (N : PoissonRandomMeasure P ν)

/-- The integrand of the jump chain rule, in its predictable form. -/
noncomputable def charIntegrand (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℂ :=
  (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) : ℝ) : ℂ) *
    (Complex.exp (Complex.I * (predStrict N w Bfam A T ω s e : ℂ))
      * (Complex.exp (Complex.I * (simpleMark w Bfam (s, e) : ℂ)) - 1))

/-- The real part of the chain rule's integrand. -/
noncomputable def charRe (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ := (charIntegrand N w Bfam A T ω s e).re

/-- The imaginary part of the chain rule's integrand. -/
noncomputable def charIm (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ := (charIntegrand N w Bfam A T ω s e).im

theorem markedPredictable_charIntegrand {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Probability.MarkedPredictable ℱ ν (charIntegrand N w Bfam A T) := by
  classical
  have hind : Probability.MarkedPredictable ℱ ν
      fun (_ : Ω) (s : ℝ) (e : E) => (⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) :=
    Probability.markedPredictable_of_measurable_window hA hAν
      (measurable_const.indicator (MeasurableSet.iUnion hBm))
      (fun p hp => Set.indicator_of_notMem
        (fun hmem => hp (Set.iUnion_subset hBsub hmem)) _)
  have hsim : Probability.MarkedPredictable ℱ ν
      fun (_ : Ω) (s : ℝ) (e : E) => simpleMark w Bfam (s, e) :=
    Probability.markedPredictable_of_measurable_window hA hAν (measurable_simpleMark w hBm)
      (fun p hp => simpleMark_eq_zero w hBsub hp)
  have hpre := markedPredictable_predStrict N hℱ w hBm hA hAν T
  change Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (p.2.1, p.2.2) : ℝ) : ℂ) *
      (Complex.exp (Complex.I * (predStrict N w Bfam A T p.1 p.2.1 p.2.2 : ℂ))
        * (Complex.exp (Complex.I * (simpleMark w Bfam (p.2.1, p.2.2) : ℂ)) - 1))
  refine Measurable.mul (Complex.measurable_ofReal.comp hind) (Measurable.mul ?_ ?_)
  · exact Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hpre).const_mul Complex.I)
  · exact (Complex.measurable_exp.comp
      ((Complex.measurable_ofReal.comp hsim).const_mul Complex.I)).sub measurable_const

theorem markedPredictable_charRe {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Probability.MarkedPredictable ℱ ν (charRe N w Bfam A T) :=
  Complex.measurable_re.comp (markedPredictable_charIntegrand N hℱ w hBm hA hAν hBsub)

theorem markedPredictable_charIm {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Probability.MarkedPredictable ℱ ν (charIm N w Bfam A T) :=
  Complex.measurable_im.comp (markedPredictable_charIntegrand N hℱ w hBm hA hAν hBsub)

theorem charIntegrand_eq_zero (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) {s : ℝ} {e : E}
    (he : (s, e) ∉ Set.Ioc (0 : ℝ) T ×ˢ A) : charIntegrand N w Bfam A T ω s e = 0 := by
  rw [charIntegrand, Set.indicator_of_notMem (fun hmem => he (Set.iUnion_subset hBsub hmem))]
  simp

theorem norm_charIntegrand_le (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ‖charIntegrand N w Bfam A T ω s e‖ ≤ 2 := by
  classical
  rw [charIntegrand, norm_mul, norm_mul]
  have hind : ‖(((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases hmem : ((s, e) : ℝ × E) ∈ ⋃ j, Bfam j
    · rw [Set.indicator_of_mem hmem]
      norm_num
    · rw [Set.indicator_of_notMem hmem]
      norm_num
  have hexp : ‖Complex.exp (Complex.I * (predStrict N w Bfam A T ω s e : ℂ))‖ = 1 := by
    rw [mul_comm]
    exact Complex.norm_exp_ofReal_mul_I _
  have hdiff : ‖Complex.exp (Complex.I * (simpleMark w Bfam (s, e) : ℂ)) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]
    norm_num
  rw [hexp, one_mul]
  nlinarith [norm_nonneg (((⋃ j, Bfam j).indicator (fun _ => (1 : ℝ)) (s, e) : ℝ) : ℂ),
    norm_nonneg (Complex.exp (Complex.I * (simpleMark w Bfam (s, e) : ℂ)) - 1)]


theorem charRe_eq_zero (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) {s : ℝ} {e : E}
    (he : (s, e) ∉ Set.Ioc (0 : ℝ) T ×ˢ A) : charRe N w Bfam A T ω s e = 0 := by
  rw [charRe, charIntegrand_eq_zero N w hBsub ω he, Complex.zero_re]

theorem charIm_eq_zero (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (ω : Ω) {s : ℝ} {e : E}
    (he : (s, e) ∉ Set.Ioc (0 : ℝ) T ×ˢ A) : charIm N w Bfam A T ω s e = 0 := by
  rw [charIm, charIntegrand_eq_zero N w hBsub ω he, Complex.zero_im]

/-- A bounded integrand carried by a window of finite mark measure has finite energy. -/
theorem lintegral_sq_of_bounded {φ : Ω → ℝ → E → ℝ} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (hbd : ∀ ω s e, ‖φ ω s e‖ ≤ 2) (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0)
    (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω s e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ≤ A.indicator (fun _ => (4 : ℝ≥0∞)) e := by
    intro ω s e
    by_cases he : e ∈ A
    · rw [Set.indicator_of_mem he]
      have h2 : (‖φ ω s e‖₊ : ℝ≥0∞) ≤ 2 := by
        rw [show ((2 : ℝ≥0∞)) = ((2 : ℝ≥0) : ℝ≥0∞) from by norm_num]
        exact ENNReal.coe_le_coe.mpr (by
          rw [← NNReal.coe_le_coe]
          simpa using hbd ω s e)
      calc (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ≤ (2 : ℝ≥0∞) ^ 2 := pow_le_pow_left' h2 2
        _ = 4 := by norm_num
    · rw [Set.indicator_of_notMem he, hsupp ω s e he]
      simp
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s =>
    lintegral_mono fun e => hpt ω s e) ?_
  rw [show (fun s : ℝ => ∫⁻ e, A.indicator (fun _ => (4 : ℝ≥0∞)) e ∂ν)
      = fun _ : ℝ => 4 * ν A from by
    funext s
    rw [lintegral_indicator hA, setLIntegral_const]]
  rw [setLIntegral_const, lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hAν))
    measure_Icc_lt_top

theorem sq_charRe (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖charRe N w Bfam A T ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  lintegral_sq_of_bounded hA hAν
    (fun ω s e => le_trans (by
      rw [charRe, Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _) (norm_charIntegrand_le N w Bfam A T ω s e))
    (fun ω s e he => charRe_eq_zero N w hBsub ω fun hmem => he hmem.2) T'

theorem sq_charIm (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {T : ℝ} (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖charIm N w Bfam A T ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  lintegral_sq_of_bounded hA hAν
    (fun ω s e => le_trans (by
      rw [charIm, Real.norm_eq_abs]
      exact Complex.abs_im_le_norm _) (norm_charIntegrand_le N w Bfam A T ω s e))
    (fun ω s e he => charIm_eq_zero N w hBsub ω fun hmem => he hmem.2) T'

end Integrand

end LevyStochCalc.Poisson
