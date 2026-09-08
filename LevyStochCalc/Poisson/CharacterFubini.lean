/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterStrict

/-!
# The pairing with the compensator as a time integral of the pairings with the characters

The chain rule's integrand for the family cut at `t` factors as a deterministic mark times the
predictable exponential. Pairing a weight with the compensator and swapping the two integrals
therefore leaves, at each point of the window, the mark times the pairing of the weight with the
character at that time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Fubini

/-- The deterministic factor of the chain rule's integrand for the family cut at `t`. -/
noncomputable def charMark (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (t : ℝ) (q : ℝ × E) : ℂ :=
  (((⋃ j, truncFam Bfam t j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)
    * (Complex.exp (Complex.I * (simpleMark w (truncFam Bfam t) q : ℂ)) - 1)

theorem charIntegrand_truncFam_eq (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (A : Set E) (T t : ℝ) (ω : Ω) (q : ℝ × E) :
    charIntegrand N w (truncFam Bfam t) A T ω q.1 q.2
      = charMark w Bfam t q
        * Complex.exp (Complex.I * (predStrict N w (truncFam Bfam t) A T ω q.1 q.2 : ℂ)) := by
  simp only [charIntegrand, charMark, Prod.mk.eta]
  ring

theorem norm_charMark_le (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (t : ℝ) (q : ℝ × E) :
    ‖charMark w Bfam t q‖ ≤ 2 := by
  rw [charMark, norm_mul]
  have h1 : ‖(((⋃ j, truncFam Bfam t j).indicator (fun _ => (1 : ℝ)) q : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    by_cases h : q ∈ ⋃ j, truncFam Bfam t j
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have h2 : ‖Complex.exp (Complex.I * (simpleMark w (truncFam Bfam t) q : ℂ)) - 1‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_exp_I_mul_ofReal, norm_one]
    norm_num
  calc _ ≤ 1 * 2 := mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = 2 := one_mul 2

theorem charMark_eq_zero (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) {t : ℝ} {q : ℝ × E}
    (hq : t < q.1) : charMark w Bfam t q = 0 := by
  have hnot : q ∉ ⋃ j, truncFam Bfam t j := by
    rw [iUnion_truncFam]
    rintro ⟨-, ⟨-, hle⟩, -⟩
    exact absurd hle (not_le.mpr hq)
  simp [charMark, Set.indicator_of_notMem hnot]

/-- **Fubini for the compensator.** Pairing an integrable weight with the compensator of the
character at `t` is the integral over the window of the mark times the pairing of the weight
with the character at that time. -/
theorem integral_mul_charCompensator (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {r : Ω → ℝ} (hr1 : Integrable r P) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {t : ℝ} (htT : t ≤ T) :
    ∫ ω, (r ω : ℂ) * charCompensator N w Bfam A T t ω ∂P
      = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          charMark w Bfam t q * ∫ ω, (r ω : ℂ) * charAt N w Bfam q.1 ω ∂P
          ∂(referenceIntensity ν) := by
  set W : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hW
  have hWm : MeasurableSet W := measurableSet_Ioc.prod hA
  have hWfin : referenceIntensity ν W ≠ ⊤ := referenceIntensity_Ioc_prod_ne_top hAν T
  haveI : IsFiniteMeasure ((referenceIntensity ν).restrict W) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hWfin⟩
  set F : Ω → ℝ × E → ℂ :=
    fun ω q => (r ω : ℂ) * charIntegrand N w (truncFam Bfam t) A T ω q.1 q.2 with hF
  have hCm : Measurable fun p : Ω × ℝ × E =>
      charIntegrand N w (truncFam Bfam t) A T p.1 p.2.1 p.2.2 :=
    (markedPredictable_charIntegrand N hℱ w (measurableSet_truncFam hBm t) hA hAν
      (truncFam_subset hBsub t)).mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hr' : AEStronglyMeasurable (fun ω => (r ω : ℂ)) P :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hr1.aestronglyMeasurable
  have hFm : AEStronglyMeasurable (Function.uncurry F)
      (P.prod ((referenceIntensity ν).restrict W)) :=
    hr'.comp_fst.mul hCm.aestronglyMeasurable
  have hF : Integrable (Function.uncurry F) (P.prod ((referenceIntensity ν).restrict W)) := by
    refine (integrable_prod_iff hFm).mpr ⟨Filter.Eventually.of_forall fun ω => ?_, ?_⟩
    · exact (integrableOn_charIntegrand N hℱ w (measurableSet_truncFam hBm t) hA hAν
        (truncFam_subset hBsub t) ω).const_mul (r ω : ℂ)
    · refine Integrable.mono'
        ((hr1.norm.const_mul 2).mul_const (((referenceIntensity ν).restrict W).real Set.univ))
        hFm.norm.integral_prod_right' (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun q => norm_nonneg _)]
      calc ∫ q, ‖F ω q‖ ∂((referenceIntensity ν).restrict W)
          ≤ ∫ _, 2 * ‖r ω‖ ∂((referenceIntensity ν).restrict W) := by
            refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
              (integrable_const _) (Filter.Eventually.of_forall fun q => ?_)
            simp only [hF, norm_mul, Complex.norm_real]
            calc ‖r ω‖ * ‖charIntegrand N w (truncFam Bfam t) A T ω q.1 q.2‖
                ≤ ‖r ω‖ * 2 := mul_le_mul_of_nonneg_left
                    (norm_charIntegrand_le N w _ A T ω q.1 q.2) (norm_nonneg _)
              _ = 2 * ‖r ω‖ := mul_comm _ _
        _ = 2 * ‖r ω‖ * ((referenceIntensity ν).restrict W).real Set.univ := by
            rw [integral_const, smul_eq_mul, mul_comm]
  have hswap := integral_integral_swap hF
  have hL : ∫ ω, (r ω : ℂ) * charCompensator N w Bfam A T t ω ∂P
      = ∫ ω, ∫ q, F ω q ∂((referenceIntensity ν).restrict W) ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [charCompensator]
    rw [MeasureTheory.integral_const_mul]
  have hR : ∫ q, ∫ ω, F ω q ∂P ∂((referenceIntensity ν).restrict W)
      = ∫ q in W, charMark w Bfam t q * ∫ ω, (r ω : ℂ) * charAt N w Bfam q.1 ω ∂P
          ∂(referenceIntensity ν) := by
    refine setIntegral_congr_fun hWm fun q hq => ?_
    have hq1 : 0 < q.1 := hq.1.1
    have hq2 : q.2 ∈ A := hq.2
    have hfac : ∀ ω, F ω q = charMark w Bfam t q
        * ((r ω : ℂ) * Complex.exp
            (Complex.I * (predStrict N w (truncFam Bfam t) A T ω q.1 q.2 : ℂ))) := by
      intro ω
      show (r ω : ℂ) * charIntegrand N w (truncFam Bfam t) A T ω q.1 q.2 = _
      rw [charIntegrand_truncFam_eq]
      ring
    simp_rw [hfac]
    rw [MeasureTheory.integral_const_mul]
    rcases le_or_gt q.1 t with hqt | hqt
    · rw [integral_mul_exp_predStrict N w hBm hq1 hqt htT hq2]
    · rw [charMark_eq_zero w Bfam hqt, zero_mul, zero_mul]
  rw [hL, hswap, hR]

end Fubini

end LevyStochCalc.Poisson
