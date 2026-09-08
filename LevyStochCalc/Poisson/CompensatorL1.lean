/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Compensator

/-!
# From energy to the mean pathwise integral

The compensator identity turns the mean of the absolute integral against the random measure into
the mean against the reference intensity, and on a window of finite intensity the latter is
controlled by the energy through the comparison of `L¹` with `L²`. So an energy-null sequence of
predictable marked integrands has pathwise compensated integrals tending to zero in mean.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Bound

variable {A : Set E} {T : ℝ}

omit [IsProbabilityMeasure P] in
/-- The reference intensity of a window, as an iterated integral over time and marks. -/
theorem lintegral_referenceIntensity_window {f : ℝ × E → ℝ≥0∞} (hf : Measurable f)
    (A : Set E) (T : ℝ) :
    ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, f q ∂(referenceIntensity ν)
      = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e in A, f (s, e) ∂ν ∂volume := by
  have hsub : Set.Ioc (0 : ℝ) T ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) T := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => h.1.le
  have hres : (referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
      = (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A) := by
    rw [referenceIntensity, ← Measure.prod_restrict,
      Measure.restrict_restrict measurableSet_Ioc, hsub]
  rw [hres, lintegral_prod _ hf.aemeasurable]


omit [SigmaFinite ν] in
/-- **Energy controls the mean absolute intensity integral.** -/
theorem lintegral_enorm_le_energy (hRfin : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤)
    {η : Ω → ℝ → E → ℝ} (hη : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P
      ≤ (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹
        * referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹ := by
  set R : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hRdef
  haveI hfin : IsFiniteMeasure ((referenceIntensity ν).restrict R) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact lt_top_iff_ne_top.mpr hRfin
  set Λ : Measure (Ω × ℝ × E) := P.prod ((referenceIntensity ν).restrict R) with hΛ
  set f : Ω × ℝ × E → ℝ := fun p => η p.1 p.2.1 p.2.2 with hf
  have hΛuniv : Λ Set.univ = referenceIntensity ν R := by
    rw [hΛ, ← Set.univ_prod_univ, Measure.prod_prod, Measure.restrict_apply_univ, measure_univ,
      one_mul]
  have hone : ∫⁻ p, ‖f p‖ₑ ∂Λ
      = ∫⁻ ω, ∫⁻ q in R, ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P := by
    rw [hΛ, lintegral_prod _ (hη.enorm.aemeasurable)]
  have htwo : ∫⁻ p, ‖f p‖ₑ ^ 2 ∂Λ
      = ∫⁻ ω, ∫⁻ q in R, ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P := by
    rw [hΛ, lintegral_prod _ ((hη.enorm.pow_const 2).aemeasurable)]
  have hL2 : eLpNorm f 2 Λ = (∫⁻ p, ‖f p‖ₑ ^ 2 ∂Λ) ^ (2 : ℝ)⁻¹ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := Λ) (f := f)
    (p := 1) (q := 2) (by norm_num) hη.stronglyMeasurable.aestronglyMeasurable
  rw [eLpNorm_one_eq_lintegral_enorm, hL2, hΛuniv] at hcmp
  rw [← hone, ← htwo]
  refine hcmp.trans (le_of_eq ?_)
  norm_num

end Bound

section Pathwise

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {A : Set E} {T : ℝ}

/-- The compensator identity for the size of a predictable marked integrand. -/
theorem lintegral_enorm_count_eq (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω) ∂P
      = ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P :=
  lintegral_lintegral_slice_eq N hℱ hA hAν T (Ψ := fun p => ‖η p.1 p.2.1 p.2.2‖ₑ)
    (measurable_enorm.comp hη)

/-- **The mean size of the pathwise compensated integral is at most twice the mean size against
the reference intensity.** -/
theorem lintegral_enorm_pathwise_le (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η) :
    ∫⁻ ω, ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ ∂P
      ≤ 2 * ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P := by
  obtain ⟨hc, -, -⟩ := aemeasurable_and_lintegral_lintegral_slice_eq N hℱ hA hAν T
    (Ψ := fun p : Ω × ℝ × E => ‖η p.1 p.2.1 p.2.2‖ₑ) (measurable_enorm.comp hη)
  have hstep : ∀ ω : Ω,
      ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ
      ≤ (∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω))
          + ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
              ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) := fun ω =>
    le_trans enorm_sub_le
      (add_le_add (enorm_integral_le_lintegral_enorm _) (enorm_integral_le_lintegral_enorm _))
  calc ∫⁻ ω, ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(N.N ω))
          - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ ∂P
      ≤ ∫⁻ ω, ((∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω))
          + ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
              ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν)) ∂P := lintegral_mono hstep
    _ = (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω) ∂P)
          + ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
              ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P := lintegral_add_left' hc _
    _ = 2 * ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P := by
        rw [lintegral_enorm_count_eq N hℱ hA hAν T hη, two_mul]

/-- **An energy-null sequence of predictable integrands has pathwise compensated integrals
tending to zero in mean.** -/
theorem tendsto_lintegral_enorm_pathwise (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : ℕ → Ω → ℝ → E → ℝ}
    (hη : ∀ n, Probability.MarkedPredictable ℱ ν (η n))
    (hηm : ∀ n, Measurable fun p : Ω × ℝ × E => η n p.1 p.2.1 p.2.2)
    (hen : Tendsto (fun n => ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ ω, ‖(∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η n ω q.1 q.2 ∂(N.N ω))
      - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          η n ω q.1 q.2 ∂(referenceIntensity ν)‖ₑ ∂P) atTop (𝓝 0) := by
  have hRfin : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAν T
  have hlim : Tendsto (fun n => 2 * ((∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹
      * referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹)) atTop (𝓝 0) := by
    have hrpow : Tendsto (fun n => (∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
        ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹) atTop (𝓝 0) := by
      have := (ENNReal.continuous_rpow_const (y := (2 : ℝ)⁻¹)).tendsto 0
      have h0 : ((0 : ℝ≥0∞)) ^ (2 : ℝ)⁻¹ = 0 := ENNReal.zero_rpow_of_pos (by norm_num)
      rw [h0] at this
      exact this.comp hen
    have hmtop : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹ ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) hRfin
    have hmul := ENNReal.Tendsto.mul_const hrpow (Or.inr hmtop)
    rw [zero_mul] at hmul
    have hfin : Tendsto (fun n => (2 : ℝ≥0∞) * ((∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
        ‖η n ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P) ^ (2 : ℝ)⁻¹
        * referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ^ (2 : ℝ)⁻¹))
        atTop (𝓝 ((2 : ℝ≥0∞) * 0)) :=
      ENNReal.Tendsto.const_mul hmul (Or.inr (by norm_num))
    rwa [mul_zero] at hfin
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun n => bot_le) (fun n => ?_)
  refine (lintegral_enorm_pathwise_le N hℱ hA hAν T (hη n)).trans ?_
  gcongr
  exact lintegral_enorm_le_energy hRfin (hηm n)

/-- **A predictable integrand of finite energy is almost surely integrable on the window**, both
against the random measure and against the reference intensity. -/
theorem ae_integrableOn_window (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) {η : Ω → ℝ → E → ℝ}
    (hη : Probability.MarkedPredictable ℱ ν η)
    (hm : Measurable fun p : Ω × ℝ × E => η p.1 p.2.1 p.2.2)
    (hen : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η ω q.1 q.2‖ₑ ^ 2 ∂(referenceIntensity ν) ∂P ≠ ⊤) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => η ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)
      ∧ IntegrableOn (fun q : ℝ × E => η ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
          (referenceIntensity ν) := by
  have hRfin : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAν T
  have hmeanI : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A,
      ‖η ω q.1 q.2‖ₑ ∂(referenceIntensity ν) ∂P ≠ ⊤ := by
    refine ne_top_of_le_ne_top ?_ (lintegral_enorm_le_energy hRfin hm)
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hen)
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) hRfin)
  have hmeanN : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ A, ‖η ω q.1 q.2‖ₑ ∂(N.N ω) ∂P ≠ ⊤ := by
    rw [lintegral_enorm_count_eq N hℱ hA hAν T hη]
    exact hmeanI
  obtain ⟨hcAE, hiM, -⟩ := aemeasurable_and_lintegral_lintegral_slice_eq N hℱ hA hAν T
    (Ψ := fun p : Ω × ℝ × E => ‖η p.1 p.2.1 p.2.2‖ₑ) (measurable_enorm.comp hη)
  have hslice : ∀ ω : Ω, Measurable fun q : ℝ × E => η ω q.1 q.2 :=
    fun ω => hm.comp measurable_prodMk_left
  filter_upwards [ae_lt_top' hcAE hmeanN, ae_lt_top' hiM.aemeasurable hmeanI] with ω hN hI
  exact ⟨⟨(hslice ω).stronglyMeasurable.aestronglyMeasurable, hN⟩,
    ⟨(hslice ω).stronglyMeasurable.aestronglyMeasurable, hI⟩⟩

/-- The pathwise compensated integral is additive on integrands integrable on the window. -/
theorem pathwise_sub {η₁ η₂ : Ω → ℝ → E → ℝ} (ω : Ω)
    (h1 : IntegrableOn (fun q : ℝ × E => η₁ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω))
    (h1' : IntegrableOn (fun q : ℝ × E => η₁ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
      (referenceIntensity ν))
    (h2 : IntegrableOn (fun q : ℝ × E => η₂ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω))
    (h2' : IntegrableOn (fun q : ℝ × E => η₂ ω q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
      (referenceIntensity ν)) :
    ((∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₁ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₁ ω q.1 q.2 ∂(referenceIntensity ν))
      - ((∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₂ ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, η₂ ω q.1 q.2 ∂(referenceIntensity ν))
      = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, (η₁ ω q.1 q.2 - η₂ ω q.1 q.2) ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            (η₁ ω q.1 q.2 - η₂ ω q.1 q.2) ∂(referenceIntensity ν) := by
  rw [integral_sub h1 h2, integral_sub h1' h2']
  ring

end Pathwise

end LevyStochCalc.Poisson
