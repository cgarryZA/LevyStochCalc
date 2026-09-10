/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.VectorItoProcess
import LevyStochCalc.Ito.Setting
import LevyStochCalc.Poisson.PathwiseIdentity

/-!
# Finite-activity splitting of a jump diffusion

A jump diffusion whose jump coefficient is carried by a mark set of finite intensity is the sum
of a vector Itô process and a pathwise jump sum. The compensated Poisson integral of such a
coefficient is the pathwise integral against the random measure minus the integral against the
reference intensity, and the latter is an absolutely continuous drift, so it can be absorbed into
the drift of the Itô part.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.jumpSum` — the pathwise sum of the jumps carried by a mark set
  over a time window.
* `LevyStochCalc.Ito.JumpSplitting.continuousDrift` — the drift of a jump diffusion with the jump
  compensator subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSum` — at every nonnegative time a
  jump diffusion is almost surely the sum of the vector Itô process with diffusion `σ` and drift
  `continuousDrift`, and the pathwise jump sum.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section ENNRealAux

/-- The square of a sum in `ℝ≥0∞` is at most four times the sum of the squares. -/
theorem sq_add_le_four_mul (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2) := by
  rcases le_total a b with h | h
  · calc (a + b) ^ 2 ≤ (b + b) ^ 2 := by gcongr
      _ = 4 * b ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl le_add_self
  · calc (a + b) ^ 2 ≤ (a + a) ^ 2 := by gcongr
      _ = 4 * a ^ 2 := by ring
      _ ≤ 4 * (a ^ 2 + b ^ 2) := mul_le_mul' le_rfl le_self_add

/-- A bound by a product of square roots squares to a bound by the product. -/
theorem sq_le_of_le_mul_rpow {x a b : ℝ≥0∞} (h : x ≤ a ^ (2 : ℝ)⁻¹ * b ^ (2 : ℝ)⁻¹) :
    x ^ 2 ≤ a * b := by
  refine le_trans (pow_le_pow_left' h 2) (le_of_eq ?_)
  rw [← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ (2 : ℝ)⁻¹),
    ← ENNReal.rpow_natCast ((a * b) ^ (2 : ℝ)⁻¹) 2, ← ENNReal.rpow_mul]
  norm_num

end ENNRealAux

section Comparison

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Over a finite measure the mean size is at most the root mean square times the square root of
the total mass. -/
theorem lintegral_enorm_le_rms [IsFiniteMeasure μ] (f : α → ℝ) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ a, ‖f a‖ₑ ∂μ ≤ (∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ * μ Set.univ ^ (2 : ℝ)⁻¹ := by
  have hcmp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (f := f)
    (p := 1) (q := 2) (by norm_num) hf
  have h2 : eLpNorm f 2 μ = (∫⁻ a, ‖f a‖ₑ ^ 2 ∂μ) ^ (2 : ℝ)⁻¹ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
    norm_num
  rw [eLpNorm_one_eq_lintegral_enorm, h2] at hcmp
  refine hcmp.trans (le_of_eq ?_)
  norm_num

/-- A square-integrable function on a bounded time window is integrable there. -/
theorem integrableOn_Icc_of_lintegral_sq_lt_top {T : ℝ} {f : ℝ → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (Set.Icc (0 : ℝ) T)))
    (h : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    IntegrableOn f (Set.Icc (0 : ℝ) T) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact isCompact_Icc.measure_lt_top⟩
  refine ⟨hf, lt_of_le_of_lt (lintegral_enorm_le_rms f hf) ?_⟩
  refine ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) h.ne) ?_
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top _ _)

end Comparison

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The reference intensity restricted to a time window times a mark set is the product of
Lebesgue measure on the window with the mark measure restricted to the mark set. -/
theorem restrict_referenceIntensity_window (A : Set E) (T : ℝ) :
    (LevyStochCalc.Poisson.referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
      = (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A) := by
  have hsub : Set.Ioc (0 : ℝ) T ∩ Set.Ici (0 : ℝ) = Set.Ioc (0 : ℝ) T := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => h.1.le
  rw [LevyStochCalc.Poisson.referenceIntensity, ← Measure.prod_restrict,
    Measure.restrict_restrict measurableSet_Ioc, hsub]

/-- On a window of finite intensity the integral against the reference intensity is the iterated
integral over times and marks, whose inner integral is integrable in time. -/
theorem integral_window_eq_and_integrableOn (g : ℝ → E → ℝ) {A : Set E} {T : ℝ}
    (hg : IntegrableOn (fun q : ℝ × E => g q.1 q.2) (Set.Ioc (0 : ℝ) T ×ˢ A)
      (LevyStochCalc.Poisson.referenceIntensity ν)) :
    (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, g q.1 q.2
          ∂(LevyStochCalc.Poisson.referenceIntensity ν)
        = ∫ s in Set.Icc (0 : ℝ) T, (∫ e in A, g s e ∂ν) ∂volume)
      ∧ IntegrableOn (fun s => ∫ e in A, g s e ∂ν) (Set.Icc (0 : ℝ) T) volume := by
  have hg' : Integrable (fun q : ℝ × E => g q.1 q.2)
      ((volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A)) := by
    rw [← restrict_referenceIntensity_window (ν := ν) A T]
    exact hg
  refine ⟨?_, ?_⟩
  · rw [show (LevyStochCalc.Poisson.referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
        = (volume.restrict (Set.Ioc (0 : ℝ) T)).prod (ν.restrict A) from
      restrict_referenceIntensity_window A T,
      integral_prod (fun q : ℝ × E => g q.1 q.2) hg', integral_Icc_eq_integral_Ioc]
  · exact IntegrableOn.congr_set_ae hg'.integral_prod_left (MeasureTheory.Ioc_ae_eq_Icc).symm

/-- The pathwise sum of the jumps carried by the mark set `A` over the window `(0, t]`. -/
noncomputable def jumpSum (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (t : ℝ) (ω : Ω)
    (i : Fin n) : ℝ :=
  ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i ∂(N.N ω)

/-- The drift of a jump diffusion with the compensator of the jumps carried by `A` subtracted. -/
noncomputable def continuousDrift (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E)
    (i : Fin n) (ω : Ω) (s : ℝ) : ℝ :=
  coeffs.μ s (X.X s ω) i - ∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν

/-- The jump sum over the degenerate window vanishes. -/
theorem jumpSum_zero (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (ω : Ω) (i : Fin n) :
    jumpSum X A 0 ω i = 0 := by
  simp [jumpSum]

section Regularity

variable (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (i : Fin n)

/-- The compensator of the jumps carried by `A`, as a function of the sample point and time. -/
theorem stronglyMeasurable_markIntegral
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) :
    StronglyMeasurable fun p : Ω × ℝ => ∫ e in A, coeffs.γ p.2 (X.X p.2 p.1) e i ∂ν :=
  (hγm.comp MeasurableEquiv.prodAssoc.measurable).stronglyMeasurable.integral_prod_right'
    (ν := ν.restrict A)

/-- The drift with the compensator subtracted is jointly measurable. -/
theorem measurable_continuousDrift
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) :
    Measurable (Function.uncurry (continuousDrift X A i)) :=
  hμm.sub (stronglyMeasurable_markIntegral X A i hγm).measurable

/-- The mark integral of a progressively measurable marked process is progressively
measurable. -/
theorem progressivelyMeasurable_markIntegral (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {φ : Ω → ℝ → E → ℝ} (h : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => ∫ e in A, φ ω s e ∂ν := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun r : (Ω × ℝ) × E =>
      (Set.Iic t).indicator (fun s => φ r.1.1 s r.2) r.1.2 :=
    (h t).comp_measurable MeasurableEquiv.prodAssoc.measurable
  have h2 : StronglyMeasurable fun p : Ω × ℝ =>
      ∫ e in A, (Set.Iic t).indicator (fun s => φ p.1 s e) p.2 ∂ν :=
    h1.integral_prod_right' (ν := ν.restrict A)
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => ∫ e in A, φ p.1 s e ∂ν) p.2)
      = fun p : Ω × ℝ => ∫ e in A, (Set.Iic t).indicator (fun s => φ p.1 s e) p.2 ∂ν := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, integral_zero]
  rw [key]
  exact h2

/-- The drift with the compensator subtracted is progressively measurable. -/
theorem progressivelyMeasurable_continuousDrift (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hμp : Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hγp : Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (X.X s ω) e i) :
    Probability.ProgressivelyMeasurable ℱ (continuousDrift X A i) :=
  hμp.sub (progressivelyMeasurable_markIntegral A ℱ hγp)

/-- The energy of the compensator over a window is at most the mark set's intensity times the
energy of the jump coefficient. -/
theorem lintegral_sq_markIntegral_le (hAν : ν A ≠ ⊤)
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * ν A := by
  haveI hfin : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hAν⟩
  have hslice : ∀ (ω : Ω) (s : ℝ), Measurable fun e => coeffs.γ s (X.X s ω) e i := by
    intro ω s
    exact hγm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖₊ : ℝ≥0∞) ^ 2
        ≤ (∫⁻ e, (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν A := by
    intro ω s
    have h1 : ‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖ₑ
        ≤ (∫⁻ e in A, ‖coeffs.γ s (X.X s ω) e i‖ₑ ^ 2 ∂ν) ^ (2 : ℝ)⁻¹
          * (ν.restrict A) Set.univ ^ (2 : ℝ)⁻¹ :=
      le_trans (enorm_integral_le_lintegral_enorm _)
        (lintegral_enorm_le_rms _ (hslice ω s).stronglyMeasurable.aestronglyMeasurable)
    refine le_trans (sq_le_of_le_mul_rpow h1) ?_
    rw [Measure.restrict_apply_univ]
    exact mul_le_mul' (lintegral_mono' Measure.restrict_le_self le_rfl) le_rfl
  calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (∫⁻ e, (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν) * ν A ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume) * ν A ∂P :=
        lintegral_congr fun ω => lintegral_mul_const' _ _ hAν
    _ = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) * ν A :=
        lintegral_mul_const' _ _ hAν

/-- The drift with the compensator subtracted has finite energy over every bounded window. -/
theorem lintegral_sq_continuousDrift_lt_top (hAν : ν A ≠ ⊤)
    (hμm : Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖continuousDrift X A i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  set M : Ω × ℝ → ℝ≥0∞ := fun p => (‖coeffs.μ p.2 (X.X p.2 p.1) i‖₊ : ℝ≥0∞) ^ 2 with hMdef
  set C : Ω × ℝ → ℝ≥0∞ :=
    fun p => (‖∫ e in A, coeffs.γ p.2 (X.X p.2 p.1) e i ∂ν‖₊ : ℝ≥0∞) ^ 2 with hCdef
  have hMmeas : Measurable M :=
    (ENNReal.continuous_coe.measurable.comp hμm.nnnorm).pow_const 2
  have hCmeas : Measurable C :=
    (ENNReal.continuous_coe.measurable.comp
      (stronglyMeasurable_markIntegral X A i hγm).measurable.nnnorm).pow_const 2
  have hbound : ∀ (ω : Ω) (s : ℝ), (‖continuousDrift X A i ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 4 * (M (ω, s) + C (ω, s)) := by
    intro ω s
    exact le_trans (pow_le_pow_left' enorm_sub_le 2) (sq_add_le_four_mul _ _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (M (ω, s) + C (ω, s)) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume :=
    fun ω => lintegral_add_left (hMmeas.comp measurable_prodMk_left) _
  have houter : ∫⁻ ω, ((∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume) ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P :=
    lintegral_add_left (hMmeas.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))) _
  have hCfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt (lintegral_sq_markIntegral_le X A i hAν hγm T) ?_
    exact ENNReal.mul_lt_top (hγq T hT) (lt_top_iff_ne_top.mpr hAν)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖continuousDrift X A i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * (M (ω, s) + C (ω, s)) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hbound ω s
    _ = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (M (ω, s) + C (ω, s)) ∂volume ∂P := by
        rw [← lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
        exact lintegral_congr fun ω =>
          lintegral_const_mul' (4 : ℝ≥0∞) _ (by norm_num)
    _ = 4 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, M (ω, s) ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C (ω, s) ∂volume ∂P) := by
        rw [lintegral_congr hinner, houter]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hμq T hT, hCfin⟩)

end Regularity

section Splitting

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The multidimensional Brownian integral of a row of the diffusion coefficient is the
martingale part of the corresponding coordinate of a vector Itô process. -/
theorem multidimIntegral_eq_vectorItoMartingale (i : Fin n) (t : ℝ) (ω : Ω) :
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
        (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
        (fun j => hσq i j) t ω
      = LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hℱW
          (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq i t ω := rfl

variable (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- **The finite-activity splitting of a jump diffusion.** If the jump coefficient is carried by
a mark set of finite intensity and its integrand along the path is predictable, then at every
nonnegative time the path is almost surely the sum of the vector Itô process with diffusion `σ`
and drift `continuousDrift`, and the pathwise jump sum over that mark set. -/
theorem eq_vectorItoProcess_add_jumpSum
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpred : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (X.X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDrift X A) t ω i
          + jumpSum X A t ω i := by
  have hsupp' : ∀ (i : Fin n) (ω : Ω) (s : ℝ) (e : E), e ∉ A →
      coeffs.γ s (X.X s ω) e i = 0 := by
    intro i ω s e he
    simp [hsupp s (X.X s ω) e he]
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    have hCzero : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) 0 ω = 0 := by
      intro i
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) 0,
        LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i)
          (le_refl (0 : ℝ))] with ω h1 h2
      rw [h1, h2]
      rfl
    have hz0 : ∀ g : ℝ → ℝ, ∫ s in Set.Icc (0 : ℝ) 0, g s ∂volume = 0 :=
      fun g => setIntegral_measure_zero g (by simp)
    filter_upwards [hSDE 0 le_rfl, MeasureTheory.ae_all_iff.mpr hCzero] with ω hω hz
    intro i
    rw [hω i, hz i, multidimIntegral_eq_vectorItoMartingale X ℱ hℱW hσm hσp hσq i 0 ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, hz0, jumpSum_zero]
  · have hpath : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω
          = jumpSum X A t ω i
            - ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i
                ∂(LevyStochCalc.Poisson.referenceIntensity ν) := fun i =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱN
        (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) hA (hpred i) hAν
        (hsupp' i) hpos
    have hwin : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
          (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [LevyStochCalc.Poisson.ae_integrableOn_window N hℱN hA hAν t (hpred i)
        (hγm i) (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγq i) (A := A) hpos)] with ω hω
      exact hω.2
    have hμint : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) t) volume := by
      intro i
      have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        ((ENNReal.continuous_coe.measurable.comp (hμm i).nnnorm).pow_const
          2).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      filter_upwards [ae_lt_top' hmeas.aemeasurable (hμq i t hpos).ne] with ω hω
      exact integrableOn_Icc_of_lintegral_sq_lt_top
        ((hμm i).comp measurable_prodMk_left).aestronglyMeasurable hω
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [hSDE t ht, hpath i, hwin i, hμint i] with ω hω hp hw hm
    obtain ⟨heq, hcint⟩ :=
      integral_window_eq_and_integrableOn (fun s e => coeffs.γ s (X.X s ω) e i) hw
    have hd : ∫ s in Set.Icc (0 : ℝ) t, continuousDrift X A i ω s ∂volume
        = (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t, (∫ e in A, coeffs.γ s (X.X s ω) e i ∂ν) ∂volume :=
      integral_sub hm hcint
    rw [hω i, hp, multidimIntegral_eq_vectorItoMartingale X ℱ hℱW hσm hσp hσq i t ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    rw [hd, heq]
    ring

end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting
