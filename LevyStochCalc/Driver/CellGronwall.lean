/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellFubini
import LevyStochCalc.Poisson.CharacterMarkFactor
import LevyStochCalc.Poisson.CharacterGronwall

/-!
# The pairing of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Parts

/-- A bounded measurable function on a probability space is square integrable. -/
theorem memLp_two_of_bound {f : Ω → ℝ} (hf : AEStronglyMeasurable f P) {C : ℝ}
    (hb : ∀ ω, |f ω| ≤ C) : MemLp f 2 P :=
  MemLp.of_bound hf C (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hb ω)

/-- The pairing of the weight and the bounded factor with a trigonometric function of the
Brownian increment against a real component of the Poisson character. -/
noncomputable def cellPart (P : Measure Ω) (Z V : Ω → ℝ) (l : ℝ) (X : ℝ → Ω → ℝ)
    (g : ℝ → ℝ) (Y : ℝ → Ω → ℝ) (s : ℝ) : ℝ :=
  ∫ ω, Z ω * V ω * (g (l * X s ω) * Y s ω) ∂P

/-- The integrand of a real cell pairing is integrable. -/
theorem integrable_cellPart {Z V : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    {Mv : ℝ} (hVb : ∀ ω, |V ω| ≤ Mv) {l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}
    (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {Y : ℝ → Ω → ℝ} {s : ℝ}
    (hXs : Measurable (X s)) (hYs : Measurable (Y s)) (hYb : ∀ ω, |Y s ω| ≤ 1) :
    Integrable (fun ω => Z ω * V ω * (g (l * X s ω) * Y s ω)) P := by
  refine integrable_mul_bdd_mul hZ2 (memLp_two_of_bound (C := 1 * 1) ?_ ?_) hVm hVb
  · exact ((hgc.measurable.comp (measurable_const.mul hXs)).mul hYs).aestronglyMeasurable
  · intro ω
    rw [abs_mul]
    exact mul_le_mul (hgb _) (hYb ω) (abs_nonneg _) zero_le_one

variable (N : PoissonRandomMeasure P ν)

/-- The pairing of the weight and the bounded factor with the product of the Brownian and Poisson
cell characters. -/
noncomputable def cellPairing (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (Z V : Ω → ℝ)
    (l : ℝ) (X : ℝ → Ω → ℝ) (s : ℝ) : ℂ :=
  ∫ ω, ((Z ω * V ω : ℝ) : ℂ)
    * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω) ∂P

/-- The complex pairing is the combination of the four real pairings. -/
theorem cellPairing_eq_parts (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {Z V : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hVm : Measurable V) {Mv : ℝ} (hVb : ∀ ω, |V ω| ≤ Mv) {l : ℝ} {X : ℝ → Ω → ℝ}
    {s : ℝ} (hXs : Measurable (X s)) :
    cellPairing N w Bfam Z V l X s
      = ((cellPart P Z V l X Real.cos (fun s ω => (charAt N w Bfam s ω).re) s
            - cellPart P Z V l X Real.sin (fun s ω => (charAt N w Bfam s ω).im) s : ℝ) : ℂ)
        + Complex.I * ((cellPart P Z V l X Real.cos (fun s ω => (charAt N w Bfam s ω).im) s
            + cellPart P Z V l X Real.sin (fun s ω => (charAt N w Bfam s ω).re) s : ℝ)
          : ℂ) := by
  have hcm : Measurable fun ω => (charAt N w Bfam s ω).re :=
    Complex.measurable_re.comp (measurable_charAt N w hBm s)
  have him : Measurable fun ω => (charAt N w Bfam s ω).im :=
    Complex.measurable_im.comp (measurable_charAt N w hBm s)
  have hcb : ∀ ω, |(charAt N w Bfam s ω).re| ≤ 1 := fun ω => abs_charAt_re_le N w s ω
  have hib : ∀ ω, |(charAt N w Bfam s ω).im| ≤ 1 := fun ω => abs_charAt_im_le N w s ω
  have h1 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_cos
    Real.abs_cos_le_one (Y := fun s ω => (charAt N w Bfam s ω).re) hXs hcm hcb
  have h2 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_sin
    Real.abs_sin_le_one (Y := fun s ω => (charAt N w Bfam s ω).im) hXs him hib
  have h3 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_cos
    Real.abs_cos_le_one (Y := fun s ω => (charAt N w Bfam s ω).im) hXs him hib
  have h4 := integrable_cellPart hZ2 hVm hVb (l := l) (X := X) Real.continuous_sin
    Real.abs_sin_le_one (Y := fun s ω => (charAt N w Bfam s ω).re) hXs hcm hcb
  have hpt : ∀ ω, ((Z ω * V ω : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ)) * charAt N w Bfam s ω)
      = ((Z ω * V ω * (Real.cos (l * X s ω) * (charAt N w Bfam s ω).re)
            - Z ω * V ω * (Real.sin (l * X s ω) * (charAt N w Bfam s ω).im) : ℝ) : ℂ)
        + Complex.I * ((Z ω * V ω * (Real.cos (l * X s ω) * (charAt N w Bfam s ω).im)
            + Z ω * V ω * (Real.sin (l * X s ω) * (charAt N w Bfam s ω).re) : ℝ) : ℂ) := by
    intro ω
    have hre : (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ))).re = Real.cos (l * X s ω) :=
      exp_I_mul_ofReal_re _
    have hiim : (Complex.exp (Complex.I * ((l * X s ω : ℝ) : ℂ))).im = Real.sin (l * X s ω) :=
      exp_I_mul_ofReal_im _
    refine Complex.ext ?_ ?_ <;>
      simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, hre, hiim,
        zero_mul, mul_zero, zero_add, add_zero, sub_zero, one_mul] <;>
      ring
  have hofReal : ∀ f : Ω → ℝ,
      ∫ ω, ((f ω : ℝ) : ℂ) ∂P = ((∫ ω, f ω ∂P : ℝ) : ℂ) :=
    fun _ => integral_ofReal
  rw [cellPairing]
  simp_rw [hpt]
  rw [integral_add (h1.sub h2).ofReal ((h3.add h4).ofReal.const_mul _),
    MeasureTheory.integral_const_mul, hofReal, hofReal, integral_sub h1 h2, integral_add h3 h4]
  rfl

end Parts

section Half

variable (N : PoissonRandomMeasure P ν)

/-- The pairing of the weight, the bounded factor and a trigonometric function of the Brownian
increment with the Poisson cell character. -/
noncomputable def cellHalf (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (Z V : Ω → ℝ) (l : ℝ)
    (X : ℝ → Ω → ℝ) (g : ℝ → ℝ) (s : ℝ) : ℂ :=
  ∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω ∂P

variable {Z V : Ω → ℝ} {Mv l : ℝ} {X : ℝ → Ω → ℝ} {g : ℝ → ℝ}

/-- The weight, the bounded factor and a trigonometric function of the Brownian increment are
jointly integrable. -/
theorem integrable_weight (hZ2 : MemLp Z 2 P) (hVm : Measurable V) (hVb : ∀ ω, |V ω| ≤ Mv)
    (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ} (hXs : Measurable (X s)) :
    Integrable (fun ω => Z ω * V ω * g (l * X s ω)) P :=
  integrable_mul_bdd_mul hZ2
    (memLp_two_of_bound (C := 1)
      (hgc.measurable.comp (measurable_const.mul hXs)).aestronglyMeasurable
      (fun _ => hgb _)) hVm hVb

/-- The real cell pairings are the real and imaginary parts of the complex half. -/
theorem cellPart_eq_cellHalf_re (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ}
    (hXs : Measurable (X s)) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) s
      = (cellHalf N w Bfam Z V l X g s).re := by
  have hint := integrable_mul_charAt N w hBm
    (integrable_weight (l := l) (X := X) hZ2 hVm hVb hgc hgb hXs) s
  have hre : ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω).re ∂P
      = (∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω ∂P).re :=
    integral_re hint
  rw [cellPart, cellHalf, ← hre]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The real cell pairings are the real and imaginary parts of the complex half. -/
theorem cellPart_eq_cellHalf_im (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ}
    (hXs : Measurable (X s)) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) s
      = (cellHalf N w Bfam Z V l X g s).im := by
  have hint := integrable_mul_charAt N w hBm
    (integrable_weight (l := l) (X := X) hZ2 hVm hVb hgc hgb hXs) s
  have him : ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω).im ∂P
      = (∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω ∂P).im :=
    integral_im hint
  rw [cellPart, cellHalf, ← him]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  ring

/-- The complex pairing is the cosine half plus `i` times the sine half. -/
theorem cellPairing_eq_halves (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) {s : ℝ} (hXs : Measurable (X s)) :
    cellPairing N w Bfam Z V l X s
      = cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * cellHalf N w Bfam Z V l X Real.sin s := by
  rw [cellPairing_eq_parts N w hBm hZ2 hVm hVb hXs,
    cellPart_eq_cellHalf_re N w hBm hZ2 hVm hVb Real.continuous_cos Real.abs_cos_le_one hXs,
    cellPart_eq_cellHalf_im N w hBm hZ2 hVm hVb Real.continuous_sin Real.abs_sin_le_one hXs,
    cellPart_eq_cellHalf_im N w hBm hZ2 hVm hVb Real.continuous_cos Real.abs_cos_le_one hXs,
    cellPart_eq_cellHalf_re N w hBm hZ2 hVm hVb Real.continuous_sin Real.abs_sin_le_one hXs]
  refine Complex.ext ?_ ?_ <;>
    simp only [Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      mul_zero, zero_add, add_zero, zero_sub, sub_zero] <;>
    ring

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- Inside the window the pairing against the real part of the chain rule's integrand is the real
part of the mark factor times the half. -/
theorem integral_mul_charRe_eq (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ} (hs : 0 < s)
    (hsT : s ≤ T) {e : E} (he : e ∈ A) (hXs : Measurable (X s)) :
    ∫ ω, Z ω * V ω * (g (l * X s ω) * charRe N w Bfam A T ω s e) ∂P
      = (markFactor w Bfam (s, e) * cellHalf N w Bfam Z V l X g s).re := by
  have hr := integrable_weight (l := l) (X := X) hZ2 hVm hVb hgc hgb hXs
  have hjoint : Measurable fun p : Ω × ℝ × E => charIntegrand N w Bfam A T p.1 p.2.1 p.2.2 :=
    (markedPredictable_charIntegrand N hℱ w hBm hA hAν hBsub).mono
      (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hcm : Measurable fun ω => charIntegrand N w Bfam A T ω s e :=
    hjoint.comp (measurable_id.prodMk
      (measurable_const : Measurable fun _ : Ω => ((s, e) : ℝ × E)))
  have hint : Integrable (fun ω => ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
      * charIntegrand N w Bfam A T ω s e) P := by
    refine (hr.ofReal.bdd_mul (c := 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => norm_charIntegrand_le N w Bfam A T ω s e)).congr
      (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hstep : ∫ ω, Z ω * V ω * (g (l * X s ω) * charRe N w Bfam A T ω s e) ∂P
      = ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
          * charIntegrand N w Bfam A T ω s e).re ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, charRe]
    ring
  have hre : ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
        * charIntegrand N w Bfam A T ω s e).re ∂P
      = (∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
        * charIntegrand N w Bfam A T ω s e ∂P).re := integral_re hint
  rw [hstep, hre, integral_mul_charIntegrand N w hBm hs hsT he]
  rfl

/-- Inside the window the pairing against the imaginary part of the chain rule's integrand is the
imaginary part of the mark factor times the half. -/
theorem integral_mul_charIm_eq (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1) {s : ℝ} (hs : 0 < s)
    (hsT : s ≤ T) {e : E} (he : e ∈ A) (hXs : Measurable (X s)) :
    ∫ ω, Z ω * V ω * (g (l * X s ω) * charIm N w Bfam A T ω s e) ∂P
      = (markFactor w Bfam (s, e) * cellHalf N w Bfam Z V l X g s).im := by
  have hr := integrable_weight (l := l) (X := X) hZ2 hVm hVb hgc hgb hXs
  have hjoint : Measurable fun p : Ω × ℝ × E => charIntegrand N w Bfam A T p.1 p.2.1 p.2.2 :=
    (markedPredictable_charIntegrand N hℱ w hBm hA hAν hBsub).mono
      (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hcm : Measurable fun ω => charIntegrand N w Bfam A T ω s e :=
    hjoint.comp (measurable_id.prodMk
      (measurable_const : Measurable fun _ : Ω => ((s, e) : ℝ × E)))
  have hint : Integrable (fun ω => ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
      * charIntegrand N w Bfam A T ω s e) P := by
    refine (hr.ofReal.bdd_mul (c := 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => norm_charIntegrand_le N w Bfam A T ω s e)).congr
      (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hstep : ∫ ω, Z ω * V ω * (g (l * X s ω) * charIm N w Bfam A T ω s e) ∂P
      = ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
          * charIntegrand N w Bfam A T ω s e).im ∂P := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, charIm]
    ring
  have him : ∫ ω, (((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
        * charIntegrand N w Bfam A T ω s e).im ∂P
      = (∫ ω, ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ)
        * charIntegrand N w Bfam A T ω s e ∂P).im := integral_im hint
  rw [hstep, him, integral_mul_charIntegrand N w hBm hs hsT he]
  rfl

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The pairing is bounded by the weight's mass times the bound on the bounded factor. -/
theorem norm_cellHalf_le (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) (hZ1 : Integrable Z P)
    (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv) (hgb : ∀ x, |g x| ≤ 1) (s : ℝ) :
    ‖cellHalf N w Bfam Z V l X g s‖ ≤ Mv * ∫ ω, ‖Z ω‖ ∂P := by
  have hb : ∀ ω, ‖((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω‖
      ≤ Mv * ‖Z ω‖ := by
    intro ω
    rw [norm_mul, Complex.norm_real, charAt, Complex.norm_exp_I_mul_ofReal, mul_one,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    calc |Z ω| * |V ω| * |g (l * X s ω)| ≤ |Z ω| * Mv * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (hVb ω) (abs_nonneg _)) (hgb _)
            (abs_nonneg _) (mul_nonneg (abs_nonneg _) hMv0)
      _ = Mv * |Z ω| := by ring
  have h := norm_integral_le_of_norm_le (μ := P) (hZ1.norm.const_mul Mv)
    (Filter.Eventually.of_forall hb)
  rw [MeasureTheory.integral_const_mul] at h
  exact h

/-- The pairing is a measurable function of the time: at every positive time it is the pairing
against the predictable representative of the strict-past character. -/
theorem aestronglyMeasurable_cellHalf {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {b T : ℝ} (hT : 0 < T) (hbT : b < T) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A)
    {e₀ : E} (he₀ : e₀ ∈ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V) (hgc : Continuous g)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (T' : ℝ) :
    AEStronglyMeasurable (fun s => cellHalf N w Bfam Z V l X g s)
      (volume.restrict (Set.Icc (0 : ℝ) T')) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T') with hμ
  have hZV : AEStronglyMeasurable (fun ω => Z ω * V ω) P :=
    hZ2.aestronglyMeasurable.mul hVm.aestronglyMeasurable
  have hgX : Measurable fun p : Ω × ℝ => g (l * X p.2 p.1) :=
    hgc.measurable.comp (measurable_const.mul hXm)
  have hR : AEStronglyMeasurable
      (fun p : Ω × ℝ => ((Z p.1 * V p.1 * g (l * X p.2 p.1) : ℝ) : ℂ)) (P.prod μ) :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable
      (hZV.comp_fst.mul hgX.aestronglyMeasurable)
  have hC : Measurable fun p : Ω × ℝ => charStrictPred N w Bfam A T e₀ p.2 p.1 :=
    measurable_uncurry_charStrictPred N w hℱ hBm hA hAν T e₀
  have hjoint : AEStronglyMeasurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) =>
        ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charStrictPred N w Bfam A T e₀ s ω)
      (P.prod μ) := hR.mul hC.aestronglyMeasurable
  refine (hjoint.prod_swap.integral_prod_right').congr ?_
  have h0 : ∀ᵐ s ∂μ, s ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton, hμ,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  have hmem : ∀ᵐ s ∂μ, s ∈ Set.Icc (0 : ℝ) T' := by
    rw [hμ]; exact ae_restrict_mem measurableSet_Icc
  filter_upwards [h0, hmem] with s hs0 hs
  have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
  refine integral_congr_ae ?_
  filter_upwards [ae_charStrictPred_eq_charAt N w hBm hT hbT hBsub he₀ hspos] with ω hω
  show ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charStrictPred N w Bfam A T e₀ s ω
      = ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω
  rw [hω]

/-- The pairing is integrable over a window of times. -/
theorem integrableOn_cellHalf {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {b T : ℝ} (hT : 0 < T) (hbT : b < T) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A)
    {e₀ : E} (he₀ : e₀ ∈ A) (hZ2 : MemLp Z 2 P) (hVm : Measurable V) (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (T' : ℝ) :
    IntegrableOn (fun s => cellHalf N w Bfam Z V l X g s) (Set.Icc (0 : ℝ) T') volume := by
  refine Integrable.mono' (integrable_const (Mv * ∫ ω, ‖Z ω‖ ∂P))
    (aestronglyMeasurable_cellHalf N hℱ w hBm hA hAν hT hbT hBsub he₀ hZ2 hVm hgc hXm T')
    (Filter.Eventually.of_forall fun s => ?_)
  exact norm_cellHalf_le N w Bfam (hZ2.integrable one_le_two) hMv0 hVb hgb s

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A function of the time alone is integrable over a window against the reference intensity. -/
theorem integrableOn_prod_of_time_complex {f : ℝ → ℂ} {t : ℝ}
    (hf : IntegrableOn f (Set.Ioc 0 t) volume) {A : Set E} (hAν : ν A ≠ ⊤) :
    IntegrableOn (fun q : ℝ × E => f q.1) (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) := by
  haveI : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hAν⟩
  have hI : Set.Ioc (0 : ℝ) t ∩ Set.Ici 0 = Set.Ioc 0 t :=
    Set.inter_eq_left.mpr fun x hx => le_of_lt hx.1
  rw [IntegrableOn, referenceIntensity, ← Measure.prod_restrict,
    Measure.restrict_restrict measurableSet_Ioc, hI]
  exact hf.comp_fst _

end Half

section Reduced

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱW : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {Z V : Ω → ℝ} {Mv l : ℝ}

/-- The deterministic drift factor of the cell identity. -/
noncomputable def cellDrift (l : ℝ) (a b : ℝ) (s : ℝ) : ℝ :=
  -(l ^ 2) / 2 * ((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s) ^ 2

theorem abs_cellDrift_le (l : ℝ) (a b : ℝ) (s : ℝ) : |cellDrift l a b s| ≤ l ^ 2 / 2 := by
  classical
  rw [cellDrift, abs_mul, abs_pow]
  have hind : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s| ≤ 1 := by
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]; norm_num
    · rw [Set.indicator_of_notMem hs]; norm_num
  have h1 : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s| ^ 2 ≤ 1 :=
    (pow_le_pow_left₀ (abs_nonneg _) hind 2).trans (by norm_num)
  have h2 : |-(l ^ 2) / 2| = l ^ 2 / 2 := by
    rw [abs_div, abs_neg, abs_of_nonneg (sq_nonneg l)]
    norm_num
  rw [h2]
  nlinarith [sq_nonneg l, abs_nonneg ((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s)]

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **A paired cell identity in the form the recombination consumes.** Given the identity for a
bounded component `Y` of the character with the strict-past component `Ym`, Fubini and the almost
sure agreement of `Ym` with `Y` at each positive time put the drift term over the time interval
and the compensator term over the window. -/
theorem cellPart_of_paired
    (hX : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {A : Set E} (hAν : ν A ≠ ⊤)
    {Y Ym : ℝ → Ω → ℝ} (hYmm : Measurable (Function.uncurry fun ω s => Ym s ω))
    (hYmb : ∀ s ω, |Ym s ω| ≤ 1)
    (hYY : ∀ s, 0 < s → ∀ᵐ ω ∂P, Ym s ω = Y s ω)
    {K : Ω → ℝ → E → ℝ} (hKm : Measurable fun p : Ω × ℝ × E => K p.1 p.2.1 p.2.2)
    {MK : ℝ} (hKb : ∀ ω s e, |K ω s e| ≤ MK)
    (hZ1 : Integrable Z P) (hVm : Measurable V) (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ}
    (hbase : ∫ ω, Z ω * V ω * (g (l * X t ω) * Y t ω) ∂P
      = ∫ ω, Z ω * V ω * (g (l * X 0 ω) * Y 0 ω) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            Ym s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * K ω q.1 q.2 ∂(referenceIntensity ν)) ∂P) :
    cellPart P Z V l X g Y t
      = cellPart P Z V l X g Y 0
        + ∫ s in Set.Ioc (0 : ℝ) t, cellDrift l a b s * cellPart P Z V l X g Y s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            (∫ ω, Z ω * V ω * (g (l * X q.1 ω) * K ω q.1 q.2) ∂P)
            ∂(referenceIntensity ν) := by
  have hdrift := integral_mul_setIntegral_drift hX l hgc hgb hYmm hYmb hZ1
    hVm.aestronglyMeasurable hMv0 hVb t
  have hjump := integral_mul_setIntegral_jump (X := X) hX.measurable_uncurry l hgc hgb hAν
    hKm hKb hZ1 hVm.aestronglyMeasurable hMv0 hVb t
  have hswap : ∫ s in Set.Ioc (0 : ℝ) t, ∫ ω, Z ω * V ω *
        (Ym s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) t,
          cellDrift l a b s * cellPart P Z V l X g Y s ∂volume := by
    refine setIntegral_congr_ae measurableSet_Ioc (Filter.Eventually.of_forall fun s hs => ?_)
    have hcongr : ∫ ω, Z ω * V ω *
          (Ym s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P
        = ∫ ω, Z ω * V ω *
          (Y s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hYY s hs.1] with ω hω
      rw [hω]
    rw [hcongr, integral_mul_trigDriftCell (Z := Z) (V := V) l g Y s]
    rfl
  rw [cellPart, hbase, hdrift, hjump, hswap]
  rfl

end Reduced

section Identity

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {ι : Type*} [Fintype ι]

include hℱN hℱW in
/-- **The real part of the cell identity, in the recombination's form.** -/
theorem cellPart_identity_re
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) t
      = cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) 0
        + ∫ s in Set.Ioc (0 : ℝ) t, cellDrift l a b s
            * cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            (∫ ω, Z ω * V ω * (g (l * X q.1 ω) * charRe N w Bfam A T ω q.1 q.2) ∂P)
            ∂(referenceIntensity ν) := by
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  refine cellPart_of_paired hXbase hgc hgb hAν
    (Ym := fun s ω => (charStrictPred N w Bfam A T e₀ s ω).re)
    (Complex.measurable_re.comp (measurable_uncurry_charStrictPred N w hℱN hBm hA hAν T e₀))
    (fun s ω => abs_charStrictPred_re_le N w Bfam A T e₀ s ω) (fun s hs => ?_)
    (measurable_charRe N hℱN w hBm hA hAν hBsub') (abs_charRe_le N w Bfam A T)
    (hZ2.integrable one_le_two) ((hVa.mono (ℱ.le a)).measurable) hMv0 hVb
    (paired_cell_re N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b hmg hpg hqg hito
      hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT)
  filter_upwards [ae_charStrictPred_eq_charAt N w hBm hT hbT hBsub0 he₀ hs] with ω hω
  rw [hω]

include hℱN hℱW in
/-- **The imaginary part of the cell identity, in the recombination's form.** -/
theorem cellPart_identity_im
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) t
      = cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) 0
        + ∫ s in Set.Ioc (0 : ℝ) t, cellDrift l a b s
            * cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            (∫ ω, Z ω * V ω * (g (l * X q.1 ω) * charIm N w Bfam A T ω q.1 q.2) ∂P)
            ∂(referenceIntensity ν) := by
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  refine cellPart_of_paired hXbase hgc hgb hAν
    (Ym := fun s ω => (charStrictPred N w Bfam A T e₀ s ω).im)
    (Complex.measurable_im.comp (measurable_uncurry_charStrictPred N w hℱN hBm hA hAν T e₀))
    (fun s ω => abs_charStrictPred_im_le N w Bfam A T e₀ s ω) (fun s hs => ?_)
    (measurable_charIm N hℱN w hBm hA hAν hBsub') (abs_charIm_le N w Bfam A T)
    (hZ2.integrable one_le_two) ((hVa.mono (ℱ.le a)).measurable) hMv0 hVb
    (paired_cell_im N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b hmg hpg hqg hito
      hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT)
  filter_upwards [ae_charStrictPred_eq_charAt N w hBm hT hbT hBsub0 he₀ hs] with ω hω
  rw [hω]

include hℱN hℱW in
/-- **The cell identity for the complex half.** The four real identities recombine into one
identity for the pairing against the Poisson character, with the deterministic drift factor over
the time interval and the mark factor over the window. -/
theorem cellHalf_identity
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    cellHalf N w Bfam Z V l X g t
      = cellHalf N w Bfam Z V l X g 0
        + ∫ s in Set.Ioc (0 : ℝ) t,
            (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1
            ∂(referenceIntensity ν) := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  have hWm : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hKI : IntegrableOn (fun s => cellHalf N w Bfam Z V l X g s) (Set.Icc (0 : ℝ) T) volume :=
    integrableOn_cellHalf N hℱN w hBm hA hAν hT hbT hBsub0 he₀ hZ2 hVm hMv0 hVb hgc hgb hXm T
  have hKt : IntegrableOn (fun s => cellHalf N w Bfam Z V l X g s) (Set.Ioc (0 : ℝ) t) volume :=
    hKI.mono_set (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hcm : Measurable fun s : ℝ => ((cellDrift l a b s : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.indicator measurableSet_Ioc).pow_const 2)
  have hdI : IntegrableOn
      (fun s => (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s)
      (Set.Ioc (0 : ℝ) t) volume :=
    hKt.bdd_mul (c := l ^ 2 / 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cellDrift_le l a b s)
  have hWI : IntegrableOn
      (fun q : ℝ × E => markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) :=
    (integrableOn_prod_of_time_complex hKt hAν).bdd_mul (c := 2)
      (measurable_markFactor w hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_markFactor_le w Bfam q)
  have hPre : ∀ s, cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).re) s
      = (cellHalf N w Bfam Z V l X g s).re := fun s =>
    cellPart_eq_cellHalf_re N w hBm hZ2 hVm hVb hgc hgb (hXbase.measurable s)
  have hPim : ∀ s, cellPart P Z V l X g (fun s ω => (charAt N w Bfam s ω).im) s
      = (cellHalf N w Bfam Z V l X g s).im := fun s =>
    cellPart_eq_cellHalf_im N w hBm hZ2 hVm hVb hgc hgb (hXbase.measurable s)
  have hJre : Set.EqOn
      (fun q : ℝ × E => ∫ ω, Z ω * V ω * (g (l * X q.1 ω) * charRe N w Bfam A T ω q.1 q.2) ∂P)
      (fun q : ℝ × E => (markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1).re)
      (Set.Ioc (0 : ℝ) t ×ˢ A) := by
    rintro ⟨s, e⟩ ⟨hs, he⟩
    exact integral_mul_charRe_eq N hℱN w hBm hA hAν hBsub' hZ2 hVm hVb hgc hgb hs.1
      (hs.2.trans htT) he (hXbase.measurable s)
  have hJim : Set.EqOn
      (fun q : ℝ × E => ∫ ω, Z ω * V ω * (g (l * X q.1 ω) * charIm N w Bfam A T ω q.1 q.2) ∂P)
      (fun q : ℝ × E => (markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1).im)
      (Set.Ioc (0 : ℝ) t ×ˢ A) := by
    rintro ⟨s, e⟩ ⟨hs, he⟩
    exact integral_mul_charIm_eq N hℱN w hBm hA hAν hBsub' hZ2 hVm hVb hgc hgb hs.1
      (hs.2.trans htT) he (hXbase.measurable s)
  have hre := cellPart_identity_re N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b
    hmg hpg hqg hito hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  have him := cellPart_identity_im N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b
    hmg hpg hqg hito hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  rw [setIntegral_congr_fun hWm hJre] at hre
  rw [setIntegral_congr_fun hWm hJim] at him
  simp only [hPre] at hre
  simp only [hPim] at him
  have hdre : (∫ s in Set.Ioc (0 : ℝ) t,
        (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s ∂volume).re
      = ∫ s in Set.Ioc (0 : ℝ) t,
          cellDrift l a b s * (cellHalf N w Bfam Z V l X g s).re ∂volume := by
    have h : ∫ s in Set.Ioc (0 : ℝ) t,
          ((cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s).re ∂volume
        = (∫ s in Set.Ioc (0 : ℝ) t,
          (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s ∂volume).re := integral_re hdI
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hdim : (∫ s in Set.Ioc (0 : ℝ) t,
        (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s ∂volume).im
      = ∫ s in Set.Ioc (0 : ℝ) t,
          cellDrift l a b s * (cellHalf N w Bfam Z V l X g s).im ∂volume := by
    have h : ∫ s in Set.Ioc (0 : ℝ) t,
          ((cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s).im ∂volume
        = (∫ s in Set.Ioc (0 : ℝ) t,
          (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X g s ∂volume).im := integral_im hdI
    rw [← h]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  have hWre : (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1 ∂(referenceIntensity ν)).re
      = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          (markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1).re
          ∂(referenceIntensity ν) := (integral_re hWI).symm
  have hWim : (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1 ∂(referenceIntensity ν)).im
      = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          (markFactor w Bfam q * cellHalf N w Bfam Z V l X g q.1).im
          ∂(referenceIntensity ν) := (integral_im hWI).symm
  refine Complex.ext ?_ ?_
  · rw [Complex.add_re, Complex.add_re, hdre, hWre]
    exact hre
  · rw [Complex.add_im, Complex.add_im, hdim, hWim]
    exact him

include hℱN hℱW in
/-- **The cell identity for the complex pairing.** Combining the cosine and sine halves, the
pairing of the weight and the bounded factor with the product of the Brownian and Poisson cell
characters satisfies the integral equation the Grönwall argument consumes. -/
theorem cellPairing_identity
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    cellPairing N w Bfam Z V l X t
      = cellPairing N w Bfam Z V l X 0
        + ∫ s in Set.Ioc (0 : ℝ) t,
            (cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s ∂volume
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1
            ∂(referenceIntensity ν) := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hgc' : Continuous fun x : ℝ => -l * Real.sin (l * x) :=
    continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id))
  have hgs' : Continuous fun x : ℝ => l * Real.cos (l * x) :=
    continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))
  have hmgc := measurable_trig_integrand hXbase hgc'
  have hpgc := progressivelyMeasurable_trig_integrand hXbase hgc'
  have hqgc : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(-l * Real.sin (l * X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' hT' => lintegral_sq_trig_integrand_lt_top (P := P) (X := X) (a := a) (b := b)
      (LevyStochCalc.Analysis.abs_neg_mul_sin_scaled_le l) (abs_nonneg l) T' hT'
  have hmgs := measurable_trig_integrand hXbase hgs'
  have hpgs := progressivelyMeasurable_trig_integrand hXbase hgs'
  have hqgs : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(l * Real.cos (l * X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' hT' => lintegral_sq_trig_integrand_lt_top (P := P) (X := X) (a := a) (b := b)
      (LevyStochCalc.Analysis.abs_mul_cos_scaled_le l) (abs_nonneg l) T' hT'
  have hC := cellHalf_identity N hℱN W hℱW hXbase hX0 ha hab l Real.continuous_cos
    Real.abs_cos_le_one hgc' (LevyStochCalc.Analysis.abs_neg_mul_sin_scaled_le l)
    hmgc hpgc hqgc
    (fun T' hT' => itoFormula_cos_scaled zero_le_one (indIoc_le_one a b) hXbase l
      hmgc hpgc hqgc hT')
    hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  have hS := cellHalf_identity N hℱN W hℱW hXbase hX0 ha hab l Real.continuous_sin
    Real.abs_sin_le_one hgs' (LevyStochCalc.Analysis.abs_mul_cos_scaled_le l)
    hmgs hpgs hqgs
    (fun T' hT' => itoFormula_sin_scaled zero_le_one (indIoc_le_one a b) hXbase l
      hmgs hpgs hqgs hT')
    hT hbT hA hAν w hBm hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT
  have hcm : Measurable fun s : ℝ => ((cellDrift l a b s : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.indicator measurableSet_Ioc).pow_const 2)
  have hKt : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun s => cellHalf N w Bfam Z V l X h s) (Set.Ioc (0 : ℝ) t) volume := by
    intro h hhc hhb
    exact (integrableOn_cellHalf N hℱN w hBm hA hAν hT hbT hBsub0 he₀ hZ2 hVm hMv0 hVb
      hhc hhb hXm T).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hdI : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun s => (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X h s)
        (Set.Ioc (0 : ℝ) t) volume := fun h hhc hhb =>
    (hKt h hhc hhb).bdd_mul (c := l ^ 2 / 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cellDrift_le l a b s)
  have hWI : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun q : ℝ × E => markFactor w Bfam q * cellHalf N w Bfam Z V l X h q.1)
        (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) := fun h hhc hhb =>
    (integrableOn_prod_of_time_complex (hKt h hhc hhb) hAν).bdd_mul (c := 2)
      (measurable_markFactor w hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_markFactor_le w Bfam q)
  have hsplit : ∀ s, cellPairing N w Bfam Z V l X s
      = cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * cellHalf N w Bfam Z V l X Real.sin s := fun s =>
    cellPairing_eq_halves N w hBm hZ2 hVm hVb (hXbase.measurable s)
  have hD : ∫ s in Set.Ioc (0 : ℝ) t,
        (cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s ∂volume
      = (∫ s in Set.Ioc (0 : ℝ) t,
          (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X Real.cos s ∂volume)
        + Complex.I * ∫ s in Set.Ioc (0 : ℝ) t,
          (cellDrift l a b s : ℂ) * cellHalf N w Bfam Z V l X Real.sin s ∂volume := by
    simp_rw [hsplit, mul_add, ← mul_assoc, mul_comm (cellDrift l a b _ : ℂ) Complex.I,
      mul_assoc]
    rw [integral_add (hdI Real.cos Real.continuous_cos Real.abs_cos_le_one)
      ((hdI Real.sin Real.continuous_sin Real.abs_sin_le_one).const_mul Complex.I),
      MeasureTheory.integral_const_mul]
  have hW : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1 ∂(referenceIntensity ν)
      = (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          markFactor w Bfam q * cellHalf N w Bfam Z V l X Real.cos q.1
          ∂(referenceIntensity ν))
        + Complex.I * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          markFactor w Bfam q * cellHalf N w Bfam Z V l X Real.sin q.1
          ∂(referenceIntensity ν) := by
    simp_rw [hsplit, mul_add, ← mul_assoc, mul_comm (markFactor w Bfam _) Complex.I, mul_assoc]
    rw [integral_add (hWI Real.cos Real.continuous_cos Real.abs_cos_le_one)
      ((hWI Real.sin Real.continuous_sin Real.abs_sin_le_one).const_mul Complex.I),
      MeasureTheory.integral_const_mul]
  rw [hsplit t, hsplit 0, hC, hS, hD, hW]
  ring

include hℱN hℱW in
/-- **The Grönwall bound for the cell pairing.** The pairing at `t` is bounded by its value at
the origin plus a constant times the integral of its norm over `(0, t]`. -/
theorem norm_cellPairing_le
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ‖cellPairing N w Bfam Z V l X t‖
      ≤ ‖cellPairing N w Bfam Z V l X 0‖
        + (l ^ 2 / 2 + 2 * (ν A).toReal)
          * ∫ s in Set.Ioc (0 : ℝ) t, ‖cellPairing N w Bfam Z V l X s‖ ∂volume := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hcm : Measurable fun s : ℝ => ((cellDrift l a b s : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    exact measurable_const.mul ((measurable_const.indicator measurableSet_Ioc).pow_const 2)
  have hKt : ∀ h : ℝ → ℝ, Continuous h → (∀ x, |h x| ≤ 1) →
      IntegrableOn (fun s => cellHalf N w Bfam Z V l X h s) (Set.Ioc (0 : ℝ) t) volume := by
    intro h hhc hhb
    exact (integrableOn_cellHalf N hℱN w hBm hA hAν hT hbT hBsub0 he₀ hZ2 hVm hMv0 hVb
      hhc hhb hXm T).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl htT))
  have hsplit : ∀ s, cellPairing N w Bfam Z V l X s
      = cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * cellHalf N w Bfam Z V l X Real.sin s := fun s =>
    cellPairing_eq_halves N w hBm hZ2 hVm hVb (hXbase.measurable s)
  have hUt : IntegrableOn (fun s => cellPairing N w Bfam Z V l X s)
      (Set.Ioc (0 : ℝ) t) volume := by
    have hc := hKt Real.cos Real.continuous_cos Real.abs_cos_le_one
    have hs := hKt Real.sin Real.continuous_sin Real.abs_sin_le_one
    exact (hc.add (hs.const_mul Complex.I)).congr
      (Filter.Eventually.of_forall fun s => (hsplit s).symm)
  have hUn : IntegrableOn (fun s => ‖cellPairing N w Bfam Z V l X s‖)
      (Set.Ioc (0 : ℝ) t) volume := hUt.norm
  have hdI : IntegrableOn
      (fun s => (cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s)
      (Set.Ioc (0 : ℝ) t) volume :=
    hUt.bdd_mul (c := l ^ 2 / 2) hcm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by
        rw [Complex.norm_real, Real.norm_eq_abs]; exact abs_cellDrift_le l a b s)
  have hWn : IntegrableOn (fun q : ℝ × E => ‖cellPairing N w Bfam Z V l X q.1‖)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) :=
    integrableOn_prod_of_time (ν := ν) hUn hAν
  have hWI : IntegrableOn
      (fun q : ℝ × E => markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) :=
    (integrableOn_prod_of_time_complex hUt hAν).bdd_mul (c := 2)
      (measurable_markFactor w hBm).aestronglyMeasurable
      (Filter.Eventually.of_forall fun q => norm_markFactor_le w Bfam q)
  have hDbound : ‖∫ s in Set.Ioc (0 : ℝ) t,
        (cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s ∂volume‖
      ≤ l ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ) t,
          ‖cellPairing N w Bfam Z V l X s‖ ∂volume := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    rw [← MeasureTheory.integral_const_mul]
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => norm_nonneg _)
      (hUn.const_mul _) (Filter.Eventually.of_forall fun s => ?_)
    show ‖(cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s‖
        ≤ l ^ 2 / 2 * ‖cellPairing N w Bfam Z V l X s‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (abs_cellDrift_le l a b s) (norm_nonneg _)
  have hWbound : ‖∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1 ∂(referenceIntensity ν)‖
      ≤ 2 * (ν A).toReal * ∫ s in Set.Ioc (0 : ℝ) t,
          ‖cellPairing N w Bfam Z V l X s‖ ∂volume := by
    refine le_trans (norm_integral_le_integral_norm _) ?_
    have hstep : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          ‖markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1‖ ∂(referenceIntensity ν)
        ≤ ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          2 * ‖cellPairing N w Bfam Z V l X q.1‖ ∂(referenceIntensity ν) := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
        (hWn.const_mul 2) (Filter.Eventually.of_forall fun q => ?_)
      show ‖markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1‖
          ≤ 2 * ‖cellPairing N w Bfam Z V l X q.1‖
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (norm_markFactor_le w Bfam q) (norm_nonneg _)
    refine hstep.trans ?_
    rw [MeasureTheory.integral_const_mul, setIntegral_prod_of_time (ν := ν) hUn hAν, mul_assoc]
  calc ‖cellPairing N w Bfam Z V l X t‖
      = ‖cellPairing N w Bfam Z V l X 0
          + (∫ s in Set.Ioc (0 : ℝ) t,
              (cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s ∂volume)
          + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
              markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1
              ∂(referenceIntensity ν)‖ := by
        rw [← cellPairing_identity N hℱN W hℱW hXbase hX0 ha hab l hT hbT hA hAν w hBm
          hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb ht htT]
    _ ≤ ‖cellPairing N w Bfam Z V l X 0‖
          + ‖∫ s in Set.Ioc (0 : ℝ) t,
              (cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s ∂volume‖
          + ‖∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
              markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1
              ∂(referenceIntensity ν)‖ := norm_add₃_le
    _ ≤ ‖cellPairing N w Bfam Z V l X 0‖
          + l ^ 2 / 2 * (∫ s in Set.Ioc (0 : ℝ) t,
              ‖cellPairing N w Bfam Z V l X s‖ ∂volume)
          + 2 * (ν A).toReal * ∫ s in Set.Ioc (0 : ℝ) t,
              ‖cellPairing N w Bfam Z V l X s‖ ∂volume := by
        gcongr
    _ = ‖cellPairing N w Bfam Z V l X 0‖
          + (l ^ 2 / 2 + 2 * (ν A).toReal)
            * ∫ s in Set.Ioc (0 : ℝ) t,
              ‖cellPairing N w Bfam Z V l X s‖ ∂volume := by ring

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- At the origin the pairing is the mean of the weight against the bounded factor. -/
theorem cellPairing_zero (w : ι → ℝ) (Bfam : ι → Set (ℝ × E)) {Z V : Ω → ℝ} {l : ℝ}
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) :
    cellPairing N w Bfam Z V l X 0 = ((∫ ω, Z ω * V ω ∂P : ℝ) : ℂ) := by
  rw [cellPairing]
  have h : ∀ᵐ ω ∂P, ((Z ω * V ω : ℝ) : ℂ)
      * (Complex.exp (Complex.I * ((l * X 0 ω : ℝ) : ℂ)) * charAt N w Bfam 0 ω)
      = ((Z ω * V ω : ℝ) : ℂ) := by
    filter_upwards [hX0] with ω hω
    rw [hω, charAt_zero N w]
    simp
  rw [integral_congr_ae h]
  exact integral_ofReal

/-- The pairing is bounded uniformly in the time. -/
theorem norm_cellPairing_bound (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
    (hBm : ∀ j, MeasurableSet (Bfam j)) {Z V : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv) {l : ℝ} {s : ℝ}
    (hXs : Measurable (X s)) :
    ‖cellPairing N w Bfam Z V l X s‖ ≤ 2 * (Mv * ∫ ω, ‖Z ω‖ ∂P) := by
  rw [cellPairing_eq_halves N w hBm hZ2 hVm hVb hXs]
  refine le_trans (norm_add_le _ _) ?_
  have h1 := norm_cellHalf_le (l := l) (X := X) N w Bfam (hZ2.integrable one_le_two) hMv0 hVb
    Real.abs_cos_le_one s
  have h2 := norm_cellHalf_le (l := l) (X := X) N w Bfam (hZ2.integrable one_le_two) hMv0 hVb
    Real.abs_sin_le_one s
  rw [norm_mul, Complex.norm_I, one_mul]
  linarith

include hℱN hℱW in
/-- **The mixed cell lemma.** For a square-integrable weight orthogonal to every Itô integral and
every compensated integral, and of mean zero against a bounded factor measurable before the cell,
the pairing with the product of the Brownian and Poisson cell characters vanishes throughout the
cell. -/
theorem cellPairing_eq_zero
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b) (l : ℝ)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (hZV : ∫ ω, Z ω * V ω ∂P = 0) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, cellPairing N w Bfam Z V l X t = 0 := by
  have hVm : Measurable V := (hVa.mono (ℱ.le a)).measurable
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := hXbase.measurable_uncurry
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have hu0 : cellPairing N w Bfam Z V l X 0 = 0 := by
    rw [cellPairing_zero N w Bfam hX0, hZV, Complex.ofReal_zero]
  have hsplit : ∀ s, cellPairing N w Bfam Z V l X s
      = cellHalf N w Bfam Z V l X Real.cos s
        + Complex.I * cellHalf N w Bfam Z V l X Real.sin s := fun s =>
    cellPairing_eq_halves N w hBm hZ2 hVm hVb (hXbase.measurable s)
  have hmeas : AEStronglyMeasurable (fun s => ‖cellPairing N w Bfam Z V l X s‖)
      (volume.restrict (Set.Icc (0 : ℝ) b)) := by
    have hc := aestronglyMeasurable_cellHalf (l := l) N hℱN w hBm hA hAν hT hbT hBsub0 he₀
      hZ2 hVm Real.continuous_cos hXm b
    have hs := aestronglyMeasurable_cellHalf (l := l) N hℱN w hBm hA hAν hT hbT hBsub0 he₀
      hZ2 hVm Real.continuous_sin hXm b
    exact ((hc.add (hs.const_mul Complex.I)).congr
      (Filter.Eventually.of_forall fun s => (hsplit s).symm)).norm
  have hzero := LevyStochCalc.Analysis.eq_zero_of_le_mul_setIntegral
    (a := (0 : ℝ)) (b := b) (c := l ^ 2 / 2 + 2 * (ν A).toReal)
    (B := 2 * (Mv * ∫ ω, ‖Z ω‖ ∂P))
    (by positivity) hmeas (fun t => norm_nonneg _)
    (fun t _ => norm_cellPairing_bound (l := l) N w hBm hZ2 hVm hMv0 hVb
      (hXbase.measurable t)) ?_
  · intro t ht
    exact norm_eq_zero.mp (hzero t ht)
  · intro t ht
    rcases eq_or_lt_of_le ht.1 with h0 | h0
    · rw [← h0, hu0, norm_zero, Set.Ioc_self]
      simp
    · have hb := norm_cellPairing_le N hℱN W hℱW hXbase hX0 ha hab l hT hbT hA hAν w hBm
        hBsub he₀ hZ2 hZito hZcomp hVa hMv0 hVb h0 (ht.2.trans hbT.le)
      rw [hu0, norm_zero, zero_add] at hb
      exact hb

end Identity

end LevyStochCalc.Driver
