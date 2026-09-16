/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellFubini
import LevyStochCalc.Poisson.CharacterMarkFactor
import LevyStochCalc.Poisson.CharacterGronwall

/-!
# The pairings of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character, and equally the
cosine half plus `i` times the sine half, a half being the pairing of a trigonometric function of
the Brownian increment with the Poisson character. This file introduces those pairings together
with their integrability and boundedness, and records the cell identity for a real pairing in the
reduced form that the recombination consumes.
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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
  refine Complex.ext ?_ ?_
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      mul_zero, add_zero, zero_sub, sub_zero]
    ring
  · simp only [Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul,
      mul_zero, zero_add]

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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
  change ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charStrictPred N w Bfam A T e₀ s ω
      = ((Z ω * V ω * g (l * X s ω) : ℝ) : ℂ) * charAt N w Bfam s ω
  rw [hω]

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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

end LevyStochCalc.Driver
