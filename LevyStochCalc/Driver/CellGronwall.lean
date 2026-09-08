/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellFubini
import LevyStochCalc.Poisson.CharacterMarkFactor

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

open LevyStochCalc.Poisson LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

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
  have hofReal : ∀ f : Ω → ℝ, ∫ ω, ((f ω : ℝ) : ℂ) ∂P = ((∫ ω, f ω ∂P : ℝ) : ℂ) :=
    fun _ => integral_ofReal
  rw [cellPairing]
  simp_rw [hpt]
  rw [integral_add (h1.sub h2).ofReal ((h3.add h4).ofReal.const_mul _),
    MeasureTheory.integral_const_mul, hofReal, hofReal, integral_sub h1 h2, integral_add h3 h4]
  rfl

end Parts

end LevyStochCalc.Driver
