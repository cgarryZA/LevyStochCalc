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

end Identity

end LevyStochCalc.Driver
