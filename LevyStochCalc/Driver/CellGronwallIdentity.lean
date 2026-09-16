/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellGronwallPairing

/-!
# The cell identity and the Grönwall bound for the cell pairing

The real and the imaginary cell identities recombine into an integral equation for the pairing of
a square-integrable weight and a bounded factor with the product of the Brownian cell character
`e^{i l X_s}` and the Poisson cell character: the pairing at a time in the cell is its value at
the origin plus a deterministic drift term over the elapsed times and a mark-factor term over the
window. The Grönwall estimate that follows forces the pairing to vanish throughout the cell when
the weight is orthogonal to every Itô integral and every compensated integral and has mean zero
against the bounded factor.
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
    change ‖(cellDrift l a b s : ℂ) * cellPairing N w Bfam Z V l X s‖
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
      change ‖markFactor w Bfam q * cellPairing N w Bfam Z V l X q.1‖
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

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
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
