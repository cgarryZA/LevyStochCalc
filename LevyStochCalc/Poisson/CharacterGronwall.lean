/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterFubini
import LevyStochCalc.Analysis.GronwallIterate

/-!
# The pairing with the characters satisfies a Grönwall inequality

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is a
window integral of the marks times the pairings at earlier times. Its norm is therefore bounded by
`2 ν(A)` times its own running integral, and it is a bounded measurable function of the time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Pairing

/-- The pairing of a weight with the character of the window counts up to time `s`. -/
noncomputable def charPairing (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (r : Ω → ℝ) (s : ℝ) : ℂ :=
  ∫ ω, (r ω : ℂ) * charAt N w Bfam s ω ∂P

theorem integrable_mul_charAt (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {r : Ω → ℝ}
    (hr1 : Integrable r P) (s : ℝ) :
    Integrable (fun ω => (r ω : ℂ) * charAt N w Bfam s ω) P := by
  have h := hr1.ofReal.bdd_mul (c := 1) (measurable_charAt N w hBm s).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => by
      rw [charAt, Complex.norm_exp_I_mul_ofReal])
  exact h.congr (Filter.Eventually.of_forall fun ω => mul_comm _ _)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_charPairing_le (N : PoissonRandomMeasure P ν) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    {r : Ω → ℝ} (hr1 : Integrable r P) (s : ℝ) :
    ‖charPairing N w Bfam r s‖ ≤ ∫ ω, ‖r ω‖ ∂P := by
  refine norm_integral_le_of_norm_le hr1.norm (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul, Complex.norm_real, charAt, Complex.norm_exp_I_mul_ofReal, mul_one]

/-- The pairing of an integrable weight with a unimodular exponential of a jointly measurable
integrand is a measurable function of the time. -/
theorem aestronglyMeasurable_pairing_exp {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    {r : Ω → ℝ} (hr1 : Integrable r P) (μ : Measure ℝ) [SFinite μ] :
    AEStronglyMeasurable
      (fun s => ∫ ω, (r ω : ℂ) * Complex.exp (Complex.I * (f ω s : ℂ)) ∂P) μ := by
  have hr' : AEStronglyMeasurable (fun ω => (r ω : ℂ)) P :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable hr1.aestronglyMeasurable
  have hexp : Measurable fun p : Ω × ℝ => Complex.exp (Complex.I * (f p.1 p.2 : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul (Complex.measurable_ofReal.comp hf))
  exact (hr'.comp_fst.mul hexp.aestronglyMeasurable).prod_swap.integral_prod_right'

/-- A function of the time that agrees, at every time in `(0, T]`, with the pairing of an
integrable weight against a unimodular exponential of a jointly measurable integrand is
measurable on `[0, T]`. -/
theorem aestronglyMeasurable_of_pairing_exp {f : Ω → ℝ → ℝ}
    (hf : Measurable (Function.uncurry f)) {r : Ω → ℝ} (hr1 : Integrable r P) {u : ℝ → ℂ}
    {T : ℝ} (hu : ∀ s, 0 < s → s ≤ T →
      ∫ ω, (r ω : ℂ) * Complex.exp (Complex.I * (f ω s : ℂ)) ∂P = u s) :
    AEStronglyMeasurable u (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  refine (aestronglyMeasurable_pairing_exp hf hr1 (volume.restrict (Set.Icc (0 : ℝ) T))).congr ?_
  have h0 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
  exact hu s (lt_of_le_of_ne hs.1 hs0.symm) hs.2

/-- The pairing is, at every positive time up to `T`, a pairing against the predictable
exponential of the chain rule, hence measurable in the time. -/
theorem aestronglyMeasurable_charPairing (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {r : Ω → ℝ} (hr1 : Integrable r P) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) (hAne : A.Nonempty) :
    AEStronglyMeasurable (charPairing N w Bfam r) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  obtain ⟨e₀, he₀⟩ := hAne
  have hpm : Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
      predStrict N w (truncFam Bfam T) A T p.1 p.2.1 p.2.2 :=
    markedPredictable_predStrict N hℱ w (measurableSet_truncFam hBm T) hA hAν T
  have hpm' : Measurable fun p : Ω × ℝ × E =>
      predStrict N w (truncFam Bfam T) A T p.1 p.2.1 p.2.2 :=
    hpm.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl
  have hg : Measurable fun p : Ω × ℝ => (p.1, (p.2, e₀)) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  -- Elaborated without an expected type: unifying `?g ∘ ?f` against the composite would
  -- unfold `predStrict`.
  have hf := hpm'.comp hg
  exact aestronglyMeasurable_of_pairing_exp
    (f := fun ω s => predStrict N w (truncFam Bfam T) A T ω s e₀) hf hr1
    (fun s hs hsT => integral_mul_exp_predStrict N w hBm hs hsT le_rfl he₀)

theorem integrableOn_norm_charPairing (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {r : Ω → ℝ} (hr1 : Integrable r P) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) (hAne : A.Nonempty) :
    IntegrableOn (fun s => ‖charPairing N w Bfam r s‖) (Set.Icc (0 : ℝ) T) volume := by
  refine Integrable.mono' (integrable_const (∫ ω, ‖r ω‖ ∂P))
    (aestronglyMeasurable_charPairing N hℱ hr1 w hBm hA hAν T hAne).norm
    (Filter.Eventually.of_forall fun s => ?_)
  rw [norm_norm]
  exact norm_charPairing_le N w Bfam hr1 s

end Pairing

section Bound

/-- **The pairing as a window integral.** For a square-integrable weight of mean zero orthogonal to
every compensated integral, the pairing at `t` is the integral over the window of the mark times
the pairings at earlier times. -/
theorem charPairing_eq_window_integral (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    {t : ℝ} (htT : t ≤ T) :
    charPairing N w Bfam r t
      = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          charMark w Bfam t q * charPairing N w Bfam r q.1 ∂(referenceIntensity ν) := by
  have hr1 : Integrable r P := hr2.integrable one_le_two
  have h1 : charPairing N w Bfam r t = ∫ ω, (r ω : ℂ) * (charAt N w Bfam t ω - 1) ∂P := by
    have hsub : ∀ ω, (r ω : ℂ) * (charAt N w Bfam t ω - 1)
        = (r ω : ℂ) * charAt N w Bfam t ω - (r ω : ℂ) := fun ω => by ring
    simp_rw [hsub]
    have hrC : Integrable (fun ω => (r ω : ℂ)) P := hr1.ofReal
    have hz : ∫ ω, (r ω : ℂ) ∂P = 0 := by
      have : ∫ ω, (r ω : ℂ) ∂P = ((∫ ω, r ω ∂P : ℝ) : ℂ) := integral_ofReal
      rw [this, hr0]; simp
    rw [integral_sub (integrable_mul_charAt N w hBm hr1 t) hrC, hz, sub_zero]
    rfl
  rw [h1, integral_mul_charAt_sub_one N hℱ hT hr2 hperp w hBm hA hAν hBsub htT,
    integral_mul_charCompensator N hℱ hr1 w hBm hA hAν hBsub htT]
  rfl

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The function of the time alone is integrable over a window against the reference
intensity. -/
theorem integrableOn_prod_of_time {f : ℝ → ℝ} {t : ℝ} (hf : IntegrableOn f (Set.Ioc 0 t) volume)
    {A : Set E} (hAν : ν A ≠ ⊤) :
    IntegrableOn (fun q : ℝ × E => f q.1) (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) := by
  haveI : IsFiniteMeasure (ν.restrict A) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hAν⟩
  have hI : Set.Ioc (0 : ℝ) t ∩ Set.Ici 0 = Set.Ioc 0 t :=
    Set.inter_eq_left.mpr (fun x hx => le_of_lt hx.1)
  rw [IntegrableOn, referenceIntensity, ← Measure.prod_restrict,
    Measure.restrict_restrict measurableSet_Ioc, hI]
  have := hf.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : E => (1 : ℝ)) (ν.restrict A))
  simpa using this

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A window integral of a function of the time alone is the mark measure of the window times
the time integral. -/
theorem setIntegral_prod_of_time {f : ℝ → ℝ} {t : ℝ} (hf : IntegrableOn f (Set.Ioc 0 t) volume)
    {A : Set E} (hAν : ν A ≠ ⊤) :
    ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, f q.1 ∂(referenceIntensity ν)
      = (ν A).toReal * ∫ s in Set.Ioc (0 : ℝ) t, f s := by
  have hint := integrableOn_prod_of_time (ν := ν) hf hAν
  rw [referenceIntensity] at hint ⊢
  rw [setIntegral_prod _ hint]
  simp_rw [setIntegral_const, smul_eq_mul]
  have hI : Set.Ioc (0 : ℝ) t ∩ Set.Ici 0 = Set.Ioc 0 t :=
    Set.inter_eq_left.mpr fun x hx => le_of_lt hx.1
  rw [MeasureTheory.integral_const_mul, Measure.restrict_restrict measurableSet_Ioc, hI,
    measureReal_def]

/-- **The Grönwall inequality for the pairing.** -/
theorem norm_charPairing_le_integral (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    (hAne : A.Nonempty) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖charPairing N w Bfam r t‖
      ≤ 2 * (ν A).toReal * ∫ s in (0 : ℝ)..t, ‖charPairing N w Bfam r s‖ := by
  have hr1 : Integrable r P := hr2.integrable one_le_two
  have hWm : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  have hSm : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hSW : Set.Ioc (0 : ℝ) t ×ˢ A ⊆ Set.Ioc (0 : ℝ) T ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right ht.2) le_rfl
  have hUt : IntegrableOn (fun s => ‖charPairing N w Bfam r s‖) (Set.Ioc 0 t) volume :=
    (integrableOn_norm_charPairing N hℱ hr1 w hBm hA hAν T hAne).mono_set
      (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc le_rfl ht.2))
  have hUint : IntegrableOn (fun q : ℝ × E => 2 * ‖charPairing N w Bfam r q.1‖)
      (Set.Ioc (0 : ℝ) t ×ˢ A) (referenceIntensity ν) :=
    (integrableOn_prod_of_time (ν := ν) hUt hAν).const_mul 2
  calc ‖charPairing N w Bfam r t‖
      = ‖∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          charMark w Bfam t q * charPairing N w Bfam r q.1 ∂(referenceIntensity ν)‖ := by
        rw [charPairing_eq_window_integral N hℱ hT hr2 hr0 hperp w hBm hA hAν hBsub ht.2]
    _ ≤ ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          ‖charMark w Bfam t q * charPairing N w Bfam r q.1‖ ∂(referenceIntensity ν) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          (Set.Ioc (0 : ℝ) t ×ˢ A).indicator (fun q => 2 * ‖charPairing N w Bfam r q.1‖) q
          ∂(referenceIntensity ν) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun q => norm_nonneg _)
          (hUint.integrable_indicator hSm).integrableOn ?_
        rw [Filter.EventuallyLE, ae_restrict_iff' hWm]
        refine Filter.Eventually.of_forall fun q hq => ?_
        rcases le_or_gt q.1 t with hqt | hqt
        · have hqS : q ∈ Set.Ioc (0 : ℝ) t ×ˢ A := ⟨⟨hq.1.1, hqt⟩, hq.2⟩
          rw [Set.indicator_of_mem hqS, norm_mul]
          exact mul_le_mul_of_nonneg_right (norm_charMark_le w Bfam t q) (norm_nonneg _)
        · rw [charMark_eq_zero w Bfam hqt, zero_mul, norm_zero]
          exact Set.indicator_nonneg (fun q _ => by positivity) q
    _ = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, 2 * ‖charPairing N w Bfam r q.1‖
          ∂(referenceIntensity ν) := by
        rw [setIntegral_indicator hSm, Set.inter_eq_right.mpr hSW]
    _ = 2 * (ν A).toReal * ∫ s in (0 : ℝ)..t, ‖charPairing N w Bfam r s‖ := by
        rw [MeasureTheory.integral_const_mul, setIntegral_prod_of_time hUt hAν,
          intervalIntegral.integral_of_le ht.1, mul_assoc]

end Bound

end LevyStochCalc.Poisson
