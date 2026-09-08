/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.PredictableContinuous
import LevyStochCalc.Poisson.CompensatedRange
import LevyStochCalc.Poisson.PathwiseIdentity

/-!
# A continuous adapted factor in a marked integrand

A bounded continuous adapted process, cut to a window of finite mark measure, multiplies a
predictable marked integrand carried by that window into another one: the product is predictable
(`Probability/PredictableContinuous.lean`), vanishes off the horizon and has finite energy. Since
the product is predictable it is pathwise, so on the window the integral of the product against
the random measure is its compensated integral plus its integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Cut

/-- A process cut to a window of the time–mark space. -/
noncomputable def cutWindow (X : ℝ → Ω → ℝ) (A : Set E) (τ : ℝ) (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  (Set.Ioc (0 : ℝ) τ ×ˢ A).indicator (fun _ : ℝ × E => X s ω) (s, e)

omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem cutWindow_eq_zero {X : ℝ → Ω → ℝ} {A : Set E} {τ : ℝ} {s : ℝ} {e : E}
    (h : ((s, e) : ℝ × E) ∉ Set.Ioc (0 : ℝ) τ ×ˢ A) (ω : Ω) : cutWindow X A τ ω s e = 0 :=
  Set.indicator_of_notMem h _

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Shrinking the domain of a set integral to where the integrand lives. -/
theorem setIntegral_eq_of_vanishing {μ : Measure (ℝ × E)} {S S' : Set (ℝ × E)}
    (hS : MeasurableSet S) (hSS' : S ⊆ S') {f : ℝ × E → ℝ}
    (hf : ∀ q ∈ S', q ∉ S → f q = 0) (hS'm : MeasurableSet S') :
    ∫ q in S', f q ∂μ = ∫ q in S, f q ∂μ := by
  have hcongr : ∫ q in S', f q ∂μ = ∫ q in S', S.indicator f q ∂μ := by
    refine setIntegral_congr_fun hS'm fun q hq => ?_
    by_cases hqS : q ∈ S
    · rw [Set.indicator_of_mem hqS]
    · rw [Set.indicator_of_notMem hqS, hf q hq hqS]
  rw [hcongr, setIntegral_indicator hS, Set.inter_eq_right.mpr hSS']

omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem cutWindow_eq {X : ℝ → Ω → ℝ} {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T) {e : E}
    (he : e ∈ A) (ω : Ω) : cutWindow X A T ω s e = X s ω := by
  have hmem : ((s, e) : ℝ × E) ∈ Set.Ioc (0 : ℝ) T ×ˢ A := ⟨⟨hs, hsT⟩, he⟩
  exact Set.indicator_of_mem hmem _

omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem abs_cutWindow_le {X : ℝ → Ω → ℝ} {C : ℝ} (hC0 : 0 ≤ C) (hX : ∀ s ω, |X s ω| ≤ C)
    (A : Set E) (T : ℝ) (ω : Ω) (s : ℝ) (e : E) : |cutWindow X A T ω s e| ≤ C := by
  unfold cutWindow
  by_cases h : ((s, e) : ℝ × E) ∈ Set.Ioc (0 : ℝ) T ×ˢ A
  · rw [Set.indicator_of_mem h]; exact hX s ω
  · rw [Set.indicator_of_notMem h, abs_zero]; exact hC0

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
theorem measurable_uncurry_cutWindow {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) {A : Set E} (hA : MeasurableSet A)
    (T : ℝ) :
    Measurable fun p : Ω × ℝ × E => cutWindow X A T p.1 p.2.1 p.2.2 := by
  have h1 : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_fst.prodMk measurable_snd.fst)
  have h2 : MeasurableSet ((Set.Ioc (0 : ℝ) T ×ˢ A : Set (ℝ × E))) :=
    measurableSet_Ioc.prod hA
  have h3 : Measurable fun p : Ω × ℝ × E => ((p.2.1, p.2.2) : ℝ × E) :=
    measurable_snd.fst.prodMk measurable_snd.snd
  exact h1.indicator (h3 h2)

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A factor bounded by `C` scales the energy by at most `C²`. -/
theorem markedEnergy_bddMul_ne_top {φ ψ : Ω → ℝ → E → ℝ} {C T : ℝ}
    (hψ : ∀ ω s e, |ψ ω s e| ≤ C) (h : markedEnergy P ν T φ ≠ ⊤) :
    markedEnergy P ν T (fun ω s e => ψ ω s e * φ ω s e) ≠ ⊤ := by
  have hC : ENNReal.ofReal (C ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hC h) ?_
  unfold markedEnergy
  rw [← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun ω => ?_
  rw [← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun s => ?_
  rw [← lintegral_const_mul' _ _ hC]
  refine lintegral_mono fun e => ?_
  rw [coe_nnnorm_sq_eq_ofReal_sq, coe_nnnorm_sq_eq_ofReal_sq,
    ← ENNReal.ofReal_mul (sq_nonneg C)]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [mul_pow, ← sq_abs (ψ ω s e)]
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (abs_nonneg _) (hψ ω s e) 2) (sq_nonneg _)

namespace MarkedHorizonIntegrand

variable {T : ℝ}

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The cut factor times a predictable integrand is predictable. -/
theorem markedPredictable_cutMul {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {φ : Ω → ℝ → E → ℝ}
    (hφ : Probability.MarkedPredictable ℱ ν φ) (T : ℝ) :
    Probability.MarkedPredictable ℱ ν fun ω s e => cutWindow X A T ω s e * φ ω s e :=
  (Probability.markedPredictable_of_continuous_adapted hXc hXa hA hAν T).mul hφ

/-- A bounded continuous adapted process, cut to the window, times an admissible marked
integrand. -/
noncomputable def cutMul (G : MarkedHorizonIntegrand P ν ℱ T) {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {C : ℝ} (hC0 : 0 ≤ C) (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun) (τ : ℝ) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => cutWindow X A τ ω s e * G.toFun ω s e
  measurable_uncurry := by
    have hXjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) := by
      have h : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => X t ω) :=
        measurable_uncurry_of_continuous_of_measurable (fun ω => hXc ω)
          (fun t => ((hXa t).mono (ℱ.le t)).measurable)
      exact h.comp measurable_swap
    exact (measurable_uncurry_cutWindow hXjoint hA τ).mul G.measurable_uncurry
  progressive := (markedPredictable_cutMul hXc hXa hA hAν hGpred τ).markedProgressivelyMeasurable
  vanishing := fun ω s e hs => by rw [G.vanishing ω s e hs, mul_zero]
  energy_ne_top := markedEnergy_bddMul_ne_top (abs_cutWindow_le hC0 hXb A τ) G.energy_ne_top

/-- **The window integral of a continuous adapted factor against the random measure.** For a
bounded continuous adapted `X` and a predictable admissible integrand `G` carried by the window,
the integral of `X · G` against the random measure over the window is the compensated integral of
the cut product plus its integral against the reference intensity. -/
theorem setIntegral_count_eq_integral_add (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (G : MarkedHorizonIntegrand P ν ℱ T) {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {C : ℝ} (hC0 : 0 ≤ C) (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun) (hT : 0 < T)
    {τ : ℝ} (hτT : τ ≤ T) :
    ∀ᵐ ω ∂P, (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω))
      = (G.cutMul hXc hXa hC0 hXb hA hAν hGpred τ).integral N hℱ ω
        + ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
            X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν) := by
  set F := G.cutMul hXc hXa hC0 hXb hA hAν hGpred τ with hF
  have hsupp : ∀ (ω : Ω) (s : ℝ) (e : E), e ∉ A → F.toFun ω s e = 0 := by
    intro ω s e he
    have : cutWindow X A τ ω s e = 0 :=
      Set.indicator_of_notMem (fun hmem => he hmem.2) _
    change cutWindow X A τ ω s e * G.toFun ω s e = 0
    rw [this, zero_mul]
  have hpath := stochasticIntegral_ae_eq_pathwise N ℱ hℱ F.toFun F.measurable_uncurry
    F.progressive F.sq_int_global hA
    (markedPredictable_cutMul hXc hXa hA hAν hGpred τ) hAν hsupp hT
  have hWm : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  have hSm : MeasurableSet (Set.Ioc (0 : ℝ) τ ×ˢ A) := measurableSet_Ioc.prod hA
  have hSS : (Set.Ioc (0 : ℝ) τ ×ˢ A : Set (ℝ × E)) ⊆ Set.Ioc (0 : ℝ) T ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right hτT) le_rfl
  have hcongr : ∀ (μ : Measure (ℝ × E)) (ω : Ω),
      (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, F.toFun ω q.1 q.2 ∂μ)
        = ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, X q.1 ω * G.toFun ω q.1 q.2 ∂μ := by
    intro μ ω
    have hshrink : (∫ q in Set.Ioc (0 : ℝ) T ×ˢ A, F.toFun ω q.1 q.2 ∂μ)
        = ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, F.toFun ω q.1 q.2 ∂μ := by
      refine setIntegral_eq_of_vanishing hSm hSS (fun q _ hq => ?_) hWm
      change cutWindow X A τ ω q.1 q.2 * G.toFun ω q.1 q.2 = 0
      rw [cutWindow_eq_zero (by simpa using hq) ω, zero_mul]
    rw [hshrink]
    refine setIntegral_congr_fun hSm fun q hq => ?_
    change cutWindow X A τ ω q.1 q.2 * G.toFun ω q.1 q.2 = _
    rw [cutWindow_eq hq.1.1 hq.1.2 hq.2]
  filter_upwards [hpath] with ω hω
  have hI : F.integral N hℱ ω
      = (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A, X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω))
        - ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
            X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν) := by
    rw [MarkedHorizonIntegrand.integral, hω, hcongr (N.N ω) ω, hcongr (referenceIntensity ν) ω]
  rw [hI]
  ring

end MarkedHorizonIntegrand

end Cut

end LevyStochCalc.Poisson.Compensated
