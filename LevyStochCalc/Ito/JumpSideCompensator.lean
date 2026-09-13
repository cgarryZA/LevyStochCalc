/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.StochasticIntegralLimit
import LevyStochCalc.Ito.AtomJumpRelation

/-!
# A predictable integrand vanishing at the atoms

On a window of finite intensity the compensated integral of a predictable integrand is the
integral against the random measure minus the integral against the reference intensity, so an
integrand vanishing at every atom of the window has compensated integral minus its compensator.
The mark sets of finite intensity exhaust the mark space, the compensated integrals of the cut
integrands converge to the compensated integral of the integrand, and the compensators converge
to the compensator, so the identity survives at infinite activity.

## Main statements

* `stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning` — the identity for an integrand
  vanishing at the atoms of every window built from the spanning sets of the mark measure. Both
  the vanishing and the integrability of the compensator are asked only on a set of sample
  points, and the conclusion holds there: an integrand that is square integrable against the
  intensity need not be integrable against it, so the compensator converges only where the
  hypothesis puts it.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSide

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated LevyStochCalc.Ito.IntegralLimit

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

omit [MeasurableSpace Ω] [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  [IsProbabilityMeasure P] in
/-- The spanning sets of the mark measure eventually contain almost every mark. -/
theorem ae_eventually_mem_spanningSets :
    ∀ᵐ e ∂ν, ∀ᶠ j in atTop, e ∉ (spanningSets ν j)ᶜ := by
  filter_upwards with e
  have he : e ∈ ⋃ j, spanningSets ν j := by
    rw [iUnion_spanningSets ν]
    trivial
  obtain ⟨j₀, hj₀⟩ := Set.mem_iUnion.mp he
  filter_upwards [eventually_ge_atTop j₀] with j hj
  simpa using monotone_spanningSets ν hj hj₀

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **An integrand vanishing at the atoms has compensated integral minus its compensator.** The
identity holds at each finite-intensity level by the pathwise form of the compensated integral,
and both sides converge as the level exhausts the mark space. -/
theorem stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hφpred : Probability.MarkedPredictable ℱ ν φ)
    (hφ0 : ∀ (ω : Ω) (s : ℝ) (e : E), s ≤ 0 → φ ω s e = 0) {T : ℝ} (hT : 0 < T) (G : Set Ω)
    (hint : ∀ᵐ ω ∂P, ω ∈ G → IntegrableOn (fun q : ℝ × E => φ ω q.1 q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hatoms : ∀ᵐ ω ∂P, ω ∈ G → ∀ j : ℕ,
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, φ ω q.1 q.2 ∂(N.N ω) = 0) :
    ∀ᵐ ω ∂P, ω ∈ G →
      Compensated.stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω
        = -∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), φ ω q.1 q.2
            ∂(referenceIntensity ν) := by
  classical
  set A : ℕ → Set E := fun j => (spanningSets ν j)ᶜ with hAdef
  have hA : ∀ j, MeasurableSet (A j) := fun j => (measurableSet_spanningSets ν j).compl
  have hAc : ∀ j, (A j)ᶜ = spanningSets ν j := fun j => compl_compl _
  -- the identity at each finite-intensity level
  have hlevel : ∀ j : ℕ, ∀ᵐ ω ∂P, ω ∈ G →
      Compensated.stochasticIntegral N ℱ hℱ (markCut (A j)ᶜ φ)
          (measurable_markCut h_meas (hA j).compl)
          (h_progMeas.indicator_mark (hA j).compl)
          (fun T' hT' => sq_markCut h_sq (A j)ᶜ T' hT') T ω
        = -∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, φ ω q.1 q.2
            ∂(referenceIntensity ν) := by
    intro j
    have hAνj : ν ((A j)ᶜ) ≠ ⊤ := by
      rw [hAc j]
      exact (measure_spanningSets_lt_top ν j).ne
    have hsupp : ∀ ω s e, e ∉ (A j)ᶜ → markCut (A j)ᶜ φ ω s e = 0 := by
      intro ω s e he
      rw [markCut_apply, Set.indicator_of_notMem he]
    have hzero : ∀ᵐ ω ∂P, ω ∈ G →
        ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (A j)ᶜ, markCut (A j)ᶜ φ ω q.1 q.2 ∂(N.N ω) = 0 := by
      filter_upwards [hatoms] with ω hω hG
      have hcongr : ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (A j)ᶜ, markCut (A j)ᶜ φ ω q.1 q.2 ∂(N.N ω)
          = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (A j)ᶜ, φ ω q.1 q.2 ∂(N.N ω) := by
        refine setIntegral_congr_fun (measurableSet_Ioc.prod (hA j).compl) fun q hq => ?_
        rw [markCut_apply, Set.indicator_of_mem hq.2]
      rw [hcongr, hAc j]
      exact hω hG j
    have hmain := stochasticIntegral_eq_neg_setIntegral_of_atoms_zero N ℱ hℱ (markCut (A j)ᶜ φ)
      (measurable_markCut h_meas (hA j).compl) (h_progMeas.indicator_mark (hA j).compl)
      (fun T' hT' => sq_markCut h_sq (A j)ᶜ T' hT') (hA j).compl
      (LevyStochCalc.Ito.JumpFormula.markedPredictable_markCut hφpred hφ0 (hA j).compl)
      hAνj hsupp hT G hzero
    filter_upwards [hmain] with ω hω hG
    rw [hω hG, hAc j]
    congr 1
    refine setIntegral_congr_fun (measurableSet_Ioc.prod (measurableSet_spanningSets ν j))
      fun q hq => ?_
    rw [markCut_apply, Set.indicator_of_mem hq.2]
  -- the two limits
  obtain ⟨k, hk, hkge, hlim⟩ := exists_seq_ae_tendsto_stochasticIntegral_markCut_compl N ℱ hℱ φ
    h_meas h_progMeas h_sq A hA ae_eventually_mem_spanningSets hT
  have hunion : ⋃ m : ℕ, Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m)
      = Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E) := by
    rw [← Set.prod_iUnion]
    congr 1
    refine Set.eq_univ_of_subset ?_ (iUnion_spanningSets ν)
    exact Set.iUnion_mono' fun m => ⟨m, monotone_spanningSets ν (hkge m)⟩
  have hmono : Monotone fun m : ℕ => Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m) := by
    intro a b hab
    exact Set.prod_mono_right (monotone_spanningSets ν (hk.monotone hab))
  have hcomp : ∀ᵐ ω ∂P, ω ∈ G → Tendsto
      (fun m => ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m), φ ω q.1 q.2
        ∂(referenceIntensity ν)) atTop
      (𝓝 (∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), φ ω q.1 q.2
        ∂(referenceIntensity ν))) := by
    filter_upwards [hint] with ω hω hG
    have := MeasureTheory.tendsto_setIntegral_of_monotone
      (μ := referenceIntensity ν) (f := fun q : ℝ × E => φ ω q.1 q.2)
      (fun m => measurableSet_Ioc.prod (measurableSet_spanningSets ν (k m))) hmono
      (by rw [hunion]; exact hω hG)
    rwa [hunion] at this
  filter_upwards [hlim, hcomp, MeasureTheory.ae_all_iff.mpr hlevel] with ω hω hcω hlω hG
  refine tendsto_nhds_unique hω ?_
  have : (fun m => Compensated.stochasticIntegral N ℱ hℱ (markCut (A (k m))ᶜ φ)
      (measurable_markCut h_meas (hA (k m)).compl)
      (h_progMeas.indicator_mark (hA (k m)).compl)
      (fun T' hT' => sq_markCut h_sq (A (k m))ᶜ T' hT') T ω)
      = fun m => -∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (k m), φ ω q.1 q.2
          ∂(referenceIntensity ν) := by
    funext m
    exact hlω (k m) hG
  rw [this]
  exact (hcω hG).neg

end LevyStochCalc.Ito.JumpSide
