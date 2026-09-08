/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterVanish
import LevyStochCalc.Brownian.AugmentedFiltration

/-!
# The predictable representation property of a Poisson random measure

A square-integrable weight of mean zero, measurable at the horizon for a filtration below the
augmented natural filtration of the random measure and orthogonal to every compensated integral
over the horizon, is orthogonal to the character of every finite family of window sets
(`charPairing_eq_zero`), so it vanishes by the separation of the window family
(`ae_eq_zero_of_integral_char_window`). Fed into the orthogonal decomposition
`Compensated.exists_markedHorizonIntegrand_of_mean_zero`, this represents every square-integrable
weight of mean zero measurable at the horizon as a compensated integral of a horizon integrand.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [IsProbabilityMeasure P]
  [SigmaFinite ν] in
/-- A finite family of window sets lies inside one window of finite mark measure. -/
theorem exists_window_of_finset (T : ℝ) (F : Finset (WindowSet E ν T)) :
    ∃ A : Set E, MeasurableSet A ∧ ν A ≠ ⊤ ∧
      ∀ D : F, ((D : WindowSet E ν T) : Set (ℝ × E)) ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := by
  choose A hA using fun D : F => (D : WindowSet E ν T).2.2
  refine ⟨⋃ D : F, A D, MeasurableSet.iUnion fun D => (hA D).1, ?_, fun D => ?_⟩
  · exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.mpr fun D _ => (hA D).2.1)
      (measure_iUnion_fintype_le ν A)
  · exact (hA D).2.2.trans (Set.prod_mono le_rfl (Set.subset_iUnion A D))

/-- **Separation by the compensated integrals.** A square-integrable weight of mean zero,
measurable at the horizon for a filtration below the augmented natural filtration and orthogonal
to every compensated integral over the horizon, vanishes almost surely. -/
theorem ae_eq_zero_of_integral_mul_compensated_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (hℱT : ℱ T ≤ Probability.aug (naturalFiltration N T) ‹MeasurableSpace Ω› P)
    {r : Ω → ℝ} (hr2 : MemLp r 2 P) (hrm : AEStronglyMeasurable[ℱ T] r P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0) :
    r =ᵐ[P] 0 := by
  have hr1 : Integrable r P := hr2.integrable one_le_two
  have hZm : AEStronglyMeasurable[Probability.aug (naturalFiltration N T) ‹MeasurableSpace Ω› P]
      (fun ω => (r ω : ℂ)) P := by
    obtain ⟨g, hg, hrg⟩ := hrm
    exact ⟨fun ω => (g ω : ℂ), Complex.continuous_ofReal.comp_stronglyMeasurable (hg.mono hℱT),
      hrg.mono fun ω h => by simp only [h]⟩
  have hZ : (fun ω => (r ω : ℂ)) =ᵐ[P] 0 := by
    refine ae_eq_zero_of_integral_char_window N T hr1.ofReal hZm fun F w => ?_
    obtain ⟨A, hA, hAν, hsub⟩ := exists_window_of_finset T F
    have hD : ∀ D : F, ((D : WindowSet E ν T) : Set (ℝ × E)) ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ
        = ((D : WindowSet E ν T) : Set (ℝ × E)) := fun D =>
      Set.inter_eq_left.mpr fun p hp => ⟨(hsub D hp).1, Set.mem_univ _⟩
    have hsum : ∀ ω, (∑ D : F, (N.N ω ((D : WindowSet E ν T) : Set (ℝ × E))).toReal * w D)
        = ∑ D : F, w D * (N.N ω (((D : WindowSet E ν T) : Set (ℝ × E))
            ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ)).toReal :=
      fun ω => Finset.sum_congr rfl fun D _ => by rw [hD D, mul_comm]
    have h0 := charPairing_eq_zero N hℱ hT hr2 hr0 hperp w
      (Bfam := fun D : F => ((D : WindowSet E ν T) : Set (ℝ × E)))
      (fun D => WindowSet.measurableSet _) hA hAν hsub ⟨hT.le, le_rfl⟩
    rw [← h0, charPairing]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    dsimp only
    rw [charAt, hsum ω, mul_comm _ Complex.I, mul_comm]
  filter_upwards [hZ] with ω hω
  simpa using hω

/-- **The predictable representation property of a Poisson random measure.** For a filtration
below the augmented natural filtration at the horizon, every square-integrable weight of mean
zero that is measurable at the horizon is a compensated integral of a horizon integrand. -/
theorem exists_markedHorizonIntegrand_of_le_aug (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (hℱT : ℱ T ≤ Probability.aug (naturalFiltration N T) ‹MeasurableSpace Ω› P)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : Compensated.MarkedHorizonIntegrand P ν ℱ T, Z =ᵐ[P] G.integral N hℱ :=
  Compensated.exists_markedHorizonIntegrand_of_mean_zero (N := N) (hℱ := hℱ) (hT := hT)
    (hsep := fun _ hr2 hrm hr0 hperp =>
      ae_eq_zero_of_integral_mul_compensated_eq_zero N hℱ hT hℱT hr2 hrm hr0 hperp)
    (hZ2 := hZ2) (hZm := hZm) (hZ0 := hZ0)

/-- The predictable representation property for the natural filtration. -/
theorem exists_markedHorizonIntegrand_natural (N : PoissonRandomMeasure P ν) {T : ℝ}
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[naturalFiltration N T] Z P) (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : Compensated.MarkedHorizonIntegrand P ν (naturalFiltration N) T,
      Z =ᵐ[P] G.integral N (isPoissonFiltration_natural N) :=
  exists_markedHorizonIntegrand_of_le_aug N (isPoissonFiltration_natural N) hT
    (Probability.le_aug ((naturalFiltration N).le T)) hZ2 hZm hZ0

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- A Poisson random measure for `ℱ` is one for the `0`-clamped augmentation of `ℱ`. -/
theorem isPoissonFiltration_augFiltration {N : PoissonRandomMeasure P ν}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsPoissonFiltration N ℱ) :
    IsPoissonFiltration N (Brownian.augFiltration ℱ P) where
  measurable _ _ hB hBm := (h.measurable hB hBm).mono (Brownian.le_augFiltration ℱ P _) le_rfl
  indep s t hs hst A hA hAν := by
    have hfeq : Brownian.augFiltration ℱ P s = Probability.aug (ℱ s) ‹MeasurableSpace Ω› P := by
      change Probability.aug (ℱ (max s 0)) ‹MeasurableSpace Ω› P = _
      rw [max_eq_left hs]
    rw [hfeq]
    exact Probability.indep_aug P (h.indep hs hst hA hAν)

/-- The predictable representation property for the augmented natural filtration. -/
theorem exists_markedHorizonIntegrand_augFiltration (N : PoissonRandomMeasure P ν) {T : ℝ}
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration (naturalFiltration N) P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : Compensated.MarkedHorizonIntegrand P ν (Brownian.augFiltration (naturalFiltration N) P) T,
      Z =ᵐ[P] G.integral N (isPoissonFiltration_augFiltration (isPoissonFiltration_natural N)) :=
  exists_markedHorizonIntegrand_of_le_aug N _ hT
    (by change Probability.aug (naturalFiltration N (max T 0)) ‹MeasurableSpace Ω› P ≤ _
        rw [max_eq_left hT.le]) hZ2 hZm hZ0

end LevyStochCalc.Poisson
