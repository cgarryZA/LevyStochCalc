/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterIntegrand
import LevyStochCalc.Poisson.CompensatedRange
import LevyStochCalc.Poisson.WindowFiltration

/-!
# The character's compensated part is orthogonal to a perpendicular weight

The real and imaginary parts of the chain rule's integrand are admissible marked integrands over
the horizon, so a square-integrable weight orthogonal to every compensated integral is orthogonal
to them. What is left of the character's increment is its compensator.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Bundle

/-- The real part of the chain rule's integrand, as an admissible horizon integrand. -/
noncomputable def charReIntegrand (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Compensated.MarkedHorizonIntegrand P ν ℱ T where
  toFun := charRe N w Bfam A T
  measurable_uncurry := measurable_charRe N hℱ w hBm hA hAν hBsub
  progressive := (markedPredictable_charRe N hℱ w hBm hA hAν hBsub).markedProgressivelyMeasurable
  vanishing := fun ω s e hs =>
    charRe_eq_zero N w hBsub ω fun hmem => hs ⟨hmem.1.1.le, hmem.1.2⟩
  energy_ne_top := (sq_charRe N w hA hAν hBsub T).ne

/-- The imaginary part of the chain rule's integrand, as an admissible horizon integrand. -/
noncomputable def charImIntegrand (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    Compensated.MarkedHorizonIntegrand P ν ℱ T where
  toFun := charIm N w Bfam A T
  measurable_uncurry := measurable_charIm N hℱ w hBm hA hAν hBsub
  progressive := (markedPredictable_charIm N hℱ w hBm hA hAν hBsub).markedProgressivelyMeasurable
  vanishing := fun ω s e hs =>
    charIm_eq_zero N w hBsub ω fun hmem => hs ⟨hmem.1.1.le, hmem.1.2⟩
  energy_ne_top := (sq_charIm N w hA hAν hBsub T).ne

theorem charReIntegrand_integral (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    (charReIntegrand N hℱ w hBm hA hAν hBsub).integral N hℱ
      =ᵐ[P] Compensated.process N ℱ hℱ (charRe N w Bfam A T)
        (measurable_charRe N hℱ w hBm hA hAν hBsub)
        (markedPredictable_charRe N hℱ w hBm hA hAν hBsub).markedProgressivelyMeasurable
        (fun T' _ => sq_charRe N w hA hAν hBsub T') T :=
  Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ _ _ _ _ T

theorem charImIntegrand_integral (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) :
    (charImIntegrand N hℱ w hBm hA hAν hBsub).integral N hℱ
      =ᵐ[P] Compensated.process N ℱ hℱ (charIm N w Bfam A T)
        (measurable_charIm N hℱ w hBm hA hAν hBsub)
        (markedPredictable_charIm N hℱ w hBm hA hAν hBsub).markedProgressivelyMeasurable
        (fun T' _ => sq_charIm N w hA hAν hBsub T') T :=
  Compensated.stochasticIntegral_ae_eq_process N ℱ hℱ _ _ _ _ T

end Bundle

end LevyStochCalc.Poisson
