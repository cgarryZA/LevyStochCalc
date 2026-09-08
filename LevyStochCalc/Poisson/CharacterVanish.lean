/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterGronwall

/-!
# The pairing with the characters vanishes

For a square-integrable weight of mean zero orthogonal to every compensated integral over the
horizon, the pairing `u(t) = 𝔼[r · χ_t]` with the character of the window counts up to `t` is
bounded by `2 ν(A)` times its own running integral, so the Grönwall iteration makes it vanish on
`[0, T]`. The weight is therefore orthogonal to the character of every finite family of window
sets inside `(0, T] × A`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- With no window at all the characters are constant, so the pairing is the mean of the
weight. -/
theorem charPairing_of_forall_eq_empty (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hB : ∀ j, Bfam j = ∅) (r : Ω → ℝ) (t : ℝ) :
    charPairing N w Bfam r t = ((∫ ω, r ω ∂P : ℝ) : ℂ) := by
  have hchar : ∀ ω, charAt N w Bfam t ω = 1 := fun ω => by simp [charAt, hB]
  rw [charPairing]
  simp_rw [hchar, mul_one]
  exact integral_ofReal

/-- **The pairing vanishes.** For a square-integrable weight of mean zero orthogonal to every
compensated integral over the horizon, the pairing with the character of the window counts
vanishes at every time in `[0, T]`. -/
theorem charPairing_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hr0 : ∫ ω, r ω ∂P = 0)
    (hperp : ∀ G : Compensated.MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, r ω * G.integral N hℱ ω ∂P = 0)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    charPairing N w Bfam r t = 0 := by
  rcases A.eq_empty_or_nonempty with hAe | hAne
  · have hB : ∀ j, Bfam j = ∅ := fun j =>
      Set.subset_empty_iff.mp (by simpa only [hAe, Set.prod_empty] using hBsub j)
    rw [charPairing_of_forall_eq_empty N w hB r t, hr0, Complex.ofReal_zero]
  · have hr1 : Integrable r P := hr2.integrable one_le_two
    exact Analysis.eq_zero_of_norm_le_integral (K := 2 * (ν A).toReal) (by positivity)
      (integrableOn_norm_charPairing N hℱ hr1 w hBm hA hAν T hAne)
      (fun s _ => norm_charPairing_le N w Bfam hr1 s)
      (fun s hs =>
        norm_charPairing_le_integral N hℱ hT hr2 hr0 hperp w hBm hA hAν hBsub hAne hs)
      t ht

end LevyStochCalc.Poisson
