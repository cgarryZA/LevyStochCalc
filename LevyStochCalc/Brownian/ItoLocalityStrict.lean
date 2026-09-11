/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoLocality

/-!
# Strict locality of the Itô integral

Two integrands that agree almost everywhere on a window have almost surely equal integrals
(`stochasticIntegralBrownian_congr_ae`), because the difference isometry turns the vanishing of
the energy of their difference into the vanishing of the second moment of the difference of the
integrals.

That upgrades the locality statement of `Brownian/ItoLocality.lean` from agreement at the times
`s ≤ τ ω` to agreement at the times `s < τ ω` (`stochasticIntegralBrownian_congr_of_lt`): the two
cut-off integrands then differ at the single time `s = τ ω`, a Lebesgue-null set of times. The
strict form is what a càdlàg path needs, since two integrands read along it can disagree exactly
at a jump time.

## Main statements

* `stochasticIntegralBrownian_congr_ae` — almost-everywhere equal integrands, almost surely
  equal integrals.
* `stochasticIntegralBrownian_congr_of_lt` — integrands agreeing strictly below a stopping time
  have the same integral at a time that stopping time has not reached.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

/-- **Integrands agreeing almost everywhere on the window have almost surely equal
integrals.** -/
theorem stochasticIntegralBrownian_congr_ae {H₁ H₂ : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry H₁)) (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂)) (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), H₁ ω s = H₂ ω s) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by
  have hiso := isometry_diff_stochasticIntegralBrownian W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hT
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
    have hinner : (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) =ᵐ[P] fun _ => 0 := by
      filter_upwards [h] with ω hω
      calc ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume
          = ∫⁻ _ in Set.Icc (0 : ℝ) T, (0 : ℝ≥0∞) ∂volume := by
            refine lintegral_congr_ae ?_
            filter_upwards [hω] with s hs
            simp [hs]
        _ = 0 := lintegral_zero
    rw [lintegral_congr_ae hinner, lintegral_zero]
  rw [hzero] at hiso
  have hmeas : AEMeasurable (fun ω => (‖stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞) ^ 2) P := by
    have h1 := (stochasticIntegralBrownian_memLp W ℱ hℱ H₁ hm₁ hp₁ hq₁ T).aestronglyMeasurable
    have h2 := (stochasticIntegralBrownian_memLp W ℱ hℱ H₂ hm₂ hp₂ hq₂ T).aestronglyMeasurable
    exact ((h1.aemeasurable.sub h2.aemeasurable).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hae := (lintegral_eq_zero_iff' hmeas).mp hiso
  filter_upwards [hae] with ω hω
  simp only [Pi.zero_apply] at hω
  have h1 : (‖stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞) = 0 := by
    by_contra hne
    exact absurd hω (pow_ne_zero 2 hne)
  have h2 : ‖stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ = 0 := by
    exact_mod_cast h1
  have h3 : stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω = 0 := by
    simpa using h2
  linarith [h3]

variable {τ : Ω → WithTop ℝ}

/-- **Integrands agreeing strictly below a stopping time have the same integral at a time that
stopping time has not reached.** The two cut-off integrands differ at the single time `s = τ ω`,
which carries no Lebesgue measure. -/
theorem stochasticIntegralBrownian_congr_of_lt
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) < τ ω → H₁ ω s = H₂ ω s)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        = stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  classical
  have e1 := stochasticIntegralBrownian_stopped_eq_of_le τ W ℱ hℱ hτ hm₁ hp₁ hq₁ ht
  have e2 := stochasticIntegralBrownian_stopped_eq_of_le τ W ℱ hℱ hτ hm₂ hp₂ hq₂ ht
  -- the cut integrands agree off the time `0` and the value of the stopping time
  have hstop : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      Probability.stopped τ H₁ ω s = Probability.stopped τ H₂ ω s := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hnull : (volume.restrict (Set.Icc (0 : ℝ) t))
        ({(0 : ℝ)} ∪ {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω}) = 0 := by
      refine measure_union_null (by simp) ?_
      rcases eq_or_ne (τ ω) ⊤ with hτω | hτω
      · have hempty : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = ∅ := by
          ext s
          simp [hτω]
        rw [hempty]
        exact measure_empty
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hτω
        have hsing : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = {r} := by
          ext s
          rw [Set.mem_setOf_eq, Set.mem_singleton_iff, ← hr]
          exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
        rw [hsing]
        simp
    filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc]
      with s hs0 hs
    have hsn : ¬ s = 0 ∧ ¬ ((s : ℝ) : WithTop ℝ) = τ ω := by
      simpa [not_or] using hs0
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsn.1)
    unfold LevyStochCalc.Probability.stopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hspos (lt_of_le_of_ne hle hsn.2)]
    · rw [if_neg hle, if_neg hle]
  have e3 := stochasticIntegralBrownian_congr_ae W ℱ hℱ
    (Probability.measurable_uncurry_stopped hτ hm₁)
    (Probability.ProgressivelyMeasurable.stopped hτ hp₁)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H₁ ω s) hq₁)
    (Probability.measurable_uncurry_stopped hτ hm₂)
    (Probability.ProgressivelyMeasurable.stopped hτ hp₂)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H₂ ω s) hq₂)
    ht hstop
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]

end LevyStochCalc.Brownian.Ito
