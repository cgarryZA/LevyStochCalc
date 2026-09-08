/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellIdentity
import LevyStochCalc.Probability.PairingFubini

/-!
# Swapping the pairing with the time and window integrals

The two surviving terms of the paired cell identity are an integral over the sample space of a
set integral: over a time interval for the drift, over a window of times and marks for the
compensator. Both are instances of `LevyStochCalc.Probability.integral_mul_setIntegral_swap`,
which lives in the measure-theoretic layer; only the instantiations are here.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Probability
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]


section Cell

variable {E : Type v} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {W : LevyStochCalc.Brownian.BrownianMotion P} {hℱW : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}
  {Z : Ω → ℝ} {V : Ω → ℝ} {Mv : ℝ}

/-- The drift term of the paired cell identity, with the time integral outside. -/
theorem integral_mul_setIntegral_drift
    (hX : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {Y : ℝ → Ω → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hYb : ∀ s ω, |Y s ω| ≤ 1)
    (hZ1 : Integrable Z P) (hVm : AEStronglyMeasurable V P) (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (t : ℝ) :
    ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
        Y s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
      = ∫ s in Set.Ioc (0 : ℝ) t, ∫ ω, Z ω * V ω *
          (Y s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P ∂volume := by
  have hgl : Continuous fun x => g (l * x) := hgc.comp (continuous_const.mul continuous_id)
  have hglb : ∀ x, |g (l * x)| ≤ 1 := fun x => hgb _
  refine integral_mul_setIntegral_swap (μ := volume) (S := Set.Ioc (0 : ℝ) t)
    (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top) hZ1 hVm hMv0 hVb
    (hYm.mul (measurable_trigDriftCell hX l hgl)) (MF := 1 * (1 / 2 * (l ^ 2 * 1))) ?_
  intro ω s
  rw [abs_mul]
  exact mul_le_mul (hYb s ω) (abs_trigDriftCell_le l hglb zero_le_one X a b ω s)
    (abs_nonneg _) zero_le_one

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The compensator term of the paired cell identity, with the window integral outside. -/
theorem integral_mul_setIntegral_jump
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {A : Set E} (hAν : ν A ≠ ⊤)
    {K : Ω → ℝ → E → ℝ} (hKm : Measurable fun p : Ω × ℝ × E => K p.1 p.2.1 p.2.2)
    {MK : ℝ} (hKb : ∀ ω s e, |K ω s e| ≤ MK)
    (hZ1 : Integrable Z P) (hVm : AEStronglyMeasurable V P) (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv) (t : ℝ) :
    ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
        g (l * X q.1 ω) * K ω q.1 q.2 ∂(referenceIntensity ν)) ∂P
      = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, ∫ ω, Z ω * V ω *
          (g (l * X q.1 ω) * K ω q.1 q.2) ∂P ∂(referenceIntensity ν) := by
  haveI : SigmaFinite (referenceIntensity ν) := by
    rw [referenceIntensity]; infer_instance
  have hXq : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  refine integral_mul_setIntegral_swap (μ := referenceIntensity ν)
    (S := Set.Ioc (0 : ℝ) t ×ˢ A) (MF := 1 * MK)
    (Poisson.referenceIntensity_Ioc_prod_ne_top hAν t) hZ1 hVm hMv0 hVb
    ((hgc.measurable.comp (measurable_const.mul hXq)).mul hKm) ?_
  intro ω q
  rw [abs_mul]
  exact mul_le_mul (hgb _) (hKb ω q.1 q.2) (abs_nonneg _) zero_le_one

omit [IsProbabilityMeasure P] in
/-- The drift factor of the paired cell identity is deterministic, so it comes out of the
pairing. -/
theorem integral_mul_trigDriftCell (l : ℝ) (g : ℝ → ℝ) (Y : ℝ → Ω → ℝ) (s : ℝ) :
    ∫ ω, Z ω * V ω * (Y s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s) ∂P
      = -(l ^ 2) / 2 * ((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s) ^ 2
        * ∫ ω, Z ω * V ω * (g (l * X s ω) * Y s ω) ∂P := by
  rw [← MeasureTheory.integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  simp only [trigDriftCell, indIoc]
  ring

end Cell

end LevyStochCalc.Driver
