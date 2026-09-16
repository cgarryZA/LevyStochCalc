/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoLocality
import LevyStochCalc.Poisson.CompensatedPullOut
import LevyStochCalc.Poisson.CompensatedCongr
import LevyStochCalc.Ito.JumpIntegrandLeftLim

/-!
# The marked integrand cut off at a stopping time

The marked process `markedStopped τ φ`, which agrees with `φ` at the times a stopping time `τ`
has not passed and vanishes afterwards, is dominated pointwise by `φ` and inherits from it joint
measurability, marked progressive measurability and finite energy; those three admissibility
properties transport along an equality of marked integrands and are stable under differences.

## Main definitions

* `markedStopped τ φ` — the marked process `φ` cut off at the stopping time `τ`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section MarkedStopped

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

/-- A marked process cut off at a stopping time. -/
noncomputable def markedStopped (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  if ((s : ℝ) : WithTop ℝ) ≤ τ ω then φ ω s e else 0

omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem abs_markedStopped_le (ω : Ω) (s : ℝ) (e : E) :
    |markedStopped τ φ ω s e| ≤ |φ ω s e| := by
  rw [markedStopped]
  split_ifs
  · exact le_rfl
  · simp

omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem markedStopped_of_le {ω : Ω} {s : ℝ} (h : ((s : ℝ) : WithTop ℝ) ≤ τ ω) (e : E) :
    markedStopped τ φ ω s e = φ ω s e := if_pos h

omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem markedStopped_of_not_le {ω : Ω} {s : ℝ} (h : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω)
    (e : E) :
    markedStopped τ φ ω s e = 0 := if_neg h

variable {τ φ}

/-- Cutting off at a stopping time preserves joint measurability. -/
theorem measurable_markedStopped (hτ : IsStoppingTime ℱ τ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => markedStopped τ φ p.1 p.2.1 p.2.2 := by
  set S : Set (Ω × ℝ × E) := {p | (p.1, p.2.1) ∈ LevyStochCalc.Probability.stoppedSet τ}
    with hS
  have hfun : (fun p : Ω × ℝ × E => markedStopped τ φ p.1 p.2.1 p.2.2)
      = S.indicator fun p => φ p.1 p.2.1 p.2.2 := by
    funext p
    by_cases hp : ((p.2.1 : ℝ) : WithTop ℝ) ≤ τ p.1
    · rw [Set.indicator_of_mem (show p ∈ S from hp)]
      exact if_pos hp
    · rw [Set.indicator_of_notMem (show p ∉ S from hp)]
      exact if_neg hp
  rw [hfun]
  exact hm.indicator ((LevyStochCalc.Probability.measurableSet_stoppedSet hτ).preimage
    (measurable_fst.prodMk measurable_snd.fst))

/-- Cutting off at a stopping time preserves marked progressive measurability. -/
theorem markedProgressivelyMeasurable_markedStopped (hτ : IsStoppingTime ℱ τ)
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (markedStopped τ φ) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  set R : Set (Ω × ℝ × E) :=
    {p | (p.1, p.2.1) ∈ LevyStochCalc.Probability.stoppedRegion τ t} with hR
  have key : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => markedStopped τ φ p.1 s p.2.2) p.2.1)
      = R.indicator fun p => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1 := by
    funext p
    by_cases h1 : p ∈ R
    · obtain ⟨h1a, h1b⟩ := h1
      rw [Set.indicator_of_mem (show p ∈ R from ⟨h1a, h1b⟩),
        Set.indicator_of_mem (show p.2.1 ∈ Set.Iic t from h1a),
        Set.indicator_of_mem (show p.2.1 ∈ Set.Iic t from h1a), markedStopped_of_le τ φ h1b]
    · rw [Set.indicator_of_notMem h1]
      by_cases h2 : p.2.1 ∈ Set.Iic t
      · have h3 : ¬ ((p.2.1 : ℝ) : WithTop ℝ) ≤ τ p.1 := fun hc => h1 ⟨h2, hc⟩
        rw [Set.indicator_of_mem h2, markedStopped_of_not_le τ φ h3]
      · rw [Set.indicator_of_notMem h2]
  rw [key]
  exact (hp t).indicator ((LevyStochCalc.Probability.measurableSet_stoppedRegion hτ t).preimage
    (measurable_fst.prodMk measurable_snd.fst))

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A marked integrand dominated pointwise by one of finite energy has finite energy. -/
theorem sq_int_global_of_abs_le {ψ : Ω → ℝ → E → ℝ}
    (h : ∀ ω s e, |ψ ω s e| ≤ |φ ω s e|)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono
    fun e => ?_) (hq T hT)
  have hle : (‖ψ ω s e‖₊ : ℝ≥0∞) ≤ (‖φ ω s e‖₊ : ℝ≥0∞) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using h ω s e
  gcongr

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The cut-off integrand has finite energy. -/
theorem sq_int_global_markedStopped
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  sq_int_global_of_abs_le (fun ω s e => abs_markedStopped_le τ φ ω s e) hq

end MarkedStopped

section Transport

variable {φ ψ : Ω → ℝ → E → ℝ}

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- Joint measurability transported along an equality of marked integrands. -/
theorem measurable_uncurry_congr [MeasurableSpace Ω] [MeasurableSpace E] (h : φ = ψ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) :
    Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by
  subst h
  exact hm

/-- Progressive measurability transported along an equality of marked integrands. -/
theorem markedProgressivelyMeasurable_congr (h : φ = ψ)
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ := by
  subst h
  exact hp

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Finite energy transported along an equality of marked integrands. -/
theorem sq_int_global_congr (h : φ = ψ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  subst h
  exact hq

/-- Differences of progressively measurable marked processes are progressively measurable. -/
theorem markedProgressivelyMeasurable_sub
    (h₁ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
    (h₂ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => φ ω s e - ψ ω s e := by
  refine markedProgressivelyMeasurable_congr ?_
    (markedProgressivelyMeasurable_add h₁
      (markedProgressivelyMeasurable_const_mul h₂ (-1 : ℝ)))
  funext ω s e
  ring

end Transport

end LevyStochCalc.Poisson.Compensated
