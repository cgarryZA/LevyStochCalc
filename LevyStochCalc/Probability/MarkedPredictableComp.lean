/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpCoefficientPredictable

/-!
# Marked predictability under measurable post-composition

On the positive times the time coordinate of the time–mark space is measurable for the marked
predictable σ-algebra, a predictable process of the time and the sample point lifts to a marked
predictable one, and a marked predictable process keeps its measurability. A measurable function
of the time, a predictable process and a marked predictable process is therefore marked
predictable once it is cut to the positive times.

## Main statements

* `LevyStochCalc.Probability.measurableSet_markedPredictableSigma_time_pos` — a measurable set
  of positive times, carrying all sample points and marks, is marked predictable.
* `LevyStochCalc.Probability.measurable_markedPredictableSigma_time_pos` — the time coordinate,
  cut to the positive times, is marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_measurable` — a measurable function of the
  time, a predictable process and a marked predictable process, cut to the positive times, is
  marked predictable.
* `LevyStochCalc.Probability.MarkedPredictable.comp_continuous` — the same for a continuous
  function.

## References

* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
  {E : Type v} [MeasurableSpace E] {ν : Measure E}

section Time

/-- A measurable set of positive times, carrying all sample points and marks, is marked
predictable. -/
theorem measurableSet_markedPredictableSigma_time_pos [SigmaFinite ν] {S : Set ℝ}
    (hS : MeasurableSet S) :
    MeasurableSet[markedPredictableSigma ℱ ν] {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S} := by
  have hrw : {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S}
      = (Set.univ : Set Ω) ×ˢ ((S ×ˢ (Set.univ : Set E))
          ∩ Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set E)) := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and, and_true,
      Set.mem_inter_iff, Set.mem_Ioi]
    exact and_comm
  rw [hrw]
  exact measurableSet_markedPredictableSigma_univ_prod_pos (hS.prod MeasurableSet.univ)

/-- A function on the time–mark space whose level sets, cut to the positive times, are marked
predictable is marked predictable once it is cut to the positive times. -/
theorem measurable_markedPredictableSigma_ite_pos [SigmaFinite ν] {G : Type*}
    [MeasurableSpace G] [Zero G] {g : Ω × ℝ × E → G}
    (hg : ∀ U : Set G, MeasurableSet U →
      MeasurableSet[markedPredictableSigma ℱ ν] (g ⁻¹' U ∩ {p : Ω × ℝ × E | 0 < p.2.1})) :
    Measurable[markedPredictableSigma ℱ ν]
      fun p : Ω × ℝ × E => if 0 < p.2.1 then g p else 0 := by
  classical
  have hpos := measurableSet_markedPredictableSigma_pos (Ω := Ω) (E := E) ℱ ν
  intro U hU
  have hkey := hg U hU
  by_cases h0 : (0 : G) ∈ U
  · have hrw : (fun p : Ω × ℝ × E => if 0 < p.2.1 then g p else 0) ⁻¹' U
        = (g ⁻¹' U ∩ {p : Ω × ℝ × E | 0 < p.2.1}) ∪ {p : Ω × ℝ × E | 0 < p.2.1}ᶜ := by
      ext p
      by_cases hp : 0 < p.2.1 <;> simp [hp, h0]
    rw [hrw]
    exact hkey.union hpos.compl
  · have hrw : (fun p : Ω × ℝ × E => if 0 < p.2.1 then g p else 0) ⁻¹' U
        = g ⁻¹' U ∩ {p : Ω × ℝ × E | 0 < p.2.1} := by
      ext p
      by_cases hp : 0 < p.2.1 <;> simp [hp, h0]
    rw [hrw]
    exact hkey

/-- The time coordinate of the time–mark space, cut to the positive times, is marked
predictable. -/
theorem measurable_markedPredictableSigma_time_pos [SigmaFinite ν] :
    Measurable[markedPredictableSigma ℱ ν]
      fun p : Ω × ℝ × E => if 0 < p.2.1 then p.2.1 else 0 :=
  measurable_markedPredictableSigma_ite_pos fun S hS => by
    have hrw : (fun p : Ω × ℝ × E => p.2.1) ⁻¹' S ∩ {p : Ω × ℝ × E | 0 < p.2.1}
        = {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      exact and_comm
    rw [hrw]
    exact measurableSet_markedPredictableSigma_time_pos hS

end Time

section Comp

/-- **A measurable function of the time, a predictable process and a marked predictable process
is marked predictable once it is cut to the positive times.** -/
theorem MarkedPredictable.comp_measurable [SigmaFinite ν] {F₁ : Type*} {F₂ : Type*}
    {F₃ : Type*} [MeasurableSpace F₁] [MeasurableSpace F₂] [MeasurableSpace F₃] [Zero F₃]
    {F : ℝ × F₁ × F₂ → F₃} (hF : Measurable F) {Y : Ω → ℝ → F₁}
    (hY : Measurable[predictableSigma ℱ] fun q : ℝ × Ω => Y q.2 q.1)
    {Γ : Ω → ℝ → E → F₂} (hΓ : MarkedPredictable ℱ ν Γ) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then F (s, Y ω s, Γ ω s e) else 0 := by
  classical
  have hpos := measurableSet_markedPredictableSigma_pos (Ω := Ω) (E := E) ℱ ν
  have h1 : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => p.2.1 := by
    intro S hS
    change MeasurableSet[markedPredictableSigma ℱ ν] (_ ∩ _)
    have hrw : (fun p : Ω × ℝ × E => p.2.1) ⁻¹' S ∩ {p : Ω × ℝ × E | 0 < p.2.1}
        = {p : Ω × ℝ × E | 0 < p.2.1 ∧ p.2.1 ∈ S} := by
      ext p
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq]
      exact and_comm
    rw [hrw]
    exact measurableSet_markedPredictableSigma_time_pos hS
  have h2 : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => Y p.1 p.2.1 := fun D hD =>
    measurableSet_markedPredictableSigma_of_predictableSigma (E := E) (ν := ν) (hY hD)
  have h3 : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => Γ p.1 p.2.1 p.2.2 := fun D hD => (hΓ hD).inter hpos
  have hcomp : Measurable[traceSigma (markedPredictableSigma ℱ ν) hpos]
      fun p : Ω × ℝ × E => F (p.2.1, Y p.1 p.2.1, Γ p.1 p.2.1 p.2.2) :=
    hF.comp (h1.prodMk (h2.prodMk h3))
  exact measurable_markedPredictableSigma_ite_pos fun U hU => hcomp hU

/-- **A measurable function of the time, a predictable process and a marked predictable process
is marked predictable once it is cut to the positive times**, for a predictable process in the
sense of `Predictable`. -/
theorem MarkedPredictable.comp_measurable_of_predictable [SigmaFinite ν] {F₁ : Type*}
    {F₂ : Type*} {F₃ : Type*} [TopologicalSpace F₁] [TopologicalSpace.PseudoMetrizableSpace F₁]
    [MeasurableSpace F₁] [BorelSpace F₁] [Zero F₁] [MeasurableSpace F₂] [MeasurableSpace F₃]
    [Zero F₃] {F : ℝ × F₁ × F₂ → F₃} (hF : Measurable F) {Y : Ω → ℝ → F₁}
    (hY : Predictable ℱ Y) {Γ : Ω → ℝ → E → F₂} (hΓ : MarkedPredictable ℱ ν Γ) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then F (s, Y ω s, Γ ω s e) else 0 :=
  hΓ.comp_measurable hF hY.measurable

/-- **A continuous function of the time, a predictable process and a marked predictable process
is marked predictable once it is cut to the positive times.** -/
theorem MarkedPredictable.comp_continuous [SigmaFinite ν] {F₁ : Type*} {F₂ : Type*}
    {F₃ : Type*} [TopologicalSpace F₁] [MeasurableSpace F₁] [OpensMeasurableSpace F₁]
    [TopologicalSpace F₂] [MeasurableSpace F₂] [OpensMeasurableSpace F₂]
    [SecondCountableTopologyEither F₁ F₂] [TopologicalSpace F₃] [MeasurableSpace F₃]
    [BorelSpace F₃] [Zero F₃] {F : ℝ × F₁ × F₂ → F₃} (hF : Continuous F) {Y : Ω → ℝ → F₁}
    (hY : Measurable[predictableSigma ℱ] fun q : ℝ × Ω => Y q.2 q.1)
    {Γ : Ω → ℝ → E → F₂} (hΓ : MarkedPredictable ℱ ν Γ) :
    MarkedPredictable ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then F (s, Y ω s, Γ ω s e) else 0 :=
  hΓ.comp_measurable hF.measurable hY

end Comp

end LevyStochCalc.Probability
