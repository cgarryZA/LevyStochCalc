/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.JumpTimes

/-!
# Arrival times as stopping times for a filtration containing the null sets

For a filtration whose time-zero σ-algebra contains the `P`-null sets, the arrival times
`jumpTime N A i` of a Poisson random measure `N` in a mark set `A` of finite intensity are
stopping times for the filtration itself: the counting process is almost surely finite at every
time, and the exceptional set is absorbed by the null sets of the time-zero σ-algebra. This
avoids both the pathwise finiteness hypothesis of `isStoppingTime_jumpTime` and the passage to
the right-continuous filtration in `isStoppingTime_jumpTime_rightCont`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : PoissonRandomMeasure P ν) (A : Set E)

/-- **The arrival times are stopping times for `ℱ` itself** when `ℱ 0` contains the `P`-null sets
and the mark set has finite intensity. -/
theorem isStoppingTime_jumpTime_of_complete {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) (i : ℕ) :
    IsStoppingTime ℱ (jumpTime N A i) := by
  obtain ⟨B, hsubB, hBm, hB0⟩ := exists_measurable_superset_of_null
    (ae_iff.mp (ae_forall_arrivalCount_ne_top N A hA hAν))
  have hGfin : ∀ ω : Ω, ω ∉ B → ∀ s : ℝ, arrivalCount N A s ω ≠ ⊤ := by
    intro ω hω s hcon
    exact hω (hsubB fun h => h s hcon)
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω : Ω | jumpTime N A i ω ≤ (t : WithTop ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h0 : ((0 : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ) :=
        (coe_zero_le_jumpTime N A i ω).trans hle
      exact absurd (by exact_mod_cast h0 : (0 : ℝ) ≤ t) (not_le.mpr ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have ht' : (0 : ℝ) ≤ t := ht
    have hSamb : MeasurableSet {ω : Ω | jumpTime N A i ω ≤ (t : WithTop ℝ)} :=
      ℱ.rightCont.le t _ (isStoppingTime_jumpTime_rightCont N A hℱ hA i t)
    have hSB : MeasurableSet[ℱ t] ({ω : Ω | jumpTime N A i ω ≤ (t : WithTop ℝ)} ∩ B) :=
      ℱ.mono ht' _
        (hnull _ (hSamb.inter hBm) (measure_mono_null Set.inter_subset_right hB0))
    have hBc : MeasurableSet[ℱ t] (Bᶜ : Set Ω) := ℱ.mono ht' _ (hnull B hBm hB0).compl
    have hcount : MeasurableSet[ℱ t] {ω : Ω | (i : ℝ≥0∞) ≤ arrivalCount N A t ω} :=
      measurable_arrivalCount N A hℱ hA t measurableSet_Ici
    have hsplit : {ω : Ω | jumpTime N A i ω ≤ (t : WithTop ℝ)}
        = ({ω : Ω | (i : ℝ≥0∞) ≤ arrivalCount N A t ω} ∩ Bᶜ)
          ∪ ({ω : Ω | jumpTime N A i ω ≤ (t : WithTop ℝ)} ∩ B) := by
      ext ω
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_compl_iff]
      constructor
      · intro hS
        by_cases hω : ω ∈ B
        · exact Or.inr ⟨hS, hω⟩
        · exact Or.inl ⟨(jumpTime_le_iff N A hA ht' (hGfin ω hω (t + 1))).mp hS, hω⟩
      · rintro (⟨hc, hω⟩ | ⟨hS, -⟩)
        · exact (jumpTime_le_iff N A hA ht' (hGfin ω hω (t + 1))).mpr hc
        · exact hS
    rw [hsplit]
    exact (hcount.inter hBc).union hSB

/-- The arrival times of `N` in a mark set of finite intensity form an increasing chain of
stopping times for a filtration whose time-zero σ-algebra contains the `P`-null sets, starting
at the origin. -/
theorem isStoppingTime_jumpTime_chain_of_complete {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    (∀ k : ℕ, IsStoppingTime ℱ (jumpTime N A k))
      ∧ (∀ (k : ℕ) (ω : Ω), jumpTime N A k ω ≤ jumpTime N A (k + 1) ω)
      ∧ (∀ ω : Ω, jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ)) :=
  ⟨fun k => isStoppingTime_jumpTime_of_complete N A hℱ hA hAν hnull k,
    fun k ω => jumpTime_mono N A (Nat.le_succ k) ω, jumpTime_zero N A⟩

end LevyStochCalc.Poisson
