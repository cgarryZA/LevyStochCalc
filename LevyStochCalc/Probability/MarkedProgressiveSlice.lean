/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.Progressive

/-!
# Mark slices and right-continuous transfer of progressive measurability

For a marked process `φ : Ω → ℝ → E → F` that is `MarkedProgressivelyMeasurable` for a
filtration `ℱ`, each mark `e : E` gives a slice `(ω, s) ↦ φ ω s e` which is
`ProgressivelyMeasurable` for `ℱ`.

Composing with `ProgressivelyMeasurable.isStronglyProgressive` and the inclusion
`ℱ ≤ ℱ.rightCont` transfers both the scalar and the mark-sliced statements to
`MeasureTheory.IsStronglyProgressive ℱ.rightCont`, in Mathlib's `fun s ω` argument order;
`isStronglyProgressive_rightCont_pi` is the coordinatewise form for processes valued in
`Fin d → ℝ`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Slice

variable {E F : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]
  {φ : Ω → ℝ → E → F}

/-- The slice of a marked progressively measurable process at a fixed mark is progressively
measurable. -/
theorem MarkedProgressivelyMeasurable.slice (h : MarkedProgressivelyMeasurable ℱ φ) (e : E) :
    ProgressivelyMeasurable ℱ fun ω s => φ ω s e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hg : Measurable fun p : Ω × ℝ => (p.1, p.2, e) :=
    measurable_fst.prodMk (measurable_snd.prodMk measurable_const)
  exact (h t).comp_measurable hg

end Slice

section Transfer

variable {F : Type*} [TopologicalSpace F] [Zero F] {H : Ω → ℝ → F}

/-- A progressively measurable process is strongly progressive for the right-continuous
filtration `ℱ.rightCont`. -/
theorem ProgressivelyMeasurable.isStronglyProgressive_rightCont
    (h : ProgressivelyMeasurable ℱ H) :
    IsStronglyProgressive ℱ.rightCont fun s ω => H ω s :=
  (h.mono fun t => ℱ.le_rightCont t).isStronglyProgressive

end Transfer

section Pi

variable {d : ℕ} {Z : ℝ → Ω → Fin d → ℝ}

/-- A process valued in `Fin d → ℝ` whose coordinates are progressively measurable is strongly
progressive for the right-continuous filtration `ℱ.rightCont`. -/
theorem isStronglyProgressive_rightCont_pi
    (h : ∀ i : Fin d, ProgressivelyMeasurable ℱ fun ω s => Z s ω i) :
    IsStronglyProgressive ℱ.rightCont Z := by
  intro t
  letI : MeasurableSpace Ω := ℱ.rightCont t
  refine stronglyMeasurable_iff_measurable.mpr (measurable_pi_lambda _ fun i => ?_)
  exact ((h i).isStronglyProgressive_rightCont t).measurable

end Pi

section MarkedTransfer

variable {E F : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]
  {U : ℝ → Ω → E → F}

/-- Every mark slice of a marked progressively measurable process is strongly progressive for
the right-continuous filtration `ℱ.rightCont`. -/
theorem MarkedProgressivelyMeasurable.isStronglyProgressive_rightCont
    (h : MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e) :
    ∀ e : E, IsStronglyProgressive ℱ.rightCont fun s ω => U s ω e :=
  fun e => (h.slice e).isStronglyProgressive_rightCont

end MarkedTransfer

end LevyStochCalc.Probability
