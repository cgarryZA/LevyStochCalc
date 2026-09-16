/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.AugmentationMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable

/-!
# `L²` of an augmented σ-algebra

Augmenting a sub-σ-algebra `m ≤ m₀` by the `μ`-null sets (`aug`) does not change the associated
subspace of `L²`: a function almost everywhere strongly measurable for `aug m m₀ μ` is almost
everywhere equal to an `m`-strongly measurable one, since every `aug m m₀ μ`-measurable set
differs from an `m`-measurable set by a null set.

## Main statements

* `aestronglyMeasurable_aug_iff` — `AEStronglyMeasurable[aug m m₀ μ] f μ ↔
  AEStronglyMeasurable[m] f μ`.
* `lpMeas_aug` — `lpMeas F ℝ (aug m m₀ μ) 2 μ = lpMeas F ℝ m 2 μ`.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure[m₀] Ω}
variable {F : Type*} [NormedAddCommGroup F] [CompleteSpace F]

/-- A function is almost everywhere strongly measurable for the augmentation of `m` exactly when
it is almost everywhere strongly measurable for `m`. -/
theorem aestronglyMeasurable_aug_iff (hm : m ≤ m₀) {f : Ω → F} :
    AEStronglyMeasurable[aug m m₀ μ] f μ ↔ AEStronglyMeasurable[m] f μ := by
  refine ⟨fun h => ?_, fun h => h.mono (le_aug hm)⟩
  obtain ⟨g, hg, hfg⟩ := h
  exact (aestronglyMeasurable_of_stronglyMeasurable_aug hg).congr hfg.symm

/-- **The `L²` subspace of an augmented σ-algebra is the `L²` subspace of the σ-algebra.** -/
theorem lpMeas_aug [NormedSpace ℝ F] (hm : m ≤ m₀) :
    lpMeas F ℝ (aug m m₀ μ) 2 μ = lpMeas F ℝ m 2 μ := by
  ext f
  rw [mem_lpMeas_iff_aestronglyMeasurable, mem_lpMeas_iff_aestronglyMeasurable]
  exact aestronglyMeasurable_aug_iff hm

end LevyStochCalc.Probability
