/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Process.Filtration
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Restricting a filtration on `ℝ` to `ℝ≥0`

The càdlàg-modification machinery for quasimartingales is stated for an index type with a bottom
element, which `ℝ` does not have. `restrictNNReal` reindexes a filtration on `ℝ` by `ℝ≥0`, and
right continuity is inherited: the reals above a nonnegative time are exactly the nonnegative
reals above it.

## Main statements

* `restrictNNReal` — the reindexed filtration.
* `restrictNNReal.instIsRightContinuous` — it is right-continuous when the original is.
-/

open MeasureTheory
open scoped NNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω}

/-- The restriction to `ℝ≥0` of a filtration indexed by `ℝ`. -/
noncomputable def restrictNNReal (ℱ : Filtration ℝ m₀) : Filtration ℝ≥0 m₀ where
  seq t := ℱ t
  mono' _ _ hst := ℱ.mono (by exact_mod_cast hst)
  le' t := ℱ.le t

@[simp] theorem restrictNNReal_apply (ℱ : Filtration ℝ m₀) (t : ℝ≥0) :
    restrictNNReal ℱ t = ℱ (t : ℝ) := rfl

instance restrictNNReal.instIsRightContinuous (ℱ : Filtration ℝ m₀) [ℱ.IsRightContinuous] :
    (restrictNNReal ℱ).IsRightContinuous where
  RC t := by
    have hℱ : (⨅ r > (t : ℝ), ℱ r) = ℱ (t : ℝ) := by
      rw [← ℱ.rightCont_eq (t : ℝ), Filtration.IsRightContinuous.eq]
    rw [Filtration.rightCont_eq]
    refine le_trans (le_iInf₂ fun r hr => ?_) hℱ.le
    have hr0 : (0 : ℝ) ≤ r := le_trans t.coe_nonneg hr.le
    have hcoe : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr0
    have hlt : t < r.toNNReal := by
      rw [← NNReal.coe_lt_coe, hcoe]; exact hr
    exact iInf₂_le_of_le r.toNNReal hlt (le_of_eq (by rw [restrictNNReal_apply, hcoe]))

end LevyStochCalc.Probability
