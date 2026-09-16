/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoFourthMomentIncrements
import LevyStochCalc.Brownian.Continuity

/-!
# The value of the standard Gaussian fourth moment

The fourth moment of a centred real Gaussian of variance `v` is `3 v²`
(`LevyStochCalc.Brownian.Continuity.gaussianReal_fourth_moment`), so at `v = 1` the constant
`gaussianFourthMoment` of `LevyStochCalc.Brownian.ItoFourthMomentIncrements` is `3`.

## Main statements

* `gaussianFourthMoment_eq_three` — `∫ x, x ^ 4 ∂(gaussianReal 0 1) = 3`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

/-- The fourth moment of the standard real Gaussian distribution is `3`. -/
theorem gaussianFourthMoment_eq_three : gaussianFourthMoment = 3 := by
  have h := Continuity.gaussianReal_fourth_moment 1
  rw [gaussianFourthMoment, h]
  norm_num

end LevyStochCalc.Brownian.Ito
