/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.MathlibBridge
import LevyStochCalc.Probability.WienerChaosStep

/-!
# The Wiener chaos elements of a Brownian step

For a Brownian motion `W` and times `s ≤ t`, the degree-`n` element of the Wiener chaos of the
step `(s, t]` is the Hermite polynomial `H_n(W_t - W_s; t - s)` of variance `t - s` evaluated at
the increment. The increment has law `gaussianReal 0 (t - s)`, so these elements are square
integrable, orthogonal across degrees with `E[H_n H_m] = δ_(n m) n! (t - s) ^ n`, and centred in
positive degree.

## Main statements

* `LevyStochCalc.Brownian.BrownianMotion.memLp_two_wienerChaosStep_increment` — square
  integrability.
* `LevyStochCalc.Brownian.BrownianMotion.integral_wienerChaosStep_increment_mul` —
  `E[H_n H_m] = δ_(n m) n! (t - s) ^ n`.
* `LevyStochCalc.Brownian.BrownianMotion.integral_wienerChaosStep_increment_sq` —
  `E[H_n ^ 2] = n! (t - s) ^ n`.
* `LevyStochCalc.Brownian.BrownianMotion.integral_wienerChaosStep_increment` — `E[H_n] = 0` for
  `n ≠ 0`.
-/

namespace LevyStochCalc.Brownian

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

namespace BrownianMotion

/-- The degree-`n` chaos element of a Brownian step lies in `L²`. -/
theorem memLp_two_wienerChaosStep_increment (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) :
    MemLp (fun ω => wienerChaosStep n (t - s) (W.W (t : ℝ) ω - W.W (s : ℝ) ω)) 2 P :=
  memLp_two_wienerChaosStep (W.hasLaw_increment s t hst) n

/-- A product of two chaos elements of a Brownian step is integrable. -/
theorem integrable_wienerChaosStep_increment_mul (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) :
    Integrable (fun ω => wienerChaosStep n (t - s) (W.W (t : ℝ) ω - W.W (s : ℝ) ω)
      * wienerChaosStep m (t - s) (W.W (t : ℝ) ω - W.W (s : ℝ) ω)) P :=
  integrable_wienerChaosStep_mul (W.hasLaw_increment s t hst) n m

/-- The `L²` pairing of the chaos elements of a Brownian step,
`E[H_n H_m] = δ_(n m) n! (t - s) ^ n`. -/
theorem integral_wienerChaosStep_increment_mul (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t)
    (n m : ℕ) :
    ∫ ω, wienerChaosStep n (t - s) (W.W (t : ℝ) ω - W.W (s : ℝ) ω)
        * wienerChaosStep m (t - s) (W.W (t : ℝ) ω - W.W (s : ℝ) ω) ∂P
      = if n = m then (n.factorial : ℝ) * ((t - s : ℝ≥0) : ℝ) ^ n else 0 :=
  integral_wienerChaosStep_mul (W.hasLaw_increment s t hst) n m

/-- The `L²` norm of the degree-`n` chaos element of a Brownian step,
`E[H_n ^ 2] = n! (t - s) ^ n`. -/
theorem integral_wienerChaosStep_increment_sq (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t)
    (n : ℕ) :
    ∫ ω, wienerChaosStep n (t - s) (W.W (t : ℝ) ω - W.W (s : ℝ) ω) ^ 2 ∂P
      = (n.factorial : ℝ) * ((t - s : ℝ≥0) : ℝ) ^ n :=
  integral_wienerChaosStep_sq (W.hasLaw_increment s t hst) n

/-- The chaos elements of a Brownian step are centred in positive degree. -/
theorem integral_wienerChaosStep_increment (W : BrownianMotion P) (s t : ℝ≥0) (hst : s ≤ t)
    {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, wienerChaosStep n (t - s) (W.W (t : ℝ) ω - W.W (s : ℝ) ω) ∂P = 0 :=
  integral_wienerChaosStep (W.hasLaw_increment s t hst) hn

end BrownianMotion

end LevyStochCalc.Brownian
