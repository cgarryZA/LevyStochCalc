/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoFourthMomentIncrements
import LevyStochCalc.Brownian.ItoFourthMomentPartialSums
import LevyStochCalc.Brownian.ItoFourthMomentLintegral

/-!
# Fourth moment of the elementary Brownian integral

The moments of a Brownian increment, and the fourth-moment bound they give for the elementary
integral of a uniformly bounded simple integrand. The bound comes from a recursion over the
partial sums: the odd-power cross terms drop out because a coefficient measurable before an
increment is independent of it, and the surviving terms are controlled by the second moment of
the partial sums, itself bounded by the same recursion.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_zero` — the moments of a centred real
  Gaussian scale with the standard deviation.
* `LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_odd` — the odd moments of the standard
  real Gaussian vanish.
* `LevyStochCalc.Brownian.Ito.integral_increment_sq`,
  `LevyStochCalc.Brownian.Ito.integral_increment_pow_four` — the second and fourth moments of a
  Brownian increment.
* `LevyStochCalc.Brownian.Ito.integral_mul_increment_pow` — a random variable measurable before
  `a` factors out of the integral against a power of the increment over `(a, b]`.
* `LevyStochCalc.Brownian.Ito.memLp_increment`, `LevyStochCalc.Brownian.Ito.memLp_mul_increment`
  — a Brownian increment, and a bounded random variable times one, have moments of every order.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.partialSum` — the partial sums of the elementary
  integral.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_sq_le`,
  `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le` — the second and
  fourth moments of the partial sums.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_simpleIntegral_pow_four_le_horizon` —
  `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·C⁴·T²` for a simple integrand bounded by `C`, where `c` is the
  fourth moment of the standard Gaussian.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock` — the variance budget
  `∑_{j<k} c_j² (τ_{j+1} − τ_j)` of a per-tile coefficient bound `c`, with
  `LevyStochCalc.Brownian.Ito.SimplePredictable.integral_simpleIntegral_pow_four_le_varClock`:
  `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·(∑_j c_j² Δ_j)²`, which for a coefficient vanishing off a
  subinterval sees only that subinterval's length.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.truncate` — the coefficients of a simple
  integrand clamped to `[-C, C]`, with `LevyStochCalc.Brownian.Ito.abs_clamp_sub_le`: clamping
  moves a value no further from a target already in `[-C, C]`, so a truncated approximant is
  still an approximant.
* `LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le` — the same bound
  for the `L²` Itô integral of any integrand bounded by `C`, by Fatou along an
  almost-everywhere convergent subsequence of truncated simple approximants.

The material is split over three files, all re-exported here:

* `LevyStochCalc.Brownian.ItoFourthMomentIncrements` — the Gaussian and Brownian increment
  moments, the partial sums of the elementary integral and the variance budget `varClock`;
* `LevyStochCalc.Brownian.ItoFourthMomentPartialSums` — the second- and fourth-moment recursions
  for the partial sums and the resulting bounds for the elementary integral;
* `LevyStochCalc.Brownian.ItoFourthMomentLintegral` — truncation of a simple integrand and the
  `lintegral` form of the bound, up to the `L²` Itô integral.
-/
