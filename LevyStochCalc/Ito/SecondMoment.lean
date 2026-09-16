/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.SecondMomentToolkit
import LevyStochCalc.Ito.SecondMomentQuadratic
import LevyStochCalc.Ito.SecondMomentBilinear
import LevyStochCalc.Ito.SecondMomentWeighted

/-!
# The second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. It follows from the isometries of the two stochastic
integrals, the orthogonality of the Brownian coordinates and of the Brownian and compensated
integrals, the martingale property of both integrals against the initial value and the drift,
and the pathwise identity `(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds`. The drift term is the time
integral of the expected pairing; at every time the pairing is expanded along the decomposition,
and the two martingale pieces are read at the horizon by the martingale property.

Polarising, for two such processes `X` and `Y` over the same driver,

`𝔼[X_T Y_T] = 𝔼[X₀ Y₀] + ∫_0^T 𝔼[X_s b'_s + Y_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j σ'_j ds
  + 𝔼 ∫_0^T ∫_E γ γ' dν ds`,

the expectation form of the bilinear Itô formula, from the polarised isometries of the two
stochastic integrals and the polarised drift identity
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`.

Weighting by `e^{βs}`, since `t ↦ 𝔼[X_t²]` is the initial value plus the time integral of the
rate `2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`, integration by parts against the
weight gives

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic formula.

## Main statements

* `integral_mul_self_eq_of_isItoLevyProcess` — the second moment of a scalar Itô–Lévy process
  over a Lévy driver whose Brownian and compensated integrals are orthogonal
  (`LevyDriver.CrossWitness`, supplied by `LevyDriver.crossWitness` for the joint natural
  filtration and by `CrossWitness.aug` for its augmentation).
* `integral_sum_mul_self_eq_of_isItoLevyProcess` — the vector form, coordinate by coordinate.
* `integral_mul_self_eq_of_isItoLevyProcess_aug` — the scalar form over the augmented joint
  natural filtration of the driver, with the witness supplied by the driver.
* `integral_mul_eq_of_isItoLevyProcess` — the bilinear form: the expected product at the
  horizon of two scalar Itô–Lévy processes over the same driver.
* `integral_exp_mul_self_eq_of_isItoLevyProcess` — the exponentially weighted form
  `e^{βT} 𝔼[X_T²]`, from `integral_mul_self_eq_add_setIntegral` (the second moment as the
  initial value plus the time integral of its rate) and `exp_mul_eq_add_setIntegral` (the
  weighting of an absolutely continuous function, by `setIntegral_exp_mul_setIntegral`); its
  vector form `integral_exp_mul_sum_mul_self_eq_of_isItoLevyProcess`.
* `integral_mul_eq_of_isItoLevyProcess_aug`, `integral_exp_mul_self_eq_of_isItoLevyProcess_aug`
  — the bilinear and weighted forms over the augmented joint natural filtration of the driver.
* `memLp_two_of_isItoLevyProcess` — such a process is square integrable at every nonnegative
  time.
* `integral_mul_martingale_eq` — pairing a square-integrable martingale at a later time against
  a square-integrable variable measurable at an earlier time reads the martingale at the earlier
  time.
* `integral_setIntegral_mul` — the pairing of a time integral against a square-integrable
  variable is the time integral of the pairings.
* `mul_self_setIntegral_eq` — the square of the integral of an integrable function over `[0, T]`
  is twice the integral of its running integral against the function.
* `mul_setIntegral_eq` — its polarised form for two integrable functions.
* `integral_mul_stochasticIntegralBrownian`, `integral_mul_stochasticIntegral` — the polarised
  isometries: the expected product of two Brownian, or two compensated, integrals at a time is
  the expected time integral of the product of the integrands.

## Implementation notes

The development is split into `SecondMomentToolkit` (the `L²` and pathwise auxiliary lemmas, the
running integral of the drift and the polarised Brownian isometry), `SecondMomentQuadratic` (the
polarised compensated isometry and the quadratic identity in scalar, vector and augmented form),
`SecondMomentBilinear` (the bilinear identity) and `SecondMomentWeighted` (the exponentially
weighted forms); this module is their union.
-/
