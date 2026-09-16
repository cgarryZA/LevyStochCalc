/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.CompensatedLocalityCutoff
import LevyStochCalc.Ito.CompensatedLocalityWindow
import LevyStochCalc.Ito.CompensatedLocalityStopping

/-!
# Locality of the compensated Poisson integral at a stopping time

Two admissible marked integrands that agree up to a stopping time `τ` have the same compensated
integral at every time `τ` has not reached. The route is that of `Brownian/ItoLocality.lean`:
the integral of an integrand cut off at a stopping time of finite range is the integral minus
the increments after the stopping time, a general stopping time is the decreasing limit of its
grid approximations, the cut-off integrands converge in energy, and the difference isometry
squeezes the integrals.

## Parts

* `LevyStochCalc.Ito.CompensatedLocalityCutoff` — the cut-off integrand `markedStopped τ φ` and
  the transport of admissibility along equalities of marked integrands.
* `LevyStochCalc.Ito.CompensatedLocalityWindow` — the integral over a time window and the
  additivity of the integral in its integrand.
* `LevyStochCalc.Ito.CompensatedLocalityStopping` — optional stopping at a stopping time of
  finite range, and locality at a general stopping time.

## Main definitions

* `markedStopped τ φ` — the marked process `φ` cut off at the stopping time `τ`.

## Main statements

* `stochasticIntegral_ae_eq_of_vanishing_gt` — the integral of an integrand vanishing after a
  time `c` does not move after `c`.
* `stochasticIntegral_indicator_Ioc` — restricting the integrand to `(c, t]` gives the increment
  of the integral over `(c, t]`.
* `stochasticIntegral_markedStopped_finiteRange` — optional stopping at a stopping time of
  finite range.
* `stochasticIntegral_markedStopped_eq_of_le` — at a time the stopping time has not reached,
  cutting the integrand off at it changes nothing.
* `stochasticIntegral_congr_of_le`, `stochasticIntegral_congr_of_lt` — integrands agreeing up
  to (respectively, strictly before) a stopping time have the same integral at every time the
  stopping time has not reached.
-/
