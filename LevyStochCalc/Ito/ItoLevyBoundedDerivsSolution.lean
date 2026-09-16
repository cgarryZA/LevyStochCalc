/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMain

/-!
# The Itô–Lévy formula at bounded derivatives, from the solution data

`itoLevyFormula_jumpResidual_of_boundedDerivs` asks, besides the bounded derivatives of the state
function, for the admissibility of the derived integrands `(∇u)ᵀσ` and `u(x + γ) − u(x)` along the
solution, for left limits of the solution at every sample point and every time, and for the
progressive measurability of the drift along the solution. This file derives each of these from
the data the well-posedness theorem produces — regular Lipschitz coefficients, a filtration
satisfying the usual conditions, and the window solutions of `exists_globalSolution` — and
states the formula for a solution built from that data alone.

## The càdlàg representative

The well-posedness theorem gives paths that are càdlàg on `[0, ∞)` almost surely. The formula
needs left limits at every sample point and every time, so the solution is replaced by
`cadlagRep G X`: the same path on a measurable set `G` of full measure where the paths are
càdlàg, the constant zero path off `G`, and the zero state before time zero. The representative
agrees with the original at every nonnegative time on `G`, is adapted because `G` belongs to the
initial σ-algebra (which contains the null sets), is progressively measurable because it is
right-continuous everywhere, and satisfies the same window equations because both stochastic
integrals depend only on the class of their integrand.

## Main statements

* `cadlagRep_cadlag`, `progressivelyMeasurable_cadlagRep`, `solvesOn_cadlagRep` — the
  representative is càdlàg at every sample point and every time, progressively measurable, and
  solves the equation on every window.
* `measurable_diffusionIntegrand_path`, `progressivelyMeasurable_diffusionIntegrand_path`,
  `lintegral_sq_diffusionIntegrand_path_lt_top` — admissibility of `(∇u)ᵀσ` along a path.
* `measurable_jumpIncrement_path`, `markedProgressivelyMeasurable_jumpIncrement_path`,
  `lintegral_sq_jumpIncrement_path_lt_top` — admissibility of `u(x + γ) − u(x)` along a path.
* `ae_integrableOn_drift_path`, `ae_lintegral_compensatorDriftIntegrand_lt_top` — integrability
  of the drift and of the compensator-drift integrand along a path.
* `multidimIntegral_congr_ae` — Itô integrals of vector integrands agreeing a.e. on a window.
* `itoLevyFormula_jumpResidual_of_sdeData_of_leftLim` — the formula for a *given* jump diffusion
  carrying SDE data at a filtration satisfying the usual conditions and having left limits at
  every sample point and every time; the adaptedness of the path, the drift's measurability,
  progressive measurability and energy, the four derived-integrand admissibility bundles and the
  two integrability side conditions are all derived from the SDE data and the coefficient
  regularity.
* `itoLevyFormula_jumpResidual_of_sdeData` — the same formula for a given jump diffusion carrying
  SDE data, with the left limits derived as well: the almost-sure càdlàg paths of a jump
  diffusion give a representative with left limits everywhere, which carries SDE data at the same
  filtration, and each term of the formula reads the path only up to a null set.
* `itoLevyFormula_of_boundedDerivs` — the same statement in its four-term form,
  `u(T, X_T) − u(0, X_0) = drift + Brownian + compensated + compensator-drift`, the shape the
  dissertation forwards.
* `itoLevyFormula_jumpResidual_of_solvesOn` — the formula for a jump diffusion solving the
  equation relative to the given filtration, every admissibility input being one of the lemmas
  above.

## Parts

* `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative` — the càdlàg representative
  `cadlagRep` and its measurability, path regularity and window equations.
* `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands` — admissibility of the derived
  integrands `(∇u)ᵀσ`, `u(x + γ) − u(x)`, the drift and the compensator-drift integrand along a
  path.
* `LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionMain` — the Itô–Lévy formula itself, in its
  window, SDE-data and four-term forms.
-/
