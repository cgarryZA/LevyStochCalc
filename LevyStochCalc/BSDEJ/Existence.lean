/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.MartingaleRepresentation

/-!
# The Picard map of a BSDEJ

`picardMap` is the iteration map of the Picard scheme for a backward SDE with jumps and
`Lipschitz` the Lipschitz condition on its generator (Tang & Li 1994; Becherer 2006).

Existence and uniqueness of the solution is not stated here. Its previous formulation
`continuousBSDEJ_exists_unique` (cited result #9) quantified over an arbitrary measurable
forward process `X` and asked for a solution in the class `IsBSDEJSolution`, whose integrands
are adapted to the natural filtration of a single driver; a terminal condition `g(X_T)`
independent of `(W, N)` has no adapted solution, and `ξ = W_T · Ñ_t` none in that class, so the
statement was refutable and was retired on 2026-09-06. It will be restated once the `L²`
integrals are built over the joint filtration of `(W, N)` (`Plan.md`, work package X2).

## Source

* Tang & Li, "Necessary conditions for optimal control of stochastic
  systems with random jumps", SICON 32(5), 1994.
* Becherer, "Bounded solutions to backward SDEs with jumps for utility
  optimization and indifference hedging", AAP 16(4), 2006.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Existence

universe u v

section PicardMap
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The Picard iteration map `Φ` for a BSDEJ. Given `(Y', Z', U')`, define
`(Y, Z, U)` by:
* `Y_t := 𝔼[g(X_T) + ∫_t^T f(s, X_{s-}, Y'_{s-}, Z'_s, U'_s) ds | ℱ_t]`
* `(Z, U)`: extracted from the martingale representation of `M_t := Y_t + ∫_0^t f`.
The fixed point of `Φ` is the BSDEJ solution. -/
noncomputable def picardMap
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (_bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (_X : ℝ → Ω → (Fin n → ℝ))
    (_T : ℝ)
    (_input :
      (ℝ → Ω → ℝ) × (ℝ → Ω → (Fin d → ℝ)) × (ℝ → Ω → E → ℝ)) :
    (ℝ → Ω → ℝ) × (ℝ → Ω → (Fin d → ℝ)) × (ℝ → Ω → E → ℝ) :=
  -- Placeholder: identity on input. Substantive Picard map (Tang-Li 1994 / Becherer 2006)
  -- requires the conditional expectation + martingale representation machinery.
  _input

/-- Lipschitz constant of the BSDEJ generator `f`. Substantive proofs require
explicit Lipschitz bounds; we package them as a single hypothesis. The norm
on `Fin d → ℝ` is the Euclidean norm; the norm on `E → ℝ` is the L²(ν) norm
implicit in the next clause's `∫⁻ e, ...` integrand. -/
def Lipschitz {n d : ℕ}
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (ν : Measure E) (L : ℝ) : Prop :=
  ∀ s : ℝ, ∀ x : Fin n → ℝ, ∀ y₁ y₂ : ℝ,
    ∀ z₁ z₂ : Fin d → ℝ, ∀ u₁ u₂ : E → ℝ,
    |bsdej.f s x y₁ z₁ u₁ - bsdej.f s x y₂ z₂ u₂|
      ≤ L * (|y₁ - y₂| + ‖z₁ - z₂‖
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal.sqrt)

end PicardMap

section Existence
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end Existence

end LevyStochCalc.BSDEJ.Existence
