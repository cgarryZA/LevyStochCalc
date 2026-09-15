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
were then adapted to the natural filtration of a single driver; a terminal condition `g(X_T)`
independent of `(W, N)` has no adapted solution, and `ξ = W_T · Ñ_T` none in that class, so the
statement was refutable and was retired on 2026-09-06. The `L²` integrals and
`IsBSDEJSolution` now take a common filtration `ℱ` with `IsBrownianFiltration` and
`IsPoissonFiltration` hypotheses; restating existence and uniqueness over the joint filtration
of `(W, N)` is `Plan.md`'s work package A6.

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

/-- The Picard iteration map `Φ` for a BSDEJ, as the identity on `(Y, Z, U)`.

The substantive map sends `(Y', Z', U')` to `(Y, Z, U)` with
`Y_t = 𝔼[g(X_T) + ∫_t^T f(s, X_{s-}, Y'_{s-}, Z'_s, U'_s) ds | ℱ_t]` and `(Z, U)` read off the
martingale representation of `M_t = Y_t + ∫_0^t f`; its fixed point is the BSDEJ solution. -/
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

/-- Lipschitz condition on the BSDEJ generator `f`: uniformly in `(s, x)`, the increment of `f`
is bounded by `L` times the sum of `|y₁ - y₂|`, the supremum norm `‖z₁ - z₂‖` on `Fin d → ℝ`
and the `L²(ν)` distance `(∫ ‖u₁ - u₂‖² dν)^{1/2}` of the jump variables.

The inequality is stated in `ℝ≥0∞`, so it also constrains pairs `u₁, u₂` whose difference is not
square integrable for `ν`; the real-valued form is `abs_sub_le_of_lipschitz`. -/
def Lipschitz {n d : ℕ}
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (ν : Measure E) (L : ℝ) : Prop :=
  ∀ s : ℝ, ∀ x : Fin n → ℝ, ∀ y₁ y₂ : ℝ,
    ∀ z₁ z₂ : Fin d → ℝ, ∀ u₁ u₂ : E → ℝ,
    (‖bsdej.f s x y₁ z₁ u₁ - bsdej.f s x y₂ z₂ u₂‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal L * ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ))

/-- The real-valued form of the Lipschitz inequality, for jump variables at finite `L²(ν)`
distance. -/
theorem abs_sub_le_of_lipschitz {n d : ℕ}
    {bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E}
    {ν : Measure E} {L : ℝ} (hL : 0 ≤ L) (h : Lipschitz bsdej ν L)
    (s : ℝ) (x : Fin n → ℝ) (y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) :
    |bsdej.f s x y₁ z₁ u₁ - bsdej.f s x y₂ z₂ u₂|
      ≤ L * (|y₁ - y₂| + ‖z₁ - z₂‖
          + Real.sqrt (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  set A : ℝ≥0∞ := ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν with hA
  have hroot : A ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt A.toReal) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hu]
  have key := h s x y₁ y₂ z₁ z₂ u₁ u₂
  rw [hroot] at key
  have hne : ENNReal.ofReal L * ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
      + ENNReal.ofReal (Real.sqrt A.toReal)) ≠ ⊤ := by finiteness
  have hmono := ENNReal.toReal_mono hne key
  rwa [ENNReal.toReal_mul, ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
    ENNReal.coe_toReal, ENNReal.coe_toReal, ENNReal.toReal_ofReal hL,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), coe_nnnorm, coe_nnnorm, coe_nnnorm,
    Real.norm_eq_abs, Real.norm_eq_abs] at hmono

end PicardMap

section Existence
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

end Existence

end LevyStochCalc.BSDEJ.Existence
