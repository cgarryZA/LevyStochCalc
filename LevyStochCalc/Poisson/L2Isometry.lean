/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Compensated

/-!
# Layer 1 (deaxiomatises I02): Itô-Lévy L² isometry

This file is the *integration entry-point*: when its main theorem
`itoLevyIsometry` lands CLEAN (no `sorry`, no custom axioms beyond Mathlib's),
the main dissertation can replace its cited axiom

  `Dissertation.Continuous.itoLevyIsometry`  (file `Dissertation/Continuous.lean:85`)

with a wrapper theorem that imports this module and re-exports the result
under the dissertation's specific types
(`Dissertation.Time`, `Dissertation.BSDE.Discrete.LevyMeasure d`, etc.).

The mathematical statement is:

  `𝔼[ (∫_0^T ∫_E φ(s, e) Ñ(ds, de))² ] = 𝔼[ ∫_0^T ∫_E |φ(s, e)|² ν(de) ds ]`

for predictable square-integrable `φ`. Its proof reduces to the quadratic-
variation identity from
`LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral`.

## Source

Applebaum, *Lévy Processes and Stochastic Calculus*, Cambridge 2009,
Theorem 4.2.3.

## Status

Clean wrapper around `Compensated.itoLevyIsometry`. ENNReal-norm form
matches the dissertation's `I02` axiom exactly. Sorry-free; transitively
depends only on Tier 1 cited axiom #6
(`itoIsometry_compensated_unified_existence`, Applebaum 2009 Thm 4.2.3).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.L2Isometry

universe u v

/-- **I02 (Itô-Lévy L² isometry).** For a Poisson random measure `N` with
σ-finite intensity `ν` on `(E, ℰ)`, and a predictable square-integrable
integrand `φ : Ω × [0,T] × E → ℝ`,

  `𝔼[ (∫_0^T ∫_E φ(s, e) Ñ(ds, de))² ] = 𝔼[ ∫_0^T ∫_E |φ(s, e)|² ν(de) ds ]`.

This is the headline theorem that the main dissertation will pull in (via
Lake-dep) to replace its `Dissertation.Continuous.itoLevyIsometry` axiom.

Wrapper around `LevyStochCalc.Poisson.Compensated.itoLevyIsometry`,
which forwards to Tier 1 cited axiom #6. -/
theorem itoLevyIsometry
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int_global : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N φ
            h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P :=
  LevyStochCalc.Poisson.Compensated.itoLevyIsometry N φ
    h_meas h_progMeas h_sq_int_global T hT

end LevyStochCalc.Poisson.L2Isometry
