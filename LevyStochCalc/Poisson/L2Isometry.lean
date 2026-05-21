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

Phase 2 spec: clean wrapper around `Compensated.itoLevyIsometry`. ENNReal-norm
form matches the dissertation's `I02` axiom exactly. Currently inherits the
underlying `sorry` transitively.
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

Currently a wrapper around
`LevyStochCalc.Poisson.Compensated.itoLevyIsometry`, which carries the
substantive `sorry`. -/
theorem itoLevyIsometry
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
    (h_sq_int :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N φ T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P :=
  LevyStochCalc.Poisson.Compensated.itoLevyIsometry N φ T hT h_meas h_sq_int

end LevyStochCalc.Poisson.L2Isometry
