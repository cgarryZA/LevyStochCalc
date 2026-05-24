/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc

/-!
# Example: how to consume `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry`

This file demonstrates how a downstream client (e.g. the main
`Dissertation/Continuous.lean` axiom site, or a finance library
implementing Föllmer-Schweizer quadratic hedging in a Lévy market)
calls the project's headline I02 axiom and its sister Cu03 axiom.

P10 F4 fix (red-team 2nd audit, 2026-05-23): closes the
"library ships ZERO examples or tests" gap by providing minimal
end-to-end public-API usage examples.

These are `example` blocks rather than `theorem`s — they only need to
TYPECHECK against the public signature; the proofs are `by exact ...`
forwards. No sorryAx is introduced (the wrappers themselves use the
Tier 1 cited axioms via their `noncomputable def stochasticIntegral`
chain).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples

universe u v

section ItoLevyIsometry

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {ν : Measure E} [SigmaFinite ν]

/-- **I02 Itô-Lévy isometry — caller-side typechecking example.**

Demonstrates that the I02 wrapper has the exact shape needed to
replace the main dissertation's
`Dissertation.Continuous.itoLevyIsometry` axiom. Given:
- a Poisson random measure `N` with σ-finite intensity `ν`,
- a `Ω → ℝ → E → ℝ` integrand `φ` with joint Ω×ℝ×E measurability,
- progressive measurability with respect to `N`'s natural filtration,
- and a global L²-bound across all horizons `T > 0`,

we get the L² isometry
`𝔼[‖∫₀^T ∫_E φ Ñ‖²] = 𝔼[∫₀^T ∫_E ‖φ‖² ν(de) ds]` for every `T > 0`.

The body uses `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry`
verbatim; the example only exists to certify the public API signature
typechecks without modification. -/
example
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
  LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry N φ
    h_meas h_progMeas h_sq_int_global T hT

end ItoLevyIsometry

section BSDEJSolutionPredicate

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {ν : Measure E} [SigmaFinite ν]

/-- **BSDEJ solution predicate — public-API shape demonstration.**

Demonstrates the call-site shape for `IsBSDEJSolution`. A concrete
client (Tang-Li solver, Picard-iteration prover, deep-BSDE numerical
implementation) plugs in its candidate `(Y, Z, U)` and discharges the
predicate as a hypothesis. The predicate carries càdlàg-S² + L² + the
adapted + martingale-pinned conjuncts internally; the client only
sees the `Prop`.

This example is intentionally generic — it just asserts that
"satisfying the predicate" is the conclusion-witness, no proof body
beyond plumbing. -/
example
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (Y : ℝ → Ω → ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (U : ℝ → Ω → E → ℝ)
    (T : ℝ)
    (h_solution : LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution
      W N bsdej X Y Z U T) :
    LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution
      W N bsdej X Y Z U T :=
  h_solution

end BSDEJSolutionPredicate

section BSDEJPathRegularityLinearRate

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {ν : Measure E} [SigmaFinite ν]

/-- **BSDEJ path regularity (linear-rate corollary) — caller-side typechecking example.**

Demonstrates the call-site shape for `bsdej_path_regularity_linear_rate`.
Given:
- a multidim Brownian motion `W` and a Poisson random measure `N`,
- a `BSDEJData` quadruple `(f, g, ...)` together with the forward
  process `X` and the BSDEJ horizon `T > 0`,
- a Lipschitz constant `L` for the driver,
- and `L²` integrability of the terminal condition `g(X_T)`,

we obtain a single positive real constant `C` such that for every
partition of `[0, T]` and every BSDEJ solution triple `(Y, Z, U)`, the
combined L²-time modulus + projection errors are bounded by
`C · Δt`, where `Δt = max_n (t_{n+1} − t_n)`.

This is the public-API entry point for downstream chapters that need
the BET 2008 linear-in-`Δt` rate (`ψ(h) := C · h`), notably the
`discrete_to_continuous_convergence_sq` headline of the main
dissertation's discrete-to-continuous chapter (parked 2026-05-04 in
`D:/Dissertation/Dissertation/BSDE/Discrete/DiscretizationConvergence.lean`).

The body uses `bsdej_path_regularity_linear_rate` verbatim. -/
example
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X))
    (T : ℝ) (hT : 0 < T)
    {L : ℝ} (hL : LevyStochCalc.BSDEJ.Existence.Lipschitz bsdej ν L)
    (hξ_sq_int : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (_hM : 0 < M) (partition : Fin (M + 1) → ℝ)
        (_h_part_mono : StrictMono partition)
        (_h_part_start : partition 0 = 0)
        (_h_part_end : partition (Fin.last M) = T)
        (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
        (_h_solution :
          LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T),
        let Δt : ℝ := ⨆ n : Fin M,
          partition n.succ - partition n.castSucc
        (⨆ n : Fin M, ∫⁻ ω,
            ⨆ t ∈ Set.Icc (partition n.castSucc) (partition n.succ),
              (‖Y t ω - Y (partition n.castSucc) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              ∑ i, (‖Z s ω i -
                LevyStochCalc.BSDEJ.PathRegularity.conditionalTimeAverage_Z
                  partition Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖U s ω e -
                LevyStochCalc.BSDEJ.PathRegularity.conditionalTimeAverage_U
                  partition U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
          ≤ ENNReal.ofReal (C * Δt) :=
  LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity_linear_rate
    W N bsdej X hX_meas T hT (L := L) hL hξ_sq_int

end BSDEJPathRegularityLinearRate

end LevyStochCalc.Examples
