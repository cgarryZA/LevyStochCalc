/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardSpace
import LevyStochCalc.Ito.PicardSpaceBielecki
import LevyStochCalc.Ito.PicardSelfMap
import LevyStochCalc.Ito.PicardContractionTight
import Mathlib.Topology.UniformSpace.UniformEmbedding
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Wrap-up: Picard fixed-point existence/uniqueness on the AE quotient

This file extends `Ito/PicardSpaceBielecki.lean` with the wrap-up bridge
that eliminates `picardFixedPoint_jumpDiffusion_exists_unique_axiom`
(Tier 1 cited axiom #14): the axiom is replaced by a theorem
(`picardFixedPoint_jumpDiffusion_exists_unique_axiom`, in
`PicardBanach.lean`) that forwards through the wrap-up theorem here.

## What this file delivers

* `instNonemptyWithBielecki` / `instNonemptyAEQuot` — the constant-zero
  process witnesses inhabitedness of both type synonyms (genuine
  Nonempty, no sorry).

* `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` — the
  wrap-up theorem chaining together (literature: Applebaum 6.2.9 /
  Ikeda-Watanabe IV):

  1. `CompleteSpace (AEQuot β T)` via `Lp`-completeness + Doob
     càdlàg-modification (multi-session Mathlib glue).
  2. The descended Picard map `Φ : AEQuot β T → AEQuot β T` via
     `SeparationQuotient.lift'` from `picardStepOnS2`
     (`PicardSelfMap.lean`); well-definedness reduces to integrand-
     ae-equivalence respect by the three integrals (Bochner,
     Brownian-Itô, compensated-Poisson-Itô).
  3. Contraction rate transfer through the descent
     (`picardStep_bielecki_contraction_tight` in
     `PicardContractionTight.lean`).
  4. Banach fixed-point via `ContractingWith.fixedPoint` on the
     Banach space `AEQuot β T`.
  5. Bridge to a `JumpDiffusion W N coeffs x₀` structure:
     representative choice via `Quotient.out` + six-field verification.
  6. Uniqueness: any other `JumpDiffusion` solution descends to a
     fixed point of `Φ`; by `ContractingWith.fixedPoint_unique` it
     agrees with the chosen fixed point in `AEQuot`, hence a.s. at
     every `t`.

The entire chain is bundled into a **single explicit `sorry`** in the
wrap-up theorem body. This is the lone baseline-sorry entry for the
file. Splitting into named lemmas (one per chain step) does not reduce
the proof obligation — it only moves the same sorry across multiple
declarations.

## Status — sorry budget

* `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` — `sorry`
  (entire Picard chain, see "Mathematical content" above).

Tracked in `tools/sorry_baseline.txt`. The literature reference
(Applebaum 6.2.9) and Mathlib status (waits on Lp completeness for the
Bielecki S² space + Doob càdlàg modification + integrand ae-equivalence
descent for the three integrals) are documented in the docstring.

## References

* Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP
  2009, Theorem 6.2.9 (Picard iteration in `S²` for jump-diffusion SDEs).
* Ikeda-Watanabe, *Stochastic Differential Equations and Diffusion
  Processes*, North-Holland 1989, Chapter IV.
* Karatzas-Shreve, *Brownian Motion and Stochastic Calculus*, Springer
  1991, §3.2 (`S²` Banach space + Picard contraction).
* Mathlib `Mathlib.MeasureTheory.Function.LpSpace.Complete`
  (`MeasureTheory.Lp.instCompleteSpace`).
* Mathlib `Mathlib.Topology.UniformSpace.UniformEmbedding`
  (`SeparationQuotient.instCompleteSpace`).
* Mathlib `Mathlib.Topology.MetricSpace.Contracting`
  (`ContractingWith.fixedPoint`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-! ### Nonemptiness of `WithBielecki β T` and `AEQuot β T`

The constant-zero `SBoundedProcess` (from `PicardSpace.lean`) witnesses
inhabitedness of the underlying type, hence of the type synonym and the
AE-quotient. -/

/-- **Nonemptiness of `WithBielecki β T`.** The constant-zero
`SBoundedProcess` (from `PicardSpace.lean`) witnesses inhabitedness
of the underlying type, which inhabits the type synonym. -/
noncomputable instance instNonemptyWithBielecki
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T β : ℝ} :
    Nonempty (SBoundedProcess.WithBielecki (n := n) P T β) :=
  ⟨SBoundedProcess.WithBielecki.of (β := β) (constantZeroProcess (n := n) P T)⟩

/-- **Nonemptiness of `AEQuot β T`.** Lifts from the constant-zero process
via `SeparationQuotient.mk`. -/
noncomputable instance instNonemptyAEQuot
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T β : ℝ} :
    Nonempty (SBoundedProcess.AEQuot (n := n) P T β) :=
  ⟨SeparationQuotient.mk (SBoundedProcess.WithBielecki.of (β := β)
    (constantZeroProcess (n := n) P T))⟩

/-! ### The wrap-up theorem (Tier 1 axiom #14 replacement)

The single explicit `sorry` collects the entire Picard chain — see
module docstring for the breakdown. -/

/-- **Wrap-up: existence + a.s. uniqueness of the JumpDiffusion solution
via the descended Picard fixed point on the Bielecki AE quotient.**

This is the theorem that replaces the previous Tier 1 cited axiom
`picardFixedPoint_jumpDiffusion_exists_unique_axiom`. The proof
encapsulates the entire literature Picard chain (Applebaum 6.2.9 /
Ikeda-Watanabe IV) — see module docstring "What this file delivers"
for the six-step breakdown. The single explicit `sorry` collects every
analytic + Mathlib-glue obligation, hence:

`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` (this thm)
  ↓ forwarder
`picardFixedPoint_jumpDiffusion_exists_unique_axiom` (now a theorem
  in `PicardBanach.lean`, ex-Tier-1-axiom #14)
  ↓ forwarder
`picardFixedPoint_jumpDiffusion_exists_unique`
  ↓ forwarder
`JumpDiffusion.exists_unique` (the headline)

When the chain is fully proven (a multi-session Mathlib-glue program),
this sorry is replaced by the standard proof body and ALL downstream
forwarders gain genuine soundness without source-level changes.

**Signature strength**: requires `JumpDiffusionCoeffs.IsLipschitz coeffs
ν L` (Tanaka's `|X|^α` counterexample for α < 1/2 rules out uniqueness
without this); produces a CONCRETE `JumpDiffusion` (all six fields
populated — `X`, `measurable_path`, `initial_value`, `sup_L2`,
`cadlag_paths`, `is_solution`) plus the a.s. pairwise agreement at
every `t ≥ 0`. No trivial constant-path witness satisfies this for
generic non-zero coefficients: `X t ω = x₀` fails `is_solution` because
the integrals don't vanish. -/
theorem picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    {L : ℝ}
    (hL : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L) :
    ∃ (jd : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀),
      ∀ (jd' : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀),
        ∀ t : ℝ, ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω := by
  -- The full literature chain (Applebaum 6.2.9 / Ikeda-Watanabe IV) —
  -- see module docstring "What this file delivers" for the six steps.
  -- The chain consolidates into this single sorry: every analytic
  -- piece (Lp completeness, càdlàg modification, integrand-ae-equivalence
  -- descent, contraction transfer, Quotient.out representative choice,
  -- six-field verification, inverse-direction uniqueness) is documented
  -- there with literature references.
  sorry

end LevyStochCalc.Ito.Picard
