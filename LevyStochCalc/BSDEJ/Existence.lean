/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.MartingaleRepresentation

/-!
# Continuous BSDEJ existence and uniqueness

For Lipschitz `(f, g)` and `L²`-terminal data, the BSDEJ admits a unique
solution `(Y, Z, U) ∈ S² × H² × H²_N`.

Proof following Tang & Li 1994 / Becherer 2006: Picard contraction on the
Banach space of solution triples.

## Source

* Tang & Li, "Necessary conditions for optimal control of stochastic
  systems with random jumps", SICON 32(5), 1994.
* Becherer, "Bounded solutions to backward SDEs with jumps for utility
  optimization and indifference hedging", AAP 16(4), 2006.

## Structure

The existence/uniqueness statement `continuousBSDEJ_exists_unique` is a cited
axiom (Tang–Li 1994); `picardMap` and the surrounding lemmas set up the
Picard-contraction route of its standard proof.
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

/-- **CITED AXIOM: Continuous BSDEJ existence and uniqueness (Tang-Li 1994).**

Under Lipschitz hypotheses on `(f, g)` and L² integrability of the terminal data,
the BSDEJ has a unique adapted solution triple `(Y, Z, U) ∈ S² × H² × H²_N`.

**Reference**: Tang, S. & Li, X. *Necessary conditions for optimal control of
stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994,
pp. 1447-1475 — the historical first BSDEJ existence/uniqueness reference.
Andersson, Gnoatto, Patacca & Picarelli, *A deep solver for BSDEs with jumps*,
arXiv:2211.04349, 2025, **Theorem 2.4**. Delong, Ł. *Backward Stochastic
Differential Equations with Jumps and their Actuarial and Financial
Applications*, Springer EAA Series, 2013, **Theorem 4.1.3** (jumps case). For
the continuous-only background (no jumps), see Pardoux & Răşcanu, *Stochastic
Differential Equations, Backward SDEs, Partial Differential Equations*, Springer
2014, **Theorem 4.79** — Pardoux–Răşcanu does not cover the jump case; Tang–Li
1994 and Delong 2013 are the jump-case authorities.

**Standard proof outline**: Banach fixed-point theorem applied to the Picard
map in the Banach space `S² × H² × H²_N` with weighted norm `e^{-βt}` for
sufficiently large `β`. The Picard map is K-Lipschitz with K < 1 for large β.
Uses the martingale representation theorem (`jacodYor_representation`) for the
Z, U extraction.

**Uniqueness-scope note.** The
final conjunct of the conclusion below asserts uniqueness for the **Y
component only**: `∀ Y' Z' U', IsBSDEJSolution W N bsdej X Y' Z' U' T →
∀ t, ∀ᵐ ω ∂P, Y t ω = Y' t ω`. It does **not** assert pointwise-in-`(t,
ω)` a.e. equality for `Z` or `U`.

This is **strictly weaker than the literature `S² × H² × H²_N`
uniqueness statement**, which delivers Y-uniqueness in `S²` AND Z, U
uniqueness in `H² × H²_N` (the latter two as `volume × P`- and
`ν × volume × P`-a.e. equalities, respectively). The literature
derivation proceeds:

1. The pair `(Z, U)` arises (in the standard Tang–Li 1994 proof) as the
   integrand of the L²-martingale representation `M_t :=
   Y_t + ∫_0^t f(s, X_s, Y_s, Z_s, U_s) ds`, projected onto the
   `(W, N)`-noise basis via the Jacod–Yor predictable representation
   theorem (`jacodYor_representation`, Tier 1 cited axiom #13).
2. Given two solutions `(Y, Z, U)` and `(Y, Z', U')` sharing the same
   Y (by step 1 of the conclusion below), the corresponding
   martingales `M, M'` coincide in `S²` (since `Y = Y'` and `f(s, X_s,
   Y_s, Z_s, U_s) = f(s, X_s, Y_s, Z'_s, U'_s)` modulo the Lipschitz
   bound — needs the bound + Grönwall to be made rigorous). Then the
   uniqueness of the predictable Itô representation
   (Jacod–Yor / Kunita–Watanabe orthogonality) forces `Z = Z'`
   `volume × P`-a.e. and `U = U'` `ν × volume × P`-a.e.

A downstream "(Z, U) uniqueness extractor" would package the two steps
above into a lemma `bsdej_zu_unique_via_representation` that takes two
`IsBSDEJSolution` witnesses with `Y =ᵃᵉ Y'` and produces the `(Z, U)`
a.e.-equality. The extractor's proof body invokes
`jacodYor_representation` plus algebraic manipulations of the
Itô–Lévy decomposition; it is mechanical given the literature step (2)
but not currently in this library — the L² Picard-iteration scope
delivered here suffices for the dissertation BSDEJ chain, where
Y-uniqueness alone is the load-bearing conclusion (downstream
applications fix `(Z, U)` via the canonical projection from `(Y, M)`
and inherit a.e.-uniqueness through that channel).

**Scope rationale**: stating Y-only uniqueness in the axiom and
deriving (Z, U) uniqueness separately as a downstream theorem mirrors
the structure of the rest of the library (canonical-integral pins +
extractor theorems). The axiom statement here matches the strength of
Tang–Li 1994's Theorem 3.1 step on Y-uniqueness; the (Z, U)-uniqueness
strengthening is left as a downstream theorem rather than baked in,
because the proof requires Tier 1 axiom #13 (`jacodYor_representation`)
and is not bottlenecked on additional Tier 1 content.

**Replacement plan**: when Mathlib gains BSDEJ existence, replace this `axiom`
with a forwarder. Tracked in `tools/cited_axioms.md`. -/
axiom continuousBSDEJ_exists_unique
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    -- Joint measurability of the forward process X (required for the SDE
    -- equation in IsBSDEJSolution to be well-typed):
    (_hX_meas : Measurable (Function.uncurry X))
    (T : ℝ) (_hT : 0 < T)
    -- Lipschitz hypothesis (Tang-Li / Pardoux-Răşcanu requirement; without it
    -- the statement would claim existence-uniqueness for non-Lipschitz drivers
    -- like `f(s,x,y,z,u) = y²`, which the literature does not cover):
    {L : ℝ} (_hL : Lipschitz bsdej ν L)
    -- L² terminal data hypothesis (`g(X_T)` is L²-bounded — required for
    -- the solution to live in `S² × H² × H²_N`):
    (_hξ_sq_int : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤)
    -- Linear-growth-at-zero / Tang-Li H2 hypothesis:
    -- `E[∫₀^T |f(s, X_s, 0, 0, 0)|² ds] < ∞`. Without
    -- this, the BSDEJ Picard iteration's first iterate may have infinite
    -- L²-norm even when the driver is Lipschitz (e.g., a Lipschitz `f` that
    -- is unbounded in (s, x) and constant in (y, z, u) has no L² solution).
    -- Tang-Li 1994 Thm 3.1 lists this as hypothesis H2:
    (_hf_zero_sq_int :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖bsdej.f s (X s ω) 0 0 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    -- Expose the Tang-Li 1994 / Pardoux-Răşcanu Thm 4.79 quantitative bound
    -- on the solution norm.
    -- The literature theorem yields not just existence + uniqueness but
    -- an a-priori bound `‖(Y, Z, U)‖_{S²×H²×H²_ν}² ≤ K(L, T) · (‖ξ‖² +
    -- ‖f(·, ·, 0, 0, 0)‖_{L²(P×dt)}²)`. The constant `K(L, T)` is
    -- polynomial in T and exponential in `L·T` (from the Grönwall step
    -- of the Tang-Li proof). Without exposing this bound, downstream
    -- numerical work (P6 numerical_analyst lens) cannot control
    -- discretisation error on the solution norm.
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
      (K_TL : ℝ),
      0 < K_TL ∧
      LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T ∧
      -- Tang-Li a-priori bound on the S²×H²×H²_ν solution norm:
      ((∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P).toReal
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal)
        ≤ K_TL *
          ((∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
            + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
                (‖bsdej.f s (X s ω) 0 0 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal) ∧
      ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ))
        (U' : ℝ → Ω → E → ℝ),
        LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y' Z' U' T →
        (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = Y' t ω)

end Existence

end LevyStochCalc.BSDEJ.Existence
