/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Picard
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Banach fixed-point shim for the Picard iteration

This file wraps Mathlib's `ContractingWith.fixedPoint` (the Banach fixed-point
theorem on a complete metric space) into the form needed by the Picard
iteration for the jump-diffusion SDE. The substantive contraction estimate
lives in `LevyStochCalc/Ito/Picard.lean` (the `bielecki_*` lemma family
plus the per-component drift / diffusion / jump Lipschitz bounds); this file
just packages the Mathlib invocation so the SDE-existence proof in
`LevyStochCalc/Ito/Setting.lean` can use a single named theorem rather
than unfolding the Mathlib API.

## Status

The `S²([0, T]; ℝⁿ)` Banach-space structure on `SBoundedProcess` is downstream
work: it requires
* a `MetricSpace` (or `EMetricSpace`) instance whose distance is the
  Bielecki / `S²`-sup norm,
* a `CompleteSpace` instance (`S²` is the standard Banach space of càdlàg
  L²-bounded processes; completeness is the usual quotient by P-null sets),
* `Nonempty` (the constant zero process trivially witnesses this).

These instances are **not** built here — they are a separate downstream
piece. This file states the Banach shim in two forms:

1. **`picardFixedPoint_generic`** (substantive shim) — for *any* complete
   nonempty metric space `M` and *any* contraction `Φ : M → M`, there
   exists a unique fixed point. This is the direct repackaging of
   Mathlib's `ContractingWith.fixedPoint` + `fixedPoint_unique` into the
   `∃!` form natural for Picard.

2. **`picardFixedPoint`** (target shape from the project plan) — for
   `SBoundedProcess P T` equipped with the (downstream) `MetricSpace`,
   `Nonempty`, `CompleteSpace` instances and a contraction `Φ`, the
   `picardFixedPoint_generic` result specialises to a unique fixed point.

Both are sorry-free; the metric instances are taken as `[...]`
hypotheses, deferring the analytic construction (which is independent
substantive work) to a downstream file that builds them.

## Reference

* Mathlib: `Mathlib.Topology.MetricSpace.Contracting`,
  `ContractingWith.fixedPoint`, `ContractingWith.fixedPoint_isFixedPt`,
  `ContractingWith.fixedPoint_unique`.
* Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., 2009,
  Thm 6.2.9 (Picard iteration in `S²`).
-/

open MeasureTheory ProbabilityTheory Function
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Banach fixed-point shim (generic form).** For any nonempty complete
metric space `M` and any contraction `Φ : M → M` (i.e. `ContractingWith K Φ`
for some `K < 1`), there is a **unique** fixed point of `Φ`.

This is the direct repackaging of Mathlib's
`ContractingWith.fixedPoint` + `fixedPoint_isFixedPt` + `fixedPoint_unique`
into the `∃!` shape natural for the Picard iteration:

  `∃! X : M, Φ X = X`.

Substantive content sits inside `ContractingWith`: Mathlib proves
existence by showing `(Φ^[n] x)` is a Cauchy sequence (geometric `K^n`
decay) and uses completeness to extract its limit; uniqueness is
immediate from the contraction (two fixed points would have
`d(x, y) ≤ K · d(x, y)` with `K < 1`).

This generic form takes the metric / completeness / nonemptiness as
instance arguments — the SDE specialisation
(`picardFixedPoint`) bundles them on the SBoundedProcess Banach space. -/
theorem picardFixedPoint_generic
    {M : Type*} [MetricSpace M] [Nonempty M] [CompleteSpace M]
    {K : NNReal} {Φ : M → M} (hΦ : ContractingWith K Φ) :
    ∃! X : M, Φ X = X := by
  -- Extract the fixed point from Mathlib's `ContractingWith.fixedPoint`.
  refine ⟨ContractingWith.fixedPoint Φ hΦ, ?_, ?_⟩
  · -- Existence: `fixedPoint_isFixedPt` says `Φ (fixedPoint ...) = fixedPoint ...`.
    exact hΦ.fixedPoint_isFixedPt
  · -- Uniqueness: any fixed point equals `ContractingWith.fixedPoint`.
    intro Y hY
    -- `hY : Φ Y = Y` is `Function.IsFixedPt Φ Y`.
    exact hΦ.fixedPoint_unique hY

/-- **Banach fixed-point shim (SBoundedProcess form).** Specialises
`picardFixedPoint_generic` to the SBoundedProcess setting required by
the jump-diffusion SDE Picard iteration.

The hypothesis bundle:

* `[MetricSpace (SBoundedProcess P T)]` — the `S²` / Bielecki metric on
  the càdlàg L²-bounded process space (downstream construction; the
  Bielecki β-norm of `Picard.lean` is the canonical choice).
* `[Nonempty (SBoundedProcess P T)]` — witnessed e.g. by the constant
  zero process.
* `[CompleteSpace (SBoundedProcess P T)]` — `S²` is the standard Banach
  space of càdlàg L²-bounded processes; completeness is the usual
  quotient by P-null sets / Lebesgue-null time sets.
* `Φ : SBoundedProcess P T → SBoundedProcess P T` — the Picard map on
  the process space (lifted from `picardStep`, requires the
  measurability / progressive-measurability / L²-finiteness
  hypotheses on `(μ, σ, γ)` along candidate processes).
* `hΦ : ContractingWith K Φ` — the substantive Bielecki β-norm
  contraction estimate (combines `bielecki_weighted_integral_bound`
  with the per-component Lipschitz bounds on drift / diffusion / jump).

Conclusion: **a unique fixed point of `Φ`**, which (downstream) becomes
the strong solution of the SDE via `fixedPoint_is_solution`.

Note the metric / completeness / nonemptiness are deliberately taken as
instance arguments (rather than bundled as fields on `SBoundedProcess`)
to keep this shim agnostic to the metric choice: the same theorem
applies to the Bielecki β-norm, the standard `S²` norm, or any
equivalent norm on the same space. The contraction `Φ` and rate `K` are
parameters because they depend on the choice of norm (the Bielecki
β-norm gives `K = nL²T/(2β) < 1` for `β > nL²T/2`; the standard `S²`
norm requires Grönwall and gives only iterated contraction). -/
theorem picardFixedPoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (_coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (_x₀ : Fin n → ℝ) (T : ℝ) (_hT : 0 < T)
    [MetricSpace (SBoundedProcess (n := n) P T)]
    [Nonempty (SBoundedProcess (n := n) P T)]
    [CompleteSpace (SBoundedProcess (n := n) P T)]
    {K : NNReal} {Φ : SBoundedProcess (n := n) P T → SBoundedProcess (n := n) P T}
    (hΦ : ContractingWith K Φ) :
    ∃! X : SBoundedProcess (n := n) P T, Φ X = X :=
  picardFixedPoint_generic hΦ

/-- **Convenience corollary — Picard fixed point in the user's
existential-bundle form.** Same content as `picardFixedPoint`, but
expressed with the contraction packaged as an existential
`∃ (Φ : ...) (K : ℝ≥0) (_hK : K < 1), LipschitzWith K Φ`.

This matches the natural form a downstream caller would obtain from
the (downstream) `picardStep_bielecki_contraction` lemma: that lemma
produces the map `Φ`, the rate `K`, the proof `K < 1`, and the
Lipschitz bound, all bundled together.

The conclusion strips out a witness `Φ` from the existential and
delivers its unique fixed point. -/
theorem picardFixedPoint_of_exists
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (_coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (_x₀ : Fin n → ℝ) (T : ℝ) (_hT : 0 < T)
    [MetricSpace (SBoundedProcess (n := n) P T)]
    [Nonempty (SBoundedProcess (n := n) P T)]
    [CompleteSpace (SBoundedProcess (n := n) P T)]
    (h_contraction :
      ∃ (Φ : SBoundedProcess (n := n) P T → SBoundedProcess (n := n) P T)
        (K : NNReal) (_hK : K < 1),
          ∀ X Y : SBoundedProcess (n := n) P T, edist (Φ X) (Φ Y) ≤ K * edist X Y) :
    ∃ (Φ : SBoundedProcess (n := n) P T → SBoundedProcess (n := n) P T),
      ∃! X : SBoundedProcess (n := n) P T, Φ X = X := by
  -- Unpack the contraction existential.
  obtain ⟨Φ, K, hK_lt_one, hΦ_lip⟩ := h_contraction
  -- Build a `ContractingWith K Φ`: the contraction is the conjunction of
  -- `K < 1` (given by `hK_lt_one`) and `LipschitzWith K Φ`. The latter is
  -- definitionally `∀ x y, edist (Φ x) (Φ y) ≤ K * edist x y`, which is
  -- precisely `hΦ_lip`.
  have hΦ : ContractingWith K Φ := ⟨hK_lt_one, hΦ_lip⟩
  exact ⟨Φ, picardFixedPoint_generic hΦ⟩

/-- **Banach fixed-point output for the jump-diffusion SDE.**

Under Lipschitz hypotheses on `(μ, σ, γ)`, the Picard iteration in the
Banach space `S²([0, T]; ℝⁿ)` with the Bielecki β-norm
`‖X‖_β,T = sup_{t ≤ T} e^{-βt} √(𝔼[‖X_t‖²])` for `β > n L² T / 2`
delivers a unique fixed point of the Picard map `Φ` (`picardStep`). This
fixed point is a càdlàg-adapted L²-sup-bounded process satisfying the
SDE integral equation, and bundles into a `JumpDiffusion W N coeffs x₀`.

The "exists + a.s. unique" form below is the direct output of the
Banach fixed-point step (`ContractingWith.fixedPoint` +
`ContractingWith.fixedPoint_unique` — see `picardFixedPoint_generic`
in this file): the fixed point is the limit of Picard iterates `Φⁿ X₀`
for any starting `X₀`, and every other fixed point coincides with it
(so any two `JumpDiffusion` solutions, both being fixed points of Φ,
must agree a.s. at every `t`).

**Reference**: Applebaum 2009 Theorem 6.2.9; Ikeda-Watanabe IV.

**Status (2026-05-23, Rule-1 progress)**: sorry body — the contraction
proof is broken across the `Picard.lean` scaffolding (drift
L²-Lipschitz, Cauchy-Schwarz, Bielecki weight bound, contraction-rate
threshold, σ/γ measurability) plus parallel agent work on σ and γ
Lipschitz analogs of `picardStep_drift_diff_lintegral_sq_bound`. When
those land, combined with the Bielecki β-norm completeness instance
on `SBoundedProcess` (downstream work — `S²` Banach-space structure
via the standard quotient by P-null sets), this intermediate becomes
mechanically derivable via the `picardFixedPoint_of_exists` shim. -/
theorem picardFixedPoint_jumpDiffusion_exists_unique
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    {L : ℝ}
    (_hL : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L) :
    ∃ (jd : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀),
      ∀ (jd' : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀),
        ∀ t : ℝ, ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω := by
  -- **Proof skeleton (downstream work):**
  --
  -- The full Picard-iteration argument needs three independent pieces of
  -- substantive infrastructure that are NOT yet in the codebase:
  --
  -- 1. **`MetricSpace (SBoundedProcess P T)` + `CompleteSpace` instance** —
  --    the Bielecki β-norm metric on the S² Banach space of càdlàg
  --    L²-bounded processes, with the standard quotient-by-P-null-sets
  --    completeness argument. (Mathlib has `MeasureTheory.Lp` Banach
  --    structure for fixed-time L²; the path-space S² Banach structure
  --    is the standard extension.)
  --
  -- 2. **`Φ : SBoundedProcess P T → SBoundedProcess P T` lifting of
  --    `picardStep`** — promoting the Picard map from the unstructured
  --    function space `ℝ → Ω → (Fin n → ℝ)` to the structured S² space.
  --    Requires showing `picardStep` preserves joint measurability +
  --    càdlàg + L²-sup-bound (using the L²-isometry / boundedness of the
  --    component Itô integrals).
  --
  -- 3. **`ContractingWith K Φ` proof** — the Bielecki contraction
  --    estimate combining `bielecki_weighted_integral_bound` (in
  --    `Picard.lean`) with the per-component L²-Lipschitz bounds on the
  --    drift step (in `Picard.lean`), diffusion step (parallel Agent 1
  --    work in progress — `PicardSigmaLipschitz.lean`), and jump step
  --    (parallel Agent 2 work in progress — `PicardGammaLipschitz.lean`).
  --
  -- Once (1), (2), (3) are in place, the Banach shim `picardFixedPoint`
  -- delivers a unique fixed point `X : SBoundedProcess`, which by
  -- (2) bundles into a `JumpDiffusion` satisfying the SDE equation.
  -- Uniqueness in the headline statement then follows from
  -- `picardFixedPoint`'s `∃!`: any other `JumpDiffusion`, lifted to a
  -- fixed point of `Φ`, must equal `X`.
  --
  -- For the present commit, we mark this as the sole baseline sorry of
  -- the Picard chain. The (much larger) chain of helper lemmas in
  -- `Picard.lean` is sorry-free, as is the Banach shim above; only
  -- this single assembly step remains.
  sorry

end LevyStochCalc.Ito.Picard

/-! ## Literature theorem: `JumpDiffusion.exists_unique`

This is the headline existence-and-uniqueness theorem cited from
Applebaum 2009 Theorem 6.2.9 / Ikeda-Watanabe IV. Its qualified name is
`LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` — we re-open
that namespace explicitly here so the original location in
`Ito/Setting.lean` (a module that this file imports) is preserved at
the level of qualified names.

**Why the theorem lives here, not in `Ito/Setting.lean`**: the proof
forwards through `picardFixedPoint_jumpDiffusion_exists_unique` (above),
which is the SDE-specialised Banach fixed-point output. Putting the
theorem in `Ito/Setting.lean` would require `Setting.lean` to import
`Picard.lean` and `PicardBanach.lean`, creating a cycle (both already
import `Setting.lean` for the `JumpDiffusion` structure definition).
Forwarding through the Banach intermediate is the canonical pattern
(mirrors the `itoIsometry_brownian_unified_existence` → `itoIsometry`
derived-theorem forwarding used in `Brownian/Ito.lean`, and the
`itoIsometry_compensated_unified_existence` → `Compensated.itoLevyIsometry`
forwarding in `Poisson/Compensated.lean`).

The intermediate `picardFixedPoint_jumpDiffusion_exists_unique` is the
SINGLE remaining baseline-sorry on this chain — when the Picard
contraction proof + Banach fixed-point invocation is completed, the
intermediate gets a real proof body and `JumpDiffusion.exists_unique`
inherits soundness automatically without source-level changes here. -/

namespace LevyStochCalc.Ito.Setting
namespace JumpDiffusion

/-- **Existence and uniqueness of the jump-diffusion SDE
(Applebaum 6.2.9 / Ikeda-Watanabe IV).**

Under Lipschitz hypotheses on `(μ, σ, γ)`, the jump-diffusion SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`,
  `X_0 = x_0`

admits a strong solution that is càdlàg, adapted, L²-bounded in the
supremum norm on every bounded interval, and **a.s. unique** (any two
solutions agree a.s. at every time `t ≥ 0`).

**Reference**: Applebaum, D. *Lévy Processes and Stochastic Calculus*,
2nd ed., Cambridge University Press, 2009, **Theorem 6.2.9**;
Ikeda, N. & Watanabe, S. *Stochastic Differential Equations and
Diffusion Processes*, North-Holland, 1989, Chapter IV.

**Proof**: Forwarder over
`LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique`,
the SDE-specialised Banach fixed-point output. The statement is
unchanged from the previous sorry-bodied version in `Ito/Setting.lean`;
the move here reflects the canonical refactor pattern where the
literature theorem's proof forwards through the underlying analytical
machinery (which lives in a separate module to break the import cycle
between the structure definition and the framework). -/
theorem exists_unique
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    {L : ℝ} (hL : JumpDiffusionCoeffs.IsLipschitz coeffs ν L) :
    ∃ (jd : JumpDiffusion W N coeffs x₀),
      ∀ (jd' : JumpDiffusion W N coeffs x₀),
        ∀ t : ℝ, ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω :=
  LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique
    W N coeffs x₀ hL

/-- **Pairwise a.s. agreement at `t = 0`.** Any two jump-diffusion
solutions for the same coefficients and initial condition agree a.s.
at `t = 0`. This is the degenerate-time slice of the headline a.s.
uniqueness conclusion that follows DIRECTLY from each structure's
`initial_value : ∀ᵐ ω, X 0 ω = x₀` field, WITHOUT invoking the
Picard/Banach contraction machinery. Useful as a public extractor for
downstream callers needing the `t = 0` uniqueness in isolation
(e.g. consistency checks on user-supplied JumpDiffusion candidates). -/
theorem agree_at_zero
    {Ω : Type*} [MeasurableSpace Ω]
    {E : Type*} [MeasurableSpace E]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
    {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
    {coeffs : JumpDiffusionCoeffs n d E}
    {x₀ : Fin n → ℝ}
    (jd jd' : JumpDiffusion W N coeffs x₀) :
    ∀ᵐ ω ∂P, jd.X 0 ω = jd'.X 0 ω := by
  -- Both jd.X 0 = x₀ a.s. and jd'.X 0 = x₀ a.s. ; transitivity through the
  -- common value x₀ gives jd.X 0 = jd'.X 0 a.s. on the intersection of
  -- the two a.s. events, which is itself a.s.
  filter_upwards [jd.initial_value, jd'.initial_value] with ω h₁ h₂
  rw [h₁, h₂]

end JumpDiffusion
end LevyStochCalc.Ito.Setting
