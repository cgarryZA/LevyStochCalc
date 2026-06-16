/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardSpace
import Mathlib.Topology.MetricSpace.Contracting

/-!
# Existence and uniqueness via the Banach fixed-point theorem

This file applies Banach's fixed-point theorem (`ContractingWith.fixedPoint`)
to the Picard map: the contraction estimate of `Picard.lean` together with
the complete-metric-space structure of `PicardSpace.lean` yield the
existence/uniqueness theorem for the jump-diffusion SDE.

## Contents

* `picardFixedPoint_generic`, `picardFixedPoint`, `picardFixedPoint_of_exists`
  — the abstract fixed-point packaging.
* `picardFixedPoint_jumpDiffusion_exists_unique` — the concrete
  existence/uniqueness statement for the jump-diffusion SDE.
* `JumpDiffusion.exists_unique`, `JumpDiffusion.agree_at_zero` — the form
  consumed by `Ito/Setting.lean`.
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

**Typeclass-placeholder notice:**
when invoked with the *default* `MetricSpace` / `CompleteSpace` instances
on `SBoundedProcess P T` (the discrete-metric instances installed in
`PicardSpace.lean`), this theorem is **typeclass-trivial**: a contraction
on the discrete metric collapses to the identity on the fixed-point
fibre, completeness is vacuous (Cauchy sequences are eventually
constant), and the unique fixed point is the starting iterate. NO
SUBSTANTIVE MATHEMATICAL CONTENT is carried by the discrete-metric
specialisation — it discharges the typeclass obligation only.

The literature-substantive Banach work (Bielecki β-weighted L²-sup
norm with genuine contraction at the analytical rate
`3 n L² (T+2) / (2β)` for `β > 3 n L² (T+2) / 2`) lives in
`LevyStochCalc.Ito.PicardSpace`: the genuine metric on the
AE-quotient `AEQuot β T` and the `CompleteSpace` instance (via Lp
completeness + Doob càdlàg modification), and the SDE chain wraps up via
`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` there. **Downstream consumers needing the actual SDE strong-existence
result should use the `_via_aeQuot` wrap-up theorem, not this
typeclass-shim theorem applied on `SBoundedProcess`.**

The hypothesis bundle:

* `[MetricSpace (SBoundedProcess P T)]` — the `S²` / Bielecki metric on
  the càdlàg L²-bounded process space (the discrete-metric instance
  from `PicardSpace.lean` is one canonical choice — but typeclass-
  trivial as above; the Bielecki β-norm on the `AEQuot` quotient from
  `PicardSpace.lean` is the literature choice).
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

This form uses the globally-available instances on `SBoundedProcess`
(from `PicardSpace.lean`: discrete metric + Cauchy-eventually-constant
completeness — typeclass-placeholders only). Substantive Bielecki work
uses `AEQuot β T` instead, where the Bielecki β-norm is a genuine
metric. -/
theorem picardFixedPoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (_coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (_x₀ : Fin n → ℝ) (T : ℝ) (_hT : 0 < T)
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

/-- **SDE-specialised Banach fixed-point output for the jump-diffusion
equation (Applebaum 6.2.9 / Ikeda-Watanabe IV) — ex-Tier-1-axiom #14,
now a theorem.**

Under Lipschitz hypotheses on `(μ, σ, γ)`, the Picard iteration in the
Banach space `S²([0, T]; ℝⁿ)` with the Bielecki β-norm
`‖X‖_β,T = sup_{t ≤ T} e^{-βt} √(𝔼[‖X_t‖²])` for `β > 3 n L² (T + 2) / 2`
delivers a unique fixed point of the Picard map `Φ` (`picardStep`). This
fixed point is a càdlàg-adapted L²-sup-bounded process satisfying the
SDE integral equation, and bundles into a `JumpDiffusion W N coeffs x₀`.

The "exists + a.s. unique" form is the direct output of the
Banach fixed-point step (`ContractingWith.fixedPoint` +
`ContractingWith.fixedPoint_unique` — see `picardFixedPoint_generic`
in this file): the fixed point is the limit of Picard iterates `Φⁿ X₀`
for any starting `X₀`, and every other fixed point coincides with it
(so any two `JumpDiffusion` solutions, both being fixed points of Φ,
must agree a.s. at every `t ≥ 0` — the SDE time domain).

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd
ed., CUP 2009, **Theorem 6.2.9** (Picard iteration in `S²` for jump-
diffusion SDEs with Lipschitz coefficients); Ikeda-Watanabe, *Stochastic
Differential Equations and Diffusion Processes*, North-Holland 1989,
Chapter IV (jump SDE strong existence + uniqueness via Picard iteration).

This forwards through the wrap-up theorem
`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` in `PicardSpace.lean`,
which carries the single baseline `sorry` collecting the entire Picard chain
(six steps; see that file's module docstring). The analytical content is the
Picard iteration in `S²([0, T]; ℝⁿ)` (Applebaum 6.2.9). The downstream
forwarders `picardFixedPoint_jumpDiffusion_exists_unique` and the headline
`JumpDiffusion.exists_unique` consume this; the `sorry` is tracked in
`tools/sorry_baseline.txt` via the wrap-up theorem name.

**Signature strength**: requires `JumpDiffusionCoeffs.IsLipschitz coeffs
ν L` (Tanaka's `|X|^α` counterexample for α < 1/2 rules out uniqueness
without this); produces a CONCRETE `JumpDiffusion` (all six fields
populated — `X`, `measurable_path`, `initial_value`, `sup_L2`,
`cadlag_paths`, `is_solution`) plus the a.s. pairwise agreement at
every `t ≥ 0` (the literature uniqueness conclusion). No trivial
constant-path witness satisfies this for generic non-zero coefficients:
`X t ω = x₀` fails `is_solution` because the integrals don't vanish.

**Quantifier scope**: pairwise a.s. agreement is asserted on the SDE time
domain `t ≥ 0` only, matching the literature scope (Applebaum 6.2.9 /
Ikeda-Watanabe IV work on `[0, ∞)`; the SDE integral equation in
`JumpDiffusion.is_solution` is itself quantified over `t ≥ 0`). -/
theorem picardFixedPoint_jumpDiffusion_exists_unique_axiom
    {Ω : Type u} [MeasurableSpace Ω]
    {E : Type v} [MeasurableSpace E]
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
        ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω :=
  picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot W N coeffs x₀ hL

/-- **Banach fixed-point output for the jump-diffusion SDE — forwarding theorem.**

Thin forwarder over the (now-)theorem
`picardFixedPoint_jumpDiffusion_exists_unique_axiom` (above), which in
turn forwards through `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`
in `PicardSpace.lean`. The single explicit `sorry` for
the entire Picard chain lives in that wrap-up theorem; this forwarder
is sorry-free in source but transitively depends on the chain.

The Picard contraction analysis (drift / diffusion / jump
L²-Lipschitz bounds + Bielecki β-norm contraction at rate `3 n L² (T+2) / (2β)`
for `β > 3 n L² (T+2) / 2`) is fully proven downstream in `Ito/Picard.lean`,
`Ito/Picard.lean`, `Ito/Picard.lean`, and
`Ito/Picard.lean`; the remaining sorry covers the Bielecki
`S²` Banach-space packaging (`Lp` completeness + Doob càdlàg modification)
+ the structure bridge into `JumpDiffusion`.

**Reference**: Applebaum 2009 Theorem 6.2.9; Ikeda-Watanabe IV. -/
theorem picardFixedPoint_jumpDiffusion_exists_unique
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
        ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω :=
  picardFixedPoint_jumpDiffusion_exists_unique_axiom W N coeffs x₀ hL

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
`Picard.lean` and `PicardFixedPoint.lean`, creating a cycle (both already
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
solutions agree a.s. at every time `t ≥ 0`; the SDE time domain
`[0, ∞)` is the literature scope — Applebaum 6.2.9 / Ikeda-Watanabe IV).

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
        ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω :=
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
