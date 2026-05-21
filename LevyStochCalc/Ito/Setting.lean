import LevyStochCalc.Brownian.Ito
import LevyStochCalc.Poisson.L2Isometry

/-!
# Layer 2 substrate: Jump-diffusion process structure

A *jump diffusion* on `ℝⁿ` driven by a `d`-dimensional Brownian motion `W` and
a Poisson random measure `N` (with intensity `dt ⊗ ν` on `[0,T] × E`) is the
solution of the SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`,

with `X_0 = x_0`. Under Lipschitz `(μ, σ, γ)` (uniform in `(t, e)`; for `γ`,
`L²(ν)`-Lipschitz), the SDE admits a unique càdlàg adapted solution with
`𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`.

Reference: Applebaum 2009 Ch 6; user's dissertation
[ch02_mathematical_framework.tex](D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex)
eq (jump-diffusion) at line 41.

## Status

Phase 2 spec: `JumpDiffusion` structure carries `is_solution : Prop` field
that asserts the path map `X` is measurable and starts at the prescribed
initial condition. The full SDE-validity hypothesis (involving Itô + Poisson
integrals along `X`) is layered on top once those integrals are defined.

**Red-team note (2026-05-21, P01/P02/P03/P04/P05/P07/P10/P12).** The
`is_solution : True` field is a known stub — the actual SDE integral
equation (drift integral + Itô Brownian integral + compensated-Poisson
integral) is not enforced. Anything jointly measurable with the right
initial value satisfies the structure. The `exists_unique` theorem below
was previously a `theorem` with a constant-path trivial-witness proof
(`X t ω := x₀`, `is_solution := trivial`). On 2026-05-21 it was demoted
to a documented `axiom` citing Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe
Ch IV, and renamed from `exists_unique` to `exists` since the previous
theorem proved no uniqueness despite the name.

Replacing `is_solution : True` with the actual SDE integral equation is
the substantive follow-up; it requires multidim Brownian + compensated-
Poisson stochastic integrals along the X-path, which in turn require
the integrand to be the path-dependent process `s ↦ μ(s, X_s)` etc.
Tracked as future work in the red-team summary.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Setting

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Coefficient bundle for a jump diffusion: drift `μ`, diffusion `σ`, jump
size `γ`. Lipschitz / measurability hypotheses live on the headline theorem. -/
structure JumpDiffusionCoeffs (n d : ℕ) (E : Type v) where
  μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)
  γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)

/-- A *jump diffusion* solution. The `is_adapted` field asserts the path map
is measurable in `ω` for each `t`; the full SDE-satisfaction predicate is
layered on top once the Itô + compensated-Poisson integrals are
defined (Phase 3). -/
structure JumpDiffusion
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (_N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) where
  /-- The path map. -/
  X : ℝ → Ω → (Fin n → ℝ)
  /-- The path map is jointly measurable in `(t, ω)`. -/
  measurable_path : Measurable (Function.uncurry X)
  /-- Almost-sure initial condition: `X_0 = x_0`. -/
  initial_value : ∀ᵐ ω ∂P, X 0 ω = x₀
  /-- Square-integrable supremum: `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞` for every `T`.
  Stated component-wise via the `Fin n` Euclidean structure, with the supremum
  taken over `Set.Icc 0 T` viewed as a subtype (so the empty case is automatic
  when `0 ≤ T`). -/
  sup_L2 : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X t.1 ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
  /-- The SDE itself: stubbed, since the integrals along `X` require Phase 3
  development. -/
  is_solution : True

/-- **Existence of the jump-diffusion SDE (Applebaum 2009 Thm 6.2.9).**

Under Lipschitz hypotheses on `(μ, σ, γ)`, the jump-diffusion SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`,
  `X_0 = x_0`

admits a strong solution that is càdlàg, adapted, and L²-bounded in
the supremum norm on every bounded interval.

**Reference**: Applebaum, D. *Lévy Processes and Stochastic Calculus*,
2nd ed., Cambridge University Press, 2009, **Theorem 6.2.9**;
Ikeda, N. & Watanabe, S. *Stochastic Differential Equations and
Diffusion Processes*, North-Holland, 1989, Chapter IV.

**Status (2026-05-21 — DEMOTED to axiom per red-team P01/P02/P03/P04/P05/P07/P10/P12)**:
this was previously a `theorem` whose proof body was the trivial-witness
pattern

  `refine ⟨{X := fun _ _ => x₀, …, is_solution := trivial}⟩`

— a constant path `X t ω = x₀` populating the `JumpDiffusion` structure
whose `is_solution : True` field accepts anything. The existential
`Nonempty (JumpDiffusion …)` is thus trivially satisfiable without
solving any SDE. Demoted to a documented `axiom` carrying the literature
citation. The previous name `exists_unique` claimed uniqueness that the
proof did not establish; renamed to `exists`.

**Replacement plan**: when (a) the `JumpDiffusion` structure's
`is_solution : True` field is upgraded to the actual SDE integral
equation (requires multidim Brownian + compensated-Poisson stochastic
integrals along the X-path), and (b) the Lipschitz / L² hypotheses are
threaded through, this `axiom` can be replaced by a real Picard
iteration proof. Multi-session work. -/
axiom JumpDiffusion.exists
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) :
    Nonempty (JumpDiffusion W N coeffs x₀)

end LevyStochCalc.Ito.Setting
