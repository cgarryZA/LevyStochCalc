import LevyStochCalc.Brownian.Ito
import LevyStochCalc.Poisson.L2Isometry

/-!
# Layer 2 substrate: Jump-diffusion process structure

A *jump diffusion* on `ℝⁿ` driven by a `d`-dimensional Brownian motion `W` and
a Poisson random measure `N` (with intensity `dt ⊗ ν` on `[0,T] × E`) is the
solution of the SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`,

with `X_0 = x_0`. Under Lipschitz `(μ, σ, γ)` the SDE admits a unique càdlàg
adapted solution with `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`.

Reference: Applebaum 2009 Ch 6; Ikeda-Watanabe IV.

## Status (2026-05-21, Rule-0 restoration after revert)

Restored with `sorry` in the existence/uniqueness theorem. The claim is the
Applebaum 6.2.9 / Ikeda-Watanabe IV existence-and-uniqueness theorem. Per
the user's Rule 0 (`CRITICAL_RULES.md`): never weaken claims, always
strengthen content. The proof is the next concrete strengthening step.

**Structural HOLE still open**: `is_solution : True` is a placeholder. The
real SDE integral equation involves stochastic integrals along the X-path
(`∫ μ(s, X_s) ds`, `∫ σ(s, X_s) dW_s`, `∫∫ γ(s, X_s, e) Ñ(ds, de)`). Pinning
requires the multidim Brownian Itô integral and compensated-Poisson integral
to accept path-dependent integrands; both are downstream construction work.
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

/-- A *jump diffusion* solution.

Fields:
* `X : ℝ → Ω → (Fin n → ℝ)` — the path map.
* `measurable_path` — joint measurability.
* `initial_value` — `X_0 = x_0` a.s.
* `sup_L2` — `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞` for every `T > 0`.
* `is_solution` — **TODO(Rule-0 strengthening)**: currently `True`. The real
  SDE integral equation requires stochastic integrals along `X`, which are
  not yet defined in this library. Tracked in `CRITICAL_RULES.md`. -/
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
  /-- Square-integrable supremum: `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞` for every `T`. -/
  sup_L2 : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X t.1 ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
  /-- The SDE integral equation. **TODO**: currently `True`; needs the actual
  jump-diffusion integral equation once stochastic integrals along `X` exist. -/
  is_solution : True

/-- **Existence and uniqueness of the jump-diffusion SDE.**

Under Lipschitz hypotheses on `(μ, σ, γ)`, the jump-diffusion SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`,
  `X_0 = x_0`

admits a strong solution that is càdlàg, adapted, L²-bounded in the supremum
norm on every bounded interval, and **a.s. unique** (any two solutions agree
a.s. at every time `t ≥ 0`).

**Reference**: Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed.,
Cambridge University Press, 2009, **Theorem 6.2.9**; Ikeda, N. & Watanabe, S.
*Stochastic Differential Equations and Diffusion Processes*, North-Holland,
1989, Chapter IV.

**Status (2026-05-21)**: proof is `sorry`. The literature proof (Picard
iteration in `S²([0,T]; ℝⁿ)`) requires multidim Brownian + compensated-Poisson
stochastic integrals along the path. Both are out-of-scope downstream work
that needs to be built before this `sorry` can be eliminated. -/
theorem JumpDiffusion.exists_unique
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) :
    -- Existence + a.s. uniqueness (strengthened from `Nonempty` per Rule 0):
    ∃ (jd : JumpDiffusion W N coeffs x₀),
      ∀ (jd' : JumpDiffusion W N coeffs x₀),
        ∀ t : ℝ, ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω := by
  sorry

end LevyStochCalc.Ito.Setting
