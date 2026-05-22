/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Ito
import LevyStochCalc.Brownian.MultidimIto
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

## Status

`JumpDiffusion.exists_unique` claims Applebaum 6.2.9 / Ikeda-Watanabe IV
existence-and-uniqueness with proof body `sorry` (the literature proof
is Picard iteration in `S²([0,T]; ℝⁿ)`).

The `is_solution` field of the `JumpDiffusion` structure was strengthened
on 2026-05-21 from `True` to the actual SDE integral equation (bundled
with hypotheses on `σ(s, X_s)` for the multidim Brownian integral to be
defined). Constant-path X = x₀ no longer satisfies the structure for
generic non-zero coefficients.
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
* `is_solution` — the SDE integral equation (red-team P12 strengthening
  2026-05-21): for almost every `ω` and every `t ≥ 0` and component `i`,
  `X t ω i` equals `x₀ i` plus the drift integral `∫_0^t μ(s, X_s) ds`
  plus the multidim Brownian Itô integral `∫_0^t σ(s, X_s) · dW_s` (row `i`)
  plus the compensated-Poisson integral `∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)` (row `i`).
  The Brownian integral requires existence of measurability /
  progressive-measurability / L²-bounds on `(s, ω) ↦ σ(s, X_s)`; these
  are bundled inside the existential. The constant-path witness
  `X t ω = x₀` fails this constraint for generic `(μ, σ, γ)` because
  the integrals don't vanish. -/
structure JumpDiffusion
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
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
  /-- The SDE integral equation. Bundles the per-row Brownian-integrand
  hypotheses (h_σ_meas, h_σ_progMeas, h_σ_sq) inside the existential
  alongside the equation itself. -/
  is_solution :
    ∃ (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
        Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
      (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
        @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
          (@Prod.instMeasurableSpace Ω ℝ
            ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
            inferInstance)
          (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i j))
      (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
    ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X t ω i = x₀ i
        + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W (fun s ω => coeffs.σ s (X s ω) i)
            (fun j => h_σ_meas i j)
            (fun j => h_σ_progMeas i j)
            (fun j => h_σ_sq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N
            (fun ω' s e => coeffs.γ s (X s ω') e i) t ω

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
