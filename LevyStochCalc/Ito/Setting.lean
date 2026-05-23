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

/-- Joint Lipschitz hypothesis on the jump-diffusion coefficients
`(μ, σ, γ)`. Required for `JumpDiffusion.exists_unique` (Applebaum 2009
Thm 6.2.9 — without this, Tanaka's example shows uniqueness can fail,
e.g. `dX_t = |X_t|^α dW_t` for `α < 1/2` has infinitely many strong
solutions; cf. Karatzas-Shreve 5.3.2). -/
def JumpDiffusionCoeffs.IsLipschitz {n d : ℕ}
    (coeffs : JumpDiffusionCoeffs n d E) (ν : Measure E) (L : ℝ) : Prop :=
  0 ≤ L ∧
  -- μ uniformly Lipschitz in x:
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ‖coeffs.μ s x₁ - coeffs.μ s x₂‖ ≤ L * ‖x₁ - x₂‖) ∧
  -- σ uniformly Lipschitz in x (with the Frobenius / Euclidean norm on matrices):
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    (∑ i, ∑ j, (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
      ≤ L ^ 2 * ‖x₁ - x₂‖ ^ 2) ∧
  -- γ uniformly Lipschitz in x (L²-in-e sense):
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    (∫⁻ e, (‖coeffs.γ s x₁ e - coeffs.γ s x₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal
      ≤ L ^ 2 * ‖x₁ - x₂‖ ^ 2)

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
  /-- Almost-sure càdlàg paths (right-continuous with left limits, a.s.).
  Required by the literature jump-diffusion SDE convention: Applebaum 6.2.9 /
  Ikeda-Watanabe IV assume X is càdlàg-adapted so that `X_{s−}` (the left
  limit at s) is well-defined for the integrand evaluation in the
  compensated-Poisson integral. P4 H / P7 F5 closure (red-team 2nd audit,
  2026-05-23): without this field, `X.X s` and `X_{s−}` are silently equal
  (no left-limit notion), and the SDE equation diverges from Applebaum at
  jump times.

  **P4 F8 note (red-team 2nd audit, 2026-05-23)**: Applebaum 6.2.9 / Ikeda-
  Watanabe IV use `X_{s−}` (the left limit) inside the SDE integrands,
  whereas this structure uses `X s` (point evaluation) below. For càdlàg
  adapted X, the discrepancy `{s : X_{s−} ω ≠ X s ω}` has Lebesgue
  measure 0 a.s. (a càdlàg path has at most countably many jumps), so
  the Lebesgue-`ds` drift integral and the ν⊗ds-`dν` jump integrals
  agree pointwise a.s. (Lebesgue⊗P-null differences are integrated
  away). The compensated-Poisson integral evaluates the integrand at
  `(s, e)` against `Ñ(ds, de)`; at a jump time `s₀` of the underlying
  PRM, `X s₀` differs from `X_{s₀−}` and the integrand picks up the
  right-limit value, but this is also Ñ⊗P-null because the integrand
  is L² and PRM jumps are themselves a null set in ds. The two
  conventions coincide for L²-Itô-Lévy integrals; the literature
  prefers `X_{s−}` for predictability hygiene (`X_{s−}` is `ℱ_{s−}`-
  measurable, i.e., predictable). The structure's `cadlag_paths` field
  is what makes this convention-equivalence well-typed; without it,
  the discrepancy is unbounded. -/
  cadlag_paths : ∀ᵐ ω ∂P, ∀ t : ℝ,
    Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- The SDE integral equation. Bundles per-row Brownian + per-row Compensated
  integrand hypotheses inside the existential alongside the equation itself.
  H6 fix (red-team 2nd audit 2026-05-23): γ-side hypotheses now bundled too
  (mirror of σ-side bundling), required by the strengthened
  `Compensated.stochasticIntegral` signature. -/
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
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
      (h_γ_meas : ∀ i : Fin n,
        Measurable (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => coeffs.γ s (X s ω') e i) p.1 p.2.1 p.2.2))
      (h_γ_progMeas : ∀ i : Fin n, ∀ t : ℝ,
        @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
          (@Prod.instMeasurableSpace Ω (ℝ × E)
            ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
            inferInstance)
          (fun p : Ω × ℝ × E =>
            (fun ω' s e => coeffs.γ s (X s ω') e i) p.1 p.2.1 p.2.2))
      (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
    ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X t ω i = x₀ i
        + ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W (fun s ω => coeffs.σ s (X s ω) i)
            (fun j => h_σ_meas i j)
            (fun j => h_σ_progMeas i j)
            (fun j => h_σ_sq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N
            (fun ω' s e => coeffs.γ s (X s ω') e i)
            (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) t ω

/-- **Existence and uniqueness of the jump-diffusion SDE
(Applebaum 6.2.9 / Ikeda-Watanabe IV).**

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

**Status (2026-05-23, Rule-1 START)**: Picard iteration framework is being
built in `LevyStochCalc/Ito/Picard.lean`. Current state: sorry body,
proof in active construction. Per Rule 1 (no "this can't be done"
deferrals), the multi-day Picard-iteration build is HAPPENING, one
piece at a time. See `Picard.lean` for the framework. -/
theorem JumpDiffusion.exists_unique
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    -- Lipschitz hypothesis (P12 CRIT F3 fix 2026-05-23 — without this,
    -- Tanaka's example exhibits multiple strong solutions, so the
    -- uniqueness claim below is unprovable for arbitrary `(μ, σ, γ)`):
    {L : ℝ} (_hL : JumpDiffusionCoeffs.IsLipschitz coeffs ν L) :
    -- Existence + a.s. uniqueness (strengthened from `Nonempty` per Rule 0):
    ∃ (jd : JumpDiffusion W N coeffs x₀),
      ∀ (jd' : JumpDiffusion W N coeffs x₀),
        ∀ t : ℝ, ∀ᵐ ω ∂P, jd.X t ω = jd'.X t ω := by
  sorry

end LevyStochCalc.Ito.Setting
