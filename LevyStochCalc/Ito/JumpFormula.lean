import LevyStochCalc.Ito.Setting

/-!
# Layer 2 (deaxiomatises Cu03): Itô-Lévy formula for jump diffusions

For `u ∈ C^{1,2}([0,T] × ℝⁿ)` and `X` a jump diffusion driven by
`(W, N)` with coefficients `(μ, σ, γ)`,

  `u(T, X_T) − u(0, X_0)`
  `= ∫_0^T (∂_t u + 𝓛u)(s, X_{s-}) ds`
  `+ ∫_0^T ∇u(s, X_{s-})ᵀ σ(s, X_{s-}) dW_s`
  `+ ∫_0^T ∫_E [u(s, X_{s-} + γ(s, X_{s-}, e)) − u(s, X_{s-})] Ñ(ds, de)`
  `+ ∫_0^T ∫_E [u(·+γ) − u − γᵀ ∇u](s, X_{s-}, e) ν(de) ds`,

where `𝓛u = μᵀ ∇u + ½ Tr(σ σᵀ ∇²u)` is the diffusion generator.

This file provides the Lean form of the formula. When CLEAN, the main
dissertation imports this module and replaces its
`Dissertation.Continuous.itoLevyFormula` axiom (Continuous.lean:146).

## Source

* Applebaum 2009, Theorem 4.4.7.
* User's dissertation
  [ch02_mathematical_framework.tex](D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex)
  eq (jump-ito) at lines 51-56.

## Status

**DEMOTED 2026-05-11 to `axiom` (Tier 1 cited).** Previous status: a
`theorem` whose proof body was the trivial-witness pattern `refine ⟨0,
0, 0, change, ?_⟩; simp` — three identically-zero processes with the
entire `u(T, X_T) − u(0, X_0)` stuffed into the fourth term. That
satisfied the existential trivially without engaging any drift /
diffusion-martingale / jump-martingale / compensator-drift content.
Per the recursive audit standard the user has been chasing, that
trivial-witness theorem was downgraded to a documented `axiom` with
the literature citation — better an honest axiom than a fake theorem.

A real proof would derive the four-term decomposition from
* the Brownian stochastic integral primitive
  (`Brownian.SimplePredictableRefine.stochasticIntegral`),
* the compensated-Poisson stochastic integral primitive
  (`Poisson.Compensated.stochasticIntegral`),
* the Lévy generator `𝓛u = μᵀ∇u + ½Tr(σσᵀ∇²u) + ∫(u(·+γ) − u − γᵀ∇u) ν`,
* and the càdlàg modification of the jump diffusion `X`.

That is multi-session work; deferred until each primitive carries the
correct semimartingale apparatus.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Gradient of `u : ℝ → (Fin n → ℝ) → ℝ` in its space argument, returning a
`Fin n → ℝ` vector. Equals `fderiv ℝ (u s) x (Pi.single i 1)` for each
component i; for non-differentiable u, Mathlib's `fderiv` returns 0 so
the gradient is 0. -/
noncomputable def gradient {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (s : ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i => fderiv ℝ (u s) x (Pi.single i 1)

/-- Row product `(∇u)ᵀ σ : Fin d → ℝ` of the gradient row vector with the
diffusion matrix `σ : Fin n → Fin d → ℝ`. -/
noncomputable def diffusionIntegrand {n d : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ))
    (s : ℝ) (x : Fin n → ℝ) : Fin d → ℝ :=
  fun j => ∑ i : Fin n, gradient u s x i * σ s x i j

/-- Compensator-drift integrand `u(s, x + γ(s, x, e)) − u(s, x) − γ(s, x, e)ᵀ ∇u(s, x)`.
This is the inner integrand of the compensator-drift term in the Itô–Lévy
formula (the Lévy-generator correction integrated against `ν(de) ds`). -/
noncomputable def compensatorDriftIntegrand {n : ℕ} {E : Type v}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ))
    (s : ℝ) (x : Fin n → ℝ) (e : E) : ℝ :=
  u s (x + γ s x e) - u s x - ∑ i : Fin n, γ s x e i * gradient u s x i

/-- **Cu03 (Itô-Lévy formula for jump diffusions, Applebaum 2009 Thm 4.4.7).**

For `C^{1,2}` functions `u` and a jump diffusion `X = (μ, σ, γ)`-driven by
`(W, N)`, the chain-rule decomposition

  `u(T, X_T) − u(0, X_0)`
  `= ∫_0^T (∂_t u + 𝓛u)(s, X_{s-}) ds`     -- drift_term
  `+ ∫_0^T ∇u(s, X_{s-})ᵀ σ(s, X_{s-}) dW_s`  -- diff_mart
  `+ ∫_0^T ∫_E [u(s, X_{s-} + γ(s, X_{s-}, e)) − u(s, X_{s-})] Ñ(ds, de)`  -- jump_mart
  `+ ∫_0^T ∫_E [u(·+γ) − u − γᵀ ∇u](s, X_{s-}, e) ν(de) ds`               -- comp_drift

holds almost surely, where `𝓛u = μᵀ∇u + ½Tr(σσᵀ∇²u)` is the diffusion
generator.

**Reference**: Applebaum, D. *Lévy Processes and Stochastic Calculus*,
2nd ed., Cambridge University Press, 2009, Theorem 4.4.7. See also
Cont, R. & Tankov, P. *Financial Modelling with Jump Processes*,
Chapman & Hall/CRC, 2003, Proposition 8.18.

**Status (2026-05-11):** declared as `axiom` because a previous `theorem`
form discharged the existential with three-zero-terms +
entire-change-stuffed-into-fourth (trivial-witness pattern). Demoted in
the recursive audit, with the literature citation preserved.

**Replacement plan:** real proof requires the full continuous-time
stochastic calculus apparatus (Brownian semimartingale, jump SDE with
Lévy generator, càdlàg modifications). Tracked in `tools/cited_axioms.md`
entry #11. -/
axiom itoLevyFormula
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (T : ℝ) (_hT : 0 < T) :
    -- 2026-05-22 strengthening (continuation of C2):
    -- * `jump_mart` PINNED to `Compensated.stochasticIntegral` of the jump
    --   increment `u(s, X_s + γ) − u(s, X_s)` (2026-05-21).
    -- * `diff_mart` PINNED to the multidim Brownian Itô integral of
    --   `diffusionIntegrand := ∇uᵀ σ` along X (2026-05-22 earlier).
    -- * `comp_drift` PINNED to the Lebesgue integral of the Lévy-generator
    --   correction `u(s, X_s + γ) − u(s, X_s) − γᵀ ∇u(s, X_s)` against
    --   `ν(de) ds` (2026-05-22, this commit).
    -- Remaining unbound: only `drift_term` (the `(∂_t u + Lu)(s, X_s) ds`
    -- Lebesgue integral, where `Lu = μᵀ∇u + ½Tr(σσᵀ∇²u)` needs the Hessian
    -- ∇²u which isn't yet defined as a helper).
    ∃ (drift_term : Ω → ℝ)
      (h_sigmaGrad_meas : ∀ j : Fin d,
        Measurable (Function.uncurry
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)))
      (h_sigmaGrad_progMeas : ∀ j : Fin d, ∀ t : ℝ,
        @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
          (@Prod.instMeasurableSpace Ω ℝ
            ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
            inferInstance)
          (fun p : Ω × ℝ => diffusionIntegrand u coeffs.σ p.2 (X.X p.2 p.1) j))
      (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤),
      (∀ᵐ ω ∂P,
        u T (X.X T ω) - u 0 (X.X 0 ω) =
          drift_term ω
          + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
              W (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω
          + LevyStochCalc.Poisson.Compensated.stochasticIntegral N
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                              - u s (X.X s ω')) T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)

end LevyStochCalc.Ito.JumpFormula
