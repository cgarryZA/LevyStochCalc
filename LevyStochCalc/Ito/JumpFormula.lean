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
    -- 2026-05-21 strengthening (red-team C2 + P12 + statement-level fix):
    -- the `jump_mart` term is now PINNED to the canonical compensated-Poisson
    -- stochastic integral of the jump increment `u(s, X_s + γ(s, X_s, e)) −
    -- u(s, X_s)`. Previously all four reals were unbound existentials, admitting
    -- the trivial witness `drift = change, diff_mart = jump_mart = comp_drift = 0`.
    -- Pinning jump_mart removes one degree of freedom from the trivial-witness
    -- attack. (The remaining `drift_term, diff_mart, comp_drift` are still
    -- unbound — future strengthening will pin those to their literature
    -- integral forms once the Mathlib derivative apparatus is threaded in.)
    ∃ (drift_term diff_mart comp_drift : Ω → ℝ),
      (∀ᵐ ω ∂P,
        u T (X.X T ω) - u 0 (X.X 0 ω) =
          drift_term ω + diff_mart ω
          + LevyStochCalc.Poisson.Compensated.stochasticIntegral N
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                              - u s (X.X s ω')) T ω
          + comp_drift ω)

end LevyStochCalc.Ito.JumpFormula
