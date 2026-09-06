/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Setting

/-!
# Itô-Lévy formula for jump diffusions

For `u ∈ C^{1,2}([0,T] × ℝⁿ)` and `X` a jump diffusion driven by
`(W, N)` with coefficients `(μ, σ, γ)`,

  `u(T, X_T) − u(0, X_0)`
  `= ∫_0^T (∂_t u + 𝓛u)(s, X_{s-}) ds`
  `+ ∫_0^T ∇u(s, X_{s-})ᵀ σ(s, X_{s-}) dW_s`
  `+ ∫_0^T ∫_E [u(s, X_{s-} + γ(s, X_{s-}, e)) − u(s, X_{s-})] Ñ(ds, de)`
  `+ ∫_0^T ∫_E [u(·+γ) − u − γᵀ ∇u](s, X_{s-}, e) ν(de) ds`,

where `𝓛u = μᵀ ∇u + ½ Tr(σ σᵀ ∇²u)` is the diffusion generator.

## Source

* Applebaum 2009, Theorem 4.4.7.

## Structure

`itoLevyFormula` is a `theorem` derived by algebra from the cited sub-primitive
`itoLevyFormula_jumpResidual_canonical_axiom` (cited axiom #16, Applebaum
4.4.10 + 4.4.7 step II): the canonical residual
`R_canonical T ω := u(T, X_T) − u(0, X_0) − drift − diff_mart` equals the sum
of the jump-martingale and compensator-drift terms. This is the whole content
of the Itô–Lévy formula; its continuous part is the Itô formula for the
Brownian Itô integral of this library (Karatzas–Shreve 3.3.6), and its jump
part is the small/large jump decomposition and the `ε → 0` limit through the
`L²`-isometry of the compensated-Poisson integral.

The universal-`R` form `itoLevyFormula_jumpResidual_axiom` is a derived theorem
forwarding over the canonical-`R` axiom by per-`ω` algebra. The qualified name
`LevyStochCalc.Ito.JumpFormula.itoLevyFormula` is preserved so the dissertation
forwarder is unaffected. (A former cited axiom #15, an unconstrained existential
residual for the continuous part, was retired on 2026-09-06: its statement was
satisfiable by the trivial residual and carried no content.)
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Integrands
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

/-- Time derivative `∂_t u (s, x)`. Returns 0 if u is not differentiable in t
at (s, x). -/
noncomputable def timeDeriv {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  deriv (fun t => u t x) s

/-- Hessian `∇²u (s, x) : Fin n → Fin n → ℝ`. Returns 0 entries where u is not
twice differentiable. -/
noncomputable def hessian {n : ℕ} (u : ℝ → (Fin n → ℝ) → ℝ)
    (s : ℝ) (x : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => fderiv ℝ (fun y => fderiv ℝ (u s) y (Pi.single i 1)) x (Pi.single j 1)

/-- The Lévy generator `Lu(s, x) := μᵀ∇u + ½Tr(σσᵀ∇²u)` (the continuous part;
the jump part is integrated into `comp_drift`'s integrand). -/
noncomputable def levyGenerator {n d : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ))
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ))
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, μ s x i * gradient u s x i)
  + (1 / 2) * (∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin d,
      σ s x i k * σ s x j k * hessian u s x i j)

/-- Drift-term integrand `(∂_t u + Lu)(s, x)`. -/
noncomputable def driftIntegrand {n d : ℕ}
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (s : ℝ) (x : Fin n → ℝ) : ℝ :=
  timeDeriv u s x + levyGenerator u coeffs.μ coeffs.σ s x

/-! ### The cited sub-primitive of the Itô–Lévy formula

The headline `itoLevyFormula` (Applebaum 4.4.7) is derived by algebra from
`itoLevyFormula_jumpResidual_canonical_axiom` (Applebaum 4.4.10 + 4.4.7
step II): for the canonical residual `R_canonical T ω :=
u(T, X_T) − u(0, X_0) − drift − diff_mart`, we have
`R_canonical = jump_mart + comp_drift` a.s. The universal-`R` form
`itoLevyFormula_jumpResidual_axiom` (any `R` satisfying the continuous-part
identity) is a derived theorem: any two such `R`s agree a.s.
-/

end Integrands

section Formula
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **CITED AXIOM (Tier 1 #16, narrower than the previous #16):
Canonical-residual jump decomposition (Applebaum 4.4.10 + 4.4.7 step II).**

This is the canonical (non-universal-`R`) form of the Lévy-Itô
combinatorial step: for the *specific* residual

  `R_canonical T ω := u(T, X_T) − u(0, X_0)`
                  `− ∫₀^T (∂_t u + 𝓛^c u)(s, X_s) ds`
                  `− (multidim-Brownian Itô integral of ∇uᵀσ along X at T)`,

we identify it as the sum of the *jump martingale* term and the
*compensator drift* term:

  `R_canonical T ω = jump_mart_T(ω) + comp_drift_T(ω)`  a.s.,

where
* `jump_mart_T(ω) = Compensated.stochasticIntegral N (u(·+γ) − u along X) T ω`,
* `comp_drift_T(ω) = ∫₀^T ∫_E [u(·+γ) − u − γᵀ∇u](s, X_s, e) ν(de) ds`.

**Narrowing compared to the previous Tier 1 #16 axiom**: the previous
form quantified over *any* `R` satisfying a continuous-part identity
`u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω`. That quantifier
is now eliminated: this axiom asserts the identity only for the
canonical `R` constructed by direct subtraction from the LHS. The
universal-`R` statement (the old `itoLevyFormula_jumpResidual_axiom`)
is recovered as a derived theorem below by per-ω substitution
(`R = R_canonical` a.s. when both satisfy the continuous-part
identity). The narrower axiom captures exactly the analytical content
(Applebaum 4.4.10 + 4.4.7 step II); the universal-`R` form adds only
algebraic glue.

The literature derivation is Applebaum 4.4.10 (the small/large jump
decomposition `∫₀^T ∫_E φ Ñ = ∫₀^T ∫_{|e|<ε} φ Ñ + ∑_{|γ|≥ε} φ`) plus
the `ε → 0` limit using the `L²`-isometry of the compensated-Poisson
integral (Applebaum 4.2.3 / Tier 1 #6 / Tier 1 #18
`itoIsometry_diff_compensated`).

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*,
2nd ed., Cambridge University Press, 2009, **Theorem 4.4.10** (small/
large jump decomposition); same source **Theorem 4.4.7** proof
**step (II)** for the `ε → 0` limit (page 240); Ikeda–Watanabe
**Section II.5**; Cont–Tankov **Proposition 8.18** + Chapter 8.

**Mathlib status (May 2026)**: No compensated-Poisson integral in
Mathlib (waits on PRM construction). The small/large decomposition
is itself a derived statement once the integral exists; the
`ε → 0` limit uses `itoIsometry_diff_compensated` (Tier 1 #18).

**Replacement plan**: derive as a theorem from
`itoIsometry_diff_compensated` (Tier 1 #18, in `Poisson/Compensated.lean`)
+ a Mathlib-level linearity result on the compensated-Poisson
L²-integral once that machinery becomes available. -/
axiom itoLevyFormula_jumpResidual_canonical_axiom
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (T : ℝ) (_hT : 0 < T)
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
            ∂volume ∂P < ⊤)
    (h_jumpInt_meas : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_progMeas : ∀ t : ℝ,
        @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
          (@Prod.instMeasurableSpace Ω (ℝ × E)
            ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
            inferInstance)
          (fun p : Ω × ℝ × E =>
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (_h_compDrift_int : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω)
        =
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω'))
            h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν

/-- **Universal-residual form of the jump decomposition.**

Given any residual `R` satisfying the continuous-part identity
`u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω` a.s., this theorem
identifies it as the sum of the *jump martingale* term and the
*compensator drift* term:

  `R T ω = jump_mart_T(ω) + comp_drift_T(ω)`  a.s.,

where
* `jump_mart_T(ω) = Compensated.stochasticIntegral N (u(·+γ) − u along X) T ω`,
* `comp_drift_T(ω) = ∫₀^T ∫_E [u(·+γ) − u − γᵀ∇u](s, X_s, e) ν(de) ds`.

Derived by per-`ω` algebra from the narrower axiom
`itoLevyFormula_jumpResidual_canonical_axiom` (the canonical-`R` form), which
carries the analytical content (Applebaum 4.4.10 + 4.4.7 step II); the
universal-`R` step is algebra (`R` and `R_canonical` differ by zero a.s. when
both satisfy the continuous-part identity).

**Proof outline**: apply the narrower axiom to get `R_canonical T ω =
jump_mart + comp_drift`. From `h_continuousPart`, get `R T ω =
u(T,X_T) − u(0,X_0) − drift − diff_mart = R_canonical T ω`. Combine
to conclude `R T ω = jump_mart + comp_drift`.

The hypothesis `h_continuousPart` makes the theorem apply only to
residuals arising from a continuous-part identity, ruling out the
trivial-witness pathology (any `R T ω` could otherwise be made to
satisfy the conclusion vacuously by absorbing the discrepancy).

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*,
2nd ed., Cambridge University Press, 2009, **Theorem 4.4.10** + **Theorem
4.4.7** step (II); Ikeda–Watanabe **Section II.5**; Cont–Tankov
**Proposition 8.18** + Chapter 8. -/
theorem itoLevyFormula_jumpResidual_axiom
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (T : ℝ) (hT : 0 < T)
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
            ∂volume ∂P < ⊤)
    (h_jumpInt_meas : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_progMeas : ∀ t : ℝ,
        @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
          (@Prod.instMeasurableSpace Ω (ℝ × E)
            ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
            inferInstance)
          (fun p : Ω × ℝ × E =>
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume < ⊤)
    -- Input: any residual `R` satisfying the continuous-part identity.
    -- The theorem then identifies `R T ω` with the two jump-side terms.
    (R : ℝ → Ω → ℝ)
    (h_continuousPart : ∀ᵐ ω ∂P,
        u T (X.X T ω) - u 0 (X.X 0 ω) =
          (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
              W (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω
          + R T ω) :
    ∀ᵐ ω ∂P,
      R T ω =
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω'))
            h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  -- Step 1: apply the narrower axiom to get the canonical-R identity.
  have h_canonical := itoLevyFormula_jumpResidual_canonical_axiom
    W N coeffs x₀ X u T hT
    h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq
    h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq h_compDrift_int
  -- Step 2: combine the two a.s. hypotheses; per-ω algebra collapses
  -- the two identities.
  filter_upwards [h_canonical, h_continuousPart] with ω h_canon_ω h_cp_ω
  -- h_canon_ω : (u(T,X_T) − u(0,X_0) − drift − diff_mart) = jump_mart + comp_drift
  -- h_cp_ω : u(T,X_T) − u(0,X_0) = drift + diff_mart + R T ω
  -- So R T ω = u(T,X_T) − u(0,X_0) − drift − diff_mart = jump_mart + comp_drift.
  linarith

/-- **Itô-Lévy formula for jump diffusions (Applebaum 2009 Thm 4.4.7).**

For `C^{1,2}` functions `u` and a jump diffusion `X = (μ, σ, γ)`-driven by
`(W, N)`, the chain-rule decomposition

  `u(T, X_T) − u(0, X_0)`
  `= ∫_0^T (∂_t u + 𝓛u)(s, X_{s-}) ds`     -- drift_term
  `+ ∫_0^T ∇u(s, X_{s-})ᵀ σ(s, X_{s-}) dW_s`  -- diff_mart
  `+ ∫_0^T ∫_E [u(s, X_{s-} + γ(s, X_{s-}, e)) − u(s, X_{s-})] Ñ(ds, de)`  -- jump_mart
  `+ ∫_0^T ∫_E [u(·+γ) − u − γᵀ ∇u](s, X_{s-}, e) ν(de) ds`  -- comp_drift

holds almost surely, where `𝓛u = μᵀ∇u + ½Tr(σσᵀ∇²u)` is the diffusion
generator.

**Reference**: Applebaum, D. *Lévy Processes and Stochastic Calculus*,
2nd ed., Cambridge University Press, 2009, Theorem 4.4.7. See also
Cont, R. & Tankov, P. *Financial Modelling with Jump Processes*,
Chapman & Hall/CRC, 2003, Proposition 8.18.

Derived by algebra from `itoLevyFormula_jumpResidual_canonical_axiom`
(cited axiom #16): the canonical residual
`u(T, X_T) − u(0, X_0) − drift − diff_mart` equals `jump_mart + comp_drift`
almost surely, and the four-term identity is that equation rearranged. -/
theorem itoLevyFormula
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (T : ℝ) (hT : 0 < T)
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
            ∂volume ∂P < ⊤)
    (h_jumpInt_meas : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_progMeas : ∀ t : ℝ,
        @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
          (@Prod.instMeasurableSpace Ω (ℝ × E)
            ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
            inferInstance)
          (fun p : Ω × ℝ × E =>
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      u T (X.X T ω) - u 0 (X.X 0 ω) =
        (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω'))
            h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  have h := itoLevyFormula_jumpResidual_canonical_axiom W N coeffs x₀ X u T hT
    h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq
    h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq h_compDrift_int
  filter_upwards [h] with ω hω
  linarith

end Formula

end LevyStochCalc.Ito.JumpFormula
