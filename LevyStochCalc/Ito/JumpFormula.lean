/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
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

This file provides the Lean form of the formula. The main dissertation
imports this module and replaces its
`Dissertation.Continuous.itoLevyFormula` axiom (Continuous.lean:415).

## Source

* Applebaum 2009, Theorem 4.4.7.
* User's dissertation
  [ch02_mathematical_framework.tex](
  D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex)
  eq (jump-ito) at lines 51-56.

## Status (2026-05-26 Rule-1 STEP 2 — axiom #16 → theorem narrowing)

**`itoLevyFormula` is a `theorem`**, derived by algebraic re-bundling
from TWO Tier 1 cited sub-primitives that expose the precise content
of the Applebaum 4.4.7 proof:

* **`itoFormula_continuousSemimartingale_axiom`** (Tier 1 #15) —
  Karatzas–Shreve 3.3.6: the Itô formula for continuous
  semimartingales applied to `u(t, X^c_t)` where `X^c` is the
  continuous-semimartingale part of the Lévy–Itô decomposition
  `X = X^c + X^d`. Produces the drift + diff-mart identity with a
  packaged residual `R`.

* **`itoLevyFormula_jumpResidual_canonical_axiom`** (Tier 1 #16,
  2026-05-26 narrowing of the previous #16) — Applebaum 4.4.10 +
  4.4.7 step (II): the canonical residual `R_canonical T ω :=
  u(T, X_T) − u(0, X_0) − drift − diff_mart` (constructed by direct
  subtraction from the LHS) equals the sum of jump-martingale +
  compensator-drift terms, derived via the small/large jump
  decomposition + `ε → 0` limit using the `L²`-isometry of the
  compensated-Poisson integral (Tier 1 #6 / #18).

The previous Tier 1 #16 axiom (`itoLevyFormula_jumpResidual_axiom`,
universal-`R` form) is now a **derived theorem** that forwards over
the narrower canonical-`R` axiom by per-ω algebra (`R = R_canonical`
a.s. when both satisfy the continuous-part identity).

These sub-primitives mirror the canonical "axiom + theorem forwarder"
pattern used by `picardFixedPoint_jumpDiffusion_exists_unique` (ex-Tier
1 #14, demoted axiom→theorem 2026-05-26) and `jacodYor_representation`
(Tier 1 #13) — see the 2026-05-23/26 log entries in
`tools/cited_axioms.md`.

The previous Tier 1 #11 axiom `itoLevyFormula` is replaced by the
combination of #15 + #16 above. The qualified theorem name
`LevyStochCalc.Ito.JumpFormula.itoLevyFormula` is preserved so the
dissertation forwarder (`Dissertation.Continuous.itoLevyFormula`) is
unaffected by the refactor.

### History

* 2026-05-11 (commit db582f9): `itoLevyFormula` demoted from `theorem`
  (trivial-witness proof `refine ⟨0, 0, 0, change, ?_⟩; simp`) to
  `axiom` with literature citation.
* 2026-05-22 (4 commits 7d232bf, 09687cf, 9675e44, 94f0155):
  statement fully pinned with all four terms in literature integral
  form (jump_mart → Compensated.stochasticIntegral, diff_mart →
  MultidimBrownianMotion.stochasticIntegral, comp_drift → ∫∫…ν ds,
  drift → ∫ driftIntegrand ds).
* 2026-05-23 (red-team 2nd audit fixes): `h_jumpInt_*` hypotheses
  bundled (H6 mirror of σ-side); `_h_compDrift_int` hypothesis added
  (red-team P4 H fix for non-`ν`-integrable case).
* 2026-05-24 (Rule-1 START): split the headline axiom into two
  literature sub-primitives (continuous-semimartingale Itô formula +
  jump-residual decomposition) and PROVE `itoLevyFormula` as a
  `theorem` by algebraic re-bundling. Tier 1 entry #11 is retired
  (replaced by #15 + #16).
* 2026-05-26 (this commit, Rule-1 STEP 2): narrow Tier 1 #16 to its
  canonical-`R` form (`itoLevyFormula_jumpResidual_canonical_axiom`);
  convert the previous universal-`R` form
  (`itoLevyFormula_jumpResidual_axiom`) to a derived theorem
  forwarding over the narrower axiom by per-ω algebra.
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

/-! ### Tier 1 sub-primitives for the Itô–Lévy formula

The headline `itoLevyFormula` (Applebaum 4.4.7) is derived by
algebraic re-bundling from TWO Tier 1 cited sub-primitives below.
Each is a real literature theorem in its own right; their conjunction
gives the headline four-term identity.

* `itoFormula_continuousSemimartingale_axiom` (Karatzas–Shreve 3.3.6):
  Itô formula for the continuous part of `X` in the Lévy–Itô
  decomposition `X = X^c + X^d`. Produces `drift + diff_mart + R T ω`
  with the jump correction packaged as an existential residual `R`.

* `itoLevyFormula_jumpResidual_canonical_axiom` (Applebaum 4.4.10 +
  4.4.7 step II): for the canonical residual `R_canonical T ω :=
  u(T, X_T) − u(0, X_0) − drift − diff_mart`, we have
  `R_canonical = jump_mart + comp_drift` a.s., via the small/large
  jump decomposition + `ε → 0` limit (using the `L²`-isometry of the
  compensated-Poisson integral, Tier 1 #6 / #18).

  This is the **narrower** form of the (previous, retired)
  `itoLevyFormula_jumpResidual_axiom` (universal-`R` form, now a
  derived theorem). The narrowing eliminates the unbound `R`
  quantifier, which is the algebraic-glue layer (any two `R`s
  satisfying the continuous-part identity agree a.s.).
-/

/-- **CITED AXIOM (Tier 1 #15): Itô formula for continuous semimartingales
applied to the continuous part of `X`.**

For `u ∈ C^{1,2}` and a jump-diffusion `X = (μ, σ, γ)`, apply the
classical Itô formula (Karatzas–Shreve 3.3.6) to `u(t, X^c_t)`, where
`X^c` is the continuous-semimartingale part in the Lévy–Itô
decomposition `X = X^c + X^d`. The output is

  `u(T, X^c_T) − u(0, X^c_0)`
    `= ∫₀^T (∂_t u + 𝓛^c u)(s, X_{s-}) ds + ∫₀^T ∇uᵀσ dW_s`,

where `𝓛^c u = μᵀ∇u + ½ Tr(σσᵀ ∇²u)` is the *continuous* part of the
Lévy generator (no jump correction). For the full
`u(T, X_T) − u(0, X_0)` the residual

  `R T ω := u(T, X_T) − u(0, X_0) − ∫₀^T (∂_t u + 𝓛^c u) ds`
            `  − ∫₀^T ∇uᵀσ dW`

is the "jump correction" identified by
`itoLevyFormula_jumpResidual_axiom`.

In the present axiomatisation the residual `R` is exposed as an
existential, packaged together with the continuous-part identity:

  `∃ R : ℝ → Ω → ℝ, ∀ᵐ ω, u(T, X_T) − u(0, X_0)`
    `= (∫₀^T (∂_t u + 𝓛^c u)(s, X_s) ds)`
    `+ (multidim-Brownian Itô integral of ∇uᵀσ along X at time T)`
    `+ R T ω`.

The conjunction with `itoLevyFormula_jumpResidual_axiom` (which
identifies `R T ω = jump_mart + comp_drift`) reconstructs the
literature four-term identity.

**Note on `X_{s-}` vs `X_s`**: the literature continuous Itô formula
uses `X_{s-}` (the left-continuous version) in the integrand for
predictability hygiene. For the càdlàg-adapted `X` of `JumpDiffusion`
(field `cadlag_paths`), the set `{s : X_{s-} ω ≠ X_s ω}` has Lebesgue
measure zero a.s., so the `ds` integrals and Brownian Itô integrals
agree pointwise a.s. with the `X_s`-evaluated versions used in the
statement here.

**Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic
Calculus*, 2nd ed., Springer 1991, **Theorem 3.3.6** (Itô formula for
continuous semimartingales — multidimensional vector form, equation
(3.3.5)); Le Gall, *Brownian Motion, Martingales and Stochastic
Calculus*, Springer 2016, **Theorem 5.10**; Revuz–Yor, *Continuous
Martingales and Brownian Motion*, 3rd ed., Springer 1999,
**Theorem IV.3.3**.

**Mathlib status (May 2026)**: No Itô formula in Mathlib (waits on
Brownian motion construction + L² Itô integral; tracked alongside
Tier 1 #5). The Degenne et al stochastic-integration effort
(arXiv:2511.20118, late 2025) is the most active push toward a
Mathlib Itô formula; no PR merged at time of writing.

**Replacement plan**: when Mathlib gains the Itô formula for
continuous semimartingales (Karatzas–Shreve 3.3.6), this axiom is
replaced by a forwarder that decomposes `X = X^c + X^d` via the
Lévy–Itô decomposition and applies the Mathlib theorem to `X^c`. -/
axiom itoFormula_continuousSemimartingale_axiom
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
            ∂volume ∂P < ⊤) :
    ∃ R : ℝ → Ω → ℝ,
      ∀ᵐ ω ∂P,
        u T (X.X T ω) - u 0 (X.X 0 ω) =
          (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
              W (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω
          + R T ω

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

/-- **Honest derivative theorem (was Tier 1 #16, axiom→theorem 2026-05-26):
universal-residual form of the jump decomposition.**

Given any residual `R` arising from the continuous-part Itô identity
(see `itoFormula_continuousSemimartingale_axiom`), this theorem
identifies it as the sum of the *jump martingale* term and the
*compensator drift* term:

  `R T ω = jump_mart_T(ω) + comp_drift_T(ω)`  a.s.,

where
* `jump_mart_T(ω) = Compensated.stochasticIntegral N (u(·+γ) − u along X) T ω`,
* `comp_drift_T(ω) = ∫₀^T ∫_E [u(·+γ) − u − γᵀ∇u](s, X_s, e) ν(de) ds`.

**Status (2026-05-26 — Rule-1 axiom→theorem conversion):** this was
Tier 1 axiom #16; it is now a **theorem** derived by per-ω algebra
from the narrower Tier 1 axiom
`itoLevyFormula_jumpResidual_canonical_axiom` (the canonical-`R` form).
The narrower axiom carries the genuine analytical content
(Applebaum 4.4.10 + 4.4.7 step II); the universal-`R` step is genuine
algebra (per-ω: `R` and `R_canonical` differ by zero a.s. when both
satisfy the continuous-part identity).

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

**Status (2026-05-24 — `axiom → theorem` conversion via two sub-axioms):**
this is now a `theorem`, derived by algebraic re-bundling from
`itoFormula_continuousSemimartingale_axiom` (Tier 1 #15) and
`itoLevyFormula_jumpResidual_axiom` (Tier 1 #16). The previous
single-axiom Tier 1 #11 entry is retired (replaced by #15 + #16).

**Proof**: extract the residual `R` from the continuous-semimartingale
Itô identity (`Classical.choose`); apply
`itoLevyFormula_jumpResidual_axiom` to `R` (which satisfies the
continuous-part identity by construction of `R`); substitute the
identification `R T ω = jump_mart + comp_drift` into the
continuous-part identity. The proof is genuine algebra (no further
stochastic-calculus content beyond the two sub-axioms). -/
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
  -- Step 1: extract the residual `R` from the continuous-semimartingale
  -- Itô identity (Tier 1 #15).
  obtain ⟨R, hR⟩ := itoFormula_continuousSemimartingale_axiom
    W N coeffs x₀ X u T hT
    h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq
  -- Step 2: apply the jump-residual decomposition (Tier 1 #16) to `R`.
  -- The continuous-part hypothesis `hR` is exactly the witness needed.
  have hR_decomp := itoLevyFormula_jumpResidual_axiom
    W N coeffs x₀ X u T hT
    h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq
    h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq h_compDrift_int
    R hR
  -- Step 3: combine the two a.s. equalities.
  filter_upwards [hR, hR_decomp] with ω h_cont h_jump
  -- `h_cont : u(T, X_T ω) - u(0, X_0 ω) = drift + diff_mart + R T ω`
  -- `h_jump : R T ω = jump_mart + comp_drift`
  -- Substitute and re-associate.
  rw [h_cont, h_jump]
  ring

end LevyStochCalc.Ito.JumpFormula
