/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Picard

/-!
# Lifting the Picard step to a self-map on `SBoundedProcess P T`

The Picard map `picardStep` (defined in `Ito.Picard`) takes a candidate process
`X : ℝ → Ω → (Fin n → ℝ)` together with σ/γ-side measurability + L²
hypothesis bundles and produces a new candidate process. For the
Banach fixed-point argument we need this map to be a self-map on
`SBoundedProcess P T` — the literature's `S²([0, T]; ℝⁿ)` Banach space.

This file builds that lift in the form
`picardStepOnS2 : SBoundedProcess P T → SBoundedProcess P T`,
with the inevitable "missing-Mathlib-infrastructure" hypotheses
discharged at the call site as explicit arguments. The `2` in
`picardStepOnS2` stands for `S²` — the literature shorthand for the
Banach space of square-integrable càdlàg-adapted processes
(Karatzas-Shreve §3.2, Protter §V.3); the ASCII spelling is forced by
Lean's identifier rules (the superscript `²` is not a valid identifier
character).

## Why a `fromCandidate` constructor with bundled hypotheses

The three `SBoundedProcess` fields — `measurable_path`, `cadlag_paths`,
`sup_L2` — are *not* derivable from the current axiomatisation of
`MultidimBrownianMotion.stochasticIntegral` and
`Compensated.stochasticIntegral`:

* The Brownian unified-existence axiom
  (`itoIsometry_brownian_unified_existence`, Tier 1 #5) exposes
  martingale + quadratic variation + L²-isometry, but does **not**
  expose joint `(t, ω)`-measurability or càdlàg paths of the integral
  process.

* The Compensated unified-existence axiom
  (`itoIsometry_compensated_unified_existence`, Tier 1 #6) exposes
  martingale + quadVar + L²-isometry + càdlàg paths (conjunct 5),
  but does **not** expose joint `(ω, t)`-measurability either.

* The standard analytic route to deriving these — the
  Burkholder–Davis–Gundy inequality, which would convert the per-`T`
  L²-isometries into a single `S²` sup-norm bound — is **not yet** in
  Mathlib (as of May 2026; the only adjacent infrastructure is
  `MeasureTheory.Martingale` plus partial work in `Mathlib.Probability`
  on the Doob–Meyer decomposition).

Pursuing a sorry-free derivation of these three fields from the existing
unified-existence axioms would therefore either (a) need a new Tier 1
axiom upgrade adding the missing conjuncts, or (b) bring in BDG as a
separate axiom and assemble the three fields downstream. Neither change
is in scope for *this* file — the prompt-spec ALTERNATIVE
("build a SBoundedProcess.fromCandidate constructor with stronger
hypothesis bundles, and discharge them at the call site") is exactly
the right shape: it cleanly factors the missing analytic content into
*explicit caller-supplied hypotheses* without smuggling new axioms in.
The Banach contraction step (downstream in `PicardContraction.lean`)
then consumes these hypotheses unchanged.

## What this file delivers

* `SBoundedProcess.ofPicardStep` — the explicit constructor: given
  `(W, N, coeffs, x₀)` plus σ/γ measurability + L²-bound hypotheses
  along the supplied path map, **plus** the three explicit
  hypothesis bundles for the three `SBoundedProcess` fields of the
  output, returns the lifted `SBoundedProcess`.

* `picardStepOnS2` — the same map in `SBoundedProcess P T → SBoundedProcess P T`
  shape, with the same three output-field hypotheses bundled as
  parameters (one σ/γ bundle that *depends* on the input
  `SBoundedProcess`, plus the three output-field hypotheses). This is
  the SBoundedProcess-self-map shape that `picardFixedPoint` consumes.

* `picardStepOnS2_X` — the lifted map agrees with `picardStep`
  pointwise (`(t, ω)`-pointwise equality on the underlying path map).

The bundled output-field hypotheses are *substantive missing analytic
content* — they are the precise statements that BDG + the standard
Doob martingale-inequality + Bochner-Fubini chain would discharge in a
hypothetical extended axiomatisation. Discharging them in this file
without that chain would either require BDG-as-axiom or a sorry; the
present design defers the decision to the call site
(`PicardContraction.lean` Banach assembly), where the entire iteration
sees the same set of hypotheses and they can be discharged uniformly.

## Status

* Sorry-free, axiom-clean (only depends on the same Tier 1 axioms that
  `Picard.lean` and `PicardBanach.lean` already use).
* All output-field hypotheses are explicit parameters; no hidden BDG
  assumption.
* The file compiles cleanly under `lake build`; the `_audit.lean`
  axiom-set entries for the public symbols are added.

## References

* Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP
  2009, Theorem 6.2.9 (Picard iteration in `S²` for jump-diffusion SDEs).
* Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
  Springer 1991, §5.2 (Picard iteration for continuous SDEs).
* Protter, P. *Stochastic Integration and Differential Equations*,
  Springer 2005, §V.3 (BDG inequality and `S²` Banach structure).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Construct an `SBoundedProcess` from the Picard step output and
the three caller-supplied field hypotheses.**

This is the `fromCandidate`-style constructor described in the module
docstring: given the data + hypotheses that make `picardStep` well-typed
(σ-side measurability/progressive-measurability/L²-boundedness +
γ-side analogue), PLUS three explicit hypothesis bundles for the
output's joint measurability, càdlàg paths, and finite Bielecki-norm,
package the result into an `SBoundedProcess`.

The σ/γ hypothesis bundles are the same ones that `picardStep` takes;
they are reproduced here as named arguments so the constructor can be
invoked uniformly across Picard iterates (each iterate produces the
same shape of hypotheses for the next iterate, with σ/γ replaced by
σ/γ along the new candidate).

The three output-field hypotheses
(`h_out_meas`, `h_out_cadlag`, `h_out_sup_L2`) encode the
"missing-Mathlib-infrastructure" content that a BDG-based analytic
argument would otherwise discharge — see the module docstring. -/
noncomputable def SBoundedProcess.ofPicardStep
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    -- σ-side hypotheses for the Brownian integral
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses for the compensated-Poisson integral
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ)
    -- Three explicit output-field hypotheses (see module docstring).
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N coeffs X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N coeffs X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N coeffs X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N coeffs X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    SBoundedProcess (n := n) P T where
  X := fun t ω => picardStep (E := E) W N coeffs X x₀
    h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω
  measurable_path := h_out_meas
  cadlag_paths := h_out_cadlag
  sup_L2 := h_out_sup_L2

/-- **The Picard self-map on `SBoundedProcess`.**

Given:

* the Brownian motion `W`, the Poisson random measure `N`, the coefficient
  bundle `coeffs`, and the initial condition `x₀`,
* an `SBoundedProcess` candidate `X`,
* σ/γ-side measurability + L²-boundedness bundles for `coeffs` along
  `X.X` (these depend on `X` and must be supplied at call time — they
  are produced uniformly across all Picard iterates by combining the
  shared coeffs measurability with the SBoundedProcess's joint
  measurability via `sigma_along_X_measurable` and
  `gamma_along_X_measurable`),
* the **three output-field hypothesis bundles** for the lifted iterate.

…produces a new `SBoundedProcess` whose underlying path map is
exactly `picardStep` applied to `X.X`.

This is the `Φ : SBoundedProcess → SBoundedProcess` map that the Banach
fixed-point theorem consumes in
`picardFixedPoint_jumpDiffusion_exists_unique`. The contraction
estimate (proved in `PicardContraction.lean`) operates on the
underlying path map and lifts trivially through `picardStepOnS2`. -/
noncomputable def picardStepOnS2
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) (T : ℝ)
    (X : SBoundedProcess (n := n) P T)
    -- σ-side hypotheses along X.X
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X.X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X.X p.2 p.1) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- γ-side hypotheses along X.X
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Three output-field hypothesis bundles (see module docstring).
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N coeffs X.X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    SBoundedProcess (n := n) P T :=
  SBoundedProcess.ofPicardStep (E := E) W N coeffs X.X x₀
    h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq T
    h_out_meas h_out_cadlag h_out_sup_L2

/-- **The lifted Picard map agrees pointwise with `picardStep`.**

Pointwise extensionality lemma: the underlying path map of
`picardStepOnS2` is definitionally equal to `picardStep` applied to
the input `SBoundedProcess`'s path map. This is the load-bearing
"the lift is the right one" statement — the contraction estimate
proved in `PicardContraction.lean` operates on `picardStep` directly,
and this lemma converts those estimates into estimates on
`(picardStepOnS2).X`. -/
@[simp]
lemma picardStepOnS2_X
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) (T : ℝ)
    (X : SBoundedProcess (n := n) P T)
    (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X.X s ω) i j)))
    (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X.X p.2 p.1) i j))
    (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i))
    (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_out_meas : Measurable (Function.uncurry
      (fun t ω => picardStep (E := E) W N coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω)))
    (h_out_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto
        (fun s => picardStep (E := E) W N coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω)
        (nhdsWithin t (Set.Ioi t))
        (nhds (picardStep (E := E) W N coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
            Filter.Tendsto
              (fun s => picardStep (E := E) W N coeffs X.X x₀
                h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq s ω i)
              (nhdsWithin t (Set.Iio t)) (nhds L))
    (h_out_sup_L2 : bieleckiNorm (P := P) 0 T
      (fun t ω => picardStep (E := E) W N coeffs X.X x₀
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω) < ⊤) :
    (picardStepOnS2 (E := E) W N coeffs x₀ T X
        h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq
        h_out_meas h_out_cadlag h_out_sup_L2).X
      = fun t ω => picardStep (E := E) W N coeffs X.X x₀
          h_σ_meas h_σ_progMeas h_σ_sq h_γ_meas h_γ_progMeas h_γ_sq t ω := by
  rfl

end LevyStochCalc.Ito.Picard
