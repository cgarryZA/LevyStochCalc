/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Setting

/-!
# Picard iteration framework for jump-diffusion SDEs

Rule-1 START (2026-05-23): this file is the active construction of the
proof of `JumpDiffusion.exists_unique` (currently sorry'd in
`Ito/Setting.lean`). The literature proof (Applebaum 2009 Theorem 6.2.9
/ Ikeda-Watanabe Chapter IV) is Picard iteration in the Banach space
`S²([0,T]; ℝⁿ)` of càdlàg-adapted L²-sup-bounded processes, with the
contraction provided by a Bielecki-weighted norm `‖X‖_β := sup_{t ≤ T}
e^{-βt} √(E[‖X_t‖²])`.

## Structure of the proof

1. **`SBoundedProcess`** — the Banach space of jointly-measurable,
   adapted, càdlàg, L²-sup-bounded processes on `[0, T]` with values in
   `Fin n → ℝ`.

2. **`bieleckiNorm β X`** — the Bielecki-weighted L² norm
   `sup_{t ≤ T} e^{-βt} (E[‖X_t‖²])^{1/2}`. Equivalent to the standard
   `S²` norm for any fixed `β ≥ 0`, but the weighting absorbs the
   Grönwall constant in the contraction step.

3. **`picardStep`** — the actual Picard map
   `Φ X : t ↦ x₀ + ∫_0^t μ(s, X_s) ds + ∫_0^t σ(s, X_s) dW_s
        + ∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)`,
   defined using the multidim Brownian and compensated-Poisson integrals
   already exposed by `Brownian.MultidimIto` and `Poisson.Compensated`.

4. **`picardStep_contraction`** — for sufficiently large `β` (depending
   on the Lipschitz constant L of `(μ, σ, γ)`), the Picard map is a
   contraction w.r.t. `bieleckiNorm β`. This uses the L²-isometry of
   the Brownian Itô integral (Tier 1 #5) and the compensated-Poisson
   Itô isometry (Tier 1 #6), plus the Lipschitz hypothesis on the
   coefficients.

5. **`picardFixedPoint`** — applying Banach's fixed-point theorem
   (`ContractingWith.fixedPoint`) yields a unique fixed point of `Φ`
   in `SBoundedProcess`.

6. **`fixedPoint_is_solution`** — the fixed point of `Φ` satisfies the
   SDE integral equation and hence furnishes the strong solution.

7. **Uniqueness** — direct consequence of contraction (any two
   fixed points must coincide).

## Status

Active build. Each step below is currently `sorry` and gradually being
filled in. The framework definition (steps 1-3) is being built first.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The Bielecki-weighted L² norm of a process `X : ℝ → Ω → (Fin n → ℝ)`
on `[0, T]`:

  `‖X‖_β,T := sup_{t ∈ [0, T]} e^{-βt} · (E[‖X_t‖²])^{1/2}`.

For `β = 0` this is the standard `S²` norm; for `β > 0` it is
equivalent to `S²` but absorbs the Grönwall constant in the Picard
contraction estimate. -/
noncomputable def bieleckiNorm
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P]
    (β T : ℝ) (X : ℝ → Ω → (Fin n → ℝ)) : ℝ≥0∞ :=
  ⨆ t ∈ Set.Icc (0 : ℝ) T,
    ENNReal.ofReal (Real.exp (-β * t)) *
      (∫⁻ ω, (∑ i, (‖X t ω i‖₊ : ℝ≥0∞) ^ 2) ∂P) ^ (1/2 : ℝ)

/-- The space of L²-bounded jointly-measurable processes on `[0, T]`
with values in `Fin n → ℝ`. A subset of `ℝ → Ω → Fin n → ℝ` carrying:
* joint measurability,
* almost-sure càdlàg paths,
* finite Bielecki-norm for some (equivalently, every) `β ≥ 0`.

This is the literature's `S²([0, T]; ℝⁿ)` Banach space. -/
structure SBoundedProcess
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) where
  /-- The path map. -/
  X : ℝ → Ω → (Fin n → ℝ)
  /-- Joint measurability in `(t, ω)`. -/
  measurable_path : Measurable (Function.uncurry X)
  /-- Almost-sure càdlàg paths. -/
  cadlag_paths : ∀ᵐ ω ∂P, ∀ t : ℝ,
    Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- Finite Bielecki-norm at the standard weight `β = 0`. -/
  sup_L2 : bieleckiNorm (P := P) 0 T X < ⊤

/-- **The Picard map step.** Given a candidate process `X` and the
coefficients `(μ, σ, γ)`, the next iterate is

  `Φ X : t ↦ x_0 + ∫_0^t μ(s, X_s) ds + ∫_0^t σ(s, X_s) dW_s
      + ∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)`.

This is the actual Picard map — not a placeholder. The integrands
require joint measurability + adaptedness hypotheses on `X` together
with measurability of the coefficient functions; these are bundled as
explicit hypotheses to keep the map well-typed.

For now we provide ONLY the drift component `∫_0^t μ(s, X_s) ds`; the
Brownian and compensated-Poisson integral components require
additional measurability bundling that is built up in subsequent
lemmas. -/
noncomputable def picardStep_drift
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  x₀ + fun i => ∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component pointwise drift difference identity.** For any two
candidates `X, Y`, the difference of drift components is the Bochner
integral of the per-component drift-coefficient difference:

  `(drift X x₀ t ω - drift Y x₀ t ω) i
    = ∫ s in [0, t], (μ s (X s ω) i - μ s (Y s ω) i) ds`.

This is just the algebraic identity that `picardStep_drift` cancels the
common `x₀` and pulls the integral subtraction componentwise — no
analytic content yet, but a load-bearing intermediate. -/
lemma picardStep_drift_diff
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    -- Integrability of each side (needed for `integral_sub`):
    (h_X_int : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (X s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn (fun s => coeffs.μ s (Y s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    (picardStep_drift (E := E) coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i
      = ∫ s in Set.Icc (0 : ℝ) t,
          (coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i) := by
  unfold picardStep_drift
  -- LHS = ((x₀ + (fun i => ∫ ... μ(X) i)) - (x₀ + (fun i => ∫ ... μ(Y) i))) i
  --     = (∫ ... μ(X) i - ∫ ... μ(Y) i)  by add_sub_add_cancel
  --     = ∫ ... (μ(X) i - μ(Y) i)        by integral_sub
  simp only [Pi.add_apply, Pi.sub_apply, add_sub_add_left_eq_sub]
  exact (MeasureTheory.integral_sub h_X_int h_Y_int).symm

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Vector form of the drift difference identity.** Bundles the per-component
identity into a `funext` over `i : Fin n`.

  `drift X x₀ t ω - drift Y x₀ t ω
    = fun i => ∫ s in [0, t], (μ s (X s ω) i - μ s (Y s ω) i)`. -/
lemma picardStep_drift_diff_vec
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω)
    (h_X_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω
      = fun i => ∫ s in Set.Icc (0 : ℝ) t,
          (coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i) := by
  funext i
  exact picardStep_drift_diff coeffs X Y x₀ t ω i (h_X_int i) (h_Y_int i)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component pointwise L¹ Lipschitz bound on the drift step.**

For Lipschitz μ with rate `L_μ` componentwise, the i-th component of
the drift-step difference is bounded by the time-integral of the
componentwise difference:

  `|(drift X x₀ t ω - drift Y x₀ t ω) i|
    ≤ ∫ s in [0, t], |μ s (X s ω) i - μ s (Y s ω) i|`. -/
lemma picardStep_drift_diff_componentwise_norm_bound
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i|
      ≤ ∫ s in Set.Icc (0 : ℝ) t,
          |coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i| := by
  rw [picardStep_drift_diff coeffs X Y x₀ t ω i h_X_int h_Y_int]
  -- |∫ f| ≤ ∫ |f| via MeasureTheory.norm_integral_le_integral_norm specialized to ℝ.
  have h_sub_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i)
      (Set.Icc (0 : ℝ) t) MeasureTheory.volume := h_X_int.sub h_Y_int
  -- For ℝ-valued integrand, ‖x‖ = |x|, so norm_integral_le_integral_norm gives
  -- |∫ f| ≤ ∫ |f|. The lemma is stated for normed groups; |·| is the ℝ-norm.
  have h := MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))
    (f := fun s => coeffs.μ s (X s ω) i - coeffs.μ s (Y s ω) i)
  -- ‖·‖ on ℝ is |·|, so the goal matches after rewriting.
  simpa [Real.norm_eq_abs] using h

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component Lipschitz bound on the drift step.**

Using the per-component Lipschitz hypothesis on `μ`, the i-th component
of the drift difference is bounded by `L_μ * ∫_0^t ‖X_s - Y_s‖ ds`:

  `|(drift X x₀ t ω - drift Y x₀ t ω) i|
    ≤ L_μ · ∫ s in [0, t], ‖X s ω - Y s ω‖`.

This is the operator-level statement that feeds the Bielecki-norm
contraction. -/
lemma picardStep_drift_diff_lipschitz_componentwise
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    -- Per-component Lipschitz on μ: |μ s x₁ i - μ s x₂ i| ≤ L_μ · ‖x₁ - x₂‖.
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    -- And the integrand ‖X_s - Y_s‖ must itself be integrable for the RHS
    -- bound's `mul_integral` rewrite to be valid:
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i|
      ≤ L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ := by
  -- Chain the two preceding bounds:
  -- |·| ≤ ∫ |μ(X) i - μ(Y) i|        (norm_integral_le_integral_norm)
  --     ≤ ∫ L_μ * ‖X - Y‖             (Lipschitz, integral monotonicity)
  --     = L_μ * ∫ ‖X - Y‖             (constant pull-out)
  refine (picardStep_drift_diff_componentwise_norm_bound
    coeffs X Y x₀ t ω i h_X_int h_Y_int).trans ?_
  -- Now goal: ∫ |μ(X) i - μ(Y) i| ≤ L_μ * ∫ ‖X - Y‖.
  -- Use integral_mono_of_nonneg or set_integral_mono after rewriting RHS as integral.
  rw [show L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖
        = ∫ s in Set.Icc (0 : ℝ) t, L_μ * ‖X s ω - Y s ω‖ from
      (MeasureTheory.integral_const_mul L_μ _).symm]
  -- Integral monotonicity. Need: integrability of both integrands + pointwise ≤.
  refine MeasureTheory.setIntegral_mono_on ?_ ?_
    measurableSet_Icc (fun s _ => h_μ_lip s (X s ω) (Y s ω) i)
  · -- LHS integrable: |μ(X) i - μ(Y) i| ∈ L¹.
    exact (h_X_int.sub h_Y_int).abs
  · -- RHS integrable: L_μ * ‖X - Y‖ ∈ L¹.
    exact h_XY_diff_int.const_mul L_μ

end LevyStochCalc.Ito.Picard
