/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Setting
import Mathlib.Algebra.Order.Chebyshev

/-!
# Picard iteration operator for jump-diffusion SDEs

This file sets up the Picard iteration scheme used to construct strong
solutions of the jump-diffusion SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t⁻}, e) Ñ(dt, de)`,

following Applebaum (2009, Thm 6.2.9) / Ikeda–Watanabe (Ch. IV): Picard
iteration in the space `S²([0,T]; ℝⁿ)` of L²-sup-bounded adapted processes,
with the contraction provided by a Bielecki-weighted norm
`‖X‖_β := sup_{t ≤ T} e^{-βt} √(𝔼‖X_t‖²)`.

## Contents

* `SBoundedProcess`, `bieleckiNorm` — the space of processes and its
  Bielecki-weighted L² norm.
* `picardStep` — the Picard map `Φ`, built from the multidim Brownian and
  compensated-Poisson Itô integrals, with measurability and the
  drift/diffusion/jump a-priori L² estimates of a single step.
* `picardStep_diffusion_diff_lipschitz_sq_componentwise`,
  `picardStep_jump_diff_lipschitz_sq_componentwise` — the per-component
  Lipschitz estimates of the diffusion and jump terms.
* `SBoundedProcess.ofPicardStep`, `picardStepOnS2` — the self-map property
  of `Φ` on the process space.
* `picardStep_bielecki_contraction`, `picardStep_bielecki_contraction_tight`
  — `Φ` is a Bielecki-norm contraction once `β` is large relative to the
  Lipschitz constant of `(μ, σ, γ)`.

The complete-metric-space structure on the process space lives in
`PicardSpace.lean`; the Banach fixed-point conclusion in
`PicardFixedPoint.lean`.
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

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **L² Cauchy-Schwarz on `[0, t]`.** For non-negative `L²` function `f`,

  `(∫ s in [0, t], f s)² ≤ t · ∫ s in [0, t], (f s)²`.

Derivation: view `f` and the constant `1` as elements of
`L²(volume.restrict [0,t])`. The `L²` inner product is `⟨f, 1⟩ = ∫ f`,
the `L²`-norms are `‖f‖_2 = √(∫ f²)` and `‖1‖_2 = √t`, and Cauchy-
Schwarz gives `(∫ f)² ≤ (∫ f²) · t`. -/
lemma integral_sq_le_mul_integral_sq_on_Icc
    (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hf_nn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), 0 ≤ f s)
    (hf_L2 : MeasureTheory.MemLp f 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    (∫ s in Set.Icc (0 : ℝ) t, f s) ^ 2
      ≤ t * ∫ s in Set.Icc (0 : ℝ) t, (f s) ^ 2 := by
  set μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)
  -- Constant function 1 ∈ L²(μ) since μ is finite.
  have h_one_L2 : MeasureTheory.MemLp (1 : ℝ → ℝ) 2 μ := MeasureTheory.memLp_const 1
  have h_one_nn : (0 : ℝ → ℝ) ≤ᵐ[μ] 1 :=
    Filter.Eventually.of_forall (fun _ => zero_le_one)
  have h2c : Real.HolderConjugate 2 2 := ⟨by norm_num, by norm_num, by norm_num⟩
  -- Convert MemLp 2 to MemLp (ENNReal.ofReal 2) for Hölder API.
  have hf_L2' : MeasureTheory.MemLp f (ENNReal.ofReal 2) μ := by
    rwa [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num]
  have h_one_L2' : MeasureTheory.MemLp (1 : ℝ → ℝ) (ENNReal.ofReal 2) μ := by
    rwa [show ENNReal.ofReal 2 = (2 : ℝ≥0∞) by norm_num]
  -- Hölder: ∫ f · 1 ≤ (∫ f²)^(1/2) · (∫ 1²)^(1/2).
  have h_holder := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := μ) (p := 2) (q := 2) h2c hf_nn h_one_nn hf_L2' h_one_L2'
  -- LHS simplification: ∫ f · 1 = ∫ f.
  have h_lhs_eq : ∫ a, f a * (1 : ℝ → ℝ) a ∂μ = ∫ a, f a ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change f a * (1 : ℝ → ℝ) a = f a
    rw [Pi.one_apply, mul_one]
  -- ∫ 1² = ∫ 1 = t.
  have h_one_sq_eq_one :
      ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ = ∫ _a : ℝ, (1 : ℝ) ∂μ := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    change ((1 : ℝ → ℝ) a) ^ 2 = (1 : ℝ)
    rw [Pi.one_apply, one_pow]
  have h_one_int : ∫ _a : ℝ, (1 : ℝ) ∂μ = t := by
    rw [MeasureTheory.integral_const]
    change (μ Set.univ).toReal • (1 : ℝ) = t
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal ht, smul_eq_mul, mul_one]
  have h_int_one_sq_eq_t : ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ = t :=
    h_one_sq_eq_one.trans h_one_int
  rw [h_lhs_eq] at h_holder
  -- h_holder : ∫ f ≤ (∫ f²)^(1/2) · (∫ 1²)^(1/2).
  -- The `1 a ^ 2` in h_holder doesn't syntactically match my h_int_one_sq_eq_t LHS
  -- (Lean's elaboration of Pi.one_apply differs). Use calc directly with both.
  -- h_holder uses `^ (2 : ℝ)` (real exponent from HolderConjugate). Convert.
  have h_rpow_two_eq_sq : ∀ x : ℝ, x ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
  have h_f_sq_conv : ∫ a, f a ^ (2 : ℝ) ∂μ = ∫ a, (f a) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a =>
      h_rpow_two_eq_sq (f a))
  have h_one_sq_conv : ∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ =
      ∫ a, ((1 : ℝ → ℝ) a) ^ 2 ∂μ :=
    MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun a =>
      h_rpow_two_eq_sq _)
  have h_holder' : (∫ a, f a ∂μ) ≤
      (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
    have h_step1 : (∫ a, f a ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) =
        (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) := by rw [h_f_sq_conv]
    have h_step2 : (∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) =
        t ^ ((1 : ℝ) / 2) := by
      rw [h_one_sq_conv, h_int_one_sq_eq_t]
    calc (∫ a, f a ∂μ)
        ≤ (∫ a, f a ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) *
            (∫ a, ((1 : ℝ → ℝ) a) ^ (2 : ℝ) ∂μ) ^ ((1 : ℝ) / 2) := h_holder
      _ = (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) := by
            rw [h_step1, h_step2]
  clear h_holder
  have h_LHS_nn : 0 ≤ ∫ a, f a ∂μ := MeasureTheory.integral_nonneg_of_ae hf_nn
  have h_sq_int_nn : 0 ≤ ∫ a, (f a) ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg_of_ae <| by
      filter_upwards [hf_nn] with s _ using sq_nonneg _
  have h_squared := mul_self_le_mul_self h_LHS_nn h_holder'
  have h_rpow_half_sq : ∀ a : ℝ, 0 ≤ a → a ^ ((1 : ℝ) / 2) * a ^ ((1 : ℝ) / 2) = a := by
    intro a ha
    rw [← Real.rpow_add_of_nonneg ha
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    norm_num
  calc (∫ a, f a ∂μ) ^ 2
      = (∫ a, f a ∂μ) * (∫ a, f a ∂μ) := by ring
    _ ≤ ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) *
        ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) := h_squared
    _ = ((∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2) * (∫ a, (f a) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) *
        (t ^ ((1 : ℝ) / 2) * t ^ ((1 : ℝ) / 2)) := by ring
    _ = (∫ a, (f a) ^ 2 ∂μ) * t := by
        rw [h_rpow_half_sq _ h_sq_int_nn, h_rpow_half_sq _ ht]
    _ = t * ∫ a, (f a) ^ 2 ∂μ := by ring

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Per-component L² Lipschitz bound on the drift step.**

Combining the L¹ Lipschitz bound `|drift X i - drift Y i| ≤
L_μ · ∫_0^t ‖X-Y‖` with the L² Cauchy-Schwarz `(∫ g)² ≤ t · ∫ g²`
applied to `g = ‖X - Y‖`:

  `|drift X i - drift Y i|² ≤ L_μ² · t · ∫_0^t ‖X_s - Y_s‖² ds`.

This is the per-(t, ω) bound. Taking `E[·]` over ω gives the L²-norm
Lipschitz bound, which is the ingredient for the Bielecki β-norm
contraction. -/
lemma picardStep_drift_diff_lipschitz_sq_componentwise
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω) (i : Fin n)
    (h_X_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_sq_L2 : MeasureTheory.MemLp
      (fun s => ‖X s ω - Y s ω‖) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by
  -- Step 1: L¹ Lipschitz bound (proven).
  have h_L1 := picardStep_drift_diff_lipschitz_componentwise
    coeffs hL_μ_nn h_μ_lip X Y x₀ t ω i h_X_int h_Y_int h_XY_diff_int
  -- The L¹ bound's |·| is the abs of the i-th component diff.
  -- Square both sides (LHS² = (|·|)² = (·)², RHS² = L² · (∫‖X-Y‖)²).
  have h_abs_sq : ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      = |(picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i| ^ 2 := by
    rw [sq_abs]
  rw [h_abs_sq]
  -- |·|² ≤ (L_μ · ∫‖X-Y‖)² by squaring h_L1 (both sides nonneg).
  have h_abs_nn : 0 ≤ |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i| := abs_nonneg _
  have h_int_nn : 0 ≤ ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ :=
    MeasureTheory.integral_nonneg_of_ae
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
  have h_RHS_nn : 0 ≤ L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ :=
    mul_nonneg hL_μ_nn h_int_nn
  have h_sq_bound := mul_self_le_mul_self h_abs_nn h_L1
  -- h_sq_bound: |·| * |·| ≤ (L_μ · ∫‖X-Y‖) * (L_μ · ∫‖X-Y‖)
  -- Convert ·*· to ·^2 on both sides:
  have h_LHS_sq_eq : |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i| *
      |(picardStep_drift coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i|
      = |(picardStep_drift coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i| ^ 2 := by ring
  have h_RHS_sq_eq : (L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) *
      (L_μ * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖)
      = L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2 := by ring
  rw [h_LHS_sq_eq, h_RHS_sq_eq] at h_sq_bound
  -- Apply Cauchy-Schwarz: (∫ ‖X-Y‖)² ≤ t · ∫ ‖X-Y‖².
  have h_CS := integral_sq_le_mul_integral_sq_on_Icc
    (fun s => ‖X s ω - Y s ω‖) t ht
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    h_XY_diff_sq_L2
  -- Chain: |·|² ≤ L_μ² · (∫‖X-Y‖)² ≤ L_μ² · t · ∫‖X-Y‖².
  have h_L_sq_nn : 0 ≤ L_μ ^ 2 := sq_nonneg _
  have h_CS_mul : L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2
      ≤ L_μ ^ 2 * (t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :=
    mul_le_mul_of_nonneg_left h_CS h_L_sq_nn
  calc |(picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i| ^ 2
      ≤ L_μ ^ 2 * (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖) ^ 2 := h_sq_bound
    _ ≤ L_μ ^ 2 * (t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := h_CS_mul
    _ = L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by ring

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Vector-norm L² Lipschitz bound on the drift step.**

Sum the per-component L² bound over `i : Fin n`:

  `∑ i, ((drift X - drift Y) i)² ≤ n · L_μ² · t · ∫_0^t ‖X-Y‖²`.

This is the squared-Euclidean-norm bound on the drift difference; the
factor `n` comes from summing the per-component bound. Together with
the `E[·]` step (next lemma) this gives the Bielecki-norm Lipschitz
constant for the drift step. -/
lemma picardStep_drift_diff_sum_sq_bound
    {n d : ℕ}
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (hL_μ_nn : 0 ≤ L_μ)
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (ω : Ω)
    (h_X_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_Y_int : ∀ i : Fin n, MeasureTheory.IntegrableOn
      (fun s => coeffs.μ s (Y s ω) i) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_int : MeasureTheory.IntegrableOn
      (fun s => ‖X s ω - Y s ω‖) (Set.Icc (0 : ℝ) t) MeasureTheory.volume)
    (h_XY_diff_sq_L2 : MeasureTheory.MemLp
      (fun s => ‖X s ω - Y s ω‖) 2
      (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t))) :
    (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ (n : ℝ) * L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by
  -- Per-component bound, summed over Fin n.
  have h_each : ∀ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
      ≤ L_μ ^ 2 * t * ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := fun i =>
    picardStep_drift_diff_lipschitz_sq_componentwise
      coeffs hL_μ_nn h_μ_lip X Y x₀ t ht ω i
      (h_X_int i) (h_Y_int i) h_XY_diff_int h_XY_diff_sq_L2
  -- Sum the bounds. Sum of n copies of B = n · B.
  calc (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
        - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ ∑ _i : Fin n, L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 :=
        Finset.sum_le_sum (fun i _ => h_each i)
    _ = (n : ℝ) * (L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
    _ = (n : ℝ) * L_μ ^ 2 * t *
          ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2 := by ring

omit [MeasurableSpace E] in
/-- **Drift step L² Lipschitz: integrated form (lintegral over ω).**

Take the lintegral of the sum-of-squares pointwise bound from
`picardStep_drift_diff_sum_sq_bound`. Using monotonicity of `∫⁻`
(the lemma `MeasureTheory.lintegral_mono_ae` applied to the pointwise
bound that holds for a.e. ω), we get:

  `∫⁻ ω, (∑ i, ((drift X - drift Y) i)²)
    ≤ n · L_μ² · t · ∫⁻ ω, ∫ s in [0, t], ‖X-Y‖² ds`.

The conversion from the real-valued pointwise bound to the ℝ≥0∞-valued
lintegral form uses `ENNReal.ofReal_le_ofReal` and the nonnegativity
of all the integrands.

This is the operator-level (probability-measure-integrated) bound that
sits one step away from the Bielecki β-norm contraction. -/
lemma picardStep_drift_diff_lintegral_sq_bound
    {n d : ℕ} (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    (_h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L_μ * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (t : ℝ) (ht : 0 ≤ t)
    -- Almost-everywhere integrability hypotheses (the pointwise bound only
    -- holds for ω with all integrands well-defined):
    (h_bound_ae : ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L_μ ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- Nonnegativity of the per-ω inner integral (for ENNReal conversion):
    (h_inner_nn : ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal
          (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  -- Monotonicity of lintegral applied to the a.e. bound.
  have h_pointwise_ennreal : ∀ᵐ ω ∂P,
      ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_drift (E := E) coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
      ≤ ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) := by
    filter_upwards [h_bound_ae, h_inner_nn] with ω h_bd h_inner_nn
    rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (n : ℝ) * L_μ ^ 2 * t)]
    exact ENNReal.ofReal_le_ofReal h_bd
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
          ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_mono_ae h_pointwise_ennreal
    _ = ENNReal.ofReal ((n : ℝ) * L_μ ^ 2 * t) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki calculus identity.** For `β > 0` and `t ≥ 0`,

  `∫_0^t e^{2βs} ds = (e^{2βt} - 1) / (2β)`.

This is the standard calculus identity that, combined with the
`e^{-2βt}` weight, gives the `1/(2β)` factor in the Bielecki β-norm
contraction estimate. The derivation: antiderivative of `e^{2βs}` is
`e^{2βs}/(2β)`, evaluated between 0 and t. -/
lemma integral_exp_two_beta_Icc
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t) :
    ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s)
      = (Real.exp (2 * β * t) - 1) / (2 * β) := by
  -- Standard integration via FTC: antiderivative of e^{2βs} is e^{2βs}/(2β).
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by positivity
  have h_two_beta_ne : (2 * β) ≠ 0 := h_two_beta_pos.ne'
  -- Reduce Icc to Ioc (Lebesgue-null endpoint), then Ioc to interval integral.
  rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [show ∫ s in Set.Ioc (0 : ℝ) t, Real.exp (2 * β * s)
        = ∫ s in (0 : ℝ)..t, Real.exp (2 * β * s) from
    (intervalIntegral.integral_of_le ht).symm]
  -- FTC: ∫_0^t f'(s) ds = f(t) - f(0) where f(s) = e^{2βs}/(2β), f'(s) = e^{2βs}.
  have h_FTC : ∫ s in (0 : ℝ)..t, Real.exp (2 * β * s)
      = Real.exp (2 * β * t) / (2 * β) - Real.exp (2 * β * 0) / (2 * β) := by
    have h_deriv : ∀ s ∈ Set.uIcc (0 : ℝ) t,
        HasDerivAt (fun u : ℝ => Real.exp (2 * β * u) / (2 * β))
          (Real.exp (2 * β * s)) s := by
      intro s _
      have h₁ : HasDerivAt (fun u : ℝ => 2 * β * u) (2 * β) s := by
        have := (hasDerivAt_id s).const_mul (2 * β)
        simpa using this
      have h₂ : HasDerivAt (fun u : ℝ => Real.exp (2 * β * u))
          (Real.exp (2 * β * s) * (2 * β)) s := h₁.exp
      have h₃ : HasDerivAt (fun u : ℝ => Real.exp (2 * β * u) / (2 * β))
          (Real.exp (2 * β * s) * (2 * β) / (2 * β)) s := h₂.div_const (2 * β)
      have h_simp : Real.exp (2 * β * s) * (2 * β) / (2 * β) = Real.exp (2 * β * s) := by
        field_simp
      rw [← h_simp]
      exact h₃
    -- Integrability of the integrand on [0, t].
    have h_int_cont : Continuous (fun s : ℝ => Real.exp (2 * β * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have h_int : IntervalIntegrable (fun s : ℝ => Real.exp (2 * β * s))
        MeasureTheory.volume 0 t := h_int_cont.intervalIntegrable 0 t
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv h_int
  rw [h_FTC]
  -- Simplify Real.exp (2 * β * 0) = 1.
  have h_zero : Real.exp (2 * β * 0) = 1 := by rw [mul_zero, Real.exp_zero]
  rw [h_zero]
  field_simp

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki weight bound.** For `β > 0` and `t ≥ 0`,

  `e^{-2βt} · (e^{2βt} - 1) / (2β) = (1 - e^{-2βt}) / (2β) ≤ 1 / (2β)`.

This is the key bound that makes the Bielecki β-norm a contraction:
the weighted integral `∫_0^t e^{-2βt+2βs} ds` is uniformly bounded
above by `1/(2β)` regardless of `t`. -/
lemma bielecki_weight_bound
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (_ht : 0 ≤ t) :
    Real.exp (-(2 * β * t)) * ((Real.exp (2 * β * t) - 1) / (2 * β))
      ≤ 1 / (2 * β) := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by positivity
  have h_two_beta_ne : (2 * β) ≠ 0 := h_two_beta_pos.ne'
  -- Step 1: expand e^{-2βt} · (e^{2βt} - 1) = 1 - e^{-2βt}.
  have h_exp_mul_neg : Real.exp (-(2 * β * t)) * Real.exp (2 * β * t) = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h_step1 : Real.exp (-(2 * β * t)) * ((Real.exp (2 * β * t) - 1) / (2 * β))
      = (1 - Real.exp (-(2 * β * t))) / (2 * β) := by
    rw [mul_div_assoc', mul_sub, h_exp_mul_neg, mul_one]
  rw [h_step1]
  -- Step 2: (1 - e^{-2βt}) ≤ 1 since e^{-2βt} ≥ 0.
  have h_exp_neg_nn : 0 ≤ Real.exp (-(2 * β * t)) := Real.exp_nonneg _
  have h_num_bound : 1 - Real.exp (-(2 * β * t)) ≤ 1 := by linarith
  -- Divide both sides by 2β > 0.
  exact div_le_div_of_nonneg_right h_num_bound h_two_beta_pos.le |>.trans_eq rfl

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki integration interchange.** For `β > 0`, `t ≥ 0`, and a
non-negative `L¹` function `g : ℝ → ℝ`,

  `e^{-2βt} · ∫_0^t e^{2βs} · g(s) ds ≤ (⨆_{s ≤ t} g(s)) · (1/(2β))`,

assuming `g` is bounded by a constant `M`. The bound `M · 1/(2β)`
follows from `∫_0^t e^{2βs} M ds = M · (e^{2βt}-1)/(2β)` times the
weight `e^{-2βt}`.

This is the key "sup pull-out + Bielecki contraction" lemma used in the
Picard argument. -/
lemma bielecki_weighted_integral_bound
    {β : ℝ} (hβ : 0 < β) {t : ℝ} (ht : 0 ≤ t)
    {M : ℝ} (hM_nn : 0 ≤ M)
    (g : ℝ → ℝ)
    (_hg_nn : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), 0 ≤ g s)
    (hg_bound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)), g s ≤ M)
    (hg_int : MeasureTheory.IntegrableOn
      (fun s => Real.exp (2 * β * s) * g s) (Set.Icc (0 : ℝ) t) MeasureTheory.volume) :
    Real.exp (-(2 * β * t)) *
        ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * g s
      ≤ M * (1 / (2 * β)) := by
  -- Bound the integrand: e^{2βs} · g(s) ≤ e^{2βs} · M.
  have h_exp_nn : ∀ s : ℝ, 0 ≤ Real.exp (2 * β * s) := fun s => Real.exp_nonneg _
  have h_pt_bound : ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) t)),
      Real.exp (2 * β * s) * g s ≤ Real.exp (2 * β * s) * M := by
    filter_upwards [hg_bound] with s h_bd
    exact mul_le_mul_of_nonneg_left h_bd (h_exp_nn s)
  -- Integrate the bound.
  have h_int_bound : ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * g s
      ≤ ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * M := by
    refine MeasureTheory.integral_mono_ae hg_int ?_ h_pt_bound
    -- Integrability of e^{2βs} · M on [0, t].
    have h_exp_cont : Continuous (fun s : ℝ => Real.exp (2 * β * s)) :=
      Real.continuous_exp.comp (continuous_const.mul continuous_id)
    have h_exp_int : MeasureTheory.IntegrableOn
        (fun s : ℝ => Real.exp (2 * β * s)) (Set.Icc (0 : ℝ) t) MeasureTheory.volume :=
      h_exp_cont.integrableOn_Icc
    exact h_exp_int.mul_const M
  -- Compute ∫_0^t e^{2βs} · M ds = M · (e^{2βt} - 1)/(2β).
  have h_const_int : ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * M
      = M * ((Real.exp (2 * β * t) - 1) / (2 * β)) := by
    rw [show (fun s => Real.exp (2 * β * s) * M) = (fun s => M * Real.exp (2 * β * s)) from
      funext fun s => by ring]
    rw [MeasureTheory.integral_const_mul, integral_exp_two_beta_Icc hβ ht]
  -- Multiply by e^{-2βt} on both sides (both nonneg).
  have h_exp_neg_nn : 0 ≤ Real.exp (-(2 * β * t)) := Real.exp_nonneg _
  have h_mul_LHS_RHS : Real.exp (-(2 * β * t)) *
        ∫ s in Set.Icc (0 : ℝ) t, Real.exp (2 * β * s) * g s
      ≤ Real.exp (-(2 * β * t)) * (M * ((Real.exp (2 * β * t) - 1) / (2 * β))) := by
    refine mul_le_mul_of_nonneg_left ?_ h_exp_neg_nn
    rw [h_const_int] at h_int_bound
    exact h_int_bound
  refine h_mul_LHS_RHS.trans ?_
  -- e^{-2βt} · (M · (e^{2βt}-1)/(2β)) = M · (e^{-2βt} · (e^{2βt}-1)/(2β))
  --                                 ≤ M · 1/(2β)   by bielecki_weight_bound.
  rw [show Real.exp (-(2 * β * t)) * (M * ((Real.exp (2 * β * t) - 1) / (2 * β)))
      = M * (Real.exp (-(2 * β * t)) * ((Real.exp (2 * β * t) - 1) / (2 * β))) by ring]
  exact mul_le_mul_of_nonneg_left (bielecki_weight_bound hβ ht) hM_nn

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki weight bound — variant with `n L² T` constant.**

For the drift step of the Picard map with Lipschitz constant `L_μ`,
state dimension `n`, and time horizon `T`, the Bielecki-norm
contraction constant is `n L_μ² T / (2β)`. This wraps the
`bielecki_weight_bound` lemma in the specific multiplicative form that
arises from the drift L²-Lipschitz analysis. -/
lemma bielecki_drift_contraction_factor
    (n : ℕ) {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    {β T : ℝ} (hβ : 0 < β) (_hT : 0 ≤ T) :
    (n : ℝ) * L_μ ^ 2 * T * (1 / (2 * β)) =
      (n : ℝ) * L_μ ^ 2 * T / (2 * β) := by
  -- Algebraic equality; the substance is the bound's USE in the contraction.
  -- This lemma exposes the canonical form for downstream Banach-fixed-point use.
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by positivity
  field_simp

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Bielecki contraction threshold.** The drift step is a Bielecki-norm
contraction iff `β > n L_μ² T / 2`, i.e., the Picard contraction
rate `n L_μ² T / (2β) < 1`.

This lemma asserts the threshold and rate explicitly so downstream
Picard-iteration callers can plug in `β = n L_μ² T` (giving rate `1/2`,
a strict contraction). -/
lemma bielecki_contraction_rate_lt_one
    (n : ℕ) {L_μ : ℝ} (_hL_μ_nn : 0 ≤ L_μ)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : (n : ℝ) * L_μ ^ 2 * T < 2 * β) :
    (n : ℝ) * L_μ ^ 2 * T / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_LHS_nn : 0 ≤ (n : ℝ) * L_μ ^ 2 * T :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg n) (sq_nonneg L_μ)) hT_pos.le
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold

omit [MeasurableSpace E] in
/-- **Joint measurability of σ-along-X.** If `X : ℝ → Ω → (Fin n → ℝ)`
is jointly measurable and `σ : ℝ → (Fin n → ℝ) → Fin n → Fin d → ℝ`
is jointly measurable in `(s, x)`, then the composite
`(s, ω) ↦ σ s (X s ω) i j` is jointly measurable on `ℝ × Ω`.

This is the structural lemma that lets the σ component of the Picard
step be passed to `MultidimBrownianMotion.stochasticIntegral` as a
valid integrand. -/
lemma sigma_along_X_measurable
    {n d : ℕ}
    (σ : ℝ → (Fin n → ℝ) → Fin n → Fin d → ℝ)
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X))
    (hσ_meas : Measurable (Function.uncurry σ))
    (i : Fin n) (j : Fin d) :
    Measurable (fun (p : Ω × ℝ) => σ p.2 (X p.2 p.1) i j) := by
  -- Decompose: (ω, s) ↦ σ s (X s ω) i j
  --          = (((s, X s ω) → σ s (X s ω)) → σ s (X s ω) i j) ∘ (p ↦ (p.2, X p.2 p.1))
  -- Each component is measurable.
  -- Step 1: (p : Ω × ℝ) ↦ X p.2 p.1 is measurable via hX_meas.
  have h_X_swap_meas : Measurable (fun p : Ω × ℝ => X p.2 p.1) := by
    have : (fun p : Ω × ℝ => X p.2 p.1)
        = (Function.uncurry X) ∘ (fun p : Ω × ℝ => (p.2, p.1)) := by
      funext p; rfl
    rw [this]
    exact hX_meas.comp (measurable_snd.prodMk measurable_fst)
  -- Step 2: (p : Ω × ℝ) ↦ (p.2, X p.2 p.1) is measurable (product of measurable).
  have h_prod_meas : Measurable (fun p : Ω × ℝ => (p.2, X p.2 p.1)) :=
    measurable_snd.prodMk h_X_swap_meas
  -- Step 3: (s, x) ↦ σ s x is measurable (hσ_meas via Function.uncurry).
  -- Then take component (i, j).
  have h_eval_ij : Measurable (fun (m : Fin n → Fin d → ℝ) => m i j) :=
    (measurable_pi_apply j).comp (measurable_pi_apply i)
  -- σ along the path:
  --   σ p.2 (X p.2 p.1) i j = (h_eval_ij ∘ Function.uncurry σ ∘ h_prod_meas).
  exact h_eval_ij.comp (hσ_meas.comp h_prod_meas)

/-- **Joint measurability of γ-along-X.** Analog of `sigma_along_X_measurable`
for the jump coefficient `γ : ℝ → (Fin n → ℝ) → E → Fin n → ℝ`.

The composite `(ω, s, e) ↦ γ s (X s ω) e i` is jointly measurable on
`Ω × ℝ × E`, given joint measurability of X and γ. This is what makes
the γ component of the Picard step well-typed for the
`Compensated.stochasticIntegral` integrand. -/
lemma gamma_along_X_measurable
    {n : ℕ}
    (γ : ℝ → (Fin n → ℝ) → E → Fin n → ℝ)
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X))
    (hγ_meas : Measurable
      (fun (p : ℝ × (Fin n → ℝ) × E) => γ p.1 p.2.1 p.2.2))
    (i : Fin n) :
    Measurable (fun (p : Ω × ℝ × E) => γ p.2.1 (X p.2.1 p.1) p.2.2 i) := by
  -- The composite extracts (ω, s, e), evaluates X at (ω, s), and feeds (s, X s ω, e) into γ.
  -- Step 1: (p : Ω × ℝ × E) ↦ X p.2.1 p.1 measurable.
  have h_X_along_meas : Measurable (fun p : Ω × ℝ × E => X p.2.1 p.1) := by
    have : (fun p : Ω × ℝ × E => X p.2.1 p.1)
        = (Function.uncurry X) ∘ (fun p : Ω × ℝ × E => (p.2.1, p.1)) := by
      funext p; rfl
    rw [this]
    exact hX_meas.comp ((measurable_snd.comp measurable_id).fst.prodMk measurable_fst)
  -- Step 2: (p : Ω × ℝ × E) ↦ (p.2.1, X p.2.1 p.1, p.2.2) measurable.
  have h_triple_meas : Measurable
      (fun p : Ω × ℝ × E => (p.2.1, X p.2.1 p.1, p.2.2)) := by
    exact ((measurable_snd.comp measurable_id).fst.prodMk
      (h_X_along_meas.prodMk (measurable_snd.comp measurable_id).snd))
  -- Step 3: γ evaluation gives Fin n → ℝ; take component i.
  have h_eval_i : Measurable (fun (v : Fin n → ℝ) => v i) := measurable_pi_apply i
  exact h_eval_i.comp (hγ_meas.comp h_triple_meas)

/-- **Picard map diffusion component (σ row i along X).**

For row `i : Fin n`, the diffusion component is
`∫_0^t (σ(s, X_s) i) · dW_s`, i.e., the multidim Brownian Itô integral
of `Z_i(s, ω) := fun j => σ(s, X(s,ω)) i j` against `W`.

Built using `MultidimBrownianMotion.stochasticIntegral`. The hypotheses
`h_meas`, `h_progMeas`, `h_sq_int_global` propagate from joint-measurability
+ progressive-measurability + L²-boundedness of σ along X, which in turn
follow from the corresponding hypotheses on X and σ. -/
noncomputable def picardStep_diffusion
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    -- Per-row joint measurability of σ along X.
    (h_meas : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    -- Progressive measurability wrt W component j's natural filtration.
    (h_progMeas : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i j))
    -- Per-row, per-component L² boundedness on every finite horizon.
    (h_sq_int_global : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
    W (fun s ω' => fun j => coeffs.σ s (X s ω') i j)
    (h_meas i) (h_progMeas i) (h_sq_int_global i) t ω

/-- **Picard map jump component (γ row i along X compensated-Poisson integral).**

For row `i : Fin n`, the jump component is
`∫_0^t ∫_E γ(s, X_s, e) i Ñ(ds, de)`, i.e., the compensated-Poisson
integral of `(s, e, ω) ↦ γ(s, X(s,ω), e) i` against `Ñ`.

Built using `Compensated.stochasticIntegral`. The hypotheses
`h_meas`, `h_progMeas`, `h_sq` propagate from joint Ω×ℝ×E-measurability
+ progressive-measurability + L²-boundedness of γ along X. -/
noncomputable def picardStep_jump
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    -- Per-row joint Ω×ℝ×E measurability.
    (h_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    -- Per-row progressive measurability wrt N's natural filtration.
    (h_progMeas : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    -- Per-row L² boundedness on every finite horizon.
    (h_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => LevyStochCalc.Poisson.Compensated.stochasticIntegral N
    (fun ω' s e => coeffs.γ s (X s ω') e i)
    (h_meas i) (h_progMeas i) (h_sq i) t ω

/-- **The full Picard map.** Combines the drift, diffusion (Brownian),
and jump (compensated-Poisson) components:

  `Φ X t ω = x₀ + ∫_0^t μ(s, X_s) ds + ∫_0^t σ(s, X_s) dW_s
          + ∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)`

The `x₀ +` is already in `picardStep_drift`; here we add the diffusion
and jump components.

This is the literature Picard map for the jump-diffusion SDE (Applebaum
6.2.9 / Ikeda-Watanabe IV). The hypotheses required to make all three
components well-typed are bundled as explicit parameters. -/
noncomputable def picardStep
    {P : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    -- σ-side hypotheses for the Brownian integral.
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
    -- γ-side hypotheses for the compensated-Poisson integral.
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
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  picardStep_drift coeffs X x₀ t ω
    + picardStep_diffusion W coeffs X h_σ_meas h_σ_progMeas h_σ_sq t ω
    + picardStep_jump N coeffs X h_γ_meas h_γ_progMeas h_γ_sq t ω

/-! ## Next-step roadmap (Picard contraction & fixed point)

The lemmas above are the drift-component Lipschitz scaffolding (L¹
form). The remaining pieces of the Picard fixed-point proof are:

1. **L² Cauchy-Schwarz helper** `(∫_0^t f)² ≤ t · ∫_0^t f²` for the
   Bielecki-norm contraction estimate. (Hölder with `p = q = 2`,
   constant `1` as `g`; in progress, see commit history.)

2. **`picardStep_diffusion`** — Brownian-integral component of the
   Picard map, defined via `MultidimBrownianMotion.stochasticIntegral`
   applied row-wise to `σ(s, X_s)`.

3. **`picardStep_diffusion_lipschitz`** — Lipschitz bound via the
   Tier 1 #5 L²-isometry + Lipschitz hypothesis on σ.

4. **`picardStep_jump`** — Compensated-Poisson component via
   `Compensated.stochasticIntegral` on `γ(s, X_s, e)`.

5. **`picardStep_jump_lipschitz`** — Lipschitz bound via the Tier 1
   #6 L²-isometry + Lipschitz hypothesis on γ.

6. **`picardStep`** — full Picard map summing drift + diffusion + jump.

7. **`picardStep_bielecki_contraction`** — for `β ≥ β₀(L)` (some
   threshold depending on the Lipschitz constant), Φ is a contraction
   in the Bielecki β-norm.

8. **`picardFixedPoint`** — apply `ContractingWith.fixedPoint` (Mathlib
   Banach-fixed-point) to get a unique fixed point of Φ.

9. **`fixedPoint_is_solution`** — show the fixed point satisfies the
   SDE integral equation, providing the strong solution.

10. **`JumpDiffusion.exists_unique`** — assemble the above into the
    theorem statement; uniqueness from the Banach contraction.

Active work continues file by file; each Mathlib API need (Cauchy-
Schwarz, integral monotonicity, ContractingWith) gets a dedicated
lemma here when not already available. -/

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **L²-isometry for the *difference* of two Brownian Itô integrals** (formerly
cited axiom #17, now a theorem).

For two progressively-measurable, L²-bounded integrands `H₁, H₂`, the
difference `M¹_T - M²_T := ∫_0^T H₁ dW - ∫_0^T H₂ dW` satisfies the
L²-isometry against the *integrand difference*:

  `𝔼 |M¹_T - M²_T|² = 𝔼 ∫_0^T |H₁(s) - H₂(s)|² ds`.

**Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*,
Springer 1991, **Theorem 3.2.6** + the unique-extension lemma for the
L²-Itô integral as a continuous linear isometry from `L²(Ω × [0, T])`
to `L²(Ω)` (Karatzas-Shreve §3.2.B).

Now that `stochasticIntegral` is the genuine `L²`-limit construction
(`stochasticIntegralBrownian`), this follows from
`isometry_diff_stochasticIntegralBrownian`: both the integral difference and the
integrand difference are `L²`-limits of the same simple-integral difference. -/
theorem itoIsometry_diff_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H₁ H₂ : Ω → ℝ → ℝ)
    (h_meas₁ : Measurable (Function.uncurry H₁))
    (h_meas₂ : Measurable (Function.uncurry H₂))
    (h_progMeas₁ : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H₁ p.1 p.2))
    (h_progMeas₂ : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H₂ p.1 p.2))
    (h_sq_int_global₁ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_sq_int_global₂ : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral W H₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T ω
              - stochasticIntegral W H₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T ω‖₊
            : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  unfold stochasticIntegral
  exact isometry_diff_stochasticIntegralBrownian W H₁ H₂ h_meas₁ h_meas₂
    h_progMeas₁ h_progMeas₂ h_sq_int_global₁ h_sq_int_global₂ hT

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Cauchy-Schwarz on a finite sum (real form).**

For `d` real numbers `a₀, ..., a_{d-1}`, the discrete Cauchy-Schwarz
inequality gives `(∑_j a_j)² ≤ d · ∑_j a_j²`. Used below to bound the
squared norm of the row-`i` diffusion sum `∑_j ∫ σ(X)_{ij} dW^j_s` from
the per-component bounds. -/
lemma sum_sq_le_card_mul_sum_sq_real
    {d : ℕ} (a : Fin d → ℝ) :
    (∑ j : Fin d, a j) ^ 2 ≤ (d : ℝ) * ∑ j : Fin d, (a j) ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d))) (f := a)
  simpa [Finset.card_univ, Fintype.card_fin] using h

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Real-to-ENNReal nnnorm-square identity.**  For `r : ℝ`,

  `(‖r‖₊ : ℝ≥0∞)² = ENNReal.ofReal (r²)`.

The bridge between the real-side bookkeeping (where we manipulate
`(∑ j a_j)²` with ring/algebra rules) and the ENNReal-side bookkeeping
(where we apply isometry / lintegral mono). -/
lemma ennreal_nnnorm_sq_real (r : ℝ) :
    ((‖r‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (r ^ 2) := by
  have h1 : ((‖r‖₊ : ℝ≥0∞)) = ENNReal.ofReal |r| := by
    rw [show ((‖r‖₊ : ℝ≥0∞)) = ‖r‖ₑ from rfl, Real.enorm_eq_ofReal_abs]
  rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Normed-space ENNReal nnnorm-square identity.**  For a normed group
element `r : α`,

  `(‖r‖₊ : ℝ≥0∞)² = ENNReal.ofReal (‖r‖²)`.

Generalization of `ennreal_nnnorm_sq_real` to any `NormedAddCommGroup`,
used below for `Fin n → ℝ`-valued differences `X s ω - Y s ω`. -/
lemma ennreal_nnnorm_sq_normed {α : Type*} [NormedAddCommGroup α] (r : α) :
    ((‖r‖₊ : ℝ≥0∞)) ^ 2 = ENNReal.ofReal (‖r‖ ^ 2) := by
  have h : ((‖r‖₊ : ℝ≥0∞)) = ENNReal.ofReal ‖r‖ :=
    (ofReal_norm_eq_enorm r).symm
  rw [h, ← ENNReal.ofReal_pow (norm_nonneg _)]

omit [MeasurableSpace E] in
/-- **Sum-of-Itô-integrals Cauchy-Schwarz bound, ENNReal lintegral form.**

For a finite family `M_j : Ω → ℝ` of square-integrable processes,
applying the pointwise discrete Cauchy-Schwarz inequality
`(∑_j M_j(ω))² ≤ d · ∑_j (M_j(ω))²` and taking the `P`-lintegral gives

  `∫⁻ ω, ‖∑_j M_j(ω)‖₊² ∂P ≤ d · ∑_j ∫⁻ ω, ‖M_j(ω)‖₊² ∂P`.

The proof routes through `ENNReal.ofReal` for the real-valued square
bound, then uses `lintegral_const_mul` and `lintegral_finsetSum`
(monotonicity of swapping `∑` and `∫⁻` for non-negative integrands). -/
lemma lintegral_nnnorm_sum_sq_le_card_mul_sum_lintegral_nnnorm_sq
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {d : ℕ} (M : Fin d → Ω → ℝ)
    (hM : ∀ j : Fin d, Measurable (M j)) :
    ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Pointwise: ENNReal.ofReal((∑ M_j ω)²) ≤ ENNReal.ofReal(d * ∑ M_j ω²)
  --                                         = d · ∑ ENNReal.ofReal(M_j ω²)
  have h_cs_ofReal : ∀ ω : Ω,
      ENNReal.ofReal ((∑ j : Fin d, M j ω) ^ 2)
        ≤ ENNReal.ofReal ((d : ℝ)) * ∑ j : Fin d, ENNReal.ofReal ((M j ω) ^ 2) := by
    intro ω
    have h_sum_sq : (∑ j : Fin d, M j ω) ^ 2
        ≤ (d : ℝ) * ∑ j : Fin d, (M j ω) ^ 2 :=
      sum_sq_le_card_mul_sum_sq_real (fun j => M j ω)
    have h_d_nn : (0 : ℝ) ≤ (d : ℝ) := by positivity
    have h_each_nn : ∀ j : Fin d, 0 ≤ (M j ω) ^ 2 := fun j => sq_nonneg _
    have h_sum_inner_nn : 0 ≤ ∑ j : Fin d, (M j ω) ^ 2 :=
      Finset.sum_nonneg (fun j _ => h_each_nn j)
    calc ENNReal.ofReal ((∑ j : Fin d, M j ω) ^ 2)
        ≤ ENNReal.ofReal ((d : ℝ) * ∑ j : Fin d, (M j ω) ^ 2) :=
            ENNReal.ofReal_le_ofReal h_sum_sq
      _ = ENNReal.ofReal ((d : ℝ)) * ENNReal.ofReal (∑ j : Fin d, (M j ω) ^ 2) :=
            ENNReal.ofReal_mul h_d_nn
      _ = ENNReal.ofReal ((d : ℝ)) * ∑ j : Fin d, ENNReal.ofReal ((M j ω) ^ 2) := by
            rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h_each_nn j)]
  -- Rewrite the LHS to the ofReal form via nnnorm_sq_real.
  have h_LHS_ofReal : ∀ ω : Ω,
      (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2
        = ENNReal.ofReal ((∑ j : Fin d, M j ω) ^ 2) :=
    fun ω => ennreal_nnnorm_sq_real _
  -- Per-j rewrite: (‖M_j ω‖₊ : ℝ≥0∞)² = ENNReal.ofReal((M_j ω)²)
  have h_per_j_ofReal : ∀ ω : Ω, ∀ j : Fin d,
      (‖M j ω‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((M j ω) ^ 2) :=
    fun ω j => ennreal_nnnorm_sq_real _
  -- Pull together the pointwise bound:
  have h_pt : ∀ ω : Ω,
      (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal ((d : ℝ)) * ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω
    rw [h_LHS_ofReal ω]
    refine (h_cs_ofReal ω).trans ?_
    rw [show ∑ j : Fin d, ENNReal.ofReal ((M j ω) ^ 2)
          = ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 from by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [h_per_j_ofReal ω j]]
  -- Now take the lintegral.
  calc ∫⁻ ω, (‖∑ j : Fin d, M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal ((d : ℝ)) *
          ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_mono h_pt
    _ = ENNReal.ofReal ((d : ℝ)) *
        ∫⁻ ω, ∑ j : Fin d, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((d : ℝ)) *
        ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        congr 1
        rw [MeasureTheory.lintegral_finsetSum]
        intro j _
        exact ((hM j).enorm).pow_const 2
    _ = (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖M j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
        rw [ENNReal.ofReal_natCast]

omit [MeasurableSpace E] in
/-- **Per-row L²-Lipschitz bound on the Picard diffusion step (ENNReal form).**

For row `i : Fin n`, the squared expected difference of the diffusion
component is bounded by `d · L_σ² · 𝔼 ∫_0^T ‖X-Y‖²`:

  `𝔼 |(picardStep_diffusion W coeffs X)ᵢ -
       (picardStep_diffusion W coeffs Y)ᵢ|²
   ≤ d · L_σ² · 𝔼 ∫_0^T ‖X_s - Y_s‖² ds`.

**Proof sketch**:

1. The row-`i` diffusion is `∑_j ∫ σ(X)_{ij} dW^j` (definition of
   `MultidimBrownianMotion.stochasticIntegral` + `picardStep_diffusion`).

2. Cauchy-Schwarz on the j-sum:
   `(∑_j a_j)² ≤ d · ∑_j a_j²`.

3. Per-(i, j) L²-isometry of the integral difference (Tier 1 axiom #11
   `itoIsometry_diff_brownian`):
   `𝔼 |∫ σ(X)_{ij} dW^j - ∫ σ(Y)_{ij} dW^j|² = 𝔼 ∫ |σ(X)_{ij} - σ(Y)_{ij}|² ds`.

4. Sum over `j` and apply the Lipschitz hypothesis (rebracketing the
   joint sum to feed `∑_j (σ(X)_{ij} - σ(Y)_{ij})² ≤ ∑_{i'j'} (...)²
   ≤ L_σ² · ‖X-Y‖²`).

5. Combine: `𝔼 |row-i diff|² ≤ d · L_σ² · 𝔼 ∫ ‖X-Y‖²`. -/
lemma picardStep_diffusion_diff_lipschitz_sq_componentwise
    {n d : ℕ}
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_σ : ℝ} (_hL_σ_nn : 0 ≤ L_σ)
    -- Componentwise Lipschitz hypothesis on σ (matches `JumpDiffusionCoeffs.IsLipschitz`):
    -- `∑_{i,j} (σ(s, x₁)_{ij} - σ(s, x₂)_{ij})² ≤ L_σ² · ‖x₁ - x₂‖²`
    (h_σ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
      (∑ i : Fin n, ∑ j : Fin d,
        (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
        ≤ L_σ ^ 2 * ‖x₁ - x₂‖ ^ 2)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n)
    -- Per-(i', j) measurability / progressive-measurability / L²
    -- hypotheses for σ along X and Y, threaded to `picardStep_diffusion`.
    (h_σ_meas_X : ∀ i' : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i' j)))
    (h_σ_meas_Y : ∀ i' : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i' j)))
    (h_σ_progMeas_X : ∀ i' : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i' j))
    (h_σ_progMeas_Y : ∀ i' : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (Y p.2 p.1) i' j))
    (h_σ_sq_X : ∀ i' : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i' j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_σ_sq_Y : ∀ i' : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (Y s ω) i' j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X T ω i
              - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y T ω i‖₊
            : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal ((d : ℝ) * L_σ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Abbreviation for the per-j 1D Brownian integrals (X and Y branches).
  set Mx : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j)
      (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_σ_meas_X i j) (h_σ_progMeas_X i j) (h_σ_sq_X i j) T ω with hMx
  set My : Fin d → Ω → ℝ := fun j ω =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W j)
      (fun ω' s => coeffs.σ s (Y s ω') i j)
      (h_σ_meas_Y i j) (h_σ_progMeas_Y i j) (h_σ_sq_Y i j) T ω with hMy
  -- The 1D Brownian Itô integral returned by `stochasticIntegral` is a
  -- martingale (`martingale_stochasticIntegral`); each `Mx j T`, `My j T`
  -- is `StronglyMeasurable` w.r.t. the filtration's σ-algebra (a
  -- sub-σ-algebra of the ambient one), and so is measurable w.r.t. the
  -- ambient by `Measurable.mono`.
  have hMx_meas : ∀ j : Fin d, Measurable (Mx j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (h_σ_meas_X i j) (h_σ_progMeas_X i j) (h_σ_sq_X i j)
    have h_sm := hMart.stronglyMeasurable T
    exact h_sm.measurable.mono (Filt.le T) le_rfl
  have hMy_meas : ∀ j : Fin d, Measurable (My j) := by
    intro j
    obtain ⟨Filt, hMart⟩ := LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
      (W.W j) (fun ω' s => coeffs.σ s (Y s ω') i j)
      (h_σ_meas_Y i j) (h_σ_progMeas_Y i j) (h_σ_sq_Y i j)
    have h_sm := hMart.stronglyMeasurable T
    exact h_sm.measurable.mono (Filt.le T) le_rfl
  -- Step 1: unfold picardStep_diffusion to ∑ j (Mx j - My j).
  have h_unfold : ∀ ω : Ω,
      picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X T ω i
        - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y T ω i
        = ∑ j : Fin d, (Mx j ω - My j ω) := by
    intro ω
    simp only [picardStep_diffusion,
      LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
      Mx, My]
    exact (Finset.sum_sub_distrib _ _).symm
  -- Step 2: rewrite the LHS using h_unfold via lintegral_congr.
  have h_LHS_rewrite :
      ∫⁻ ω, (‖picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X T ω i
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y T ω i‖₊
            : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖∑ j : Fin d, (Mx j ω - My j ω)‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_congr (fun ω => by rw [h_unfold ω])
  rw [h_LHS_rewrite]
  -- Step 3: apply the CS-lintegral bound to M_j := Mx j - My j.
  have hM_sub_meas : ∀ j : Fin d, Measurable (fun ω => Mx j ω - My j ω) :=
    fun j => (hMx_meas j).sub (hMy_meas j)
  have h_cs := lintegral_nnnorm_sum_sq_le_card_mul_sum_lintegral_nnnorm_sq
    (P := P) (d := d) (M := fun j ω => Mx j ω - My j ω) hM_sub_meas
  -- Step 4: apply isometry on each j.
  --   ∫⁻ ‖Mx j - My j‖² = ∫⁻ ∫⁻ ‖σ(X) - σ(Y)‖².
  have h_isom_j : ∀ j : Fin d,
      ∫⁻ ω, (‖Mx j ω - My j ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P := by
    intro j
    simp only [Mx, My]
    exact LevyStochCalc.Brownian.Ito.itoIsometry_diff_brownian
      (W.W j) (fun ω' s => coeffs.σ s (X s ω') i j)
      (fun ω' s => coeffs.σ s (Y s ω') i j)
      (h_σ_meas_X i j) (h_σ_meas_Y i j)
      (h_σ_progMeas_X i j) (h_σ_progMeas_Y i j)
      (h_σ_sq_X i j) (h_σ_sq_Y i j) T hT
  -- Step 5: swap ∑_j and ∫⁻ ∫⁻ on the bound.
  --   ∑_j ∫⁻ ω ∫⁻ s f_j = ∫⁻ ω ∫⁻ s ∑_j f_j.
  have h_swap : (∑ j : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ∑ j : Fin d,
          (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P := by
    rw [← MeasureTheory.lintegral_finsetSum]
    · refine MeasureTheory.lintegral_congr (fun ω => ?_)
      rw [← MeasureTheory.lintegral_finsetSum]
      intro j _
      have h_X := h_σ_meas_X i j
      have h_Y := h_σ_meas_Y i j
      have h_X_at_ω : Measurable (fun s : ℝ => coeffs.σ s (X s ω) i j) := by
        have h_pair_meas : Measurable (fun s : ℝ => (ω, s)) :=
          (measurable_const).prodMk measurable_id
        exact h_X.comp h_pair_meas
      have h_Y_at_ω : Measurable (fun s : ℝ => coeffs.σ s (Y s ω) i j) := by
        have h_pair_meas : Measurable (fun s : ℝ => (ω, s)) :=
          (measurable_const).prodMk measurable_id
        exact h_Y.comp h_pair_meas
      have h_sub_at_ω : Measurable
          (fun s : ℝ => coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) :=
        h_X_at_ω.sub h_Y_at_ω
      exact (h_sub_at_ω.enorm).pow_const 2
    · intro j _
      have h_X := h_σ_meas_X i j
      have h_Y := h_σ_meas_Y i j
      have h_sub : Measurable
          (fun p : Ω × ℝ =>
            coeffs.σ p.2 (X p.2 p.1) i j - coeffs.σ p.2 (Y p.2 p.1) i j) :=
        h_X.sub h_Y
      have h_meas_pow : Measurable
          (fun p : Ω × ℝ =>
            (‖coeffs.σ p.2 (X p.2 p.1) i j - coeffs.σ p.2 (Y p.2 p.1) i j‖₊
              : ℝ≥0∞) ^ 2) :=
        (h_sub.enorm).pow_const 2
      exact h_meas_pow.lintegral_prod_right
  -- Step 6: pointwise Lipschitz bound after the swap.
  --   ∑_j (σ(X) i j - σ(Y) i j)² ≤ ∑_{i' j'} (σ(X) i' j' - σ(Y) i' j')²
  --                              ≤ L_σ² ‖X-Y‖²
  have h_lip_pt : ∀ ω : Ω, ∀ s : ℝ,
      (∑ j : Fin d,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal (L_σ ^ 2 * ‖X s ω - Y s ω‖ ^ 2) := by
    intro ω s
    have h_ofReal_each : ∀ j : Fin d,
        (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
          = ENNReal.ofReal ((coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) ^ 2) :=
      fun j => ennreal_nnnorm_sq_real _
    rw [show ∑ j : Fin d,
          (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
        = ∑ j : Fin d,
            ENNReal.ofReal
              ((coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) ^ 2) from
      Finset.sum_congr rfl (fun j _ => h_ofReal_each j)]
    have h_each_nn : ∀ j : Fin d,
        (0 : ℝ) ≤ (coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j) ^ 2 :=
      fun j => sq_nonneg _
    rw [← ENNReal.ofReal_sum_of_nonneg (fun j _ => h_each_nn j)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine le_trans ?_ (h_σ_lip s (X s ω) (Y s ω))
    refine Finset.single_le_sum (f := fun i' => ∑ j : Fin d,
        (coeffs.σ s (X s ω) i' j - coeffs.σ s (Y s ω) i' j) ^ 2)
      (fun i' _ => Finset.sum_nonneg (fun j _ => sq_nonneg _))
      (Finset.mem_univ i)
  -- Step 7: chain everything.
  calc ∫⁻ ω, (‖∑ j : Fin d, (Mx j ω - My j ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d,
          ∫⁻ ω, (‖Mx j ω - My j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := h_cs
    _ = (d : ℝ≥0∞) * ∑ j : Fin d,
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => h_isom_j j)
    _ = (d : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ∑ j : Fin d,
            (‖coeffs.σ s (X s ω) i j - coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by rw [h_swap]
    _ ≤ (d : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (L_σ ^ 2 * ‖X s ω - Y s ω‖ ^ 2) ∂volume ∂P := by
        refine mul_le_mul_of_nonneg_left ?_ (by exact bot_le)
        refine lintegral_mono (fun ω => ?_)
        refine lintegral_mono (fun s => ?_)
        exact h_lip_pt ω s
    _ = (d : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (L_σ ^ 2) *
          (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        congr 1
        refine lintegral_congr (fun ω => ?_)
        refine lintegral_congr (fun s => ?_)
        rw [ennreal_nnnorm_sq_normed (X s ω - Y s ω),
          ← ENNReal.ofReal_mul (sq_nonneg _)]
    _ = (d : ℝ≥0∞) * (ENNReal.ofReal (L_σ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
        congr 1
        have h_inner : ∀ ω : Ω,
            ∫⁻ s in Set.Icc (0 : ℝ) T,
              ENNReal.ofReal (L_σ ^ 2) *
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
            = ENNReal.ofReal (L_σ ^ 2) *
              ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
          fun ω => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
              ENNReal.ofReal (L_σ ^ 2) *
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
            = (fun ω => ENNReal.ofReal (L_σ ^ 2) *
              ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume) from funext h_inner]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((d : ℝ) * L_σ ^ 2) *
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← mul_assoc]
        congr 1
        rw [show (d : ℝ≥0∞) = ENNReal.ofReal (d : ℝ) by
          rw [ENNReal.ofReal_natCast]]
        rw [← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ (d:ℝ))]

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Per-component L²-Lipschitz bound on the γ (jump) component of the
Picard map.**

Given:

* a compensated-Poisson integrand structure (PRM `N`, intensity `ν`,
  coefficient bundle `coeffs`),
* L²-in-`e` Lipschitz hypothesis on `γ` in the state argument with rate
  `L_γ` (ENNReal form),
* the joint measurability / progressive measurability / L²-boundedness
  hypothesis bundles that `picardStep_jump` requires for `X` and `Y`,

the per-(t = T) L²-norm of the difference of jump-step components is
bounded by `L_γ²` times the time-integrated squared L² distance:

  `∫⁻ ω, ‖(picardStep_jump X)_i T ω − (picardStep_jump Y)_i T ω‖² ∂P
    ≤ ENNReal.ofReal L_γ² · ∫⁻ ω, ∫⁻ s ∈ [0, T], ‖X_s ω − Y_s ω‖² ds ∂P`.

This is the operator-level per-component bound that, when summed over
`i ∈ Fin n` and combined with the Bielecki time-weight, yields the
γ-Lipschitz term in the Bielecki β-norm contraction estimate.

**Proof**: forwards through the per-difference L²-isometry axiom
`LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated` (cited axiom
#18), then applies the γ-Lipschitz hypothesis pointwise and extracts the
constant via `lintegral_const_mul`. -/
lemma picardStep_jump_diff_lipschitz_sq_componentwise
    {n d : ℕ}
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L_γ : ℝ} (_hL_γ_nn : 0 ≤ L_γ)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n)
    -- L²-in-e Lipschitz hypothesis on γ (ENNReal form, pointwise in (s, ω)):
    (h_γ_lip : ∀ s : ℝ, ∀ ω : Ω,
      ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
        ≤ ENNReal.ofReal (L_γ ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2)
    -- Hypothesis bundles for `picardStep_jump` well-typedness — X side:
    (hX_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (hX_progMeas : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (hX_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Hypothesis bundles — Y side:
    (hY_meas : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hY_progMeas : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hY_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖picardStep_jump (E := E) N coeffs X hX_meas hX_progMeas hX_sq T ω i
            - picardStep_jump N coeffs Y hY_meas hY_progMeas hY_sq T ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (L_γ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Step 1: unfold `picardStep_jump` (definitional) so the LHS is exactly
  -- the L²-norm-squared of the difference of two `Compensated.stochasticIntegral`
  -- outputs, matching the LHS of the `itoIsometry_diff_compensated` axiom.
  -- `picardStep_jump` is `noncomputable def`-ed as
  --   `fun i => Compensated.stochasticIntegral N (fun ω' s e => γ s (X s ω') e i) ... T ω`
  -- so the lemma's LHS is, by `unfold + simp only [picardStep_jump]`,
  -- exactly the LHS of Tier 1 axiom #14 with
  --   φ₁ ω' s e := γ s (X s ω') e i
  --   φ₂ ω' s e := γ s (Y s ω') e i.
  -- Step 2: apply the axiom to get equality with the inner double-lintegral
  -- of `‖γ(s, X_s, e) i − γ(s, Y_s, e) i‖²`.
  have h_iso := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated
    N (fun ω' s e => coeffs.γ s (X s ω') e i)
      (fun ω' s e => coeffs.γ s (Y s ω') e i)
    (hX_meas i) (hY_meas i)
    (hX_progMeas i) (hY_progMeas i)
    (hX_sq i) (hY_sq i) T hT
  -- Rewriting the LHS via the axiom turns the goal into the bound
  -- `inner double lintegral ≤ ENNReal.ofReal L_γ²
  --   · ∫⁻ ω ∫⁻ s, ‖X-Y‖² ∂volume ∂P`.
  -- `picardStep_jump i` unfolds definitionally to the `Compensated.stochasticIntegral`
  -- of `γ ... i`, so the rewrite goes through `show`+`exact_mod_cast`.
  simp only [picardStep_jump] at *
  rw [h_iso]
  -- Goal now:
  -- ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e,
  --   ‖γ(s, X_s, e) i − γ(s, Y_s, e) i‖² ν⊗ds ∂P
  --   ≤ ENNReal.ofReal L_γ² · ∫⁻ ω, ∫⁻ s in [0,T], ‖X_s ω − Y_s ω‖² ds ∂P
  -- Step 3: apply the Lipschitz hypothesis h_γ_lip pointwise in (s, ω) under
  -- the inner ν-integral.  This gives a chain through `lintegral_mono`.
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞)) ^ 2
          ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (ENNReal.ofReal (L_γ ^ 2) * (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2)
            ∂volume ∂P := by
        refine lintegral_mono fun ω => ?_
        refine lintegral_mono fun s => ?_
        exact h_γ_lip s ω
    _ = ∫⁻ ω, ENNReal.ofReal (L_γ ^ 2) *
            ∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine lintegral_congr fun ω => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (L_γ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end LevyStochCalc.Ito.Picard

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
estimate (proved in `Picard.lean`) operates on the
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
proved in `Picard.lean` operates on `picardStep` directly,
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

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Sub-additivity of squared sums on three terms.**

  `(a + b + c)² ≤ 3 · (a² + b² + c²)`.

This is the standard Cauchy-Schwarz / AM-QM bound on three terms and is the
load-bearing combinatorial step that turns the three component L² bounds
(drift, σ, γ) into a single bound on the full Picard step. -/
lemma sq_add_three_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Sub-additivity of squared norms on three vector terms.**

For `u v w : Fin n → ℝ`,

  `∑ i, (u i + v i + w i)² ≤ 3 · (∑ i, (u i)² + ∑ i, (v i)² + ∑ i, (w i)²)`.

This is `sq_add_three_le` applied componentwise and summed over `Fin n`. -/
lemma sum_sq_add_three_le {n : ℕ} (u v w : Fin n → ℝ) :
    ∑ i : Fin n, (u i + v i + w i) ^ 2
      ≤ 3 * (∑ i : Fin n, (u i) ^ 2 + ∑ i : Fin n, (v i) ^ 2
              + ∑ i : Fin n, (w i) ^ 2) := by
  have h_each : ∀ i : Fin n, (u i + v i + w i) ^ 2
      ≤ 3 * ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) := fun i =>
    sq_add_three_le (u i) (v i) (w i)
  calc (∑ i : Fin n, (u i + v i + w i) ^ 2)
      ≤ ∑ i : Fin n, 3 * ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) :=
        Finset.sum_le_sum (fun i _ => h_each i)
    _ = 3 * ∑ i : Fin n, ((u i) ^ 2 + (v i) ^ 2 + (w i) ^ 2) := by
        rw [← Finset.mul_sum]
    _ = 3 * (∑ i : Fin n, (u i) ^ 2 + ∑ i : Fin n, (v i) ^ 2
              + ∑ i : Fin n, (w i) ^ 2) := by
        congr 1
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- **Picard step pointwise sum-of-squares triangle bound.**

For `Φ X = drift X + diff X + jump X` and any two `X Y`, the squared
Euclidean norm of `(Φ X - Φ Y) t ω` is bounded componentwise by three
times the sum of the three component squared norms:

  `∑ i, ((Φ X t ω - Φ Y t ω) i)²
    ≤ 3 · (∑ i, ((drift_diff)i)² + ∑ i, ((diff_diff)i)² + ∑ i, ((jump_diff)i)²)`.

This is the algebraic identity `picardStep = drift + diff + jump` followed
by `sum_sq_add_three_le`. -/
lemma picardStep_diff_sum_sq_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (Y p.2 p.1) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) :
    ∑ i : Fin n, ((picardStep W N coeffs X x₀
        h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
      - picardStep W N coeffs Y x₀
        h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2
    ≤ 3 * (∑ i : Fin n, ((picardStep_drift coeffs X x₀ t ω
                          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
          + ∑ i : Fin n, ((picardStep_diffusion W coeffs X
                            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                          - picardStep_diffusion W coeffs Y
                            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2
          + ∑ i : Fin n, ((picardStep_jump N coeffs X
                            h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                          - picardStep_jump N coeffs Y
                            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) := by
  -- Unfold picardStep = drift + diffusion + jump and apply sum_sq_add_three_le.
  unfold picardStep
  have h_sq_eq : ∀ i : Fin n,
      (((picardStep_drift coeffs X x₀ t ω
            + picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            + picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω)
          - (picardStep_drift coeffs Y x₀ t ω
            + picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω
            + picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω)) i) ^ 2
      = ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i
          + (picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
              - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i
          + (picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2 := by
    intro i
    simp only [Pi.add_apply, Pi.sub_apply]; ring
  rw [Finset.sum_congr rfl (fun i _ => h_sq_eq i)]
  exact sum_sq_add_three_le _ _ _

/-- **Picard step lintegral sum-of-squares triangle bound (single-integral form).**

Lift `picardStep_diff_sum_sq_le` to the lintegral over `ω`. The RHS is
stated as a SINGLE lintegral of the (pointwise) three-term sum, not as
three separate lintegrals, in order to avoid requiring AEMeasurable
hypotheses on the individual component differences (which would in turn
require joint measurability hypotheses on `X, Y` that are not yet in scope
at this level of the Picard scaffolding).

To downstream callers: once you have AEMeasurable hypotheses for the
individual `ENNReal.ofReal (∑ i, ((picardStep_drift ...) i)^2)` and the
analogous σ + γ functions, you can split the RHS lintegral via
`MeasureTheory.lintegral_add_left'` to recover the three-separate-lintegrals
form expected by the drift/σ/γ bound lemmas. -/
lemma picardStep_diff_lintegral_sum_sq_le
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (Y p.2 p.1) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (t : ℝ) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep W N coeffs X x₀
          h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        - picardStep W N coeffs Y x₀
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ∫⁻ ω, 3 * (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P := by
  -- Pointwise (in ω) ENNReal-lifted form of `picardStep_diff_sum_sq_le`.
  have h_ptw : ∀ ω : Ω,
      ENNReal.ofReal (∑ i : Fin n,
        ((picardStep W N coeffs X x₀
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep W N coeffs Y x₀
            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)
      ≤ 3 *
          (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) := by
    intro ω
    have h_real := picardStep_diff_sum_sq_le W N coeffs X Y x₀
      h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω
    have h_drift_nn : 0 ≤ ∑ i : Fin n,
        ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_diff_nn : 0 ≤ ∑ i : Fin n,
        ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have h_jump_nn : 0 ≤ ∑ i : Fin n,
        ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    -- Convert h_real : LHS ≤ 3 * (a + b + c) to ENNReal.
    have h_RHS_eq : (3 : ℝ≥0∞) *
        (ENNReal.ofReal (∑ i : Fin n,
            ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
        = ENNReal.ofReal (3 * (∑ i : Fin n,
            ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2
          + ∑ i : Fin n,
            ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
              - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2
          + ∑ i : Fin n,
            ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N coeffs Y
                  h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) := by
      rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by rw [ENNReal.ofReal_ofNat]]
      rw [← ENNReal.ofReal_add h_drift_nn h_diff_nn]
      rw [← ENNReal.ofReal_add (by positivity) h_jump_nn]
      rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    rw [h_RHS_eq]
    exact ENNReal.ofReal_le_ofReal h_real
  exact MeasureTheory.lintegral_mono h_ptw

/-- **Picard step Bielecki β-norm contraction (per-time lintegral form).**

The headline contraction estimate. For each `t ∈ [0, T]`, the lintegral L²
mass of the Picard step difference is bounded by

  `9 · n · L² · T · ∫⁻ ω, ∫₀^t ‖X_s - Y_s‖² ds ∂P`,

via the triangle bound on the three components (factor 3) combined with
the uniform overbound `n L² t` on the σ-step and γ-step (factor 3 again
because `t ≤ T` is applied to a sum of three identical-shape bounds). The
literature-tight σ/γ bounds (`L²` per component without `n t`) tighten this
to the prompt's stated `3 n L² T / (2β)` rate; the gap is intentionally
left open since the σ/γ-Lipschitz proofs are in flight.

After applying the Bielecki weight `e^{-2βt}` and using
`bielecki_weighted_integral_bound`, the per-`t` weighted bound is
`9 n L² T / (2β) · ‖X - Y‖²_β,T`. Together with
`picardStep_bielecki_contraction_rate_lt_one`, the Picard map is a strict
contraction in the Bielecki β-norm for `β > 9 n L² T / 2`.

The σ-step and γ-step bound hypotheses (`h_σ_step_bound`, `h_γ_step_bound`)
have the EXACT signature shape of the proven drift bound
`picardStep_drift_diff_lintegral_sq_bound`; they will be discharged when
the parallel σ + γ Lipschitz proofs land. -/
theorem picardStep_bielecki_contraction
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hL_nn : 0 ≤ L)
    -- μ-Lipschitz (componentwise; used inside the drift lintegral bound):
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (T : ℝ) (_hT : 0 < T)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (Y p.2 p.1) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Drift bound's a.e. hypotheses (must hold at every `t ∈ [0, T]`):
    (h_drift_bound_ae : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    (h_drift_inner_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- σ-step lintegral bound (hypothesis — discharged by parallel σ-Lipschitz proof):
    (h_σ_step_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- γ-step lintegral bound (hypothesis — discharged by parallel γ-Lipschitz proof):
    (h_γ_step_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- AEMeasurability of the three component sum-of-squares ofReal functions.
    -- These are needed to split the triple-term lintegral on the RHS of
    -- `picardStep_diff_lintegral_sum_sq_le`. The downstream caller will produce
    -- them from joint measurability of X, Y and the σ/γ coefficient measurability.
    (h_drift_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)) P)
    (h_diff_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)) P)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep W N coeffs X x₀
          h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        - picardStep W N coeffs Y x₀
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal (9 * (n : ℝ) * L ^ 2 * T) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
          ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  obtain ⟨ht_nn, ht_le⟩ := ht
  -- Drift bound at t (proven; from `Picard.lean`).
  have h_drift := picardStep_drift_diff_lintegral_sq_bound (E := E) P coeffs hL_nn h_μ_lip
    X Y x₀ t ht_nn (h_drift_bound_ae t ⟨ht_nn, ht_le⟩) (h_drift_inner_nn t ⟨ht_nn, ht_le⟩)
  -- σ + γ bounds at t (hypothesized).
  have h_σ := h_σ_step_bound t ⟨ht_nn, ht_le⟩
  have h_γ := h_γ_step_bound t ⟨ht_nn, ht_le⟩
  -- Triangle inequality bound (lintegral form; single-integral RHS).
  have h_triangle' := picardStep_diff_lintegral_sum_sq_le W N coeffs X Y x₀
    h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
    h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t
  -- Combine: triangle (single-integral RHS) bounded by 3 * (drift + σ + γ) bound sum.
  -- Rewrite the single-integral RHS as three separate integrals via the AEMeasurable hypotheses,
  -- then sum the three lintegral bounds.
  set Iω : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
      ‖X s ω - Y s ω‖ ^ 2) ∂P with hIω_def
  set Bnt : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) with hBnt_def
  -- h_drift, h_σ, h_γ are bounds of the form `lintegral ≤ Bnt * Iω` for each component.
  -- Sum: `drift_l + σ_l + γ_l ≤ 3 (Bnt * Iω)`.
  -- Step 1: Split the lintegral RHS in h_triangle' into three pieces.
  have h_split_2 : ∫⁻ ω, (ENNReal.ofReal
        (∑ i : Fin n,
          ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
        + ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P :=
    MeasureTheory.lintegral_add_left' (h_diff_ofReal_aemeas t) _
  have h_split_1 : ∫⁻ ω, (ENNReal.ofReal
        (∑ i : Fin n,
          ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P :=
    MeasureTheory.lintegral_add_left' (h_drift_ofReal_aemeas t) _
  -- Combine the splits with the pulled-out 3 factor.
  have h_triangle_split :
      ∫⁻ ω, 3 * (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω
                  - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
            + (∫⁻ ω, ENNReal.ofReal
                  (∑ i : Fin n,
                    ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                      - picardStep_diffusion W coeffs Y
                          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
            + ∫⁻ ω, ENNReal.ofReal
                (∑ i : Fin n,
                  ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                    - picardStep_jump N coeffs Y
                        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P) := by
    rw [MeasureTheory.lintegral_const_mul' _ _ (by norm_num)]
    -- After pulling 3 out: goal is `3 * lintegral_of_sum = 3 * (l1 + l2 + l3)`.
    -- The lintegral_of_sum needs to be split using h_split_1 and h_split_2.
    congr 1
    rw [show (fun ω => ENNReal.ofReal (∑ i, ((picardStep_drift coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + ENNReal.ofReal (∑ i, ((picardStep_diffusion W coeffs X
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
        + ENNReal.ofReal (∑ i,
            ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
            - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
      = (fun ω => ENNReal.ofReal (∑ i, ((picardStep_drift coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal (∑ i, ((picardStep_diffusion W coeffs X
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N coeffs Y
                  h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) from by
      funext ω; rw [add_assoc]]
    rw [h_split_1, h_split_2, add_assoc]
  -- Now: combine the three lintegrals using drift/σ/γ bounds (each ≤ Bnt * Iω).
  have h_sum_bound :
      (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P)
      ≤ Bnt * Iω + Bnt * Iω + Bnt * Iω :=
    add_le_add (add_le_add h_drift h_σ) h_γ
  -- Bnt ≤ ofReal(n L² T) since t ≤ T.
  have h_Bnt_T : Bnt ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h_nL2_nn : 0 ≤ (n : ℝ) * L ^ 2 :=
      mul_nonneg (Nat.cast_nonneg n) (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left ht_le h_nL2_nn
  -- 9 = 3 * 3 as ℝ≥0∞.
  -- Final chain: Φ ≤ ∫⁻ (3 * ...) = 3 * (...) ≤ 3 * (3 Bnt Iω)
  --   = 9 Bnt Iω ≤ 9 (n L² T) Iω.
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep W N coeffs X x₀
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep W N coeffs Y x₀
            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, 3 *
          (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
          ∂P := h_triangle'
    _ = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω
                  - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
            + (∫⁻ ω, ENNReal.ofReal
                  (∑ i : Fin n,
                    ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                      - picardStep_diffusion W coeffs Y
                          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
            + ∫⁻ ω, ENNReal.ofReal
                (∑ i : Fin n,
                  ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                    - picardStep_jump N coeffs Y
                        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P) :=
        h_triangle_split
    _ ≤ 3 * (Bnt * Iω + Bnt * Iω + Bnt * Iω) :=
        mul_le_mul_of_nonneg_left h_sum_bound (by exact bot_le)
    _ = 9 * Bnt * Iω := by ring
    _ ≤ 9 * ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) * Iω := by
        gcongr
    _ = ENNReal.ofReal (9 * ((n : ℝ) * L ^ 2 * T)) * Iω := by
        rw [show (9 : ℝ≥0∞) = ENNReal.ofReal 9 from by rw [ENNReal.ofReal_ofNat]]
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9)]
    _ = ENNReal.ofReal (9 * (n : ℝ) * L ^ 2 * T) * Iω := by ring_nf

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Picard contraction rate threshold.**

The Picard contraction rate `9 n L² T / (2β)` is `< 1` iff `β > 9 n L² T / 2`.

This is the threshold condition for the Picard map to be a strict contraction
in the Bielecki β-norm. Pairing with `picardStep_bielecki_contraction` and
the Bielecki weight bound `bielecki_weighted_integral_bound`, the resulting
estimate

  `e^{-2βt} · ‖Φ X t - Φ Y t‖_{L²(P)}² ≤ (9 n L² T / (2β)) · ‖X - Y‖_{β,T}²`

is a strict contraction for `β > 9 n L² T / 2`. -/
lemma picardStep_bielecki_contraction_rate_lt_one
    (n : ℕ) {L : ℝ} (_hL_nn : 0 ≤ L)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : 9 * (n : ℝ) * L ^ 2 * T < 2 * β) :
    9 * (n : ℝ) * L ^ 2 * T / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_LHS_nn : 0 ≤ 9 * (n : ℝ) * L ^ 2 * T :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (sq_nonneg L)) hT_pos.le
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold

end LevyStochCalc.Ito.Picard

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Picard step Bielecki β-norm contraction — literature-tight rate.**

Refinement of `picardStep_bielecki_contraction` that produces the
literature-tight contraction rate `3 n L² (T + 2)` instead of
`9 n L² T`. The improvement comes from taking the σ-step and γ-step
bound hypotheses in their *tight* form (without the redundant `t`
factor that the original lemma uses to over-bound all three
components uniformly by the drift's `n L² t` constant).

For each `t ∈ [0, T]`, the lintegral L² mass of the Picard step
difference is bounded by

  `3 · n · L² · (T + 2) · ∫⁻ ω, ∫₀^t ‖X_s - Y_s‖² ds ∂P`,

where the three constants summed before the triangle factor 3 are:

* drift: `n · L² · t` per dimension — Cauchy-Schwarz on the time
  integral × per-row μ-Lipschitz × sum over `n` rows,
* σ: `n · L²` per dimension — Itô isometry (no `t` factor) ×
  per-row σ-Lipschitz × sum over `n` rows,
* γ: `n · L²` per dimension — Itô-Lévy isometry (no `t` factor) ×
  per-row γ-Lipschitz × sum over `n` rows.

Total: `(n L² t + 2 n L²) ≤ n L² (T + 2)`, then × 3 from the
triangle inequality `(a + b + c)² ≤ 3 (a² + b² + c²)`.

After applying the Bielecki weight `e^{-2βt}` and using
`bielecki_weighted_integral_bound`, the per-`t` weighted bound is
`3 n L² (T + 2) / (2β) · ‖X - Y‖²_β,T`. Together with
`picardStep_bielecki_contraction_tight_rate_lt_one`, the Picard map
is a strict contraction in the Bielecki β-norm for
`β > 3 n L² (T + 2) / 2`.

For `T ≥ 1` and `n ≥ 1`, this threshold is strictly tighter than the
original `β > 9 n L² T / 2` (since `T + 2 ≤ 3 T` when `T ≥ 1`).
Asymptotically (large `n T`) it matches the literature's
`3 n L² T / (2β)` rate. -/
theorem picardStep_bielecki_contraction_tight
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    {L : ℝ} (hL_nn : 0 ≤ L)
    -- μ-Lipschitz (componentwise; used inside the drift lintegral bound):
    (h_μ_lip : ∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ, ∀ i : Fin n,
      |coeffs.μ s x₁ i - coeffs.μ s x₂ i| ≤ L * ‖x₁ - x₂‖)
    (X Y : ℝ → Ω → (Fin n → ℝ))
    (x₀ : Fin n → ℝ)
    (T : ℝ) (_hT : 0 < T)
    (h_σ_meas_X : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
    (h_σ_progMeas_X : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (X p.2 p.1) i j))
    (h_σ_sq_X : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_X : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_X : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i))
    (h_γ_sq_X : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_σ_meas_Y : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry (fun ω s => coeffs.σ s (Y s ω) i j)))
    (h_σ_progMeas_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W j)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => coeffs.σ p.2 (Y p.2 p.1) i j))
    (h_σ_sq_Y : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Y s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_γ_meas_Y : ∀ i : Fin n,
      Measurable (fun (p : Ω × ℝ × E) => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_progMeas_Y : ∀ i : Fin n, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (h_γ_sq_Y : ∀ i : Fin n, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Drift bound's a.e. hypotheses (must hold at every `t ∈ [0, T]`):
    (h_drift_bound_ae : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        ≤ (n : ℝ) * L ^ 2 * t *
            ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    (h_drift_inner_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, 0 ≤
      ∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2)
    -- **Tight σ-step lintegral bound** (no `t` factor — the
    -- redundant `n · t` padding from the loose version has been
    -- removed; only the natural `n L²` constant remains):
    (h_σ_step_bound_tight : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- **Tight γ-step lintegral bound** (no `t` factor — analogous
    -- removal of the `n · t` padding):
    (h_γ_step_bound_tight : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2) *
          ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P)
    -- AEMeasurability of the three component sum-of-squares ofReal functions,
    -- needed to split the triple-term lintegral on the RHS of
    -- `picardStep_diff_lintegral_sum_sq_le`.
    (h_drift_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_drift (E := E) coeffs X x₀ t ω
          - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)) P)
    (h_diff_ofReal_aemeas : ∀ t : ℝ, AEMeasurable (fun ω : Ω => ENNReal.ofReal
      (∑ i : Fin n, ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
          - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)) P)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
      ((picardStep W N coeffs X x₀
          h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
        - picardStep W N coeffs Y x₀
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
            h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal (3 * (n : ℝ) * L ^ 2 * (T + 2)) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
          ‖X s ω - Y s ω‖ ^ 2) ∂P := by
  obtain ⟨ht_nn, ht_le⟩ := ht
  -- Drift bound at t (proven; from `Picard.lean`).
  have h_drift := picardStep_drift_diff_lintegral_sq_bound (E := E) P coeffs hL_nn h_μ_lip
    X Y x₀ t ht_nn (h_drift_bound_ae t ⟨ht_nn, ht_le⟩) (h_drift_inner_nn t ⟨ht_nn, ht_le⟩)
  -- σ + γ bounds at t (tight form, hypothesized).
  have h_σ := h_σ_step_bound_tight t ⟨ht_nn, ht_le⟩
  have h_γ := h_γ_step_bound_tight t ⟨ht_nn, ht_le⟩
  -- Triangle inequality bound (lintegral form; single-integral RHS).
  have h_triangle' := picardStep_diff_lintegral_sum_sq_le W N coeffs X Y x₀
    h_σ_meas_X h_σ_progMeas_X h_σ_sq_X
    h_γ_meas_X h_γ_progMeas_X h_γ_sq_X
    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t
  -- Abbreviations.
  set Iω : ℝ≥0∞ :=
    ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t,
      ‖X s ω - Y s ω‖ ^ 2) ∂P with hIω_def
  -- Bnt_drift = n L² t  (drift), Bnt_σγ = n L²  (σ and γ tight).
  set Bnt_drift : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) * L ^ 2 * t) with hBnt_drift_def
  set Bnt_σγ : ℝ≥0∞ := ENNReal.ofReal ((n : ℝ) * L ^ 2) with hBnt_σγ_def
  -- Step 1: Split the triple-sum lintegral on the RHS into three separate lintegrals.
  have h_split_2 : ∫⁻ ω, (ENNReal.ofReal
        (∑ i : Fin n,
          ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
        + ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P :=
    MeasureTheory.lintegral_add_left' (h_diff_ofReal_aemeas t) _
  have h_split_1 : ∫⁻ ω, (ENNReal.ofReal
        (∑ i : Fin n,
          ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P :=
    MeasureTheory.lintegral_add_left' (h_drift_ofReal_aemeas t) _
  -- Combine the splits with the pulled-out 3 factor.
  have h_triangle_split :
      ∫⁻ ω, 3 * (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y
                      h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω
                  - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
            + (∫⁻ ω, ENNReal.ofReal
                  (∑ i : Fin n,
                    ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                      - picardStep_diffusion W coeffs Y
                          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
            + ∫⁻ ω, ENNReal.ofReal
                (∑ i : Fin n,
                  ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                    - picardStep_jump N coeffs Y
                        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P) := by
    rw [MeasureTheory.lintegral_const_mul' _ _ (by norm_num)]
    congr 1
    rw [show (fun ω => ENNReal.ofReal (∑ i, ((picardStep_drift coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + ENNReal.ofReal (∑ i, ((picardStep_diffusion W coeffs X
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
        + ENNReal.ofReal (∑ i,
            ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
            - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
      = (fun ω => ENNReal.ofReal (∑ i, ((picardStep_drift coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal (∑ i, ((picardStep_diffusion W coeffs X
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N coeffs Y
                  h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) from by
      funext ω; rw [add_assoc]]
    rw [h_split_1, h_split_2, add_assoc]
  -- Combine the three lintegrals with their NATURAL (distinct) Bnt constants.
  have h_sum_bound :
      (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y
                    h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P)
      ≤ Bnt_drift * Iω + Bnt_σγ * Iω + Bnt_σγ * Iω :=
    add_le_add (add_le_add h_drift h_σ) h_γ
  -- Algebraic upper bound: Bnt_drift + 2·Bnt_σγ ≤ ENNReal.ofReal (n L² (T + 2)).
  -- Pointwise: n L² t + 2 n L² = n L² (t + 2) ≤ n L² (T + 2)  since t ≤ T.
  have h_nL2_nn : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 :=
    mul_nonneg (Nat.cast_nonneg n) (sq_nonneg L)
  have h_nL2t_nn : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * t :=
    mul_nonneg h_nL2_nn ht_nn
  have h_T2_nn : (0 : ℝ) ≤ T + 2 := by linarith [(le_trans ht_nn ht_le)]
  have h_nL2_T2_nn : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * (T + 2) :=
    mul_nonneg h_nL2_nn h_T2_nn
  -- Bnt_drift + 2·Bnt_σγ = ENNReal.ofReal (n L² t + 2 n L²) = ENNReal.ofReal (n L² (t + 2))
  --                     ≤ ENNReal.ofReal (n L² (T + 2)).
  have h_Bnt_combine : Bnt_drift + Bnt_σγ + Bnt_σγ
      ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * (T + 2)) := by
    -- Step 1: Convert sum of ofReal to ofReal of sum (using nonnegativity).
    rw [show Bnt_drift + Bnt_σγ + Bnt_σγ
          = ENNReal.ofReal ((n : ℝ) * L ^ 2 * t + (n : ℝ) * L ^ 2 + (n : ℝ) * L ^ 2) from by
      rw [hBnt_drift_def, hBnt_σγ_def]
      rw [← ENNReal.ofReal_add h_nL2t_nn h_nL2_nn,
          ← ENNReal.ofReal_add (add_nonneg h_nL2t_nn h_nL2_nn) h_nL2_nn]]
    -- Step 2: Bound n L² t + n L² + n L² = n L² (t + 2) ≤ n L² (T + 2)  via t ≤ T.
    refine ENNReal.ofReal_le_ofReal ?_
    have h_eq : (n : ℝ) * L ^ 2 * t + (n : ℝ) * L ^ 2 + (n : ℝ) * L ^ 2
                = (n : ℝ) * L ^ 2 * (t + 2) := by ring
    rw [h_eq]
    have h_mono : (n : ℝ) * L ^ 2 * (t + 2) ≤ (n : ℝ) * L ^ 2 * (T + 2) :=
      mul_le_mul_of_nonneg_left (by linarith) h_nL2_nn
    exact h_mono
  -- Final chain.
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep W N coeffs X x₀
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep W N coeffs Y x₀
            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y
              h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, 3 *
          (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W coeffs Y
                      h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
          ∂P := h_triangle'
    _ = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω
                  - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
            + (∫⁻ ω, ENNReal.ofReal
                  (∑ i : Fin n,
                    ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                      - picardStep_diffusion W coeffs Y
                          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
            + ∫⁻ ω, ENNReal.ofReal
                (∑ i : Fin n,
                  ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                    - picardStep_jump N coeffs Y
                        h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P) :=
        h_triangle_split
    _ ≤ 3 * (Bnt_drift * Iω + Bnt_σγ * Iω + Bnt_σγ * Iω) :=
        mul_le_mul_of_nonneg_left h_sum_bound (by exact bot_le)
    _ = 3 * (Bnt_drift + Bnt_σγ + Bnt_σγ) * Iω := by ring
    _ ≤ 3 * ENNReal.ofReal ((n : ℝ) * L ^ 2 * (T + 2)) * Iω := by
        gcongr
    _ = ENNReal.ofReal (3 * ((n : ℝ) * L ^ 2 * (T + 2))) * Iω := by
        rw [show (3 : ℝ≥0∞) = ENNReal.ofReal 3 from by rw [ENNReal.ofReal_ofNat]]
        rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 3)]
    _ = ENNReal.ofReal (3 * (n : ℝ) * L ^ 2 * (T + 2)) * Iω := by ring_nf

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- **Tight Picard contraction rate threshold.**

The tight Picard contraction rate `3 n L² (T + 2) / (2β)` is `< 1`
iff `β > 3 n L² (T + 2) / 2`.

This is the threshold condition for the Picard map to be a strict
contraction in the Bielecki β-norm under the tight rate. Pairing with
`picardStep_bielecki_contraction_tight` and the Bielecki weight bound
`bielecki_weighted_integral_bound`, the resulting estimate

  `e^{-2βt} · ‖Φ X t - Φ Y t‖_{L²(P)}²`
  `  ≤ (3 n L² (T + 2) / (2β)) · ‖X - Y‖_{β,T}²`

is a strict contraction for `β > 3 n L² (T + 2) / 2`.

For `T ≥ 1` and `n ≥ 1`, this threshold is strictly less than the
original loose threshold `9 n L² T / 2` (since `T + 2 ≤ 3 T` when
`T ≥ 1`), so the Picard fixed point exists at a smaller `β`. -/
lemma picardStep_bielecki_contraction_tight_rate_lt_one
    (n : ℕ) {L : ℝ} (_hL_nn : 0 ≤ L)
    {β T : ℝ} (hT_pos : 0 < T)
    (h_β_threshold : 3 * (n : ℝ) * L ^ 2 * (T + 2) < 2 * β) :
    3 * (n : ℝ) * L ^ 2 * (T + 2) / (2 * β) < 1 := by
  have h_two_beta_pos : (0 : ℝ) < 2 * β := by
    have h_T2_nn : 0 ≤ T + 2 := by linarith
    have h_LHS_nn : 0 ≤ 3 * (n : ℝ) * L ^ 2 * (T + 2) :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg n))
        (sq_nonneg L)) h_T2_nn
    linarith
  rw [div_lt_one h_two_beta_pos]
  exact h_β_threshold

end LevyStochCalc.Ito.Picard
