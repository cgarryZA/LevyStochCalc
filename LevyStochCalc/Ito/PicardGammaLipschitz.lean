/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Picard

/-!
# Picard map γ-component (jump) L²-Lipschitz bound

This file proves the L²-Lipschitz bound for the jump (compensated-Poisson)
component of the Picard map. It is the γ-analog of the drift-side
`picardStep_drift_diff_lipschitz_sq_componentwise` proved in
`Ito.Picard`, completing one of the three operator-level Lipschitz
estimates that feed the Bielecki β-norm contraction.

## Main result

`picardStep_jump_diff_lipschitz_sq_componentwise` — for each
component `i : Fin n`,

  `∫⁻ ω, ‖(picardStep_jump X − picardStep_jump Y) i T ω‖² ∂P
    ≤ ENNReal.ofReal L_γ² · ∫⁻ ω, ∫⁻ s ∈ [0,T], ‖X_s − Y_s‖² ds ∂P`,

assuming γ is L²-in-e Lipschitz in x with rate `L_γ`.

## Proof outline

1. Apply the **per-difference L²-isometry** for the compensated-Poisson
   Itô-Lévy integral
   (`LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated`,
   Tier 1 cited axiom #14):
   `𝔼 |∫∫ φ₁ Ñ − ∫∫ φ₂ Ñ|² = 𝔼 ∫∫ |φ₁ − φ₂|² ν⊗ds`.
   Applied to `φ_k(ω, s, e) := γ(s, X_s ω, e) i` and
   `γ(s, Y_s ω, e) i`, this directly equates the LHS L²-norm of the
   difference of jump-step components to the inner double integral of
   the squared integrand difference.

2. Apply the Lipschitz hypothesis on γ to bound the inner ν-integral by
   `ENNReal.ofReal (L_γ²) · ‖X − Y‖²` pointwise in `(s, ω)`.

3. Monotonicity of `∫⁻` and `lintegral_const_mul` extract the constant
   `ENNReal.ofReal (L_γ²)`.

This is the per-component-i, integrated-over-ω L²-Lipschitz bound.
The corresponding sum-over-`i ∈ Fin n` and time-horizon-T forms follow
by `Finset.sum_le_sum` and `lintegral_mono`, building toward the
full Picard contraction theorem.

## 2026-05-23 refactor: drop bundled `h_lin` hypothesis

The previous version of `picardStep_jump_diff_lipschitz_sq_componentwise`
took a bundled linearity hypothesis `h_lin` asserting that the
difference of two `Compensated.stochasticIntegral` outputs equals the
single integral of the difference. This was a precondition because the
integral is defined via `Classical.choose` on the unified-existence
axiom (Tier 1 #6), so each integrand gets an independent existence
witness and the "difference of choices" and "choice of difference"
are not syntactically equal. The bundled hypothesis was the path of
least resistance for the initial Picard-framework commits.

With Tier 1 #18 (`itoIsometry_diff_compensated`, per the 2026-05-27
3rd-audit renumbering — historically called #14) now stating the
per-difference isometry as a first-class axiom, the bundled
`h_lin` hypothesis (and the `hDiff_meas`, `hDiff_progMeas`,
`hDiff_sq` measurability/integrability hypotheses that only fed into
it) are no longer needed. The refactored lemma has **four fewer**
hypotheses, and the proof body forwards directly through the new
axiom in a single `exact ... .trans (lintegral_mono ...)` chain.
This mirrors the `itoIsometry_diff_brownian` axiom + simplified
σ-side proof in `PicardSigmaLipschitz.lean`.
-/

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

**Proof**: forwards directly through the per-difference L²-isometry
axiom `LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated`
(Tier 1 #18), then applies the γ-Lipschitz hypothesis pointwise and
extracts the constant via `lintegral_const_mul`.

**2026-05-23 refactor**: previously took a bundled linearity hypothesis
`h_lin` plus `hDiff_meas`/`hDiff_progMeas`/`hDiff_sq` measurability /
integrability hypotheses for the difference integrand (four extra
preconditions). Replaced with a forward through Tier 1 axiom #18; the
four hypotheses are gone. -/
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
      ∫⁻ e, (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν
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
  -- `inner double lintegral ≤ ENNReal.ofReal L_γ² · ∫⁻ ω ∫⁻ s, ‖X-Y‖² ∂volume ∂P`.
  -- `picardStep_jump i` unfolds definitionally to the `Compensated.stochasticIntegral`
  -- of `γ ... i`, so the rewrite goes through `show`+`exact_mod_cast`.
  simp only [picardStep_jump] at *
  rw [h_iso]
  -- Goal now:
  -- ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖γ(s, X_s, e) i − γ(s, Y_s, e) i‖² ν⊗ds ∂P
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
            ∫⁻ s in Set.Icc (0 : ℝ) T, (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        refine lintegral_congr fun ω => ?_
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (L_γ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end LevyStochCalc.Ito.Picard
