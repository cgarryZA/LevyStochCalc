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

1. Apply the Itô-Lévy isometry
   (`LevyStochCalc.Poisson.Compensated.itoLevyIsometry`) to the **difference
   integrand** `(s, e, ω) ↦ γ(s, X_s, e) i − γ(s, Y_s, e) i`:
   `𝔼[(∫∫ φ Ñ)²] = 𝔼[∫∫ |φ|² ν⊗ds]`.

2. Use the linearity hypothesis (`h_lin`, bundled with the lemma — this is
   the operator-level linearity of `Compensated.stochasticIntegral`, which
   is provable for predictable L² integrands by the standard L²-completion
   construction; for now we accept it as a precondition mirroring how the
   drift-side bundles its `IntegrableOn` preconditions for `integral_sub`).
   With this, the L² norm of the difference of the two component integrals
   equals the L² norm of the integral of the difference, which is bounded
   by the inner double integral of the squared difference.

3. Apply the Lipschitz hypothesis on γ to bound the inner ν-integral by
   `ENNReal.ofReal (L_γ²) · ‖X − Y‖²` pointwise in `(s, ω)`.

4. Monotonicity of `∫⁻` and `lintegral_const_mul` extract the constant
   `ENNReal.ofReal (L_γ²)`.

This is the per-component-i, integrated-over-ω L²-Lipschitz bound.
The corresponding sum-over-`i ∈ Fin n` and time-horizon-T forms follow
by `Finset.sum_le_sum` and `lintegral_mono`, building toward the
full Picard contraction theorem.
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
* the **linearity** identity for the L² compensated-Poisson integral on
  the per-component difference integrand (`h_lin` — see proof outline
  in the file docstring for why this is bundled as a hypothesis),
* together with the joint measurability / progressive measurability /
  L²-boundedness hypothesis bundles that `picardStep_jump` requires for
  `X`, `Y`, AND their difference `(s, ω, e) ↦ γ(s, X_s, e) i − γ(s, Y_s, e) i`,

the per-(t = T) L²-norm of the difference of jump-step components is
bounded by `L_γ²` times the time-integrated squared L² distance:

  `∫⁻ ω, ‖(picardStep_jump X)_i T ω − (picardStep_jump Y)_i T ω‖² ∂P
    ≤ ENNReal.ofReal L_γ² · ∫⁻ ω, ∫⁻ s ∈ [0, T], ‖X_s ω − Y_s ω‖² ds ∂P`.

This is the operator-level per-component bound that, when summed over
`i ∈ Fin n` and combined with the Bielecki time-weight, yields the
γ-Lipschitz term in the Bielecki β-norm contraction estimate. -/
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
    -- Hypothesis bundles — difference (γ_X − γ_Y) i:
    (hDiff_meas : Measurable (fun (p : Ω × ℝ × E) =>
      coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i - coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hDiff_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E =>
          coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i - coeffs.γ p.2.1 (Y p.2.1 p.1) p.2.2 i))
    (hDiff_sq : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i - coeffs.γ s (Y s ω) e i‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T)
    -- **Linearity hypothesis**: the difference of jump-step components at
    -- coordinate `i` equals the L² Itô-Lévy integral of the difference of the
    -- coefficient slices.  This is the operator-level linearity of
    -- `Compensated.stochasticIntegral`; it is bundled as a precondition
    -- (mirroring `integral_sub` preconditions in the drift-side lemmas)
    -- because the integral is defined via `Classical.choose` on an
    -- existential, hence syntactic equality of "difference of choices = choice
    -- of difference" requires either an explicit witness or an axiom upgrade,
    -- both deferred to the Picard contraction integration step. Stated for the
    -- specific T at which the L²-norm is taken below.
    (h_lin : ∀ ω : Ω,
      picardStep_jump (E := E) N coeffs X hX_meas hX_progMeas hX_sq T ω i
          - picardStep_jump N coeffs Y hY_meas hY_progMeas hY_sq T ω i
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral N
            (fun ω' s e => coeffs.γ s (X s ω') e i - coeffs.γ s (Y s ω') e i)
            hDiff_meas hDiff_progMeas hDiff_sq T ω) :
    ∫⁻ ω, (‖picardStep_jump (E := E) N coeffs X hX_meas hX_progMeas hX_sq T ω i
            - picardStep_jump N coeffs Y hY_meas hY_progMeas hY_sq T ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (L_γ ^ 2) *
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖X s ω - Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Step 1: rewrite the LHS using the linearity hypothesis h_lin.
  have h_LHS_eq : ∫⁻ ω, (‖picardStep_jump (E := E) N coeffs X hX_meas hX_progMeas hX_sq T ω i
            - picardStep_jump N coeffs Y hY_meas hY_progMeas hY_sq T ω i‖₊
          : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N
              (fun ω' s e => coeffs.γ s (X s ω') e i - coeffs.γ s (Y s ω') e i)
              hDiff_meas hDiff_progMeas hDiff_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [h_lin ω]
  rw [h_LHS_eq]
  -- Step 2: apply the Itô-Lévy isometry to the difference integrand.
  have h_iso := LevyStochCalc.Poisson.Compensated.itoLevyIsometry N
    (fun ω' s e => coeffs.γ s (X s ω') e i - coeffs.γ s (Y s ω') e i)
    hDiff_meas hDiff_progMeas hDiff_sq T hT
  rw [h_iso]
  -- Goal:
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
