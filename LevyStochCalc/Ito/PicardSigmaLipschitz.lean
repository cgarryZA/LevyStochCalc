/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Picard

/-!
# L² Lipschitz bound for the diffusion (σ) component of the Picard map

This file completes the **σ-side Lipschitz analysis** for the Picard
iteration framework: given Lipschitz hypothesis `∑ᵢⱼ (σ(s, x₁) i j -
σ(s, x₂) i j)² ≤ L_σ² ‖x₁ - x₂‖²`, the row-`i` diffusion difference
satisfies the L² bound

  `𝔼 ‖(Φ_diff X) i - (Φ_diff Y) i‖² ≤ d · L_σ² · 𝔼 ∫_0^T ‖X_s - Y_s‖² ds`

where `Φ_diff X t ω := ∑_{j=1}^d ∫_0^t σ(s, X_s) i j dW^j_s` is the
row-`i` multidim Brownian Itô integral.

The proof chains:

1. **Componentwise sum expansion**: `(Φ_diff X) i = ∑_j ∫ σ(X)_{ij} dW^j`.
2. **Cauchy-Schwarz on the j-sum**: `(∑_j a_j)² ≤ d · ∑_j a_j²`.
3. **Per-component L² isometry of the difference** (Tier 1 axiom #11 below):
   `𝔼 |∫ H₁ dW - ∫ H₂ dW|² = 𝔼 ∫ |H₁ - H₂|² ds`.
4. **Lipschitz hypothesis pointwise**: `∑ⱼ (σ(X)ᵢⱼ - σ(Y)ᵢⱼ)² ≤ L_σ² ‖X-Y‖²`.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009,
  §6.2 Theorem 6.2.9 (Picard contraction proof for jump-diffusion SDE).
* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer
  1991, §5.2 (Picard iteration for continuous SDEs).

## Tier 1 axiom added in this file

* `Brownian.Ito.itoIsometry_diff_brownian` (#11): For two predictable
  square-integrable integrands `H₁, H₂`, the L²-norm of the difference
  of their Itô integrals equals the L²-norm of the integrand difference.
  Standard consequence of L²-linearity + isometry of the Itô integral
  (Karatzas-Shreve §3.2 proof of Theorem 3.2.6 — the L²-Itô integral is
  a continuous linear isometry from L²(Ω × [0,T]) to L²(Ω)). Pure axiom
  here because the current `stochasticIntegral` is defined via
  `Classical.choose` on the unified-existence axiom, which does not
  expose linearity directly. Tracked in `tools/cited_axioms.md`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **CITED AXIOM (Tier 1 #11): L²-isometry for the *difference* of two
Brownian Itô integrals.**

For two progressively-measurable, L²-bounded integrands `H₁, H₂`, the
difference `M¹_T - M²_T := ∫_0^T H₁ dW - ∫_0^T H₂ dW` satisfies the
L²-isometry against the *integrand difference*:

  `𝔼 |M¹_T - M²_T|² = 𝔼 ∫_0^T |H₁(s) - H₂(s)|² ds`.

This is a standard consequence of L²-linearity + isometry of the Itô
integral. In the present axiomatization, `stochasticIntegral W H` is
constructed via `Classical.choose` on
`itoIsometry_brownian_unified_existence` (Tier 1 #5), which does not
expose linearity directly. We therefore state this difference-form
isometry as a separate axiom.

**Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*,
Springer 1991, **Theorem 3.2.6** + the unique-extension lemma for the
L²-Itô integral as a continuous linear isometry from `L²(Ω × [0, T])`
to `L²(Ω)` (Karatzas-Shreve §3.2.B, eq. (2.20) and following).

**Replacement plan**: derive as a theorem from a Mathlib-level linearity
result on the L²-Itô integral when that machinery becomes available.
Tracked in `tools/cited_axioms.md` Tier 1 #11. -/
axiom itoIsometry_diff_brownian
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
    (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral W H₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T ω
              - stochasticIntegral W H₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T ω‖₊
            : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P

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
  -- Step 4: apply isometry on each j.  ∫⁻ ‖Mx j - My j‖² = ∫⁻ ∫⁻ ‖σ(X) - σ(Y)‖².
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
  -- Step 5: swap ∑_j and ∫⁻ ∫⁻ on the bound.  ∑_j ∫⁻ ω ∫⁻ s f_j = ∫⁻ ω ∫⁻ s ∑_j f_j.
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
      ≤ (d : ℝ≥0∞) * ∑ j : Fin d, ∫⁻ ω, (‖Mx j ω - My j ω‖₊ : ℝ≥0∞) ^ 2 ∂P := h_cs
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
