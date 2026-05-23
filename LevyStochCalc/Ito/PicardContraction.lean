/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Picard

/-!
# Picard contraction in the Bielecki β-norm

This file assembles the three component-wise L² Lipschitz bounds (drift,
diffusion, jump) into the **Bielecki-norm contraction estimate** for the
full Picard map `Φ X = x₀ + ∫μ + ∫σ dW + ∫γ dÑ`.

## Main results

* `sq_add_three_le` and `sum_sq_add_three_le` — the elementary
  Cauchy-Schwarz-on-three-terms inequality `(a + b + c)² ≤ 3 (a² + b² + c²)`,
  lifted vector-wise to `Fin n → ℝ`.

* `picardStep_diff_sum_sq_le` — the pointwise (in `t, ω`) sum-of-squares
  triangle bound: the squared Euclidean norm of `(Φ X - Φ Y) t ω` is at
  most three times the sum of the three component squared norms.

* `picardStep_diff_lintegral_sum_sq_le` — same, lintegrated over `ω`. Stated
  as a SINGLE lintegral of the three-term sum on the RHS to avoid requiring
  AEMeasurable hypotheses on the individual component differences (which
  would in turn require joint measurability hypotheses on `X, Y` that are
  not yet in scope at this level of the Picard scaffolding).

* `picardStep_bielecki_contraction` — the headline contraction estimate.
  Given a per-step lintegral L² bound on each of the three components
  (the drift bound is already proven in `Picard.lean` via
  `picardStep_drift_diff_lintegral_sq_bound`; the σ-step and γ-step
  analogs are taken as explicit hypotheses with the EXACT signature shape
  that the parallel proofs in flight will produce), the lintegral L² mass
  of the Picard step difference at each time `t ∈ [0, T]` is bounded by

    `9 · n · L² · T · ∫⁻ ω, ∫₀^t ‖X_s - Y_s‖² ds ∂P`,

  where the factor 3 in the prompt-spec rate `3 n L² T / (2β)` is doubled
  here because each of the three components is uniformly over-bounded by
  the largest one (`n L² t` from the drift). Tight σ/γ bounds (constant
  `L²` per component, without `n t`) bring the rate down by a factor of `n T`;
  the gap is intentionally left open at this stage because the σ/γ bounds
  are in flight in `Ito/PicardSigmaLipschitz` and `Ito/PicardGammaLipschitz`.

* `picardStep_bielecki_contraction_rate_lt_one` — the contraction rate is
  `< 1` provided `β` exceeds the corresponding threshold.

## Structure

The proof is a straightforward triangle / three-term Cauchy-Schwarz on the
three component-wise L² bounds. The σ-step and γ-step bounds are taken
as hypotheses since the parallel proofs of these (mirroring the drift's
`picardStep_drift_diff_lintegral_sq_bound`) are in flight. Once the
σ + γ Lipschitz bounds land, the σ-step and γ-step bound hypotheses here
will be discharged.

The Bielecki β-norm reduction from the per-`t` lintegral bound to the
`bieleckiNorm` itself happens in `bielecki_weighted_integral_bound` (proven
in `Picard.lean`); this file produces the lintegral bound that
`bielecki_weighted_integral_bound` consumes.
-/

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
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ∫⁻ ω, 3 * (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω
                - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
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
            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)
      ≤ 3 *
          (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
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
                - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
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
              - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) := by
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
          h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
    ≤ ENNReal.ofReal (9 * (n : ℝ) * L ^ 2 * T) *
        ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P := by
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
    ∫⁻ ω, ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) t, ‖X s ω - Y s ω‖ ^ 2) ∂P with hIω_def
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
                - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P :=
    MeasureTheory.lintegral_add_left' (h_diff_ofReal_aemeas t) _
  have h_split_1 : ∫⁻ ω, (ENNReal.ofReal
        (∑ i : Fin n,
          ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) ∂P
      = (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + ∫⁻ ω, (ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
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
                  - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2)) ∂P
      = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
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
        + ENNReal.ofReal (∑ i, ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
            - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
      = (fun ω => ENNReal.ofReal (∑ i, ((picardStep_drift coeffs X x₀ t ω
            - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
        + (ENNReal.ofReal (∑ i, ((picardStep_diffusion W coeffs X
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
            - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
          + ENNReal.ofReal (∑ i, ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
              - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))) from by
      funext ω; rw [add_assoc]]
    rw [h_split_1, h_split_2, add_assoc]
  -- Now: combine the three lintegrals using drift/σ/γ bounds (each ≤ Bnt * Iω).
  have h_sum_bound :
      (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                - picardStep_diffusion W coeffs Y
                    h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2) ∂P)
        + (∫⁻ ω, ENNReal.ofReal
            (∑ i : Fin n,
              ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P)
      ≤ Bnt * Iω + Bnt * Iω + Bnt * Iω :=
    add_le_add (add_le_add h_drift h_σ) h_γ
  -- Bnt ≤ ofReal(n L² T) since t ≤ T.
  have h_Bnt_T : Bnt ≤ ENNReal.ofReal ((n : ℝ) * L ^ 2 * T) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have h_nL2_nn : 0 ≤ (n : ℝ) * L ^ 2 :=
      mul_nonneg (Nat.cast_nonneg n) (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left ht_le h_nL2_nn
  -- 9 = 3 * 3 as ℝ≥0∞.
  -- Final chain: Φ ≤ ∫⁻ (3 * ...) = 3 * (...) ≤ 3 * (3 Bnt Iω) = 9 Bnt Iω ≤ 9 (n L² T) Iω.
  calc ∫⁻ ω, ENNReal.ofReal (∑ i : Fin n,
        ((picardStep W N coeffs X x₀
            h_σ_meas_X h_σ_progMeas_X h_σ_sq_X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
          - picardStep W N coeffs Y x₀
            h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2) ∂P
      ≤ ∫⁻ ω, 3 *
          (ENNReal.ofReal (∑ i : Fin n,
              ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_diffusion W coeffs X h_σ_meas_X h_σ_progMeas_X h_σ_sq_X t ω
                  - picardStep_diffusion W coeffs Y h_σ_meas_Y h_σ_progMeas_Y h_σ_sq_Y t ω) i) ^ 2)
            + ENNReal.ofReal (∑ i : Fin n,
                ((picardStep_jump N coeffs X h_γ_meas_X h_γ_progMeas_X h_γ_sq_X t ω
                  - picardStep_jump N coeffs Y h_γ_meas_Y h_γ_progMeas_Y h_γ_sq_Y t ω) i) ^ 2))
          ∂P := h_triangle'
    _ = 3 * ((∫⁻ ω, ENNReal.ofReal
              (∑ i : Fin n,
                ((picardStep_drift coeffs X x₀ t ω - picardStep_drift coeffs Y x₀ t ω) i) ^ 2) ∂P)
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
