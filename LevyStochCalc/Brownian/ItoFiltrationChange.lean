/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoAlgebra
import LevyStochCalc.Brownian.ItoDriverLinear
import LevyStochCalc.Brownian.AugmentedFiltration
import LevyStochCalc.Poisson.Compensated
import LevyStochCalc.Poisson.PredictableRepresentation

/-!
# The stochastic integrals under a change of filtration

The `L²` Brownian Itô integral and the `L²` Itô–Lévy integral against a compensated Poisson
random measure are each assembled from an approximating sequence of elementary integrands
selected relative to a filtration, so one integrand integrated against one driver over two
filtrations gives two constructions. The elementary integral of such an approximant mentions no
filtration, and the `L²` distance between two elementary integrals, or between an elementary
integral and the limit, is the energy of the difference of the integrands; both constructions
are therefore the `L²`-limit of a single sequence, and they agree almost everywhere. Passing to
the augmented filtration is the case of interest, since that filtration satisfies the usual
conditions.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_filtration` — the Brownian
  integral over `ℱ` agrees almost everywhere with the integral over a larger filtration.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_augFiltration` — the Brownian integral
  over `ℱ` agrees almost everywhere with the integral over `augFiltration ℱ P`.
* `LevyStochCalc.Poisson.Compensated.process_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_filtration`,
  `LevyStochCalc.Poisson.Compensated.stochasticIntegral_augFiltration` — the same three
  statements for the compensated Poisson integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The `L²` Brownian Itô integral of a progressively measurable integrand is almost everywhere
unchanged when the filtration is enlarged to one for which the driver is still Brownian. -/
theorem stochasticIntegralBrownian_congr_filtration
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) (h𝒢 : IsBrownianFiltration W 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hp' : Probability.ProgressivelyMeasurable 𝒢 H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H hm hp hq T
      =ᵐ[P] stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T := by
  rcases le_or_gt T 0 with hT | hT
  · exact (stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H hm hp hq hT).trans
      (stochasticIntegralBrownian_ae_zero_of_nonpos W 𝒢 h𝒢 H hm hp' hq hT).symm
  have hSm : ∀ n : ℕ,
      AEStronglyMeasurable (simpleIntegral W (masterApprox ℱ H hm hp hq n) T) P := by
    intro n
    refine (Finset.measurable_sum _ fun k _ => ?_).aestronglyMeasurable
    exact ((masterApprox ℱ H hm hp hq n).ξ_measurable k).mul
      ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIf : AEStronglyMeasurable (stochasticIntegralBrownian W ℱ hℱ H hm hp hq T) P :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq T).mono
      (ℱ.le T)).aestronglyMeasurable
  have hIg : AEStronglyMeasurable (stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T) P :=
    ((stochasticIntegralBrownian_stronglyAdapted W 𝒢 h𝒢 H hm hp' hq T).mono
      (𝒢.le T)).aestronglyMeasurable
  have hFf := masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq hT.le
  have hiso : ∀ n : ℕ,
      eLpNorm (fun ω => simpleIntegral W (masterApprox ℱ H hm hp hq n) T ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P
        = eLpNorm (fun ω => simpleIntegral W (masterApprox ℱ H hm hp hq n) T ω
          - stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T ω) 2 P := by
    intro n
    have h1 : ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H hm hp hq n) T ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ H hm hp hq n) T ω
          - stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      rw [isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (masterApprox ℱ H hm hp hq n)
          (masterApprox_adapt ℱ H hm hp hq n) H hm hp hq hT,
        isometry_simple_sub_stochasticIntegralBrownian W 𝒢 h𝒢 (masterApprox ℱ H hm hp hq n)
          (fun i => (masterApprox_adapt ℱ H hm hp hq n i).mono (hle _)) H hm hp' hq hT]
    have hsq : eLpNorm (fun ω => simpleIntegral W (masterApprox ℱ H hm hp hq n) T ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P ^ (2 : ℝ)
        = eLpNorm (fun ω => simpleIntegral W (masterApprox ℱ H hm hp hq n) T ω
          - stochasticIntegralBrownian W 𝒢 h𝒢 H hm hp' hq T ω) 2 P ^ (2 : ℝ) := by
      rw [eLpNorm_two_rpow_eq_lintegral_sq, eLpNorm_two_rpow_eq_lintegral_sq]
      exact h1
    exact ENNReal.rpow_left_injective (by norm_num : (2 : ℝ) ≠ 0) hsq
  exact ae_eq_of_tendsto_eLpNorm hSm hIf hIg hFf (hFf.congr hiso)

/-- The `L²` Brownian Itô integral agrees almost everywhere with the integral taken over the
filtration augmented by the null sets and frozen before time zero. -/
theorem stochasticIntegralBrownian_augFiltration
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hp' : Probability.ProgressivelyMeasurable (augFiltration ℱ P) H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ H hm hp hq T
      =ᵐ[P] stochasticIntegralBrownian W (augFiltration ℱ P)
        (isBrownianFiltration_augFiltration hℱ) H hm hp' hq T :=
  stochasticIntegralBrownian_congr_filtration W ℱ (augFiltration ℱ P) hℱ
    (isBrownianFiltration_augFiltration hℱ) (le_augFiltration ℱ P) H hm hp hp' hq T

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Poisson.Compensated

open MeasureTheory
open scoped NNReal ENNReal

universe v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- Marked progressive measurability transfers along an inclusion of filtrations. -/
theorem markedProgressivelyMeasurable_mono {ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›}
    {φ : Ω → ℝ → E → ℝ} (h : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) : Probability.MarkedProgressivelyMeasurable 𝒢 φ := fun t =>
  (h t).mono (sup_le_sup (MeasurableSpace.comap_mono (hle t)) le_rfl)

/-- Adaptedness of a mark-step integrand transfers along an inclusion of filtrations. -/
theorem MarkStep.Adapted.mono_filtration {g : TimeGrid}
    {ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›} {G : MarkStep Ω E ν g}
    (hG : G.Adapted ℱ) (hle : ∀ t, ℱ t ≤ 𝒢 t) : G.Adapted 𝒢 :=
  fun i hi k => (hG i hi k).mono (hle _)

/-- The stage tolerances `((n : ℝ≥0∞) + 1)⁻¹` tend to zero. -/
theorem tendsto_natCast_add_one_inv :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
  refine h.congr (fun n => ?_)
  simp [Nat.cast_add_one]

/-- The `L²` integral process against the compensated Poisson measure is almost everywhere
unchanged when the filtration is enlarged to one for which the measure is still Poisson. -/
theorem process_congr_filtration
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (h𝒢 : IsPoissonFiltration N 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hp' : Probability.MarkedProgressivelyMeasurable 𝒢 φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) :
    process N ℱ hℱ φ hm hp hq T =ᵐ[P] process N 𝒢 h𝒢 φ hm hp' hq T := by
  rcases le_or_gt T 0 with hT | hT
  · exact (process_ae_zero_of_nonpos N ℱ hℱ φ hm hp hq hT).trans
      (process_ae_zero_of_nonpos N 𝒢 h𝒢 φ hm hp' hq hT).symm
  have hbd : ∀ n : ℕ, T ≤ stageHorizon n →
      ∫⁻ ω, (‖stageIntegral N ℱ hℱ φ hm hp hq n T ω
          - stageIntegral N 𝒢 h𝒢 φ hm hp' hq n T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n hTn
    have hmax1 : (master N ℱ hℱ φ hm hp hq n).1
        ≤ max (master N ℱ hℱ φ hm hp hq n).1 (master N 𝒢 h𝒢 φ hm hp' hq n).1 := le_max_left _ _
    have hmax2 : (master N 𝒢 h𝒢 φ hm hp' hq n).1
        ≤ max (master N ℱ hℱ φ hm hp hq n).1 (master N 𝒢 h𝒢 φ hm hp' hq n).1 := le_max_right _ _
    set G := (master N ℱ hℱ φ hm hp hq n).2 with hGdef
    set G' := (master N 𝒢 h𝒢 φ hm hp' hq n).2 with hG'def
    have hG : G.Adapted 𝒢 :=
      (master_adapted N ℱ hℱ φ hm hp hq n).mono_filtration hle
    have hG' : G'.Adapted 𝒢 := master_adapted N 𝒢 h𝒢 φ hm hp' hq n
    have hRf : (G.dyadicRefine hmax1).Adapted 𝒢 := hG.dyadicRefine N hmax1
    have hRf' : (G'.dyadicRefine hmax2).Adapted 𝒢 := hG'.dyadicRefine N hmax2
    have e1 : ∀ ω, stageIntegral N ℱ hℱ φ hm hp hq n T ω = G.integral N T ω := fun _ => rfl
    have e2 : ∀ ω, stageIntegral N 𝒢 h𝒢 φ hm hp' hq n T ω = G'.integral N T ω := fun _ => rfl
    have hae : (fun ω => (‖G.integral N T ω - G'.integral N T ω‖₊ : ℝ≥0∞) ^ 2)
        =ᵐ[P] fun ω => (‖(G.dyadicRefine hmax1).integral N T ω
          - (G'.dyadicRefine hmax2).integral N T ω‖₊ : ℝ≥0∞) ^ 2 := by
      filter_upwards [G.integral_dyadicRefine N h𝒢 hmax1 hG T,
        G'.integral_dyadicRefine N h𝒢 hmax2 hG' T] with ω hω hω'
      rw [hω, hω']
    simp_rw [e1, e2]
    rw [lintegral_congr_ae hae,
      (G.dyadicRefine hmax1).lintegral_integral_sub_sq_at N h𝒢 (G'.dyadicRefine hmax2)
        hRf hRf' hT.le]
    have hev : ∀ ω e s, (G.dyadicRefine hmax1).eval s e ω - (G'.dyadicRefine hmax2).eval s e ω
        = G.eval s e ω - G'.eval s e ω := fun ω e s => by
      rw [G.eval_dyadicRefine hmax1, G'.eval_dyadicRefine hmax2]
    have hw : Measurable (fun p : Ω × ℝ × E =>
        (‖G.eval p.2.1 p.2.2 p.1 - G'.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_coe.measurable.comp
        (G.eval_measurable.sub G'.eval_measurable).nnnorm).pow_const 2
    have hu : Measurable (fun p : Ω × ℝ × E =>
        (‖φ p.1 p.2.1 p.2.2 - G.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_coe.measurable.comp (hm.sub G.eval_measurable).nnnorm).pow_const 2
    have hv : Measurable (fun p : Ω × ℝ × E =>
        (‖φ p.1 p.2.1 p.2.2 - G'.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_coe.measurable.comp (hm.sub G'.eval_measurable).nnnorm).pow_const 2
    have hpt : ∀ ω s e, (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
          + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s e
      rw [show G.eval s e ω - G'.eval s e ω
        = -(φ ω s e - G.eval s e ω) + (φ ω s e - G'.eval s e ω) by ring]
      have h2 := sq_nnnorm_add_le_two_mul (-(φ ω s e - G.eval s e ω)) (φ ω s e - G'.eval s e ω)
      rwa [nnnorm_neg] at h2
    have hresG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
      le_trans (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hTn))
        (master_err N ℱ hℱ φ hm hp hq n).le
    have hresG' : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ :=
      le_trans (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hTn))
        (master_err N 𝒢 h𝒢 φ hm hp' hq n).le
    calc ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G.dyadicRefine hmax1).eval s e ω
            - (G'.dyadicRefine hmax2).eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← lintegral_swap_es
            (fun ω s e => (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hw ω]
          refine lintegral_congr fun e => ?_
          refine setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
          rw [hev ω e s]
      _ ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            2 * ((‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2
              + (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2) ∂ν ∂volume ∂P :=
          lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
            + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖φ ω s e - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) := by
          rw [lintegral_triple_const_mul 2 (by norm_num), lintegral_triple_add hu hv]
      _ ≤ 2 * (((n : ℝ≥0∞) + 1)⁻¹ + ((n : ℝ≥0∞) + 1)⁻¹) := by gcongr
      _ = 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n : ℝ≥0∞) + 1)⁻¹ := mul_add _ _ _
  have hHor : ∀ᶠ n : ℕ in Filter.atTop, T ≤ stageHorizon n := by
    have h2 : Filter.Tendsto (fun n : ℕ => (2 : ℝ) ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    exact h2.eventually_ge_atTop T
  have hsq : Filter.Tendsto (fun n : ℕ => ∫⁻ ω,
      (‖stageIntegral N ℱ hℱ φ hm hp hq n T ω
        - stageIntegral N 𝒢 h𝒢 φ hm hp' hq n T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto
        (fun n : ℕ => 2 * ((n : ℝ≥0∞) + 1)⁻¹ + 2 * ((n : ℝ≥0∞) + 1)⁻¹)
        Filter.atTop (nhds 0) := by
      have h1 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) tendsto_natCast_add_one_inv
        (Or.inr (by simp))
      simpa using h1.add h1
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [hHor] with n hn using hbd n hn
  have hcross : Filter.Tendsto (fun n : ℕ => eLpNorm
      (fun ω => stageIntegral N ℱ hℱ φ hm hp hq n T ω
        - stageIntegral N 𝒢 h𝒢 φ hm hp' hq n T ω) 2 P) Filter.atTop (nhds 0) := by
    have h2 : Filter.Tendsto (fun n : ℕ => eLpNorm
        (fun ω => stageIntegral N ℱ hℱ φ hm hp hq n T ω
          - stageIntegral N 𝒢 h𝒢 φ hm hp' hq n T ω) 2 P ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      refine hsq.congr fun n => ?_
      exact (LevyStochCalc.Brownian.Ito.eLpNorm_two_rpow_eq_lintegral_sq _).symm
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr fun n => ?_
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  have hmix : Filter.Tendsto (fun n : ℕ => eLpNorm
      (fun ω => stageIntegral N ℱ hℱ φ hm hp hq n T ω
        - process N 𝒢 h𝒢 φ hm hp' hq T ω) 2 P) Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using hcross.add (stageIntegral_tendsto_process N 𝒢 h𝒢 φ hm hp' hq T))
      (Filter.Eventually.of_forall fun n => bot_le)
      (Filter.Eventually.of_forall fun n => ?_)
    refine le_trans (le_of_eq ?_) (eLpNorm_add_le
      ((memLp_stageIntegral N ℱ hℱ φ hm hp hq n T).sub
        (memLp_stageIntegral N 𝒢 h𝒢 φ hm hp' hq n T)).aestronglyMeasurable
      ((memLp_stageIntegral N 𝒢 h𝒢 φ hm hp' hq n T).sub
        (process_memLp N 𝒢 h𝒢 φ hm hp' hq T)).aestronglyMeasurable (by norm_num))
    refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [Pi.add_apply]
    ring
  exact LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_eLpNorm
    (fun n => (memLp_stageIntegral N ℱ hℱ φ hm hp hq n T).aestronglyMeasurable)
    (process_memLp N ℱ hℱ φ hm hp hq T).aestronglyMeasurable
    (process_memLp N 𝒢 h𝒢 φ hm hp' hq T).aestronglyMeasurable
    (stageIntegral_tendsto_process N ℱ hℱ φ hm hp hq T) hmix

/-- The `L²` Itô–Lévy integral against the compensated Poisson measure is almost everywhere
unchanged when the filtration is enlarged to one for which the measure is still Poisson. -/
theorem stochasticIntegral_congr_filtration
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsPoissonFiltration N ℱ) (h𝒢 : IsPoissonFiltration N 𝒢)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hp' : Probability.MarkedProgressivelyMeasurable 𝒢 φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq T =ᵐ[P] stochasticIntegral N 𝒢 h𝒢 φ hm hp' hq T :=
  ((stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq T).trans
      (process_congr_filtration N ℱ 𝒢 hℱ h𝒢 hle φ hm hp hp' hq T)).trans
    (stochasticIntegral_ae_eq_process N 𝒢 h𝒢 φ hm hp' hq T).symm

/-- The `L²` Itô–Lévy integral against the compensated Poisson measure agrees almost everywhere
with the integral taken over the filtration augmented by the null sets and frozen before time
zero. -/
theorem stochasticIntegral_augFiltration
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hp' : Probability.MarkedProgressivelyMeasurable (Brownian.augFiltration ℱ P) φ)
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq T
      =ᵐ[P] stochasticIntegral N (Brownian.augFiltration ℱ P)
        (isPoissonFiltration_augFiltration hℱ) φ hm hp' hq T :=
  stochasticIntegral_congr_filtration N ℱ (Brownian.augFiltration ℱ P) hℱ
    (isPoissonFiltration_augFiltration hℱ) (Brownian.le_augFiltration ℱ P) φ hm hp hp' hq T

end LevyStochCalc.Poisson.Compensated
