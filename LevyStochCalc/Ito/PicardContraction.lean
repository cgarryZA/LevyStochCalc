/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardOutput
import LevyStochCalc.Ito.PicardLimit

/-!
# The Picard self-map is a Bielecki contraction

The contraction estimate of `bieleckiNorm_picardStep_diff_le` is stated for the Picard step along
two raw path maps. Along two processes of the space its hypotheses are supplied by the frozen
integrand lemmas, and the Bielecki norm of a difference is unchanged by freezing at the horizon,
so the estimate transfers to `picardStepOnStop` and from there, through the modification
`picardSelfMap_ae_eq`, to `picardSelfMap` itself.

## Main statements

* `bieleckiNorm_picardStepOnStop_diff_le` — the estimate for the step along frozen processes.
* `bieleckiNorm_picardSelfMap_diff_le` — the estimate for the self-map.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ} {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-! ### The difference of two frozen processes -/

/-- The squared norm of a difference is at most twice the sum of the squared norms. -/
theorem sq_nnnorm_sub_le {α : Type*} [SeminormedAddCommGroup α] (a b : α) :
    (‖a - b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    have h := norm_sub_le a b
    nlinarith [norm_nonneg a, norm_nonneg b, norm_nonneg (a - b), sq_nonneg (‖a‖ - ‖b‖)]
  calc (‖a - b‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖a - b‖ ^ 2) := sq_coe_nnnorm _
    _ ≤ ENNReal.ofReal (2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2) := ENNReal.ofReal_le_ofReal hreal
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), sq_coe_nnnorm, sq_coe_nnnorm,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
        norm_num

/-- The difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Y.stop.X s ω) :=
  (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
    (Y.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst))

/-- The norm of the difference of two frozen processes is jointly measurable. -/
theorem measurable_uncurry_stop_sub_norm (X Y : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ‖X.stop.X s ω - Y.stop.X s ω‖) :=
  (measurable_uncurry_stop_sub X Y).norm

/-- The `ω`-slice of the squared norms of a frozen process is measurable in time. -/
theorem measurable_sq_stop_slice (X : SBoundedProcess (n := n) P ℱ T) (ω : Ω) :
    Measurable fun s : ℝ => ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (X.stop.measurable_path.comp (measurable_id.prodMk measurable_const))).nnnorm)).pow_const 2

/-- The squared norms of a frozen process are jointly measurable. -/
theorem measurable_uncurry_sq_stop (X : SBoundedProcess (n := n) P ℱ T) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2) :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (X.stop.measurable_path.comp
          (measurable_snd.prodMk measurable_fst))).nnnorm)).pow_const 2

/-- The energy of a frozen process over a window is measurable in the sample point. -/
theorem measurable_lintegral_sq_stop (X : SBoundedProcess (n := n) P ℱ T) (b : ℝ) :
    Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
  (measurable_uncurry_sq_stop X).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) b))

/-- The energy of the difference of two frozen processes is finite on every window. -/
theorem lintegral_sq_stop_sub_lt_top (X Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖X.stop.X s ω - Y.stop.X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω : Ω, ∀ s : ℝ, (‖X.stop.X s ω - Y.stop.X s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2
        + 2 * ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    refine (sq_nnnorm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (2 * ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2
          + 2 * ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = 2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    have hA : Measurable fun s : ℝ => 2 * ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 :=
      (measurable_sq_stop_slice X ω).const_mul 2
    rw [lintegral_add_left hA, lintegral_const_mul _ (measurable_sq_stop_slice X ω),
      lintegral_const_mul _ (measurable_sq_stop_slice Y ω)]
  have houter : Measurable fun ω : Ω =>
      2 * ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (measurable_lintegral_sq_stop X b).const_mul 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖X.stop.X s ω - Y.stop.X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
          (2 * ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2
            + 2 * ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := by
        exact lintegral_congr fun ω => hinner ω
    _ = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Y.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [lintegral_add_left houter, lintegral_const_mul _ (measurable_lintegral_sq_stop X b),
          lintegral_const_mul _ (measurable_lintegral_sq_stop Y b)]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) ?_,
          ENNReal.mul_lt_top (by norm_num) ?_⟩
        · exact lt_of_le_of_lt (lintegral_lintegral_sq_stop_le X hT b)
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2))
        · exact lt_of_le_of_lt (lintegral_lintegral_sq_stop_le Y hT b)
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))

/-- Freezing at the horizon does not change the Bielecki norm of a difference. -/
theorem bieleckiNorm_stop_sub (β : ℝ) (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.stop.X t ω i - Y.stop.X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) :=
  bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Y.X t ω i

/-! ### The contraction estimate for the step and the self-map -/

/-- **The Picard step along frozen processes is a Bielecki contraction**, with the rate of
`bieleckiNorm_picardStep_diff_le`. -/
theorem bieleckiNorm_picardStepOnStop_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  rw [← bieleckiNorm_stop_sub β X Y]
  exact bieleckiNorm_picardStep_diff_le W N ℱ hℱW hℱN coeffs hLip X.stop.X Y.stop.X x₀
    (fun i j => measurable_sigma_stop coeffs hReg X i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg X i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (fun i j => measurable_sigma_stop coeffs hReg Y i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg Y i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip Y hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg Y i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg Y i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip Y hT.le i hT')
    (fun i => measurable_mu_stop coeffs hReg X i)
    (fun i => measurable_mu_stop coeffs hReg Y i)
    (measurable_uncurry_stop_sub_norm X Y)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip Y hT.le i hb)
    (fun b _ => lintegral_sq_stop_sub_lt_top X Y hT.le b)
    (measurable_uncurry_stop_sub X Y) hβ hT

/-- **The Picard self-map is a Bielecki contraction.** The self-map is a modification of the step
along the frozen process, and the Bielecki norm is unchanged under modification. -/
theorem bieleckiNorm_picardSelfMap_diff_le
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)
    {L : ℝ} (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) := by
  have hcongr : bieleckiNorm (P := P) β T (fun t ω i =>
        (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X).X t ω i
          - (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y).X t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnStop W N hℱW hℱN coeffs hReg hLip Y hT.le x₀ t ω i) := by
    refine bieleckiNorm_congr_ae (P := P) β T fun t => ?_
    filter_upwards [picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X t,
      picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT Y t] with ω hX hY
    funext i
    rw [hX, hY]
  rw [hcongr]
  exact bieleckiNorm_picardStepOnStop_diff_le W N hℱW hℱN coeffs hReg hLip x₀ hβ hT X Y

end LevyStochCalc.Ito.Picard
