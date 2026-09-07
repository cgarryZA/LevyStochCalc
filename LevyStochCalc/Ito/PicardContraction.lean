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

/-- The `ω`-slice of the squared norms of a path map is measurable in time. -/
theorem measurable_sq_slice_time {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (ω : Ω) :
    Measurable fun s : ℝ => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_id.prodMk measurable_const))).nnnorm)).pow_const 2

/-- The squared norms of a path map are jointly measurable. -/
theorem measurable_uncurry_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2) :=
  Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp
      (((measurable_pi_apply i).comp
        (hZm.comp (measurable_snd.prodMk measurable_fst))).nnnorm)).pow_const 2

/-- The energy of a path map over a window is measurable in the sample point. -/
theorem measurable_lintegral_sq {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (b : ℝ) :
    Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
  (measurable_uncurry_sq hZm).lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) b))

/-- The energy of the difference of two path maps of finite energy is finite. -/
theorem lintegral_sq_sub_lt_top_of_energy {Z₁ Z₂ : ℝ → Ω → (Fin n → ℝ)}
    (hm₁ : Measurable (Function.uncurry Z₁)) (hm₂ : Measurable (Function.uncurry Z₂))
    (h₁ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h₂ : ∀ b : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω : Ω, ∀ s : ℝ, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    refine (sq_nnnorm_sub_le _ _).trans (add_le_add ?_ ?_)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
    · exact mul_le_mul' le_rfl (by rw [sq_coe_nnnorm]; exact ofReal_sq_norm_le_sum _)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume
      = 2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [lintegral_add_left ((measurable_sq_slice_time hm₁ ω).const_mul 2),
      lintegral_const_mul _ (measurable_sq_slice_time hm₁ ω),
      lintegral_const_mul _ (measurable_sq_slice_time hm₂ ω)]
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b, (‖Z₁ s ω - Z₂ s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
          (2 * ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2
            + 2 * ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
    _ = ∫⁻ ω, (2 * (∫⁻ s in Set.Icc (0 : ℝ) b, ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + 2 * ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := lintegral_congr fun ω => hinner ω
    _ = 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
              ∑ i, (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [lintegral_add_left ((measurable_lintegral_sq hm₁ b).const_mul 2),
          lintegral_const_mul _ (measurable_lintegral_sq hm₁ b),
          lintegral_const_mul _ (measurable_lintegral_sq hm₂ b)]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (h₁ b),
        ENNReal.mul_lt_top (by norm_num) (h₂ b)⟩

/-- The energy of the difference of two frozen processes is finite on every window. -/
theorem lintegral_sq_stop_sub_lt_top (X Y : SBoundedProcess (n := n) P ℱ T) (hT : 0 ≤ T)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
        (‖X.stop.X s ω - Y.stop.X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lintegral_sq_sub_lt_top_of_energy X.stop.measurable_path Y.stop.measurable_path
    (fun c => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le X hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2)))
    (fun c => lt_of_le_of_lt (lintegral_lintegral_sq_stop_le Y hT c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top Y.sup_L2))) b

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

/-! ### The Picard iterates and their limit -/

/-- A positive Bielecki weight only shrinks the norm on `[0, T]`. -/
theorem bieleckiNorm_le_bieleckiNorm_zero {β : ℝ} (hβ : 0 ≤ β) (T : ℝ)
    (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T Z ≤ bieleckiNorm (P := P) 0 T Z := by
  refine iSup₂_le fun t ht => ?_
  have hw : ENNReal.ofReal (Real.exp (-β * t)) ≤ ENNReal.ofReal (Real.exp (-0 * t)) := by
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
    have : 0 ≤ β * t := mul_nonneg hβ ht.1
    nlinarith
  exact le_trans (mul_le_mul' hw le_rfl)
    (le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-0 * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht)

variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ' : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) [ℱ'.IsRightContinuous]
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ')
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ')
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
  (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
  (hReg : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular coeffs ν)

/-- **The Picard iterates** of a starting process under the self-map. -/
noncomputable def picardIter {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    ℕ → SBoundedProcess (n := n) P ℱ' T
  | 0 => X₀
  | k + 1 => picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
      (picardIter hLip x₀ hT X₀ k)

/-- The Picard iterates are geometrically Bielecki-Cauchy at the contraction rate. -/
theorem bieleckiNorm_picardIter_step_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k).X t ω i)
      ≤ ((ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)) ^ k
        * bieleckiNorm (P := P) β T (fun t ω i =>
            (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
              - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i) := by
  induction k with
  | zero => simp
  | succ k ih =>
    refine le_trans (bieleckiNorm_picardSelfMap_diff_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
      hLip x₀ hβ hT _ _) ?_
    refine le_trans (mul_le_mul' le_rfl ih) (le_of_eq ?_)
    rw [← mul_assoc, ← pow_succ']

/-! ### The limit of the iterates -/

omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference of two processes of the space is finite. -/
theorem bieleckiNorm_sub_lt_top {β : ℝ} (hβ : 0 ≤ β)
    (X Y : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Y.X t ω i) < ⊤ := by
  have hneg : bieleckiNorm (P := P) 0 T (fun t ω => -(Y.X t ω))
      = bieleckiNorm (P := P) 0 T Y.X := by
    unfold bieleckiNorm
    refine iSup_congr fun t => iSup_congr fun _ => ?_
    congr 2
    exact lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => by simp
  have hEq : (fun t ω i => X.X t ω i - Y.X t ω i)
      = fun t (ω : Ω) => X.X t ω + (fun i => -(Y.X t ω i)) := by
    funext t ω i
    simp [Pi.add_apply, sub_eq_add_neg]
  have hnegm : Measurable (Function.uncurry fun t (ω : Ω) => -(Y.X t ω)) :=
    measurable_neg.comp Y.measurable_path
  have hadd := bieleckiNorm_add_le (P := P) 0 T X.X (fun t ω => -(Y.X t ω))
    (fun t => bieleckiNorm_inner_aemeasurable _ X.measurable_path t)
    (fun t => bieleckiNorm_inner_aemeasurable (fun t ω => -(Y.X t ω)) hnegm t)
  refine lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ T _) ?_
  rw [hEq]
  refine lt_of_le_of_lt hadd ?_
  rw [hneg]
  exact ENNReal.add_lt_top.mpr ⟨X.sup_L2, Y.sup_L2⟩

/-- **The Picard iterates converge in Bielecki norm.** At a weight making the contraction rate
`< 1`, the iterates converge to `bieleckiLimit` at that rate. -/
theorem bieleckiNorm_picardIter_sub_bieleckiLimit_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) (k : ℕ) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k).X t ω i
          - bieleckiLimit
              (fun m => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).X)
              t ω i)
      ≤ ((ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)) ^ k
        * ((1 - (ENNReal.ofReal
              ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
                / (2 * β))) ^ ((1 : ℝ) / 2))⁻¹
            * bieleckiNorm (P := P) β T (fun t ω i =>
                (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
                  - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X
                      t ω i)) :=
  bieleckiNorm_sub_bieleckiLimit_geometric (P := P) β T
    (fun m => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).measurable_path)
    (bieleckiNorm_picardIter_step_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hβ hT X₀)
    hq (bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne k

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg in
/-- Some Bielecki weight makes the contraction rate strictly less than one. -/
theorem exists_bieleckiWeight_rate_lt_one (L : ℝ) (hT : 0 < T) :
    ∃ β : ℝ, 0 < β ∧
      (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2) < 1 := by
  set A : ℝ := 3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2) with hA
  have hAnn : 0 ≤ A := by
    have h1 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 * T := by positivity
    have h2 : (0 : ℝ) ≤ (n : ℝ) * ((d : ℝ) * L ^ 2) := by positivity
    have h3 : (0 : ℝ) ≤ (n : ℝ) * L ^ 2 := by positivity
    rw [hA]; linarith
  refine ⟨A / 2 + 1, by linarith, ?_⟩
  have hden : 0 < 2 * (A / 2 + 1) := by linarith
  have hlt : A / (2 * (A / 2 + 1)) < 1 := by
    rw [div_lt_one hden]; linarith
  refine ENNReal.rpow_lt_one ?_ (by norm_num)
  calc ENNReal.ofReal (A / (2 * (A / 2 + 1))) < ENNReal.ofReal 1 :=
        (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).mpr hlt
    _ = 1 := ENNReal.ofReal_one

/-! ### Bielecki bookkeeping for the fixed point -/

omit [ℱ'.IsRightContinuous] in
/-- Slice measurability suffices for the Bielecki subadditivity hypothesis. -/
theorem bieleckiNorm_inner_aemeasurable_of_slice {Y : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i) (t : ℝ) :
    AEMeasurable (fun ω => (∑ i, (‖Y t ω i‖₊ : ℝ≥0∞) ^ 2) ^ ((1 : ℝ) / 2)) P :=
  ((Finset.measurable_sum _ fun i _ =>
    (ENNReal.continuous_coe.measurable.comp (h t i).nnnorm).pow_const 2).pow_const
      ((1 : ℝ) / 2)).aemeasurable

omit [ℱ'.IsRightContinuous] in
/-- The Bielecki norm of a difference is symmetric. -/
theorem bieleckiNorm_sub_comm (β T : ℝ) (A B : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) β T (fun t ω i => A t ω i - B t ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => B t ω i - A t ω i) := by
  unfold bieleckiNorm
  refine iSup_congr fun t => iSup_congr fun _ => ?_
  congr 2
  refine lintegral_congr fun ω => Finset.sum_congr rfl fun i _ => ?_
  simp only [show A t ω i - B t ω i = -(B t ω i - A t ω i) from by ring, nnnorm_neg]

omit [ℱ'.IsRightContinuous] in
/-- The unweighted Bielecki norm is bounded by the weighted one, at the cost of `e^{βT}`. -/
theorem bieleckiNorm_zero_le_mul {β : ℝ} (hβ : 0 ≤ β) {T : ℝ} (Z : ℝ → Ω → (Fin n → ℝ)) :
    bieleckiNorm (P := P) 0 T Z
      ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z := by
  refine iSup₂_le fun t ht => ?_
  have hle : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      ≤ bieleckiNorm (P := P) β T Z :=
    le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  have hexp : ENNReal.ofReal (Real.exp (β * t)) ≤ ENNReal.ofReal (Real.exp (β * T)) :=
    ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (by nlinarith [ht.2, ht.1]))
  calc ENNReal.ofReal (Real.exp (-0 * t))
        * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)
      = ENNReal.ofReal (Real.exp (β * t)) * (ENNReal.ofReal (Real.exp (-β * t))
          * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
        simp
    _ ≤ ENNReal.ofReal (Real.exp (β * T)) * bieleckiNorm (P := P) β T Z :=
        mul_le_mul' hexp hle

omit [ℱ'.IsRightContinuous] in
/-- A path map at finite Bielecki distance from one of finite Bielecki norm has finite Bielecki
norm. -/
theorem bieleckiNorm_lt_top_of_approx (β T : ℝ) {A Z : ℝ → Ω → (Fin n → ℝ)}
    (hAm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => A t ω i)
    (hZm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Z t ω i)
    (hA : bieleckiNorm (P := P) β T A < ⊤)
    (hd : bieleckiNorm (P := P) β T (fun t ω i => A t ω i - Z t ω i) < ⊤) :
    bieleckiNorm (P := P) β T Z < ⊤ := by
  have hEq : Z = fun t (ω : Ω) => A t ω + fun i => Z t ω i - A t ω i := by
    funext t ω i
    simp [Pi.add_apply]
  have hadd := bieleckiNorm_add_le (P := P) β T A (fun t ω => fun i => Z t ω i - A t ω i)
    (bieleckiNorm_inner_aemeasurable_of_slice hAm)
    (bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hZm t i).sub (hAm t i))
  rw [hEq]
  refine lt_of_le_of_lt hadd (ENNReal.add_lt_top.mpr ⟨hA, ?_⟩)
  rwa [bieleckiNorm_sub_comm (P := P) β T Z A]

/-! ### The step against a raw state process -/

/-- **The Picard step contracts between a process of the space and a raw state process.** -/
theorem bieleckiNorm_picardStepOnStop_sub_rawStop_le {L : ℝ}
    (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤)
    (x₀ : Fin n → ℝ) {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X : SBoundedProcess (n := n) P ℱ' T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnStop W N hℱW hℱN coeffs hReg hLip X hT.le x₀ t ω i
          - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) := by
  have hZsm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z (min s T) ω) :=
    hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have hXe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖X.stop.X s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun c =>
    lt_of_le_of_lt (lintegral_lintegral_sq_stop_le X hT.le c)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top X.sup_L2))
  have hZe : ∀ c : ℝ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) c,
      ∑ i, (‖Z (min s T) ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lintegral_sq_rawStop_lt_top hZm hZb hT.le
  have hdiffm : Measurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) => X.stop.X s ω - Z (min s T) ω) :=
    (X.stop.measurable_path.comp (measurable_snd.prodMk measurable_fst)).sub
      (hZsm.comp (measurable_snd.prodMk measurable_fst))
  have hrhs : bieleckiNorm (P := P) β T
      (fun t ω i => X.stop.X t ω i - Z (min t T) ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => X.X t ω i - Z t ω i) :=
    bieleckiNorm_min (P := P) β T fun t ω i => X.X t ω i - Z t ω i
  rw [← hrhs]
  exact bieleckiNorm_picardStep_diff_le W N ℱ' hℱW hℱN coeffs hLip X.stop.X
    (fun s ω => Z (min s T) ω) x₀
    (fun i j => measurable_sigma_stop coeffs hReg X i j)
    (fun i j => progressivelyMeasurable_sigma_stop coeffs hReg X i j)
    (fun i j _ hT' => lintegral_sq_sigma_stop_lt_top coeffs hReg hLip X hT.le i j hT')
    (fun i => measurable_gamma_stop coeffs hReg X i)
    (fun i => markedProgressivelyMeasurable_gamma_stop coeffs hReg X i)
    (fun i _ hT' => lintegral_sq_gamma_stop_lt_top coeffs hReg hLip X hT.le i hT')
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i j hT')
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i hT')
    (fun i => measurable_mu_stop coeffs hReg X i)
    (measurable_mu_rawStop coeffs hReg hZm T)
    hdiffm.norm
    (fun i b hb => lintegral_sq_mu_stop_lt_top coeffs hReg hLip X hT.le i hb)
    (fun i b hb => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω) hZsm hZe i hb)
    (fun b _ => lintegral_sq_sub_lt_top_of_energy X.stop.measurable_path hZsm hXe hZe b)
    hdiffm hβ hT

/-! ### The fixed point -/

variable {L : ℝ}
  (hLip : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsLipschitz coeffs ν L)
  (x₀ : Fin n → ℝ)

/-- **The limit of the Picard iterates.** -/
noncomputable def picardLimit (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    ℝ → Ω → (Fin n → ℝ) :=
  bieleckiLimit fun m =>
    (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).X

theorem measurable_picardLimit (hT : 0 < T) (X₀ : SBoundedProcess (n := n) P ℱ' T) :
    Measurable (Function.uncurry
      (picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)) :=
  measurable_bieleckiLimit fun m =>
    (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).measurable_path

theorem progressivelyMeasurable_picardLimit (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T) (i : Fin n) :
    Probability.ProgressivelyMeasurable ℱ'
      fun ω s => picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ s ω i :=
  progressivelyMeasurable_bieleckiLimit
    (fun m i' => (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ m).adapted i') i

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg in
/-- Slice measurability of a jointly measurable path map. -/
theorem measurable_slice_of_uncurry {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZm : Measurable (Function.uncurry Z)) (t : ℝ) (i : Fin n) :
    Measurable fun ω => Z t ω i :=
  (measurable_pi_apply i).comp (Measurable.of_uncurry_left hZm)

/-- The limit of the Picard iterates has finite Bielecki norm at weight `0`. -/
theorem bieleckiNorm_picardLimit_lt_top {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    bieleckiNorm (P := P) 0 T
      (picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀) < ⊤ := by
  have hYm := measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hbase : bieleckiNorm (P := P) β T X₀.X < ⊤ :=
    lt_of_le_of_lt (bieleckiNorm_le_bieleckiNorm_zero hβ.le T X₀.X) X₀.sup_L2
  have hsub := bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull coeffs
    hReg hLip x₀ hβ hT X₀ hq 0
  have hfin : ((1 - (ENNReal.ofReal
        ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
          / (2 * β))) ^ ((1 : ℝ) / 2))⁻¹
      * bieleckiNorm (P := P) β T (fun t ω i =>
          (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
            - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i))
      ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne
  have hd : bieleckiNorm (P := P) β T (fun t ω i => X₀.X t ω i
      - picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) < ⊤ := by
    refine lt_of_le_of_lt hsub ?_
    rw [pow_zero, one_mul]
    exact lt_top_iff_ne_top.mpr hfin
  refine lt_of_le_of_lt (bieleckiNorm_zero_le_mul (P := P) hβ.le _)
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
  exact bieleckiNorm_lt_top_of_approx β T
    (fun t i => measurable_slice_of_uncurry X₀.measurable_path t i)
    (fun t i => measurable_slice_of_uncurry hYm t i) hbase hd

/-- Slice measurability of the Picard step along a raw state process. -/
theorem measurable_picardStepOnRawStop_slice
    {Z : ℝ → Ω → (Fin n → ℝ)} (hZm : Measurable (Function.uncurry Z))
    (hZa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z s ω i)
    (hZb : bieleckiNorm (P := P) 0 T Z < ⊤) (hT : 0 ≤ T) (t : ℝ) (i : Fin n) :
    Measurable fun ω =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hZm hZa hZb hT x₀ t ω i :=
  measurable_picardStep_slice W N ℱ' hℱW hℱN coeffs (fun s ω => Z (min s T) ω) x₀
    (measurable_sigma_rawStop coeffs hReg hZm T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg hZa T)
    (fun i' j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT) i' j hT')
    (measurable_gamma_rawStop coeffs hReg hZm T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg hZa T)
    (fun i' _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z (min s T) ω)
      (hZm.comp ((measurable_fst.min measurable_const).prodMk measurable_snd))
      (lintegral_sq_rawStop_lt_top hZm hZb hT) i' hT')
    (measurable_mu_rawStop coeffs hReg hZm T) t i

/-- **The limit of the Picard iterates is a fixed point of the Picard step**: the Bielecki
distance between the step along the limit and the limit itself is zero. -/
theorem bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
            (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
              x₀ hT X₀)
            (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
              hβ hT X₀ hq)
            hT.le x₀ t ω i
          - picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i) = 0 := by
  set q := (ENNReal.ofReal
      ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
        / (2 * β))) ^ ((1 : ℝ) / 2) with hqdef
  set Y := picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ with hYdef
  have hYm := measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Φ := picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT.le x₀ with hΦdef
  set D := (1 - q)⁻¹ * bieleckiNorm (P := P) β T (fun t ω i =>
      (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 1).X t ω i
        - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ 0).X t ω i)
    with hDdef
  have hDfin : D ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hq).ne')
      (bieleckiNorm_sub_lt_top ℱ' hβ.le _ _).ne
  have hiter := fun k => bieleckiNorm_picardIter_sub_bieleckiLimit_le W N ℱ' hℱW hℱN hℱ0 hnull
    coeffs hReg hLip x₀ hβ hT X₀ hq k
  have hbound : ∀ k : ℕ, bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i - Y t ω i)
      ≤ q ^ (k + 1) * D + q ^ (k + 1) * D := by
    intro k
    have hXm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i :=
      fun t i => measurable_slice_of_uncurry
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
          (k + 1)).measurable_path t i
    have hΦm : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Φ t ω i := fun t i =>
      measurable_picardStepOnRawStop_slice W N ℱ' hℱW hℱN coeffs hReg hLip x₀
        hYm hYa hYb hT.le t i
    have hYsl : ∀ (t : ℝ) (i : Fin n), Measurable fun ω => Y t ω i :=
      fun t i => measurable_slice_of_uncurry hYm t i
    have hEq : (fun t ω i => Φ t ω i - Y t ω i)
        = fun t (ω : Ω) =>
          (fun i => Φ t ω i
            - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
          + fun i =>
            (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
              - Y t ω i := by
      funext t ω i
      simp [Pi.add_apply, sub_add_sub_cancel]
    have hadd := bieleckiNorm_add_le (P := P) β T
      (fun t ω => fun i => Φ t ω i
        - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
      (fun t ω => fun i =>
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i
          - Y t ω i)
      (bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hΦm t i).sub (hXm t i))
      (bieleckiNorm_inner_aemeasurable_of_slice fun t i => (hXm t i).sub (hYsl t i))
    have hcongr : bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        = bieleckiNorm (P := P) β T (fun t ω i =>
            picardStepOnStop W N hℱW hℱN coeffs hReg hLip
              (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) hT.le x₀ t ω i
              - Φ t ω i) := by
      rw [bieleckiNorm_sub_comm (P := P) β T]
      refine bieleckiNorm_congr_ae (P := P) β T fun t => ?_
      filter_upwards [picardSelfMap_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
        (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k) t] with ω hω
      funext i
      have hunfold : (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
            (k + 1)).X t ω
          = (picardSelfMap W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ k)).X t ω := rfl
      rw [hunfold, hω]
    have hfirst : bieleckiNorm (P := P) β T (fun t ω i => Φ t ω i
          - (picardIter W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ (k + 1)).X t ω i)
        ≤ q ^ (k + 1) * D := by
      rw [hcongr]
      refine le_trans (bieleckiNorm_picardStepOnStop_sub_rawStop_le W N ℱ' hℱW hℱN
        coeffs hReg hLip hYm hYa hYb x₀ hβ hT _) ?_
      refine le_trans (mul_le_mul' le_rfl (hiter k)) (le_of_eq ?_)
      rw [← mul_assoc, ← pow_succ']
    rw [hEq]
    exact hadd.trans (add_le_add hfirst (hiter (k + 1)))
  have htend : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D + q ^ (k + 1) * D)
      Filter.atTop (nhds 0) := by
    have hp : Filter.Tendsto (fun k : ℕ => q ^ (k + 1)) Filter.atTop (nhds 0) :=
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq).comp (Filter.tendsto_add_atTop_nat 1)
    have hm : Filter.Tendsto (fun k : ℕ => q ^ (k + 1) * D) Filter.atTop (nhds 0) := by
      simpa using ENNReal.Tendsto.mul_const hp (Or.inr hDfin)
    simpa using hm.add hm
  exact le_antisymm (ge_of_tendsto' htend hbound) zero_le

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip in
/-- A vanishing Bielecki norm means the path map vanishes almost surely at every time of the
window. -/
theorem ae_eq_zero_of_bieleckiNorm_eq_zero {β T : ℝ} {Z : ℝ → Ω → (Fin n → ℝ)}
    (hZs : ∀ (u : ℝ) (i : Fin n), Measurable fun ω => Z u ω i)
    (h : bieleckiNorm (P := P) β T Z = 0) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0 := by
  have hterm : ENNReal.ofReal (Real.exp (-β * t))
      * (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) = 0 := by
    refine le_antisymm ?_ zero_le
    rw [← h]
    exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (0 : ℝ) T) =>
      ENNReal.ofReal (Real.exp (-β * u))
        * (∫⁻ ω, ∑ i, (‖Z u ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2)) t ht
  have hexp : ENNReal.ofReal (Real.exp (-β * t)) ≠ 0 := by
    simp [ENNReal.ofReal_eq_zero, Real.exp_pos]
  have hrpow : (∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) ^ ((1 : ℝ) / 2) = 0 :=
    (mul_eq_zero.mp hterm).resolve_left hexp
  have hint : ∫⁻ ω, ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
    rcases ENNReal.rpow_eq_zero_iff.mp hrpow with ⟨h0, _⟩ | ⟨_, hneg⟩
    · exact h0
    · exact absurd hneg (by norm_num)
  have hmeas : AEMeasurable (fun ω => ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2) P :=
    (Finset.measurable_sum _ fun i _ =>
      (ENNReal.continuous_coe.measurable.comp (hZs t i).nnnorm).pow_const 2).aemeasurable
  filter_upwards [(lintegral_eq_zero_iff' hmeas).mp hint] with ω hω i
  have hle : (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2 = 0 :=
    le_antisymm (le_of_le_of_eq (Finset.single_le_sum
      (f := fun j => (‖Z t ω j‖₊ : ℝ≥0∞) ^ 2) (fun _ _ => zero_le) (Finset.mem_univ i)) hω)
      zero_le
  simpa using hle

/-- **The fixed point is realised by a process of the space.** The raw self-map applied to the
Picard limit is a jointly measurable, adapted, almost surely càdlàg process which agrees with the
limit almost surely at every time of the window. -/
theorem picardSelfMapRaw_picardLimit_ae_eq {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
          (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
          (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
            x₀ hT X₀)
          (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
            hβ hT X₀ hq)).X t ω i
        = picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ t ω i := by
  have hYm := measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  have hslice : ∀ (u : ℝ) (i : Fin n), Measurable fun ω =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip hYm hYa hYb hT.le x₀ u ω i
        - picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ u ω i :=
    fun u i => (measurable_picardStepOnRawStop_slice W N ℱ' hℱW hℱN coeffs hReg hLip x₀
      hYm hYa hYb hT.le u i).sub (measurable_slice_of_uncurry hYm u i)
  have hzero := ae_eq_zero_of_bieleckiNorm_eq_zero (P := P) hslice
    (bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero W N ℱ' hℱW hℱN hℱ0 hnull coeffs
      hReg hLip x₀ hβ hT X₀ hq) ht
  filter_upwards [picardSelfMapRaw_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
    hYm hYa hYb t, hzero] with ω hmod hz i
  rw [congrFun hmod i, ← sub_eq_zero]
  exact hz i

/-! ### The step respects almost sure equality of its input -/

/-- **The Picard step contracts between two raw state processes.** -/
theorem bieleckiNorm_picardStepOnRawStop_diff_le
    {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
    (h₁a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
    (h₁b : bieleckiNorm (P := P) 0 T Z₁ < ⊤)
    {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
    (h₂a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
    (h₂b : bieleckiNorm (P := P) 0 T Z₂ < ⊤)
    {β : ℝ} (hβ : 0 < β) (hT : 0 < T) :
    bieleckiNorm (P := P) β T (fun t ω i =>
        picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
          - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i)
      ≤ (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2)
        * bieleckiNorm (P := P) β T (fun t ω i => Z₁ t ω i - Z₂ t ω i) := by
  have h₁sm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z₁ (min s T) ω) :=
    h₁m.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have h₂sm : Measurable (Function.uncurry fun (s : ℝ) (ω : Ω) => Z₂ (min s T) ω) :=
    h₂m.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)
  have h₁e := lintegral_sq_rawStop_lt_top h₁m h₁b hT.le
  have h₂e := lintegral_sq_rawStop_lt_top h₂m h₂b hT.le
  have hdiffm : Measurable
      (Function.uncurry fun (ω : Ω) (s : ℝ) => Z₁ (min s T) ω - Z₂ (min s T) ω) :=
    (h₁sm.comp (measurable_snd.prodMk measurable_fst)).sub
      (h₂sm.comp (measurable_snd.prodMk measurable_fst))
  have hrhs : bieleckiNorm (P := P) β T
      (fun t ω i => Z₁ (min t T) ω i - Z₂ (min t T) ω i)
      = bieleckiNorm (P := P) β T (fun t ω i => Z₁ t ω i - Z₂ t ω i) :=
    bieleckiNorm_min (P := P) β T fun t ω i => Z₁ t ω i - Z₂ t ω i
  rw [← hrhs]
  exact bieleckiNorm_picardStep_diff_le W N ℱ' hℱW hℱN coeffs hLip
    (fun s ω => Z₁ (min s T) ω) (fun s ω => Z₂ (min s T) ω) x₀
    (measurable_sigma_rawStop coeffs hReg h₁m T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg h₁a T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁sm h₁e i j hT')
    (measurable_gamma_rawStop coeffs hReg h₁m T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg h₁a T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁sm h₁e i hT')
    (measurable_sigma_rawStop coeffs hReg h₂m T)
    (progressivelyMeasurable_sigma_rawStop coeffs hReg h₂a T)
    (fun i j _ hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂sm h₂e i j hT')
    (measurable_gamma_rawStop coeffs hReg h₂m T)
    (markedProgressivelyMeasurable_gamma_rawStop coeffs hReg h₂a T)
    (fun i _ hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂sm h₂e i hT')
    (measurable_mu_rawStop coeffs hReg h₁m T)
    (measurable_mu_rawStop coeffs hReg h₂m T)
    hdiffm.norm
    (fun i b hb => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₁ (min s T) ω) h₁sm h₁e i hb)
    (fun i b hb => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (Z := fun s ω => Z₂ (min s T) ω) h₂sm h₂e i hb)
    (fun b _ => lintegral_sq_sub_lt_top_of_energy h₁sm h₂sm h₁e h₂e b)
    hdiffm hβ hT

omit [ℱ'.IsRightContinuous] hℱW hℱN hℱ0 hnull hReg hLip in
/-- A path map vanishing almost surely at every time of the window has zero Bielecki norm. -/
theorem bieleckiNorm_eq_zero_of_ae (β T : ℝ) {Z : ℝ → Ω → (Fin n → ℝ)}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z t ω i = 0) :
    bieleckiNorm (P := P) β T Z = 0 := by
  refine le_antisymm (iSup₂_le fun t ht => ?_) zero_le
  have hz : (fun ω => ∑ i, (‖Z t ω i‖₊ : ℝ≥0∞) ^ 2) =ᵐ[P] 0 := by
    filter_upwards [h t ht] with ω hω
    simp [hω]
  rw [lintegral_congr_ae hz]
  simp [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]

/-- **The Picard step respects almost sure equality of its input.** -/
theorem picardStepOnRawStop_congr_ae
    {Z₁ : ℝ → Ω → (Fin n → ℝ)} (h₁m : Measurable (Function.uncurry Z₁))
    (h₁a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₁ s ω i)
    (h₁b : bieleckiNorm (P := P) 0 T Z₁ < ⊤)
    {Z₂ : ℝ → Ω → (Fin n → ℝ)} (h₂m : Measurable (Function.uncurry Z₂))
    (h₂a : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ' fun ω s => Z₂ s ω i)
    (h₂b : bieleckiNorm (P := P) 0 T Z₂ < ⊤)
    (heq : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i, Z₁ t ω i = Z₂ t ω i)
    {β : ℝ} (hβ : 0 < β) (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ t ω i
        = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ t ω i := by
  have hin : bieleckiNorm (P := P) β T (fun u ω i => Z₁ u ω i - Z₂ u ω i) = 0 := by
    refine bieleckiNorm_eq_zero_of_ae (P := P) β T fun u hu => ?_
    filter_upwards [heq u hu] with ω hω i
    rw [hω i, sub_self]
  have hout : bieleckiNorm (P := P) β T (fun u ω i =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ u ω i
        - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ u ω i) = 0 := by
    refine le_antisymm ?_ zero_le
    refine le_trans (bieleckiNorm_picardStepOnRawStop_diff_le W N ℱ' hℱW hℱN coeffs hReg hLip
      x₀ h₁m h₁a h₁b h₂m h₂a h₂b hβ hT) ?_
    rw [hin, mul_zero]
  have hslice : ∀ (u : ℝ) (i : Fin n), Measurable fun ω =>
      picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₁m h₁a h₁b hT.le x₀ u ω i
        - picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip h₂m h₂a h₂b hT.le x₀ u ω i :=
    fun u i => (measurable_picardStepOnRawStop_slice W N ℱ' hℱW hℱN coeffs hReg hLip x₀
      h₁m h₁a h₁b hT.le u i).sub
      (measurable_picardStepOnRawStop_slice W N ℱ' hℱW hℱN coeffs hReg hLip x₀
        h₂m h₂a h₂b hT.le u i)
  filter_upwards [ae_eq_zero_of_bieleckiNorm_eq_zero (P := P) hslice hout ht] with ω hω i
  exact sub_eq_zero.mp (hω i)

/-! ### The fixed point solves its own Picard equation -/

/-- **The fixed point is a solution of the Picard equation along its own path.** On the window,
the process agrees almost surely with the Picard step taken along itself, frozen at the horizon.
-/
theorem picardSelfMapRaw_isFixedPoint {β : ℝ} (hβ : 0 < β) (hT : 0 < T)
    (X₀ : SBoundedProcess (n := n) P ℱ' T)
    (hq : (ENNReal.ofReal
            ((3 * ((n : ℝ) * L ^ 2 * T + (n : ℝ) * ((d : ℝ) * L ^ 2) + (n : ℝ) * L ^ 2))
              / (2 * β))) ^ ((1 : ℝ) / 2) < 1)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∀ᵐ ω ∂P, ∀ i,
      (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
          (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
          (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
            x₀ hT X₀)
          (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
            hβ hT X₀ hq)).X t ω i
        = picardStepOnRawStop W N hℱW hℱN coeffs hReg hLip
            (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).measurable_path
            (fun i' =>
              (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
                (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
                (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
                  hLip x₀ hT X₀)
                (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                  x₀ hβ hT X₀ hq)).adapted i')
            (picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
              (measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀)
              (progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
                x₀ hT X₀)
              (bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
                hβ hT X₀ hq)).sup_L2
            hT.le x₀ t ω i := by
  have hYm := measurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀
  have hYa := progressivelyMeasurable_picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip
    x₀ hT X₀
  have hYb := bieleckiNorm_picardLimit_lt_top W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀
    hβ hT X₀ hq
  set Xhat := picardSelfMapRaw W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT hYm hYa hYb
    with hXhat
  have heq : ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, ∀ i,
      picardLimit W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT X₀ u ω i
        = Xhat.X u ω i := by
    intro u hu
    filter_upwards [picardSelfMapRaw_picardLimit_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg
      hLip x₀ hβ hT X₀ hq hu] with ω hω i
    exact (hω i).symm
  have hcongr := picardStepOnRawStop_congr_ae W N ℱ' hℱW hℱN coeffs hReg hLip x₀
    hYm hYa hYb Xhat.measurable_path (fun i' => Xhat.adapted i') Xhat.sup_L2 heq hβ hT ht
  filter_upwards [picardSelfMapRaw_ae_eq W N ℱ' hℱW hℱN hℱ0 hnull coeffs hReg hLip x₀ hT
    hYm hYa hYb t, hcongr] with ω hmod hc i
  rw [congrFun hmod i]
  exact hc i

end LevyStochCalc.Ito.Picard
