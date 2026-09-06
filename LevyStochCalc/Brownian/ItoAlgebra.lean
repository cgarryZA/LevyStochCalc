/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoL2Completion

/-!
# Simple integrands inside the `L²` Brownian Itô integral

The `L²` Itô integral is built as a limit of elementary integrals of simple integrands, so a
simple integrand can be fed to it in its own right. This file records that a simple integrand is
progressively measurable and square-integrable on every window, and that the `L²` integral of a
simple integrand is its elementary integral.

## Main statements

* `SimplePredictable.progressivelyMeasurable_eval` — a simple integrand with adapted
  coefficients is progressively measurable.
* `simpleIntegral_diff_isometry_of_adapted` — the difference isometry for two adapted simple
  integrands at an intermediate time, with no constraint relating their horizons.
* `stochasticIntegralBrownian_eval_simple` — the `L²` Itô integral of a simple integrand agrees
  almost everywhere with its elementary integral.
* `SimplePredictable.mul_on_common` — the product of two simple integrands, carried on their
  common refinement, together with its evaluation and its adaptedness.
* `SimplePredictable.integralAgainst` — the elementary integral of a simple integrand against an
  arbitrary process.
* `SimplePredictable.sum_xi_mul_simpleIntegral_sub` — the elementary integral of `G` against the
  elementary integral of `K` is the elementary integral of the product `G · K`.
* `isometry_simple_sub_stochasticIntegralBrownian` — the difference isometry between an
  elementary integral and an `L²` integral.
* `stochasticIntegralBrownian_integralAgainst` — summing the increments of the `L²` Itô integral
  of `H` against the coefficients of a simple integrand `G` gives the `L²` Itô integral of the
  product `G · H`.
* `stepIoc`, `stepIoc₀` — the simple integrand `1_{(a, b]}`.
* `stochasticIntegralBrownian_indicator_Ioc` — restricting the integrand to `(a, b]` gives the
  increment of the integral across `(a, b]`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A simple integrand is uniformly bounded in both variables. -/
theorem SimplePredictable.exists_eval_bound {T : ℝ} (G : SimplePredictable Ω T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ s ω, |G.eval s ω| ≤ B := by
  classical
  choose M hM using G.ξ_bounded
  refine ⟨∑ i : Fin G.N, max (M i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun s ω => ?_⟩
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  by_cases h : G.partition i.castSucc < s ∧ s ≤ G.partition i.succ
  · rw [if_pos h]; exact (hM i ω).trans (le_max_left _ _)
  · rw [if_neg h, abs_zero]; exact le_max_right _ _

/-- The `L²`-mass of a simple integrand over any time window is finite. -/
theorem SimplePredictable.lintegral_eval_sq_lt_top {T : ℝ} (G : SimplePredictable Ω T)
    (P : Measure Ω) [IsProbabilityMeasure P] (T' : ℝ) (_hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  have hpt : ∀ s ω, ((‖G.eval s ω‖₊ : ℝ≥0∞)) ^ 2 ≤ (ENNReal.ofReal B) ^ 2 := by
    intro s ω
    refine pow_le_pow_left' ?_ 2
    have hx : ‖G.eval s ω‖ ≤ B := (Real.norm_eq_abs _).le.trans (hB s ω)
    calc (‖G.eval s ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖G.eval s ω‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal B := ENNReal.ofReal_le_ofReal hx
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T',
        (ENNReal.ofReal B) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt s ω
    _ < ⊤ := by
        rw [lintegral_const, setLIntegral_const, Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
          ENNReal.ofReal_lt_top


/-- A finite sum of step processes `1_{(aᵢ, bᵢ]}(s) · ξᵢ ω`, with `ξᵢ` measurable for
`ℱ (aᵢ)`, is progressively measurable. -/
theorem progressivelyMeasurable_sum_indicator_Ioc
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {n : ℕ} (a b : Fin n → ℝ)
    (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (a i)) (ξ i)) :
    Probability.ProgressivelyMeasurable ℱ
      (fun ω s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i ω) s) := by
  classical
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => ∑ i : Fin n, (Set.Ioc (a i) (b i)).indicator (fun _ => ξ i p.1) s) p.2)
      = fun p : Ω × ℝ => ∑ i : Fin n,
        (Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t)).indicator
          (fun q : Ω × ℝ => ξ i q.1) p := by
    funext p
    by_cases hp : p.2 ≤ t
    · rw [Set.indicator_of_mem (Set.mem_Iic.mpr hp)]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : p.2 ∈ Set.Ioc (a i) (b i)
      · have hmem : p ∈ Set.univ ×ˢ (Set.Ioc (a i) (b i) ∩ Set.Iic t) :=
          ⟨Set.mem_univ _, hi, Set.mem_Iic.mpr hp⟩
        rw [Set.indicator_of_mem hi, Set.indicator_of_mem hmem]
      · rw [Set.indicator_of_notMem hi, Set.indicator_of_notMem]
        rintro ⟨-, hmem, -⟩
        exact hi hmem
    · rw [Set.indicator_of_notMem (by simpa using hp)]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [Set.indicator_of_notMem]
      rintro ⟨-, -, hmem⟩
      exact hp (Set.mem_Iic.mp hmem)
  letI : MeasurableSpace Ω := ℱ t
  rw [key]
  refine Finset.stronglyMeasurable_fun_sum _ fun i _ => ?_
  by_cases hi : a i < t
  · refine MeasureTheory.StronglyMeasurable.indicator ?_
      (MeasurableSet.univ.prod (measurableSet_Ioc.inter measurableSet_Iic))
    exact ((hξ i).mono (ℱ.mono hi.le)).comp_measurable measurable_fst
  · have hempty : Set.Ioc (a i) (b i) ∩ Set.Iic t = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun s hs =>
        absurd (lt_of_lt_of_le hs.1.1 hs.2) (not_lt.mpr (not_lt.mp hi))
    rw [hempty, Set.prod_empty, Set.indicator_empty]
    exact MeasureTheory.stronglyMeasurable_const

/-- A simple integrand with `ℱ`-adapted coefficients is progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    Probability.ProgressivelyMeasurable ℱ (fun ω s => G.eval s ω) := by
  have hfun : (fun ω s => G.eval s ω)
      = fun ω s => ∑ i : Fin G.N,
        (Set.Ioc (G.partition i.castSucc) (G.partition i.succ)).indicator
          (fun _ => G.ξ i ω) s := by
    funext ω s; exact eval_eq_sum_indicator G s ω
  rw [hfun]
  exact progressivelyMeasurable_sum_indicator_Ioc ℱ _ _ _ h_adapt


/-- Difference isometry at an intermediate time for two adapted simple integrands whose
horizons need not agree. -/
theorem simpleIntegral_diff_isometry_of_adapted
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {T₁ T₂ : ℝ} (G₁ : SimplePredictable Ω T₁) (G₂ : SimplePredictable Ω T₂)
    (h₁ : ∀ i : Fin G₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₁.partition i.castSucc)) (G₁.ξ i))
    (h₂ : ∀ i : Fin G₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G₂.partition i.castSucc)) (G₂.ξ i))
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω,
        (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set K : ℝ :=
    max (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N)) + 1 with hK
  have hK₁ : G₁.partition (Fin.last G₁.N) < K := by
    have := le_max_left (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have hK₂ : G₂.partition (Fin.last G₂.N) < K := by
    have := le_max_right (G₁.partition (Fin.last G₁.N)) (G₂.partition (Fin.last G₂.N))
    rw [hK]; linarith
  have h_eq : (G₁.appendInterval hK₁).partition (Fin.last (G₁.appendInterval hK₁).N)
      = (G₂.appendInterval hK₂).partition (Fin.last (G₂.appendInterval hK₂).N) :=
    (G₁.appendInterval_partition_last hK₁).trans (G₂.appendInterval_partition_last hK₂).symm
  have hiso := simpleIntegral_intermediate_diff_isometry W ℱ hℱ (G₁.appendInterval hK₁)
    (G₂.appendInterval hK₂) h_eq (G₁.appendInterval_adapt ℱ hK₁ h₁)
    (G₂.appendInterval_adapt ℱ hK₂ h₂) ht
  have hL : ∫⁻ ω,
        (‖simpleIntegral W G₁ t ω - simpleIntegral W G₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (G₁.appendInterval hK₁) t ω
          - simpleIntegral W (G₂.appendInterval hK₂) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    lintegral_congr fun ω => by
      rw [G₁.appendInterval_simpleIntegral W hK₁ t ω,
        G₂.appendInterval_simpleIntegral W hK₂ t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖G₁.eval s ω - G₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(G₁.appendInterval hK₁).eval s ω
          - (G₂.appendInterval hK₂).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    lintegral_congr fun ω => MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => by
      rw [G₁.appendInterval_eval hK₁ s ω, G₂.appendInterval_eval hK₂ s ω]
  rw [hL, hR]; exact hiso


/-- A simple integrand is jointly measurable in the form the integral consumes. -/
theorem SimplePredictable.measurable_uncurry_eval {T : ℝ} (G : SimplePredictable Ω T) :
    Measurable (Function.uncurry fun ω s => G.eval s ω) := G.eval_jointly_measurable

/-- A simple integrand times a jointly measurable process is jointly measurable. -/
theorem SimplePredictable.measurable_uncurry_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) :
    Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s) :=
  G.eval_jointly_measurable.mul hm

/-- A simple integrand with adapted coefficients times a progressively measurable process is
progressively measurable. -/
theorem SimplePredictable.progressivelyMeasurable_eval_mul {T : ℝ} (G : SimplePredictable Ω T)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s :=
  (G.progressivelyMeasurable_eval ℱ h_adapt).mul hp

/-- A simple integrand times a square-integrable process is square-integrable on every
window. -/
theorem SimplePredictable.lintegral_eval_mul_sq_lt_top {T : ℝ} (G : SimplePredictable Ω T)
    {P : Measure Ω} [IsProbabilityMeasure P] {H : Ω → ℝ → ℝ}
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T' : ℝ) (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
    intro s ω
    calc (‖G.eval s ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal ‖G.eval s ω‖ := by
          rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
      _ ≤ ENNReal.ofReal B :=
          ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
  have hpt : ∀ s ω, (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro s ω
    rw [nnnorm_mul, ENNReal.coe_mul, mul_pow]
    gcongr
    exact hbd s ω
  have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          ENNReal.ofReal B ^ 2 * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        lintegral_mono fun ω => lintegral_mono fun s => hpt s ω
    _ = ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
        exact lintegral_congr fun ω => MeasureTheory.lintegral_const_mul' _ _ hne
    _ < ⊤ := ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hne) (hq T' hT')

section EvalSimple

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (hm : Measurable (Function.uncurry fun ω s => G.eval s ω))
  (hp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **The `L²` Itô integral of a simple integrand is its elementary integral.** -/
theorem stochasticIntegralBrownian_eval_simple {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t
      =ᵐ[P] simpleIntegral W G t := by
  classical
  have hIn : ∀ n : ℕ, Measurable
      (simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIG : Measurable (simpleIntegral W G t) := by
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hSI : Measurable
      (stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t).mono (ℱ.le t)).measurable
  -- the master integrals converge to the elementary integral of `G`
  have hA : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    refine (masterApprox_eval_tendsto ℱ (fun ω s => G.eval s ω) hm hp hq ht).congr
      fun n => ?_
    rw [simpleIntegral_diff_isometry_of_adapted W ℱ hℱ _ G
      (masterApprox_adapt ℱ (fun ω s => G.eval s ω) hm hp hq n) h_adapt ht]
    refine lintegral_congr fun ω =>
      MeasureTheory.setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
    rw [← nnnorm_neg, neg_sub]
  -- and to the `L²` Itô integral
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  have hB : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have h := masterApprox_tendsto_L2 W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq ht
    have h2 := ENNReal.Tendsto.mul h (Or.inr (by simp)) h (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze
  have hle : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
      hq t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim : Filter.Tendsto (fun n => 2 * ((∫⁻ ω,
        (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp hq n) t ω
          - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
            hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
            hq n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P))
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul (a := 2) (hB.add hA) (Or.inr (by simp))
      simpa using this
    refine ge_of_tendsto hlim (Filter.Eventually.of_forall fun n => ?_)
    calc ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
          hq t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2
            + (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                hq t ω - simpleIntegral W G t ω
              = -(simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω)
                  hm hp hq t ω)
                + (simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
                  hq n) t ω - simpleIntegral W G t ω) := by ring
          rw [hrw]
          refine le_trans (sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm
              hp hq n) t ω - stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => G.eval s ω) hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖simpleIntegral W (masterApprox ℱ (fun ω s => G.eval s ω) hm hp
              hq n) t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          have hm2 : AEMeasurable (fun ω => (‖simpleIntegral W (masterApprox ℱ
              (fun ω s => G.eval s ω) hm hp hq n) t ω
                - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp
                  hq t ω‖₊ : ℝ≥0∞) ^ 2) P :=
            ((((hIn n).sub hSI).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm
      hp hq t ω - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    le_antisymm hle bot_le
  have hmeas : Measurable fun ω => (‖stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω) hm hp hq t ω
        - simpleIntegral W G t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hSI.sub hIG).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) hm hp hq t ω
      - simpleIntegral W G t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0

end EvalSimple

/-- At most one cell of a strictly monotone partition contains a given time, so a product of
two step sums over that partition is the step sum of the pointwise product. -/
theorem sum_ite_mul_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f g : Fin M → ℝ) (s : ℝ) :
    (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      * (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j * g j else 0 := by
  classical
  by_cases h : ∃ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ → j = j₀ := by
      intro j hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (j.succ : Fin (M + 1)) ≤ j₀.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
        exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hj₀.1)
      · have hle : (j₀.succ : Fin (M + 1)) ≤ j.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
        exact absurd (hj₀.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
    have hsum : ∀ h : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h j else 0) = h j₀ := by
      intro h
      rw [Finset.sum_eq_single j₀ (fun j _ hjne => if_neg fun hc => hjne (huniq j hc))
        (fun hnm => absurd (Finset.mem_univ _) hnm)]
      exact if_pos hj₀
    rw [hsum f, hsum g, hsum fun j => f j * g j]
  · push Not at h
    have hz : ∀ h' : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h' j else 0) = 0 :=
      fun h' => Finset.sum_eq_zero fun j _ => if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz f, hz g, hz fun j => f j * g j, mul_zero]


/-- The product of two simple integrands, carried on their common refinement. -/
noncomputable def SimplePredictable.mul_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T where
  N := H₁.mergedM H₂
  partition := H₁.mergedπ H₂
  partition_zero := H₁.mergedπ_zero H₂
  partition_le_T := (H₁.mergedπ_last H₂ h_eq) ▸ H₁.partition_le_T
  partition_strictMono := H₁.mergedπ_strictMono H₂
  ξ := fun j ω => H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
    * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω
  ξ_bounded := fun j => by
    obtain ⟨C₁, hC₁⟩ := H₁.ξ_bounded (H₁.mergedIdxMap_left H₂ h_eq j)
    obtain ⟨C₂, hC₂⟩ := H₂.ξ_bounded (H₁.mergedIdxMap_right H₂ h_eq j)
    refine ⟨max C₁ 0 * max C₂ 0, fun ω => ?_⟩
    rw [abs_mul]
    exact mul_le_mul ((hC₁ ω).trans (le_max_left _ _)) ((hC₂ ω).trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)
  ξ_measurable := fun j =>
    (H₁.ξ_measurable _).mul (H₂.ξ_measurable _)

/-- The product on the common refinement evaluates to the product of the evaluations. -/
theorem SimplePredictable.eval_mul_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.mul_on_common H₂ h_eq).eval s ω = H₁.eval s ω * H₂.eval s ω := by
  have hl := H₁.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂) (H₁.mergedπ_zero H₂)
    (H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_left H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq) (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) s ω
  have hr := H₂.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂) (H₁.mergedπ_zero H₂)
    (h_eq ▸ H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_right H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq) (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) s ω
  rw [SimplePredictable.eval] at hl hr ⊢
  change (∑ j : Fin (H₁.mergedM H₂),
      if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
        then H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          * H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω else 0)
    = H₁.eval s ω * H₂.eval s ω
  rw [← hl, ← hr]
  exact (sum_ite_mul_sum_ite (H₁.mergedπ_strictMono H₂) _ _ s).symm


private lemma min_min_of_le {a b t : ℝ} (h : a ≤ b) : min a (min b t) = min a t := by
  rw [← min_assoc, min_eq_left h]

private lemma min_min_of_le' {a b t : ℝ} (h : a ≤ b) : min b (min a t) = min a t := by
  rw [← min_assoc, min_eq_right h]

/-- **The elementary integral against an elementary integral.** Summing the increments of
`simpleIntegral W K` against the coefficients of `G` gives the elementary integral of the
product `G · K` on the common refinement. -/
theorem SimplePredictable.sum_xi_mul_simpleIntegral_sub
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (G K : SimplePredictable Ω T)
    (h_eq : G.partition (Fin.last G.N) = K.partition (Fin.last K.N))
    (t : ℝ) (ω : Ω) :
    (∑ i : Fin G.N, G.ξ i ω *
        (simpleIntegral W K (min (G.partition i.succ) t) ω
          - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = simpleIntegral W (G.mul_on_common K h_eq) t ω := by
  classical
  set π : Fin (G.mergedM K + 1) → ℝ := G.mergedπ K with hπ
  set L : Fin (G.mergedM K) → Fin G.N := G.mergedIdxMap_left K h_eq with hL
  set R : Fin (G.mergedM K) → Fin K.N := G.mergedIdxMap_right K h_eq with hR
  have hmono : StrictMono π := G.mergedπ_strictMono K
  have hLle : ∀ j, G.partition (L j).castSucc ≤ π j.castSucc :=
    G.mergedIdxMap_left_idx_le K h_eq
  have hLge : ∀ j, π j.succ ≤ G.partition (L j).succ := G.mergedIdxMap_left_idx_ge K h_eq
  -- `K`'s elementary integral, read on the merged partition
  have hK : ∀ u : ℝ, simpleIntegral W K u ω
      = ∑ j : Fin (G.mergedM K), K.ξ (R j) ω
        * (W.W (min (π j.succ) u) ω - W.W (min (π j.castSucc) u) ω) := by
    intro u
    rw [← K.simpleIntegral_refine_intermediate W (G.mergedM K) π (G.mergedπ_zero K)
      (h_eq ▸ G.mergedπ_last K h_eq) hmono R (G.mergedIdxMap_right_idx_le K h_eq)
      (G.mergedIdxMap_right_idx_ge K h_eq) (G.mergedπ_refines_right K) u ω]
    rfl
  set ΔW : Fin (G.mergedM K) → ℝ := fun j =>
    W.W (min (π j.succ) t) ω - W.W (min (π j.castSucc) t) ω with hΔW
  set D : Fin G.N → Fin (G.mergedM K) → ℝ := fun i j =>
    (W.W (min (π j.succ) (min (G.partition i.succ) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.succ) t)) ω)
      - (W.W (min (π j.succ) (min (G.partition i.castSucc) t)) ω
        - W.W (min (π j.castSucc) (min (G.partition i.castSucc) t)) ω) with hD
  have hDself : ∀ j, D (L j) j = ΔW j := by
    intro j
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have h2 : G.partition (L j).castSucc ≤ π j.castSucc := hLle j
    rw [hD, hΔW]
    simp only
    rw [min_min_of_le (hLge j), min_min_of_le (h1.trans (hLge j)),
      min_min_of_le' (h2.trans h1), min_min_of_le' h2]
    ring
  have hDzero : ∀ (j : Fin (G.mergedM K)) (i : Fin G.N), i ≠ L j → D i j = 0 := by
    intro j i hne
    have h1 : π j.castSucc ≤ π j.succ := (hmono Fin.castSucc_lt_succ).le
    have hGi : G.partition i.castSucc ≤ G.partition i.succ :=
      G.partition_strictMono.monotone Fin.castSucc_lt_succ.le
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (i.succ : Fin (G.N + 1)) ≤ (L j).castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
      have hstep : G.partition i.succ ≤ π j.castSucc :=
        (G.partition_strictMono.monotone hle).trans (hLle j)
      rw [hD]
      simp only
      rw [min_min_of_le' hstep, min_min_of_le' (hstep.trans h1),
        min_min_of_le' (hGi.trans hstep), min_min_of_le' ((hGi.trans hstep).trans h1)]
      ring
    · have hle : ((L j).succ : Fin (G.N + 1)) ≤ i.castSucc := by
        rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
      have hstep : π j.succ ≤ G.partition i.castSucc :=
        (hLge j).trans (G.partition_strictMono.monotone hle)
      rw [hD]
      simp only
      rw [min_min_of_le (hstep.trans hGi), min_min_of_le (h1.trans (hstep.trans hGi)),
        min_min_of_le hstep, min_min_of_le (h1.trans hstep)]
      ring
  calc (∑ i : Fin G.N, G.ξ i ω *
          (simpleIntegral W K (min (G.partition i.succ) t) ω
            - simpleIntegral W K (min (G.partition i.castSucc) t) ω))
      = ∑ i : Fin G.N, ∑ j : Fin (G.mergedM K), G.ξ i ω * (K.ξ (R j) ω * D i j) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hK, hK, ← Finset.sum_sub_distrib, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hD]; ring
    _ = ∑ j : Fin (G.mergedM K), ∑ i : Fin G.N, G.ξ i ω * (K.ξ (R j) ω * D i j) :=
        Finset.sum_comm
    _ = ∑ j : Fin (G.mergedM K), G.ξ (L j) ω * K.ξ (R j) ω * ΔW j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_eq_single (L j)
          (fun i _ hne => by rw [hDzero j i hne, mul_zero, mul_zero])
          (fun hnm => absurd (Finset.mem_univ _) hnm), hDself j]
        ring
    _ = simpleIntegral W (G.mul_on_common K h_eq) t ω := by
        unfold simpleIntegral
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hΔW]
        rfl


/-- Adaptedness passes to the product on the common refinement. -/
theorem SimplePredictable.mul_on_common_adapt
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∀ j : Fin (H₁.mul_on_common H₂ h_eq).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((H₁.mul_on_common H₂ h_eq).partition j.castSucc))
        ((H₁.mul_on_common H₂ h_eq).ξ j) := by
  intro j
  have h₁ := (h_adapt₁ (H₁.mergedIdxMap_left H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_left_idx_le H₂ h_eq j))
  have h₂ := (h_adapt₂ (H₁.mergedIdxMap_right H₂ h_eq j)).mono
    (ℱ.mono (H₁.mergedIdxMap_right_idx_le H₂ h_eq j))
  exact h₁.mul h₂

/-- The elementary integral of a simple integrand against an arbitrary process. -/
noncomputable def SimplePredictable.integralAgainst {T : ℝ} (G : SimplePredictable Ω T)
    (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin G.N, G.ξ i ω *
    (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)

/-- The zero-extension leaves the elementary integral against a process unchanged. -/
theorem SimplePredictable.appendInterval_integralAgainst
    {T : ℝ} (G : SimplePredictable Ω T) {T' : ℝ}
    (hlt : G.partition (Fin.last G.N) < T') (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (G.appendInterval hlt).integralAgainst M t ω = G.integralAgainst M t ω := by
  unfold SimplePredictable.integralAgainst
  rw [G.appendInterval_partition_eq hlt, G.appendInterval_xi_eq hlt]
  change (∑ i : Fin (G.N + 1),
      (Fin.snoc (α := fun _ => Ω → ℝ) G.ξ (fun _ : Ω => (0 : ℝ))) i ω
        * (M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.succ) t) ω
            - M (min ((Fin.snoc (α := fun _ => ℝ) G.partition T') i.castSucc) t) ω))
    = ∑ i : Fin G.N, G.ξ i ω
        * (M (min (G.partition i.succ) t) ω - M (min (G.partition i.castSucc) t) ω)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_last, zero_mul, add_zero]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show (Fin.castSucc i).succ = Fin.castSucc i.succ from Fin.ext rfl]
  simp only [Fin.snoc_castSucc]

section SimpleVsGeneral

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **Difference isometry between an elementary integral and an `L²` integral.** -/
theorem isometry_simple_sub_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖simpleIntegral W G T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hiso := isometry_diff_stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω) H
    G.measurable_uncurry_eval hm (G.progressivelyMeasurable_eval ℱ h_adapt) hp
    (G.lintegral_eval_sq_lt_top P) hq hT
  rw [← hiso]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegralBrownian_eval_simple W ℱ hℱ G h_adapt
    G.measurable_uncurry_eval (G.progressivelyMeasurable_eval ℱ h_adapt)
    (G.lintegral_eval_sq_lt_top P) hT.le] with ω hω
  rw [hω]

end SimpleVsGeneral

/-- **The product of two simple integrands as a simple integrand.** For adapted `G` and `K` with
arbitrary horizons there is an adapted simple integrand `Q` whose evaluation is the product of
the evaluations and whose elementary integral is the elementary integral of `G` against the
elementary integral of `K`. -/
theorem SimplePredictable.exists_mul_simple
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T₁ T₂ : ℝ} (G : SimplePredictable Ω T₁) (K : SimplePredictable Ω T₂)
    (h_adaptG : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    (h_adaptK : ∀ i : Fin K.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (K.partition i.castSucc)) (K.ξ i)) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = G.eval s ω * K.eval s ω)
      ∧ (∀ t ω, G.integralAgainst (fun u ω' => simpleIntegral W K u ω') t ω
          = simpleIntegral W Q t ω) := by
  have hG : G.partition (Fin.last G.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_left (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have hK : K.partition (Fin.last K.N)
      < max (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)) + 1 := by
    have := le_max_right (G.partition (Fin.last G.N)) (K.partition (Fin.last K.N)); linarith
  have h_eq : (G.appendInterval hG).partition (Fin.last (G.appendInterval hG).N)
      = (K.appendInterval hK).partition (Fin.last (K.appendInterval hK).N) :=
    (G.appendInterval_partition_last hG).trans (K.appendInterval_partition_last hK).symm
  refine ⟨_, (G.appendInterval hG).mul_on_common (K.appendInterval hK) h_eq, ?_, ?_, ?_⟩
  · exact SimplePredictable.mul_on_common_adapt ℱ _ _ h_eq
      (G.appendInterval_adapt ℱ hG h_adaptG) (K.appendInterval_adapt ℱ hK h_adaptK)
  · intro s ω
    rw [SimplePredictable.eval_mul_on_common, G.appendInterval_eval hG,
      K.appendInterval_eval hK]
  · intro t ω
    rw [← SimplePredictable.sum_xi_mul_simpleIntegral_sub W (G.appendInterval hG)
      (K.appendInterval hK) h_eq t ω]
    have hKfun : (fun u (ω' : Ω) => simpleIntegral W K u ω')
        = fun u ω' => simpleIntegral W (K.appendInterval hK) u ω' := by
      funext u ω'; exact (K.appendInterval_simpleIntegral W hK u ω').symm
    rw [hKfun, ← G.appendInterval_integralAgainst hG
      (fun u ω' => simpleIntegral W (K.appendInterval hK) u ω') t ω]
    rfl

private lemma eLpNorm_mul_le_of_bound {P : Measure Ω} {c g : Ω → ℝ} {M : ℝ}
    (hM : ∀ ω, |c ω| ≤ M) :
    MeasureTheory.eLpNorm (fun ω => c ω * g ω) 2 P
      ≤ (‖M‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm g 2 P := by
  have hsm : (fun ω => M * g ω) = (M • g : Ω → ℝ) := by funext ω; simp
  refine le_trans (MeasureTheory.eLpNorm_mono (g := fun ω => M * g ω) fun ω => ?_) ?_
  · have hM0 : 0 ≤ M := (abs_nonneg (c ω)).trans (hM ω)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hM0]
    exact mul_le_mul_of_nonneg_right (hM ω) (abs_nonneg _)
  · rw [hsm]; exact MeasureTheory.eLpNorm_const_smul_le

section Associativity

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  {T₀ : ℝ} (G : SimplePredictable Ω T₀)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hmm : Measurable (Function.uncurry fun ω s => G.eval s ω * H ω s))
  (hmp : Probability.ProgressivelyMeasurable ℱ fun ω s => G.eval s ω * H ω s)
  (hmq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖G.eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ h_adapt in
/-- **Associativity against a simple integrand.** Summing the increments of the `L²` Itô integral
of `H` against the coefficients of a simple integrand `G` gives the `L²` Itô integral of the
product `G · H`. -/
theorem stochasticIntegralBrownian_integralAgainst {t : ℝ} (ht : 0 < t) :
    G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
        hmm hmp hmq t := by
  classical
  obtain ⟨B, hB0, hB⟩ := G.exists_eval_bound
  choose Th Q hQadapt hQeval hQint using fun n : ℕ =>
    SimplePredictable.exists_mul_simple W ℱ G (masterApprox ℱ H hm hp hq n) h_adapt
      (masterApprox_adapt ℱ H hm hp hq n)
  choose Mb hMb using G.ξ_bounded
  -- measurability bookkeeping
  have hMmeas : ∀ u : ℝ, Measurable (stochasticIntegralBrownian W ℱ hℱ H hm hp hq u) :=
    fun u => ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq u).mono
      (ℱ.le u)).measurable
  have hInmeas : ∀ (n : ℕ) (u : ℝ),
      Measurable (simpleIntegral W (masterApprox ℱ H hm hp hq n) u) := by
    intro n u
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((masterApprox ℱ H hm hp hq n).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hQmeas : ∀ n : ℕ, Measurable (simpleIntegral W (Q n) t) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hIAmeas : Measurable (G.integralAgainst
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t) := by
    unfold SimplePredictable.integralAgainst
    exact Finset.measurable_sum _ fun i _ =>
      (G.ξ_measurable i).mul ((hMmeas _).sub (hMmeas _))
  have hconv : ∀ g : Ω → ℝ, MeasureTheory.eLpNorm g 2 P * MeasureTheory.eLpNorm g 2 P
      = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro g
    rw [← eLpNorm_two_rpow_eq_lintegral_sq,
      show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
  -- (d) the product elementary integrals converge to the `L²` integral of `G.eval · H`
  have hd : Filter.Tendsto (fun n => ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) Filter.atTop (nhds 0) := by
    have hbd : ∀ s ω, (‖G.eval s ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal B := by
      intro s ω
      calc (‖G.eval s ω‖₊ : ℝ≥0∞)
          = ENNReal.ofReal ‖G.eval s ω‖ := by
            rw [ENNReal.ofReal_eq_coe_nnreal (norm_nonneg _)]; rfl
        _ ≤ ENNReal.ofReal B :=
            ENNReal.ofReal_le_ofReal ((Real.norm_eq_abs _).le.trans (hB s ω))
    have hne : ENNReal.ofReal B ^ 2 ≠ ⊤ := (ENNReal.pow_lt_top ENNReal.ofReal_lt_top).ne
    have hkey : ∀ n, ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal B ^ 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox ℱ H hm hp hq n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n)
        (fun ω s => G.eval s ω * H ω s) hmm hmp hmq ht,
        ← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun ω => ?_
      rw [← MeasureTheory.lintegral_const_mul' _ _ hne]
      refine lintegral_mono fun s => ?_
      have hrw : (Q n).eval s ω - G.eval s ω * H ω s
          = G.eval s ω * -(H ω s - (masterApprox ℱ H hm hp hq n).eval s ω) := by
        rw [hQeval n s ω]; ring
      rw [hrw, nnnorm_mul, nnnorm_neg, ENNReal.coe_mul, mul_pow]
      gcongr
      exact hbd s ω
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ?_
      (Filter.Eventually.of_forall fun n => bot_le) (Filter.Eventually.of_forall hkey)
    have hml := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal B ^ 2)
      (masterApprox_eval_tendsto ℱ H hm hp hq ht.le) (Or.inr hne)
    simpa using hml
  -- (e) the product elementary integrals converge to the integral against the `L²` integral
  have hu_nn : ∀ i : Fin G.N, 0 ≤ min (G.partition i.succ) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hu_nn' : ∀ i : Fin G.N, 0 ≤ min (G.partition i.castSucc) t :=
    fun i => le_min (G.partition_nonneg _) ht.le
  have hstep : ∀ n : ℕ, (fun ω => simpleIntegral W (Q n) t ω
      - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
      = ∑ i : Fin G.N,
        ((fun ω => G.ξ i ω * (simpleIntegral W (masterApprox ℱ H hm hp hq n)
            (min (G.partition i.succ) t) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω))
        - (fun ω => G.ξ i ω * (simpleIntegral W (masterApprox ℱ H hm hp hq n)
            (min (G.partition i.castSucc) t) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq
              (min (G.partition i.castSucc) t) ω))) := by
    intro n
    funext ω
    simp only [Finset.sum_apply, Pi.sub_apply]
    rw [← hQint n t ω]
    unfold SimplePredictable.integralAgainst
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hbound : ∀ n : ℕ, MeasureTheory.eLpNorm (fun ω => simpleIntegral W (Q n) t ω
      - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P
      ≤ ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P) := by
    intro n
    have haesm : ∀ (i : Fin G.N) (u : ℝ), MeasureTheory.AEStronglyMeasurable
        (fun ω => G.ξ i ω * (simpleIntegral W (masterApprox ℱ H hm hp hq n) u ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq u ω)) P :=
      fun i u => ((G.ξ_measurable i).mul ((hInmeas n u).sub (hMmeas u))).aestronglyMeasurable
    rw [hstep n]
    refine le_trans (MeasureTheory.eLpNorm_sum_le
      (fun i _ => (haesm i _).sub (haesm i _)) (by norm_num)) ?_
    refine Finset.sum_le_sum fun i _ => ?_
    refine le_trans (MeasureTheory.eLpNorm_sub_le (haesm i _) (haesm i _) (by norm_num)) ?_
    exact add_le_add (eLpNorm_mul_le_of_bound (hMb i)) (eLpNorm_mul_le_of_bound (hMb i))
  have hlim : Filter.Tendsto (fun n : ℕ =>
      ∑ i : Fin G.N, ((‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.succ) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min (G.partition i.succ) t) ω) 2 P
        + (‖Mb i‖₊ : ℝ≥0∞) * MeasureTheory.eLpNorm (fun ω =>
          simpleIntegral W (masterApprox ℱ H hm hp hq n) (min (G.partition i.castSucc) t) ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq
                (min (G.partition i.castSucc) t) ω) 2 P)) Filter.atTop (nhds 0) := by
    have h0 : (0 : ℝ≥0∞) = ∑ _i : Fin G.N, (0 : ℝ≥0∞) := by simp
    rw [h0]
    refine tendsto_finsetSum _ fun i _ => ?_
    have h1 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn i)) (Or.inr ENNReal.coe_ne_top)
    have h2 := ENNReal.Tendsto.const_mul (a := (‖Mb i‖₊ : ℝ≥0∞))
      (masterApprox_tendsto_L2 W ℱ hℱ H hm hp hq (hu_nn' i)) (Or.inr ENNReal.coe_ne_top)
    simpa using h1.add h2
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω =>
      simpleIntegral W (Q n) t ω
        - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω) 2 P)
      Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall hbound)
  have he : Filter.Tendsto (fun n => ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
      - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    have h2 := ENNReal.Tendsto.mul heL (Or.inr (by simp)) heL (Or.inr (by simp))
    simpa [hconv] using h2
  -- squeeze the two limits together
  have hle : ∫⁻ ω,
      (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P ≤ 0 := by
    have hlim2 : Filter.Tendsto (fun n => 2 * ((∫⁻ ω, (‖simpleIntegral W (Q n) t ω
          - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
            : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
          - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)) Filter.atTop (nhds 0) := by
      have h3 := ENNReal.Tendsto.const_mul (a := 2) (he.add hd) (Or.inr (by simp))
      simpa using h3
    refine ge_of_tendsto hlim2 (Filter.Eventually.of_forall fun n => ?_)
    have hm2 : AEMeasurable (fun ω => (‖simpleIntegral W (Q n) t ω
        - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
          : ℝ≥0∞) ^ 2) P :=
      ((((hQmeas n).sub hIAmeas).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.aemeasurable
    calc ∫⁻ ω, (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
          - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
              hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, 2 * ((‖simpleIntegral W (Q n) t ω
              - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2
            + (‖simpleIntegral W (Q n) t ω
              - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have hrw : G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
                - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                    hmm hmp hmq t ω
              = -(simpleIntegral W (Q n) t ω
                    - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω)
                + (simpleIntegral W (Q n) t ω
                    - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                        hmm hmp hmq t ω) := by ring
          rw [hrw]
          refine le_trans (sq_nnnorm_add_le_two_mul_brownian _ _) ?_
          rw [nnnorm_neg]
      _ = 2 * ((∫⁻ ω, (‖simpleIntegral W (Q n) t ω
              - G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω‖₊
                : ℝ≥0∞) ^ 2 ∂P)
            + ∫⁻ ω, (‖simpleIntegral W (Q n) t ω
              - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
                  hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) := by
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hm2]
  have hzero : ∫⁻ ω,
      (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P = 0 := le_antisymm hle bot_le
  have hSIm : Measurable (stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => G.eval s ω * H ω s) hmm hmp hmq t) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
      hmm hmp hmq t).mono (ℱ.le t)).measurable
  have hmeas : Measurable fun ω =>
      (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
        - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
            hmm hmp hmq t ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((hIAmeas.sub hSIm).nnnorm).coe_nnreal_ennreal).pow_const 2
  filter_upwards [(lintegral_eq_zero_iff hmeas).mp hzero] with ω hω
  have h0 : (‖G.integralAgainst (stochasticIntegralBrownian W ℱ hℱ H hm hp hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => G.eval s ω * H ω s)
          hmm hmp hmq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa using hω
  simpa [sub_eq_zero] using h0

end Associativity

/-- The simple integrand `1_{(a, b]}`, for `0 < a < b`. -/
noncomputable def stepIoc (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    SimplePredictable Ω b where
  N := 2
  partition := ![0, a, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    · simpa using ha
    · simpa using hab
  ξ := ![fun _ => 0, fun _ => 1]
  ξ_bounded := by intro i; fin_cases i <;> exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i <;> exact measurable_const

/-- The simple integrand `1_{(0, b]}`, for `0 < b`. -/
noncomputable def stepIoc₀ (Ω) [MeasurableSpace Ω] {b : ℝ} (hb : 0 < b) :
    SimplePredictable Ω b where
  N := 1
  partition := ![0, b]
  partition_zero := by simp
  partition_le_T := by simp
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    fin_cases i
    simpa using hb
  ξ := ![fun _ => 1]
  ξ_bounded := by intro i; fin_cases i; exact ⟨1, fun ω => by norm_num⟩
  ξ_measurable := by intro i; fin_cases i; exact measurable_const

theorem stepIoc_eval {a b : ℝ} (ha : 0 < a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (stepIoc Ω ha hab).eval s ω
      = ∑ i : Fin 2, if (![0, a, b] : Fin 3 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, a, b] : Fin 3 → ℝ) i.succ
          then (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_two]
  by_cases h : a < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Fin.isValue,
      Matrix.cons_val_two, Matrix.tail_cons, Fin.castSucc_zero, Fin.succ_zero_eq_one,
      Fin.castSucc_one, Fin.succ_one_eq_two]
    simp only [ite_self, zero_add]
    exact if_neg h

theorem stepIoc₀_eval {b : ℝ} (hb : 0 < b) (s : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).eval s ω = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s := by
  have hrw : (stepIoc₀ Ω hb).eval s ω
      = ∑ i : Fin 1, if (![0, b] : Fin 2 → ℝ) i.castSucc < s
            ∧ s ≤ (![0, b] : Fin 2 → ℝ) i.succ
          then (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω else 0 := rfl
  rw [hrw, Fin.sum_univ_one]
  by_cases h : (0 : ℝ) < s ∧ s ≤ b
  · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
    simp [h]
  · rw [Set.indicator_of_notMem fun hm => h (Set.mem_Ioc.mp hm)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue,
      Fin.castSucc_zero, Fin.succ_zero_eq_one]
    exact if_neg h

theorem stepIoc_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 < a)
    (hab : a < b) :
    ∀ i : Fin (stepIoc Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc Ω ha hab).partition i.castSucc)) ((stepIoc Ω ha hab).ξ i) := by
  intro i
  fin_cases i <;> exact MeasureTheory.stronglyMeasurable_const

theorem stepIoc₀_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {b : ℝ} (hb : 0 < b) :
    ∀ i : Fin (stepIoc₀ Ω hb).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIoc₀ Ω hb).partition i.castSucc)) ((stepIoc₀ Ω hb).ξ i) := by
  intro i
  fin_cases i
  exact MeasureTheory.stronglyMeasurable_const

theorem stepIoc_integralAgainst {a b : ℝ} (ha : 0 < a) (hab : a < b) (M : ℝ → Ω → ℝ)
    (t : ℝ) (ω : Ω) :
    (stepIoc Ω ha hab).integralAgainst M t ω = M (min b t) ω - M (min a t) ω := by
  have hrw : (stepIoc Ω ha hab).integralAgainst M t ω
      = ∑ i : Fin 2, (![fun _ => (0 : ℝ), fun _ => (1 : ℝ)] : Fin 2 → Ω → ℝ) i ω
        * (M (min ((![0, a, b] : Fin 3 → ℝ) i.succ) t) ω
          - M (min ((![0, a, b] : Fin 3 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_two]
  simp

theorem stepIoc₀_integralAgainst {b : ℝ} (hb : 0 < b) (M : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    (stepIoc₀ Ω hb).integralAgainst M t ω = M (min b t) ω - M (min 0 t) ω := by
  have hrw : (stepIoc₀ Ω hb).integralAgainst M t ω
      = ∑ i : Fin 1, (![fun _ => (1 : ℝ)] : Fin 1 → Ω → ℝ) i ω
        * (M (min ((![0, b] : Fin 2 → ℝ) i.succ) t) ω
          - M (min ((![0, b] : Fin 2 → ℝ) i.castSucc) t) ω) := rfl
  rw [hrw, Fin.sum_univ_one]
  simp

/-- The `L²` Itô integral depends on the integrand only through the function itself. -/
theorem stochasticIntegralBrownian_congr_fun
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {F₁ F₂ : Ω → ℝ → ℝ} (hEq : F₁ = F₂)
    (hm₁ : Measurable (Function.uncurry F₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ F₁)
    (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry F₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ F₂)
    (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) :
    stochasticIntegralBrownian W ℱ hℱ F₁ hm₁ hp₁ hq₁ t
      = stochasticIntegralBrownian W ℱ hℱ F₂ hm₂ hp₂ hq₂ t := by
  subst hEq; rfl

/-- **Locality of the `L²` Itô integral.** Restricting the integrand to `(a, b]` gives the
increment of the integral across `(a, b]`. -/
theorem stochasticIntegralBrownian_indicator_Ioc
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (him : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s))
    (hip : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
    (hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) him hip hiq t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min b t) ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min a t) ω := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · have hfun : (fun ω s => (stepIoc₀ Ω hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [stepIoc₀_eval]
    have hpt : ∀ (ω : Ω) (s : ℝ), (stepIoc₀ Ω hab).eval s ω * H ω s
        = (Set.Ioc 0 b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (stepIoc₀ Ω hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (stepIoc₀ Ω hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc₀ Ω hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := stochasticIntegralBrownian_integralAgainst W ℱ hℱ (stepIoc₀ Ω hab)
      (stepIoc₀_adapt ℱ hab) H hm hp hq him' hip' hiq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => stepIoc₀_integralAgainst hab _ t ω)
  · have hfun : (fun ω s => (stepIoc Ω ha' hab).eval s ω * H ω s)
        = fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s := by
      funext ω s; rw [stepIoc_eval]
    have hpt : ∀ (ω : Ω) (s : ℝ), (stepIoc Ω ha' hab).eval s ω * H ω s
        = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
      fun ω s => congrFun (congrFun hfun ω) s
    have him' : Measurable
        (Function.uncurry fun ω s => (stepIoc Ω ha' hab).eval s ω * H ω s) := by
      rw [hfun]; exact him
    have hip' : Probability.ProgressivelyMeasurable ℱ
        (fun ω s => (stepIoc Ω ha' hab).eval s ω * H ω s) := by rw [hfun]; exact hip
    have hiq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(stepIoc Ω ha' hab).eval s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT; simp_rw [hpt]; exact hiq T hT
    have hkey := stochasticIntegralBrownian_integralAgainst W ℱ hℱ (stepIoc Ω ha' hab)
      (stepIoc_adapt ℱ ha' hab) H hm hp hq him' hip' hiq' ht
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hfun him' hip' hiq' him hip hiq t] at hkey
    exact hkey.symm.trans
      (Filter.Eventually.of_forall fun ω => stepIoc_integralAgainst ha' hab _ t ω)

end LevyStochCalc.Brownian.Ito
