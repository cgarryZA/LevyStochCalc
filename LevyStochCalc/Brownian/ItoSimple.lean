/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Multidim

/-!
# Brownian Itô integral on simple predictable integrands

The simple predictable integrands `∑_i ξ_i · 1_{(t_i, t_{i+1}]}` for a scalar
Brownian motion `W`, their integral `simpleIntegral`, and the L²-isometry on
this class (`simpleIntegral_isometry`, `simpleIntegral_L2_isometry_brownian`).
L²-density of simple predictables is in `Brownian/ItoDensity.lean`; the
martingale property in `Brownian/ItoMartingale.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A *simple predictable* integrand: a finite linear combination
`∑_i ξ_i · 1_{(t_i, t_{i+1}]}` where `ξ_i : Ω → ℝ` is `ℱ_{t_i}`-measurable
and bounded. We package the partition + the per-piece coefficient. -/
structure SimplePredictable (Ω : Type u) [MeasurableSpace Ω] (T : ℝ) where
  /-- Number of partition pieces. -/
  N : ℕ
  /-- Partition points `0 = t_0 < t_1 < ⋯ < t_N ≤ T`. -/
  partition : Fin (N + 1) → ℝ
  partition_zero : partition 0 = 0
  partition_le_T : partition (Fin.last N) ≤ T
  partition_strictMono : StrictMono partition
  /-- Per-piece bounded coefficients `ξ_i : Ω → ℝ`. -/
  ξ : Fin N → Ω → ℝ
  /-- Each `ξ_i` is bounded. -/
  ξ_bounded : ∀ i : Fin N, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M
  /-- Each `ξ_i` is measurable. (The full `ℱ_{t_i}`-measurability requires
  the natural filtration of `W`; for the L²-density argument the ambient
  measurability suffices.) -/
  ξ_measurable : ∀ i : Fin N, Measurable (ξ i)

/-- Evaluate a simple predictable integrand at a fixed time. -/
noncomputable def SimplePredictable.eval {T : ℝ} (H : SimplePredictable Ω T)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin H.N,
    if H.partition i.castSucc < t ∧ t ≤ H.partition i.succ then H.ξ i ω else 0

/-- Integral of a simple predictable integrand against Brownian motion `W`:
`∑_i ξ_i (W_{t_{i+1}∧t} − W_{t_i∧t})`. -/
noncomputable def simpleIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ i : Fin H.N,
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
              - W.W (min (H.partition i.castSucc) t) ω)

/-- **`simpleIntegral` at time `T` collapses the `min` clauses.** Since
`partition_le_T` ensures `partition i.succ ≤ T` and `partition i.castSucc ≤ T`
for all `i : Fin H.N`, the `min` becomes the partition value. -/
lemma simpleIntegral_eq_sum
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    simpleIntegral W H T ω
      = ∑ i : Fin H.N,
        H.ξ i ω * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) := by
  unfold simpleIntegral
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h_part_le_succ : H.partition i.succ ≤ T := by
    refine le_trans ?_ H.partition_le_T
    exact H.partition_strictMono.monotone (Fin.le_last _)
  have h_part_le_castSucc : H.partition i.castSucc ≤ T :=
    le_of_lt ((H.partition_strictMono Fin.castSucc_lt_succ).trans_le h_part_le_succ)
  rw [min_eq_left h_part_le_succ, min_eq_left h_part_le_castSucc]

/-- **Eval as a sum of indicators.** Rewrite `H.eval s ω` as a sum of
indicator-functions of disjoint intervals `(t_i, t_{i+1}]`. -/
lemma eval_eq_sum_indicator {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    H.eval s ω = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => H.ξ i ω) s := by
  unfold SimplePredictable.eval
  refine Finset.sum_congr rfl (fun i _ => ?_)
  by_cases h : H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
  · rw [if_pos h]
    rw [Set.indicator_of_mem (Set.mem_Ioc.mpr h)]
  · rw [if_neg h]
    rw [Set.indicator_of_notMem (fun hmem => h (Set.mem_Ioc.mp hmem))]

/-- **Disjoint intervals.** The intervals `(t_i, t_{i+1}]` for
`i : Fin H.N` are pairwise disjoint. -/
lemma partition_intervals_disjoint {T : ℝ} (H : SimplePredictable Ω T) :
    Pairwise (fun i j : Fin H.N => Disjoint
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
      (Set.Ioc (H.partition j.castSucc) (H.partition j.succ))) := by
  intro i j hij
  -- WLOG i < j (or j < i); then partition i.succ ≤ partition j.castSucc.
  rcases lt_or_gt_of_ne hij with h | h
  · -- i < j: i.succ ≤ j.castSucc, so (t_i, t_{i+1}] is to the left of (t_j, t_{j+1}]
    have h_succ_le : H.partition i.succ ≤ H.partition j.castSucc :=
      H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x ⟨hx_i, hx_j⟩
    obtain ⟨_, hx_i_le⟩ := Set.mem_Ioc.mp hx_i
    obtain ⟨hx_j_lt, _⟩ := Set.mem_Ioc.mp hx_j
    -- hx_i_le : x ≤ t_{i+1}, hx_j_lt : t_j < x. Combined with h_succ_le: contradiction.
    have : x ≤ H.partition j.castSucc := hx_i_le.trans h_succ_le
    exact absurd this (not_le.mpr hx_j_lt)
  · -- j < i: symmetric
    have h_succ_le : H.partition j.succ ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
    rw [Set.disjoint_iff]
    intro x ⟨hx_i, hx_j⟩
    obtain ⟨hx_i_lt, _⟩ := Set.mem_Ioc.mp hx_i
    obtain ⟨_, hx_j_le⟩ := Set.mem_Ioc.mp hx_j
    have : x ≤ H.partition i.castSucc := hx_j_le.trans h_succ_le
    exact absurd this (not_le.mpr hx_i_lt)

/-- **`‖H.eval s ω‖₊²` decomposes as a sum of indicator-squares** because
the partition intervals are pairwise disjoint, so at most one summand of
`H.eval` is nonzero at any `s`. -/
lemma eval_sq_eq_sum_indicator
    {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s := by
  rw [eval_eq_sum_indicator]
  -- (∑ i, indicator A_i s · ξ_i ω)² with disjoint A_i.
  -- At most one indicator is nonzero at any s, so the square equals
  -- ∑ i, indicator A_i s · (ξ_i ω)².
  by_cases h_any : ∃ i : Fin H.N, s ∈ Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
  · obtain ⟨i₀, hi₀⟩ := h_any
    -- At i₀, indicator gives ξ_{i₀}; at all other j, indicator gives 0 (by disjointness).
    have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
        s ∉ Set.Ioc (H.partition j.castSucc) (H.partition j.succ) := by
      intro j hj hj_mem
      have := partition_intervals_disjoint H hj
      exact Set.disjoint_left.mp this hj_mem hi₀
    have h_sum_eq : (∑ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => H.ξ i ω) s) = H.ξ i₀ ω := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    have h_sum_sq_eq : (∑ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s)
        = (‖H.ξ i₀ ω‖₊ : ℝ≥0∞) ^ 2 := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq, h_sum_sq_eq]
  · -- s is in none of the intervals; both sides are 0.
    push Not at h_any
    have h_zero : ∀ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => H.ξ i ω) s = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    have h_zero_sq : ∀ i : Fin H.N,
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
          (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s = 0 :=
      fun i => Set.indicator_of_notMem (h_any i) _
    rw [Finset.sum_eq_zero (fun i _ => h_zero i),
        Finset.sum_eq_zero (fun i _ => h_zero_sq i)]
    simp

/-- **Inner lintegral of `‖H.eval s ω‖₊²` over `s ∈ [0, T]`** equals the sum
of `(t_{i+1} - t_i) · ‖ξ_i ω‖₊²` over partition pieces. -/
lemma lintegral_eval_sq {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 := by
  -- Step 1: rewrite |H.eval|² as sum of indicators using `eval_sq_eq_sum_indicator`.
  rw [show (fun s => (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun s => ∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s) from
    funext (eval_sq_eq_sum_indicator H · ω)]
  -- Step 2: pull sum out of lintegral.
  rw [MeasureTheory.lintegral_finsetSum]
  · -- Step 3: each summand evaluates to (t_{i+1} - t_i) · ‖ξ_i‖²
    refine Finset.sum_congr rfl (fun i _ => ?_)
    -- ∫⁻ s in [0, T], indicator (t_i, t_{i+1}] · |ξ_i|² ds = |ξ_i|² · vol((t_i, t_{i+1}])
    have h_meas_set : MeasurableSet
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)) := measurableSet_Ioc
    have h_subset : Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
        ⊆ Set.Icc (0 : ℝ) T := by
      intro x hx
      have h_part_zero_le : 0 ≤ H.partition i.castSucc := by
        have : H.partition 0 ≤ H.partition i.castSucc :=
          H.partition_strictMono.monotone (Fin.zero_le _)
        rw [H.partition_zero] at this; exact this
      have h_part_succ_le_T : H.partition i.succ ≤ T := by
        refine le_trans ?_ H.partition_le_T
        exact H.partition_strictMono.monotone (Fin.le_last _)
      refine ⟨?_, ?_⟩
      · exact h_part_zero_le.trans (le_of_lt hx.1)
      · exact hx.2.trans h_part_succ_le_T
    rw [show (fun s => (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
              (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s)
          = (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
              (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) from rfl]
    rw [MeasureTheory.lintegral_indicator h_meas_set]
    rw [MeasureTheory.setLIntegral_const]
    rw [show volume.restrict (Set.Icc (0 : ℝ) T)
            (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
          = volume (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)) from ?_]
    · rw [Real.volume_Ioc]
      ring
    · rw [MeasureTheory.Measure.restrict_apply h_meas_set]
      congr 1
      exact Set.inter_eq_left.mpr h_subset
  · -- Step 4: each term is measurable.
    intro i _
    refine Measurable.indicator ?_ measurableSet_Ioc
    fun_prop

/-- **Outer lintegral of `‖H.eval‖₊²` over `Ω × [0,T]`** equals the sum of
`ENNReal.ofReal(t_{i+1} - t_i) · ∫⁻ ‖ξ_i‖₊² ∂P`. This is the RHS reduction
of `simpleIntegral_isometry`. -/
lemma lintegral_eval_sq_outer
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (H : SimplePredictable Ω T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      = (fun ω => ∑ i : Fin H.N,
          ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
          (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) from
    funext (fun ω => lintegral_eval_sq H ω)]
  rw [MeasureTheory.lintegral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [MeasureTheory.lintegral_const_mul']
    exact ENNReal.ofReal_ne_top
  · intro i _
    refine Measurable.const_mul ?_ _
    exact (H.ξ_measurable i).enorm.pow_const 2

/-- The simple integral at time `0` is identically zero (each term is
`ξ_i · (W_{0∧0} − W_{0∧0}) = ξ_i · 0`). -/
lemma simpleIntegral_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    simpleIntegral W H 0 ω = 0 := by
  unfold simpleIntegral
  -- Each summand: ξ_i ω · (W (min partition_succ 0) ω − W (min partition_castSucc 0) ω).
  -- By H.partition_zero = 0 and H.partition_strictMono, partition i ≥ 0 for i ≥ 0,
  -- so min(partition_succ, 0) = 0 and similarly for castSucc.
  -- Hence each term is ξ_i ω · (W 0 ω − W 0 ω) = ξ_i ω · 0 = 0.
  apply Finset.sum_eq_zero
  intro i _
  -- Show: H.partition i.succ ≥ 0 and H.partition i.castSucc ≥ 0.
  have h_zero_le_castSucc : H.partition 0 ≤ H.partition i.castSucc :=
    H.partition_strictMono.monotone (Fin.zero_le i.castSucc)
  have h_zero_le_succ : H.partition 0 ≤ H.partition i.succ :=
    H.partition_strictMono.monotone (Fin.zero_le i.succ)
  rw [H.partition_zero] at h_zero_le_castSucc h_zero_le_succ
  rw [min_eq_right h_zero_le_succ, min_eq_right h_zero_le_castSucc]
  ring

/-- Diagonal contribution: `E[ξ_i² · (W_{t_{i+1}} − W_{t_i})²]
= (t_{i+1} − t_i) · E[ξ_i²]`.

Proof: `(W_{t_{i+1}} − W_{t_i})²` is independent of `ξ_i²` (since the
increment is independent of `W_{t_i}`-past, and `ξ_i` is `F_{t_i}`-meas
by hypothesis `h_adapt`). The increment squared has expectation
`(t_{i+1} − t_i)` (Gaussian variance via `gaussianReal_second_moment`).

Hypotheses for the proof (added beyond what `SimplePredictable` provides):
* `h_part_nn`: the left endpoint `t_i := partition i.castSucc ≥ 0`,
  so the increment law applies.
* `h_adapt`: `ξ_i` is `(naturalFiltration W).seq t_i`-measurable. -/
lemma simpleIntegral_diagonal
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_part_nn : 0 ≤ H.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω,
      (‖H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set s : ℝ := H.partition i.castSucc with hs_def
  set t : ℝ := H.partition i.succ with ht_def
  set ΔW : Ω → ℝ := fun ω => W.W t ω - W.W s ω with hΔW_def
  set ξ : Ω → ℝ := H.ξ i with hξ_def
  have hst : s < t := H.partition_strictMono Fin.castSucc_lt_succ
  have h_ξ_meas : Measurable ξ := H.ξ_measurable i
  have h_ΔW_meas : Measurable ΔW := (W.measurable_eval t).sub (W.measurable_eval s)
  -- Step 1: Show IndepFun ξ ΔW.
  -- By h_adapt, σ(ξ) ⊆ F_s. By joint_increment_independent, F_s ⊥ σ(ΔW).
  -- So σ(ξ) ⊥ σ(ΔW), i.e., IndepFun ξ ΔW.
  have h_indep_F_ΔW := W.joint_increment_independent h_part_nn hst
  have h_ξ_comap_le :
      MeasurableSpace.comap ξ inferInstance ≤
        ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W.W j) inferInstance := by
    -- ξ is F_s-measurable, where F_s = ⨆ j ≤ s, σ(W_j)
    have h_ξ_F_meas : @Measurable Ω ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s) _ ξ :=
      h_adapt.measurable
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have h_naturalFilter_eq :
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s
          = ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W.W j) inferInstance := by
      show (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s = _
      unfold LevyStochCalc.Brownian.Martingale.naturalFiltration
        MeasureTheory.Filtration.natural
      rfl
    rw [← h_naturalFilter_eq]
    exact h_ξ_F_meas hv
  have h_indep_ξ_ΔW : ProbabilityTheory.IndepFun ξ ΔW P := by
    -- Indep σ(ξ) σ(ΔW) P, using h_indep_F_ΔW and σ(ξ) ⊆ F_s.
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : @MeasurableSet Ω
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W.W j) inferInstance) u :=
      h_ξ_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW
    exact h_indep_F_ΔW u v hu_F hv
  -- Step 2: Compose with norm² to get IndepFun on ENNReal.
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2)
        (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) P := by
    have := h_indep_ξ_ΔW.comp h_nn_meas h_nn_meas
    simpa [Function.comp_def] using this
  -- Step 3: ‖ξ · ΔW‖₊² = ‖ξ‖₊² · ‖ΔW‖₊² pointwise.
  have h_norm_mul : ∀ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)^2
      = (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 := by
    intro ω
    rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
        = (‖ξ ω‖₊ : ℝ≥0∞) * (‖ΔW ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
          = ((‖ξ ω * ΔW ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0)
          = ‖ξ ω‖₊ * ‖ΔW ω‖₊ from nnnorm_mul _ _]
      push_cast; rfl]
    ring
  -- Step 4: Apply lintegral_mul for IndepFun.
  rw [show (∫⁻ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2)
      = (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2)
        * (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) from rfl]
  have h_ξ_norm_sq_meas : Measurable (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_ΔW_norm_sq_meas : Measurable (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξ_norm_sq_meas h_ΔW_norm_sq_meas h_indep_norm_sq]
  -- Step 5: Compute ∫⁻ ‖ΔW‖₊² ∂P = ENNReal.ofReal(t - s).
  have h_ΔW_sq_int : ∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P
      = ENNReal.ofReal (t - s) := by
    -- Pushforward to gaussianReal:
    -- ∫⁻ ω, ‖ΔW‖₊² ∂P = ∫⁻ x, ‖x‖₊² ∂(P.map ΔW)
    --   = ∫⁻ x, ‖x‖₊² ∂(gaussianReal 0 ⟨t-s, _⟩)
    rw [show (∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ x, (‖x‖₊ : ℝ≥0∞)^2 ∂(P.map ΔW) from
      (MeasureTheory.lintegral_map h_nn_meas h_ΔW_meas).symm]
    rw [W.increment_gaussian h_part_nn hst]
    -- ∫⁻ x, ‖x‖₊² ∂(gaussianReal 0 v) = ENNReal.ofReal v.
    -- Via ENNReal.ofReal of ∫ x², which equals v by gaussianReal_second_moment.
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x^2)
        (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
        ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1
      ext x
      change x^2 = ‖x‖^2
      rw [Real.norm_eq_abs, sq_abs]
    have h_nn_sq : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩]
        fun x : ℝ => x^2 := by
      filter_upwards with x
      positivity
    have h_norm_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := by
      intro x
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from
            ofReal_norm x |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ x, (‖x‖₊ : ℝ≥0∞)^2 ∂(ProbabilityTheory.gaussianReal 0
                ⟨t - s, by linarith⟩))
        = ∫⁻ x, ENNReal.ofReal (x^2) ∂(ProbabilityTheory.gaussianReal 0
                ⟨t - s, by linarith⟩) from
      MeasureTheory.lintegral_congr (fun x => h_norm_eq x)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq h_nn_sq]
    rw [LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨t - s, by linarith⟩]
    rfl
  rw [h_ΔW_sq_int]
  ring

/-- **Integrability of Brownian increment squared.** For `0 ≤ s < t`,
`(W_t − W_s)² ∈ L¹(P)`. Pushforward + Gaussian `MemLp 2`. -/
lemma brownian_increment_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (h_s_nn : 0 ≤ s) (h_st : s < t) :
    MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω)^2) P := by
  have h_meas : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  have h_law := W.increment_gaussian h_s_nn h_st
  -- Convert to integrability on the pushforward measure (gaussianReal).
  have h_x_sq_meas : Measurable (fun x : ℝ => x^2) :=
    measurable_id.pow_const 2
  rw [show (fun ω => (W.W t ω - W.W s ω)^2)
        = (fun x : ℝ => x^2) ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
  rw [(MeasureTheory.integrable_map_measure (μ := P)
      (f := fun ω => W.W t ω - W.W s ω)
      h_x_sq_meas.aestronglyMeasurable h_meas.aemeasurable).symm]
  rw [h_law]
  -- Integrable (fun x => x²) (gaussianReal 0 ⟨t-s, _⟩) via MemLp 2 of id.
  have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
      (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :=
    ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
  have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
  convert h using 1
  ext x
  change x^2 = ‖x‖^2
  rw [Real.norm_eq_abs, sq_abs]

/-- **Bochner version of `simpleIntegral_diagonal`** for Brownian. -/
private lemma simpleIntegral_diagonal_bochner
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_part_nn : 0 ≤ H.partition i.castSucc)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω))^2 ∂P
      = (H.partition i.succ - H.partition i.castSucc) *
        ∫ ω, (H.ξ i ω)^2 ∂P := by
  have hst : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  -- Common identity.
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  have h_lint := simpleIntegral_diagonal W H i h_part_nn h_adapt
  rw [show (∫⁻ ω, (‖H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞)^2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((H.ξ i ω)^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  -- Integrabilities.
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (H.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (H.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_int_ΔW_sq : MeasureTheory.Integrable
      (fun ω => (W.W (H.partition i.succ) ω
                - W.W (H.partition i.castSucc) ω)^2) P :=
    brownian_increment_sq_integrable W h_part_nn hst
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                - W.W (H.partition i.castSucc) ω))^2) P := by
    have h_eq : ∀ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2
              = (H.ξ i ω)^2 *
                (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)^2 := fun ω => by ring
    rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2)
            = fun ω => (H.ξ i ω)^2 *
                (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)^2 from funext h_eq]
    refine MeasureTheory.Integrable.bdd_mul (c := M^2) h_int_ΔW_sq
      ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 := by
    filter_upwards with ω; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  -- Combine ENNReal.ofReal of constant * ofReal of integral.
  have h_xi_int_nn : 0 ≤ ∫ ω, (H.ξ i ω)^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_aN_int_nn : 0 ≤ ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 ∂P :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)
  have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc := sub_nonneg.mpr (le_of_lt hst)
  rw [show ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
          ENNReal.ofReal (∫ ω, (H.ξ i ω)^2 ∂P)
          = ENNReal.ofReal
              ((H.partition i.succ - H.partition i.castSucc) *
                ∫ ω, (H.ξ i ω)^2 ∂P) from
    (ENNReal.ofReal_mul h_dt_nn).symm] at h_lint
  have h_rhs_nn : 0 ≤ (H.partition i.succ - H.partition i.castSucc) *
                      ∫ ω, (H.ξ i ω)^2 ∂P :=
    mul_nonneg h_dt_nn h_xi_int_nn
  exact (ENNReal.ofReal_eq_ofReal_iff h_aN_int_nn h_rhs_nn).mp h_lint

/-- Off-diagonal vanishing: for `i < j`,
`E[ξ_i ξ_j · ΔW_i · ΔW_j] = 0`.

Proof: `ξ_j` is `F_{t_j}`-measurable, `ΔW_j ⊥ F_{t_j}` (independence of
increment from past), and `E[ΔW_j] = 0` (Gaussian mean). Then
`E[ξ_i ξ_j ΔW_i ΔW_j | F_{t_j}] = ξ_i ξ_j ΔW_i · E[ΔW_j | F_{t_j}]
= ξ_i ξ_j ΔW_i · 0 = 0`. -/
lemma simpleIntegral_offDiagonal
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {i j : Fin H.N} (hij : i < j)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    (h_adapt_j : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition j.castSucc)) (H.ξ j)) :
    ∫ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω)) *
         (H.ξ j ω * (W.W (H.partition j.succ) ω
                    - W.W (H.partition j.castSucc) ω)) ∂P = 0 := by
  set t_i_pre : ℝ := H.partition i.castSucc with hti0_def
  set t_i : ℝ := H.partition i.succ with hti_def
  set t_j_pre : ℝ := H.partition j.castSucc with htj0_def
  set t_j : ℝ := H.partition j.succ with htj_def
  set ΔW_i : Ω → ℝ := fun ω => W.W t_i ω - W.W t_i_pre ω
  set ΔW_j : Ω → ℝ := fun ω => W.W t_j ω - W.W t_j_pre ω
  set ξ_i : Ω → ℝ := H.ξ i
  set ξ_j : Ω → ℝ := H.ξ j
  -- Partition monotonicity
  have h_part_zero_le_i_pre : 0 ≤ t_i_pre := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_i_pre_lt : t_i_pre < t_i := H.partition_strictMono Fin.castSucc_lt_succ
  have h_i_le_j_pre : t_i ≤ t_j_pre := by
    apply H.partition_strictMono.monotone
    exact Fin.succ_le_castSucc_iff.mpr hij
  have h_j_pre_lt : t_j_pre < t_j := H.partition_strictMono Fin.castSucc_lt_succ
  have h_j_pre_nn : 0 ≤ t_j_pre := h_part_zero_le_i_pre.trans (le_of_lt h_i_pre_lt)
    |>.trans h_i_le_j_pre
  -- The integrand factors as f · ΔW_j where f := ξ_i · ΔW_i · ξ_j.
  -- f is F_{t_j_pre}-measurable.
  set f : Ω → ℝ := fun ω => ξ_i ω * ΔW_i ω * ξ_j ω
  have h_factored : (fun ω => (ξ_i ω * ΔW_i ω) * (ξ_j ω * ΔW_j ω))
      = fun ω => f ω * ΔW_j ω := by
    funext ω
    change (ξ_i ω * ΔW_i ω) * (ξ_j ω * ΔW_j ω)
      = ξ_i ω * ΔW_i ω * ξ_j ω * ΔW_j ω
    ring
  rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                      - W.W (H.partition i.castSucc) ω))
              * (H.ξ j ω * (W.W (H.partition j.succ) ω
                          - W.W (H.partition j.castSucc) ω)))
        = fun ω => f ω * ΔW_j ω from h_factored]
  -- Step 1: f is F_{t_j_pre}-measurable.
  have h_t_i_pre_le_t_j_pre : t_i_pre ≤ t_j_pre :=
    (le_of_lt h_i_pre_lt).trans h_i_le_j_pre
  have h_F_i_pre_le_j_pre :
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_i_pre
        ≤ (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre :=
    (LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono h_t_i_pre_le_t_j_pre
  -- Use the σ-algebra independence: σ(f) ⊆ F_{t_j_pre}; σ(ΔW_j) ⊥ F_{t_j_pre}.
  -- Then E[f * ΔW_j] = E[f] * E[ΔW_j] = E[f] * 0 = 0.
  -- Setup: F-measurability of pieces.
  have h_W_t_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre) (W.W t_i) := by
    have h := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) t_i
    -- W_t_i is F_{t_i}-meas; F_{t_i} ≤ F_{t_j_pre} (since t_i ≤ t_j_pre)
    refine h.mono ?_
    exact (LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono h_i_le_j_pre
  have h_W_t_pre_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre) (W.W t_i_pre) := by
    have h := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) t_i_pre
    refine h.mono ?_
    exact (LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono
      ((le_of_lt h_i_pre_lt).trans h_i_le_j_pre)
  have h_ΔW_i_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre) ΔW_i :=
    h_W_t_meas.sub h_W_t_pre_meas
  have h_ξ_i_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre) ξ_i :=
    h_adapt_i.mono h_F_i_pre_le_j_pre
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre) f :=
    (h_ξ_i_F_meas.mul h_ΔW_i_F_meas).mul h_adapt_j
  -- Step 2: IndepFun f ΔW_j
  have h_indep_F_ΔW_j := W.joint_increment_independent h_j_pre_nn h_j_pre_lt
  have h_f_meas : Measurable f :=
    ((H.ξ_measurable i).mul ((W.measurable_eval t_i).sub
      (W.measurable_eval t_i_pre))).mul (H.ξ_measurable j)
  have h_ΔW_j_meas : Measurable ΔW_j :=
    (W.measurable_eval t_j).sub (W.measurable_eval t_j_pre)
  have h_f_comap_le :
      MeasurableSpace.comap f inferInstance ≤
        ⨆ jj ∈ Set.Iic t_j_pre, MeasurableSpace.comap (W.W jj) inferInstance := by
    have h_f_F_measurable : @Measurable Ω ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre) _ f :=
      h_f_F_meas.measurable
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have h_naturalFilter_eq :
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre
          = ⨆ jj ∈ Set.Iic t_j_pre, MeasurableSpace.comap (W.W jj) inferInstance := by
      show (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_j_pre = _
      unfold LevyStochCalc.Brownian.Martingale.naturalFiltration
        MeasureTheory.Filtration.natural
      rfl
    rw [← h_naturalFilter_eq]
    exact h_f_F_measurable hv
  have h_indep_f_ΔW_j : ProbabilityTheory.IndepFun f ΔW_j P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : @MeasurableSet Ω
        (⨆ jj ∈ Set.Iic t_j_pre, MeasurableSpace.comap (W.W jj) inferInstance) u :=
      h_f_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW_j
    exact h_indep_F_ΔW_j u v hu_F hv
  -- Step 3: ∫ ΔW_j = 0 (Gaussian mean).
  have h_ΔW_j_mean : ∫ ω, ΔW_j ω ∂P = 0 := by
    rw [show ∫ ω, ΔW_j ω ∂P = ∫ x, x ∂(P.map ΔW_j) from
      (MeasureTheory.integral_map h_ΔW_j_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (id : ℝ → ℝ) _)).symm]
    rw [W.increment_gaussian h_j_pre_nn h_j_pre_lt]
    exact ProbabilityTheory.integral_id_gaussianReal
  -- Step 4: E[f · ΔW_j] = E[f] · E[ΔW_j] = E[f] · 0 = 0.
  rw [show (fun ω => f ω * ΔW_j ω) = f * ΔW_j from rfl]
  rw [h_indep_f_ΔW_j.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW_j_meas.aestronglyMeasurable]
  rw [h_ΔW_j_mean, mul_zero]

/-- **Integrability of cross product `(ξ_i ΔW_i)(ξ_j ΔW_j)`** for Brownian. -/
private lemma cross_sq_integrable
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i j : Fin H.N) :
    MeasureTheory.Integrable
      (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                          - W.W (H.partition i.castSucc) ω)) *
                (H.ξ j ω * (W.W (H.partition j.succ) ω
                          - W.W (H.partition j.castSucc) ω))) P := by
  have h_part_i_nn : 0 ≤ H.partition i.castSucc := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_part_j_nn : 0 ≤ H.partition j.castSucc := by
    have : H.partition 0 ≤ H.partition j.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_st_i : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have h_st_j : H.partition j.castSucc < H.partition j.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have h_int_i_sq := brownian_increment_sq_integrable W h_part_i_nn h_st_i
  have h_int_j_sq := brownian_increment_sq_integrable W h_part_j_nn h_st_j
  -- Integrability of ΔW_i · ΔW_j via AM-GM.
  have h_meas_i : Measurable (fun ω => W.W (H.partition i.succ) ω
                                     - W.W (H.partition i.castSucc) ω) :=
    (W.measurable_eval _).sub (W.measurable_eval _)
  have h_meas_j : Measurable (fun ω => W.W (H.partition j.succ) ω
                                     - W.W (H.partition j.castSucc) ω) :=
    (W.measurable_eval _).sub (W.measurable_eval _)
  have h_int_ΔW : MeasureTheory.Integrable
      (fun ω => (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)
              * (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) P := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1/2 : ℝ))
        (h_int_j_sq.const_mul (1/2 : ℝ))) (h_meas_i.mul h_meas_j).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have : |W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω| *
           |W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω|
        ≤ (1/2) * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)^2 +
          (1/2) * (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)^2 := by
      nlinarith [sq_abs (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω),
                 sq_abs (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω),
                 sq_nonneg (|W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω| -
                            |W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω|)]
    exact this
  -- (ξ_i · ΔW_i) · (ξ_j · ΔW_j) = (ξ_i · ξ_j) · (ΔW_i · ΔW_j). Bounded × integrable.
  obtain ⟨M_i, hM_i⟩ := H.ξ_bounded i
  obtain ⟨M_j, hM_j⟩ := H.ξ_bounded j
  have h_eq : ∀ ω, (H.ξ i ω * (W.W (H.partition i.succ) ω
                              - W.W (H.partition i.castSucc) ω)) *
                   (H.ξ j ω * (W.W (H.partition j.succ) ω
                              - W.W (H.partition j.castSucc) ω))
            = (H.ξ i ω * H.ξ j ω) *
              ((W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) *
              (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) :=
    fun ω => by ring
  rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                 - W.W (H.partition i.castSucc) ω)) *
                     (H.ξ j ω * (W.W (H.partition j.succ) ω
                                 - W.W (H.partition j.castSucc) ω)))
        = fun ω => (H.ξ i ω * H.ξ j ω) *
                   ((W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) *
                   (W.W (H.partition j.succ) ω - W.W (H.partition j.castSucc) ω)) from
    funext h_eq]
  refine MeasureTheory.Integrable.bdd_mul (c := |M_i| * |M_j|) h_int_ΔW
    ((H.ξ_measurable i).mul (H.ξ_measurable j)).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hM_i ω) (le_abs_self _))
    (le_trans (hM_j ω) (le_abs_self _)) (abs_nonneg _) (abs_nonneg _)

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Bochner LHS reduction for Brownian.** -/
private lemma simpleIntegral_sq_bochner_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2 ∂P
      = ∑ i : Fin H.N,
        (H.partition i.succ - H.partition i.castSucc) *
        ∫ ω, (H.ξ i ω)^2 ∂P := by
  -- Expand (∑ a_i)² = ∑_{i,j} a_i a_j via Finset.sum_mul_sum.
  have h_expand : ∀ ω,
      (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2
      = ∑ i : Fin H.N, ∑ j : Fin H.N,
          (H.ξ i ω * (W.W (H.partition i.succ) ω
                    - W.W (H.partition i.castSucc) ω)) *
          (H.ξ j ω * (W.W (H.partition j.succ) ω
                    - W.W (H.partition j.castSucc) ω)) := by
    intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
  rw [show (fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N,
            (H.ξ i ω * (W.W (H.partition i.succ) ω
                      - W.W (H.partition i.castSucc) ω)) *
            (H.ξ j ω * (W.W (H.partition j.succ) ω
                      - W.W (H.partition j.castSucc) ω)) from funext h_expand]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun j _ => cross_sq_integrable W H i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _
    (fun j _ => cross_sq_integrable W H i j)]
  rw [Finset.sum_eq_single i]
  · -- j = i: diagonal Bochner
    have h_part_nn : 0 ≤ H.partition i.castSucc := by
      have : H.partition 0 ≤ H.partition i.castSucc :=
        H.partition_strictMono.monotone (Fin.zero_le _)
      rw [H.partition_zero] at this; exact this
    rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)))
          = fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                - W.W (H.partition i.castSucc) ω))^2 from by
      funext ω; ring]
    exact simpleIntegral_diagonal_bochner W H i h_part_nn (h_adapt i)
  · -- j ≠ i: offDiagonal (with symmetry)
    intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) *
                         (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)))
            = fun ω => (H.ξ j ω * (W.W (H.partition j.succ) ω
                                  - W.W (H.partition j.castSucc) ω)) *
                       (H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) from by
        funext ω; ring]
      exact simpleIntegral_offDiagonal W H h_lt (h_adapt j) (h_adapt i)
    · exact simpleIntegral_offDiagonal W H h_gt (h_adapt i) (h_adapt j)
  · intro h_not; exact absurd (Finset.mem_univ _) h_not

set_option maxHeartbeats 800000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **LHS reduction for Brownian Itô isometry on simples.** -/
lemma simpleIntegral_sq_lintegral_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  -- Expand simpleIntegral via simpleIntegral_eq_sum.
  simp_rw [simpleIntegral_eq_sum W H]
  -- Convert (‖x‖)² to ENNReal.ofReal(x²).
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞)^2 = ENNReal.ofReal (x^2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖^2 = x^2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [show (∫⁻ ω, (‖∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω)‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal
            ((∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)]
  -- Integrability of squared sum.
  have h_int_sum_sq : MeasureTheory.Integrable
      (fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2) P := by
    have h_eq : ∀ ω, (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω))^2
                = ∑ i : Fin H.N, ∑ j : Fin H.N,
                  (H.ξ i ω * (W.W (H.partition i.succ) ω
                            - W.W (H.partition i.castSucc) ω)) *
                  (H.ξ j ω * (W.W (H.partition j.succ) ω
                            - W.W (H.partition j.castSucc) ω)) := by
      intro ω; rw [sq]; exact Finset.sum_mul_sum _ _ _ _
    rw [show (fun ω => (∑ i, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2)
          = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N,
              (H.ξ i ω * (W.W (H.partition i.succ) ω
                        - W.W (H.partition i.castSucc) ω)) *
              (H.ξ j ω * (W.W (H.partition j.succ) ω
                        - W.W (H.partition j.castSucc) ω)) from funext h_eq]
    refine MeasureTheory.integrable_finsetSum _ (fun i _ => ?_)
    refine MeasureTheory.integrable_finsetSum _ (fun j _ => ?_)
    exact cross_sq_integrable W H i j
  have h_nn_sum_sq :
      0 ≤ᵐ[P] fun ω => (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                  - W.W (H.partition i.castSucc) ω))^2 := by
    filter_upwards with ω; exact sq_nonneg _
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sum_sq h_nn_sum_sq]
  rw [simpleIntegral_sq_bochner_eq W H h_adapt]
  rw [show ENNReal.ofReal (∑ i : Fin H.N,
            (H.partition i.succ - H.partition i.castSucc) * ∫ ω, (H.ξ i ω)^2 ∂P)
        = ∑ i : Fin H.N,
          ENNReal.ofReal
            ((H.partition i.succ - H.partition i.castSucc) * ∫ ω, (H.ξ i ω)^2 ∂P) from by
    rw [ENNReal.ofReal_sum_of_nonneg]
    intro i _
    refine mul_nonneg ?_ (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _))
    have : H.partition i.castSucc < H.partition i.succ :=
      H.partition_strictMono Fin.castSucc_lt_succ
    linarith]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_xi_sq_bound : ∀ ω : Ω, (H.ξ i ω)^2 ≤ M^2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (H.ξ i ω)^2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M^2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (H.ξ i ω)^2 := by
    filter_upwards with ω; positivity
  have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc :=
    sub_nonneg.mpr (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  rw [ENNReal.ofReal_mul h_dt_nn]
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq]
  rw [show (fun ω => ENNReal.ofReal ((H.ξ i ω)^2))
        = fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => (h_norm_sq_eq _).symm)]

/-- **Itô isometry on simple integrands.** The L²-norm of the simple integral
equals the L²-norm of the integrand against `dP ⊗ ds`. -/
lemma simpleIntegral_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (_hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [simpleIntegral_sq_lintegral_eq W H h_adapt]
  rw [lintegral_eval_sq_outer H]

/-- **L² isometry on simple integrands (Bochner sum form).**
For an adapted simple predictable integrand
`H = ∑_i ξ_i · 1_{(t_i, t_{i+1}]}`,
`E[(∑_i ξ_i ΔB_i)²] = Σ_i (t_{i+1} - t_i) · E[ξ_i²]`.

Cross terms vanish by `simpleIntegral_offDiagonal` (which is the integral
form of the Brownian-increment martingale-difference property — see
`martingale_simpleIntegral_brownian`); the diagonal is computed in
`simpleIntegral_diagonal_bochner`. -/
theorem simpleIntegral_L2_isometry_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (simpleIntegral W H T ω) ^ 2 ∂P
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) *
          ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_eq : ∀ ω, (simpleIntegral W H T ω) ^ 2
      = (∑ i : Fin H.N, H.ξ i ω * (W.W (H.partition i.succ) ω
                                  - W.W (H.partition i.castSucc) ω)) ^ 2 := by
    intro ω; rw [simpleIntegral_eq_sum]
  simp_rw [h_eq]
  exact simpleIntegral_sq_bochner_eq W H h_adapt

/-- **Inner Bochner integral of `(H.eval s ω)²` over `s ∈ [0, T]`** equals
the sum of `(t_{i+1} - t_i) · (ξ_i ω)²` over partition pieces. Bochner
mirror of `lintegral_eval_sq`. -/
lemma integral_eval_sq {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2 := by
  -- Real version of `eval_sq_eq_sum_indicator`.
  have h_sq_decomp : ∀ s, (H.eval s ω) ^ 2 = ∑ i : Fin H.N,
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
        (fun _ => (H.ξ i ω) ^ 2) s := by
    intro s
    rw [eval_eq_sum_indicator]
    by_cases h_any : ∃ i : Fin H.N,
        s ∈ Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
    · obtain ⟨i₀, hi₀⟩ := h_any
      have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
          s ∉ Set.Ioc (H.partition j.castSucc) (H.partition j.succ) := by
        intro j hj hj_mem
        have := partition_intervals_disjoint H hj
        exact Set.disjoint_left.mp this hj_mem hi₀
      have h_sum_eq : (∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => H.ξ i ω) s) = H.ξ i₀ ω := by
        rw [Finset.sum_eq_single i₀]
        · exact Set.indicator_of_mem hi₀ _
        · intro j _ hj
          exact Set.indicator_of_notMem (h_unique j hj) _
        · intro h_not; exact absurd (Finset.mem_univ _) h_not
      have h_sum_sq_eq : (∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (H.ξ i ω) ^ 2) s) = (H.ξ i₀ ω) ^ 2 := by
        rw [Finset.sum_eq_single i₀]
        · exact Set.indicator_of_mem hi₀ _
        · intro j _ hj
          exact Set.indicator_of_notMem (h_unique j hj) _
        · intro h_not; exact absurd (Finset.mem_univ _) h_not
      rw [h_sum_eq, h_sum_sq_eq]
    · push Not at h_any
      have h_zero_sq : ∀ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (H.ξ i ω) ^ 2) s = 0 :=
        fun i => Set.indicator_of_notMem (h_any i) _
      have h_zero : ∀ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => H.ξ i ω) s = 0 :=
        fun i => Set.indicator_of_notMem (h_any i) _
      rw [Finset.sum_eq_zero (fun i _ => h_zero i),
          Finset.sum_eq_zero (fun i _ => h_zero_sq i)]
      simp
  simp_rw [h_sq_decomp]
  rw [MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    have h_meas_set : MeasurableSet
        (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)) := measurableSet_Ioc
    have h_subset : Set.Ioc (H.partition i.castSucc) (H.partition i.succ)
        ⊆ Set.Icc (0 : ℝ) T := by
      intro x hx
      have h_part_zero_le : 0 ≤ H.partition i.castSucc := by
        have : H.partition 0 ≤ H.partition i.castSucc :=
          H.partition_strictMono.monotone (Fin.zero_le _)
        rw [H.partition_zero] at this; exact this
      have h_part_succ_le_T : H.partition i.succ ≤ T := by
        refine le_trans ?_ H.partition_le_T
        exact H.partition_strictMono.monotone (Fin.le_last _)
      refine ⟨?_, ?_⟩
      · exact h_part_zero_le.trans (le_of_lt hx.1)
      · exact hx.2.trans h_part_succ_le_T
    have h_dt_nn : 0 ≤ H.partition i.succ - H.partition i.castSucc :=
      sub_nonneg.mpr (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
    rw [MeasureTheory.integral_indicator h_meas_set]
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def]
    rw [MeasureTheory.Measure.restrict_apply h_meas_set]
    rw [Set.inter_eq_left.mpr h_subset]
    rw [Real.volume_Ioc, ENNReal.toReal_ofReal h_dt_nn]
    rw [smul_eq_mul]
  · intro i _
    refine MeasureTheory.Integrable.indicator ?_ measurableSet_Ioc
    exact MeasureTheory.integrable_const _

/-- **Outer Bochner integral of `(H.eval)²` over `Ω × [0,T]`** equals the
sum of `(t_{i+1} - t_i) · ∫ (ξ_i)² ∂P`. Bochner mirror of
`lintegral_eval_sq_outer`. -/
lemma integral_eval_sq_outer
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (H : SimplePredictable Ω T) :
    ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume ∂P
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) *
          ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_inner : ∀ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume
      = ∑ i : Fin H.N, (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2 :=
    fun ω => integral_eval_sq H ω
  rw [show (fun ω => ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume)
      = (fun ω => ∑ i : Fin H.N,
          (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2) from
    funext h_inner]
  -- Per-term integrability of `(t_{i+1} - t_i) · (ξ_i)²`.
  have h_int_term : ∀ i ∈ (Finset.univ : Finset (Fin H.N)),
      MeasureTheory.Integrable
        (fun ω => (H.partition i.succ - H.partition i.castSucc) * (H.ξ i ω) ^ 2) P := by
    intro i _
    refine MeasureTheory.Integrable.const_mul ?_ _
    obtain ⟨M, hM⟩ := H.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) ?_ ?_
    · exact ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable
    · filter_upwards with ω
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  rw [MeasureTheory.integral_finsetSum _ h_int_term]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul]

/-- **A2: L² isometry on simple integrands (Bochner integral form).**
For an adapted simple predictable integrand `H`,
`E[(simpleIntegral W H T)²] = ∫_0^T E[(H.eval s)²] ds`.

Combines `simpleIntegral_L2_isometry_brownian` (sum form) with
`integral_eval_sq_outer` (which expresses the same Σ in step-function
integral form). -/
theorem simpleIntegral_L2_isometry_brownian_integral_form
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫ ω, (simpleIntegral W H T ω) ^ 2 ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, (H.eval s ω) ^ 2 ∂volume ∂P := by
  rw [simpleIntegral_L2_isometry_brownian W H h_adapt]
  rw [integral_eval_sq_outer H]
end LevyStochCalc.Brownian.Ito
