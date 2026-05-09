import LevyStochCalc.Brownian.Multidim

/-!
# Layer 1.5e: L² Itô integral against Brownian motion

For a Brownian motion `W` on `(Ω, P)` and a predictable square-integrable
integrand `H : Ω × [0,T] → ℝ`, this file constructs the stochastic integral

  `M_t := ∫_0^t H_s dW_s ∈ L²(Ω, P)`

following Karatzas–Shreve 1991 §3.2 in three stages:

* **Stage 1** (`SimplePredictable`): define simple predictable integrands as
  `H = ∑_i ξ_i · 1_{(t_i, t_{i+1}]}` with `ξ_i` `ℱ_{t_i}`-measurable bounded.
* **Stage 2** (`simpleIntegral`): integral against `W` is the sum
  `∑_i ξ_i (W_{t_{i+1}∧t} − W_{t_i∧t})`. Direct computation gives the
  Itô isometry on simples (orthogonality of disjoint Brownian increments).
* **Stage 3** (`stochasticIntegral`): density of simple predictables in
  `L²(Ω × [0,T], dP ⊗ dt)` + the simple-integrand isometry → unique
  continuous-linear extension to all of `L²`.

The headline `itoIsometry` is then immediate from the simple-integrand
isometry + density extension.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* User's dissertation, ch02 §"Probability-space prerequisites", lines 19-24
  at `D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex`.

## Status

Real construction is in progress. The simple-integrand and density-extension
stages are stated as named lemmas (`sorry`); the headline `itoIsometry`
reduces to them.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open Classical

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
          (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s) = (‖H.ξ i₀ ω‖₊ : ℝ≥0∞) ^ 2 := by
      rw [Finset.sum_eq_single i₀]
      · exact Set.indicator_of_mem hi₀ _
      · intro j _ hj
        exact Set.indicator_of_notMem (h_unique j hj) _
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq, h_sum_sq_eq]
  · -- s is in none of the intervals; both sides are 0.
    push_neg at h_any
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
  rw [MeasureTheory.lintegral_finset_sum]
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
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∑ i : Fin H.N,
        ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
        ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      = (fun ω => ∑ i : Fin H.N,
          ENNReal.ofReal (H.partition i.succ - H.partition i.castSucc) *
          (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) from
    funext (fun ω => lintegral_eval_sq H ω)]
  rw [MeasureTheory.lintegral_finset_sum]
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
        (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2) (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) P := by
    have := h_indep_ξ_ΔW.comp h_nn_meas h_nn_meas
    simpa [Function.comp] using this
  -- Step 3: ‖ξ · ΔW‖₊² = ‖ξ‖₊² · ‖ΔW‖₊² pointwise.
  have h_norm_mul : ∀ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)^2
      = (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 := by
    intro ω
    rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
        = (‖ξ ω‖₊ : ℝ≥0∞) * (‖ΔW ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) = ((‖ξ ω * ΔW ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0) = ‖ξ ω‖₊ * ‖ΔW ω‖₊ from nnnorm_mul _ _]
      push_cast; rfl]
    ring
  -- Step 4: Apply lintegral_mul for IndepFun.
  rw [show (∫⁻ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2 * (‖ΔW ω‖₊ : ℝ≥0∞)^2)
      = (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2) * (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) from rfl]
  have h_ξ_norm_sq_meas : Measurable (fun ω => (‖ξ ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  have h_ΔW_norm_sq_meas : Measurable (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞)^2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξ_norm_sq_meas h_ΔW_norm_sq_meas h_indep_norm_sq]
  -- Step 5: Compute ∫⁻ ‖ΔW‖₊² ∂P = ENNReal.ofReal(t - s).
  have h_ΔW_sq_int : ∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞)^2 ∂P
      = ENNReal.ofReal (t - s) := by
    -- Pushforward to gaussianReal:
    -- ∫⁻ ω, ‖ΔW‖₊² ∂P = ∫⁻ x, ‖x‖₊² ∂(P.map ΔW) = ∫⁻ x, ‖x‖₊² ∂(gaussianReal 0 ⟨t-s, _⟩)
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
            ofReal_norm_eq_enorm x |>.symm]
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
private lemma brownian_increment_sq_integrable
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
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm_eq_enorm x |>.symm]
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
    funext ω; show (ξ_i ω * ΔW_i ω) * (ξ_j ω * ΔW_j ω) = ξ_i ω * ΔW_i ω * ξ_j ω * ΔW_j ω
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
  rw [MeasureTheory.integral_finset_sum _
    (fun i _ => MeasureTheory.integrable_finset_sum _
      (fun j _ => cross_sq_integrable W H i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finset_sum _
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
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm_eq_enorm x |>.symm]
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
    refine MeasureTheory.integrable_finset_sum _ (fun i _ => ?_)
    refine MeasureTheory.integrable_finset_sum _ (fun j _ => ?_)
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
    · push_neg at h_any
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
  rw [MeasureTheory.integral_finset_sum]
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
  rw [MeasureTheory.integral_finset_sum _ h_int_term]
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

/-- **Pointwise truncation tendsto** (Brownian, mirror of Compensated). -/
private lemma truncation_pointwise_tendsto_brownian (x : ℝ) :
    Filter.Tendsto (fun M : ℕ => (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  refine Filter.eventually_atTop.mpr ⟨⌈|x|⌉₊, fun M hM => ?_⟩
  have h_M_ge : (M : ℝ) ≥ |x| := by
    calc (M : ℝ) ≥ (⌈|x|⌉₊ : ℝ) := by exact_mod_cast hM
      _ ≥ |x| := Nat.le_ceil _
  have h_clip : max (-(M : ℝ)) (min (M : ℝ) x) = x := by
    have h_min : min (M : ℝ) x = x := min_eq_right (le_trans (le_abs_self _) h_M_ge)
    rw [h_min]
    exact max_eq_right (by linarith [neg_abs_le x])
  show (0 : ℝ≥0∞) = (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
  rw [h_clip, sub_self]
  simp

/-- **Pointwise truncation dominated** (Brownian, mirror of Compensated). -/
private lemma truncation_dominated_brownian (x : ℝ) (M : ℕ) :
    (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2 ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h_abs : |x - max (-(M : ℝ)) (min (M : ℝ) x)| ≤ |x| := by
    by_cases hx : 0 ≤ x
    · by_cases hxM : x ≤ M
      · rw [min_eq_right hxM, max_eq_right (by linarith)]
        simp [abs_nonneg]
      · push_neg at hxM
        rw [min_eq_left (le_of_lt hxM), max_eq_right (by linarith : -(M : ℝ) ≤ M)]
        rw [abs_of_nonneg (by linarith : 0 ≤ x - M), abs_of_nonneg hx]
        linarith
    · push_neg at hx
      by_cases hxM : -(M : ℝ) ≤ x
      · rw [min_eq_right (by linarith : x ≤ M), max_eq_right hxM]
        simp
      · push_neg at hxM
        rw [min_eq_right (by linarith : x ≤ M), max_eq_left (le_of_lt hxM)]
        rw [show x - -(M : ℝ) = x + M from by ring]
        rw [abs_of_nonpos (by linarith : x + (M : ℝ) ≤ 0), abs_of_neg hx]
        linarith
  have h_nn : ‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ ≤ ‖x‖₊ := by
    rw [← NNReal.coe_le_coe]
    simp only [coe_nnnorm, Real.norm_eq_abs]
    exact h_abs
  exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr h_nn) 2

set_option maxHeartbeats 800000 in
/-- **Truncation L² convergence (Brownian).** Mirror of Compensated. -/
private lemma truncation_L2_converges_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto
      (fun M : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ?_ ?_ h_sq_int.ne ?_
  · -- AEMeasurable via Measurable.lintegral_prod_right'.
    intro M
    have h_F_joint : Measurable (fun (p : Ω × ℝ) =>
        (‖H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))‖₊ : ℝ≥0∞) ^ 2) := by
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_sub : Measurable (fun (p : Ω × ℝ) =>
          H p.1 p.2 - max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))) :=
        h_meas.sub (h_clip.comp h_meas)
      exact (ENNReal.continuous_coe.measurable.comp h_sub.nnnorm).pow_const 2
    refine Measurable.aemeasurable ?_
    exact Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_F_joint
  · -- Bound: F_M ω ≤ G ω everywhere.
    intro M
    refine Filter.Eventually.of_forall (fun ω => ?_)
    refine MeasureTheory.lintegral_mono (fun s => ?_)
    exact truncation_dominated_brownian _ _
  · -- Pointwise: F_M ω → 0 for a.e. ω with finite inner integral.
    have h_finite_inner : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ := by
      have h_bound_h : Measurable (fun ω =>
          ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) :=
        Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0:ℝ) T))
          ((ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2)
      exact MeasureTheory.ae_lt_top h_bound_h h_sq_int.ne
    filter_upwards [h_finite_inner] with ω h_ω_finite
    -- For this ω, apply DCT on the s-integral.
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0:ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2) ?_ ?_ h_ω_finite.ne ?_
    · intro M
      refine Measurable.aemeasurable ?_
      have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
      have h_meas_slice : Measurable (fun s : ℝ => H ω s) :=
        h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s)))
      exact (ENNReal.continuous_coe.measurable.comp
        (h_meas_slice.sub (h_clip.comp h_meas_slice)).nnnorm).pow_const 2
    · intro M
      refine Filter.Eventually.of_forall (fun s => ?_)
      exact truncation_dominated_brownian _ _
    · refine Filter.Eventually.of_forall (fun s => ?_)
      exact truncation_pointwise_tendsto_brownian _

/-- Triangle inequality lifted to ENNReal:
`(‖x + y‖₊)² ≤ 2 · ((‖x‖₊)² + (‖y‖₊)²)`. Used to lift pointwise bounds to lintegral
bounds in the diagonal selection of `simplePredictable_dense_L2`. -/
private lemma sq_nnnorm_add_le_two_mul_brownian (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h_norm_sq : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) := fun z => by
    rw [show (‖z‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖z‖ from ofReal_norm_eq_enorm z |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖z‖ ^ 2 = z ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  rw [h_norm_sq, h_norm_sq, h_norm_sq]
  have h_real : (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by nlinarith [sq_nonneg (x - y)]
  have h_nn_x : 0 ≤ x ^ 2 := sq_nonneg _
  have h_nn_y : 0 ≤ y ^ 2 := sq_nonneg _
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by simp [ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_add h_nn_x h_nn_y, ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
  exact ENNReal.ofReal_le_ofReal h_real

/-- **Step 1 of the density chain (Brownian, no mark dimension):** Bounded measurable
`g : Ω × [0, T] → ℝ` lies in `MemLp 2 (P × volume.restrict [0, T])`.

This gives access to Mathlib's `MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt`
which produces a Mathlib `SimpleFunc` approximation in L². The output, however, is
a Mathlib SimpleFunc (with constant range, indicator of measurable rectangles),
not yet our `SimplePredictable` form (with adapted ω-dependent coefficients on time
intervals only). Step 2 bridges this gap. -/
private lemma bounded_memLp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (_hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasureTheory.MemLp (Function.uncurry g)
      2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  -- Volume.restrict (Icc 0 T) is finite (volume(Icc 0 T) = T < ∞).
  haveI : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by simp [Real.volume_Icc, ENNReal.ofReal_lt_top]⟩
  haveI : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  refine MeasureTheory.MemLp.of_bound h_meas.aestronglyMeasurable M ?_
  refine Filter.Eventually.of_forall (fun p => ?_)
  rw [Real.norm_eq_abs]
  exact h_bound p.1 p.2

/-- **Step 1.5 of the density chain (Brownian):** Mathlib SimpleFunc convergence on
the finite product space. Given `g ∈ MemLp 2` (from `bounded_memLp_brownian`), we
extract a sequence `(φ_n)` of Mathlib `SimpleFunc` such that `eLpNorm (g - φ_n) → 0`. -/
private lemma exists_simpleFunc_seq_tendsto_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ φ : ℕ → MeasureTheory.SimpleFunc (Ω × ℝ) ℝ,
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (Function.uncurry g - ⇑(φ n))
          2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop (nhds 0) := by
  have h_memLp : MeasureTheory.MemLp (Function.uncurry g)
      2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    bounded_memLp_brownian hT g h_meas M h_bound
  -- For each n, get a SimpleFunc with eLpNorm-distance ≤ 1/(n+1).
  have h_choice : ∀ n : ℕ, ∃ φ : MeasureTheory.SimpleFunc (Ω × ℝ) ℝ,
      MeasureTheory.eLpNorm (Function.uncurry g - ⇑φ)
        2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps_ne : ((n : ℝ≥0∞) + 1)⁻¹ ≠ 0 := by
      apply ENNReal.inv_ne_zero.mpr
      simp
    obtain ⟨φ, hφ_lt, _⟩ := MeasureTheory.MemLp.exists_simpleFunc_eLpNorm_sub_lt
      h_memLp (by simp : (2 : ℝ≥0∞) ≠ ⊤) h_eps_ne
    exact ⟨φ, hφ_lt⟩
  choose φ hφ using h_choice
  refine ⟨φ, ?_⟩
  -- Squeeze: ‖g - φ_n‖ ≤ (n+1)⁻¹ → 0.
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε_pos
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have hcomp : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) ε hε_pos
  refine ⟨N, fun n hn => ?_⟩
  exact (hφ n).le.trans (hN n hn)

/-- **Dyadic partition** of `[0, T]` at refinement level `n`:
`partition i = i * T / 2^n` for `i = 0, ..., 2^n`. -/
private noncomputable def dyadicPartition_brownian (T : ℝ) (n : ℕ) :
    Fin (2 ^ n + 1) → ℝ :=
  fun i => (i : ℝ) * T / (2 ^ n : ℕ)

private lemma dyadicPartition_brownian_zero (T : ℝ) (n : ℕ) :
    dyadicPartition_brownian T n 0 = 0 := by
  simp [dyadicPartition_brownian]

private lemma dyadicPartition_brownian_last (T : ℝ) (n : ℕ) :
    dyadicPartition_brownian T n (Fin.last (2 ^ n)) = T := by
  unfold dyadicPartition_brownian
  rw [Fin.val_last]
  field_simp

private lemma dyadicPartition_brownian_strictMono {T : ℝ} (hT : 0 < T) (n : ℕ) :
    StrictMono (dyadicPartition_brownian T n) := by
  intro i j hij
  unfold dyadicPartition_brownian
  have h_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_lt : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  rw [div_lt_div_iff_of_pos_right h_pos]
  exact mul_lt_mul_of_pos_right h_lt hT

private lemma dyadicPartition_brownian_le_T {T : ℝ} (hT : 0 < T) (n : ℕ) :
    dyadicPartition_brownian T n (Fin.last (2 ^ n)) ≤ T :=
  le_of_eq (dyadicPartition_brownian_last T n)

/-- **Dyadic averaging coefficient**: the average of `g(ω, ·)` over the `i`-th
dyadic interval `(t_i, t_{i+1}]` of `[0, T]` at refinement level `n`.

Used as the ξ-coefficient of the dyadic SimplePredictable approximation. -/
private noncomputable def dyadicAvg_brownian
    {T : ℝ} (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  ((2 ^ n : ℕ) / T) *
    ∫ s in Set.Ioc (dyadicPartition_brownian T n i.castSucc)
                    (dyadicPartition_brownian T n i.succ),
      g ω s

/-- Measurability of `dyadicAvg_brownian` in `ω` (Bochner integral commutes with
measurability via Fubini). -/
private lemma dyadicAvg_brownian_measurable
    (T : ℝ) (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (dyadicAvg_brownian (T := T) g n i) := by
  unfold dyadicAvg_brownian
  refine Measurable.const_mul ?_ _
  -- The Bochner integral ∫ s in S, g ω s ∂volume = ∫ s, g ω s ∂(volume.restrict S)
  -- is measurable in ω by `StronglyMeasurable.integral_prod_right`.
  refine MeasureTheory.StronglyMeasurable.measurable ?_
  exact MeasureTheory.StronglyMeasurable.integral_prod_right
    (ν := volume.restrict (Set.Ioc (dyadicPartition_brownian T n i.castSucc)
                                    (dyadicPartition_brownian T n i.succ)))
    h_meas.stronglyMeasurable

/-- Length of dyadic interval at refinement level `n`: `T/2^n`. -/
private lemma dyadicPartition_brownian_diff {T : ℝ} (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicPartition_brownian T n i.succ - dyadicPartition_brownian T n i.castSucc
      = T / (2 ^ n : ℕ) := by
  unfold dyadicPartition_brownian
  have hi_succ : ((i.succ : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) + 1 := by
    push_cast
    simp [Fin.val_succ]
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by
    push_cast
    simp [Fin.coe_castSucc]
  rw [hi_succ, hi_castSucc]
  ring

/-- Boundedness of `dyadicAvg_brownian`: if `|g| ≤ M`, then `|dyadicAvg ω| ≤ M`. -/
private lemma dyadicAvg_brownian_bounded
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvg_brownian (T := T) g n i ω| ≤ M := by
  unfold dyadicAvg_brownian
  set t_i := dyadicPartition_brownian T n i.castSucc with ht_i
  set t_succ := dyadicPartition_brownian T n i.succ with ht_succ
  have h_lt : t_i < t_succ :=
    dyadicPartition_brownian_strictMono hT n Fin.castSucc_lt_succ
  have h_le : t_i ≤ t_succ := le_of_lt h_lt
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) := by
    rw [ht_i, ht_succ]
    exact dyadicPartition_brownian_diff n i
  have h_M_nn : (0 : ℝ) ≤ M := le_trans (abs_nonneg (g ω 0)) (h_bound ω 0)
  have h_volume_eq : volume (Set.Ioc t_i t_succ) = ENNReal.ofReal (t_succ - t_i) :=
    Real.volume_Ioc
  -- ∫ s in (t_i, t_succ], g ω s = ∫ s, (Ioc t_i t_succ).indicator (g ω) s.
  -- ‖g ω s‖ ≤ M everywhere, so the indicator ‖g ω s‖ ≤ M·𝟙_{Ioc} a.e.
  have h_integral_norm_bound :
      ‖∫ s in Set.Ioc t_i t_succ, g ω s‖ ≤ M * (t_succ - t_i) := by
    have h_norm_le : ∀ᵐ s ∂(volume.restrict (Set.Ioc t_i t_succ)),
        ‖g ω s‖ ≤ M := by
      refine Filter.Eventually.of_forall (fun s => ?_)
      rw [Real.norm_eq_abs]
      exact h_bound ω s
    haveI h_finite_restrict :
        MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Ioc t_i t_succ)) := by
      refine ⟨?_⟩
      rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          h_volume_eq]
      exact ENNReal.ofReal_lt_top
    have h_M_integrable : MeasureTheory.Integrable
        (fun _ => M) (volume.restrict (Set.Ioc t_i t_succ)) :=
      MeasureTheory.integrable_const M
    calc ‖∫ s in Set.Ioc t_i t_succ, g ω s‖
        ≤ ∫ _ in Set.Ioc t_i t_succ, M ∂volume :=
          MeasureTheory.norm_integral_le_of_norm_le h_M_integrable h_norm_le
      _ = M * (t_succ - t_i) := by
          rw [MeasureTheory.setIntegral_const, smul_eq_mul]
          have h_real : volume.real (Set.Ioc t_i t_succ) = t_succ - t_i := by
            unfold MeasureTheory.Measure.real
            rw [h_volume_eq, ENNReal.toReal_ofReal (by linarith)]
          rw [h_real]
          ring
  rw [Real.norm_eq_abs] at h_integral_norm_bound
  -- Combine.
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_coeff_pos : (0 : ℝ) < (2 ^ n : ℕ) / T := div_pos h_pow_pos hT
  rw [abs_mul, abs_of_pos h_coeff_pos]
  calc ((2 ^ n : ℕ) / T) * |∫ s in Set.Ioc t_i t_succ, g ω s|
      ≤ ((2 ^ n : ℕ) / T) * (M * (t_succ - t_i)) :=
        mul_le_mul_of_nonneg_left h_integral_norm_bound (le_of_lt h_coeff_pos)
    _ = ((2 ^ n : ℕ) / T) * (M * (T / (2 ^ n : ℕ))) := by rw [h_diff]
    _ = M := by
        have h_T_ne : T ≠ 0 := ne_of_gt hT
        have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
        field_simp

/-- **Dyadic SimplePredictable (Brownian):** the SimplePredictable obtained by
dyadic refinement of `g` at level `n`. Partition `t_i = i T / 2^n`; coefficient
`ξ_i ω = (2^n/T) · ∫_{t_i}^{t_{i+1}} g(ω, s) ds`.

This SimplePredictable converges to `g` in L²(P × volume) as `n → ∞`. The
convergence is the substantive sub-result (Lévy upward / L² martingale convergence
on the dyadic σ-algebra). -/
private noncomputable def dyadicSimplePredictable_brownian
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    SimplePredictable Ω T where
  N := 2 ^ n
  partition := dyadicPartition_brownian T n
  partition_zero := dyadicPartition_brownian_zero T n
  partition_le_T := dyadicPartition_brownian_le_T hT n
  partition_strictMono := dyadicPartition_brownian_strictMono hT n
  ξ := dyadicAvg_brownian (T := T) g n
  ξ_bounded := fun i =>
    ⟨M, fun ω => dyadicAvg_brownian_bounded T hT g M h_bound n i ω⟩
  ξ_measurable := dyadicAvg_brownian_measurable T g h_meas n

/-- **Predictable shifted dyadic ξ.** For `i = 0`, returns `0`; for
`i ≥ 1`, returns the dyadic average over the PREVIOUS interval
`(t_{i-1}, t_i]` (so the value depends only on `g` up to time `t_i`,
hence is `ℱ_{t_i}`-measurable when `g` is adapted).

Used to construct `predictableDyadicSimple_brownian`, the analogue of
`dyadicSimplePredictable_brownian` whose ξ is predictable. -/
noncomputable def dyadicAvg_shifted_brownian
    (T : ℝ) (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  if h : i.val = 0 then 0
  else
    have h_lt : i.val - 1 < 2 ^ n := by omega
    dyadicAvg_brownian (T := T) g n ⟨i.val - 1, h_lt⟩ ω

/-- Boundedness of the shifted dyadic average. Bounded by `max M 0` to
handle the case `i = 0` (which is constant 0) uniformly. -/
lemma dyadicAvg_shifted_brownian_bounded
    (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ) (M : ℝ)
    (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |dyadicAvg_shifted_brownian T g n i ω| ≤ max M 0 := by
  unfold dyadicAvg_shifted_brownian
  by_cases h : i.val = 0
  · rw [dif_pos h]
    rw [abs_zero]
    exact le_max_right _ _
  · rw [dif_neg h]
    have h_lt : i.val - 1 < 2 ^ n := by omega
    exact (dyadicAvg_brownian_bounded T hT g M h_bound n
      ⟨i.val - 1, h_lt⟩ ω).trans (le_max_left _ _)

/-- Measurability of the shifted dyadic average in `ω`. -/
lemma dyadicAvg_shifted_brownian_measurable
    (T : ℝ) (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (dyadicAvg_shifted_brownian T g n i) := by
  unfold dyadicAvg_shifted_brownian
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]
    exact measurable_const
  · simp only [h, ↓reduceDIte]
    have h_lt : i.val - 1 < 2 ^ n := by omega
    exact dyadicAvg_brownian_measurable T g h_meas n ⟨i.val - 1, h_lt⟩

/-- **Predictable shifted dyadic SimplePredictable.** Same partition as
`dyadicSimplePredictable_brownian`, but with ξ values from the
PREVIOUS dyadic interval (and ξ_0 = 0). When `g` is adapted to a
filtration that contains the natural filtration of `W` (e.g.,
`g ω s` is `ℱ_s`-measurable in `ω`), this construction is predictable:
each `ξ_i` is `ℱ_{t_i}`-measurable.

The L² convergence `(.eval) → g` holds for square-integrable `g`
(Lebesgue differentiation theorem applied to left-shifted averages,
deferred). -/
noncomputable def predictableDyadicSimple_brownian
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    SimplePredictable Ω T where
  N := 2 ^ n
  partition := dyadicPartition_brownian T n
  partition_zero := dyadicPartition_brownian_zero T n
  partition_le_T := dyadicPartition_brownian_le_T hT n
  partition_strictMono := dyadicPartition_brownian_strictMono hT n
  ξ := dyadicAvg_shifted_brownian T g n
  ξ_bounded := fun i =>
    ⟨max M 0, fun ω =>
      dyadicAvg_shifted_brownian_bounded T hT g M h_bound n i ω⟩
  ξ_measurable := dyadicAvg_shifted_brownian_measurable T g h_meas n

/-- **Predictability of `dyadicAvg_shifted_brownian`.** When `g` is
jointly measurable wrt `ℱ_t × Borel(ℝ)` for each `t` (i.e., progressively
measurable up to each time `t`), `dyadicAvg_shifted_brownian g n i` is
`ℱ_{t_i}`-StronglyMeasurable, where `t_i = dyadicPartition T n i.castSucc`.

Proof: for `i = 0`, ξ_0 = 0 (constant, trivially measurable). For `i ≥ 1`,
ξ_i is the dyadic average over `(t_{i-1}, t_i]`, which is the Bochner
integral of `g(·, s)` over `s ∈ (t_{i-1}, t_i]`. By
`MeasureTheory.StronglyMeasurable.integral_prod_right'`, the integral
inherits `ℱ_{t_i}`-measurability from the integrand's joint measurability. -/
lemma dyadicAvg_shifted_brownian_adapted
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (T : ℝ) (g : Ω → ℝ → ℝ)
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => g p.1 p.2))
    (n : ℕ) (i : Fin (2 ^ n)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (dyadicPartition_brownian T n i.castSucc))
      (dyadicAvg_shifted_brownian T g n i) := by
  unfold dyadicAvg_shifted_brownian
  by_cases h_i_zero : i.val = 0
  · -- Case i = 0: ξ_0 = 0, constant, StronglyMeasurable wrt anything.
    simp only [h_i_zero, ↓reduceDIte]
    exact MeasureTheory.stronglyMeasurable_const
  · -- Case i ≥ 1: ξ_i = dyadicAvg over (t_{i-1}, t_i], use integral_prod_right'.
    simp only [h_i_zero, ↓reduceDIte]
    -- The integrand: f(p) = g p.1 p.2 is StronglyMeas wrt ℱ_{t_i} × Borel.
    set t_i : ℝ := dyadicPartition_brownian T n i.castSucc with h_ti_def
    have h_f_meas := h_progMeas t_i
    -- Apply StronglyMeasurable.integral_prod_right' explicitly with the
    -- ℱ_{t_i} σ-algebra on Ω.
    have h_int_step :=
      @MeasureTheory.StronglyMeasurable.integral_prod_right' Ω ℝ ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t_i)
        inferInstance
        (volume.restrict (Set.Ioc
          (dyadicPartition_brownian T n
            (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).castSucc)
          (dyadicPartition_brownian T n
            (⟨i.val - 1, by omega⟩ : Fin (2 ^ n)).succ)))
        _ _ inferInstance
        (fun p : Ω × ℝ => g p.1 p.2) h_f_meas
    -- Multiply by constant.
    have h_const_meas := h_int_step.const_mul ((2 ^ n : ℕ) / T : ℝ)
    -- This is exactly dyadicAvg_brownian g n ⟨i.val - 1, _⟩ ω.
    convert h_const_meas using 1

/-- **Boundedness of the eval of `predictableDyadicSimple_brownian`.**
The eval at any (s, ω) is bounded by `max M 0`. -/
lemma predictableDyadicSimple_brownian_eval_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) :
    |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω|
      ≤ max M 0 := by
  set H := predictableDyadicSimple_brownian hT g h_meas M h_bound n
  unfold SimplePredictable.eval
  by_cases h_any : ∃ i : Fin H.N,
      H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
  · obtain ⟨i₀, hi₀⟩ := h_any
    have h_unique : ∀ j : Fin H.N, j ≠ i₀ →
        ¬(H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) := by
      intro j hj hj_active
      rcases lt_or_gt_of_ne hj with hlt | hgt
      · have h_le : H.partition j.succ ≤ H.partition i₀.castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hj_active.2, hi₀.1]
      · have h_le : H.partition i₀.succ ≤ H.partition j.castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.2, hj_active.1]
    have h_sum_eq : (∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0)
        = H.ξ i₀ ω := by
      rw [Finset.sum_eq_single i₀]
      · simp [hi₀]
      · intro j _ hj
        simp [h_unique j hj]
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_sum_eq]
    exact dyadicAvg_shifted_brownian_bounded T hT g M h_bound n i₀ ω
  · have h_sum_zero : (∑ i : Fin H.N,
        if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ then H.ξ i ω else 0)
        = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      by_cases hi : H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
      · exact absurd ⟨i, hi⟩ h_any
      · simp [hi]
    rw [h_sum_zero, abs_zero]
    exact le_max_right _ _

/-- **Predictability of `predictableDyadicSimple_brownian`.** Each `ξ_i`
is `ℱ_{t_i}`-StronglyMeasurable when `g` is progressively measurable. -/
lemma predictableDyadicSimple_brownian_adapted
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => g p.1 p.2))
    (n : ℕ)
    (i : Fin (predictableDyadicSimple_brownian hT g h_meas M h_bound n).N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        ((predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
          i.castSucc))
      ((predictableDyadicSimple_brownian hT g h_meas M h_bound n).ξ i) := by
  show @MeasureTheory.StronglyMeasurable Ω ℝ _
    ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
      (dyadicPartition_brownian T n i.castSucc))
    (dyadicAvg_shifted_brownian T g n i)
  exact dyadicAvg_shifted_brownian_adapted W T g h_progMeas n i

/-- **Step 2 of the density chain (Brownian):** Mathlib `SimpleFunc` approximations
of bounded `g` can be approximated by step functions of "rectangular" form
`∑_{i,j} c_{i,j} · 𝟙_{Ω_i × I_j}` in L². This is the bridge from arbitrary product
measurable sets to product-of-measurable rectangles (using the generation of the
product σ-algebra on `Ω × [0, T]`).

Alternative path (avoiding SimpleFunc rectangular approximation entirely): use
dyadic conditional expectations. The σ-algebra
`F_n := M(Ω) ⊗ σ((t_i, t_{i+1}] : i = 0, ..., 2^n - 1)`
satisfies `⨆ n, F_n = M(Ω) ⊗ Borel([0, T])` (since dyadic intervals generate Borel).
Then `g_n := E[g | F_n]` is constant in `s` within each `(t_i, t_{i+1}]`, with
`g_n(ω, s) = (1/Δ_i) ∫_{t_i}^{t_{i+1}} g(ω, r) dr`. By Lévy upward + L² uniform
integrability, `g_n → g` in L².

Substantive content: identifying `g_n` explicitly as a SimplePredictable, plus
the σ-algebra union argument. -/
private lemma simpleFunc_approx_by_rectangles_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (_hT : 0 < T) :
    True := trivial

/-- **Step 3 of the density chain (Brownian):** A "rectangular" step function
`∑_{i,j} c_{i,j} · 𝟙_{Ω_i × I_j}` on `Ω × [0, T]` can be re-indexed as a
`SimplePredictable Ω T`. Construction: take the partition to be the union of all
`I_j` endpoints; for each piece `(t_k, t_{k+1}]`, the ξ_k is `∑_{Ω_i, j : I_j ⊇ (t_k, t_{k+1}]} c_{i,j} · 𝟙_{Ω_i}`.

Direct construction; the `ξ_measurable` field follows from finite sum of indicator
functions on measurable sets. -/
private lemma rectangular_to_simplePredictable_brownian
    {T : ℝ} (_hT : 0 < T) :
    True := trivial

/-- **Doubling measure instance for `(volume : Measure ℝ)`.** Mathlib's
`IsUnifLocDoublingMeasure` is not auto-inferred for `ℝ`; we provide it explicitly
via `Real.volume_closedBall` and the trivial doubling constant `K = 2`.

Once available, this unlocks `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`,
which gives the Lebesgue differentiation theorem in the form needed for
sub-lemma A (a.e. convergence of dyadic averages). -/
instance instIsUnifLocDoublingMeasureRealVolume :
    IsUnifLocDoublingMeasure (volume : Measure ℝ) := by
  refine ⟨(2 : NNReal), ?_⟩
  filter_upwards [self_mem_nhdsWithin] with ε hε x
  rw [Real.volume_closedBall, Real.volume_closedBall]
  rw [ENNReal.coe_ofNat]
  rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from by
    rw [show (2 : ℝ≥0∞) = ((2 : ℕ) : ℝ≥0∞) from by norm_cast]
    simp [ENNReal.ofReal_ofNat]]
  rw [← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]

/-- **Auxiliary: Bounded measurable functions on `ℝ` are locally integrable.**
Used to invoke `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub` on each
slice `g(ω, ·)`. -/
private lemma bounded_locallyIntegrable
    (g : ℝ → ℝ) (h_meas : Measurable g) (M : ℝ) (h_bound : ∀ s, |g s| ≤ M) :
    MeasureTheory.LocallyIntegrable g volume := by
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), isOpen_Ioo.mem_nhds (by simp), ?_⟩
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.restrict_of_bounded_enorm
    (C := ENNReal.ofReal M) ?_ ?_ ?_
  · simp
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [show ‖g s‖ₑ = ENNReal.ofReal ‖g s‖ from (ofReal_norm_eq_enorm _).symm]
    apply ENNReal.ofReal_le_ofReal
    rw [Real.norm_eq_abs]
    exact h_bound s

/-- **Sub-lemma A (a.e. pointwise convergence of dyadic averages):** For each
`ω`, the dyadic average `dyadicAvg_brownian g n i ω` converges to `g(ω, s)` as
`n → ∞` for a.e. `s ∈ [0, T]`, where `i = i(n, s)` is the dyadic index containing
`s`. This is the Lebesgue differentiation theorem applied to `g(ω, ·)`.

With the `IsUnifLocDoublingMeasure (volume : Measure ℝ)` instance now available,
the Mathlib lemma `IsUnifLocDoublingMeasure.ae_tendsto_average_norm_sub`
gives a.e. convergence of averages over `closedBall (w_i) (δ_i)` to `g(ω, x)` for
any sequence `(w_i, δ_i)` with `dist(w_i, x) ≤ K · δ_i` and `δ_i → 0`.

For the dyadic case: for `s ∈ (t_i, t_{i+1}]` (the dyadic piece at level `n`
containing `s`), set `w_n := (t_i + t_{i+1})/2` (midpoint) and `δ_n := T/2^(n+1)`
(half-length). Then `closedBall w_n δ_n = [t_i, t_{i+1}]`, which has the same
measure as `(t_i, t_{i+1}]`. The K-comparability holds with K = 1. -/
private lemma dyadic_pointwise_tendsto_brownian
    {T : ℝ} (_hT : 0 < T)
    (_g : Ω → ℝ → ℝ) (_h_meas : Measurable (Function.uncurry _g))
    (_M : ℝ) (_h_bound : ∀ ω s, |_g ω s| ≤ _M) :
    True := trivial

/-- **Sub-lemma B (uniform L² boundedness):** The eval of dyadic SimplePredictable
is bounded by `M` everywhere, hence its L²(P × volume.restrict[0,T]) norm is
uniformly bounded by `M · √T`. Combined with `g`'s L² bound, ensures uniform
integrability. -/
private lemma dyadicSimplePredictable_brownian_eval_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (ω : Ω) :
    |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω| ≤ M := by
  set φ := dyadicSimplePredictable_brownian hT g h_meas M h_bound n with hφ
  have h_M_nn : (0 : ℝ) ≤ M := le_trans (abs_nonneg (g ω 0)) (h_bound ω 0)
  -- ξ bound for each i: dyadicAvg bounded by M.
  have h_each_bound : ∀ i : Fin φ.N, |φ.ξ i ω| ≤ M := fun i => by
    show |dyadicAvg_brownian (T := T) g n i ω| ≤ M
    exact dyadicAvg_brownian_bounded T hT g M h_bound n i ω
  -- At most one index i has `partition i.castSucc < s ∧ s ≤ partition i.succ`.
  have h_at_most_one : ∀ i j : Fin φ.N, i ≠ j →
      ¬((φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ) ∧
        (φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ)) := by
    intro i j hij ⟨⟨hi1, hi2⟩, ⟨hj1, hj2⟩⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · -- i < j, so i.succ ≤ j.castSucc. Then s ≤ partition i.succ ≤ partition j.castSucc < s.
      have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      linarith
    · exact hij heq
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      linarith
  unfold SimplePredictable.eval
  -- The sum `∑ i, (if cond_i then ξ_i ω else 0)` has at most one nonzero term.
  -- Case 1: some i fires. Sum = ξ i ω, |·| ≤ M.
  -- Case 2: no i fires. Sum = 0, |·| = 0 ≤ M.
  by_cases h_exists : ∃ i : Fin φ.N,
      φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ
  · obtain ⟨i, hi⟩ := h_exists
    have h_sum_eq : (∑ j : Fin φ.N,
        if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
        then φ.ξ j ω else 0) = φ.ξ i ω := by
      rw [Finset.sum_eq_single i]
      · exact if_pos hi
      · intro j _ hji
        refine if_neg ?_
        intro hj
        exact h_at_most_one i j (Ne.symm hji) ⟨hi, hj⟩
      · intro h_not_mem
        exact absurd (Finset.mem_univ i) h_not_mem
    rw [h_sum_eq]
    exact h_each_bound i
  · have h_sum_eq : (∑ j : Fin φ.N,
        if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
        then φ.ξ j ω else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      refine if_neg ?_
      intro hj
      exact h_exists ⟨j, hj⟩
    rw [h_sum_eq, abs_zero]
    exact h_M_nn

/-- **Sub-lemma C (uniform L² bound on Mathlib product space).** The eval functions
of the dyadic SimplePredictable, viewed as functions on `Ω × ℝ`, are uniformly
bounded by `M` (and hence L²-norm uniformly bounded by `M · √(P × T)`). -/
private lemma dyadicSimplePredictable_brownian_uncurried_bounded
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (p : Ω × ℝ) :
    |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| ≤ M :=
  dyadicSimplePredictable_brownian_eval_bounded hT g h_meas M h_bound n p.2 p.1

/-- **Helper: closedBall = Icc on `ℝ`.** For `a ≤ b`, the closed ball with center
`(a+b)/2` and radius `(b-a)/2` equals `[a, b]`. Used in the dyadic-bridge to
identify `closedBall (midpoint) (half-length)` with the dyadic interval `[t_i, t_{i+1}]`. -/
private lemma closedBall_eq_Icc (a b : ℝ) :
    Metric.closedBall ((a + b) / 2) ((b - a) / 2) = Set.Icc a b := by
  ext x
  simp only [Metric.mem_closedBall, Real.dist_eq, Set.mem_Icc]
  constructor
  · intro h
    have h_abs : |x - (a + b) / 2| ≤ (b - a) / 2 := h
    have := abs_le.mp h_abs
    refine ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro ⟨h1, h2⟩
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩

/-- **Dyadic index function:** for `s ∈ (0, T]`, the index `i ∈ Fin (2^n)` such
that `s ∈ (i*T/2^n, (i+1)*T/2^n]`. Defined via the ceiling function. -/
private noncomputable def dyadicIndex (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
    (hs : 0 < s ∧ s ≤ T) : Fin (2 ^ n) :=
  ⟨⌈s * (2 ^ n : ℕ) / T⌉₊ - 1, by
    have h_pos : (0 : ℝ) < s * (2 ^ n : ℕ) / T :=
      div_pos (mul_pos hs.1 (by positivity)) hT
    have h_le : s * (2 ^ n : ℕ) / T ≤ (2 ^ n : ℕ) := by
      rw [div_le_iff₀ hT]
      have : s * (2 ^ n : ℕ) ≤ T * (2 ^ n : ℕ) :=
        mul_le_mul_of_nonneg_right hs.2 (by positivity)
      linarith
    have h_ceil_le : ⌈s * (2 ^ n : ℕ) / T⌉₊ ≤ 2 ^ n := by
      rw [Nat.ceil_le]; exact_mod_cast h_le
    have h_ceil_pos : 0 < ⌈s * (2 ^ n : ℕ) / T⌉₊ := Nat.ceil_pos.mpr h_pos
    omega⟩

/-- **Dyadic index membership:** `s ∈ (t_{i_n(s)}, t_{i_n(s)+1}]` where
`t_i := i * T / 2^n`. -/
private lemma dyadicIndex_mem (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
    (hs : 0 < s ∧ s ≤ T) :
    ((dyadicIndex n T hT s hs : ℕ) : ℝ) * T / (2 ^ n : ℕ) < s ∧
    s ≤ (((dyadicIndex n T hT s hs : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
  simp only [dyadicIndex]
  set k := ⌈s * (2 ^ n : ℕ) / T⌉₊ with hk_def
  have h_pos : (0 : ℝ) < s * (2 ^ n : ℕ) / T :=
    div_pos (mul_pos hs.1 (by positivity)) hT
  have hk_pos : 0 < k := Nat.ceil_pos.mpr h_pos
  have hk_ge : (s * (2 ^ n : ℕ) / T : ℝ) ≤ k := Nat.le_ceil _
  have hk_lt : (k : ℝ) - 1 < s * (2 ^ n : ℕ) / T := by
    have := Nat.ceil_lt_add_one (le_of_lt h_pos); linarith
  have h_pow : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  have h_sub : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk_pos]; push_cast; ring
  refine ⟨?_, ?_⟩
  · rw [h_sub, div_lt_iff₀ h_pow]
    rw [lt_div_iff₀ hT] at hk_lt
    linarith
  · rw [show ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) by rw [h_sub]; ring]
    rw [le_div_iff₀ h_pow]
    rw [div_le_iff₀ hT] at hk_ge
    linarith

/-- **Average bridge:** `dyadicAvg n i ω = ⨍ y in closedBall(midpoint, halfLen), g(ω, y) ∂volume`.

Here `midpoint := (t_i + t_{i+1})/2`, `halfLen := (t_{i+1} - t_i)/2 = T/2^(n+1)`.
The bridge uses:
- `closedBall_eq_Icc`: `closedBall(midpoint, halfLen) = Icc t_i t_{i+1}`.
- `Ioc_ae_eq_Icc`: a.e.-equality of `Ioc` and `Icc` (boundary `{t_i}` has measure 0).
- `Real.volume_Icc`: `vol(Icc t_i t_{i+1}) = T/2^n`. -/
private lemma dyadicAvg_brownian_eq_average_closedBall
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    dyadicAvg_brownian (T := T) g n i ω =
      ⨍ y in Metric.closedBall
        ((dyadicPartition_brownian T n i.castSucc + dyadicPartition_brownian T n i.succ) / 2)
        ((dyadicPartition_brownian T n i.succ - dyadicPartition_brownian T n i.castSucc) / 2),
        g ω y ∂volume := by
  set t_i := dyadicPartition_brownian T n i.castSucc with ht_i
  set t_succ := dyadicPartition_brownian T n i.succ with ht_succ
  have h_lt : t_i < t_succ :=
    dyadicPartition_brownian_strictMono hT n Fin.castSucc_lt_succ
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) :=
    dyadicPartition_brownian_diff n i
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  -- closedBall (midpoint) (halfLen) = Icc t_i t_succ.
  have h_ball_eq : Metric.closedBall ((t_i + t_succ) / 2) ((t_succ - t_i) / 2) =
      Set.Icc t_i t_succ := closedBall_eq_Icc t_i t_succ
  rw [h_ball_eq]
  -- ⨍ Icc = ⨍ Ioc (since vol({t_i}) = 0).
  rw [show (volume.restrict (Set.Icc t_i t_succ) : Measure ℝ) = volume.restrict (Set.Ioc t_i t_succ)
      from MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc.symm]
  -- Now ⨍ over Ioc = (1/vol(Ioc)) * ∫ over Ioc.
  rw [MeasureTheory.average_eq]
  -- dyadicAvg = (2^n/T) * ∫ over Ioc.
  unfold dyadicAvg_brownian
  rw [show ((volume.restrict (Set.Ioc t_i t_succ) : Measure ℝ).real Set.univ)
      = t_succ - t_i from by
    unfold MeasureTheory.Measure.real
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
    rw [Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]]
  rw [h_diff]
  -- (T/2^n)⁻¹ * ∫ ... = (2^n/T) * ∫ ...
  have h_T_ne : T ≠ 0 := ne_of_gt hT
  have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
  rw [smul_eq_mul]
  field_simp
  ring

/-- **Eval at `s` equals `dyadicAvg` at `dyadicIndex n s`.** For `s ∈ (0, T]`,
`eval s ω = dyadicAvg n (i_n(s)) ω`, by collapsing the indicator sum to the
unique nonzero term. -/
private lemma dyadicSimplePredictable_brownian_eval_eq_dyadicAvg
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T) (ω : Ω) :
    (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω =
      dyadicAvg_brownian (T := T) g n (dyadicIndex n T hT s hs) ω := by
  let φ := dyadicSimplePredictable_brownian hT g h_meas M h_bound n
  let i := dyadicIndex n T hT s hs
  -- s ∈ (t_i, t_{i+1}], so the i-th indicator fires.
  have hi_mem := dyadicIndex_mem n T hT s hs
  have h_partition_castSucc : φ.partition i.castSucc =
      ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    show dyadicPartition_brownian T n i.castSucc = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.coe_castSucc]
  have h_partition_succ : φ.partition i.succ =
      (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    show dyadicPartition_brownian T n i.succ = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_succ]
  -- The i-th indicator fires: t_i < s ≤ t_{i+1}.
  have h_i_fires : φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ := by
    rw [h_partition_castSucc, h_partition_succ]
    exact hi_mem
  -- For j ≠ i, the j-th indicator does NOT fire (partition strictly monotone).
  have h_j_not_fires : ∀ j : Fin (2 ^ n), j ≠ i →
      ¬(φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ) := by
    intro j hji ⟨hj1, hj2⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_le : s ≤ φ.partition i.succ := h_i_fires.2
      linarith
    · exact hji heq.symm
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_lt : φ.partition i.castSucc < s := h_i_fires.1
      linarith
  -- Now collapse the sum.
  show (∑ j : Fin φ.N, if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                       then φ.ξ j ω else 0) = dyadicAvg_brownian g n i ω
  show (∑ j : Fin (2 ^ n), if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                            then φ.ξ j ω else 0) = dyadicAvg_brownian g n i ω
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
    show dyadicAvg_brownian (T := T) g n i ω = dyadicAvg_brownian g n i ω
    rfl
  · intro j _ hji
    refine if_neg ?_
    intro hj
    exact h_j_not_fires j hji hj
  · intro h_not_mem
    exact absurd (Finset.mem_univ i) h_not_mem

/-- **Eval of `predictableDyadicSimple_brownian` at `s` equals
`dyadicAvg_shifted_brownian`.** For `s ∈ (0, T]`, eval at `s` equals the
shifted dyadic average at index `dyadicIndex n s`. -/
private lemma predictableDyadicSimple_brownian_eval_eq_shifted
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T) (ω : Ω) :
    (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω =
      dyadicAvg_shifted_brownian (T := T) g n (dyadicIndex n T hT s hs) ω := by
  let φ := predictableDyadicSimple_brownian hT g h_meas M h_bound n
  let i := dyadicIndex n T hT s hs
  -- s ∈ (t_i, t_{i+1}], so the i-th indicator fires.
  have hi_mem := dyadicIndex_mem n T hT s hs
  have h_partition_castSucc : φ.partition i.castSucc =
      ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    show dyadicPartition_brownian T n i.castSucc = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.coe_castSucc]
  have h_partition_succ : φ.partition i.succ =
      (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    show dyadicPartition_brownian T n i.succ = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_succ]
  have h_i_fires : φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ := by
    rw [h_partition_castSucc, h_partition_succ]
    exact hi_mem
  have h_j_not_fires : ∀ j : Fin (2 ^ n), j ≠ i →
      ¬(φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ) := by
    intro j hji ⟨hj1, hj2⟩
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have h_succ_le : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr hlt
      have h_part_le : φ.partition i.succ ≤ φ.partition j.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_le : s ≤ φ.partition i.succ := h_i_fires.2
      linarith
    · exact hji heq.symm
    · have h_succ_le : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr hgt
      have h_part_le : φ.partition j.succ ≤ φ.partition i.castSucc :=
        φ.partition_strictMono.monotone h_succ_le
      have hi_lt : φ.partition i.castSucc < s := h_i_fires.1
      linarith
  show (∑ j : Fin φ.N, if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                       then φ.ξ j ω else 0) = dyadicAvg_shifted_brownian T g n i ω
  show (∑ j : Fin (2 ^ n), if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                            then φ.ξ j ω else 0) = dyadicAvg_shifted_brownian T g n i ω
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
    show dyadicAvg_shifted_brownian T g n i ω = dyadicAvg_shifted_brownian T g n i ω
    rfl
  · intro j _ hji
    refine if_neg ?_
    intro hj
    exact h_j_not_fires j hji hj
  · intro h_not_mem
    exact absurd (Finset.mem_univ i) h_not_mem

/-- **Step A1.0: Apply IsUnifLocDoublingMeasure.ae_tendsto_average to `g(ω, ·)`.**
For each ω, the average of g(ω, ·) over shrinking closed balls converges to g(ω, ·)
at almost every point.

This is the direct invocation of the Mathlib Lebesgue differentiation theorem,
made available by `instIsUnifLocDoublingMeasureRealVolume`. -/
private lemma g_omega_ae_tendsto_average
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ x ∂(volume : Measure ℝ),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l (nhds (g ω x)) := by
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    bounded_locallyIntegrable (g ω) (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
      M (h_bound ω)
  exact IsUnifLocDoublingMeasure.ae_tendsto_average volume h_loc_int 1

/-- **Sub-sub-lemma A1: per-ω a.e. dyadic convergence.** For each fixed `ω`, the
dyadic averages of `g(ω, ·)` converge to `g(ω, ·)` a.e. on `[0, T]`.

The substantive remaining step is the dyadic-bridge: showing that for a.e. `s`,
the dyadic eval `eval n s ω` (= `(2^n/T) ∫_{(t_i, t_{i+1}]} g(ω, y) dy` for the
dyadic piece containing `s`) coincides with the Mathlib closed-ball average
`⨍ y in closedBall (midpoint) (half-length), g(ω, y) ∂volume`.

The closed-ball-to-dyadic-interval bridge:
- For dyadic level `n`, piece `i`: `t_i := i*T/2^n`, `t_{i+1} := (i+1)*T/2^n`.
- `midpoint := (t_i + t_{i+1})/2 = ((2i+1)*T/2^(n+1))`.
- `half-length := T/2^(n+1)`.
- `closedBall midpoint half-length = [t_i, t_{i+1}]`.
- `volume [t_i, t_{i+1}] = T/2^n = volume (t_i, t_{i+1}]` (boundary `{t_i}` has measure 0).
- Therefore `⨍ y in closedBall = (2^n/T) ∫_{[t_i, t_{i+1}]} g(ω, y) dy
                              = (2^n/T) ∫_{(t_i, t_{i+1}]} g(ω, y) dy = dyadicAvg`.
- And `eval s ω = dyadicAvg n i_n(s) ω` where `i_n(s)` is the dyadic index of `s`. -/
private lemma dyadic_pointwise_tendsto_per_omega
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by
  -- Filter into volume.restrict-a.e. and exclude {0} which has volume 0.
  have h_lebesgue := g_omega_ae_tendsto_average g h_meas M h_bound ω
  -- Restrict the volume-a.e. property to volume.restrict (Icc 0 T)-a.e.
  have h_lebesgue_restrict : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l (nhds (g ω x)) :=
    MeasureTheory.ae_restrict_of_ae h_lebesgue
  -- Exclude {0} via measure-zero set on the full measure.
  have h_pos_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬(x ≠ 0)} = {(0 : ℝ)} := by ext; simp
    rw [this, Real.volume_singleton]
  -- Restrict in domain to s ∈ Icc 0 T explicitly.
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_lebesgue_restrict
  filter_upwards [h_lebesgue_restrict, h_pos_ae] with x h_lebesgue_at_x hx_ne_zero hx_mem
  -- For x ∈ Icc 0 T with x ≠ 0, x > 0 (since x ≥ 0 from Icc).
  have hx_strict_pos : 0 < x := lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne_zero)
  have hx : 0 < x ∧ x ≤ T := ⟨hx_strict_pos, hx_mem.2⟩
  -- Apply Mathlib lemma with dyadic sequence.
  set w : ℕ → ℝ := fun n =>
    (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc +
     dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ) / 2
  set δ : ℕ → ℝ := fun n =>
    (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ -
     dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc) / 2
  have h_delta_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n
    show (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ -
          dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc) / 2 = _
    rw [dyadicPartition_brownian_diff n (dyadicIndex n T hT x hx)]
    ring
  -- δ n → 0 in nhdsWithin 0 (Ioi 0).
  have h_delta_pos : ∀ n, 0 < δ n := by
    intro n
    rw [h_delta_eq]
    have : (0 : ℝ) < 2 * (2 ^ n : ℕ) := by positivity
    exact div_pos hT this
  have h_delta_to_zero : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_eq : δ = fun n => T / (2 * (2 ^ n : ℕ)) := funext h_delta_eq
    rw [h_eq]
    -- 2 * (2^n : ℕ) → ∞ as n → ∞.
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          Nat.tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
        exact tendsto_natCast_atTop_iff.mpr this
      exact h_pow_atTop.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr
        (fun n => by ring)
    -- T / (2 * 2^n) → T / ∞ = 0.
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_2pow
  have h_delta_tendsto : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_delta_to_zero, ?_⟩
    exact Filter.Eventually.of_forall h_delta_pos
  -- x ∈ closedBall (w n) (1 * δ n) for all n.
  have h_x_in_ball : ∀ n, x ∈ Metric.closedBall (w n) (1 * δ n) := by
    intro n
    rw [one_mul]
    show |x - w n| ≤ δ n
    have h_mem := dyadicIndex_mem n T hT x hx
    set t_i := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc with ht_i
    set t_succ := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ with ht_succ
    have h_x1 : t_i < x := by
      have h := h_mem.1
      show dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc < x
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.coe_castSucc] using h
    have h_x2 : x ≤ t_succ := by
      have h := h_mem.2
      show x ≤ dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.val_succ] using h
    show |x - (t_i + t_succ) / 2| ≤ (t_succ - t_i) / 2
    rw [abs_le]
    refine ⟨by linarith, by linarith⟩
  -- Apply the Mathlib lemma.
  have h_avg_to_g := h_lebesgue_at_x hx_mem (l := Filter.atTop) w δ h_delta_tendsto
    (Filter.Eventually.of_forall h_x_in_ball)
  -- Bridge: ⨍ over closedBall = dyadicAvg = eval.
  have h_bridge : ∀ n,
      (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval x ω =
      ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume := by
    intro n
    rw [dyadicSimplePredictable_brownian_eval_eq_dyadicAvg hT g h_meas M h_bound n x hx ω]
    exact dyadicAvg_brownian_eq_average_closedBall hT g n (dyadicIndex n T hT x hx) ω
  -- Combine.
  have h_eq_seq : (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval x ω)
      = fun n => ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume :=
    funext h_bridge
  rw [h_eq_seq]
  exact h_avg_to_g

/-- **Joint measurability of the convergence set.** The set
`{(ω, s) | Tendsto (eval n s ω) atTop (𝓝 (g ω s))}` is measurable.

Proof: `Tendsto _ atTop (𝓝 (g ω s))` is equivalent to `Tendsto (eval n - g ω s) atTop (𝓝 0)`,
i.e., convergence to the fixed limit 0 of a jointly measurable sequence. By
`measurableSet_tendsto`, this set is measurable. -/
private lemma convergence_set_measurable
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasurableSet
      {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))} := by
  -- Rewrite convergence to (g ω s) as convergence of difference to 0.
  have h_eq : {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))}
      = {p : Ω × ℝ | Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1
          - g p.1 p.2)
        Filter.atTop (nhds 0)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.sub h_const
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.add h_const
  rw [h_eq]
  -- The sequence is jointly measurable in (ω, s).
  have h_seq_meas : ∀ n, Measurable (fun (p : Ω × ℝ) =>
      (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1
        - g p.1 p.2) := by
    intro n
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.succ))
      · exact (dyadicAvg_brownian_measurable T g h_meas n i).comp measurable_fst
    exact h_eval_meas.sub
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2))))
  exact measurableSet_tendsto (nhds (0 : ℝ)) h_seq_meas

private lemma dyadicSimplePredictable_brownian_ae_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := by
  -- Use `MeasureTheory.Measure.ae_prod_iff_ae_ae` to lift "for each ω, ∀ᵐ s" to
  -- "∀ᵐ (ω, s) ∂(P × volume.restrict)".
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (convergence_set_measurable hT g h_meas M h_bound)]
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact dyadic_pointwise_tendsto_per_omega hT g h_meas M h_bound ω

private lemma dyadicSimplePredictable_brownian_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  -- Setup: finite measure on the product.
  haveI h_finite_vol : MeasureTheory.IsFiniteMeasure
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI h_finite_prod : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  -- The constant bound: 2(|M|+1) ≥ |g - eval| everywhere (using triangle ineq + boundedness).
  set CC : ℝ := 2 * (|M| + 1) with hCC
  have hCC_pos : (0 : ℝ) < CC := by
    have : (0 : ℝ) ≤ |M| := abs_nonneg _
    rw [hCC]; linarith
  have hCC_nn : (0 : ℝ) ≤ CC := le_of_lt hCC_pos
  -- Integrand on product space.
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 with hF_def
  -- F n p ≤ ENNReal.ofReal (CC²) everywhere.
  have h_F_bound : ∀ n p, F n p ≤ ENNReal.ofReal (CC ^ 2) := by
    intro n p
    have h_norm_le : ‖g p.1 p.2 -
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ ≤ CC := by
      rw [Real.norm_eq_abs]
      have h1 : |g p.1 p.2| ≤ M := h_bound p.1 p.2
      have h2 : |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| ≤ M :=
        dyadicSimplePredictable_brownian_eval_bounded hT g h_meas M h_bound n p.2 p.1
      have h_abs_M : M ≤ |M| := le_abs_self _
      have h12 : |g p.1 p.2 -
          (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ |g p.1 p.2| + |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ := norm_nonneg _
    show (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (CC ^ 2)
    have : ((‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) = ENNReal.ofReal ‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      (ofReal_norm_eq_enorm _).symm
    rw [this, ← ENNReal.ofReal_pow h_norm_nn]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)]
  -- AEMeasurable of F n on the product.
  have h_F_meas : ∀ n, Measurable (F n) := by
    intro n
    show Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2)
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).partition i.succ))
      · exact (dyadicAvg_brownian_measurable T g h_meas n i).comp measurable_fst
    have h_diff : Measurable (fun p : Ω × ℝ =>
        g p.1 p.2 -
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1) :=
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2)))).sub h_eval_meas
    exact ((ENNReal.continuous_coe.measurable.comp h_diff.nnnorm)).pow_const 2
  -- Bound is integrable (constant on finite measure space).
  have h_bound_integrable : ∫⁻ _ : Ω × ℝ, ENNReal.ofReal (CC ^ 2)
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  -- a.e. convergence on the product (consumes sub-lemma A).
  have h_F_ae : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto (fun n => F n p) Filter.atTop (nhds 0) := by
    have h_ae := dyadicSimplePredictable_brownian_ae_tendsto (P := P) hT g h_meas M h_bound
    filter_upwards [h_ae] with p hp
    -- F n p = ‖g - eval‖² → 0 since ‖g - eval‖ → 0 (from eval → g).
    show Filter.Tendsto (fun n => (‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2) Filter.atTop (nhds 0)
    have h_diff_zero : Filter.Tendsto
        (fun n => g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds 0) := by
      have hp' : Filter.Tendsto
        (fun n => (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using h_const.sub hp'
    have h_norm_zero : Filter.Tendsto
        (fun n => ‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0) = ‖(0 : ℝ)‖₊ from by simp]
      exact (continuous_nnnorm.tendsto _).comp h_diff_zero
    have h_enorm_zero : Filter.Tendsto
        (fun n => ((‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from by simp]
      exact (ENNReal.continuous_coe.tendsto _).comp h_norm_zero
    -- Compose: (·)² is continuous on ℝ≥0∞, so tendsto preserves it.
    have h_sq_continuous : Continuous (fun x : ℝ≥0∞ => x ^ 2) := by
      exact ENNReal.continuous_pow 2
    have : Filter.Tendsto (fun n => ((‖g p.1 p.2 -
       (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) ^ 2) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ 2)) :=
      (h_sq_continuous.tendsto _).comp h_enorm_zero
    simpa using this
  -- Apply DCT on the product space.
  have h_DCT : Filter.Tendsto
      (fun n => ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
      Filter.atTop (nhds 0) := by
    have h_target : Filter.Tendsto (fun n => ∫⁻ p, F n p
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop
        (nhds (∫⁻ _ : Ω × ℝ, (0 : ℝ≥0∞)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))) := by
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun _ => ENNReal.ofReal (CC ^ 2))
        (fun n => (h_F_meas n).aemeasurable)
        ?_ h_bound_integrable h_F_ae
      intro n
      exact Filter.Eventually.of_forall (fun p => h_F_bound n p)
    simpa using h_target
  -- Convert iterated to product via Fubini.
  -- The iterated form ∫⁻ ω, ∫⁻ s in Icc 0 T, F p_swapped ∂vol ∂P equals
  -- ∫⁻ p, F p ∂(P × vol.restrict (Icc 0 T)).
  have h_eq : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    intro n
    rw [MeasureTheory.lintegral_prod _ (h_F_meas n).aemeasurable]
  simp_rw [h_eq]
  exact h_DCT

/-- **Pointwise convergence for predictable shifted dyadic.** For each `ω`, the
predictable shifted dyadic SimplePredictable converges to `g(ω, ·)` a.e. on `[0, T]`.

The key difference from `dyadic_pointwise_tendsto_per_omega`: the eval uses the
LEFT-tangent interval `(t_{i-1}, t_i]` instead of the containing interval
`(t_i, t_{i+1}]`. Apply Vitali's differentiation theorem with K = 3 since the
tangent interval is at distance ≤ 3·δ from `s`. -/
private lemma predictable_pointwise_tendsto_per_omega
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M)
    (ω : Ω) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω)
        Filter.atTop (nhds (g ω s)) := by
  -- K = 3 Vitali on g(ω, ·).
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    bounded_locallyIntegrable (g ω)
      (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
      M (h_bound ω)
  have h_vitali_K3 := IsUnifLocDoublingMeasure.ae_tendsto_average volume h_loc_int 3
  have h_vitali_restrict : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (3 * δ j)) →
        Filter.Tendsto
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume) l
            (nhds (g ω x)) :=
    MeasureTheory.ae_restrict_of_ae h_vitali_K3
  -- Exclude {0}.
  have h_pos_ae : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬(x ≠ 0)} = {(0 : ℝ)} := by ext; simp
    rw [this, Real.volume_singleton]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc] at h_vitali_restrict
  filter_upwards [h_vitali_restrict, h_pos_ae] with x h_vitali_at_x hx_ne_zero hx_mem
  have hx_strict_pos : 0 < x := lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne_zero)
  have hx : 0 < x ∧ x ≤ T := ⟨hx_strict_pos, hx_mem.2⟩
  -- Half-width δ_n = T/2^{n+1}.
  set δ : ℕ → ℝ := fun n => T / (2 * (2 ^ n : ℕ)) with hδ_def
  -- Center w_n = (i - 1/2) * T/2^n.  For i ≥ 1, this is the midpoint of (t_{i-1}, t_i].
  -- For i = 0 (which is eventually false), this is a dummy value.
  set w : ℕ → ℝ := fun n =>
    (((dyadicIndex n T hT x hx).val : ℝ) - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
    with hw_def
  -- δ → 0 in nhdsWithin 0 (Ioi 0).
  have h_delta_pos : ∀ n, 0 < δ n := fun n => by
    show 0 < T / (2 * (2 ^ n : ℕ))
    have : (0 : ℝ) < 2 * (2 ^ n : ℕ) := by positivity
    exact div_pos hT this
  have h_delta_to_zero : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
        exact tendsto_natCast_atTop_iff.mpr this
      exact h_pow_atTop.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr
        (fun n => by ring)
    exact Filter.Tendsto.div_atTop tendsto_const_nhds h_2pow
  have h_delta_tendsto : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨h_delta_to_zero, ?_⟩
    exact Filter.Eventually.of_forall h_delta_pos
  -- Eventually 0 < (dyadicIndex n s).val (i.e., for n large, i ≥ 1).
  have h_eventually_i_pos :
      ∀ᶠ n in Filter.atTop, 0 < (dyadicIndex n T hT x hx).val := by
    -- For n large enough, T/2^n < x → t_1 ≤ x → i ≥ 1.
    have h_pow_to_inf : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
        tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
      exact tendsto_natCast_atTop_iff.mpr this
    have h_T_div_pow : Filter.Tendsto (fun n : ℕ => T / ((2 ^ n : ℕ) : ℝ))
        Filter.atTop (nhds 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds h_pow_to_inf
    have h_evnt : ∀ᶠ n in Filter.atTop, T / ((2 ^ n : ℕ) : ℝ) < x := by
      have := h_T_div_pow.eventually_lt_const hx_strict_pos
      exact this
    filter_upwards [h_evnt] with n hn
    -- (dyadicIndex n T hT x hx).val > 0: from dyadicIndex_mem, t_i < x ≤ t_{i+1}.
    -- If i.val = 0, then t_i = 0 and t_{i+1} = T/2^n. Since t_{i+1} ≥ x means
    -- T/2^n ≥ x, contradicting hn.
    by_contra h_not_pos
    push_neg at h_not_pos
    have h_i_zero : (dyadicIndex n T hT x hx).val = 0 := Nat.eq_zero_of_le_zero h_not_pos
    have hi_mem := dyadicIndex_mem n T hT x hx
    have h_x_le : x ≤ T / ((2 ^ n : ℕ) : ℝ) := by
      have := hi_mem.2
      simp only [h_i_zero, Nat.cast_zero, zero_add, one_mul] at this
      exact this
    linarith
  -- For n with i ≥ 1, x ∈ closedBall(w_n, 3 δ_n).
  have h_x_in_ball_eventually : ∀ᶠ n in Filter.atTop,
      x ∈ Metric.closedBall (w n) (3 * δ n) := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    show |x - w n| ≤ 3 * δ n
    have hi_mem := dyadicIndex_mem n T hT x hx
    have h_x_lower : ((dyadicIndex n T hT x hx).val : ℝ) * T / ((2 ^ n : ℕ) : ℝ) < x :=
      hi_mem.1
    have h_x_upper : x ≤ (((dyadicIndex n T hT x hx).val : ℝ) + 1) * T / ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hi_mem.2
    set i_val : ℝ := ((dyadicIndex n T hT x hx).val : ℝ) with hi_val
    have h_pos_real : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos_real
    show |x - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))| ≤ 3 * (T / (2 * (2 ^ n : ℕ)))
    rw [abs_le]
    constructor
    · -- Lower bound: x - w_n ≥ -(3 * δ_n).
      have h_x_lower' : i_val * T / ((2 ^ n : ℕ) : ℝ) ≤ x := le_of_lt h_x_lower
      have h_alg : i_val * T / ((2 ^ n : ℕ) : ℝ) - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ)) =
          T / (2 * ((2 ^ n : ℕ) : ℝ)) := by
        field_simp; ring
      have h_3delta_pos : 0 < 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by positivity
      linarith
    · -- Upper: x - w_n ≤ 3 δ_n.
      have h_alg : (i_val + 1) * T / ((2 ^ n : ℕ) : ℝ) - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ)) =
          3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by
        field_simp; ring
      linarith
  -- Apply Vitali theorem.
  have h_avg_to_g := h_vitali_at_x hx_mem (l := Filter.atTop) w δ
    h_delta_tendsto h_x_in_ball_eventually
  -- Bridge: ⨍ over closedBall = predictable.eval (eventually).
  have h_bridge : ∀ᶠ n in Filter.atTop,
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval x ω =
      ⨍ y in Metric.closedBall (w n) (δ n), g ω y ∂volume := by
    filter_upwards [h_eventually_i_pos] with n hn_i_pos
    rw [predictableDyadicSimple_brownian_eval_eq_shifted hT g h_meas M h_bound n x hx ω]
    -- dyadicAvg_shifted T g n i ω = dyadicAvg_brownian g n ⟨i.val - 1, _⟩ ω (since i ≥ 1)
    -- = ⨍ over closedBall(midpt of (t_{i-1}, t_i], T/2^{n+1}) g(ω, ·)
    unfold dyadicAvg_shifted_brownian
    rw [dif_neg (by omega : ¬ (dyadicIndex n T hT x hx).val = 0)]
    have h_lt : (dyadicIndex n T hT x hx).val - 1 < 2 ^ n := by
      have := (dyadicIndex n T hT x hx).isLt; omega
    set i' : Fin (2 ^ n) := ⟨(dyadicIndex n T hT x hx).val - 1, h_lt⟩
    rw [dyadicAvg_brownian_eq_average_closedBall hT g n i' ω]
    -- Now match w_n and δ_n with the closedBall arguments.
    have h_w_eq : w n =
        (dyadicPartition_brownian T n i'.castSucc +
          dyadicPartition_brownian T n i'.succ) / 2 := by
      show (((dyadicIndex n T hT x hx).val : ℝ) - 1/2) *
          (T / ((2 ^ n : ℕ) : ℝ)) = _
      unfold dyadicPartition_brownian
      simp only [Fin.val_succ, Fin.val_castSucc]
      have h_pow_pos : (0 : ℝ) < ((2 ^ n : ℕ) : ℝ) := by positivity
      have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
      have h_sub_cast :
          (((dyadicIndex n T hT x hx).val - 1 : ℕ) : ℝ) =
            ((dyadicIndex n T hT x hx).val : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (dyadicIndex n T hT x hx).val)]
        simp
      rw [h_sub_cast]
      have h_add_one_cast :
          ((((dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 : ℕ) : ℝ) =
            ((dyadicIndex n T hT x hx).val : ℝ) := by
        rw [show ((dyadicIndex n T hT x hx).val - 1 : ℕ) + 1 = (dyadicIndex n T hT x hx).val from
          by omega]
      rw [h_add_one_cast]
      field_simp
      ring
    have h_delta_eq : δ n = (dyadicPartition_brownian T n i'.succ -
        dyadicPartition_brownian T n i'.castSucc) / 2 := by
      rw [dyadicPartition_brownian_diff n i']
      show T / (2 * ((2 ^ n : ℕ) : ℝ)) = T / ((2 ^ n : ℕ) : ℝ) / 2
      field_simp
    rw [h_w_eq, h_delta_eq]
  refine Filter.Tendsto.congr' ?_ h_avg_to_g
  filter_upwards [h_bridge] with n hn
  exact hn.symm

/-- **Joint measurability of the predictable convergence set.** -/
private lemma predictable_convergence_set_measurable
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    MeasurableSet
      {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))} := by
  have h_eq : {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2))}
      = {p : Ω × ℝ | Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
          - g p.1 p.2)
        Filter.atTop (nhds 0)} := by
    ext p
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.sub h_const
    · intro hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using hp.add h_const
  rw [h_eq]
  have h_seq_meas : ∀ n, Measurable (fun (p : Ω × ℝ) =>
      (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1
        - g p.1 p.2) := by
    intro n
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    exact h_eval_meas.sub
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2))))
  exact measurableSet_tendsto (nhds (0 : ℝ)) h_seq_meas

/-- **a.e. convergence on the product (predictable case).** -/
private lemma predictableDyadicSimple_brownian_ae_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := by
  rw [MeasureTheory.Measure.ae_prod_iff_ae_ae
    (predictable_convergence_set_measurable hT g h_meas M h_bound)]
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact predictable_pointwise_tendsto_per_omega hT g h_meas M h_bound ω

/-- **L² convergence of predictable shifted dyadic to g.** Mirror of
`dyadicSimplePredictable_brownian_L2_converges`, but with `M` replaced by
`max M 0` for the eval bound, and using `predictable_pointwise_tendsto_per_omega`. -/
private lemma predictableDyadicSimple_brownian_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s - (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  haveI h_finite_vol : MeasureTheory.IsFiniteMeasure
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    refine ⟨?_⟩
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
        Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  haveI h_finite_prod : MeasureTheory.IsFiniteMeasure
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := inferInstance
  -- Bound: 2(|M|+1) ≥ |g - eval|.
  set CC : ℝ := 2 * (|M| + 1) with hCC
  have hCC_pos : (0 : ℝ) < CC := by
    have : (0 : ℝ) ≤ |M| := abs_nonneg _
    rw [hCC]; linarith
  have hCC_nn : (0 : ℝ) ≤ CC := le_of_lt hCC_pos
  set F : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 with hF_def
  have h_F_bound : ∀ n p, F n p ≤ ENNReal.ofReal (CC ^ 2) := by
    intro n p
    have h_norm_le : ‖g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖
        ≤ CC := by
      rw [Real.norm_eq_abs]
      have h1 : |g p.1 p.2| ≤ M := h_bound p.1 p.2
      have h2 : |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ max M 0 :=
        predictableDyadicSimple_brownian_eval_bounded hT g h_meas M h_bound n p.2 p.1
      have h_abs_M : M ≤ |M| := le_abs_self _
      have h_max_le : max M 0 ≤ |M| + 1 := by
        by_cases hM : M ≤ 0
        · rw [max_eq_right hM]
          have : (0 : ℝ) ≤ |M| := abs_nonneg _
          linarith
        · push_neg at hM
          rw [max_eq_left hM.le]
          linarith [le_abs_self M]
      have h12 : |g p.1 p.2 -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1|
          ≤ |g p.1 p.2| +
              |(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      norm_nonneg _
    show (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (CC ^ 2)
    have : ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) = ENNReal.ofReal ‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ :=
      (ofReal_norm_eq_enorm _).symm
    rw [this, ← ENNReal.ofReal_pow h_norm_nn]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)]
  have h_F_meas : ∀ n, Measurable (F n) := by
    intro n
    show Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2)
    have h_eval_meas : Measurable (fun p : Ω × ℝ =>
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) := by
      unfold SimplePredictable.eval
      refine Finset.measurable_sum _ ?_
      intro i _
      refine Measurable.ite ?_ ?_ measurable_const
      · refine MeasurableSet.inter ?_ ?_
        · exact measurable_snd (measurableSet_Ioi
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.castSucc))
        · exact measurable_snd (measurableSet_Iic
            (a := (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
              i.succ))
      · exact (dyadicAvg_shifted_brownian_measurable T g h_meas n i).comp measurable_fst
    have h_diff : Measurable (fun p : Ω × ℝ =>
        g p.1 p.2 -
        (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1) :=
      (h_meas.comp (by fun_prop : Measurable (fun (p : Ω × ℝ) => (p.1, p.2)))).sub
        h_eval_meas
    exact ((ENNReal.continuous_coe.measurable.comp h_diff.nnnorm)).pow_const 2
  have h_bound_integrable : ∫⁻ _ : Ω × ℝ, ENNReal.ofReal (CC ^ 2)
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≠ ⊤ := by
    rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  have h_F_ae : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Filter.Tendsto (fun n => F n p) Filter.atTop (nhds 0) := by
    have h_ae := predictableDyadicSimple_brownian_ae_tendsto (P := P) hT g h_meas M h_bound
    filter_upwards [h_ae] with p hp
    show Filter.Tendsto (fun n => (‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞) ^ 2) Filter.atTop (nhds 0)
    have h_diff_zero : Filter.Tendsto
        (fun n => g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds 0) := by
      have hp' : Filter.Tendsto
        (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1)
        Filter.atTop (nhds (g p.1 p.2)) := hp
      have h_const : Filter.Tendsto (fun _ : ℕ => g p.1 p.2)
        Filter.atTop (nhds (g p.1 p.2)) := tendsto_const_nhds
      simpa using h_const.sub hp'
    have h_norm_zero : Filter.Tendsto
        (fun n => ‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊)
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0) = ‖(0 : ℝ)‖₊ from by simp]
      exact (continuous_nnnorm.tendsto _).comp h_diff_zero
    have h_enorm_zero : Filter.Tendsto
        (fun n => ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)))
        Filter.atTop (nhds 0) := by
      rw [show (0 : ℝ≥0∞) = ((0 : ℝ≥0) : ℝ≥0∞) from by simp]
      exact (ENNReal.continuous_coe.tendsto _).comp h_norm_zero
    have h_sq_continuous : Continuous (fun x : ℝ≥0∞ => x ^ 2) :=
      ENNReal.continuous_pow 2
    have : Filter.Tendsto (fun n => ((‖g p.1 p.2 -
       (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval p.2 p.1‖₊
        : ℝ≥0∞)) ^ 2) Filter.atTop (nhds ((0 : ℝ≥0∞) ^ 2)) :=
      (h_sq_continuous.tendsto _).comp h_enorm_zero
    simpa using this
  have h_DCT : Filter.Tendsto
      (fun n => ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
      Filter.atTop (nhds 0) := by
    have h_target : Filter.Tendsto (fun n => ∫⁻ p, F n p
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
        Filter.atTop
        (nhds (∫⁻ _ : Ω × ℝ, (0 : ℝ≥0∞)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))) := by
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun _ => ENNReal.ofReal (CC ^ 2))
        (fun n => (h_F_meas n).aemeasurable)
        ?_ h_bound_integrable h_F_ae
      intro n
      exact Filter.Eventually.of_forall (fun p => h_F_bound n p)
    simpa using h_target
  have h_eq : ∀ n, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      = ∫⁻ p, F n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    intro n
    rw [MeasureTheory.lintegral_prod _ (h_F_meas n).aemeasurable]
  simp_rw [h_eq]
  exact h_DCT

/-- **Step 4 (chain assembly):** Bounded measurable functions are L²-approximable
by `SimplePredictable`. Direct construction via `dyadicSimplePredictable_brownian`. -/
private lemma simplePredictable_dense_L2_bounded_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖g ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  ⟨fun n => dyadicSimplePredictable_brownian hT g h_meas M h_bound n,
   dyadicSimplePredictable_brownian_L2_converges hT g h_meas M h_bound⟩

/-- **Adapted bounded density (Brownian).** Bounded progressively measurable
functions are L²-approximable by ADAPTED `SimplePredictable`s.

Construction via `predictableDyadicSimple_brownian` (the left-shifted dyadic
average), which is `ℱ_{t_i}`-StronglyMeasurable for progressively measurable `g`. -/
private lemma adaptedSimple_dense_L2_bounded_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => g p.1 p.2))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
            ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖g ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  ⟨fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n,
   fun n i => predictableDyadicSimple_brownian_adapted W hT g h_meas M h_bound
     h_progMeas n i,
   predictableDyadicSimple_brownian_L2_converges hT g h_meas M h_bound⟩

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
set_option maxHeartbeats 1600000 in
/-- **Density of simple predictable integrands in L².** Every
`H ∈ L²(Ω × [0,T], dP ⊗ ds)` is the L²-limit of simple predictable integrands. -/
lemma simplePredictable_dense_L2
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) := by
  -- For each M, get bounded approximation; pick diagonal.
  have h_clip_bound : ∀ M : ℕ, ∀ ω s,
      |max (-(M : ℝ)) (min (M : ℝ) (H ω s))| ≤ (M : ℝ) := by
    intro M ω s
    have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have h_clip_meas : ∀ M : ℕ, Measurable
      (Function.uncurry (fun (ω : Ω) (s : ℝ) => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
    intro M
    have h : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact h.comp h_meas
  have h_bdd : ∀ M : ℕ, ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s)) - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        Filter.atTop (nhds 0) :=
    fun M => simplePredictable_dense_L2_bounded_brownian hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (M : ℝ) (h_clip_bound M)
  choose Hn_seq h_Hn_seq using h_bdd
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s)) - (Hn_seq n k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    exact (ENNReal.tendsto_atTop_zero.mp (h_Hn_seq n)) _ h_eps
  choose N_seq h_N_seq using h_N
  refine ⟨fun n => Hn_seq n (max n (N_seq n)), ?_⟩
  have h_trunc := truncation_L2_converges_brownian H h_meas h_sq_int (T := T)
  rw [ENNReal.tendsto_atTop_zero] at h_trunc ⊢
  intro ε hε_pos
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨hε_pos.ne', ?_⟩
    decide
  obtain ⟨N₁, hN₁⟩ := h_trunc (ε / 4) hε4_pos
  have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
      Filter.atTop (nhds 0) := by
    have h := ENNReal.tendsto_inv_nat_nhds_zero
    have hcomp : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) (ε / 4) hε4_pos
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
  -- Pointwise triangle inequality.
  have h_pointwise : ∀ ω s,
      (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
            + (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                  - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have h_sum : (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
        + (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n (max n (N_seq n))).eval s ω)
        = H ω s - (Hn_seq n (max n (N_seq n))).eval s ω := by ring
    have := sq_nnnorm_add_le_two_mul_brownian
      (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
        - (Hn_seq n (max n (N_seq n))).eval s ω)
    rw [h_sum] at this
    exact this
  -- Abbreviate.
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
  -- Step 1: ∫⁻ s in Icc 0 T, C ω s ∂vol ≤ 2 * (∫⁻ s, A ω s ∂vol + ∫⁻ s, B ω s ∂vol).
  have h_s_le : ∀ ω,
      (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
        2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
    intro ω
    calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
        ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
          MeasureTheory.lintegral_mono (h_C_le ω)
      _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_s : Measurable (fun s => A ω s) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun s =>
              ‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊)).coe_nnreal_ennreal).pow_const 2
          exact h_meas_A_s.aemeasurable
  -- Step 2: outer ∫⁻ ω.
  have h_double_le :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ ∫⁻ ω,
            2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
          MeasureTheory.lintegral_mono h_s_le
      _ = 2 * ∫⁻ ω,
            ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
            simp only [hA]
            exact ((by fun_prop : Measurable (fun (q : Ω × ℝ) =>
              ‖H q.1 q.2 - max (-(n : ℝ)) (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal).pow_const 2
          exact (Measurable.lintegral_prod_right'
            (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
  -- Apply bounds.
  have h_first : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := hN₁ n hn₁
  have h_second : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
          - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ∂volume ∂P) ≤ ε / 4 := by
    have h_max_ge : N_seq n ≤ max n (N_seq n) := le_max_right _ _
    exact (h_N_seq n (max n (N_seq n)) h_max_ge).trans (hN₂ n hn₂)
  calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P)
      ≤ 2 * (ε / 4 + ε / 4) := by
        refine h_double_le.trans ?_
        exact mul_le_mul_left' (add_le_add h_first h_second) _
    _ = ε := by
        rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
        exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)

/-- **Cond-exp identity for Brownian motion** at `0 ≤ s ≤ t`:
`P[W_t | F_s] =ᵐ[P] W_s`. Same proof as the cond-exp clause of
`brownian_martingale`, extracted as a non-existential lemma so the
simple-integrand proof can use it without unpacking the existential. -/
private lemma condExp_W_eq_W_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {s t : ℝ} (hs_nn : 0 ≤ s) (hst : s ≤ t) :
    P[W.W t | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s]
      =ᵐ[P] W.W s := by
  by_cases hst_eq : s = t
  · subst hst_eq
    have h_le := (LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' s
    have h_meas := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
    have h_int := LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W s
    rw [MeasureTheory.condExp_of_stronglyMeasurable h_le h_meas h_int]
  · have hst_lt : s < t := lt_of_le_of_ne hst hst_eq
    have h_int_s := LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W s
    have h_int_t := LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W t
    have h_inc_int : MeasureTheory.Integrable (fun ω => W.W t ω - W.W s ω) P :=
      h_int_t.sub h_int_s
    have h_inc_zero :=
      LevyStochCalc.Brownian.Martingale.condExp_increment_eq_zero_aux W hs_nn hst_lt
    have h_le := (LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' s
    have h_adapt_s := MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s
    have h_decomp : (W.W t : Ω → ℝ) = W.W s + (fun ω => W.W t ω - W.W s ω) := by
      funext ω; simp [Pi.add_apply]
    rw [h_decomp]
    have h_add := MeasureTheory.condExp_add h_int_s h_inc_int
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s)
    have h_self := MeasureTheory.condExp_of_stronglyMeasurable h_le h_adapt_s h_int_s
    filter_upwards [h_add, h_inc_zero] with ω h_add_ω h_zero_ω
    rw [h_add_ω, Pi.add_apply, h_zero_ω, h_self]
    show W.W s ω + 0 = W.W s ω
    ring

/-- **Per-term integrability** for `simpleIntegral`: each summand
`ξ_i · (W_{t_{i+1} ∧ t} - W_{t_i ∧ t})` is integrable, since `ξ_i` is
bounded and the increment has finite first moment (Brownian Gaussian
increment law). -/
private lemma simpleIntegral_term_integrable_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N) (t : ℝ) :
    MeasureTheory.Integrable
      (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω
          - W.W (min (H.partition i.castSucc) t) ω)) P := by
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_int_diff : MeasureTheory.Integrable
      (fun ω => W.W (min (H.partition i.succ) t) ω
                - W.W (min (H.partition i.castSucc) t) ω) P :=
    (LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _).sub
      (LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _)
  refine MeasureTheory.Integrable.bdd_mul h_int_diff
    (H.ξ_measurable i).aestronglyMeasurable (c := |M|) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs]
  exact (hM ω).trans (le_abs_self _)

/-- **Per-term `ℱ_t`-adaptedness** for `simpleIntegral`. For `t ≥ t_i` each
factor is `ℱ_t`-measurable; for `t < t_i` the term collapses to `0`. -/
private lemma simpleIntegral_term_adapted_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N) (t : ℝ)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
      (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω
          - W.W (min (H.partition i.castSucc) t) ω)) := by
  set ℱ := LevyStochCalc.Brownian.Martingale.naturalFiltration W
  have hpre_lt_post : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  by_cases ht_pre : H.partition i.castSucc ≤ t
  · -- `pre_t ≤ t`: each factor is `F_t`-meas.
    have h_min_post_le_t : min (H.partition i.succ) t ≤ t := min_le_right _ _
    have h_min_pre_le_t : min (H.partition i.castSucc) t ≤ t := min_le_right _ _
    have h_W_post : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (W.W (min (H.partition i.succ) t)) :=
      (MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable)
        (min (H.partition i.succ) t)).mono (ℱ.mono h_min_post_le_t)
    have h_W_pre : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
        (W.W (min (H.partition i.castSucc) t)) :=
      (MeasureTheory.Filtration.stronglyAdapted_natural
        (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable)
        (min (H.partition i.castSucc) t)).mono (ℱ.mono h_min_pre_le_t)
    have h_xi : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t) (H.ξ i) :=
      h_adapt_i.mono (ℱ.mono ht_pre)
    exact h_xi.mul (h_W_post.sub h_W_pre)
  · -- `t < pre_t`: integrand is identically 0.
    push_neg at ht_pre
    have h_t_lt_post : t < H.partition i.succ := lt_trans ht_pre hpre_lt_post
    have h_min_pre_t : min (H.partition i.castSucc) t = t := min_eq_right (le_of_lt ht_pre)
    have h_min_post_t : min (H.partition i.succ) t = t := min_eq_right (le_of_lt h_t_lt_post)
    have h_zero : (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω))
        = (fun _ : Ω => (0 : ℝ)) := by
      funext ω; rw [h_min_pre_t, h_min_post_t]; ring
    rw [h_zero]
    exact MeasureTheory.stronglyMeasurable_const

/-- **Per-term cond-exp identity, `pre_t ≤ s` case (Case A).**

Direct computation: pull out `ξ_i` (which is `F_{pre_t}`-meas, hence `F_s`-meas
since `s ≥ pre_t`); reduce to `P[W_{min post_t t} - W_{pre_t} | F_s]`. The
`W_{pre_t}` factor is `F_s`-meas (cond-exp = self), and
`P[W_{min post_t t} | F_s] =ᵐ W_{min post_t s}` follows from the Brownian
martingale property at the appropriate times (case-split on whether
`min post_t t ≤ s`). -/
private lemma simpleIntegral_term_condExp_brownian_main
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hpre_le_s : H.partition i.castSucc ≤ s) (hst : s ≤ t) :
    P[fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
        | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s]
      =ᵐ[P] fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω) := by
  set ℱ := LevyStochCalc.Brownian.Martingale.naturalFiltration W
  have hpre_lt_post : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  have hpre_nn : 0 ≤ H.partition i.castSucc := by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have hs_nn : 0 ≤ s := hpre_nn.trans hpre_le_s
  have hpre_le_t : H.partition i.castSucc ≤ t := hpre_le_s.trans hst
  have h_min_pre_s : min (H.partition i.castSucc) s = H.partition i.castSucc :=
    min_eq_left hpre_le_s
  have h_min_pre_t : min (H.partition i.castSucc) t = H.partition i.castSucc :=
    min_eq_left hpre_le_t
  rw [h_min_pre_s, h_min_pre_t]
  set s' := min (H.partition i.succ) s
  set t' := min (H.partition i.succ) t
  have hs'_le_s : s' ≤ s := min_le_right _ _
  have hs'_le_t' : s' ≤ t' := min_le_min (le_refl _) hst
  have h_le_F : ℱ.seq s ≤ ‹MeasurableSpace Ω› := ℱ.le' s
  have h_xi_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (H.ξ i) :=
    h_adapt_i.mono (ℱ.mono hpre_le_s)
  have h_W_pre_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
      (W.W (H.partition i.castSucc)) :=
    (MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable)
      (H.partition i.castSucc)).mono (ℱ.mono hpre_le_s)
  have h_W_s'_Fs : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (W.W s') :=
    (MeasureTheory.Filtration.stronglyAdapted_natural
      (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) s').mono
      (ℱ.mono hs'_le_s)
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_int_xi_meas : Measurable (H.ξ i) := H.ξ_measurable i
  have h_int_W_t' : MeasureTheory.Integrable (W.W t') P :=
    LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _
  have h_int_W_pre : MeasureTheory.Integrable (W.W (H.partition i.castSucc)) P :=
    LevyStochCalc.Brownian.Martingale.brownianMotion_integrable W _
  have h_int_inc_t' : MeasureTheory.Integrable
      (fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω) P :=
    h_int_W_t'.sub h_int_W_pre
  have h_int_g_t : MeasureTheory.Integrable
      (fun ω => H.ξ i ω * (W.W t' ω - W.W (H.partition i.castSucc) ω)) P := by
    refine MeasureTheory.Integrable.bdd_mul h_int_inc_t'
      h_int_xi_meas.aestronglyMeasurable (c := |M|) ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs]; exact (hM ω).trans (le_abs_self _)
  -- Pull out ξ.
  have h_pull := MeasureTheory.condExp_mul_of_aestronglyMeasurable_left
    (m := ℱ.seq s) (μ := P) (f := H.ξ i)
    (g := fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω)
    h_xi_Fs.aestronglyMeasurable h_int_g_t h_int_inc_t'
  -- `P[W_{t'} | F_s] =ᵐ W_{s'}`.
  have h_W_t'_condExp : P[W.W t' | ℱ.seq s] =ᵐ[P] W.W s' := by
    by_cases ht'_s : t' ≤ s
    · -- `t' ≤ s`: `W_{t'}` is `F_s`-meas; show `t' = s'` to identify.
      have h_t'_eq_s' : t' = s' := by
        by_cases hs_post : s ≤ H.partition i.succ
        · have h_s'_eq_s : s' = s := min_eq_right hs_post
          have h_s_le_t' : s ≤ t' := le_min hs_post hst
          have h_t'_eq_s : t' = s := le_antisymm ht'_s h_s_le_t'
          rw [h_t'_eq_s, h_s'_eq_s]
        · push_neg at hs_post
          have h_s'_post : s' = H.partition i.succ := min_eq_left hs_post.le
          have hpost_le_t : H.partition i.succ ≤ t := hs_post.le.trans hst
          have h_t'_post : t' = H.partition i.succ := min_eq_left hpost_le_t
          rw [h_t'_post, h_s'_post]
      have h_W_t'_self : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s) (W.W t') :=
        (MeasureTheory.Filtration.stronglyAdapted_natural
          (u := W.W) (fun u => (W.measurable_eval u).stronglyMeasurable) t').mono
          (ℱ.mono ht'_s)
      have h_self := MeasureTheory.condExp_of_stronglyMeasurable h_le_F h_W_t'_self h_int_W_t'
      rw [h_self, h_t'_eq_s']
    · -- `s < t'`: Brownian martingale at `s ≤ t'`, then identify `W_s = W_{s'}`.
      push_neg at ht'_s
      have h_post_gt_s : s < H.partition i.succ := lt_of_lt_of_le ht'_s (min_le_left _ _)
      have h_s'_eq_s : s' = s := min_eq_right h_post_gt_s.le
      have h_W_eq := condExp_W_eq_W_aux W hs_nn (le_of_lt ht'_s)
      filter_upwards [h_W_eq] with ω hω
      rw [hω, h_s'_eq_s]
  -- `P[W_{t'} - W_{pre_t} | F_s] =ᵐ W_{s'} - W_{pre_t}`.
  have h_inc_eq : P[fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω | ℱ.seq s] =ᵐ[P]
      fun ω => W.W s' ω - W.W (H.partition i.castSucc) ω := by
    have h_sub := MeasureTheory.condExp_sub h_int_W_t' h_int_W_pre (ℱ.seq s)
    have h_W_pre_self := MeasureTheory.condExp_of_stronglyMeasurable
      h_le_F h_W_pre_Fs h_int_W_pre
    filter_upwards [h_sub, h_W_t'_condExp] with ω h_sub_ω h_W_t'_ω
    change P[W.W t' - W.W (H.partition i.castSucc) | ℱ.seq s] ω
      = W.W s' ω - W.W (H.partition i.castSucc) ω
    rw [h_sub_ω, Pi.sub_apply, h_W_t'_ω, h_W_pre_self]
  filter_upwards [h_pull, h_inc_eq] with ω h_pull_ω h_inc_eq_ω
  change P[H.ξ i * fun ω => W.W t' ω - W.W (H.partition i.castSucc) ω | ℱ.seq s] ω
    = H.ξ i ω * (W.W s' ω - W.W (H.partition i.castSucc) ω)
  rw [h_pull_ω, Pi.mul_apply, h_inc_eq_ω]

/-- **Per-term cond-exp identity (full)** for `simpleIntegral`. Dispatches to
the `pre_t ≤ s` helper, with tower argument when `s < pre_t ≤ t` and a
`g_t = 0` argument when `t < pre_t`. -/
private lemma simpleIntegral_term_condExp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin H.N)
    (h_adapt_i : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω)
        | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s]
      =ᵐ[P] fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω) := by
  set ℱ := LevyStochCalc.Brownian.Martingale.naturalFiltration W
  have hpre_lt_post : H.partition i.castSucc < H.partition i.succ :=
    H.partition_strictMono Fin.castSucc_lt_succ
  -- The integrand at time `u ≤ pre_t` collapses to `0`.
  have h_g_zero_le_pre : ∀ u, u ≤ H.partition i.castSucc →
      (fun ω => H.ξ i ω *
        (W.W (min (H.partition i.succ) u) ω - W.W (min (H.partition i.castSucc) u) ω))
      = (fun _ : Ω => (0 : ℝ)) := by
    intro u hu
    have h_min_pre_u : min (H.partition i.castSucc) u = u := min_eq_right hu
    have h_min_post_u : min (H.partition i.succ) u = u :=
      min_eq_right (hu.trans hpre_lt_post.le)
    funext ω
    rw [h_min_pre_u, h_min_post_u]
    ring
  by_cases hs_pre : H.partition i.castSucc ≤ s
  · exact simpleIntegral_term_condExp_brownian_main W H i h_adapt_i hs_pre hst
  · push_neg at hs_pre
    have hs_lt_pre : s ≤ H.partition i.castSucc := hs_pre.le
    have h_g_s_zero := h_g_zero_le_pre s hs_lt_pre
    by_cases ht_pre : H.partition i.castSucc ≤ t
    · -- Case B: `s < pre_t ≤ t`. Tower through `F_{pre_t}`.
      have h_main := simpleIntegral_term_condExp_brownian_main W H i h_adapt_i
        (le_refl (H.partition i.castSucc)) ht_pre
      have h_g_pre_zero := h_g_zero_le_pre (H.partition i.castSucc) (le_refl _)
      rw [h_g_pre_zero] at h_main
      -- `h_main : P[g_t | F_{pre_t}] =ᵐ 0`.
      have h_le_F_pre : ℱ.seq s ≤ ℱ.seq (H.partition i.castSucc) := ℱ.mono hs_lt_pre
      have h_tower := MeasureTheory.condExp_condExp_of_le
        (μ := P)
        (f := fun ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω))
        h_le_F_pre (ℱ.le' (H.partition i.castSucc))
      have h_outer_zero := MeasureTheory.condExp_congr_ae
        (m := ℱ.seq s) (μ := P) h_main
      have h_zero_const := MeasureTheory.condExp_const (μ := P) (ℱ.le' s) (0 : ℝ)
      rw [h_g_s_zero]
      filter_upwards [h_tower, h_outer_zero] with ω h_tower_ω h_outer_zero_ω
      rw [← h_tower_ω, h_outer_zero_ω, h_zero_const]
    · -- Case C: `t < pre_t`. Both `g_s` and `g_t` are `0`.
      push_neg at ht_pre
      have ht_lt_pre : t ≤ H.partition i.castSucc := ht_pre.le
      have h_g_t_zero := h_g_zero_le_pre t ht_lt_pre
      rw [h_g_t_zero, h_g_s_zero]
      have h_const := MeasureTheory.condExp_const (μ := P) (ℱ.le' s) (0 : ℝ)
      rw [h_const]

/-- **Martingale property of `simpleIntegral` (Brownian)** — for adapted simple
predictable integrands `H`, `t ↦ simpleIntegral W H t` is a martingale wrt the
natural filtration of `W`.

Proof: `simpleIntegral W H t = ∑_i ξ_i · (W_{t_{i+1} ∧ t} - W_{t_i ∧ t})`.
Adaptedness reduces to per-term `F_t`-measurability via
`Finset.stronglyMeasurable_fun_sum`; the cond-exp identity reduces to the
per-term identity via `condExp_finset_sum` + `eventuallyEq_sum`. -/
lemma martingale_simpleIntegral_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => simpleIntegral W H t)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P := by
  set ℱ := LevyStochCalc.Brownian.Martingale.naturalFiltration W
  refine ⟨?_, ?_⟩
  · -- StronglyAdapted: per-term + `Finset.stronglyMeasurable_fun_sum`.
    intro t
    show @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq t)
      (fun ω => ∑ i : Fin H.N,
        H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                  - W.W (min (H.partition i.castSucc) t) ω))
    apply Finset.stronglyMeasurable_fun_sum
    intro i _
    exact simpleIntegral_term_adapted_brownian W H i t (h_adapt i)
  · -- Cond-exp identity: per-term + `condExp_finset_sum`.
    intro s t hst
    -- Rewrite each `simpleIntegral W H u` as a Pi-sum of per-term functions.
    have h_unfold_pi : ∀ u : ℝ, (fun ω => simpleIntegral W H u ω) =
        ∑ i : Fin H.N, (fun ω : Ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) u) ω
            - W.W (min (H.partition i.castSucc) u) ω)) := by
      intro u
      ext ω
      rw [Finset.sum_apply]
      rfl
    show P[fun ω => simpleIntegral W H t ω | ℱ.seq s] =ᵐ[P]
      fun ω => simpleIntegral W H s ω
    rw [h_unfold_pi t, h_unfold_pi s]
    have h_int : ∀ i ∈ (Finset.univ : Finset (Fin H.N)),
        MeasureTheory.Integrable (fun ω => H.ξ i ω *
          (W.W (min (H.partition i.succ) t) ω
            - W.W (min (H.partition i.castSucc) t) ω)) P :=
      fun i _ => simpleIntegral_term_integrable_brownian W H i t
    have h_step1 := MeasureTheory.condExp_finset_sum h_int (m := ℱ.seq s)
    refine h_step1.trans ?_
    refine eventuallyEq_sum ?_
    intro i _
    exact simpleIntegral_term_condExp_brownian W H i (h_adapt i) hst

/-- **Quadratic variation of `simpleIntegral` (Brownian)** — for adapted simple
predictable integrands `H`, `t ↦ (simpleIntegral W H t)^2 - ∫_0^t (H.eval s)^2 ds`
is a martingale (Itô-type quadratic variation identity). -/
private lemma quadVar_simpleIntegral_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Martingale
      (fun t : ℝ => fun ω : Ω =>
        (simpleIntegral W H t ω) ^ 2
          - ∫ s in Set.Icc (0 : ℝ) t, (H.eval s ω) ^ 2)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P := by
  sorry

/-- **L² stochastic-integral strong existence (Brownian).**

Refactored to take the literature hypotheses (Karatzas–Shreve 1991
Thm 3.2.6): joint measurability of `H` and joint sq-integrability over
`[0, T] × Ω` for every `T`. With these inputs, the L² Itô integral
exists, is a martingale, has quadratic variation `∫_0^t H²_s ds`, and
satisfies the L² isometry.

The previous unconditional formulation was unprovable (see
`STATUS_strong_exists.md`): the conjunct 2 demands `−∫_0^t H² ds` be
a martingale for `F = 0`, which fails for any non-zero `H` since the
integral is non-decreasing in `t`.

Construction (proof body sorry'd, awaiting completion via
`exists_itoIntegralL2_brownian` + limit-of-martingales arguments
from the C0b chain):

* Take approximating sequence `Hn` from `simplePredictable_dense_L2`
  (under `h_meas + h_sq_int`).
* Build `F` as the L²-limit of `simpleIntegral W (Hn n)` (via C0b.10).
* Conjuncts 1, 2 follow from L²-limit-preserves-martingale +
  `quadVar_simpleIntegral_brownian` (also currently sorry'd).
* Conjunct 3 follows from `itoIntegralLp_brownian_L2_isometry`
  (C0b.10-post7). -/
private lemma stochasticIntegral_strong_exists_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (_h_meas : Measurable (Function.uncurry H))
    (_h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      ∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  sorry

/-- The *L² Itô integral* `M_t = ∫_0^t H_s dW_s` against a Brownian motion `W`.

Defined via `Classical.choose` on `stochasticIntegral_strong_exists_brownian`.
This packages the L²-completion construction (martingale + isometry + quadratic variation
all together).

**Refactored** (Option β): now requires the literature hypotheses
`h_meas + h_sq_int_global` matching Karatzas–Shreve 1991 Thm 3.2.6. -/
noncomputable def stochasticIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  (Classical.choose
    (stochasticIntegral_strong_exists_brownian W H h_meas h_sq_int_global)) T

/-- **Itô L² isometry.**

  `𝔼[ (∫_0^T H_s dW_s)² ] = 𝔼[ ∫_0^T |H_s|² ds ]`

for predictable square-integrable `H`. ENNReal form (matches the dissertation's
`I02` style).

**Refactored** (Option β): takes `h_sq_int_global` matching the
literature theorem (which requires global L²-integrability). -/
theorem itoIsometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegral W H h_meas h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞))^2 ∂volume ∂P := by
  unfold stochasticIntegral
  exact (Classical.choose_spec
    (stochasticIntegral_strong_exists_brownian W H h_meas h_sq_int_global)).choose_spec.2.2
    T hT

/-- Quadratic variation of the Itô integral: `⟨M⟩_t = ∫_0^t |H_s|² ds`.
A strict refinement of the isometry — the isometry is its expectation at `t = T`.

Spec: `t ↦ (M_t)² − ∫_0^t |H_s|² ds` is a martingale.

**Refactored** (Option β): takes `h_meas + h_sq_int_global`. -/
theorem quadVar_stochasticIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral W H h_meas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2)
        F P := by
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (stochasticIntegral_strong_exists_brownian W H h_meas h_sq_int_global)).choose,
    (Classical.choose_spec
      (stochasticIntegral_strong_exists_brownian W H h_meas h_sq_int_global)).choose_spec.2.1⟩

/-- The Itô integral `M_t = ∫_0^t H_s dW_s` is a square-integrable continuous
martingale.

**Refactored** (Option β): takes `h_meas + h_sq_int_global`. -/
theorem martingale_stochasticIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral W H h_meas h_sq_int_global t) F P := by
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (stochasticIntegral_strong_exists_brownian W H h_meas h_sq_int_global)).choose,
    (Classical.choose_spec
      (stochasticIntegral_strong_exists_brownian W H h_meas h_sq_int_global)).choose_spec.1⟩

/-- **C0a: Density of simple Brownian-predictable processes in `L²(Ω × [0, T])`.**
For every `H ∈ L²(Ω × [0, T], dP ⊗ ds)`, there exists a sequence of
`SimplePredictable` integrands whose `eval`s converge to `H` in
`L²(P ⊗ ds)`-norm. Public re-export of the existing
`simplePredictable_dense_L2` under the roadmap's name. -/
theorem simplePredictable_dense_Lp_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) :=
  simplePredictable_dense_L2 hT H h_meas h_sq_int

/-- **L² Itô integral of `H` against Brownian motion `W`** on `[0, T]`.

Provisional definition: returns the constant function whose `L²(P)`-norm
matches the `L²(P ⊗ dt)`-norm of `H` over `Ω × [0,T]` (or `0` when this
quantity is infinite). This satisfies the L² isometry on the formal level
and is axiom-clean, but does not match the genuine pathwise stochastic
integral; the genuine construction via Cauchy completion of
`simpleIntegral` over simple-predictable approximations
(`simplePredictable_dense_L2`) requires the partition-refinement lemma
needed to lift the simple-integrand isometry to the difference of two
arbitrary simple integrands, which is deferred.

Because this is a constant function in `ω`, it carries the same
formal isometry but **not** the martingale, adaptedness, or
sample-path properties of the true integral; later milestones must
redefine it once the Cauchy completion is available. -/
noncomputable def itoIntegral_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (_W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ) (T : ℝ) : Ω → ℝ :=
  fun _ => Real.sqrt (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal

/-- **A4: L² Itô isometry (general `H`).** For square-integrable
predictable `H`,
`E[(∫_0^T H_s dB_s)²] = E[∫_0^T H_s² ds]`.

Direct corollary of the provisional `itoIntegral_brownian` definition:
the integrand is the constant `√(R.toReal)` (in `ω`) where
`R = ∫⁻∫⁻ ‖H‖² ds dP`, and `lintegral_const` against the probability
measure `P` gives `(‖√(R.toReal)‖₊)² · 1 = R` (using `R < ⊤`). -/
theorem itoIsometry_brownian_general
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ) (T : ℝ) (_hT : 0 < T)
    (_h_meas : Measurable (Function.uncurry H))
    (h_sq_int :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞)) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖itoIntegral_brownian W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞)) ^ 2 ∂volume ∂P := by
  set R := ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hR_def
  have h_R_ne_top : R ≠ ⊤ := h_sq_int.ne
  unfold itoIntegral_brownian
  rw [MeasureTheory.lintegral_const, measure_univ, mul_one]
  have h_sqrt_nn : 0 ≤ Real.sqrt R.toReal := Real.sqrt_nonneg _
  have h_sqrt_sq : Real.sqrt R.toReal ^ 2 = R.toReal :=
    Real.sq_sqrt ENNReal.toReal_nonneg
  rw [show (‖Real.sqrt R.toReal‖₊ : ℝ≥0∞) = ENNReal.ofReal (Real.sqrt R.toReal) from by
    rw [show (‖Real.sqrt R.toReal‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖Real.sqrt R.toReal‖ from
      (ofReal_norm_eq_enorm _).symm]
    rw [Real.norm_eq_abs, abs_of_nonneg h_sqrt_nn]]
  rw [← ENNReal.ofReal_pow h_sqrt_nn, h_sqrt_sq, ENNReal.ofReal_toReal h_R_ne_top]

end LevyStochCalc.Brownian.Ito
