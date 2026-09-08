/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Analysis.DyadicGrid
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Dirac

/-!
# Sums of finitely many jumps along a dyadic grid

A finite set of points of `ℝ × E` with weights defines a step function of the time,
`jumpSum S c s`, the sum of the weights of the points with time in `(0, s]`, and its strict-past
version `jumpSumStrict S c s`. Along the dyadic grid of `[0, t]` the frozen values
`jumpSum S c (leftPt t n s)` are eventually the strict-past value, and the sums of the increments
over the cells weighted by a continuous function at the right endpoints converge to the sum of
the weights times the function at the points. A finite sum of Dirac masses integrates a function
over a time window to such a jump sum.
-/

open Filter MeasureTheory
open scoped Topology BigOperators

namespace LevyStochCalc.Analysis

variable {E : Type*}

section Sums

open scoped Classical in
/-- The sum of the weights of the points with time in `(0, s]`. -/
noncomputable def jumpSum (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) (s : ℝ) : ℝ :=
  ∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ s then c p else 0

open scoped Classical in
/-- The sum of the weights of the points with time in `(0, s)`. -/
noncomputable def jumpSumStrict (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) (s : ℝ) : ℝ :=
  ∑ p ∈ S, if 0 < p.1 ∧ p.1 < s then c p else 0

open scoped Classical in
/-- The increment of the jump sum over `(u, v]`. -/
theorem jumpSum_sub (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    jumpSum S c v - jumpSum S c u = ∑ p ∈ S, if u < p.1 ∧ p.1 ≤ v then c p else 0 := by
  unfold jumpSum
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h1 : 0 < p.1
  · by_cases h2 : p.1 ≤ u
    · rw [if_pos ⟨h1, h2.trans huv⟩, if_pos ⟨h1, h2⟩,
        if_neg (fun h => absurd h.1 (not_lt.mpr h2))]
      ring
    · by_cases h3 : p.1 ≤ v
      · rw [if_pos ⟨h1, h3⟩, if_neg (fun h => h2 h.2), if_pos ⟨lt_of_not_ge h2, h3⟩]
        ring
      · rw [if_neg (fun h => h3 h.2), if_neg (fun h => h2 h.2), if_neg (fun h => h3 h.2)]
        ring
  · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.1),
      if_neg (fun h => h1 (hu.trans_lt h.1))]
    ring

/-- The jump sum is bounded by the number of points times the bound on the weights. -/
theorem abs_jumpSum_le (S : Finset (ℝ × E)) {c : ℝ × E → ℝ} {C : ℝ} (hc : ∀ p, |c p| ≤ C)
    (s : ℝ) : |jumpSum S c s| ≤ S.card * C := by
  classical
  unfold jumpSum
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Nat.cast_one, one_mul]
  split_ifs
  · exact hc p
  · rw [abs_zero]; exact (abs_nonneg _).trans (hc p)

open scoped Classical in
/-- Without points in `(u, s)` the jump sum at `u < s` is the strict-past jump sum at `s`. -/
theorem jumpSum_eq_jumpSumStrict (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {u s : ℝ} (hus : u < s)
    (h : ∀ p ∈ S, ¬ (u < p.1 ∧ p.1 < s)) : jumpSum S c u = jumpSumStrict S c s := by
  unfold jumpSum jumpSumStrict
  refine Finset.sum_congr rfl fun p hp => ?_
  have hiff : (0 < p.1 ∧ p.1 ≤ u) ↔ (0 < p.1 ∧ p.1 < s) := by
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h1, h2.trans_lt hus⟩
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_contra h3
      exact h p hp ⟨lt_of_not_ge h3, h2⟩
  simp only [hiff]

/-- A positive gap below `s` clearing the finitely many points before `s`. -/
theorem exists_gap (S : Finset (ℝ × E)) (s : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ S, p.1 < s → p.1 + δ ≤ s := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, one_pos, fun p hp => absurd hp (Finset.notMem_empty p)⟩
  | insert q S _ ih =>
    obtain ⟨δ, hδ, hS⟩ := ih
    by_cases hq : q.1 < s
    · refine ⟨min δ (s - q.1), lt_min hδ (sub_pos.mpr hq), fun p hp hps => ?_⟩
      rcases Finset.mem_insert.mp hp with rfl | hp'
      · linarith [min_le_right δ (s - p.1)]
      · linarith [hS p hp' hps, min_le_left δ (s - q.1)]
    · exact ⟨δ, hδ, fun p hp hps => by
        rcases Finset.mem_insert.mp hp with rfl | hp'
        · exact absurd hps hq
        · exact hS p hp' hps⟩

/-- Along the dyadic grid the frozen jump sums are eventually the strict-past jump sum. -/
theorem eventually_jumpSum_leftPt (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {t : ℝ} (ht : 0 < t)
    {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n : ℕ in atTop, jumpSum S c (leftPt t n s) = jumpSumStrict S c s := by
  obtain ⟨δ, hδ, hgap⟩ := exists_gap S s
  have hlim : Tendsto (fun n : ℕ => t / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul t
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow, ← div_eq_mul_inv]
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with n hn
  refine jumpSum_eq_jumpSumStrict S c (leftPt_lt ht n hs) fun p hp ⟨h1, h2⟩ => ?_
  have := hgap p hp h2
  have := le_leftPt_add ht n hs
  linarith

/-- The right endpoint of the cell of the dyadic partition of level `n` containing `s`. -/
noncomputable def rightPt (t : ℝ) (n : ℕ) (s : ℝ) : ℝ := leftPt t n s + t / 2 ^ n

theorem tendsto_rightPt {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => rightPt t n s) atTop (𝓝 s) := by
  have hlim : Tendsto (fun n : ℕ => t / 2 ^ n) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)).const_mul t
    simp only [mul_zero] at this
    refine this.congr fun n => ?_
    rw [one_div, inv_pow, ← div_eq_mul_inv]
  simpa [rightPt] using (tendsto_leftPt ht hs).add hlim

theorem rightPt_eq_dyadicPartition_succ {t : ℝ} (ht : 0 < t) (n : ℕ) {s : ℝ} (hs : 0 < s)
    (hst : s ≤ t) :
    rightPt t n s
      = dyadicPartition t n (Fin.succ ⟨leftIdx t n s, leftIdx_lt ht n hs hst⟩) := by
  rw [dyadicPartition_succ]
  rfl

open scoped Classical in
/-- **The Riemann sum of a continuous function against the jumps.** Weighting the increments of
the jump sum over the cells of the dyadic grid by a function at the right endpoints gives the
sum of the weights times the function at the right endpoints of the cells of the points. -/
theorem sum_mul_jumpSum_sub (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) (X : ℝ → ℝ) {t : ℝ}
    (ht : 0 < t) (n : ℕ) :
    ∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ)
        * (jumpSum S c (dyadicPartition t n k.succ) - jumpSum S c (dyadicPartition t n k.castSucc))
      = ∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ t then X (rightPt t n p.1) * c p else 0 := by
  have hmono := dyadicPartition_strictMono ht n
  have h0 : ∀ k : Fin (2 ^ n), 0 ≤ dyadicPartition t n k.castSucc := fun k => by
    rw [← dyadicPartition_zero t n]
    exact hmono.monotone (Fin.zero_le _)
  simp_rw [fun k : Fin (2 ^ n) => jumpSum_sub S c (h0 k)
    (hmono (Fin.castSucc_lt_succ (i := k))).le, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : 0 < p.1 ∧ p.1 ≤ t
  · rw [if_pos hp]
    set k : Fin (2 ^ n) := ⟨leftIdx t n p.1, leftIdx_lt ht n hp.1 hp.2⟩ with hk
    have hmem : dyadicPartition t n k.castSucc < p.1 ∧ p.1 ≤ dyadicPartition t n k.succ := by
      refine ⟨leftPt_lt ht n hp.1, ?_⟩
      rw [dyadicPartition_succ]
      exact le_leftPt_add ht n hp.1
    rw [Finset.sum_eq_single k]
    · rw [if_pos hmem, rightPt_eq_dyadicPartition_succ ht n hp.1 hp.2]
    · intro i _ hik
      rw [mul_ite, mul_zero, if_neg]
      rintro ⟨h1, h2⟩
      apply hik
      have hi1 : i.castSucc < k.succ := hmono.lt_iff_lt.mp (h1.trans_le hmem.2)
      have hi2 : k.castSucc < i.succ := hmono.lt_iff_lt.mp (hmem.1.trans_le h2)
      apply Fin.ext
      have e1 : (i : ℕ) < (k : ℕ) + 1 := by simpa [Fin.lt_def] using hi1
      have e2 : (k : ℕ) < (i : ℕ) + 1 := by simpa [Fin.lt_def] using hi2
      omega
    · intro hk'
      exact absurd (Finset.mem_univ k) hk'
  · rw [if_neg hp]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [mul_ite, mul_zero, if_neg]
    rintro ⟨h1, h2⟩
    exact hp ⟨(h0 k).trans_lt h1, h2.trans (dyadicPartition_le ht n _)⟩

open scoped Classical in
/-- The Riemann sums of a continuous function against the jumps converge to the sum of the
weights times the function at the points. -/
theorem tendsto_sum_mul_jumpSum_sub (S : Finset (ℝ × E)) (c : ℝ × E → ℝ) {X : ℝ → ℝ}
    (hX : Continuous X) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n : ℕ => ∑ k : Fin (2 ^ n), X (dyadicPartition t n k.succ)
        * (jumpSum S c (dyadicPartition t n k.succ)
          - jumpSum S c (dyadicPartition t n k.castSucc)))
      atTop (𝓝 (∑ p ∈ S, if 0 < p.1 ∧ p.1 ≤ t then X p.1 * c p else 0)) := by
  simp_rw [sum_mul_jumpSum_sub S c X ht]
  refine tendsto_finsetSum _ fun p _ => ?_
  by_cases hp : 0 < p.1 ∧ p.1 ≤ t
  · simp only [if_pos hp]
    exact ((hX.tendsto _).comp (tendsto_rightPt ht hp.1)).mul_const _
  · simp only [if_neg hp]
    exact tendsto_const_nhds

end Sums

section Dirac

variable [MeasurableSpace E] [MeasurableSingletonClass E]

open scoped Classical in
/-- A finite sum of Dirac masses integrates a function over a time window to the jump sum of
the masses times the values. -/
theorem setIntegral_Ioc_of_eq_sum_dirac {μ : Measure (ℝ × E)} [IsFiniteMeasure μ]
    {S : Finset (ℝ × E)} (hμ : μ = ∑ p ∈ S, μ {p} • Measure.dirac p) (g : ℝ × E → ℝ)
    (s : ℝ) :
    ∫ p in Set.Ioc (0 : ℝ) s ×ˢ Set.univ, g p ∂μ
      = jumpSum S (fun p => (μ {p}).toReal * g p) s := by
  rw [← integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure fun p _ =>
    (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)]
  unfold jumpSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  by_cases hp : 0 < p.1 ∧ p.1 ≤ s
  · rw [if_pos hp, Set.indicator_of_mem (by simpa using hp)]
  · rw [if_neg hp, Set.indicator_of_notMem (by simpa using hp), mul_zero]

open scoped Classical in
/-- The strict-past version. -/
theorem setIntegral_Ioo_of_eq_sum_dirac {μ : Measure (ℝ × E)} [IsFiniteMeasure μ]
    {S : Finset (ℝ × E)} (hμ : μ = ∑ p ∈ S, μ {p} • Measure.dirac p) (g : ℝ × E → ℝ)
    (s : ℝ) :
    ∫ p in Set.Ioo (0 : ℝ) s ×ˢ Set.univ, g p ∂μ
      = jumpSumStrict S (fun p => (μ {p}).toReal * g p) s := by
  rw [← integral_indicator (measurableSet_Ioo.prod MeasurableSet.univ)]
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure fun p _ =>
    (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)]
  unfold jumpSumStrict
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul]
  by_cases hp : 0 < p.1 ∧ p.1 < s
  · rw [if_pos hp, Set.indicator_of_mem (by simpa using hp)]
  · rw [if_neg hp, Set.indicator_of_notMem (by simpa using hp), mul_zero]

end Dirac

end LevyStochCalc.Analysis
