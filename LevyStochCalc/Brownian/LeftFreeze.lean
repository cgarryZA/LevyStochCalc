/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoAlgebra
import LevyStochCalc.Brownian.ItoLinear
import LevyStochCalc.Analysis.DyadicGrid

/-!
# Freezing a bounded adapted process at the left endpoints of a dyadic grid

Freezing a bounded adapted process `Y` at the left endpoints of the dyadic partition of `[0, t]`
of level `n` (`Analysis/DyadicGrid.lean`) gives a simple predictable integrand
`leftFreeze Y t n`, whose value at a time `s ∈ (0, t]` is `Y` at the left endpoint `leftPt t n s`
of the cell containing `s`. When the
frozen values converge, at every positive time and almost every sample point, to a bounded
process `Y₋`, the Itô integrals of `leftFreeze Y t n · H` converge in `L²` to the Itô integral of
`Y₋ · H`, by the difference isometry and dominated convergence.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Ito

open LevyStochCalc.Analysis

universe u

variable {Ω : Type u} [MeasurableSpace Ω]


section Freeze

variable (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  {t : ℝ} (ht : 0 < t) (n : ℕ)

/-- The process frozen at the left endpoints of the dyadic partition of `[0, t]` of level
`n`. -/
noncomputable def leftFreeze : SimplePredictable Ω t where
  N := 2 ^ n
  partition := dyadicPartition t n
  partition_zero := dyadicPartition_zero t n
  partition_le_T := (dyadicPartition_last t n).le
  partition_strictMono := dyadicPartition_strictMono ht n
  ξ := fun k => Y (dyadicPartition t n k.castSucc)
  ξ_bounded := fun _ => ⟨C, fun ω => hYb _ ω⟩
  ξ_measurable := fun _ => hYm _

theorem leftFreeze_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s)) :
    ∀ i : Fin (leftFreeze Y hYb hYm ht n).N,
      StronglyMeasurable[ℱ ((leftFreeze Y hYb hYm ht n).partition i.castSucc)]
        ((leftFreeze Y hYb hYm ht n).ξ i) :=
  fun _ => hYad _

/-- On `(0, t]` the frozen process is `Y` at the left endpoint of the cell. -/
theorem leftFreeze_eval {s : ℝ} (hs : 0 < s) (hst : s ≤ t) (ω : Ω) :
    (leftFreeze Y hYb hYm ht n).eval s ω = Y (leftPt t n s) ω := by
  unfold SimplePredictable.eval
  dsimp only [leftFreeze]
  set k : Fin (2 ^ n) := ⟨leftIdx t n s, leftIdx_lt ht n hs hst⟩ with hk
  have hmem : dyadicPartition t n k.castSucc < s ∧ s ≤ dyadicPartition t n k.succ := by
    refine ⟨leftPt_lt ht n hs, ?_⟩
    rw [dyadicPartition_succ]
    exact le_leftPt_add ht n hs
  rw [Finset.sum_eq_single k]
  · rw [if_pos hmem]
    rfl
  · intro i _ hik
    rw [if_neg]
    rintro ⟨h1, h2⟩
    apply hik
    have hmono := dyadicPartition_strictMono ht n
    have hi1 : i.castSucc < k.succ := hmono.lt_iff_lt.mp (h1.trans_le hmem.2)
    have hi2 : k.castSucc < i.succ := hmono.lt_iff_lt.mp (hmem.1.trans_le h2)
    apply Fin.ext
    have e1 : (i : ℕ) < (k : ℕ) + 1 := by simpa [Fin.lt_def] using hi1
    have e2 : (k : ℕ) < (i : ℕ) + 1 := by simpa [Fin.lt_def] using hi2
    omega
  · intro hk'
    exact absurd (Finset.mem_univ k) hk'

/-- The frozen process is bounded by the bound of `Y` on `(0, t]`. -/
theorem abs_leftFreeze_eval_le {s : ℝ} (hs : 0 < s) (hst : s ≤ t) (ω : Ω) :
    |(leftFreeze Y hYb hYm ht n).eval s ω| ≤ C := by
  rw [leftFreeze_eval Y hYb hYm ht n hs hst]
  exact hYb _ ω

/-- The elementary integral of the frozen process against a process is the sum of the frozen
values times the increments of the process over the cells. -/
theorem leftFreeze_integralAgainst (M : ℝ → Ω → ℝ) (ω : Ω) :
    (leftFreeze Y hYb hYm ht n).integralAgainst M t ω
      = ∑ k : Fin (2 ^ n), Y (dyadicPartition t n k.castSucc) ω
          * (M (dyadicPartition t n k.succ) ω - M (dyadicPartition t n k.castSucc) ω) := by
  unfold SimplePredictable.integralAgainst
  dsimp only [leftFreeze]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [min_eq_left (dyadicPartition_le ht n _), min_eq_left (dyadicPartition_le ht n _)]

end Freeze

section Limit

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (Y : ℝ → Ω → ℝ) {C : ℝ} (hYb : ∀ s ω, |Y s ω| ≤ C) (hYm : ∀ s, Measurable (Y s))
  (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s)) {t : ℝ} (ht : 0 < t)

include hℱ in
/-- **The frozen Itô integrals converge.** If the frozen values converge at every positive time
to a bounded process `Y₋`, the Itô integrals of the frozen integrands converge in `L²` to the
Itô integral of `Y₋ · H`. -/
theorem tendsto_lintegral_sq_sub_leftFreeze (Yminus : ℝ → Ω → ℝ)
    (hYmb : ∀ s ω, |Yminus s ω| ≤ C)
    (hmm' : Measurable (Function.uncurry fun ω s => Yminus s ω * H ω s))
    (hmp' : Probability.ProgressivelyMeasurable ℱ fun ω s => Yminus s ω * H ω s)
    (hmq' : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hconv : ∀ᵐ ω ∂P, ∀ s, 0 < s → s ≤ t →
      Tendsto (fun n : ℕ => Y (leftPt t n s) ω) atTop (𝓝 (Yminus s ω))) :
    Tendsto (fun n : ℕ => ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (leftFreeze Y hYb hYm ht n).eval s ω * H ω s)
        ((leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm)
        ((leftFreeze Y hYb hYm ht n).progressivelyMeasurable_eval_mul ℱ
          (leftFreeze_adapt Y hYb hYm ht n ℱ hYad) hp)
        ((leftFreeze Y hYb hYm ht n).lintegral_eval_mul_sq_lt_top hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq' t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by
  have hiso : ∀ n : ℕ, (∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => (leftFreeze Y hYb hYm ht n).eval s ω * H ω s)
        ((leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm)
        ((leftFreeze Y hYb hYm ht n).progressivelyMeasurable_eval_mul ℱ
          (leftFreeze_adapt Y hYb hYm ht n ℱ hYad) hp)
        ((leftFreeze Y hYb hYm ht n).lintegral_eval_mul_sq_lt_top hq) t ω
      - stochasticIntegralBrownian W ℱ hℱ (fun ω s => Yminus s ω * H ω s) hmm' hmp' hmq' t ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P :=
    fun n => isometry_diff_stochasticIntegralBrownian W ℱ hℱ _ _ _ _ _ _ _ _ ht
  rw [tendsto_congr hiso]
  set K : ℝ≥0∞ := ENNReal.ofReal ((2 * |C|) ^ 2) with hK
  have hK' : K ≠ ⊤ := ENNReal.ofReal_ne_top
  have h0 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), s ≠ 0 := by
    rw [ae_iff]
    simp only [ne_eq, not_not, Set.setOf_eq_eq_singleton,
      Measure.restrict_apply (measurableSet_singleton (0 : ℝ))]
    exact measure_mono_null Set.inter_subset_left Real.volume_singleton
  -- the pointwise bound on `(0, t]`
  have hpt : ∀ (n : ℕ) (ω : Ω) (s : ℝ), 0 < s → s ≤ t →
      (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ K * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro n ω s hs hst
    rw [← sub_mul, sq_nnnorm_eq_ofReal_sq, sq_nnnorm_eq_ofReal_sq, hK,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_pow]
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    calc |(leftFreeze Y hYb hYm ht n).eval s ω - Yminus s ω|
        ≤ |(leftFreeze Y hYb hYm ht n).eval s ω| + |Yminus s ω| := abs_sub _ _
      _ ≤ C + C := add_le_add (abs_leftFreeze_eval_le Y hYb hYm ht n hs hst ω) (hYmb s ω)
      _ ≤ 2 * |C| := by linarith [le_abs_self C]
  -- measurability
  have hHmeas : Measurable fun p : Ω × ℝ => (‖H p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp hm)).pow_const 2
  have hHint : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    hHmeas.lintegral_prod_right'
  have hjoint : ∀ n : ℕ, Measurable fun p : Ω × ℝ =>
      (‖(leftFreeze Y hYb hYm ht n).eval p.2 p.1 * H p.1 p.2 - Yminus p.2 p.1 * H p.1 p.2‖₊
        : ℝ≥0∞) ^ 2 := fun n =>
    (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp
      (((leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm).sub hmm'))).pow_const 2
  have hslice : ∀ (n : ℕ) (ω : Ω), Measurable fun s : ℝ =>
      (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro n ω
    have h1 : Measurable fun s : ℝ => (leftFreeze Y hYb hYm ht n).eval s ω * H ω s :=
      ((leftFreeze Y hYb hYm ht n).measurable_uncurry_eval_mul hm).comp measurable_prodMk_left
    have h2 : Measurable fun s : ℝ => Yminus s ω * H ω s := hmm'.comp measurable_prodMk_left
    exact (measurable_coe_nnreal_ennreal.comp (measurable_nnnorm.comp (h1.sub h2))).pow_const 2
  have hFmeas : ∀ n : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume :=
    fun n => (hjoint n).lintegral_prod_right'
  have hfin : ∫⁻ ω, K * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := by
    rw [lintegral_const_mul' _ _ hK']
    exact ENNReal.mul_ne_top hK' (hq t ht).ne
  have hbdd : ∀ n : ℕ, ∀ᵐ ω ∂P, (∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume) ≤ K * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := fun n =>
    Filter.Eventually.of_forall fun ω => by
      rw [← lintegral_const_mul' _ _ hK']
      refine lintegral_mono_ae ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
      exact hpt n ω s (lt_of_le_of_ne hs.1 hs0.symm) hs.2
  have hHfin : ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    ae_lt_top hHint (hq t ht).ne
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume) atTop (𝓝 0) := by
    filter_upwards [hconv, hHfin] with ω hω hHω
    have hptw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), Tendsto (fun n : ℕ =>
        (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s - Yminus s ω * H ω s‖₊ : ℝ≥0∞) ^ 2)
        atTop (𝓝 0) := by
      filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
      have hs' : 0 < s := lt_of_le_of_ne hs.1 hs0.symm
      have h1 : Tendsto (fun n => (leftFreeze Y hYb hYm ht n).eval s ω) atTop
          (𝓝 (Yminus s ω)) :=
        (hω s hs' hs.2).congr fun n => (leftFreeze_eval Y hYb hYm ht n hs' hs.2 ω).symm
      have h2 : Tendsto (fun n => (leftFreeze Y hYb hYm ht n).eval s ω * H ω s
          - Yminus s ω * H ω s) atTop (𝓝 0) := by
        have := (h1.mul_const (H ω s)).sub (tendsto_const_nhds (x := Yminus s ω * H ω s))
        simpa using this
      have h3 : Tendsto (fun n => (‖(leftFreeze Y hYb hYm ht n).eval s ω * H ω s
          - Yminus s ω * H ω s‖₊ : ℝ≥0∞)) atTop (𝓝 0) := by
        rw [← ENNReal.coe_zero]
        exact ENNReal.tendsto_coe.mpr (by simpa using h2.nnnorm)
      simpa using (ENNReal.Tendsto.pow (n := 2) h3)
    have hdom := tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) t)) (f := fun _ => 0)
      (fun s => K * (‖H ω s‖₊ : ℝ≥0∞) ^ 2) (fun n => hslice n ω)
      (fun n => by
        filter_upwards [ae_restrict_mem measurableSet_Icc, h0] with s hs hs0
        exact hpt n ω s (lt_of_le_of_ne hs.1 hs0.symm) hs.2)
      (by rw [lintegral_const_mul' _ _ hK']; exact ENNReal.mul_ne_top hK' hHω.ne) hptw
    simpa using hdom
  have hmain := tendsto_lintegral_of_dominated_convergence (μ := P) (f := fun _ => 0)
    (fun ω => K * ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas hbdd hfin hlim
  simpa using hmain

end Limit

end LevyStochCalc.Brownian.Ito
