/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CondCellProjection
import LevyStochCalc.Brownian.ItoDensityUnbounded
import LevyStochCalc.Brownian.ItoAlgebraSimpleIntegrand

/-!
# Convergence of the conditional cell projections

For a progressively measurable process `Z` of finite energy on `[0, T]`, `T > 0`, and any
filtration, the cell-projection error on the uniform grid of `N` cells tends to `0` as
`N → ∞`. The proof approximates `Z` by adapted simple integrands: on a cell containing no
partition point of the simple integrand in its interior, the simple integrand is a random
constant measurable at the left endpoint, and at most one cell per partition point is not of
this kind, so optimality of the conditional cell averages bounds the error by twice the
approximation error plus a term of order `T / N`.

As a consequence a uniform bound `E ‖Z̄_i‖² ≤ B` on the conditional cell averages of all cells
of all uniform grids passes to `E ‖Z_t‖² ≤ B` for almost every `t ∈ [0, T]`.

## Main statements

* `tendsto_cellProjError_zero` — the cell-projection error tends to `0`.
* `ae_lintegral_sq_le_of_condCellAvg_le` — a uniform bound on the conditional cell averages
  bounds the second moment of the process at almost every time.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.PathRegularity

open LevyStochCalc.Brownian.Ito (SimplePredictable)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Simple

variable {T : ℝ}

/-- The value of a simple integrand just after the time `t`. -/
private noncomputable def valueAfter (H : SimplePredictable Ω T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ j : Fin H.N, if H.partition j.castSucc ≤ t ∧ t < H.partition j.succ then H.ξ j ω else 0

private theorem exists_bound (H : SimplePredictable Ω T) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ s ω, |H.eval s ω| ≤ B) ∧ ∀ t ω, |valueAfter H t ω| ≤ B := by
  classical
  choose M hM using H.ξ_bounded
  refine ⟨∑ i : Fin H.N, max (M i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun s ω => ?_, fun t ω => ?_⟩
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    split_ifs
    · exact (hM i ω).trans (le_max_left _ _)
    · rw [abs_zero]; exact le_max_right _ _
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    split_ifs
    · exact (hM i ω).trans (le_max_left _ _)
    · rw [abs_zero]; exact le_max_right _ _

private theorem stronglyMeasurable_valueAfter (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (H : SimplePredictable Ω T)
    (hH : ∀ j : Fin H.N, StronglyMeasurable[ℱ (H.partition j.castSucc)] (H.ξ j)) (t : ℝ) :
    StronglyMeasurable[ℱ t] (valueAfter H t) := by
  refine Finset.stronglyMeasurable_fun_sum _ fun j _ => ?_
  by_cases h : H.partition j.castSucc ≤ t ∧ t < H.partition j.succ
  · simp only [if_pos h]
    exact (hH j).mono (ℱ.mono h.1)
  · simp only [if_neg h]
    exact stronglyMeasurable_const

private theorem memLp_valueAfter (H : SimplePredictable Ω T) (t : ℝ) :
    MemLp (valueAfter H t) 2 P := by
  obtain ⟨B, -, -, hB⟩ := exists_bound H
  have hm : Measurable (valueAfter H t) := by
    refine Finset.measurable_sum _ fun j _ => ?_
    by_cases h : H.partition j.castSucc ≤ t ∧ t < H.partition j.succ
    · simp only [if_pos h]; exact H.ξ_measurable j
    · simp only [if_neg h]; exact measurable_const
  exact MemLp.of_bound hm.aestronglyMeasurable B
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hB t ω)

/-- A cell of the uniform grid of step `τ` holding a partition point of `H` in its interior. -/
private def IsBadCell (H : SimplePredictable Ω T) (τ : ℝ) (i : ℕ) : Prop :=
  ∃ j : Fin (H.N + 1), (i : ℝ) * τ < H.partition j ∧ H.partition j < ((i : ℝ) + 1) * τ

private theorem eval_eq_valueAfter (H : SimplePredictable Ω T) {τ : ℝ} {i : ℕ}
    (hgood : ¬ IsBadCell H τ i) {s : ℝ} (hs : s ∈ Set.Ioc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ))
    (ω : Ω) : H.eval s ω = valueAfter H ((i : ℝ) * τ) ω := by
  refine Finset.sum_congr rfl fun j _ => ?_
  have hnot : ∀ p : Fin (H.N + 1), ¬ ((i : ℝ) * τ < H.partition p
      ∧ H.partition p < ((i : ℝ) + 1) * τ) := fun p hp => hgood ⟨p, hp⟩
  have c1 : H.partition j.castSucc < s ↔ H.partition j.castSucc ≤ (i : ℝ) * τ := by
    constructor
    · intro h
      by_contra h'
      exact hnot j.castSucc ⟨lt_of_not_ge h', lt_of_lt_of_le h hs.2⟩
    · intro h; exact lt_of_le_of_lt h hs.1
  have c2 : s ≤ H.partition j.succ ↔ (i : ℝ) * τ < H.partition j.succ := by
    constructor
    · intro h; exact lt_of_lt_of_le hs.1 h
    · intro h
      by_contra h'
      exact hnot j.succ ⟨h, lt_of_lt_of_le (lt_of_not_ge h') hs.2⟩
  simp only [c1, c2]

private theorem card_bad_le (H : SimplePredictable Ω T) {τ : ℝ} (hτ : 0 < τ) (N : ℕ)
    [DecidablePred (IsBadCell H τ)] :
    ((Finset.range N).filter (IsBadCell H τ)).card ≤ H.N + 1 := by
  classical
  let t : Fin (H.N + 1) → Finset ℕ := fun j => (Finset.range N).filter fun i =>
    (i : ℝ) * τ < H.partition j ∧ H.partition j < ((i : ℝ) + 1) * τ
  have hsub : (Finset.range N).filter (IsBadCell H τ) ⊆ Finset.univ.biUnion t := by
    intro i hi
    obtain ⟨hiN, j, hj⟩ := Finset.mem_filter.mp hi
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨hiN, hj⟩⟩
  have hone : ∀ j, (t j).card ≤ 1 := by
    intro j
    refine Finset.card_le_one.mpr fun i hi i' hi' => ?_
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hi
    obtain ⟨-, h1', h2'⟩ := Finset.mem_filter.mp hi'
    have a : (i : ℝ) < (i' : ℝ) + 1 := by
      by_contra h; have h := not_lt.mp h; nlinarith
    have b : (i' : ℝ) < (i : ℝ) + 1 := by
      by_contra h; have h := not_lt.mp h; nlinarith
    have a' : i < i' + 1 := by exact_mod_cast a
    have b' : i' < i + 1 := by exact_mod_cast b
    omega
  calc ((Finset.range N).filter (IsBadCell H τ)).card
      ≤ (Finset.univ.biUnion t).card := Finset.card_le_card hsub
    _ ≤ ∑ j, (t j).card := Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin (H.N + 1), 1 := Finset.sum_le_sum fun j _ => hone j
    _ = H.N + 1 := by simp

private theorem cell_bound (H : SimplePredictable Ω T) {τ : ℝ} (i : ℕ) {B : ℝ}
    (hB : ∀ s ω, |H.eval s ω| ≤ B) (hB' : ∀ t ω, |valueAfter H t ω| ≤ B)
    [Decidable (IsBadCell H τ i)] :
    ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        (‖H.eval s ω - valueAfter H ((i : ℝ) * τ) ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ if IsBadCell H τ i then ENNReal.ofReal ((2 * B) ^ 2 * τ) else 0 := by
  split_ifs with hbad
  · have hpt : ∀ ω s, (‖H.eval s ω - valueAfter H ((i : ℝ) * τ) ω‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal ((2 * B) ^ 2) := by
      intro ω s
      rw [nnnorm_sq_eq_ofReal]
      refine ENNReal.ofReal_le_ofReal (sq_le_sq.mpr ?_)
      have h1 := hB s ω
      have h2 := hB' ((i : ℝ) * τ) ω
      have hB0 : 0 ≤ B := (abs_nonneg _).trans h1
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ 2 * B)]
      calc |H.eval s ω - valueAfter H ((i : ℝ) * τ) ω|
          ≤ |H.eval s ω| + |valueAfter H ((i : ℝ) * τ) ω| := abs_sub _ _
        _ ≤ 2 * B := by linarith
    calc ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
          (‖H.eval s ω - valueAfter H ((i : ℝ) * τ) ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ _ω, ∫⁻ _s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
          ENNReal.ofReal ((2 * B) ^ 2) ∂volume ∂P :=
          lintegral_mono fun ω => lintegral_mono fun s => hpt ω s
      _ = ENNReal.ofReal ((2 * B) ^ 2 * τ) := by
          rw [setLIntegral_const, lintegral_const, measure_univ, mul_one, Real.volume_Icc,
            ← ENNReal.ofReal_mul (sq_nonneg _)]
          congr 2
          ring
  · refine le_of_eq ?_
    refine (lintegral_congr fun ω => ?_).trans lintegral_zero
    rw [setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume)).symm]
    refine (setLIntegral_congr_fun measurableSet_Ioc fun s hs => ?_).trans lintegral_zero
    rw [eval_eq_valueAfter H hbad hs ω, sub_self, nnnorm_zero, ENNReal.coe_zero,
      zero_pow two_ne_zero]

end Simple

section Convergence

variable {d : ℕ} (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}

private theorem nnnorm_add_sq_le (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖x‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖y‖₊ : ℝ≥0∞) ^ 2 := by
  rw [nnnorm_sq_eq_ofReal, nnnorm_sq_eq_ofReal, nnnorm_sq_eq_ofReal,
    ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (x - y)])

omit [IsProbabilityMeasure P] in
private theorem lintegral_two_add {I : Set ℝ} {f g : Ω → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) :
    ∫⁻ ω, ∫⁻ s in I, (2 * f ω s + 2 * g ω s) ∂volume ∂P
      = 2 * ∫⁻ ω, ∫⁻ s in I, f ω s ∂volume ∂P + 2 * ∫⁻ ω, ∫⁻ s in I, g ω s ∂volume ∂P := by
  have h1 : ∀ ω, ∫⁻ s in I, (2 * f ω s + 2 * g ω s) ∂volume
      = 2 * ∫⁻ s in I, f ω s ∂volume + 2 * ∫⁻ s in I, g ω s ∂volume := by
    intro ω
    have hf' : Measurable (f ω) := hf.comp measurable_prodMk_left
    have hg' : Measurable (g ω) := hg.comp measurable_prodMk_left
    rw [lintegral_add_left (hf'.const_mul 2), lintegral_const_mul _ hf',
      lintegral_const_mul _ hg']
  have hmf : Measurable fun ω => ∫⁻ s in I, f ω s ∂volume := hf.lintegral_prod_right'
  have hmg : Measurable fun ω => ∫⁻ s in I, g ω s ∂volume := hg.lintegral_prod_right'
  simp_rw [h1]
  rw [lintegral_add_left (hmf.const_mul 2), lintegral_const_mul _ hmf,
    lintegral_const_mul _ hmg]

/-- The cell-projection error is at most twice the approximation error of adapted simple
integrands plus a term of order `T / N` counting the cells cut by their partitions. -/
private theorem cellProjError_le_simple (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (H : Fin d → SimplePredictable Ω T)
    (hHa : ∀ k, ∀ j : Fin (H k).N, StronglyMeasurable[ℱ ((H k).partition j.castSucc)] ((H k).ξ j))
    {B : Fin d → ℝ} (hB : ∀ k s ω, |(H k).eval s ω| ≤ B k)
    (hB' : ∀ k t ω, |valueAfter (H k) t ω| ≤ B k) :
    cellProjError ℱ P T N Z
      ≤ 2 * ∑ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T,
          (‖Z s ω k - (H k).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        + 2 * ∑ k, ENNReal.ofReal ((((H k).N : ℝ) + 1) * (2 * B k) ^ 2 * (T / N)) := by
  classical
  set τ : ℝ := T / N with hτdef
  have hτ : 0 < τ := div_pos hT (by exact_mod_cast hN)
  have hNτ : (N : ℝ) * τ = T := by rw [hτdef]; field_simp
  have hvm : ∀ (k : Fin d) (t : ℝ), Measurable (valueAfter (H k) t) := fun k t =>
    ((stronglyMeasurable_valueAfter ℱ (H k) (hHa k) t).mono (ℱ.le t)).measurable
  have hA : ∀ k, Measurable (Function.uncurry fun ω s =>
      (‖Z s ω k - (H k).eval s ω‖₊ : ℝ≥0∞) ^ 2) := fun k =>
    ((hZm k).sub (H k).measurable_uncurry_eval).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hBm : ∀ (k : Fin d) (t : ℝ), Measurable (Function.uncurry fun ω s =>
      (‖(H k).eval s ω - valueAfter (H k) t ω‖₊ : ℝ≥0∞) ^ 2) := fun k t =>
    (((H k).measurable_uncurry_eval).sub
      ((hvm k t).comp measurable_fst)).nnnorm.coe_nnreal_ennreal.pow_const 2
  have step1 := cellProjError_le ℱ hT hN hZm hZs
    (η := fun i ω k => valueAfter (H k) ((i : ℝ) * τ) ω)
    (fun i _ k => stronglyMeasurable_valueAfter ℱ (H k) (hHa k) _)
    (fun i _ k => memLp_valueAfter (H k) _)
  refine step1.trans ?_
  have step2 : ∀ i ∈ Finset.range N,
      ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
          ∑ k, (‖Z s ω k - valueAfter (H k) ((i : ℝ) * τ) ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∑ k, (2 * ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
            (‖Z s ω k - (H k).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
          + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
            (‖(H k).eval s ω - valueAfter (H k) ((i : ℝ) * τ) ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) := by
    intro i _
    calc _ ≤ ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
          ∑ k, (2 * (‖Z s ω k - (H k).eval s ω‖₊ : ℝ≥0∞) ^ 2
            + 2 * (‖(H k).eval s ω - valueAfter (H k) ((i : ℝ) * τ) ω‖₊ : ℝ≥0∞) ^ 2)
            ∂volume ∂P := by
          refine lintegral_mono fun ω => lintegral_mono fun s => Finset.sum_le_sum fun k _ => ?_
          have := nnnorm_add_sq_le (Z s ω k - (H k).eval s ω)
            ((H k).eval s ω - valueAfter (H k) ((i : ℝ) * τ) ω)
          simpa only [sub_add_sub_cancel] using this
      _ = _ := by
          rw [lintegral_setLIntegral_finsetSum fun k =>
            ((hA k).const_mul 2).add ((hBm k _).const_mul 2)]
          exact Finset.sum_congr rfl fun k _ => lintegral_two_add (hA k) (hBm k _)
  refine (Finset.sum_le_sum step2).trans ?_
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  refine add_le_add (le_of_eq ?_) ?_
  · congr 1
    rw [lintegral_sum_cells_lintegral (hA k) hτ.le N, hNτ]
  · refine mul_le_mul_right ?_ 2
    calc _ ≤ ∑ i ∈ Finset.range N,
          (if IsBadCell (H k) τ i then ENNReal.ofReal ((2 * B k) ^ 2 * τ) else 0) :=
          Finset.sum_le_sum fun i _ => cell_bound (H k) i (hB k) (hB' k)
      _ = ((Finset.range N).filter (IsBadCell (H k) τ)).card
            * ENNReal.ofReal ((2 * B k) ^ 2 * τ) := by
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
      _ ≤ (((H k).N : ℝ≥0∞) + 1) * ENNReal.ofReal ((2 * B k) ^ 2 * τ) := by
          gcongr
          exact_mod_cast card_bad_le (H k) hτ N
      _ = _ := by
          rw [show (((H k).N : ℝ≥0∞) + 1) = ENNReal.ofReal (((H k).N : ℝ) + 1) by
              rw [ENNReal.ofReal_add (by positivity) zero_le_one, ENNReal.ofReal_natCast,
                ENNReal.ofReal_one],
            ← ENNReal.ofReal_mul (by positivity), mul_assoc]

/-- **Convergence of the conditional cell projections.** For a progressively measurable
process of finite energy on `[0, T]`, `T > 0`, and any filtration, the cell-projection error on
the uniform grid of `N` cells tends to `0` as `N → ∞`. -/
theorem tendsto_cellProjError_zero (hT : 0 < T)
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Tendsto (fun N : ℕ => cellProjError ℱ P T N Z) atTop (𝓝 0) := by
  have hdens := fun k => Brownian.Ito.adaptedSimple_dense_L2_brownian (P := P) ℱ hT
    (fun ω s => Z s ω k) (hZm k) (hZp k) (hZs k)
  choose Hn hHa hHt using hdens
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hsum : Tendsto (fun n => 2 * ∑ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T,
      (‖Z s ω k - (Hn k n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) atTop (𝓝 0) := by
    have := tendsto_finsetSum Finset.univ fun k _ => hHt k
    simpa using ENNReal.Tendsto.const_mul this (Or.inr ENNReal.ofNat_ne_top)
  have hε2 : 0 < ε / 2 := ENNReal.half_pos hε.ne'
  obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp hsum (ε / 2) hε2).exists
  choose B _ hB hB' using fun k => exists_bound (Hn k n)
  have hrest : Tendsto (fun N : ℕ => 2 * ∑ k,
      ENNReal.ofReal ((((Hn k n).N : ℝ) + 1) * (2 * B k) ^ 2 * (T / N))) atTop (𝓝 0) := by
    have h1 : ∀ k, Tendsto (fun N : ℕ =>
        ENNReal.ofReal ((((Hn k n).N : ℝ) + 1) * (2 * B k) ^ 2 * (T / N))) atTop (𝓝 0) := by
      intro k
      have := (tendsto_const_div_atTop_nhds_zero_nat T).const_mul
        ((((Hn k n).N : ℝ) + 1) * (2 * B k) ^ 2)
      rw [mul_zero] at this
      simpa using ENNReal.tendsto_ofReal this
    have := tendsto_finsetSum Finset.univ fun k _ => h1 k
    simpa using ENNReal.Tendsto.const_mul this (Or.inr ENNReal.ofNat_ne_top)
  filter_upwards [ENNReal.tendsto_nhds_zero.mp hrest (ε / 2) hε2, eventually_gt_atTop 0]
    with N hN hN0
  calc cellProjError ℱ P T N Z
      ≤ _ := cellProjError_le_simple ℱ hT hN0 hZm hZs (fun k => Hn k n) (fun k => hHa k n) hB hB'
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hN
    _ = ε := ENNReal.add_halves ε

private theorem nnnorm_sq_le_weighted {δ : ℝ} (hδ : 0 < δ) (x y : ℝ) :
    (‖x‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (1 + δ) * (‖y‖₊ : ℝ≥0∞) ^ 2
        + ENNReal.ofReal (1 + δ⁻¹) * (‖x - y‖₊ : ℝ≥0∞) ^ 2 := by
  rw [nnnorm_sq_eq_ofReal, nnnorm_sq_eq_ofReal, nnnorm_sq_eq_ofReal,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have key : 0 ≤ δ * ((1 + δ) * y ^ 2 + (1 + δ⁻¹) * (x - y) ^ 2 - x ^ 2) := by
    have e : δ * ((1 + δ) * y ^ 2 + (1 + δ⁻¹) * (x - y) ^ 2 - x ^ 2)
        = (δ * y - (x - y)) ^ 2 := by field_simp; ring
    rw [e]; exact sq_nonneg _
  have := (mul_nonneg_iff_of_pos_left hδ).mp key
  linarith

/-- The per-grid inequality behind the lower-semicontinuity lemma: for `δ > 0` the energy of
`Z` over a measurable set `A ⊆ [0, T]` is at most `(1 + δ) B |A| + (1 + δ⁻¹)` times the
cell-projection error. -/
private theorem setLIntegral_le_weighted (hT : 0 < T)
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    {B : ℝ} {N : ℕ} (hN : 0 < N)
    (hB : ∀ i < N, ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P (T / N) Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal B)
    {A : Set ℝ} (hA : MeasurableSet A) {δ : ℝ} (hδ : 0 < δ) :
    ∫⁻ t in Set.Icc 0 T, A.indicator (fun t => ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P) t
      ≤ ENNReal.ofReal (1 + δ)
          * (∫⁻ t in Set.Icc 0 T, A.indicator (fun _ => ENNReal.ofReal B) t)
        + ENNReal.ofReal (1 + δ⁻¹) * cellProjError ℱ P T N Z := by
  set τ : ℝ := T / N with hτdef
  have hτ : 0 < τ := div_pos hT (by exact_mod_cast hN)
  have hNτ : (N : ℝ) * τ = T := by rw [hτdef]; field_simp
  have hcm : ∀ i k, Measurable fun ω => condCellAvg ℱ P τ Z i ω k := fun i k =>
    ((stronglyMeasurable_condCellAvg ℱ i k).mono (ℱ.le _)).measurable
  have hE : ∀ i, Measurable (Function.uncurry fun ω t =>
      ∑ k, (‖Z t ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2) := fun i =>
    Finset.measurable_sum _ fun k _ =>
      ((hZm k).sub ((hcm i k).comp measurable_fst)).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hφ : Measurable (Function.uncurry fun ω t => ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2) :=
    Finset.measurable_sum _ fun k _ => (hZm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  have hL : ∀ g : ℝ → ℝ≥0∞, ∫⁻ t in Set.Icc 0 T, g t
      = ∑ i ∈ Finset.range N, ∫⁻ t in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), g t := by
    intro g; rw [lintegral_sum_cells _ hτ.le, hNτ]
  rw [hL, hL, Finset.mul_sum, cellProjError, ← hτdef, Finset.mul_sum]
  refine (Finset.sum_le_sum fun i hi => ?_).trans (le_of_eq Finset.sum_add_distrib)
  have hiN : i < N := Finset.mem_range.mp hi
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      ∑ k, (‖Z s ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), ∫⁻ ω,
          ∑ k, (‖Z s ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ∂volume :=
    lintegral_lintegral_swap (hE i).aemeasurable
  rw [hswap]
  have hem : Measurable fun t => ∫⁻ ω,
      ∑ k, (‖Z t ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P := (hE i).lintegral_prod_left'
  have him : Measurable fun t => ENNReal.ofReal (1 + δ)
      * A.indicator (fun _ => ENNReal.ofReal B) t :=
    (measurable_const.indicator hA).const_mul _
  rw [← lintegral_const_mul _ (measurable_const.indicator hA), ← lintegral_const_mul _ hem,
    ← lintegral_add_left him]
  refine lintegral_mono fun t => ?_
  by_cases ht : t ∈ A
  · simp only [Set.indicator_of_mem ht]
    have hm1 : Measurable fun ω => ENNReal.ofReal (1 + δ)
        * ∑ k, (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 :=
      (Finset.measurable_sum _ fun k _ =>
        (hcm i k).nnnorm.coe_nnreal_ennreal.pow_const 2).const_mul _
    have hm2 : Measurable fun ω => ∑ k, (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 :=
      Finset.measurable_sum _ fun k _ => (hcm i k).nnnorm.coe_nnreal_ennreal.pow_const 2
    have hm3 : Measurable fun ω =>
        ∑ k, (‖Z t ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 :=
      Finset.measurable_sum _ fun k _ =>
        ((((hZm k).comp (measurable_prodMk_right (y := t))).sub
          (hcm i k)).nnnorm.coe_nnreal_ennreal.pow_const 2)
    calc ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ ω, (ENNReal.ofReal (1 + δ) * ∑ k, (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal (1 + δ⁻¹)
              * ∑ k, (‖Z t ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_le_sum fun k _ => nnnorm_sq_le_weighted hδ _ _
      _ = ENNReal.ofReal (1 + δ) * ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
          + ENNReal.ofReal (1 + δ⁻¹) * ∫⁻ ω,
            ∑ k, (‖Z t ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P := by
          rw [lintegral_add_left hm1, lintegral_const_mul _ hm2, lintegral_const_mul _ hm3]
      _ ≤ _ := by gcongr; exact hB i hiN
  · simp only [Set.indicator_of_notMem ht, mul_zero, zero_add]
    exact zero_le

/-- **Lower semicontinuity of the second moment along the conditional cell averages.** For a
progressively measurable process of finite energy on `[0, T]`, `T > 0`, a bound
`E ‖Z̄_i‖² ≤ B` on the conditional cell averages of every cell of every uniform grid of `[0, T]`
gives `E ‖Z_t‖² ≤ B` for almost every `t ∈ [0, T]`. -/
theorem ae_lintegral_sq_le_of_condCellAvg_le (hT : 0 < T)
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {B : ℝ} (hB : ∀ N : ℕ, 0 < N → ∀ i < N,
      ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P (T / N) Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal B) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal B := by
  have hφ : Measurable (Function.uncurry fun ω t => ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2) :=
    Finset.measurable_sum _ fun k _ => (hZm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  refine ae_le_of_forall_setLIntegral_le_of_sigmaFinite (g := fun _ => ENNReal.ofReal B)
    hφ.lintegral_prod_left' fun A hA _ => ?_
  rw [← lintegral_indicator hA, ← lintegral_indicator hA]
  change ∫⁻ t in Set.Icc 0 T, A.indicator
      (fun t => ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P) t
    ≤ ∫⁻ t in Set.Icc 0 T, A.indicator (fun _ => ENNReal.ofReal B) t
  generalize hR : ∫⁻ t in Set.Icc 0 T, A.indicator (fun _ => ENNReal.ofReal B) t = R
  have hδ : ∀ n : ℕ, ∫⁻ t in Set.Icc 0 T, A.indicator
      (fun t => ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P) t
      ≤ ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * R := by
    intro n
    have hδ0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hlim : Tendsto (fun N : ℕ => ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * R
        + ENNReal.ofReal (1 + (1 / ((n : ℝ) + 1))⁻¹) * cellProjError ℱ P T N Z) atTop
        (𝓝 (ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * R + 0)) := by
      refine tendsto_const_nhds.add ?_
      have := ENNReal.Tendsto.const_mul (tendsto_cellProjError_zero ℱ hT hZm hZp hZs)
        (a := ENNReal.ofReal (1 + (1 / ((n : ℝ) + 1))⁻¹)) (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at this
    rw [add_zero] at hlim
    refine ge_of_tendsto hlim ?_
    filter_upwards [eventually_gt_atTop 0] with N hN
    have := setLIntegral_le_weighted ℱ hT hZm hN (hB N hN) hA hδ0
    rw [← hR]
    exact this
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal (1 + 1 / ((n : ℝ) + 1)) * R) atTop
      (𝓝 (1 * R)) := by
    refine ENNReal.Tendsto.mul_const ?_ (Or.inl one_ne_zero)
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_add 1
    rw [add_zero] at this
    simpa using ENNReal.tendsto_ofReal this
  rw [one_mul] at hlim
  exact ge_of_tendsto' hlim hδ

end Convergence

end LevyStochCalc.BSDEJ.PathRegularity
