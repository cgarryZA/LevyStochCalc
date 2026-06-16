/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoSimple

/-!
# Density of simple predictable processes in L²

Dyadic approximation of `L²(Ω × [0,T])` integrands by simple predictable
processes, giving the density results `simplePredictable_dense_L2` and
`adaptedSimple_dense_L2_brownian` that extend the Itô integral off the simple
class. Builds on `Brownian/ItoSimple.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is avoided at file scope; explicit decidability is used.

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Pointwise truncation tendsto** (Brownian, mirror of Compensated). -/
private lemma truncation_pointwise_tendsto_brownian (x : ℝ) :
    Filter.Tendsto
      (fun M : ℕ => (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2)
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
  change (0 : ℝ≥0∞) = (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
  rw [h_clip, sub_self]
  simp

/-- **Pointwise truncation dominated** (Brownian, mirror of Compensated). -/
private lemma truncation_dominated_brownian (x : ℝ) (M : ℕ) :
    (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
      ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h_abs : |x - max (-(M : ℝ)) (min (M : ℝ) x)| ≤ |x| := by
    by_cases hx : 0 ≤ x
    · by_cases hxM : x ≤ M
      · rw [min_eq_right hxM, max_eq_right (by linarith)]
        simp [abs_nonneg]
      · push Not at hxM
        rw [min_eq_left (le_of_lt hxM), max_eq_right (by linarith : -(M : ℝ) ≤ M)]
        rw [abs_of_nonneg (by linarith : 0 ≤ x - M), abs_of_nonneg hx]
        linarith
    · push Not at hx
      by_cases hxM : -(M : ℝ) ≤ x
      · rw [min_eq_right (by linarith : x ≤ M), max_eq_right hxM]
        simp
      · push Not at hxM
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
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Truncation L² convergence (Brownian).** Mirror of Compensated. -/
lemma truncation_L2_converges_brownian
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
    rw [show (0 : ℝ≥0∞)
        = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0:ℝ) T)) from by simp]
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
`(‖x + y‖₊)² ≤ 2 · ((‖x‖₊)² + (‖y‖₊)²)`. Used to lift pointwise
bounds to lintegral bounds in the diagonal selection of
`simplePredictable_dense_L2`. -/
lemma sq_nnnorm_add_le_two_mul_brownian (x y : ℝ) :
    (‖x + y‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖x‖₊ : ℝ≥0∞) ^ 2 + (‖y‖₊ : ℝ≥0∞) ^ 2) := by
  have h_norm_sq : ∀ z : ℝ, (‖z‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (z ^ 2) :=
    fun z => by
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
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
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

private lemma dyadicPartition_brownian_le_T {T : ℝ} (_hT : 0 < T) (n : ℕ) :
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
    simp [Fin.val_succ]
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by
    simp [Fin.val_castSucc]
  rw [hi_succ, hi_castSucc]
  ring

-- `omit` the unused `[MeasurableSpace Ω]` section variable (this lemma's
-- `g : Ω → ℝ → ℝ` does not need it).
omit [MeasurableSpace Ω] in
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

-- `omit` the unused `[MeasurableSpace Ω]` section variable.
omit [MeasurableSpace Ω] in
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
  change @MeasureTheory.StronglyMeasurable Ω ℝ _
    ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
      (dyadicPartition_brownian T n i.castSucc))
    (dyadicAvg_shifted_brownian T g n i)
  exact dyadicAvg_shifted_brownian_adapted W T g h_progMeas n i

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
    change |dyadicAvg_brownian (T := T) g n i ω| ≤ M
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

-- `omit` the unused `[MeasurableSpace Ω]` section variable.
omit [MeasurableSpace Ω] in
/-- **Average bridge:**
`dyadicAvg n i ω = ⨍ y in closedBall(midpoint, halfLen), g(ω, y) ∂volume`.

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
  rw [show (volume.restrict (Set.Icc t_i t_succ) : Measure ℝ)
        = volume.restrict (Set.Ioc t_i t_succ)
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
    change dyadicPartition_brownian T n i.castSucc = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_castSucc]
  have h_partition_succ : φ.partition i.succ =
      (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    change dyadicPartition_brownian T n i.succ = _
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
  change (∑ j : Fin φ.N, if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                       then φ.ξ j ω else 0) = dyadicAvg_brownian g n i ω
  change (∑ j : Fin (2 ^ n), if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                            then φ.ξ j ω else 0) = dyadicAvg_brownian g n i ω
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
    change dyadicAvg_brownian (T := T) g n i ω = dyadicAvg_brownian g n i ω
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
    change dyadicPartition_brownian T n i.castSucc = _
    unfold dyadicPartition_brownian
    push_cast
    simp [Fin.val_castSucc]
  have h_partition_succ : φ.partition i.succ =
      (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    change dyadicPartition_brownian T n i.succ = _
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
  change (∑ j : Fin φ.N, if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                       then φ.ξ j ω else 0) = dyadicAvg_shifted_brownian T g n i ω
  change (∑ j : Fin (2 ^ n), if φ.partition j.castSucc < s ∧ s ≤ φ.partition j.succ
                            then φ.ξ j ω else 0) = dyadicAvg_shifted_brownian T g n i ω
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
    change dyadicAvg_shifted_brownian T g n i ω = dyadicAvg_shifted_brownian T g n i ω
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
          (fun j => ⨍ y in Metric.closedBall (w j) (δ j), g ω y ∂volume)
            l (nhds (g ω x)) := by
  have h_loc_int : MeasureTheory.LocallyIntegrable (g ω) volume :=
    bounded_locallyIntegrable (g ω)
      (h_meas.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s))))
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
    change (dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ -
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
    have h_2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have h_pow_atTop : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ))
          Filter.atTop Filter.atTop := by
        have : Filter.Tendsto (fun n : ℕ => (2 ^ n : ℕ)) Filter.atTop Filter.atTop :=
          tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2)
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
    change |x - w n| ≤ δ n
    have h_mem := dyadicIndex_mem n T hT x hx
    set t_i := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc with ht_i
    set t_succ := dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ with ht_succ
    have h_x1 : t_i < x := by
      have h := h_mem.1
      change dyadicPartition_brownian T n (dyadicIndex n T hT x hx).castSucc < x
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.val_castSucc] using h
    have h_x2 : x ≤ t_succ := by
      have h := h_mem.2
      change x ≤ dyadicPartition_brownian T n (dyadicIndex n T hT x hx).succ
      unfold dyadicPartition_brownian
      push_cast at h ⊢
      simpa [Fin.val_succ] using h
    change |x - (t_i + t_succ) / 2| ≤ (t_succ - t_i) / 2
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

Proof: `Tendsto _ atTop (𝓝 (g ω s))` is equivalent to
`Tendsto (eval n - g ω s) atTop (𝓝 0)`,
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
          ≤ |g p.1 p.2|
            + |(dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1| :=
        abs_sub _ _
      rw [hCC]; linarith
    have h_norm_nn : 0 ≤ ‖g p.1 p.2 -
        (dyadicSimplePredictable_brownian hT g h_meas M h_bound n).eval p.2 p.1‖ := norm_nonneg _
    change (‖g p.1 p.2 -
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
    change Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
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
    change Filter.Tendsto (fun n => (‖g p.1 p.2 -
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
    change 0 < T / (2 * (2 ^ n : ℕ))
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
    push Not at h_not_pos
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
    change |x - w n| ≤ 3 * δ n
    have hi_mem := dyadicIndex_mem n T hT x hx
    have h_x_lower : ((dyadicIndex n T hT x hx).val : ℝ) * T / ((2 ^ n : ℕ) : ℝ) < x :=
      hi_mem.1
    have h_x_upper :
        x ≤ (((dyadicIndex n T hT x hx).val : ℝ) + 1) * T / ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hi_mem.2
    set i_val : ℝ := ((dyadicIndex n T hT x hx).val : ℝ) with hi_val
    have h_pos_real : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pos_real
    change |x - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))| ≤ 3 * (T / (2 * (2 ^ n : ℕ)))
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
      have h_alg :
          (i_val + 1) * T / ((2 ^ n : ℕ) : ℝ)
            - (i_val - 1/2) * (T / ((2 ^ n : ℕ) : ℝ))
            = 3 * (T / (2 * ((2 ^ n : ℕ) : ℝ))) := by
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
      change (((dyadicIndex n T hT x hx).val : ℝ) - 1/2) *
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
      change T / (2 * ((2 ^ n : ℕ) : ℝ)) = T / ((2 ^ n : ℕ) : ℝ) / 2
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
lemma predictableDyadicSimple_brownian_L2_converges
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
        · push Not at hM
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
    change (‖g p.1 p.2 -
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
    change Measurable (fun (p : Ω × ℝ) => (‖g p.1 p.2 -
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
    change Filter.Tendsto (fun n => (‖g p.1 p.2 -
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

/-- **Partition endpoint of `predictableDyadicSimple_brownian` is T.** Trivially
inherited from `dyadicPartition_brownian_last`. -/
lemma predictableDyadicSimple_brownian_partition_last
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    (predictableDyadicSimple_brownian hT g h_meas M h_bound n).partition
      (Fin.last (predictableDyadicSimple_brownian hT g h_meas M h_bound n).N)
      = T := by
  change dyadicPartition_brownian T n (Fin.last (2 ^ n)) = T
  exact dyadicPartition_brownian_last T n

/-- **Joint measurability of `predictableDyadicSimple_brownian.eval`.**
The eval `(p : Ω × ℝ) ↦ (Hn n).eval p.2 p.1` is jointly measurable.
Uses the indicator-sum decomposition. -/
lemma predictableDyadicSimple_brownian_eval_jointly_measurable
    {T : ℝ} (hT : 0 < T) (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) (n : ℕ) :
    Measurable (fun (p : Ω × ℝ) =>
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

/-- **Generic joint measurability of `SimplePredictable.eval`.** For any
`SimplePredictable Ω T`, the function `(p : Ω × ℝ) ↦ H.eval p.2 p.1` is measurable.

Proof: `eval` is a finite sum of indicator-times-coefficient terms, each measurable
since the indicator's set is `{p | partition i.castSucc < p.2 ≤ partition i.succ}`
(measurable in `snd`) and the coefficient is `H.ξ i ∘ fst` (measurable since
`H.ξ_measurable i`). -/
lemma SimplePredictable.eval_jointly_measurable
    {T : ℝ} (H : SimplePredictable Ω T) :
    Measurable (fun (p : Ω × ℝ) => H.eval p.2 p.1) := by
  unfold SimplePredictable.eval
  refine Finset.measurable_sum _ ?_
  intro i _
  refine Measurable.ite ?_ ?_ measurable_const
  · refine MeasurableSet.inter ?_ ?_
    · exact measurable_snd (measurableSet_Ioi (a := H.partition i.castSucc))
    · exact measurable_snd (measurableSet_Iic (a := H.partition i.succ))
  · exact (H.ξ_measurable i).comp measurable_fst

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **L²-Cauchy from L²-tendsto.** If a sequence `(Hn n).eval` converges to `H`
in `L²` (lintegral form), then `(Hn n).eval` is L²-Cauchy.

Triangle inequality `(a+b)² ≤ 2(a²+b²)` plus `Filter.Tendsto.eventually_lt_const`
for strict `<`. Takes joint measurability of `Hn n` and `H`. -/
lemma L2_cauchy_of_L2_tendsto_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ}
    (Hn : ℕ → SimplePredictable Ω T)
    (H : Ω → ℝ → ℝ)
    (h_meas_eval : ∀ n, Measurable (fun (p : Ω × ℝ) => (Hn n).eval p.2 p.1))
    (h_meas_H : Measurable (Function.uncurry H))
    (h_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0)) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε := by
  intro ε hε_pos
  have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
    rw [ENNReal.div_pos_iff]
    refine ⟨hε_pos.ne', ?_⟩
    decide
  have h_eventually := h_tendsto.eventually_lt_const hε4_pos
  rw [Filter.eventually_atTop] at h_eventually
  obtain ⟨N, hN⟩ := h_eventually
  refine ⟨N, fun n m hn hm => ?_⟩
  have h_pointwise : ∀ ω s,
      (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * ((‖(Hn n).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2
            + (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
    intro ω s
    have h_sum : ((Hn n).eval s ω - H ω s) + (H ω s - (Hn m).eval s ω)
        = (Hn n).eval s ω - (Hn m).eval s ω := by ring
    have := sq_nnnorm_add_le_two_mul_brownian
      ((Hn n).eval s ω - H ω s) (H ω s - (Hn m).eval s ω)
    rw [h_sum] at this
    exact this
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖(Hn n).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖(Hn n).eval s ω - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_A_eq : ∀ ω s, A ω s = (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    simp only [hA]
    congr 1
    rw [show (Hn n).eval s ω - H ω s = -(H ω s - (Hn n).eval s ω) from by ring]
    rw [nnnorm_neg]
  have h_int_A_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P) < ε / 4 := by
    have h_eq : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      congr 1
      ext ω
      congr 1
      ext s
      exact h_A_eq ω s
    rw [h_eq]
    exact hN n hn
  have h_int_B_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) < ε / 4 := by
    change ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε / 4
    exact hN m hm
  have h_meas_A_s : ∀ ω, Measurable (fun s => A ω s) := by
    intro ω
    simp only [hA]
    have h_eval_n_meas : Measurable (fun s => (Hn n).eval s ω) :=
      (h_meas_eval n).comp (by fun_prop : Measurable (fun s : ℝ => ((ω, s) : Ω × ℝ)))
    have h_H_meas : Measurable (fun s : ℝ => H ω s) :=
      h_meas_H.comp (by fun_prop : Measurable (fun s : ℝ => (ω, s)))
    exact ((ENNReal.continuous_coe.measurable.comp
      (h_eval_n_meas.sub h_H_meas).nnnorm)).pow_const 2
  have h_meas_A_outer : Measurable (fun ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume) := by
    have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
      simp only [hA]
      have h_eval_n_pair : Measurable (fun (q : Ω × ℝ) =>
          (Hn n).eval q.2 q.1) := h_meas_eval n
      have h_H_pair : Measurable (fun (q : Ω × ℝ) => H q.1 q.2) :=
        h_meas_H.comp (by fun_prop : Measurable (fun (q : Ω × ℝ) => (q.1, q.2)))
      exact ((ENNReal.continuous_coe.measurable.comp
        (h_eval_n_pair.sub h_H_pair).nnnorm)).pow_const 2
    exact Measurable.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair
  have h_C_int_le :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
    have h_inner : ∀ ω,
        (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
          2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
      intro ω
      calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
            MeasureTheory.lintegral_mono (h_pointwise ω)
        _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
            rw [MeasureTheory.lintegral_const_mul']
            simp
        _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
            congr 1
            rw [MeasureTheory.lintegral_add_left']
            exact (h_meas_A_s ω).aemeasurable
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ ∫⁻ ω,
            2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
          MeasureTheory.lintegral_mono h_inner
      _ = 2 * ∫⁻ ω,
            ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
          rw [MeasureTheory.lintegral_const_mul']
          simp
      _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
          congr 1
          rw [MeasureTheory.lintegral_add_left']
          exact h_meas_A_outer.aemeasurable
  have h_AB_sum_lt :
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
      + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P < ε / 4 + ε / 4 :=
    ENNReal.add_lt_add h_int_A_lt h_int_B_lt
  have h_2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h_2_ne_top : (2 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have h_2_sum_lt :
      (2 : ℝ≥0∞) * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
      + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) <
      (2 : ℝ≥0∞) * (ε / 4 + ε / 4) :=
    ENNReal.mul_right_strictMono h_2_ne_zero h_2_ne_top h_AB_sum_lt
  have h_eq_ε : (2 : ℝ≥0∞) * (ε / 4 + ε / 4) = ε := by
    rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
    exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num)
  rw [h_eq_ε] at h_2_sum_lt
  exact lt_of_le_of_lt h_C_int_le h_2_sum_lt

/-- **L²-Cauchy of `predictableDyadicSimple_brownian` evals.** Direct corollary of
`predictableDyadicSimple_brownian_L2_converges` + `L2_cauchy_of_L2_tendsto_brownian`. -/
lemma predictableDyadicSimple_brownian_L2_cauchy
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ, N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω -
          (predictableDyadicSimple_brownian hT g h_meas M h_bound m).eval s ω‖₊
          : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε :=
  L2_cauchy_of_L2_tendsto_brownian
    (fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n) g
    (fun n => predictableDyadicSimple_brownian_eval_jointly_measurable hT g h_meas M
      h_bound n)
    h_meas
    (predictableDyadicSimple_brownian_L2_converges hT g h_meas M h_bound)

/-- **Reverse triangle for eLpNorm (tsub form).** Standard consequence of
`eLpNorm_add_le`: `eLpNorm f - eLpNorm g ≤ eLpNorm (f - g)` (ENNReal truncated). -/
private lemma eLpNorm_sub_eLpNorm_le_eLpNorm_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f g : α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm g p μ
      ≤ MeasureTheory.eLpNorm (f - g) p μ := by
  rw [tsub_le_iff_left]
  have h_decomp : f = g + (f - g) := by ext x; simp
  have h_meas_diff : MeasureTheory.AEStronglyMeasurable (f - g) μ := hf.sub hg
  conv_lhs => rw [h_decomp]
  exact MeasureTheory.eLpNorm_add_le hg h_meas_diff hp

/-- **L²-norm continuity from L²-difference vanishing.** If
`eLpNorm (fn n - f) p μ → 0`, then `eLpNorm (fn n) p μ → eLpNorm f p μ`.

Squeeze argument:
* upper bound `eLpNorm (fn n) ≤ eLpNorm f + eLpNorm (fn n - f)` from
  `fn n = f + (fn n - f)` plus triangle (`eLpNorm_add_le`);
* lower bound `eLpNorm f - eLpNorm (fn n - f) ≤ eLpNorm (fn n)` from
  the same decomposition with the role of `f` and `fn n` swapped.

Both bounds tend to `eLpNorm f` (upper via `Tendsto.const_add`, lower via
`ENNReal.Tendsto.sub`); squeeze closes the proof. -/
private lemma eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f : α → E} {fn : ℕ → α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (h_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n - f) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n) p μ) Filter.atTop
      (nhds (MeasureTheory.eLpNorm f p μ)) := by
  have h_upper : ∀ n, MeasureTheory.eLpNorm (fn n) p μ ≤
      MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ := by
    intro n
    have h_decomp : fn n = f + (fn n - f) := by ext x; simp
    have h_meas_diff : MeasureTheory.AEStronglyMeasurable (fn n - f) μ :=
      (hfn n).sub hf
    conv_lhs => rw [h_decomp]
    exact MeasureTheory.eLpNorm_add_le hf h_meas_diff hp
  have h_lower : ∀ n,
      MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ
        ≤ MeasureTheory.eLpNorm (fn n) p μ := by
    intro n
    rw [tsub_le_iff_right]
    have h_decomp : f = fn n + -(fn n - f) := by ext x; simp
    have h_meas_diff : MeasureTheory.AEStronglyMeasurable (fn n - f) μ :=
      (hfn n).sub hf
    have h_meas_neg_diff : MeasureTheory.AEStronglyMeasurable (-(fn n - f)) μ :=
      h_meas_diff.neg
    calc MeasureTheory.eLpNorm f p μ
        = MeasureTheory.eLpNorm (fn n + -(fn n - f)) p μ := by rw [← h_decomp]
      _ ≤ MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (-(fn n - f)) p μ :=
          MeasureTheory.eLpNorm_add_le (hfn n) h_meas_neg_diff hp
      _ = MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (fn n - f) p μ := by
          rw [MeasureTheory.eLpNorm_neg]
  have h_lower_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := ENNReal.Tendsto.sub
      (tendsto_const_nhds (x := MeasureTheory.eLpNorm f p μ))
      h_tendsto (Or.inr ENNReal.zero_ne_top)
    simpa using h
  have h_upper_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := h_tendsto.const_add (MeasureTheory.eLpNorm f p μ)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    h_lower_tendsto h_upper_tendsto h_lower h_upper

/-- **Bridge: nested-lintegral-of-squared-norm = `eLpNorm²` on product measure.**

For any `ℝ`-valued `h : Ω × ℝ → ℝ` measurable and `μ`-SFinite,
`∫⁻ ω, ∫⁻ s in Icc 0 T, ‖h (ω, s)‖₊² ∂vol ∂μ`
`  = eLpNorm h 2 (μ.prod (vol.restrict (Icc 0 T))) ^ 2`.
Tonelli + `eLpNorm_nnreal_pow_eq_lintegral` (instantiated at `p = 2`). -/
lemma lintegral_sq_eq_eLpNorm_sq_on_prod_brownian
    {μ : Measure Ω} [SFinite μ] {T : ℝ} (h : Ω × ℝ → ℝ) (hh : Measurable h) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖h (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
      = MeasureTheory.eLpNorm h 2
          (μ.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ^ (2 : ℝ) := by
  set μν := μ.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμν
  have h_aem_sq : AEMeasurable
      (fun p : Ω × ℝ => (‖h p‖₊ : ℝ≥0∞) ^ 2) μν :=
    (hh.enorm.pow_const 2).aemeasurable
  -- Tonelli on the squared integrand.
  have h_Tonelli :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖h (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = ∫⁻ p, (‖h p‖₊ : ℝ≥0∞) ^ 2 ∂μν := by
    rw [MeasureTheory.lintegral_prod _ h_aem_sq]
  rw [h_Tonelli]
  -- Bridge: ∫⁻ p, (‖h p‖₊ : ℝ≥0∞)^2 ∂μν = eLpNorm h 2 μν ^ (2:ℝ).
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := μν) (p := (2 : NNReal)) (f := h)
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  -- h_pow_lemma : eLpNorm h 2 μν ^ (2:ℝ) = ∫⁻ p, ‖h p‖ₑ ^ (2:ℝ) ∂μν
  rw [h_pow_lemma]
  -- Goal: ∫⁻ p, (‖h p‖₊ : ℝ≥0∞)^2 ∂μν
  --   = ∫⁻ p, ‖h p‖ₑ ^ (2:ℝ) ∂μν
  refine lintegral_congr (fun p => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl

/-- **General eval-norm-tendsto from diff-norm-tendsto, lintegral form.**

For any sequence of jointly-measurable `(p ↦ ev_n p.2 p.1)` and jointly-measurable
target `H` such that `∫⁻ ω, ∫⁻ s in [0,T], ‖H ω s - ev_n s ω‖₊² → 0`, we have
`∫⁻ ω, ∫⁻ s in [0,T], ‖ev_n s ω‖₊²`
`  → ∫⁻ ω, ∫⁻ s in [0,T], ‖H ω s‖₊²`.

Proof: bridge to `eLpNorm² _ 2 (μ.prod (vol.restrict (Icc 0 T)))` via Tonelli; the
square-root step gives `eLpNorm (F - Fn) → 0`; reverse-triangle squeeze
(`eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero`) closes; square back. -/
lemma lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian
    {μ : Measure Ω} [SFinite μ]
    {T : ℝ}
    (H : Ω → ℝ → ℝ) (h_H_meas : Measurable (Function.uncurry H))
    (ev : ℕ → ℝ → Ω → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : Ω × ℝ) => ev n p.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)) := by
  set μν := μ.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμν
  set F : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hF_def
  set Fn : ℕ → Ω × ℝ → ℝ := fun n p => ev n p.2 p.1 with hFn_def
  have h_F_meas : Measurable F := h_H_meas
  have h_Fn_meas : ∀ n, Measurable (Fn n) := h_ev_meas
  have h_F_aestrong : MeasureTheory.AEStronglyMeasurable F μν :=
    h_F_meas.stronglyMeasurable.aestronglyMeasurable
  have h_Fn_aestrong : ∀ n, MeasureTheory.AEStronglyMeasurable (Fn n) μν :=
    fun n => (h_Fn_meas n).stronglyMeasurable.aestronglyMeasurable
  have h_diff_meas : ∀ n, Measurable (F - Fn n) := fun n => h_F_meas.sub (h_Fn_meas n)
  -- Bridge each lintegral_sq form to its eLpNorm² counterpart.
  have h_F_bridge : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm F 2 μν ^ (2 : ℝ) :=
    lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) F h_F_meas
  have h_Fn_bridge : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) (Fn n) (h_Fn_meas n)
  have h_diff_bridge : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_prod_brownian (μ := μ) (T := T)
      (F - Fn n) (h_diff_meas n)
  -- Convert L²-converges (lintegral form) into eLpNorm² → 0.
  have h_eLpNorm_sq_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
        = (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s - ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ) := by
      funext n
      exact (h_diff_bridge n).symm
    rw [h_eq]
    exact h_L2_diff
  -- Square root: eLpNorm² → 0 ⟹ eLpNorm → 0 (via rpow continuity at 0).
  have h_eLpNorm_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν)
      Filter.atTop (nhds 0) := by
    have h_rpow : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν)
        = (fun n => (MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ)) ^ ((1 / 2 : ℝ))) := by
      funext n
      rw [← ENNReal.rpow_mul, show ((2 : ℝ) * (1 / 2)) = 1 from by norm_num,
          ENNReal.rpow_one]
    rw [h_rpow]
    have h := h_eLpNorm_sq_diff_tendsto.ennrpow_const (1 / 2 : ℝ)
    simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  -- Reverse triangle continuity: eLpNorm (Fn n - F) → 0 ⟹ eLpNorm Fn n → eLpNorm F.
  have h_diff_swap : ∀ n,
      MeasureTheory.eLpNorm (Fn n - F) 2 μν
        = MeasureTheory.eLpNorm (F - Fn n) 2 μν := by
    intro n
    have h_neg : Fn n - F = -(F - Fn n) := by ext p; simp [sub_eq_neg_add]
    rw [h_neg, MeasureTheory.eLpNorm_neg]
  have h_eLpNorm_diff_swap_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μν)
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μν)
        = (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν) := funext h_diff_swap
    rw [h_eq]
    exact h_eLpNorm_diff_tendsto
  have h_eLpNorm_Fn_tendsto :=
    eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
      (one_le_two : (1 : ℝ≥0∞) ≤ 2) h_F_aestrong h_Fn_aestrong h_eLpNorm_diff_swap_tendsto
  -- Square back: eLpNorm Fn n → eLpNorm F ⟹ eLpNorm² Fn n → eLpNorm² F.
  have h_eLpNorm_sq_Fn_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ))
      Filter.atTop (nhds (MeasureTheory.eLpNorm F 2 μν ^ (2 : ℝ))) :=
    h_eLpNorm_Fn_tendsto.ennrpow_const 2
  -- Convert back to lintegral form via the bridges.
  have h_eq_func : (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖ev n s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      = (fun n => MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ)) := funext h_Fn_bridge
  rw [h_eq_func, h_F_bridge]
  exact h_eLpNorm_sq_Fn_tendsto

/-- **Bounded dyadic eval lintegral_sq tendsto.** Specialization of
`lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian` to the
`predictableDyadicSimple_brownian` sequence (bounded `g` case). -/
lemma predictableDyadicSimple_brownian_eval_norm_tendsto_bounded
    {P : Measure Ω} [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval s ω‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) :=
  lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian (μ := P) (T := T) g h_meas
    (fun n => (predictableDyadicSimple_brownian hT g h_meas M h_bound n).eval)
    (fun n => predictableDyadicSimple_brownian_eval_jointly_measurable hT g h_meas
      M h_bound n)
    (predictableDyadicSimple_brownian_L2_converges (P := P) hT g h_meas M h_bound)

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Adapted density (Brownian).** Every progressively-measurable
`H ∈ L²(Ω × [0,T], dP ⊗ ds)` is the L²-limit of ADAPTED simple predictable
integrands.

Mirrors `simplePredictable_dense_L2` but produces adapted simples when `H`
is progressively measurable. Uses `predictableDyadicSimple_brownian` (the
left-shifted dyadic average construction) via
`adaptedSimple_dense_L2_bounded_brownian`. -/
lemma adaptedSimple_dense_L2_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
            ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (nhds 0) := by
  -- Truncation preserves measurability + progressive measurability.
  have h_clip_bound : ∀ M : ℕ, ∀ ω s,
      |max (-(M : ℝ)) (min (M : ℝ) (H ω s))| ≤ (M : ℝ) := by
    intro M ω s
    have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have h_clip_meas : ∀ M : ℕ, Measurable
      (Function.uncurry (fun (ω : Ω) (s : ℝ) =>
        max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
    intro M
    have h : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact h.comp h_meas
  -- Progressive measurability preserved under continuous clip.
  have h_clip_progMeas : ∀ M : ℕ, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))) := by
    intro M t
    have h_clip_cont : Continuous (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by
      fun_prop
    exact h_clip_cont.comp_stronglyMeasurable (h_progMeas t)
  -- Apply bounded adapted-density.
  have h_bdd : ∀ M : ℕ, ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n : ℕ, ∀ i : Fin (Hn n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
            ((Hn n).partition i.castSucc)) ((Hn n).ξ i)) ∧
      Filter.Tendsto
        (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s)) - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        Filter.atTop (nhds 0) :=
    fun M => adaptedSimple_dense_L2_bounded_brownian W hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (h_clip_progMeas M) (M : ℝ) (h_clip_bound M)
  choose Hn_seq h_Hn_adapt h_Hn_seq using h_bdd
  -- Same diagonal selection as simplePredictable_dense_L2.
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    exact (ENNReal.tendsto_atTop_zero.mp (h_Hn_seq n)) _ h_eps
  choose N_seq h_N_seq using h_N
  refine ⟨fun n => Hn_seq n (max n (N_seq n)), ?_, ?_⟩
  · -- Adaptedness inherited.
    intro n i
    exact h_Hn_adapt n (max n (N_seq n)) i
  -- Convergence: same proof as simplePredictable_dense_L2.
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
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
      h.comp (Filter.tendsto_add_atTop_nat 1)
    simpa [Nat.cast_add, Nat.cast_one] using hcomp
  obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) (ε / 4) hε4_pos
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn
  have hn₁ : N₁ ≤ n := le_of_max_le_left hn
  have hn₂ : N₂ ≤ n := le_of_max_le_right hn
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
  set A : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s
      - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
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
              ‖H ω s
                - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊)).coe_nnreal_ennreal).pow_const 2
          exact h_meas_A_s.aemeasurable
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
              ‖H q.1 q.2
                - max (-(n : ℝ)) (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal)
                  |>.pow_const 2
          exact (Measurable.lintegral_prod_right'
            (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
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
        exact mul_le_mul_right (add_le_add h_first h_second) _
    _ = ε := by
        rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
        exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)

-- maxHeartbeats: triangle-inequality lift through nested lintegrals + Tonelli.
set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
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
      (Function.uncurry
        (fun (ω : Ω) (s : ℝ) => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
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
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (Hn_seq n k).eval s ω‖₊ : ℝ≥0∞) ^ 2
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
    have hcomp :
        Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
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
    fun ω s => (‖H ω s
      - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  set C : Ω → ℝ → ℝ≥0∞ :=
    fun ω s => (‖H ω s - (Hn_seq n (max n (N_seq n))).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
  have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
  -- Step 1: ∫⁻ s in Icc 0 T, C ω s ∂vol
  --   ≤ 2 * (∫⁻ s, A ω s ∂vol + ∫⁻ s, B ω s ∂vol).
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
              ‖H ω s
                - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊)).coe_nnreal_ennreal).pow_const 2
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
              ‖H q.1 q.2
                - max (-(n : ℝ)) (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal)
                  |>.pow_const 2
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
        exact mul_le_mul_right (add_le_add h_first h_second) _
    _ = ε := by
        rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
        exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)
end LevyStochCalc.Brownian.Ito
