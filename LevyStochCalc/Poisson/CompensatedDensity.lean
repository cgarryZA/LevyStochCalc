/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedMartingale
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Density of adapted simple predictable integrands (compensated Poisson)

Toward the L²-completion of the compensated-Poisson simple integral: adapted
`SimplePredictable` integrands are dense in `L²(P ⊗ ds ⊗ ν)`. The construction
reduces a general predictable square-integrable integrand `φ : Ω → ℝ → E → ℝ` to a
bounded one by truncation (this file's `truncation_L2_converges`), then discretizes
time and the mark space (subsequent steps). Compensated mirror of
`Brownian/ItoDensity.lean`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Pointwise truncation tends to the value.** For the clip
`x ↦ max (-M) (min M x)`, `‖x − clip M x‖² → 0` as `M → ∞` (eventually `clip M x = x`). -/
private lemma truncation_pointwise_tendsto (x : ℝ) :
    Filter.Tendsto
      (fun M : ℕ => (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop ⌈|x|⌉₊] with M hM
  have hMx : |x| ≤ (M : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hM)
  have h_clip : max (-(M : ℝ)) (min (M : ℝ) x) = x := by
    rw [min_eq_right (le_trans (le_abs_self x) hMx)]
    exact max_eq_right (by linarith [neg_abs_le x])
  show (0 : ℝ≥0∞) = (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2
  rw [h_clip, sub_self]; simp

/-- **Pointwise truncation dominated** by the value's square. -/
private lemma truncation_dominated (x : ℝ) (M : ℕ) :
    (‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ : ℝ≥0∞) ^ 2 ≤ (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
  have h_abs : |x - max (-(M : ℝ)) (min (M : ℝ) x)| ≤ |x| := by
    by_cases hx : 0 ≤ x
    · by_cases hxM : x ≤ M
      · rw [min_eq_right hxM, max_eq_right (by linarith)]; simp [abs_nonneg]
      · push Not at hxM
        rw [min_eq_left (le_of_lt hxM), max_eq_right (by linarith : -(M : ℝ) ≤ M)]
        rw [abs_of_nonneg (by linarith : 0 ≤ x - M), abs_of_nonneg hx]; linarith
    · push Not at hx
      by_cases hxM : -(M : ℝ) ≤ x
      · rw [min_eq_right (by linarith : x ≤ M), max_eq_right hxM]; simp
      · push Not at hxM
        rw [min_eq_right (by linarith : x ≤ M), max_eq_left (le_of_lt hxM)]
        rw [show x - -(M : ℝ) = x + M from by ring]
        rw [abs_of_nonpos (by linarith : x + (M : ℝ) ≤ 0), abs_of_neg hx]; linarith
  have h_nn : ‖x - max (-(M : ℝ)) (min (M : ℝ) x)‖₊ ≤ ‖x‖₊ := by
    rw [← NNReal.coe_le_coe]; simp only [coe_nnnorm, Real.norm_eq_abs]; exact h_abs
  exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr h_nn) 2

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: nested triple-lintegral dominated-convergence budget.
/-- **Truncation `L²` convergence (compensated).** For a jointly measurable
square-integrable `φ : Ω → ℝ → E → ℝ`, the clipped integrands `clip M ∘ φ` converge
to `φ` in `L²(P ⊗ ds ⊗ ν)`. Three nested applications of the dominated-convergence
theorem (over `ν`, then `ds`, then `P`), dominated by `‖φ‖²`, tending pointwise to `0`. -/
lemma truncation_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Filter.Tendsto
      (fun M : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - max (-(M : ℝ)) (min (M : ℝ) (φ ω s e))‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  set F : ℕ → Ω → ℝ → E → ℝ≥0∞ := fun M ω s e =>
    (‖φ ω s e - max (-(M : ℝ)) (min (M : ℝ) (φ ω s e))‖₊ : ℝ≥0∞) ^ 2 with hF
  set G : Ω → ℝ → E → ℝ≥0∞ := fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 with hG
  have hFmeas : ∀ M : ℕ, Measurable (fun p : Ω × ℝ × E => F M p.1 p.2.1 p.2.2) := by
    intro M
    have h_clip : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (h_clip.comp h_meas)).nnnorm).pow_const 2
  have hGmeas : Measurable (fun p : Ω × ℝ × E => G p.1 p.2.1 p.2.2) :=
    (ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2
  -- `(ω, s) ↦ ∫⁻_E (·) ∂ν` is measurable for `F M` and `G` (reassociate `Ω×ℝ×E`).
  have hFstepA : ∀ M : ℕ, Measurable (fun q : Ω × ℝ => ∫⁻ e, F M q.1 q.2 e ∂ν) := fun M =>
    ((hFmeas M).comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  have hGstepA : Measurable (fun q : Ω × ℝ => ∫⁻ e, G q.1 q.2 e ∂ν) :=
    (hGmeas.comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, G ω s e ∂ν ∂volume) ?_ ?_ h_sq_int.ne ?_
  · intro M
    exact (hFstepA M).lintegral_prod_right'.aemeasurable
  · intro M
    refine Filter.Eventually.of_forall (fun ω => MeasureTheory.lintegral_mono (fun s => ?_))
    exact MeasureTheory.lintegral_mono (fun e => truncation_dominated _ _)
  · have h_finite_inner : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, G ω s e ∂ν ∂volume < ⊤ :=
      MeasureTheory.ae_lt_top hGstepA.lintegral_prod_right' h_sq_int.ne
    filter_upwards [h_finite_inner] with ω hω_fin
    rw [show (0 : ℝ≥0∞)
        = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => ∫⁻ e, G ω s e ∂ν) ?_ ?_ hω_fin.ne ?_
    · intro M
      exact ((hFmeas M).comp (by fun_prop :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right'.aemeasurable
    · intro M
      exact Filter.Eventually.of_forall
        (fun s => MeasureTheory.lintegral_mono (fun e => truncation_dominated _ _))
    · have h_fin_s : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫⁻ e, G ω s e ∂ν < ⊤ :=
        MeasureTheory.ae_lt_top
          ((hGmeas.comp (by fun_prop :
            Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right')
          hω_fin.ne
      filter_upwards [h_fin_s] with s hs_fin
      rw [show (0 : ℝ≥0∞) = ∫⁻ _ : E, (0 : ℝ≥0∞) ∂ν from by simp]
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun e => G ω s e) ?_ ?_ hs_fin.ne ?_
      · intro M
        exact ((hFmeas M).comp (by fun_prop :
          Measurable fun e : E => ((ω, s, e) : Ω × ℝ × E))).aemeasurable
      · intro M
        exact Filter.Eventually.of_forall (fun e => truncation_dominated _ _)
      · exact Filter.Eventually.of_forall (fun e => truncation_pointwise_tendsto (φ ω s e))

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: nested triple-lintegral dominated-convergence budget.
/-- **Mark-space `L²` reduction (compensated).** For a measurable family of mark sets
`sset` covering `E`, restricting `φ` to the first `N` pieces `Sₙ = ⋃_{m<N} sset m`
converges to `φ` in `L²(P ⊗ ds ⊗ ν)`. The squared error is
`‖φ‖² · 1_{Sₙᶜ}`, which decreases to `0` pointwise (the union exhausts `E`) and is
dominated by `‖φ‖²`; three nested dominated-convergence applications. -/
lemma mark_truncation_L2_converges
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ}
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {sset : ℕ → Set E} (hsset_meas : ∀ n, MeasurableSet (sset n))
    (hcover : ⋃ n, sset n = Set.univ) :
    Filter.Tendsto
      (fun N : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - (⋃ m ∈ Finset.range N, sset m).indicator (fun _ => φ ω s e) e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  set S : ℕ → Set E := fun N => ⋃ m ∈ Finset.range N, sset m with hS
  have hS_meas : ∀ N, MeasurableSet (S N) := fun N =>
    MeasurableSet.biUnion (Set.to_countable _) (fun m _ => hsset_meas m)
  set G : Ω → ℝ → E → ℝ≥0∞ := fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 with hG
  -- The squared error equals `‖φ‖² · 1_{Sₙᶜ}`.
  set F : ℕ → Ω → ℝ → E → ℝ≥0∞ := fun N ω s e =>
    (‖φ ω s e - (S N).indicator (fun _ => φ ω s e) e‖₊ : ℝ≥0∞) ^ 2 with hF
  have hFle : ∀ N ω s e, F N ω s e ≤ G ω s e := by
    intro N ω s e
    by_cases he : e ∈ S N
    · rw [hF, hG]; simp [Set.indicator_of_mem he]
    · rw [hF, hG]; simp [Set.indicator_of_notMem he]
  have hFmeas : ∀ N : ℕ, Measurable (fun p : Ω × ℝ × E => F N p.1 p.2.1 p.2.2) := by
    intro N
    have hind : Measurable (fun p : Ω × ℝ × E =>
        (S N).indicator (fun _ => φ p.1 p.2.1 p.2.2) p.2.2) := by
      have : (fun p : Ω × ℝ × E => (S N).indicator (fun _ => φ p.1 p.2.1 p.2.2) p.2.2)
          = Set.indicator ((fun p : Ω × ℝ × E => p.2.2) ⁻¹' S N)
              (fun p => φ p.1 p.2.1 p.2.2) := by
        funext p
        by_cases he : p.2.2 ∈ S N
        · rw [Set.indicator_of_mem he, Set.indicator_of_mem (by exact he)]
        · rw [Set.indicator_of_notMem he, Set.indicator_of_notMem (by exact he)]
      rw [this]
      exact h_meas.indicator ((measurable_snd.comp measurable_snd) (hS_meas N))
    exact (ENNReal.continuous_coe.measurable.comp (h_meas.sub hind).nnnorm).pow_const 2
  have hGmeas : Measurable (fun p : Ω × ℝ × E => G p.1 p.2.1 p.2.2) :=
    (ENNReal.continuous_coe.measurable.comp h_meas.nnnorm).pow_const 2
  have hGstepA : Measurable (fun q : Ω × ℝ => ∫⁻ e, G q.1 q.2 e ∂ν) :=
    (hGmeas.comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  have hFstepA : ∀ N : ℕ, Measurable (fun q : Ω × ℝ => ∫⁻ e, F N q.1 q.2 e ∂ν) := fun N =>
    ((hFmeas N).comp (by fun_prop :
      Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, G ω s e ∂ν ∂volume) ?_ ?_ h_sq_int.ne ?_
  · intro N; exact (hFstepA N).lintegral_prod_right'.aemeasurable
  · intro N
    refine Filter.Eventually.of_forall (fun ω => MeasureTheory.lintegral_mono (fun s => ?_))
    exact MeasureTheory.lintegral_mono (fun e => hFle N ω s e)
  · have h_finite_inner : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, G ω s e ∂ν ∂volume < ⊤ :=
      MeasureTheory.ae_lt_top hGstepA.lintegral_prod_right' h_sq_int.ne
    filter_upwards [h_finite_inner] with ω hω_fin
    rw [show (0 : ℝ≥0∞)
        = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => ∫⁻ e, G ω s e ∂ν) ?_ ?_ hω_fin.ne ?_
    · intro N
      exact ((hFmeas N).comp (by fun_prop :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right'.aemeasurable
    · intro N
      exact Filter.Eventually.of_forall
        (fun s => MeasureTheory.lintegral_mono (fun e => hFle N ω s e))
    · have h_fin_s : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫⁻ e, G ω s e ∂ν < ⊤ :=
        MeasureTheory.ae_lt_top
          ((hGmeas.comp (by fun_prop :
            Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right')
          hω_fin.ne
      filter_upwards [h_fin_s] with s hs_fin
      rw [show (0 : ℝ≥0∞) = ∫⁻ _ : E, (0 : ℝ≥0∞) ∂ν from by simp]
      refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
        (bound := fun e => G ω s e) ?_ ?_ hs_fin.ne ?_
      · intro N
        exact ((hFmeas N).comp (by fun_prop :
          Measurable fun e : E => ((ω, s, e) : Ω × ℝ × E))).aemeasurable
      · intro N
        exact Filter.Eventually.of_forall (fun e => hFle N ω s e)
      · -- pointwise: eventually `e ∈ Sₙ`, so `F N ω s e = 0`.
        refine Filter.Eventually.of_forall (fun e => ?_)
        obtain ⟨m, hm⟩ : ∃ m, e ∈ sset m := by
          have : e ∈ ⋃ n, sset n := hcover ▸ Set.mem_univ e
          simpa using this
        refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [Filter.eventually_gt_atTop m] with N hN
        have heS : e ∈ S N := by
          rw [hS]; exact Set.mem_biUnion (Finset.mem_range.mpr hN) hm
        show (0 : ℝ≥0∞) = F N ω s e
        simp only [hF, Set.indicator_of_mem heS, sub_self]; simp

/-! ### Dyadic time-discretisation (mark carried as a parameter)

The time direction is discretised by dyadic averaging, mirroring `Brownian/ItoDensity`,
but the integrand carries the mark `e`: the coefficient on the `k`-th dyadic interval is
the *previous*-interval time-average `(2ⁿ/T)∫_{tₖ₋₁}^{tₖ} φ(ω,u,e) du` (shifted left, so
it is `ℱ_{tₖ}`-measurable — adapted), evaluated as a function of `(ω, e)`. -/

/-- Dyadic partition of `[0, T]` at level `n`: `tᵢ = i·T/2ⁿ`. -/
noncomputable def dyadicPartition (T : ℝ) (n : ℕ) : Fin (2 ^ n + 1) → ℝ :=
  fun i => (i : ℝ) * T / (2 ^ n : ℕ)

lemma dyadicPartition_zero (T : ℝ) (n : ℕ) : dyadicPartition T n 0 = 0 := by
  simp [dyadicPartition]

lemma dyadicPartition_last (T : ℝ) (n : ℕ) :
    dyadicPartition T n (Fin.last (2 ^ n)) = T := by
  unfold dyadicPartition; rw [Fin.val_last]; field_simp

lemma dyadicPartition_strictMono {T : ℝ} (hT : 0 < T) (n : ℕ) :
    StrictMono (dyadicPartition T n) := by
  intro i j hij
  unfold dyadicPartition
  have h_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  rw [div_lt_div_iff_of_pos_right h_pos]
  exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) hT

lemma dyadicPartition_le_T {T : ℝ} (_hT : 0 < T) (n : ℕ) :
    dyadicPartition T n (Fin.last (2 ^ n)) ≤ T :=
  le_of_eq (dyadicPartition_last T n)

/-- Dyadic mark-time average: the average of `φ(ω, ·, e)` over the `i`-th dyadic
interval, as a function of `(ω, e)`. -/
noncomputable def dyadicAvg
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) : ℝ :=
  ((2 ^ n : ℕ) / T) *
    ∫ s in Set.Ioc (dyadicPartition T n i.castSucc) (dyadicPartition T n i.succ), φ ω s e

/-- Left-shifted dyadic average (value from the *previous* interval; `0` on the
first), the adapted coefficient of the dyadic approximation. -/
noncomputable def dyadicAvg_shifted
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) : ℝ :=
  if h : i.val = 0 then 0
  else dyadicAvg T φ n ⟨i.val - 1, by omega⟩ ω e

/-- Joint `(ω, e)`-measurability of the dyadic average (Fubini: the Bochner integral
in `s` of a jointly measurable integrand is measurable in the remaining variables). -/
lemma dyadicAvg_measurable
    (T : ℝ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (fun q : Ω × E => dyadicAvg T φ n i q.1 q.2) := by
  unfold dyadicAvg
  refine Measurable.const_mul ?_ _
  have h_reassoc : Measurable
      (fun p : (Ω × E) × ℝ => φ p.1.1 p.2 p.1.2) :=
    h_meas.comp (by fun_prop :
      Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
  exact MeasureTheory.StronglyMeasurable.integral_prod_right'
    (f := fun p : (Ω × E) × ℝ => φ p.1.1 p.2 p.1.2) h_reassoc.stronglyMeasurable |>.measurable

lemma dyadicAvg_shifted_measurable
    (T : ℝ) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (n : ℕ) (i : Fin (2 ^ n)) :
    Measurable (fun q : Ω × E => dyadicAvg_shifted T φ n i q.1 q.2) := by
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]; exact dyadicAvg_measurable T φ h_meas n _

/-- The dyadic average inherits the integrand's uniform bound: `|dyadicAvg| ≤ M`
(the average of values bounded by `M` over an interval of length `T/2ⁿ`). -/
lemma dyadicAvg_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) :
    |dyadicAvg T φ n i ω e| ≤ M := by
  unfold dyadicAvg
  set a := dyadicPartition T n i.castSucc with ha
  set b := dyadicPartition T n i.succ with hb
  have hab : a ≤ b := (dyadicPartition_strictMono hT n).monotone Fin.castSucc_lt_succ.le
  have hlen : b - a = T / (2 ^ n : ℕ) := by
    simp only [ha, hb, dyadicPartition, Fin.val_succ, Fin.val_castSucc]; push_cast; ring
  rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (2 ^ n : ℕ) / T)]
  have hint : |∫ s in Set.Ioc a b, φ ω s e| ≤ M * (b - a) := by
    rw [← Real.norm_eq_abs]
    have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Set.Ioc a b) (f := fun s => φ ω s e) (C := M)
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top)
      (fun x _ => by rw [Real.norm_eq_abs]; exact hM ω x e)
    rw [Real.volume_real_Ioc_of_le hab] at h
    exact h
  calc (2 ^ n : ℕ) / T * |∫ s in Set.Ioc a b, φ ω s e|
      ≤ (2 ^ n : ℕ) / T * (M * (b - a)) := mul_le_mul_of_nonneg_left hint (by positivity)
    _ = M := by
        rw [hlen]
        have h2 : ((2 : ℝ) ^ n) ≠ 0 := by positivity
        have hT' : T ≠ 0 := hT.ne'
        push_cast; field_simp

/-- The left-shifted dyadic average is bounded by `max M 0` (covering the `i = 0`
case, which is the constant `0`). -/
lemma dyadicAvg_shifted_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) :
    |dyadicAvg_shifted T φ n i ω e| ≤ max M 0 := by
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte, abs_zero]; exact le_max_right _ _
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_bounded hT φ hM n _ ω e).trans (le_max_left _ _)

/-- The dyadic interval length is `T/2ⁿ`. -/
lemma dyadicPartition_diff {T : ℝ} (n : ℕ) (i : Fin (2 ^ n)) :
    dyadicPartition T n i.succ - dyadicPartition T n i.castSucc = T / (2 ^ n : ℕ) := by
  unfold dyadicPartition
  have hi_succ : ((i.succ : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) + 1 := by simp [Fin.val_succ]
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by simp [Fin.val_castSucc]
  rw [hi_succ, hi_castSucc]; ring

/-- **Dyadic index:** for `s ∈ (0, T]`, the index `i ∈ Fin (2ⁿ)` with
`s ∈ (i·T/2ⁿ, (i+1)·T/2ⁿ]`, via the ceiling function. (Deterministic — no `Ω`/`E`.) -/
noncomputable def dyadicIndex (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ)
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

/-- **Dyadic index membership:** `s ∈ (tᵢ, tᵢ₊₁]` with `tᵢ = i·T/2ⁿ`. -/
lemma dyadicIndex_mem (n : ℕ) (T : ℝ) (hT : 0 < T) (s : ℝ) (hs : 0 < s ∧ s ≤ T) :
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
    rw [lt_div_iff₀ hT] at hk_lt; linarith
  · rw [show ((((k : ℕ) - 1 : ℕ) : ℝ) + 1) = (k : ℝ) by rw [h_sub]; ring]
    rw [le_div_iff₀ h_pow]
    rw [div_le_iff₀ hT] at hk_ge; linarith

/-- `closedBall ((a+b)/2) ((b-a)/2) = Icc a b`. -/
private lemma closedBall_eq_Icc (a b : ℝ) :
    Metric.closedBall ((a + b) / 2) ((b - a) / 2) = Set.Icc a b := by
  ext x
  simp only [Metric.mem_closedBall, Real.dist_eq, Set.mem_Icc]
  constructor
  · intro h
    have := abs_le.mp (show |x - (a + b) / 2| ≤ (b - a) / 2 from h)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro ⟨h1, h2⟩; rw [abs_le]; exact ⟨by linarith, by linarith⟩

/-- **Closed-ball ↔ dyadic-interval bridge:** the dyadic average equals the
Mathlib closed-ball set-average of `φ(ω, ·, e)`, connecting to the Lebesgue
differentiation theorem (`IsUnifLocDoublingMeasure.ae_tendsto_average`). -/
lemma dyadicAvg_eq_average_closedBall
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) (e : E) :
    dyadicAvg T φ n i ω e =
      ⨍ y in Metric.closedBall
        ((dyadicPartition T n i.castSucc + dyadicPartition T n i.succ) / 2)
        ((dyadicPartition T n i.succ - dyadicPartition T n i.castSucc) / 2),
        φ ω y e ∂volume := by
  set t_i := dyadicPartition T n i.castSucc with ht_i
  set t_succ := dyadicPartition T n i.succ with ht_succ
  have h_lt : t_i < t_succ := dyadicPartition_strictMono hT n Fin.castSucc_lt_succ
  have h_diff : t_succ - t_i = T / (2 ^ n : ℕ) := dyadicPartition_diff n i
  have h_pow_pos : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
  rw [closedBall_eq_Icc t_i t_succ,
    show (volume.restrict (Set.Icc t_i t_succ) : Measure ℝ)
        = volume.restrict (Set.Ioc t_i t_succ)
      from MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioc_ae_eq_Icc.symm,
    MeasureTheory.average_eq]
  unfold dyadicAvg
  rw [show ((volume.restrict (Set.Ioc t_i t_succ) : Measure ℝ).real Set.univ) = t_succ - t_i from by
        unfold MeasureTheory.Measure.real
        rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
          Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)],
    h_diff]
  have h_T_ne : T ≠ 0 := ne_of_gt hT
  have h_pow_ne : ((2 ^ n : ℕ) : ℝ) ≠ 0 := ne_of_gt h_pow_pos
  rw [smul_eq_mul]; field_simp; ring

/-- A bounded measurable real function is locally integrable. -/
private lemma bounded_locallyIntegrable (g : ℝ → ℝ) (h_meas : Measurable g)
    (M : ℝ) (h_bound : ∀ s, |g s| ≤ M) : MeasureTheory.LocallyIntegrable g volume := by
  intro x
  refine ⟨Set.Ioo (x - 1) (x + 1), isOpen_Ioo.mem_nhds (by simp), ?_⟩
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  refine MeasureTheory.HasFiniteIntegral.restrict_of_bounded_enorm
    (C := ENNReal.ofReal M) ?_ ?_ ?_
  · simp
  · rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
  · refine Filter.Eventually.of_forall (fun s => ?_)
    rw [show ‖g s‖ₑ = ENNReal.ofReal ‖g s‖ from (ofReal_norm_eq_enorm _).symm]
    exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact h_bound s)

/-- The (unshifted) dyadic eval at running time `s`, carrying the mark `e`: the
dyadic average of `φ(ω, ·, e)` over the interval containing `s` (0 outside `(0,T]`). -/
noncomputable def dyadicEval
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) : ℝ :=
  ∑ i : Fin (2 ^ n),
    if dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
    then dyadicAvg T φ n i ω e else 0

/-- For `s ∈ (0, T]`, `dyadicEval` collapses to the dyadic average at the index of `s`. -/
lemma dyadicEval_eq_dyadicAvg_at_index
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T)
    (ω : Ω) (e : E) :
    dyadicEval T φ n s ω e = dyadicAvg T φ n (dyadicIndex n T hT s hs) ω e := by
  set i := dyadicIndex n T hT s hs with hi
  have hi_mem := dyadicIndex_mem n T hT s hs
  have h_pcast : dyadicPartition T n i.castSucc = ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_castSucc]
  have h_psucc : dyadicPartition T n i.succ = (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_succ]; push_cast; ring
  have h_i_fires : dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ := by
    rw [h_pcast, h_psucc]; exact hi_mem
  unfold dyadicEval
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
  · intro j _ hji
    refine if_neg (fun ⟨hj1, hj2⟩ => ?_)
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      linarith [h_i_fires.2]
    · exact hji heq.symm
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
      linarith [h_i_fires.1]
  · intro h_not; exact absurd (Finset.mem_univ i) h_not

/-- **Per-`(ω,e)` a.e. time convergence (Lebesgue differentiation).** For a bounded
jointly measurable `φ`, for each fixed `(ω, e)`, the dyadic eval converges to
`φ(ω, s, e)` for a.e. `s ∈ [0, T]`. Applies Mathlib's
`IsUnifLocDoublingMeasure.ae_tendsto_average` to `s ↦ φ ω s e`, bridged to the dyadic
averages via `dyadicAvg_eq_average_closedBall` + `dyadicEval_eq_dyadicAvg_at_index`. -/
lemma dyadicEval_ae_tendsto_per_param
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => dyadicEval T φ n s ω e) Filter.atTop (nhds (φ ω s e)) := by
  have h_meas_slice : Measurable (fun s : ℝ => φ ω s e) :=
    h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have h_loc : MeasureTheory.LocallyIntegrable (fun s : ℝ => φ ω s e) volume :=
    bounded_locallyIntegrable _ h_meas_slice M (fun s => hM ω s e)
  have h_leb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) h_loc 1
  have h_leb_r : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (1 * δ j)) →
        Filter.Tendsto (fun j => ⨍ y in Metric.closedBall (w j) (δ j), φ ω y e ∂volume)
          l (nhds (φ ω x e)) :=
    MeasureTheory.ae_restrict_of_ae h_leb
  have h_pos_ae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)), x ≠ 0 := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬ x ≠ 0} = {0} := by ext x; simp
    rw [this, Real.volume_singleton]
  filter_upwards [h_leb_r, h_pos_ae, MeasureTheory.ae_restrict_mem measurableSet_Icc]
    with x h_leb_x hx_ne hx_mem
  have hx : 0 < x ∧ x ≤ T := ⟨lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne), hx_mem.2⟩
  -- per-level dyadic interval endpoints of `x`.
  have hmem : ∀ n, dyadicPartition T n (dyadicIndex n T hT x hx).castSucc < x ∧
      x ≤ dyadicPartition T n (dyadicIndex n T hT x hx).succ := by
    intro n
    have h := dyadicIndex_mem n T hT x hx
    have hpc : dyadicPartition T n (dyadicIndex n T hT x hx).castSucc
        = ((dyadicIndex n T hT x hx : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
      unfold dyadicPartition; rw [Fin.val_castSucc]
    have hps : dyadicPartition T n (dyadicIndex n T hT x hx).succ
        = (((dyadicIndex n T hT x hx : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
      unfold dyadicPartition; rw [Fin.val_succ]; push_cast; ring
    rw [hpc, hps]; exact h
  set w : ℕ → ℝ := fun n =>
    (dyadicPartition T n (dyadicIndex n T hT x hx).castSucc +
      dyadicPartition T n (dyadicIndex n T hT x hx).succ) / 2 with hw
  set δ : ℕ → ℝ := fun n =>
    (dyadicPartition T n (dyadicIndex n T hT x hx).succ -
      dyadicPartition T n (dyadicIndex n T hT x hx).castSucc) / 2 with hδ
  have hδ_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n
    show (dyadicPartition T n (dyadicIndex n T hT x hx).succ -
      dyadicPartition T n (dyadicIndex n T hT x hx).castSucc) / 2 = _
    rw [dyadicPartition_diff]; ring
  have hδ_pos : ∀ n, 0 < δ n := fun n => by rw [hδ_eq]; positivity
  have hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_iff.mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
      exact this.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr (fun n => by ring)
    exact (Filter.Tendsto.div_atTop tendsto_const_nhds h2pow).congr (fun n => (hδ_eq n).symm)
  have hδ_nhds : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ0, Filter.Eventually.of_forall hδ_pos⟩
  have hxball : ∀ n, x ∈ Metric.closedBall (w n) (1 * δ n) := by
    intro n
    rw [one_mul, Metric.mem_closedBall, Real.dist_eq]
    obtain ⟨h1, h2⟩ := hmem n
    rw [hw, hδ, abs_le]; constructor <;> simp only <;> linarith
  have h_avg := h_leb_x w δ hδ_nhds (Filter.Eventually.of_forall hxball)
  have h_bridge : ∀ n, dyadicEval T φ n x ω e
      = ⨍ y in Metric.closedBall (w n) (δ n), φ ω y e ∂volume := by
    intro n
    rw [dyadicEval_eq_dyadicAvg_at_index hT φ n x hx ω e,
      dyadicAvg_eq_average_closedBall hT φ n (dyadicIndex n T hT x hx) ω e]
  simp_rw [h_bridge]; exact h_avg

/-- `dyadicEval` inherits the bound `M`: at most one partition indicator fires, and each
dyadic average is bounded by `M`. -/
lemma dyadicEval_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) :
    |dyadicEval T φ n s ω e| ≤ M := by
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM ω 0 e)
  unfold dyadicEval
  by_cases h : ∃ i : Fin (2 ^ n),
      dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
  · obtain ⟨i₀, hi₀⟩ := h
    have huniq : ∀ j : Fin (2 ^ n), j ≠ i₀ →
        ¬(dyadicPartition T n j.castSucc < s ∧ s ≤ dyadicPartition T n j.succ) := by
      intro j hj ⟨hj1, hj2⟩
      rcases lt_trichotomy i₀ j with hlt | heq | hgt
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hi₀.2]
      · exact hj heq.symm
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.1]
    rw [Finset.sum_eq_single i₀ (fun j _ hj => if_neg (huniq j hj))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hi₀]
    exact dyadicAvg_bounded hT φ hM n i₀ ω e
  · rw [not_exists] at h
    rw [Finset.sum_eq_zero (fun i _ => if_neg (h i)), abs_zero]; exact hM_nn

/-- `s ↦ dyadicEval T φ n s ω e` is measurable (finite sum of interval-indicators
times constants). -/
lemma dyadicEval_measurable_in_time {T : ℝ} (φ : Ω → ℝ → E → ℝ) (n : ℕ) (ω : Ω) (e : E) :
    Measurable (fun s => dyadicEval T φ n s ω e) := by
  unfold dyadicEval
  exact Finset.measurable_sum _ (fun i _ =>
    Measurable.ite measurableSet_Ioc measurable_const measurable_const)

/-- **Per-`(ω,e)` `L²` time convergence:** for fixed `(ω, e)`, the time-`L²` error of
the dyadic eval tends to `0`. Dominated convergence on the finite interval `[0,T]`
(bound `(2M)²`, a.e. pointwise convergence from `dyadicEval_ae_tendsto_per_param`). -/
lemma dyadicEval_inner_L2_tendsto
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    Filter.Tendsto
      (fun n => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
  have hM_nn : 0 ≤ M := le_trans (abs_nonneg _) (hM ω 0 e)
  have h_meas_slice : Measurable (fun s : ℝ => φ ω s e) :=
    h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have hsq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm_eq_enorm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => ENNReal.ofReal ((2 * M) ^ 2)) ?_ ?_ ?_ ?_
  · intro n
    exact ((ENNReal.continuous_coe.measurable.comp
      (h_meas_slice.sub (dyadicEval_measurable_in_time φ n ω e)).nnnorm).pow_const 2).aemeasurable
  · intro n
    refine Filter.Eventually.of_forall (fun s => ?_)
    simp only []
    rw [hsq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ‖φ ω s e - dyadicEval T φ n s ω e‖ ≤ 2 * M := by
      rw [Real.norm_eq_abs]
      calc |φ ω s e - dyadicEval T φ n s ω e|
          ≤ |φ ω s e| + |dyadicEval T φ n s ω e| := abs_sub _ _
        _ ≤ M + M := add_le_add (hM ω s e) (dyadicEval_bounded hT φ hM n s ω e)
        _ = 2 * M := by ring
    nlinarith [norm_nonneg (φ ω s e - dyadicEval T φ n s ω e), hb, hM_nn]
  · rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  · filter_upwards [dyadicEval_ae_tendsto_per_param hT φ h_meas hM ω e] with s hs
    have hdiff : Filter.Tendsto (fun n => φ ω s e - dyadicEval T φ n s ω e)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := φ ω s e)).sub hs
    have hg : Continuous (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)
    simpa using (hg.tendsto 0).comp hdiff

/-- If `φ(ω, ·, e)` vanishes identically in time, so does its dyadic eval. -/
lemma dyadicEval_eq_zero {T : ℝ} (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E)
    (h0 : ∀ u, φ ω u e = 0) : dyadicEval T φ n s ω e = 0 := by
  unfold dyadicEval
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have havg : dyadicAvg T φ n i ω e = 0 := by unfold dyadicAvg; simp [h0]
  split_ifs with h
  · exact havg
  · rfl

/-- Joint `(s, e)`-measurability of `dyadicEval` (with `ω` fixed). -/
lemma dyadicEval_measurable_prod
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) (ω : Ω) :
    Measurable (fun q : ℝ × E => dyadicEval T φ n q.1 ω q.2) := by
  unfold dyadicEval
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite (measurable_fst measurableSet_Ioc) ?_ measurable_const
  exact (dyadicAvg_measurable T φ h_meas n i).comp
    (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.2) : Ω × E))

/-- Joint `(ω, s, e)`-measurability of `dyadicEval`. -/
lemma dyadicEval_measurable_triple
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (fun p : Ω × ℝ × E => dyadicEval T φ n p.2.1 p.1 p.2.2) := by
  unfold dyadicEval
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ((measurable_fst.comp measurable_snd) measurableSet_Ioc) ?_
    measurable_const
  exact (dyadicAvg_measurable T φ h_meas n i).comp
    (by fun_prop : Measurable fun p : Ω × ℝ × E => ((p.1, p.2.2) : Ω × E))

set_option maxHeartbeats 1000000 in
/-- **`L²` convergence of the dyadic eval (finite-mark-support).** For a bounded
jointly-measurable `φ` vanishing off a finite-`ν`-mass mark set `S`, the (unshifted)
dyadic eval converges to `φ` in `L²(P ⊗ ds ⊗ ν)`. Tonelli swap `s ↔ e`, then nested
dominated convergence over `P` then `ν` (the per-`(ω,e)` time-`L²` errors tend to `0`
for *every* `(ω,e)`; the bound `(2·max M 0)²·T·𝟙_S` is `P⊗ν`-integrable since
`ν(S) < ⊤`). -/
lemma dyadicEval_L2_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ) (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS_meas : MeasurableSet S) (hS_fin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  set M' : ℝ := max M 0 with hM'def
  have hM'_nn : 0 ≤ M' := le_max_right _ _
  have hφM' : ∀ ω s e, |φ ω s e| ≤ M' := fun ω s e => (hM ω s e).trans (le_max_left _ _)
  set cT : ℝ≥0∞ := ENNReal.ofReal ((2 * M') ^ 2 * T) with hcT
  -- joint measurability of the squared-error integrand in (ω,s,e).
  have hFmeas : ∀ n : ℕ, Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - dyadicEval T φ n p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) := fun n =>
    (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (dyadicEval_measurable_triple φ h_meas n)).nnnorm).pow_const 2
  -- the inner time-integral `h n ω e := ∫⁻_s ‖φ−dyadicEval‖²`.
  have hF_se : ∀ n ω, Measurable (fun q : ℝ × E =>
      (‖φ ω q.1 q.2 - dyadicEval T φ n q.1 ω q.2‖₊ : ℝ≥0∞) ^ 2) := fun n ω =>
    (ENNReal.continuous_coe.measurable.comp
      ((h_meas.comp (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).sub
        ((dyadicEval_measurable_prod φ h_meas n ω))).nnnorm).pow_const 2
  -- swap `s` and `e` in the inner double integral.
  have hswap : ∀ n ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = ∫⁻ e, (∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂ν := by
    intro n ω
    exact MeasureTheory.lintegral_lintegral_swap (hF_se n ω).aemeasurable
  -- per-(ω,e) inner bound: `∫⁻_s ‖φ−dyadicEval‖² ≤ 𝟙_S · cT`.
  have h_inner_le : ∀ n ω e,
      (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        ≤ S.indicator (fun _ => cT) e := by
    intro n ω e
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he]
      calc (∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((2 * M') ^ 2) ∂volume := by
            refine MeasureTheory.lintegral_mono (fun s => ?_)
            rw [show (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2
                  = ENNReal.ofReal (‖φ ω s e - dyadicEval T φ n s ω e‖ ^ 2) from by
                rw [show (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞)
                      = ENNReal.ofReal ‖φ ω s e - dyadicEval T φ n s ω e‖ from
                    (ofReal_norm_eq_enorm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]]
            refine ENNReal.ofReal_le_ofReal ?_
            have hb : ‖φ ω s e - dyadicEval T φ n s ω e‖ ≤ 2 * M' := by
              rw [Real.norm_eq_abs]
              calc |φ ω s e - dyadicEval T φ n s ω e|
                  ≤ |φ ω s e| + |dyadicEval T φ n s ω e| := abs_sub _ _
                _ ≤ M' + M' := add_le_add (hφM' ω s e)
                    ((dyadicEval_bounded hT φ hM n s ω e).trans (le_max_left _ _))
                _ = 2 * M' := by ring
            nlinarith [norm_nonneg (φ ω s e - dyadicEval T φ n s ω e), hb, hM'_nn]
        _ = cT := by
            rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, hcT,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; rw [sub_zero]
    · have hzero : ∀ s, φ ω s e - dyadicEval T φ n s ω e = 0 := by
        intro s
        rw [hSupp ω e he s, dyadicEval_eq_zero φ n s ω e (hSupp ω e he), sub_zero]
      rw [Set.indicator_of_notMem he]
      simp only [hzero, nnnorm_zero, ENNReal.coe_zero]
      simp
  -- assemble: outer DCT over P, inner DCT over ν.
  simp_rw [hswap]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => cT * ν S) ?_ ?_ (by
      rw [MeasureTheory.lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin)
        (MeasureTheory.measure_ne_top _ _)) ?_
  · intro n
    refine Measurable.aemeasurable ?_
    have : Measurable (fun q : Ω × E => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ q.1 s q.2 - dyadicEval T φ n s q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
      have hr : Measurable (fun p : (Ω × E) × ℝ =>
          (‖φ p.1.1 p.2 p.1.2 - dyadicEval T φ n p.2 p.1.1 p.1.2‖₊ : ℝ≥0∞) ^ 2) :=
        (hFmeas n).comp (by fun_prop :
          Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
      exact hr.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
    exact this.lintegral_prod_right' (ν := ν)
  · intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    calc (∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖φ ω s e - dyadicEval T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν)
        ≤ ∫⁻ e, S.indicator (fun _ => cT) e ∂ν :=
          MeasureTheory.lintegral_mono (fun e => h_inner_le n ω e)
      _ = cT * ν S := by
          rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ : E, (0 : ℝ≥0∞) ∂ν from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun e => S.indicator (fun _ => cT) e) ?_ ?_ (by
        rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin) ?_
    · intro n
      have hes : Measurable (fun q : E × ℝ =>
          (‖φ ω q.2 q.1 - dyadicEval T φ n q.2 ω q.1‖₊ : ℝ≥0∞) ^ 2) := by
        refine (ENNReal.continuous_coe.measurable.comp (Measurable.sub ?_ ?_).nnnorm).pow_const 2
        · exact h_meas.comp (by fun_prop : Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))
        · exact (dyadicEval_measurable_prod φ h_meas n ω).comp measurable_swap
      exact (hes.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))).aemeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun e => h_inner_le n ω e)
    · exact Filter.Eventually.of_forall (fun e => dyadicEval_inner_L2_tendsto hT φ h_meas hM ω e)

/-! ### Adapted (left-shifted) eval

The coefficient on the `i`-th dyadic interval is the average over the *previous*
interval (`dyadicAvg_shifted`), making it `ℱ_{tᵢ}`-measurable for progressively
measurable `φ` — the predictable/adapted version of `dyadicEval`. -/

/-- The left-shifted dyadic eval (adapted coefficients). -/
noncomputable def dyadicEvalShifted
    (T : ℝ) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) : ℝ :=
  ∑ i : Fin (2 ^ n),
    if dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
    then dyadicAvg_shifted T φ n i ω e else 0

/-- For `s ∈ (0, T]`, the shifted eval collapses to the shifted average at the index of `s`. -/
lemma dyadicEvalShifted_eq_at_index
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (hs : 0 < s ∧ s ≤ T)
    (ω : Ω) (e : E) :
    dyadicEvalShifted T φ n s ω e = dyadicAvg_shifted T φ n (dyadicIndex n T hT s hs) ω e := by
  set i := dyadicIndex n T hT s hs with hi
  have hi_mem := dyadicIndex_mem n T hT s hs
  have h_pcast : dyadicPartition T n i.castSucc = ((i : ℕ) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_castSucc]
  have h_psucc : dyadicPartition T n i.succ = (((i : ℕ) + 1) : ℝ) * T / (2 ^ n : ℕ) := by
    unfold dyadicPartition; rw [Fin.val_succ]; push_cast; ring
  have h_i_fires : dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ := by
    rw [h_pcast, h_psucc]; exact hi_mem
  unfold dyadicEvalShifted
  rw [Finset.sum_eq_single i]
  · rw [if_pos h_i_fires]
  · intro j _ hji
    refine if_neg (fun ⟨hj1, hj2⟩ => ?_)
    rcases lt_trichotomy i j with hlt | heq | hgt
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
      linarith [h_i_fires.2]
    · exact hji heq.symm
    · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
      linarith [h_i_fires.1]
  · intro h_not; exact absurd (Finset.mem_univ i) h_not

/-- The shifted eval is bounded by `max M 0` (at most one indicator fires; each shifted
average is bounded by `max M 0`). -/
lemma dyadicEvalShifted_bounded {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (n : ℕ) (s : ℝ) (ω : Ω) (e : E) :
    |dyadicEvalShifted T φ n s ω e| ≤ max M 0 := by
  unfold dyadicEvalShifted
  by_cases h : ∃ i : Fin (2 ^ n),
      dyadicPartition T n i.castSucc < s ∧ s ≤ dyadicPartition T n i.succ
  · obtain ⟨i₀, hi₀⟩ := h
    have huniq : ∀ j : Fin (2 ^ n), j ≠ i₀ →
        ¬(dyadicPartition T n j.castSucc < s ∧ s ≤ dyadicPartition T n j.succ) := by
      intro j hj ⟨hj1, hj2⟩
      rcases lt_trichotomy i₀ j with hlt | heq | hgt
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hlt)
        linarith [hi₀.2]
      · exact hj heq.symm
      · have := (dyadicPartition_strictMono hT n).monotone (Fin.succ_le_castSucc_iff.mpr hgt)
        linarith [hi₀.1]
    rw [Finset.sum_eq_single i₀ (fun j _ hj => if_neg (huniq j hj))
        (fun h => absurd (Finset.mem_univ _) h), if_pos hi₀]
    exact dyadicAvg_shifted_bounded hT φ hM n i₀ ω e
  · rw [not_exists] at h
    rw [Finset.sum_eq_zero (fun i _ => if_neg (h i)), abs_zero]; exact le_max_right _ _

/-- Joint `(ω, s, e)`-measurability of the shifted eval. -/
lemma dyadicEvalShifted_measurable_triple
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) :
    Measurable (fun p : Ω × ℝ × E => dyadicEvalShifted T φ n p.2.1 p.1 p.2.2) := by
  unfold dyadicEvalShifted
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite ((measurable_fst.comp measurable_snd) measurableSet_Ioc) ?_
    measurable_const
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_measurable T φ h_meas n _).comp
      (by fun_prop : Measurable fun p : Ω × ℝ × E => ((p.1, p.2.2) : Ω × E))

/-- `dyadicPartition` depends only on the index's value. -/
lemma dyadicPartition_val_congr {T : ℝ} {n : ℕ} {k k' : Fin (2 ^ n + 1)}
    (h : (k : ℕ) = (k' : ℕ)) : dyadicPartition T n k = dyadicPartition T n k' := by
  unfold dyadicPartition
  rw [show (k : ℝ) = (k' : ℝ) from by exact_mod_cast h]

/-- **Per-`(ω,e)` a.e. convergence of the shifted eval.** For fixed `(ω, e)`, the
left-shifted dyadic eval converges to `φ(ω, s, e)` for a.e. `s ∈ [0,T]`: Lebesgue
differentiation (`K = 3`) on the *previous* dyadic interval; the centre/half are read
off the previous-interval index `⟨iₙ−1, _⟩`, so the closed-ball bridge is definitional.
The first interval (`iₙ = 0`, shift `= 0`) is escaped for all large `n`. -/
lemma dyadicEvalShifted_ae_tendsto_per_param
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun n => dyadicEvalShifted T φ n s ω e) Filter.atTop (nhds (φ ω s e)) := by
  have h_meas_slice : Measurable (fun s : ℝ => φ ω s e) :=
    h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have h_loc : MeasureTheory.LocallyIntegrable (fun s : ℝ => φ ω s e) volume :=
    bounded_locallyIntegrable _ h_meas_slice M (fun s => hM ω s e)
  have h_leb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) h_loc 3
  have h_leb_r : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ {ι : Type} {l : Filter ι} (w : ι → ℝ) (δ : ι → ℝ),
        Filter.Tendsto δ l (nhdsWithin 0 (Set.Ioi 0)) →
        (∀ᶠ j in l, x ∈ Metric.closedBall (w j) (3 * δ j)) →
        Filter.Tendsto (fun j => ⨍ y in Metric.closedBall (w j) (δ j), φ ω y e ∂volume)
          l (nhds (φ ω x e)) :=
    MeasureTheory.ae_restrict_of_ae h_leb
  have h_pos_ae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) T)), x ≠ 0 := by
    refine MeasureTheory.ae_restrict_of_ae ?_
    rw [MeasureTheory.ae_iff]
    have : {x : ℝ | ¬ x ≠ 0} = {0} := by ext x; simp
    rw [this, Real.volume_singleton]
  filter_upwards [h_leb_r, h_pos_ae, MeasureTheory.ae_restrict_mem measurableSet_Icc]
    with x h_leb_x hx_ne hx_mem
  have hx : 0 < x ∧ x ≤ T := ⟨lt_of_le_of_ne hx_mem.1 (Ne.symm hx_ne), hx_mem.2⟩
  have hjlt : ∀ n, (dyadicIndex n T hT x hx).val - 1 < 2 ^ n := fun n => by
    have := (dyadicIndex n T hT x hx).isLt; omega
  set jp : (n : ℕ) → Fin (2 ^ n) :=
    fun n => ⟨(dyadicIndex n T hT x hx).val - 1, hjlt n⟩ with hjp
  set w : ℕ → ℝ := fun n =>
    (dyadicPartition T n (jp n).castSucc + dyadicPartition T n (jp n).succ) / 2 with hw
  set δ : ℕ → ℝ := fun n =>
    (dyadicPartition T n (jp n).succ - dyadicPartition T n (jp n).castSucc) / 2 with hδ
  have hδ_eq : ∀ n, δ n = T / (2 * (2 ^ n : ℕ)) := by
    intro n; rw [hδ]
    show (dyadicPartition T n (jp n).succ - dyadicPartition T n (jp n).castSucc) / 2 = _
    rw [dyadicPartition_diff]; ring
  have hδ_pos : ∀ n, 0 < δ n := fun n => by rw [hδ_eq]; positivity
  have hδ0 : Filter.Tendsto δ Filter.atTop (nhds 0) := by
    have h2pow : Filter.Tendsto (fun n : ℕ => 2 * ((2 ^ n : ℕ) : ℝ))
        Filter.atTop Filter.atTop := by
      have : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
        tendsto_natCast_atTop_iff.mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
      exact this.atTop_mul_const' (by norm_num : (0 : ℝ) < 2) |>.congr (fun n => by ring)
    exact (Filter.Tendsto.div_atTop tendsto_const_nhds h2pow).congr (fun n => (hδ_eq n).symm)
  have hδ_nhds : Filter.Tendsto δ Filter.atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hδ0, Filter.Eventually.of_forall hδ_pos⟩
  -- eventually the index is ≥ 1.
  have hev1 : ∀ᶠ n in Filter.atTop, 1 ≤ (dyadicIndex n T hT x hx).val := by
    have hpow : Filter.Tendsto (fun n : ℕ => ((2 ^ n : ℕ) : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_iff.mpr (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : 1 < 2))
    filter_upwards [hpow.eventually_gt_atTop (T / x)] with n hn
    have h1 : (1 : ℝ) < x * (2 ^ n : ℕ) / T := by
      rw [lt_div_iff₀ hT, one_mul]
      have h2 : T < (2 ^ n : ℕ) * x := (div_lt_iff₀ hx.1).mp hn
      linarith [h2]
    have hc : 1 < ⌈x * (2 ^ n : ℕ) / T⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast h1)
    simp only [dyadicIndex]; omega
  -- x is within 3δ of the previous interval's centre, in symbolic `a, b` form.
  have hxball : ∀ᶠ n in Filter.atTop, x ∈ Metric.closedBall (w n) (3 * δ n) := by
    filter_upwards [hev1] with n hn1
    set a := dyadicPartition T n (jp n).castSucc with ha
    set b := dyadicPartition T n (jp n).succ with hb
    have hval : ((dyadicIndex n T hT x hx).castSucc : ℕ) = ((jp n).succ : ℕ) := by
      simp only [hjp, Fin.val_castSucc, Fin.val_succ]; omega
    have hib : dyadicPartition T n (dyadicIndex n T hT x hx).castSucc = b := by
      rw [hb]; exact dyadicPartition_val_congr hval
    have hba : a ≤ b := (dyadicPartition_strictMono hT n).monotone Fin.castSucc_lt_succ.le
    have hdiff_j : b - a = T / (2 ^ n : ℕ) := dyadicPartition_diff n (jp n)
    have hdiff_i : dyadicPartition T n (dyadicIndex n T hT x hx).succ
        - dyadicPartition T n (dyadicIndex n T hT x hx).castSucc = T / (2 ^ n : ℕ) :=
      dyadicPartition_diff n (dyadicIndex n T hT x hx)
    have hlo : b < x := by
      rw [← hib]; unfold dyadicPartition; rw [Fin.val_castSucc]
      exact (dyadicIndex_mem n T hT x hx).1
    have hx_hi_part : x ≤ dyadicPartition T n (dyadicIndex n T hT x hx).succ := by
      have h2 := (dyadicIndex_mem n T hT x hx).2
      unfold dyadicPartition; rw [Fin.val_succ]; push_cast at h2 ⊢; linarith [h2]
    rw [hib] at hdiff_i
    rw [Metric.mem_closedBall, Real.dist_eq]
    show |x - (a + b) / 2| ≤ 3 * ((b - a) / 2)
    rw [abs_le]
    constructor <;> linarith [hlo, hx_hi_part, hdiff_i, hdiff_j, hba]
  -- bridge: shifted eval = closed-ball average centred at `wₙ` (definitional).
  have hbridge : ∀ᶠ n in Filter.atTop,
      dyadicEvalShifted T φ n x ω e = ⨍ y in Metric.closedBall (w n) (δ n), φ ω y e ∂volume := by
    filter_upwards [hev1] with n hn1
    have hival : (dyadicIndex n T hT x hx).val ≠ 0 := by omega
    rw [dyadicEvalShifted_eq_at_index hT φ n x hx ω e, dyadicAvg_shifted, dif_neg hival]
    show dyadicAvg T φ n (jp n) ω e = _
    rw [dyadicAvg_eq_average_closedBall hT φ n (jp n) ω e]
  exact Filter.Tendsto.congr' (hbridge.mono (fun n h => h.symm)) (h_leb_x w δ hδ_nhds hxball)

/-- If `φ(ω, ·, e)` vanishes identically in time, so does its shifted dyadic eval. -/
lemma dyadicEvalShifted_eq_zero {T : ℝ} (φ : Ω → ℝ → E → ℝ) (n : ℕ) (s : ℝ) (ω : Ω) (e : E)
    (h0 : ∀ u, φ ω u e = 0) : dyadicEvalShifted T φ n s ω e = 0 := by
  unfold dyadicEvalShifted
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have havg : dyadicAvg_shifted T φ n i ω e = 0 := by
    unfold dyadicAvg_shifted
    split_ifs with h
    · rfl
    · unfold dyadicAvg; simp [h0]
  split_ifs with h
  · exact havg
  · rfl

/-- Joint `(s, e)`-measurability of the shifted eval (with `ω` fixed). -/
lemma dyadicEvalShifted_measurable_prod
    {T : ℝ} (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)) (n : ℕ) (ω : Ω) :
    Measurable (fun q : ℝ × E => dyadicEvalShifted T φ n q.1 ω q.2) := by
  unfold dyadicEvalShifted
  refine Finset.measurable_sum _ (fun i _ => ?_)
  refine Measurable.ite (measurable_fst measurableSet_Ioc) ?_ measurable_const
  unfold dyadicAvg_shifted
  by_cases h : i.val = 0
  · simp only [h, ↓reduceDIte]; exact measurable_const
  · simp only [h, ↓reduceDIte]
    exact (dyadicAvg_measurable T φ h_meas n _).comp
      (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.2) : Ω × E))

/-- **Per-`(ω,e)` time-`L²` convergence of the shifted eval.** -/
lemma dyadicEvalShifted_inner_L2_tendsto
    {T : ℝ} (hT : 0 < T) (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M) (ω : Ω) (e : E) :
    Filter.Tendsto
      (fun n => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
  have hM'_nn : 0 ≤ max M 0 := le_max_right _ _
  have hsq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (‖x‖ ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm_eq_enorm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞) ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => ENNReal.ofReal ((2 * max M 0) ^ 2)) ?_ ?_ ?_ ?_
  · intro n
    exact ((ENNReal.continuous_coe.measurable.comp
      ((h_meas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))).sub
        ((dyadicEvalShifted_measurable_prod φ h_meas n ω).comp
          (by fun_prop : Measurable fun s : ℝ => ((s, e) : ℝ × E)))).nnnorm).pow_const 2).aemeasurable
  · intro n
    refine Filter.Eventually.of_forall (fun s => ?_)
    simp only []
    rw [hsq]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ ≤ 2 * max M 0 := by
      rw [Real.norm_eq_abs]
      calc |φ ω s e - dyadicEvalShifted T φ n s ω e|
          ≤ |φ ω s e| + |dyadicEvalShifted T φ n s ω e| := abs_sub _ _
        _ ≤ max M 0 + max M 0 :=
            add_le_add ((hM ω s e).trans (le_max_left _ _))
              (dyadicEvalShifted_bounded hT φ hM n s ω e)
        _ = 2 * max M 0 := by ring
    nlinarith [norm_nonneg (φ ω s e - dyadicEvalShifted T φ n s ω e), hb, hM'_nn]
  · rw [MeasureTheory.lintegral_const]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (MeasureTheory.measure_ne_top _ _)
  · filter_upwards [dyadicEvalShifted_ae_tendsto_per_param hT φ h_meas hM ω e] with s hs
    have hdiff : Filter.Tendsto (fun n => φ ω s e - dyadicEvalShifted T φ n s ω e)
        Filter.atTop (nhds 0) := by
      simpa using (tendsto_const_nhds (x := φ ω s e)).sub hs
    have hg : Continuous (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) :=
      (ENNReal.continuous_pow 2).comp (ENNReal.continuous_coe.comp continuous_nnnorm)
    simpa using (hg.tendsto 0).comp hdiff

set_option maxHeartbeats 1000000 in
/-- **`L²` convergence of the adapted (shifted) eval (finite-mark-support).** -/
lemma dyadicEvalShifted_L2_tendsto
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ) (h_meas : Measurable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    {M : ℝ} (hM : ∀ ω s e, |φ ω s e| ≤ M)
    {S : Set E} (hS_meas : MeasurableSet S) (hS_fin : ν S ≠ ⊤)
    (hSupp : ∀ ω e, e ∉ S → ∀ u, φ ω u e = 0) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  set M' : ℝ := max M 0 with hM'def
  have hM'_nn : 0 ≤ M' := le_max_right _ _
  have hφM' : ∀ ω s e, |φ ω s e| ≤ M' := fun ω s e => (hM ω s e).trans (le_max_left _ _)
  set cT : ℝ≥0∞ := ENNReal.ofReal ((2 * M') ^ 2 * T) with hcT
  have hFmeas : ∀ n : ℕ, Measurable (fun p : Ω × ℝ × E =>
      (‖φ p.1 p.2.1 p.2.2 - dyadicEvalShifted T φ n p.2.1 p.1 p.2.2‖₊ : ℝ≥0∞) ^ 2) := fun n =>
    (ENNReal.continuous_coe.measurable.comp
      (h_meas.sub (dyadicEvalShifted_measurable_triple φ h_meas n)).nnnorm).pow_const 2
  have hF_se : ∀ n ω, Measurable (fun q : ℝ × E =>
      (‖φ ω q.1 q.2 - dyadicEvalShifted T φ n q.1 ω q.2‖₊ : ℝ≥0∞) ^ 2) := fun n ω =>
    (ENNReal.continuous_coe.measurable.comp
      ((h_meas.comp (by fun_prop : Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).sub
        ((dyadicEvalShifted_measurable_prod φ h_meas n ω))).nnnorm).pow_const 2
  have hswap : ∀ n ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      = ∫⁻ e, (∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂ν := by
    intro n ω
    exact MeasureTheory.lintegral_lintegral_swap (hF_se n ω).aemeasurable
  have h_inner_le : ∀ n ω e,
      (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        ≤ S.indicator (fun _ => cT) e := by
    intro n ω e
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he]
      calc (∫⁻ s in Set.Icc (0 : ℝ) T,
              (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((2 * M') ^ 2) ∂volume := by
            refine MeasureTheory.lintegral_mono (fun s => ?_)
            rw [show (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2
                  = ENNReal.ofReal (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ ^ 2) from by
                rw [show (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞)
                      = ENNReal.ofReal ‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ from
                    (ofReal_norm_eq_enorm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]]
            refine ENNReal.ofReal_le_ofReal ?_
            have hb : ‖φ ω s e - dyadicEvalShifted T φ n s ω e‖ ≤ 2 * M' := by
              rw [Real.norm_eq_abs]
              calc |φ ω s e - dyadicEvalShifted T φ n s ω e|
                  ≤ |φ ω s e| + |dyadicEvalShifted T φ n s ω e| := abs_sub _ _
                _ ≤ M' + M' := add_le_add (hφM' ω s e) (dyadicEvalShifted_bounded hT φ hM n s ω e)
                _ = 2 * M' := by ring
            nlinarith [norm_nonneg (φ ω s e - dyadicEvalShifted T φ n s ω e), hb, hM'_nn]
        _ = cT := by
            rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, hcT,
              ← ENNReal.ofReal_mul (by positivity)]
            congr 1; rw [sub_zero]
    · have hzero : ∀ s, φ ω s e - dyadicEvalShifted T φ n s ω e = 0 := by
        intro s
        rw [hSupp ω e he s, dyadicEvalShifted_eq_zero φ n s ω e (hSupp ω e he), sub_zero]
      rw [Set.indicator_of_notMem he]
      simp only [hzero, nnnorm_zero, ENNReal.coe_zero]
      simp
  simp_rw [hswap]
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun _ => cT * ν S) ?_ ?_ (by
      rw [MeasureTheory.lintegral_const]
      exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin)
        (MeasureTheory.measure_ne_top _ _)) ?_
  · intro n
    refine Measurable.aemeasurable ?_
    have hmeas2 : Measurable (fun q : Ω × E => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖φ q.1 s q.2 - dyadicEvalShifted T φ n s q.1 q.2‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
      have hr : Measurable (fun p : (Ω × E) × ℝ =>
          (‖φ p.1.1 p.2 p.1.2 - dyadicEvalShifted T φ n p.2 p.1.1 p.1.2‖₊ : ℝ≥0∞) ^ 2) :=
        (hFmeas n).comp (by fun_prop :
          Measurable fun p : (Ω × E) × ℝ => ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
      exact hr.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))
    exact hmeas2.lintegral_prod_right' (ν := ν)
  · intro n
    refine Filter.Eventually.of_forall (fun ω => ?_)
    calc (∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖φ ω s e - dyadicEvalShifted T φ n s ω e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν)
        ≤ ∫⁻ e, S.indicator (fun _ => cT) e ∂ν :=
          MeasureTheory.lintegral_mono (fun e => h_inner_le n ω e)
      _ = cT * ν S := by
          rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ : E, (0 : ℝ≥0∞) ∂ν from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun e => S.indicator (fun _ => cT) e) ?_ ?_ (by
        rw [MeasureTheory.lintegral_indicator hS_meas, MeasureTheory.setLIntegral_const]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_fin) ?_
    · intro n
      have hes : Measurable (fun q : E × ℝ =>
          (‖φ ω q.2 q.1 - dyadicEvalShifted T φ n q.2 ω q.1‖₊ : ℝ≥0∞) ^ 2) := by
        refine (ENNReal.continuous_coe.measurable.comp (Measurable.sub ?_ ?_).nnnorm).pow_const 2
        · exact h_meas.comp (by fun_prop : Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))
        · exact (dyadicEvalShifted_measurable_prod φ h_meas n ω).comp measurable_swap
      exact (hes.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) T))).aemeasurable
    · intro n
      exact Filter.Eventually.of_forall (fun e => h_inner_le n ω e)
    · exact Filter.Eventually.of_forall
        (fun e => dyadicEvalShifted_inner_L2_tendsto hT φ h_meas hM ω e)

/-! ### Mark discretisation via rectangle density (general `E`)

To turn the (mark-continuous) shifted dyadic eval into a genuine `SimplePredictable`,
we approximate the mark dependence by `ℝ`-linear combinations of indicators of
measurable rectangles `A ×ˢ B`. These are dense in `L²(μΩ ⊗ μE)` for *finite*
measures by the monotone-class theorem over the rectangle π-system
(`isPiSystem_prod`/`generateFrom_prod`) — **no countable-generation/standard-Borel
on `E` is needed**. -/

/-- A finite `ℝ`-linear combination of indicators of measurable rectangles
`A ×ˢ B ⊆ Ω × E`. -/
def IsRectSimple (g : Ω × E → ℝ) : Prop :=
  ∃ L : List (ℝ × Set Ω × Set E),
    (∀ t ∈ L, MeasurableSet t.2.1 ∧ MeasurableSet t.2.2) ∧
    g = fun x => (L.map (fun t => t.1 * (t.2.1 ×ˢ t.2.2).indicator (fun _ => (1 : ℝ)) x)).sum

/-- The zero function is rectangle-simple (empty combination). -/
lemma IsRectSimple.zero : IsRectSimple (fun _ : Ω × E => (0 : ℝ)) :=
  ⟨[], by simp, by funext x; simp⟩

/-- The indicator of a measurable rectangle is rectangle-simple. -/
lemma IsRectSimple.rect {A : Set Ω} {B : Set E} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    IsRectSimple (fun x : Ω × E => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) x) := by
  refine ⟨[(1, A, B)], by simp [hA, hB], ?_⟩
  funext x; simp

/-- Rectangle-simple functions are closed under addition (list concatenation). -/
lemma IsRectSimple.add {g h : Ω × E → ℝ} (hg : IsRectSimple g) (hh : IsRectSimple h) :
    IsRectSimple (g + h) := by
  obtain ⟨L₁, hL₁, hgeq⟩ := hg
  obtain ⟨L₂, hL₂, hheq⟩ := hh
  refine ⟨L₁ ++ L₂, ?_, ?_⟩
  · intro t ht; rcases List.mem_append.mp ht with h' | h'
    exacts [hL₁ t h', hL₂ t h']
  · funext x; simp only [Pi.add_apply, hgeq, hheq, List.map_append, List.sum_append]

/-- Rectangle-simple functions are closed under scalar multiplication. -/
lemma IsRectSimple.smul {g : Ω × E → ℝ} (hg : IsRectSimple g) (c : ℝ) :
    IsRectSimple (fun x => c * g x) := by
  obtain ⟨L, hL, hgeq⟩ := hg
  refine ⟨L.map (fun t => (c * t.1, t.2.1, t.2.2)), ?_, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
    exact hL t' ht'
  · funext x
    simp only [hgeq]
    clear hgeq hL
    induction L with
    | nil => simp
    | cons hd tl ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [mul_add, ih]; ring

/-- A rectangle-simple function is measurable. -/
lemma IsRectSimple.measurable {g : Ω × E → ℝ} (hg : IsRectSimple g) : Measurable g := by
  obtain ⟨L, hL, rfl⟩ := hg
  induction L with
  | nil => simp only [List.map_nil, List.sum_nil]; exact measurable_const
  | cons t L ih =>
    simp only [List.map_cons, List.sum_cons]
    have ht := hL t (List.mem_cons_self)
    refine Measurable.add ?_ (ih (fun s hs => hL s (List.mem_cons_of_mem t hs)))
    exact measurable_const.mul (measurable_const.indicator (ht.1.prod ht.2))

/-- Rectangle-simple functions are a.e.-strongly-measurable for any measure. -/
lemma IsRectSimple.aestronglyMeasurable {g : Ω × E → ℝ} (hg : IsRectSimple g)
    (μ : Measure (Ω × E)) : MeasureTheory.AEStronglyMeasurable g μ :=
  hg.measurable.aestronglyMeasurable

/-- Rectangle-simple functions are closed under finite sums. -/
lemma IsRectSimple.sum {ι : Type*} (s : Finset ι) (f : ι → Ω × E → ℝ)
    (h : ∀ i ∈ s, IsRectSimple (f i)) : IsRectSimple (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using IsRectSimple.zero
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self i s)).add
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

/-- `f` is approximable in `L²(μ)` by rectangle-simple functions. -/
def RectApprox (μ : Measure (Ω × E)) (f : Ω × E → ℝ) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ g, IsRectSimple g ∧ MeasureTheory.eLpNorm (f - g) 2 μ < ε

/-- **Indicators of measurable sets are rectangle-approximable in `L²`** (finite `μ`).
Monotone-class induction over the rectangle π-system (`isPiSystem_prod`): rectangles are
exact; the empty set and complements/countable disjoint unions follow from subspace
structure + `L²`-tail control. **General `E` — no countable generation needed.** -/
lemma rectApprox_indicator (μ : Measure (Ω × E)) [IsFiniteMeasure μ]
    {C : Set (Ω × E)} (hC : MeasurableSet C) :
    RectApprox μ (C.indicator (fun _ => (1 : ℝ))) := by
  induction C, hC using
      MeasurableSpace.induction_on_inter generateFrom_prod.symm isPiSystem_prod with
  | empty =>
    intro ε hε
    refine ⟨fun _ => 0, IsRectSimple.zero, ?_⟩
    rw [show ((∅ : Set (Ω × E)).indicator (fun _ => (1 : ℝ))) - (fun _ => 0) = 0 from by
      funext x; simp]
    rwa [MeasureTheory.eLpNorm_zero]
  | basic u hu =>
    obtain ⟨A, hA, B, hB, rfl⟩ := Set.mem_image2.mp hu
    intro ε hε
    refine ⟨fun x => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) x, IsRectSimple.rect hA hB, ?_⟩
    rw [show ((A ×ˢ B).indicator (fun _ => (1 : ℝ)))
          - (fun x => (A ×ˢ B).indicator (fun _ => (1 : ℝ)) x) = 0 from by funext x; simp]
    rwa [MeasureTheory.eLpNorm_zero]
  | compl u hu ih =>
    intro ε hε
    obtain ⟨g, hg, hgerr⟩ := ih ε hε
    refine ⟨(fun x => (Set.univ ×ˢ Set.univ).indicator (fun _ => (1 : ℝ)) x)
        + (fun x => -1 * g x),
      (IsRectSimple.rect MeasurableSet.univ MeasurableSet.univ).add (hg.smul (-1)), ?_⟩
    have heq : (uᶜ.indicator (fun _ => (1 : ℝ)))
        - ((fun x => (Set.univ ×ˢ Set.univ).indicator (fun _ => (1 : ℝ)) x) + (fun x => -1 * g x))
        = -(u.indicator (fun _ => (1 : ℝ)) - g) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply]
      by_cases hx : x ∈ u
      · rw [Set.indicator_of_mem hx, Set.indicator_of_notMem (by simpa using hx),
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_univ _⟩)]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_mem (by simpa using hx),
          Set.indicator_of_mem (Set.mem_prod.mpr ⟨Set.mem_univ _, Set.mem_univ _⟩)]; ring
    rw [heq, MeasureTheory.eLpNorm_neg]
    exact hgerr
  | iUnion F hFd hFm ih =>
    intro ε hε
    rcases eq_or_ne ε ⊤ with rfl | hεtop
    · -- `ε = ⊤`: the zero approximant already has finite `L²` norm (finite measure).
      refine ⟨fun _ => 0, IsRectSimple.zero, ?_⟩
      rw [show ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - fun _ => (0 : ℝ))
            = (⋃ i, F i).indicator (fun _ => (1 : ℝ)) from by funext x; simp,
        MeasureTheory.eLpNorm_indicator_const (MeasurableSet.iUnion hFm)
          (by norm_num) (by norm_num)]
      simp only [enorm_one, one_mul]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top _ _)
    have hε2 : (0 : ℝ≥0∞) < ε / 2 := ENNReal.div_pos hε.ne' (by norm_num)
    set S : ℕ → Set (Ω × E) := fun N => ⋃ i ∈ Finset.range N, F i with hSdef
    have hSmono : Monotone S := fun a b hab =>
      Set.biUnion_subset_biUnion_left (fun i hi =>
        Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hi) hab))
    have hSunion : ⋃ N, S N = ⋃ i, F i := by
      ext x; simp only [hSdef, Set.mem_iUnion, Finset.mem_range]
      exact ⟨fun ⟨_, i, _, hx⟩ => ⟨i, hx⟩, fun ⟨i, hx⟩ => ⟨i + 1, i, Nat.lt_succ_self i, hx⟩⟩
    have hSmeas : ∀ N, MeasurableSet (S N) := fun N =>
      MeasurableSet.biUnion (Set.to_countable _) (fun i _ => hFm i)
    have hSsub : ∀ N, S N ⊆ ⋃ i, F i := fun N => hSunion ▸ Set.subset_iUnion S N
    -- the partial unions are disjoint sums of the `F i`.
    have hSsum : ∀ N, (S N).indicator (fun _ => (1 : ℝ))
        = ∑ i ∈ Finset.range N, (F i).indicator (fun _ => 1) := by
      intro N
      induction N with
      | zero => ext x; simp [hSdef]
      | succ n ih =>
        have hSsucc : S (n + 1) = S n ∪ F n := by
          simp only [hSdef, Finset.range_add_one, Finset.set_biUnion_insert]
          rw [Set.union_comm]
        have hdisj : Disjoint (S n) (F n) := by
          simp only [hSdef]
          rw [Set.disjoint_iUnion₂_left]
          exact fun i hi => hFd (Finset.mem_range.mp hi).ne
        rw [hSsucc, Set.indicator_union_of_disjoint hdisj, ih, Finset.sum_range_succ]
        rfl
    -- `μ((⋃F) \ Sₙ) → 0`, so the `L²` tail is eventually `< ε/2`.
    have hdiff_tend : Filter.Tendsto (fun N => μ ((⋃ i, F i) \ S N)) Filter.atTop (nhds 0) := by
      have hrw : ∀ N, μ ((⋃ i, F i) \ S N) = μ (⋃ i, F i) - μ (S N) := fun N =>
        measure_diff (hSsub N) (hSmeas N).nullMeasurableSet (measure_ne_top _ _)
      simp_rw [hrw]
      rw [show (0 : ℝ≥0∞) = μ (⋃ i, F i) - μ (⋃ i, F i) from (tsub_self _).symm]
      exact ENNReal.Tendsto.sub tendsto_const_nhds
        (hSunion ▸ tendsto_measure_iUnion_atTop hSmono) (Or.inl (measure_ne_top _ _))
    obtain ⟨N, hN⟩ := (hdiff_tend.eventually
      (gt_mem_nhds (show (0 : ℝ≥0∞) < (ε / 2) ^ 2 from by positivity))).exists
    -- approximate each `F i` (i < N) within `ε / (2·N)`.
    have hδ : (0 : ℝ≥0∞) < ε / 2 / N := ENNReal.div_pos hε2.ne' (by simp)
    choose g hg hgerr using fun i => ih i (ε / 2 / N) hδ
    refine ⟨∑ i ∈ Finset.range N, g i, IsRectSimple.sum _ _ (fun i _ => hg i), ?_⟩
    -- split: tail + finite-sum error.
    have htail : MeasureTheory.eLpNorm
        ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1)) 2 μ < ε / 2 := by
      rw [show ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1))
            = ((⋃ i, F i) \ S N).indicator (fun _ => 1) from
          (Set.indicator_diff (hSsub N) _).symm,
        MeasureTheory.eLpNorm_indicator_const
          (MeasurableSet.diff (MeasurableSet.iUnion hFm) (hSmeas N))
          (by norm_num) (by norm_num)]
      simp only [enorm_one, one_mul]
      calc (μ ((⋃ i, F i) \ S N)) ^ (1 / (2 : ℝ≥0∞).toReal)
          < ((ε / 2) ^ 2) ^ (1 / (2 : ℝ≥0∞).toReal) := by
            apply ENNReal.rpow_lt_rpow hN (by norm_num)
        _ = ε / 2 := by
            have h2 : (2 : ℝ≥0∞).toReal = 2 := by simp
            rw [h2, ← ENNReal.rpow_natCast (ε / 2) 2, ← ENNReal.rpow_mul,
              show ((2 : ℕ) : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
    -- the finite-sum error is `≤ ε/2` (with `0 ≤ ε/2` covering the `N = 0` corner).
    have hfin_le : MeasureTheory.eLpNorm
        ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) 2 μ ≤ ε / 2 := by
      rw [hSsum, ← Finset.sum_sub_distrib]
      refine le_trans (MeasureTheory.eLpNorm_sum_le
        (fun i _ => ((measurable_const.indicator (hFm i)).aestronglyMeasurable.sub
          ((hg i).aestronglyMeasurable μ))) (by norm_num)) ?_
      refine le_trans (Finset.sum_le_sum (fun i _ => (hgerr i).le)) ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      rcases Nat.eq_zero_or_pos N with hN0 | hN0
      · simp [hN0]
      · exact le_of_eq (ENNReal.mul_div_cancel (by exact_mod_cast hN0.ne') (by simp))
    have hfin_ne : MeasureTheory.eLpNorm
        ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) 2 μ ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.div_ne_top hεtop (by norm_num)) hfin_le
    calc MeasureTheory.eLpNorm ((⋃ i, F i).indicator (fun _ => (1 : ℝ))
            - ∑ i ∈ Finset.range N, g i) 2 μ
        ≤ MeasureTheory.eLpNorm
              ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1)) 2 μ
            + MeasureTheory.eLpNorm
              ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) 2 μ := by
          rw [show ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i)
                = ((⋃ i, F i).indicator (fun _ => (1 : ℝ)) - (S N).indicator (fun _ => 1))
                  + ((S N).indicator (fun _ => (1 : ℝ)) - ∑ i ∈ Finset.range N, g i) from by
              funext x
              simp only [Pi.sub_apply, Pi.add_apply, Finset.sum_apply]
              ring]
          exact MeasureTheory.eLpNorm_add_le
            ((measurable_const.indicator (MeasurableSet.iUnion hFm)).aestronglyMeasurable.sub
              (measurable_const.indicator (hSmeas N)).aestronglyMeasurable)
            ((measurable_const.indicator (hSmeas N)).aestronglyMeasurable.sub
              ((IsRectSimple.sum _ _ (fun i _ => hg i)).aestronglyMeasurable μ)) (by norm_num)
      _ < ε / 2 + ε / 2 := ENNReal.add_lt_add_of_lt_of_le hfin_ne htail hfin_le
      _ = ε := ENNReal.add_halves ε

/-- Rectangle-approximability in `L²` is preserved under scalar multiplication. -/
lemma RectApprox.const_smul {μ : Measure (Ω × E)} {f : Ω × E → ℝ}
    (hf : RectApprox μ f) (c : ℝ) : RectApprox μ (c • f) := by
  rcases eq_or_ne c 0 with rfl | hc
  · rw [zero_smul]
    intro ε hε
    refine ⟨fun _ => 0, IsRectSimple.zero, ?_⟩
    rw [show (0 : Ω × E → ℝ) - (fun _ => 0) = 0 from by funext x; simp,
      MeasureTheory.eLpNorm_zero]
    exact hε
  · intro ε hε
    have hcn : ‖c‖ₑ ≠ 0 := by simp [hc]
    obtain ⟨g, hg, hgerr⟩ := hf (ε / ‖c‖ₑ) (ENNReal.div_pos hε.ne' enorm_ne_top)
    refine ⟨c • g, hg.smul c, ?_⟩
    rw [show c • f - c • g = c • (f - g) from (smul_sub c f g).symm,
      MeasureTheory.eLpNorm_const_smul]
    calc ‖c‖ₑ * MeasureTheory.eLpNorm (f - g) 2 μ
        < ‖c‖ₑ * (ε / ‖c‖ₑ) := ENNReal.mul_lt_mul_right hcn enorm_ne_top hgerr
      _ = ε := ENNReal.mul_div_cancel hcn enorm_ne_top

/-- The indicator of a measurable set scaled by a constant is `L²`-approximable by
rectangle-simple functions (finite measure, **general `E`**). -/
lemma rectApprox_indicator_const (μ : Measure (Ω × E)) [IsFiniteMeasure μ]
    {s : Set (Ω × E)} (hs : MeasurableSet s) (c : ℝ) :
    RectApprox μ (s.indicator (fun _ => c)) := by
  have h := (rectApprox_indicator μ hs).const_smul c
  rwa [show c • s.indicator (fun _ => (1 : ℝ)) = s.indicator (fun _ => c) from by
    funext x
    by_cases hx : x ∈ s
    · simp [Set.indicator_of_mem hx]
    · simp [Set.indicator_of_notMem hx]] at h

/-- **Rectangle-simple functions are dense in `L²(μ)`** for any finite measure `μ` on
`Ω × E`, with **no countable-generation/standard-Borel hypothesis on the mark space `E`**.
Reduces (via `MemLp.induction_dense`) to the indicator case `rectApprox_indicator_const`,
using closure of `IsRectSimple` under addition. -/
lemma rectSimple_dense_L2 (μ : Measure (Ω × E)) [IsFiniteMeasure μ] {f : Ω × E → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ g, IsRectSimple g ∧ MeasureTheory.eLpNorm (f - g) 2 μ ≤ ε := by
  obtain ⟨g, hgerr, hg⟩ := MeasureTheory.MemLp.induction_dense (by norm_num) IsRectSimple
    (fun c s hs hμs ε' hε' => by
      obtain ⟨g, hg, hgerr⟩ := rectApprox_indicator_const μ hs c ε' (pos_iff_ne_zero.mpr hε')
      exact ⟨g, by rw [MeasureTheory.eLpNorm_sub_comm]; exact hgerr.le, hg⟩)
    (fun f g hf hg => hf.add hg) (fun f hf => hf.aestronglyMeasurable μ) hf hε
  exact ⟨g, hg, hgerr⟩

/-- **Rectangle-simple `L²` approximating sequence.** Any `L²` function on `Ω × E`
(finite `μ`, **general `E`**) is the `L²`-limit of a sequence of rectangle-simple
functions — the form consumed by the `masterApprox` Cauchy/limit construction. -/
lemma rectSimple_L2_tendsto (μ : Measure (Ω × E)) [IsFiniteMeasure μ] {f : Ω × E → ℝ}
    (hf : MeasureTheory.MemLp f 2 μ) :
    ∃ g : ℕ → (Ω × E → ℝ), (∀ n, IsRectSimple (g n)) ∧
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f - g n) 2 μ) Filter.atTop (nhds 0) := by
  choose g hg hgerr using fun n : ℕ =>
    rectSimple_dense_L2 μ hf (ENNReal.inv_ne_zero.mpr (ENNReal.natCast_ne_top n))
  exact ⟨g, hg, tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) hgerr⟩

/-! ### Step (finite-sum) predictable integrands

The mark-discretised approximant is rank-`>1` in the mark, so it is a finite
`ℝ`-combination of `SimplePredictable` pieces rather than a single one. Its
compensated integral is the sum of the pieces' integrals, and (being a sum of the
per-piece martingales) it is again a martingale on the natural filtration. -/

/-- The compensated integral of a **finite family** of simple predictable
integrands: `∑ⱼ ∫ φⱼ dÑ`. -/
noncomputable def stepIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ j, simpleIntegral N (Φ j) t ω

/-- The step integral vanishes at time `0` (each piece does). -/
lemma stepIntegral_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T) (ω : Ω) :
    stepIntegral N Φ 0 ω = 0 := by
  simp [stepIntegral, simpleIntegral_zero]

/-- A finite family of adapted simple predictables integrates to a martingale on the
natural filtration (the finite sum of the per-piece compensated martingales). -/
lemma martingale_stepIntegral_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T)
    (h_adapt : ∀ j : Fin k, ∀ i : Fin (Φ j).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Poisson.naturalFiltration N).seq ((Φ j).partition i.castSucc))
        ((Φ j).ξ i)) :
    MeasureTheory.Martingale (fun t : ℝ => stepIntegral N Φ t)
      (LevyStochCalc.Poisson.naturalFiltration N) P := by
  have hfun : (fun t : ℝ => stepIntegral N Φ t)
      = ∑ j : Fin k, (fun t : ℝ => simpleIntegral N (Φ j) t) := by
    funext t ω
    simp only [stepIntegral, Finset.sum_apply]
  rw [hfun]
  have hmart : ∀ s : Finset (Fin k),
      MeasureTheory.Martingale (∑ j ∈ s, fun t : ℝ => simpleIntegral N (Φ j) t)
        (LevyStochCalc.Poisson.naturalFiltration N) P := by
    intro s
    induction s using Finset.induction with
    | empty =>
        simp only [Finset.sum_empty]
        exact MeasureTheory.martingale_zero ℝ _ P
    | insert j s hj ih =>
        rw [Finset.sum_insert hj]
        exact (martingale_simpleIntegral_compensated N (Φ j) (h_adapt j)).add ih
  exact hmart Finset.univ

/-- A finite family of simple predictables integrates to an `L²` function at the
horizon `T` (finite sum of the per-piece `L²` integrals). -/
lemma stepIntegral_memLp_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (hT : 0 < T) {k : ℕ} (Φ : Fin k → SimplePredictable Ω E ν T)
    (h_adapt : ∀ j : Fin k, ∀ i : Fin (Φ j).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic ((Φ j).partition i.castSucc) ×ˢ Set.univ
                                    ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) ((Φ j).ξ i)) :
    MeasureTheory.MemLp (fun ω => stepIntegral N Φ T ω) 2 P :=
  MeasureTheory.memLp_finsetSum Finset.univ
    (fun j _ => simpleIntegral_memLp_compensated N hT (Φ j) (h_adapt j))

/-- **Disjoint compensated increments are uncorrelated.** For measurable `B, B'`
with finite reference intensity and `Disjoint B B'`, the compensated values
`Ñ(B), Ñ(B')` are independent (Poisson disjoint independence) and mean-zero, so
`E[Ñ(B)·Ñ(B')] = 0`. The bilinear building block for the step-integral isometry.
(The two-set family is indexed by `ULift (Fin 2)` to match the structure-field
universe of `independent_disjoint`.) -/
lemma compensated_cross_disjoint_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hdisj : Disjoint B B') :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P = 0 := by
  -- index the pair by `ULift (Fin 2)` (universe of `independent_disjoint`'s `ι`).
  set G : ULift (Fin 2) → Set (ℝ × E) := fun i => ![B, B'] i.down with hG
  have hmeas : ∀ i, MeasurableSet (G i) := by
    rintro ⟨i⟩; fin_cases i <;> first | exact hB | exact hB'
  have hpair : Pairwise (fun i j => Disjoint (G i) (G j)) := by
    rintro ⟨i⟩ ⟨j⟩ hij
    fin_cases i <;> fin_cases j <;>
      first | exact absurd rfl hij | exact hdisj | exact hdisj.symm
  -- `N(·,B)` and `N(·,B')` are independent.
  have hidx : ProbabilityTheory.IndepFun (fun ω => N.N ω B) (fun ω => N.N ω B') P := by
    have h01 : (ULift.up (0 : Fin 2)) ≠ ULift.up (1 : Fin 2) := by
      simp [ULift.up_inj]
    have h := (N.independent_disjoint G hmeas hpair).indepFun h01
    simpa [hG] using h
  -- `Ñ(B) = (·.toReal − ν̂(B).toReal) ∘ N(·,B)`, so independence is preserved.
  have hcompeq : (fun ω => N.compensated B ω)
      = (fun x : ℝ≥0∞ => x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B).toReal)
        ∘ (fun ω => N.N ω B) := by funext ω; rfl
  have hcompeq' : (fun ω => N.compensated B' ω)
      = (fun x : ℝ≥0∞ => x.toReal - (LevyStochCalc.Poisson.referenceIntensity ν B').toReal)
        ∘ (fun ω => N.N ω B') := by funext ω; rfl
  have hindep : ProbabilityTheory.IndepFun
      (fun ω => N.compensated B ω) (fun ω => N.compensated B' ω) P := by
    rw [hcompeq, hcompeq']
    exact hidx.comp (ENNReal.measurable_toReal.sub_const _)
      (ENNReal.measurable_toReal.sub_const _)
  have hasm : MeasureTheory.AEStronglyMeasurable (fun ω => N.compensated B ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB)).sub_const _).aestronglyMeasurable
  have hasm' : MeasureTheory.AEStronglyMeasurable (fun ω => N.compensated B' ω) P :=
    ((ENNReal.measurable_toReal.comp (N.measurable_eval hB')).sub_const _).aestronglyMeasurable
  rw [hindep.integral_fun_mul_eq_mul_integral hasm hasm',
    compensated_mean_zero N hB hfin, zero_mul]

/-- **Second moment of a difference of disjoint compensated increments.** For
measurable disjoint `C, D` with finite intensity,
`E[(Ñ(C) − Ñ(D))²] = ν̂(C).toReal + ν̂(D).toReal` — the cross term drops out by
`compensated_cross_disjoint_zero`, the squares by `compensated_second_moment`.
This is the two-piece isometry for the disjoint-support step-integral route. -/
lemma compensated_diff_sq_disjoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {C D : Set (ℝ × E)} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤)
    (hDf : LevyStochCalc.Poisson.referenceIntensity ν D ≠ ⊤)
    (hdisj : Disjoint C D) :
    ∫ ω, (N.compensated C ω - N.compensated D ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν C).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal := by
  have hCsq := compensated_sq_integrable N hC hCf
  have hDsq := compensated_sq_integrable N hD hDf
  have hCD := compensated_cross_integrable N hC hD hCf hDf
  have h2UV : MeasureTheory.Integrable
      (fun ω => 2 * (N.compensated C ω * N.compensated D ω)) P := hCD.const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => (N.compensated C ω) ^ 2 - 2 * (N.compensated C ω * N.compensated D ω)) P :=
    hCsq.sub h2UV
  have hpt : (fun ω => (N.compensated C ω - N.compensated D ω) ^ 2)
      = (fun ω => (N.compensated C ω) ^ 2
          - 2 * (N.compensated C ω * N.compensated D ω) + (N.compensated D ω) ^ 2) := by
    funext ω; ring
  rw [hpt,
    MeasureTheory.integral_add hmid hDsq,
    MeasureTheory.integral_sub hCsq h2UV,
    MeasureTheory.integral_const_mul,
    compensated_cross_disjoint_zero N hC hD hCf hdisj,
    compensated_second_moment N hC hCf, compensated_second_moment N hD hDf]
  ring

/-- **Compensated additivity over `inter`/`diff`** (a.e.). For measurable `B` with
finite intensity and measurable `C`, `Ñ(B) = Ñ(B ∩ C) + Ñ(B ∖ C)` a.e. (where the
`ℕ`-valued count `N(·,B)` is finite). Measure additivity (`measure_inter_add_diff`)
in `toReal`. -/
lemma compensated_inter_add_diff_ae
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B C : Set (ℝ × E)} (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤) :
    (fun ω => N.compensated B ω)
      =ᵐ[P] (fun ω => N.compensated (B ∩ C) ω + N.compensated (B \ C) ω) := by
  filter_upwards [N.integer_valued hB hfin] with ω hω
  obtain ⟨n, hn⟩ := hω
  have hBfin : N.N ω B ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
  have hint_ne : N.N ω (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.inter_subset_left)
  have hdiff_ne : N.N ω (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hBfin (measure_mono Set.diff_subset)
  have hrefint : LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  have hrefdiff : LevyStochCalc.Poisson.referenceIntensity ν (B \ C) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.diff_subset)
  simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
  rw [show N.N ω B = N.N ω (B ∩ C) + N.N ω (B \ C) from
        (measure_inter_add_diff (μ := N.N ω) B hC).symm,
      show LevyStochCalc.Poisson.referenceIntensity ν B
          = LevyStochCalc.Poisson.referenceIntensity ν (B ∩ C)
            + LevyStochCalc.Poisson.referenceIntensity ν (B \ C) from
        (measure_inter_add_diff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B hC).symm,
      ENNReal.toReal_add hint_ne hdiff_ne, ENNReal.toReal_add hrefint hrefdiff]
  ring

/-- **Polarisation expansion** of the squared difference: for measurable `B, B'`
with finite intensity, `E[(Ñ(B) − Ñ(B'))²] = ν̂(B).toReal − 2·E[Ñ(B)Ñ(B')] + ν̂(B').toReal`
(squares via `compensated_second_moment`, cross term left symbolic). -/
lemma compensated_diff_sq_expand
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hfin' : LevyStochCalc.Poisson.referenceIntensity ν B' ≠ ⊤) :
    ∫ ω, (N.compensated B ω - N.compensated B' ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν B).toReal
        - 2 * (∫ ω, N.compensated B ω * N.compensated B' ω ∂P)
        + (LevyStochCalc.Poisson.referenceIntensity ν B').toReal := by
  have hBsq := compensated_sq_integrable N hB hfin
  have hB'sq := compensated_sq_integrable N hB' hfin'
  have hBB' := compensated_cross_integrable N hB hB' hfin hfin'
  have h2 : MeasureTheory.Integrable
      (fun ω => 2 * (N.compensated B ω * N.compensated B' ω)) P := hBB'.const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => (N.compensated B ω) ^ 2 - 2 * (N.compensated B ω * N.compensated B' ω)) P :=
    hBsq.sub h2
  have hpt : (fun ω => (N.compensated B ω - N.compensated B' ω) ^ 2)
      = (fun ω => (N.compensated B ω) ^ 2
          - 2 * (N.compensated B ω * N.compensated B' ω) + (N.compensated B' ω) ^ 2) := by
    funext ω; ring
  rw [hpt, MeasureTheory.integral_add hmid hB'sq,
    MeasureTheory.integral_sub hBsq h2, MeasureTheory.integral_const_mul,
    compensated_second_moment N hB hfin, compensated_second_moment N hB' hfin']

/-- **Bilinear covariance of compensated increments.** For measurable `B, B'` with
finite intensity, `E[Ñ(B)·Ñ(B')] = ν̂(B ∩ B').toReal` — the full polarisation of
`compensated_second_moment`, construction-agnostic (no disjointness). Combines the
`Ñ(B)−Ñ(B') =ᵃᵉ Ñ(B∖B')−Ñ(B'∖B)` decomposition (`compensated_inter_add_diff_ae`),
the disjoint two-piece value (`compensated_diff_sq_disjoint`), the polarisation
expansion (`compensated_diff_sq_expand`), and intensity inclusion–exclusion. -/
lemma compensated_cross_covariance
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {B B' : Set (ℝ × E)} (hB : MeasurableSet B) (hB' : MeasurableSet B')
    (hfin : LevyStochCalc.Poisson.referenceIntensity ν B ≠ ⊤)
    (hfin' : LevyStochCalc.Poisson.referenceIntensity ν B' ≠ ⊤) :
    ∫ ω, N.compensated B ω * N.compensated B' ω ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal := by
  set C := B \ B' with hCdef
  set D := B' \ B with hDdef
  have hCmeas : MeasurableSet C := hB.diff hB'
  have hDmeas : MeasurableSet D := hB'.diff hB
  have hdisj : Disjoint C D := disjoint_sdiff_sdiff
  have hCf : LevyStochCalc.Poisson.referenceIntensity ν C ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.diff_subset)
  have hDf : LevyStochCalc.Poisson.referenceIntensity ν D ≠ ⊤ :=
    ne_top_of_le_ne_top hfin' (measure_mono Set.diff_subset)
  have hrefint : LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B') ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  -- a.e. `Ñ(B) − Ñ(B') = Ñ(C) − Ñ(D)`.
  have hsub_ae : (fun ω => N.compensated B ω - N.compensated B' ω)
      =ᵐ[P] (fun ω => N.compensated C ω - N.compensated D ω) := by
    filter_upwards [compensated_inter_add_diff_ae N hB hB' hfin,
      compensated_inter_add_diff_ae N hB' hB hfin'] with ω h1 h2
    rw [h1, h2, Set.inter_comm B' B]; ring
  have hsq_ae : (fun ω => (N.compensated B ω - N.compensated B' ω) ^ 2)
      =ᵐ[P] (fun ω => (N.compensated C ω - N.compensated D ω) ^ 2) :=
    hsub_ae.mono (fun ω h => by
      show (N.compensated B ω - N.compensated B' ω) ^ 2
        = (N.compensated C ω - N.compensated D ω) ^ 2
      rw [show N.compensated B ω - N.compensated B' ω
            = N.compensated C ω - N.compensated D ω from h])
  have hsq_eq : ∫ ω, (N.compensated B ω - N.compensated B' ω) ^ 2 ∂P
      = (LevyStochCalc.Poisson.referenceIntensity ν C).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal :=
    (MeasureTheory.integral_congr_ae hsq_ae).trans
      (compensated_diff_sq_disjoint N hCmeas hDmeas hCf hDf hdisj)
  have hexp := compensated_diff_sq_expand N hB hB' hfin hfin'
  -- intensity inclusion–exclusion (in `toReal`).
  have hrefB : (LevyStochCalc.Poisson.referenceIntensity ν B).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν C).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν B
          = LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')
            + LevyStochCalc.Poisson.referenceIntensity ν C from
        (measure_inter_add_diff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B hB').symm,
      ENNReal.toReal_add hrefint hCf]
  have hrefB' : (LevyStochCalc.Poisson.referenceIntensity ν B').toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (B ∩ B')).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν D).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν B'
          = LevyStochCalc.Poisson.referenceIntensity ν (B' ∩ B)
            + LevyStochCalc.Poisson.referenceIntensity ν D from
        (measure_inter_add_diff (μ := LevyStochCalc.Poisson.referenceIntensity ν) B' hB).symm,
      Set.inter_comm B' B, ENNReal.toReal_add hrefint hDf]
  rw [hexp] at hsq_eq
  linarith [hsq_eq, hrefB, hrefB']

/-- **Weighted second moment of a future-box compensated value.** For a past-at-`a`
(i.e. `ℱ_a`-)measurable weight `g` and a future box `(a,b] × A`,
`E[g·Ñ((a,b]×A)²] = E[g]·ν̂((a,b]×A).toReal`: `g` is independent of `Ñ(box)`
(`indepFun_past_compensated_box`), hence of its square, and `E[Ñ(box)²] = ν̂(box)`. -/
lemma weighted_box_sq_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAf : ν A ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq a) g) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P)
        * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal := by
  have hbox_meas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hbox_fin : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAf
  have h_indep := indepFun_past_compensated_box N ha hab hA hAf hg
  have h_indep_sq : ProbabilityTheory.IndepFun g
      (fun ω => (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2) P :=
    h_indep.comp measurable_id (measurable_id.pow_const 2)
  rw [h_indep_sq.integral_fun_mul_eq_mul_integral
      ((hg.mono ((LevyStochCalc.Poisson.naturalFiltration N).le' a)).measurable.aestronglyMeasurable)
      (((ENNReal.measurable_toReal.comp
        (N.measurable_eval hbox_meas)).sub_const _).pow_const 2).aestronglyMeasurable,
    compensated_second_moment N hbox_meas hbox_fin]

/-- **Same-time, disjoint-mark weighted cross term vanishes.** For an `ℱ_a`-measurable
bounded weight `g` and two future boxes `(a,b]×A`, `(a,b]×A'` on **disjoint** marks
`A, A'`, `E[g·Ñ((a,b]×A)·Ñ((a,b]×A')] = 0`. Polarising through the union box
`(a,b]×(A∪A')` reduces each term to `weighted_box_sq_eq`, and `ν̂(R∪R') = ν̂(R)+ν̂(R')`
(disjoint) makes the combination cancel. **No strengthening of the per-box past/future
independence is needed.** -/
lemma weighted_box_cross_disjoint_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hAf : ν A ≠ ⊤) (hA'f : ν A' ≠ ⊤) (hdisjA : Disjoint A A')
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P = 0 := by
  set R := Set.Ioc a b ×ˢ A with hRdef
  set R' := Set.Ioc a b ×ˢ A' with hR'def
  have hRmeas : MeasurableSet R := measurableSet_Ioc.prod hA
  have hR'meas : MeasurableSet R' := measurableSet_Ioc.prod hA'
  have hRf : LevyStochCalc.Poisson.referenceIntensity ν R ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAf
  have hR'f : LevyStochCalc.Poisson.referenceIntensity ν R' ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hA'f
  have hUAf : ν (A ∪ A') ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hAf, hA'f⟩) (measure_union_le A A')
  have hRUeq : R ∪ R' = Set.Ioc a b ×ˢ (A ∪ A') := Set.prod_union.symm
  have hRUf : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∪ A')) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hUAf
  have hRdisj : Disjoint R R' := Set.disjoint_prod.mpr (Or.inr hdisjA)
  -- a.e. compensated additivity on the disjoint union.
  have hadd_ae : (fun ω => N.compensated (R ∪ R') ω)
      =ᵐ[P] (fun ω => N.compensated R ω + N.compensated R' ω) := by
    filter_upwards [N.integer_valued (hRmeas.union hR'meas) (hRUeq ▸ hRUf)] with ω hω
    obtain ⟨n, hn⟩ := hω
    have hUfin : N.N ω (R ∪ R') ≠ ⊤ := by rw [hn]; exact ENNReal.natCast_ne_top n
    have hRne : N.N ω R ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono Set.subset_union_left)
    have hR'ne : N.N ω R' ≠ ⊤ := ne_top_of_le_ne_top hUfin (measure_mono Set.subset_union_right)
    simp only [LevyStochCalc.Poisson.PoissonRandomMeasure.compensated]
    rw [show N.N ω (R ∪ R') = N.N ω R + N.N ω R' from measure_union hRdisj hR'meas,
      show LevyStochCalc.Poisson.referenceIntensity ν (R ∪ R')
          = LevyStochCalc.Poisson.referenceIntensity ν R
            + LevyStochCalc.Poisson.referenceIntensity ν R' from measure_union hRdisj hR'meas,
      ENNReal.toReal_add hRne hR'ne, ENNReal.toReal_add hRf hR'f]
    ring
  -- integrability of `g·Ñ(box)²` (bounded weight × square-integrable).
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono ((LevyStochCalc.Poisson.naturalFiltration N).le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hiR : MeasureTheory.Integrable (fun ω => g ω * (N.compensated R ω) ^ 2) P :=
    (compensated_sq_integrable N hRmeas hRf).bdd_mul hg_aesm hgbnd
  have hiR' : MeasureTheory.Integrable (fun ω => g ω * (N.compensated R' ω) ^ 2) P :=
    (compensated_sq_integrable N hR'meas hR'f).bdd_mul hg_aesm hgbnd
  have hiU : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (R ∪ R') ω) ^ 2) P :=
    (compensated_sq_integrable N (hRmeas.union hR'meas) (hRUeq ▸ hRUf)).bdd_mul hg_aesm hgbnd
  -- pointwise polarisation (a.e., using the additivity).
  have hpt_ae : (fun ω => g ω * (N.compensated R ω * N.compensated R' ω))
      =ᵐ[P] (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)
          - 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)
          - 2⁻¹ * (g ω * (N.compensated R' ω) ^ 2)) := by
    filter_upwards [hadd_ae] with ω h
    rw [h]; ring
  have hfX : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)) P := hiU.const_mul 2⁻¹
  have hfY : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)) P := hiR.const_mul 2⁻¹
  have hfZ : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated R' ω) ^ 2)) P := hiR'.const_mul 2⁻¹
  have hfXY : MeasureTheory.Integrable
      (fun ω => 2⁻¹ * (g ω * (N.compensated (R ∪ R') ω) ^ 2)
        - 2⁻¹ * (g ω * (N.compensated R ω) ^ 2)) P := hfX.sub hfY
  rw [MeasureTheory.integral_congr_ae hpt_ae,
    MeasureTheory.integral_sub hfXY hfZ,
    MeasureTheory.integral_sub hfX hfY,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  -- evaluate each weighted square via `weighted_box_sq_eq`.
  rw [show (∫ ω, g ω * (N.compensated (R ∪ R') ω) ^ 2 ∂P)
        = ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ (A ∪ A')) ω) ^ 2 ∂P from by rw [hRUeq],
    weighted_box_sq_eq N ha hab (hA.union hA') hUAf hg,
    weighted_box_sq_eq N ha hab hA hAf hg, weighted_box_sq_eq N ha hab hA' hA'f hg]
  -- `ν̂(R∪R') = ν̂(R)+ν̂(R')` (disjoint) ⇒ the bracket cancels.
  have hrefU : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∪ A'))).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν R).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν R').toReal := by
    rw [← hRUeq, show LevyStochCalc.Poisson.referenceIntensity ν (R ∪ R')
          = LevyStochCalc.Poisson.referenceIntensity ν R
            + LevyStochCalc.Poisson.referenceIntensity ν R' from measure_union hRdisj hR'meas,
      ENNReal.toReal_add hRf hR'f]
  rw [hrefU]; ring

/-- **Time-ordered weighted cross term vanishes.** For an `ℱ_c`-measurable weight `g`
and boxes `(a,b]×A`, `(c,d]×A'` with `b ≤ c` (time-ordered), the earlier factor
`g·Ñ((a,b]×A)` is past-at-`c` measurable while `Ñ((c,d]×A')` is a future increment, so
`E[g·Ñ((a,b]×A)·Ñ((c,d]×A')] = E[g·Ñ((a,b]×A)]·E[Ñ((c,d]×A')] = 0`. The full-box
analogue of `offDiagonal_increment_zero` (the weight is measurable up to the *later*
box's start `c`, which is what the cross-`φ` isometry supplies). -/
lemma weighted_box_cross_timeordered_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b c d : ℝ} (hc : 0 ≤ c) (hab : a < b) (hbc : b ≤ c) (hcd : c < d)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A') (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq c) g) :
    ∫ ω, g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc c d ×ˢ A') ω) ∂P = 0 := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  have hRmeas : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hR'meas : MeasurableSet (Set.Ioc c d ×ˢ A') := measurableSet_Ioc.prod hA'
  have hR'f : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc c d ×ˢ A') ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hA'f
  have hRsub : Set.Ioc a b ×ˢ A ⊆ Set.Iic c ×ˢ Set.univ :=
    fun x hx => ⟨le_trans hx.1.2 hbc, Set.mem_univ _⟩
  -- `Ñ((a,b]×A)` is past-at-`c` measurable.
  have hÑR_c : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c)
      (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω) := by
    unfold LevyStochCalc.Poisson.PoissonRandomMeasure.compensated
    exact (((LevyStochCalc.Poisson.measurable_random_measure_of_le N hRsub
      hRmeas).ennreal_toReal).sub measurable_const).stronglyMeasurable
  have hf_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c)
      (fun ω => g ω * N.compensated (Set.Ioc a b ×ˢ A) ω) :=
    hg.mul hÑR_c
  have h_indep : ProbabilityTheory.IndepFun
      (fun ω => g ω * N.compensated (Set.Ioc a b ×ˢ A) ω)
      (fun ω => N.compensated (Set.Ioc c d ×ˢ A') ω) P :=
    indepFun_past_compensated_box N hc hcd hA' hA'f hf_meas
  rw [show (fun ω => g ω
        * (N.compensated (Set.Ioc a b ×ˢ A) ω * N.compensated (Set.Ioc c d ×ˢ A') ω))
      = (fun ω => (g ω * N.compensated (Set.Ioc a b ×ˢ A) ω)
          * N.compensated (Set.Ioc c d ×ˢ A') ω) from by funext ω; ring,
    h_indep.integral_fun_mul_eq_mul_integral
      (hf_meas.mono (ℱ.le' c)).measurable.aestronglyMeasurable
      ((ENNReal.measurable_toReal.comp
        (N.measurable_eval hR'meas)).sub_const _).aestronglyMeasurable,
    compensated_mean_zero N hR'meas hR'f, mul_zero]

/-- **Weighted disjoint-difference second moment.** For an `ℱ_a`-measurable bounded
weight `g` and two same-time boxes on disjoint marks `C, D`,
`E[g·(Ñ((a,b]×C) − Ñ((a,b]×D))²] = E[g]·ν̂((a,b]×C) + E[g]·ν̂((a,b]×D)`. Polarisation
expansion: squares via `weighted_box_sq_eq`, cross via `weighted_box_cross_disjoint_zero`. -/
lemma weighted_box_diff_sq_disjoint
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {C D : Set E} (hC : MeasurableSet C) (hD : MeasurableSet D)
    (hCf : ν C ≠ ⊤) (hDf : ν D ≠ ⊤) (hdisjCD : Disjoint C D)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        - N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ C)).toReal
        + (∫ ω, g ω ∂P)
          * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ D)).toReal := by
  have hCm : MeasurableSet (Set.Ioc a b ×ˢ C) := measurableSet_Ioc.prod hC
  have hDm : MeasurableSet (Set.Ioc a b ×ˢ D) := measurableSet_Ioc.prod hD
  have hCf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ C) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hCf
  have hDf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ D) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hDf
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono ((LevyStochCalc.Poisson.naturalFiltration N).le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  have hiC : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2) P :=
    (compensated_sq_integrable N hCm hCf').bdd_mul hg_aesm hgbnd
  have hiD : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2) P :=
    (compensated_sq_integrable N hDm hDf').bdd_mul hg_aesm hgbnd
  have hiCD : MeasureTheory.Integrable
      (fun ω => 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        * N.compensated (Set.Ioc a b ×ˢ D) ω))) P :=
    ((compensated_cross_integrable N hCm hDm hCf' hDf').bdd_mul hg_aesm hgbnd).const_mul 2
  have hmid : MeasureTheory.Integrable
      (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2
        - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
          * N.compensated (Set.Ioc a b ×ˢ D) ω))) P := hiC.sub hiCD
  have hpt : (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
        - N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2)
      = (fun ω => (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω) ^ 2
          - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ C) ω
            * N.compensated (Set.Ioc a b ×ˢ D) ω)))
          + g ω * (N.compensated (Set.Ioc a b ×ˢ D) ω) ^ 2) := by
    funext ω; ring
  rw [hpt, MeasureTheory.integral_add hmid hiD,
    MeasureTheory.integral_sub hiC hiCD, MeasureTheory.integral_const_mul,
    weighted_box_cross_disjoint_zero N ha hab hC hD hCf hDf hdisjCD hg hgb,
    weighted_box_sq_eq N ha hab hC hCf hg, weighted_box_sq_eq N ha hab hD hDf hg]
  ring

/-- **Weighted same-time bilinear covariance.** For an `ℱ_a`-measurable bounded weight `g`
and two same-time boxes on arbitrary marks `A, A'`,
`E[g·Ñ((a,b]×A)·Ñ((a,b]×A')] = E[g]·ν̂((a,b]×(A∩A'))`. The weighted polarisation of
`weighted_box_sq_eq` (`Ñ(R)−Ñ(R') =ᵃᵉ Ñ((a,b]×(A∖A'))−Ñ((a,b]×(A'∖A))`, the weighted
disjoint difference value, and intensity inclusion–exclusion). Enables the
overlapping-mark step-integral isometry. -/
lemma weighted_box_cross_sametime
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {A A' : Set E} (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hAf : ν A ≠ ⊤) (hA'f : ν A' ≠ ⊤)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq a) g)
    {M : ℝ} (hgb : ∀ ω, |g ω| ≤ M) :
    ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P
      = (∫ ω, g ω ∂P)
        * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal := by
  have hAm : MeasurableSet (Set.Ioc a b ×ˢ A) := measurableSet_Ioc.prod hA
  have hA'm : MeasurableSet (Set.Ioc a b ×ˢ A') := measurableSet_Ioc.prod hA'
  have hAf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAf
  have hA'f' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A') ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hA'f
  have hmcf : ν (A \ A') ≠ ⊤ := ne_top_of_le_ne_top hAf (measure_mono Set.diff_subset)
  have hmdf : ν (A' \ A) ≠ ⊤ := ne_top_of_le_ne_top hA'f (measure_mono Set.diff_subset)
  have hmif : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A')) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top (ne_top_of_le_ne_top hAf (measure_mono Set.inter_subset_left))
  have hmcf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A \ A')) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hmcf
  have hmdf' : LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A' \ A)) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hmdf
  -- box set identities.
  have hBdiff : Set.Ioc a b ×ˢ A \ Set.Ioc a b ×ˢ A' = Set.Ioc a b ×ˢ (A \ A') := by
    ext ⟨x, e⟩; simp only [Set.mem_diff, Set.mem_prod]; tauto
  have hBa'diff : Set.Ioc a b ×ˢ A' \ Set.Ioc a b ×ˢ A = Set.Ioc a b ×ˢ (A' \ A) := by
    ext ⟨x, e⟩; simp only [Set.mem_diff, Set.mem_prod]; tauto
  have hBinter : Set.Ioc a b ×ˢ A ∩ Set.Ioc a b ×ˢ A' = Set.Ioc a b ×ˢ (A ∩ A') := by
    ext ⟨x, e⟩; simp only [Set.mem_inter_iff, Set.mem_prod]; tauto
  -- a.e. `Ñ(R) − Ñ(R') = Ñ((a,b]×(A∖A')) − Ñ((a,b]×(A'∖A))`.
  have hsub_ae : (fun ω => N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω)
      =ᵐ[P] (fun ω => N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
        - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) := by
    filter_upwards [compensated_inter_add_diff_ae N hAm hA'm hAf',
      compensated_inter_add_diff_ae N hA'm hAm hA'f'] with ω h1 h2
    rw [h1, h2, Set.inter_comm (Set.Ioc a b ×ˢ A') (Set.Ioc a b ×ˢ A), hBdiff, hBa'diff]
    ring
  have hg_aesm : MeasureTheory.AEStronglyMeasurable g P :=
    (hg.mono ((LevyStochCalc.Poisson.naturalFiltration N).le' a)).measurable.aestronglyMeasurable
  have hgbnd : ∀ᵐ ω ∂P, ‖g ω‖ ≤ M :=
    Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hgb ω)
  -- `∫ g·(Ñ(R)−Ñ(R'))²` via the weighted disjoint-difference value.
  have hsq_ae : (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2)
      =ᵐ[P] (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
        - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) ^ 2) :=
    hsub_ae.mono (fun ω h => by
      show g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
          - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2
        = g ω * (N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
          - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω) ^ 2
      rw [show N.compensated (Set.Ioc a b ×ˢ A) ω - N.compensated (Set.Ioc a b ×ˢ A') ω
          = N.compensated (Set.Ioc a b ×ˢ (A \ A')) ω
            - N.compensated (Set.Ioc a b ×ˢ (A' \ A)) ω from h])
  have hsq_eq : ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc a b ×ˢ (A \ A'))).toReal
        + (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν
            (Set.Ioc a b ×ˢ (A' \ A))).toReal :=
    (MeasureTheory.integral_congr_ae hsq_ae).trans
      (weighted_box_diff_sq_disjoint N ha hab (hA.diff hA') (hA'.diff hA) hmcf hmdf
        disjoint_sdiff_sdiff hg hgb)
  -- weighted polarisation expansion (cross term left symbolic).
  have hexp : ∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
        - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 ∂P
      = (∫ ω, g ω ∂P) * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal
        - 2 * (∫ ω, g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            * N.compensated (Set.Ioc a b ×ˢ A') ω) ∂P)
        + (∫ ω, g ω ∂P)
          * (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')).toReal := by
    have hiA : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2) P :=
      (compensated_sq_integrable N hAm hAf').bdd_mul hg_aesm hgbnd
    have hiA' : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2) P :=
      (compensated_sq_integrable N hA'm hA'f').bdd_mul hg_aesm hgbnd
    have hicross : MeasureTheory.Integrable
        (fun ω => 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
          * N.compensated (Set.Ioc a b ×ˢ A') ω))) P :=
      ((compensated_cross_integrable N hAm hA'm hAf' hA'f').bdd_mul hg_aesm hgbnd).const_mul 2
    have hmid : MeasureTheory.Integrable
        (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2
          - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            * N.compensated (Set.Ioc a b ×ˢ A') ω))) P := hiA.sub hicross
    rw [show (fun ω => g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
            - N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2)
          = fun ω => (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω) ^ 2
            - 2 * (g ω * (N.compensated (Set.Ioc a b ×ˢ A) ω
              * N.compensated (Set.Ioc a b ×ˢ A') ω)))
            + g ω * (N.compensated (Set.Ioc a b ×ˢ A') ω) ^ 2 from funext (fun ω => by ring),
      MeasureTheory.integral_add hmid hiA', MeasureTheory.integral_sub hiA hicross,
      MeasureTheory.integral_const_mul,
      weighted_box_sq_eq N ha hab hA hAf hg, weighted_box_sq_eq N ha hab hA' hA'f hg]
  -- intensity inclusion–exclusion (in `toReal`).
  have hrefBa : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A \ A'))).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)
          = LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A ∩ Set.Ioc a b ×ˢ A')
            + LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A \ Set.Ioc a b ×ˢ A')
          from (measure_inter_add_diff _ hA'm).symm,
      hBinter, hBdiff, ENNReal.toReal_add hmif hmcf']
  have hrefBa' : (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')).toReal
      = (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A ∩ A'))).toReal
        + (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (A' \ A))).toReal := by
    rw [show LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A')
          = LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A' ∩ Set.Ioc a b ×ˢ A)
            + LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A' \ Set.Ioc a b ×ˢ A)
          from (measure_inter_add_diff _ hAm).symm,
      Set.inter_comm (Set.Ioc a b ×ˢ A') (Set.Ioc a b ×ˢ A), hBinter, hBa'diff,
      ENNReal.toReal_add hmif hmdf']
  have key := hsq_eq.symm.trans hexp
  rw [hrefBa, hrefBa'] at key
  linear_combination (1 / 2 : ℝ) * key

/-- **Cross term of two disjoint-mark full-rect sums vanishes.** For a shared time
partition `p`, pairwise-disjoint marks (`Disjoint (A i) (A' i)`), and adapted bounded
coefficients, `E[(∑ᵢ ξᵢ Ñ((pᵢ,pᵢ₊₁]×Aᵢ))·(∑ⱼ ξ'ⱼ Ñ((pⱼ,pⱼ₊₁]×A'ⱼ))] = 0`. Every term
of the `(i,j)` double sum vanishes: `i=j` (same interval, disjoint marks) by
`weighted_box_cross_disjoint_zero`, `i≠j` (time-ordered) by
`weighted_box_cross_timeordered_zero`. The bilinear cross-vanishing underlying the
multi-mark step-integral isometry. -/
lemma crossSum_disjointMark_zero
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    (A A' : Fin N₀ → Set E)
    (hAm : ∀ i, MeasurableSet (A i)) (hA'm : ∀ i, MeasurableSet (A' i))
    (hAf : ∀ i, ν (A i) ≠ ⊤) (hA'f : ∀ i, ν (A' i) ≠ ⊤)
    (hdisj : ∀ i, Disjoint (A i) (A' i))
    (ξ ξ' : Fin N₀ → Ω → ℝ)
    (hξb : ∀ i, ∃ M, ∀ ω, |ξ i ω| ≤ M) (hξ'b : ∀ i, ∃ M, ∀ ω, |ξ' i ω| ≤ M)
    (hξm : ∀ i, Measurable (ξ i)) (hξ'm : ∀ i, Measurable (ξ' i))
    (h_adapt : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (p i.castSucc)) (ξ i))
    (h_adapt' : ∀ i, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (p i.castSucc)) (ξ' i)) :
    ∫ ω, (∑ i : Fin N₀, ξ i ω
            * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
        * (∑ j : Fin N₀, ξ' j ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω) ∂P = 0 := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  -- partition facts.
  have hpnn : ∀ k : Fin (N₀ + 1), 0 ≤ p k := fun k => by
    have := hpmono.monotone (Fin.zero_le k); rwa [hp0] at this
  have hlt : ∀ i : Fin N₀, p i.castSucc < p i.succ := fun i => hpmono Fin.castSucc_lt_succ
  -- measurability + finiteness of the boxes.
  have hRm : ∀ i, MeasurableSet (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) :=
    fun i => measurableSet_Ioc.prod (hAm i)
  have hR'm : ∀ i, MeasurableSet (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A' i) :=
    fun i => measurableSet_Ioc.prod (hA'm i)
  have hRf : ∀ i, LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ≠ ⊤ :=
    fun i => referenceIntensity_Ioc_prod_ne_top (hAf i)
  have hR'f : ∀ i, LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A' i) ≠ ⊤ :=
    fun i => referenceIntensity_Ioc_prod_ne_top (hA'f i)
  -- integrability of each cross product term.
  have hint : ∀ i j : Fin N₀, MeasureTheory.Integrable
      (fun ω => (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
        * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω)) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := hξb i
    obtain ⟨Mj, hMj⟩ := hξ'b j
    have hcross := compensated_cross_integrable N (hRm i) (hR'm j) (hRf i) (hR'f j)
    have heq : (fun ω => (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
        = (fun ω => (ξ i ω * ξ' j ω)
          * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω)) := by
      funext ω; ring
    rw [heq]
    refine hcross.bdd_mul (c := Mi * Mj) ((hξm i).mul (hξ'm j)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMi ω) (hMj ω) (abs_nonneg _) ((abs_nonneg _).trans (hMi ω))
  -- expand the product of sums into a double sum and integrate term-by-term.
  rw [show (fun ω => (∑ i : Fin N₀, ξ i ω
            * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (∑ j : Fin N₀, ξ' j ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
      = fun ω => ∑ i : Fin N₀, ∑ j : Fin N₀,
          (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω) from
    funext (fun ω => Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _
      (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))]
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  -- reassociate to `g·(Ñ·Ñ)` with `g = ξᵢ·ξ'ⱼ`.
  rw [show (fun ω => (ξ i ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω)
          * (ξ' j ω * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
      = fun ω => (ξ i ω * ξ' j ω)
          * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω
            * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω) from
    funext (fun ω => by ring)]
  rcases lt_trichotomy i j with hij | hij | hij
  · -- i < j: time-ordered (`pᵢ₊₁ ≤ pⱼ`).
    have hbc : p i.succ ≤ p j.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    exact weighted_box_cross_timeordered_zero N (hpnn _) (hlt i) hbc (hlt j)
      (hAm i) (hA'm j) (hA'f j)
      (((h_adapt i).mono (ℱ.mono ((hlt i).le.trans hbc))).mul (h_adapt' j))
  · -- i = j: same interval, disjoint marks.
    subst hij
    obtain ⟨Mi, hMi⟩ := hξb i
    obtain ⟨Mj, hMj⟩ := hξ'b i
    have hbnd : ∀ ω, |ξ i ω * ξ' i ω| ≤ Mi * Mj := fun ω => by
      rw [abs_mul]
      exact mul_le_mul (hMi ω) (hMj ω) (abs_nonneg _) ((abs_nonneg _).trans (hMi ω))
    exact weighted_box_cross_disjoint_zero N (hpnn _) (hlt i)
      (hAm i) (hA'm i) (hAf i) (hA'f i) (hdisj i) ((h_adapt i).mul (h_adapt' i)) hbnd
  · -- j < i: time-ordered the other way (commute the two compensated factors).
    have hbc : p j.succ ≤ p i.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
    rw [show (fun ω => (ξ i ω * ξ' j ω)
            * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω
              * N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω))
        = fun ω => (ξ i ω * ξ' j ω)
            * (N.compensated (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ A' j) ω
              * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ A i) ω) from
      funext (fun ω => by ring)]
    exact weighted_box_cross_timeordered_zero N (hpnn _) (hlt j) hbc (hlt i)
      (hA'm j) (hAm i) (hAf i)
      ((h_adapt i).mul ((h_adapt' j).mono (ℱ.mono ((hlt j).le.trans hbc))))

/-- **Multi-mark step-integral L² isometry (sum form).** For a shared partition `p`,
pairwise-disjoint marks `B k`, and adapted bounded coefficients `ξ i k`,
`E[(∑ₖ ∑ᵢ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = ∑ₖ ∑ᵢ ν̂((pᵢ,pᵢ₊₁]×Bₖ)·E[ξᵢₖ²]`. The `k`-level
expansion: the diagonal `E[Iₖ²]` is the single-mark isometry
(`simpleIntegral_L2_isometry_compensatedPoisson_sumForm`), the cross `E[IₖIₖ']` (`k≠k'`)
vanishes by `crossSum_disjointMark_zero` (disjoint marks). -/
lemma stepIntegral_multimark_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {N₀ K : ℕ} {T : ℝ} (hT : 0 < T)
    (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpleT : p (Fin.last N₀) ≤ T) (hpmono : StrictMono p)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (hBdisj : Pairwise (fun k k' => Disjoint (B k) (B k')))
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ k : Fin K, ∑ i : Fin N₀,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∑ k : Fin K, ∑ i : Fin N₀,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k)).toReal * ∫ ω, (ξ i k ω) ^ 2 ∂P := by
  -- the single-mark predictable for each mark `B k` (shared partition `p`).
  let φ : Fin K → SimplePredictable Ω E ν T := fun k =>
    { N := N₀, partition := p, partition_zero := hp0, partition_le_T := hpleT
      partition_strictMono := hpmono, A := fun _ => B k, A_measurable := fun _ => hBm k
      A_finite := fun _ => hBf k, ξ := fun i => ξ i k, ξ_bounded := fun i => hξb i k
      ξ_measurable := fun i => hξm i k }
  have hI_eq : ∀ k ω, simpleIntegral N (φ k) T ω
      = ∑ i : Fin N₀, ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω := by
    intro k ω; rw [simpleIntegral_eq_sum_fullRect]; rfl
  have hmemLp : ∀ k, MeasureTheory.MemLp (fun ω => simpleIntegral N (φ k) T ω) 2 P :=
    fun k => simpleIntegral_memLp_compensated N hT (φ k) (fun i => h_adapt i k)
  have hII : ∀ k k', MeasureTheory.Integrable
      (fun ω => simpleIntegral N (φ k) T ω * simpleIntegral N (φ k') T ω) P :=
    fun k k' => (hmemLp k).integrable_mul (hmemLp k')
  -- rewrite the integrand and the goal in terms of `simpleIntegral N (φ k) T`.
  have hrw : (fun ω => (∑ k : Fin K, ∑ i : Fin N₀,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2)
      = fun ω => (∑ k : Fin K, simpleIntegral N (φ k) T ω) ^ 2 := by
    funext ω; congr 1; exact Finset.sum_congr rfl (fun k _ => (hI_eq k ω).symm)
  rw [hrw, show (fun ω => (∑ k : Fin K, simpleIntegral N (φ k) T ω) ^ 2)
        = fun ω => ∑ k : Fin K, ∑ k' : Fin K,
            simpleIntegral N (φ k) T ω * simpleIntegral N (φ k') T ω from
      funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun k' _ => hII k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hII k k')]
  rw [Finset.sum_eq_single k]
  · -- diagonal `k' = k`: single-mark isometry.
    rw [show (fun ω => simpleIntegral N (φ k) T ω * simpleIntegral N (φ k) T ω)
          = fun ω => (simpleIntegral N (φ k) T ω) ^ 2 from funext (fun ω => (sq _).symm)]
    exact simpleIntegral_L2_isometry_compensatedPoisson_sumForm N (φ k) (fun i => h_adapt i k)
  · -- off-diagonal `k' ≠ k`: disjoint-mark cross vanishes.
    intro k' _ hk'
    simp_rw [hI_eq]
    exact crossSum_disjointMark_zero N p hp0 hpmono (fun _ => B k) (fun _ => B k')
      (fun _ => hBm k) (fun _ => hBm k') (fun _ => hBf k) (fun _ => hBf k')
      (fun _ => hBdisj (Ne.symm hk')) (fun i => ξ i k) (fun i => ξ i k')
      (fun i => hξb i k) (fun i => hξb i k') (fun i => hξm i k) (fun i => hξm i k')
      (fun i => h_adapt i k) (fun i => h_adapt i k')
  · intro h; exact absurd (Finset.mem_univ k) h

/-- **Mark-sum square at one time interval (overlapping marks).** For a single interval
`(a,b]`, arbitrary marks `B k`, and adapted bounded coeffs `ξ k`,
`E[(∑ₖ ξₖ Ñ((a,b]×Bₖ))²] = ∑ₖ ∑ₖ' ν̂((a,b]×(Bₖ∩Bₖ'))·E[ξₖ·ξₖ']`. Expand the square and
apply the weighted same-time bilinear covariance to each `(k,k')` term. -/
lemma markSum_sq_sametime
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin K → Ω → ℝ) (hξb : ∀ k, ∃ M, ∀ ω, |ξ k ω| ≤ M) (hξm : ∀ k, Measurable (ξ k))
    (hadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq a) (ξ k)) :
    ∫ ω, (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω) ^ 2 ∂P
      = ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ k ω * ξ k' ω ∂P := by
  have hBxm : ∀ k, MeasurableSet (Set.Ioc a b ×ˢ B k) := fun k => measurableSet_Ioc.prod (hBm k)
  have hBxf : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ B k) ≠ ⊤ :=
    fun k => referenceIntensity_Ioc_prod_ne_top (hBf k)
  -- integrability of each cross term.
  have hint : ∀ k k', MeasureTheory.Integrable
      (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω)) P := by
    intro k k'
    obtain ⟨Mk, hMk⟩ := hξb k
    obtain ⟨Mk', hMk'⟩ := hξb k'
    have hcross := compensated_cross_integrable N (hBxm k) (hBxm k') (hBxf k) (hBxf k')
    have heq : (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω))
        = (fun ω => (ξ k ω * ξ k' ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc a b ×ˢ B k') ω)) := funext (fun ω => by ring)
    rw [heq]
    refine hcross.bdd_mul (c := Mk * Mk') ((hξm k).mul (hξm k')).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMk ω) (hMk' ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  rw [show (fun ω => (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω) ^ 2)
      = fun ω => ∑ k : Fin K, ∑ k' : Fin K,
          (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω) from
    funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun k' _ => hint k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hint k k')]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  obtain ⟨Mk, hMk⟩ := hξb k
  obtain ⟨Mk', hMk'⟩ := hξb k'
  have hbnd : ∀ ω, |ξ k ω * ξ k' ω| ≤ Mk * Mk' := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hMk ω) (hMk' ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  have hgadapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq a) (fun ω => ξ k ω * ξ k' ω) :=
    (hadapt k).mul (hadapt k')
  rw [show (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω))
        = fun ω => (ξ k ω * ξ k' ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc a b ×ˢ B k') ω) from funext (fun ω => by ring),
    weighted_box_cross_sametime N ha hab (hBm k) (hBm k') (hBf k) (hBf k') hgadapt hbnd,
    mul_comm]

/-- **Cross of mark-sums over time-ordered intervals vanishes.** For two intervals
`(a,b]`, `(c,d]` with `b ≤ c`, marks `B`, coeffs `ξ` (adapted at `a`) and `ζ` (adapted
at `c`), `E[(∑ₖ ξₖ Ñ((a,b]×Bₖ))·(∑ₗ ζₗ Ñ((c,d]×Bₗ))] = 0`. Each `(k,l)` term vanishes
by `weighted_box_cross_timeordered_zero`. -/
lemma markSum_cross_timeordered
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {a b c d : ℝ} (hc : 0 ≤ c) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ ζ : Fin K → Ω → ℝ)
    (hξb : ∀ k, ∃ M, ∀ ω, |ξ k ω| ≤ M) (hζb : ∀ k, ∃ M, ∀ ω, |ζ k ω| ≤ M)
    (hξm : ∀ k, Measurable (ξ k)) (hζm : ∀ k, Measurable (ζ k))
    (hξadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq a) (ξ k))
    (hζadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq c) (ζ k)) :
    ∫ ω, (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (∑ l : Fin K, ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω) ∂P = 0 := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  have hac : a ≤ c := hab.le.trans hbc
  have hBxm : ∀ k, MeasurableSet (Set.Ioc a b ×ˢ B k) := fun k => measurableSet_Ioc.prod (hBm k)
  have hCxm : ∀ l, MeasurableSet (Set.Ioc c d ×ˢ B l) := fun l => measurableSet_Ioc.prod (hBm l)
  have hBxf : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ B k) ≠ ⊤ :=
    fun k => referenceIntensity_Ioc_prod_ne_top (hBf k)
  have hCxf : ∀ l, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc c d ×ˢ B l) ≠ ⊤ :=
    fun l => referenceIntensity_Ioc_prod_ne_top (hBf l)
  have hint : ∀ k l, MeasureTheory.Integrable
      (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω)) P := by
    intro k l
    obtain ⟨Mk, hMk⟩ := hξb k
    obtain ⟨Ml, hMl⟩ := hζb l
    have hcross := compensated_cross_integrable N (hBxm k) (hCxm l) (hBxf k) (hCxf l)
    have heq : (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
        = (fun ω => (ξ k ω * ζ l ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc c d ×ˢ B l) ω)) := funext (fun ω => by ring)
    rw [heq]
    refine hcross.bdd_mul (c := Mk * Ml) ((hξm k).mul (hζm l)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMk ω) (hMl ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  rw [show (fun ω => (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (∑ l : Fin K, ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
      = fun ω => ∑ k : Fin K, ∑ l : Fin K,
          (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω) from
    funext (fun ω => Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun l _ => hint k l))]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun l _ => hint k l)]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have hgadapt : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c) (fun ω => ξ k ω * ζ l ω) :=
    ((hξadapt k).mono (ℱ.mono hac)).mul (hζadapt l)
  rw [show (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
        = fun ω => (ξ k ω * ζ l ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc c d ×ˢ B l) ω) from funext (fun ω => by ring)]
  exact weighted_box_cross_timeordered_zero N hc hab hbc hcd (hBm k) (hBm l) (hBf l) hgadapt

/-- **Overlapping-mark step-integral isometry (sum form).** For a shared partition `p`,
arbitrary marks `B`, adapted bounded coeffs `ξ`,
`E[(∑ᵢ ∑ₖ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = ∑ᵢ ∑ₖ ∑ₖ' ν̂((pᵢ,pᵢ₊₁]×(Bₖ∩Bₖ'))·E[ξᵢₖ·ξᵢₖ']`.
The `i`-level expansion: diagonal `E[markSumᵢ²]` by `markSum_sq_sametime`, off-diagonal
(time-ordered) by `markSum_cross_timeordered`. **No disjointness on the marks.** -/
lemma markSumProcess_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Poisson.naturalFiltration N).seq (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ i : Fin N₀, ∑ k : Fin K,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∑ i : Fin N₀, ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ i k ω * ξ i k' ω ∂P := by
  set ℱ := LevyStochCalc.Poisson.naturalFiltration N with hℱ
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hlt : ∀ i : Fin N₀, p i.castSucc < p i.succ := fun i => hpmono Fin.castSucc_lt_succ
  -- mark-sum at time-piece `i`.
  set S : Fin N₀ → Ω → ℝ := fun i ω =>
    ∑ k : Fin K, ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω with hSdef
  -- integrability of `Sᵢ · Sᵢ'` (finite sum of integrable cross terms).
  have hSS : ∀ i i', MeasureTheory.Integrable (fun ω => S i ω * S i' ω) P := by
    intro i i'
    have hbox : ∀ (j : Fin N₀) (k : Fin K),
        MeasurableSet (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ B k) :=
      fun j k => measurableSet_Ioc.prod (hBm k)
    have hboxf : ∀ (j : Fin N₀) (k : Fin K),
        LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ B k) ≠ ⊤ :=
      fun j k => referenceIntensity_Ioc_prod_ne_top (hBf k)
    have hterm : ∀ k l, MeasureTheory.Integrable
        (fun ω => (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
          * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω)) P := by
      intro k l
      obtain ⟨Mk, hMk⟩ := hξb i k
      obtain ⟨Ml, hMl⟩ := hξb i' l
      have hcross := compensated_cross_integrable N (hbox i k) (hbox i' l)
        (hboxf i k) (hboxf i' l)
      rw [show (fun ω => (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
            * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω))
          = (fun ω => (ξ i k ω * ξ i' l ω)
            * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω
              * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω))
          from funext (fun ω => by ring)]
      refine hcross.bdd_mul (c := Mk * Ml) ((hξm i k).mul (hξm i' l)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hMk ω) (hMl ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
    rw [show (fun ω => S i ω * S i' ω)
        = fun ω => ∑ k : Fin K, ∑ l : Fin K,
            (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
            * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω) from
      funext (fun ω => by rw [hSdef]; exact Finset.sum_mul_sum _ _ _ _)]
    exact MeasureTheory.integrable_finsetSum _
      (fun k _ => MeasureTheory.integrable_finsetSum _ (fun l _ => hterm k l))
  -- expand `(∑ᵢ Sᵢ)²` and integrate.
  rw [show (fun ω => (∑ i : Fin N₀, ∑ k : Fin K,
          ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2)
      = fun ω => ∑ i : Fin N₀, ∑ i' : Fin N₀, S i ω * S i' ω from
    funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun i' _ => hSS i i'))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun i' _ => hSS i i'), Finset.sum_eq_single i]
  · -- diagonal `i' = i`: `∫ Sᵢ² = markSum_sq_sametime`.
    rw [show (fun ω => S i ω * S i ω) = fun ω => (S i ω) ^ 2 from funext (fun ω => (sq _).symm)]
    exact markSum_sq_sametime N (hpnn _) (hlt i) B hBm hBf (fun k => ξ i k)
      (fun k => hξb i k) (fun k => hξm i k) (fun k => h_adapt i k)
  · -- off-diagonal `i' ≠ i`: time-ordered, vanishes.
    intro i' _ hi'
    rcases lt_trichotomy i i' with hlt' | hlt' | hlt'
    · have hbc : p i.succ ≤ p i'.castSucc :=
        hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt')
      exact markSum_cross_timeordered N (hpnn _) (hlt i) hbc (hlt i') B hBm hBf
        (fun k => ξ i k) (fun k => ξ i' k) (fun k => hξb i k) (fun k => hξb i' k)
        (fun k => hξm i k) (fun k => hξm i' k) (fun k => h_adapt i k) (fun k => h_adapt i' k)
    · exact absurd hlt' hi'.symm
    · have hbc : p i'.succ ≤ p i.castSucc :=
        hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt')
      rw [show (fun ω => S i ω * S i' ω) = fun ω => S i' ω * S i ω from funext (fun ω => by ring)]
      exact markSum_cross_timeordered N (hpnn _) (hlt i') hbc (hlt i) B hBm hBf
        (fun k => ξ i' k) (fun k => ξ i k) (fun k => hξb i' k) (fun k => hξb i k)
        (fun k => hξm i' k) (fun k => hξm i k) (fun k => h_adapt i' k) (fun k => h_adapt i k)
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Reference-intensity of a time-mark box factorises.** For `0 ≤ a`,
`ν̂((a,b]×A) = ofReal(b−a)·ν(A)` (`referenceIntensity = (volume.restrict (Ici 0)).prod ν`
and `(a,b] ⊆ [0,∞)`). -/
lemma referenceIntensity_Ioc_prod_eq
    {ν : Measure E} [SigmaFinite ν] {a b : ℝ} (ha : 0 ≤ a) {A : Set E} :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)
      = ENNReal.ofReal (b - a) * ν A := by
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left
      (show Set.Ioc a b ⊆ Set.Ici 0 from fun x hx => ha.trans hx.1.le), Real.volume_Ioc]

/-- **Mark-space `L²` of a finite mark-simple function.** For arbitrary marks `B k`
(finite `ν`) and reals `c k`,
`∫_E (∑ₖ cₖ·𝟙_{Bₖ}(e))² dν = ∑ₖ ∑ₖ' cₖ·cₖ'·ν(Bₖ∩Bₖ')`. The mark-direction analogue of
`markSum_sq_sametime`; underlies the Tonelli bridge from the isometry sum-form to the
integrand `L²` norm. -/
lemma mark_sq_integral
    {ν : Measure E} [SigmaFinite ν] {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤) (c : Fin K → ℝ) :
    ∫ e, (∑ k : Fin K, c k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2 ∂ν
      = ∑ k : Fin K, ∑ k' : Fin K, c k * c k' * (ν (B k ∩ B k')).toReal := by
  have hinterm : ∀ k k', MeasurableSet (B k ∩ B k') := fun k k' => (hBm k).inter (hBm k')
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  have hexp : (fun e => (∑ k : Fin K, c k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2)
      = fun e => ∑ k : Fin K, ∑ k' : Fin K,
          (c k * c k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e := by
    funext e
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    by_cases h1 : e ∈ B k <;> by_cases h2 : e ∈ B k' <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, h1, h2]
  have hintg : ∀ k k', MeasureTheory.Integrable
      (fun e => (c k * c k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e) ν :=
    fun k k' => (((MeasureTheory.integrable_indicator_iff (hinterm k k')).mpr
      (MeasureTheory.integrableOn_const (hinterf k k')))).const_mul _
  rw [hexp, MeasureTheory.integral_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ => hintg k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hintg k k')]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_indicator_const (1 : ℝ) (hinterm k k'),
    smul_eq_mul, mul_one, MeasureTheory.measureReal_def]

/-- **Time-direction `L²` of a partition-indicator sum (disjoint intervals).** For a
strictly-increasing partition `p` in `[0,T]` and reals `f i`,
`∫_{[0,T]} (∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·fᵢ)² ds = ∑ᵢ (pᵢ₊₁−pᵢ)·fᵢ²`. The square collapses to the
diagonal (intervals disjoint) and each indicator integrates to the interval length. -/
lemma timeIndicator_sq_integral
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T) (f : Fin N₀ → ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * f i) ^ 2 ∂volume
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc) * (f i) ^ 2 := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hle : ∀ i : Fin N₀, p i.castSucc ≤ p i.succ := fun i => (hpmono Fin.castSucc_lt_succ).le
  have hsubT : ∀ i : Fin N₀, Set.Ioc (p i.castSucc) (p i.succ) ⊆ Set.Icc (0 : ℝ) T := by
    intro i x hx
    exact ⟨(hpnn _).trans hx.1.le, hx.2.trans ((hpmono.monotone (Fin.le_last _)).trans hpleT)⟩
  -- pointwise: the square collapses to the diagonal.
  have hpt : ∀ s, (∑ i : Fin N₀,
        (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * f i) ^ 2
      = ∑ i : Fin N₀,
        (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * (f i) ^ 2 := by
    intro s
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · by_cases hs : s ∈ Set.Ioc (p i.castSucc) (p i.succ) <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs] <;> ring
    · intro i' _ hi'
      have hdisj : Disjoint (Set.Ioc (p i.castSucc) (p i.succ))
          (Set.Ioc (p i'.castSucc) (p i'.succ)) := by
        rw [Set.Ioc_disjoint_Ioc]
        rcases lt_or_gt_of_ne hi' with h | h
        · exact le_trans (min_le_right _ _)
            (le_trans (hpmono.monotone (Fin.succ_le_castSucc_iff.mpr h)) (le_max_left _ _))
        · exact le_trans (min_le_left _ _)
            (le_trans (hpmono.monotone (Fin.succ_le_castSucc_iff.mpr h)) (le_max_right _ _))
      by_cases hs : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
      · have hns : s ∉ Set.Ioc (p i'.castSucc) (p i'.succ) := fun hs' => hdisj.le_bot ⟨hs, hs'⟩
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs, hns]
      · simp [Set.indicator_of_notMem hs]
    · intro h; exact absurd (Finset.mem_univ i) h
  haveI hfin : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hintg : ∀ i : Fin N₀, MeasureTheory.Integrable
      (fun s => (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * (f i) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun i => ((MeasureTheory.integrable_const (1 : ℝ)).indicator measurableSet_Ioc).mul_const _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s _ => hpt s),
    MeasureTheory.integral_finsetSum _ (fun i _ => hintg i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_mul_const, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    MeasureTheory.setIntegral_const, Set.inter_eq_self_of_subset_right (hsubT i),
    Real.volume_real_Ioc_of_le (hle i), smul_eq_mul, mul_one]

/-- **`(s,e)` double integral of `eval²`** (`e`-outer, `s`-inner). For a partition `p`
in `[0,T]`, arbitrary marks `B`, and real coeffs `c`,
`∫_E ∫_{[0,T]} (∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·(∑ₖ cᵢₖ·𝟙_{Bₖ}(e)))² ds dν
  = ∑ᵢ (pᵢ₊₁−pᵢ)·∑ₖ∑ₖ' cᵢₖ·cᵢₖ'·ν(Bₖ∩Bₖ')`. The `s`-integral collapses by
`timeIndicator_sq_integral`, the `e`-integral by `mark_sq_integral`. -/
lemma eval_sq_integral
    {ν : Measure E} [SigmaFinite ν] {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0)
    (hpmono : StrictMono p) {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (c : Fin N₀ → Fin K → ℝ) :
    ∫ e, (∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume) ∂ν
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc)
        * ∑ k : Fin K, ∑ k' : Fin K, c i k * c i k' * (ν (B k ∩ B k')).toReal := by
  have hinterm : ∀ k k', MeasurableSet (B k ∩ B k') := fun k k' => (hBm k).inter (hBm k')
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  -- `s`-integral collapses (per `e`) via `timeIndicator_sq_integral`.
  rw [show (fun e => ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume)
      = fun e => ∑ i : Fin N₀, (p i.succ - p i.castSucc)
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2 from
    funext (fun e => timeIndicator_sq_integral p hp0 hpmono hpleT
      (fun i => ∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e))]
  -- `e`-integral term-by-term, each via `mark_sq_integral`.
  have hint_e : ∀ i : Fin N₀, MeasureTheory.Integrable
      (fun e => (p i.succ - p i.castSucc)
        * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2) ν := by
    intro i
    refine MeasureTheory.Integrable.const_mul ?_ _
    have hpt : (fun e => (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2)
        = fun e => ∑ k : Fin K, ∑ k' : Fin K,
            (c i k * c i k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e := by
      funext e
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
      by_cases h1 : e ∈ B k <;> by_cases h2 : e ∈ B k' <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, h1, h2]
    rw [hpt]
    refine MeasureTheory.integrable_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ => ?_))
    exact ((MeasureTheory.integrable_indicator_iff (hinterm k k')).mpr
      (MeasureTheory.integrableOn_const (hinterf k k'))).const_mul _
  rw [MeasureTheory.integral_finset_sum _ (fun i _ => hint_e i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul, mark_sq_integral B hBm hBf (fun k => c i k)]

/-- **Tonelli bridge: integrand `L²` norm = isometry sum-form.** For a partition `p`
in `[0,T]`, arbitrary marks `B`, adapted bounded coeffs `ξ`,
`E[∫_E ∫_{[0,T]} (∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·(∑ₖ ξᵢₖ·𝟙_{Bₖ}(e)))² ds dν]
  = ∑ᵢ∑ₖ∑ₖ' ν̂((pᵢ,pᵢ₊₁]×(Bₖ∩Bₖ'))·E[ξᵢₖ·ξᵢₖ']`, matching `markSumProcess_isometry`. -/
lemma markSumProcess_L2_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k)) :
    ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P
      = ∑ i : Fin N₀, ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ i k ω * ξ i k' ω ∂P := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hle : ∀ i : Fin N₀, p i.castSucc ≤ p i.succ := fun i => (hpmono Fin.castSucc_lt_succ).le
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  have hξint : ∀ i k, MeasureTheory.Integrable (ξ i k) P := by
    intro i k; obtain ⟨M, hM⟩ := hξb i k
    exact (MeasureTheory.integrable_const M).mono' (hξm i k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hM ω))
  have hξξint : ∀ i k k', MeasureTheory.Integrable (fun ω => ξ i k ω * ξ i k' ω) P := by
    intro i k k'; obtain ⟨M, hM⟩ := hξb i k
    exact (hξint i k').bdd_mul (hξm i k).aestronglyMeasurable
      (c := M) (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hM ω))
  -- factorisation `ν̂((pᵢ,pᵢ₊₁]×(Bₖ∩Bₖ')) = (pᵢ₊₁−pᵢ)·ν(Bₖ∩Bₖ')` in `toReal`.
  have hfact : ∀ (i : Fin N₀) (k k' : Fin K), (LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
      = (p i.succ - p i.castSucc) * (ν (B k ∩ B k')).toReal := by
    intro i k k'
    rw [referenceIntensity_Ioc_prod_eq (hpnn _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith [hle i])]
  -- replace the `ω`-integrand by its `(s,e)` value.
  rw [show (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume ∂ν)
      = fun ω => ∑ i : Fin N₀, (p i.succ - p i.castSucc)
          * ∑ k : Fin K, ∑ k' : Fin K,
            ξ i k ω * ξ i k' ω * (ν (B k ∩ B k')).toReal from
    funext (fun ω => eval_sq_integral p hp0 hpmono hpleT B hBm hBf (fun i k => ξ i k ω))]
  -- pull the finite sums and constants through `E[·]`, then refold via `hfact`.
  rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
    (MeasureTheory.integrable_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ =>
        (hξξint i k k').mul_const _))).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ (fun k _ =>
    MeasureTheory.integrable_finsetSum _ (fun k' _ => (hξξint i k k').mul_const _)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => (hξξint i k k').mul_const _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [MeasureTheory.integral_mul_const, hfact i k k']
  ring

end LevyStochCalc.Poisson.Compensated
