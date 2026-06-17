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

end LevyStochCalc.Poisson.Compensated
