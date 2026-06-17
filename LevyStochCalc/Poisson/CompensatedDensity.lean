/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedMartingale

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
    simp only [ha, hb, dyadicPartition, Fin.val_succ, Fin.coe_castSucc]; push_cast; ring
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
  have hi_castSucc : ((i.castSucc : Fin (2 ^ n + 1)) : ℝ) = (i : ℝ) := by simp [Fin.coe_castSucc]
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

end LevyStochCalc.Poisson.Compensated
