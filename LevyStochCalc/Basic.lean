/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Bare `import Mathlib` retained: Basic.lean serves as the project-wide
-- Mathlib re-export point so every downstream file gets the full namespace
-- via `import LevyStochCalc.Basic`. Narrowing to specific submodule imports
-- (red-team L3/L4) is tracked as a follow-up: each generic L²/measure
-- lemma in this file uses 10+ Mathlib namespaces (eLpNorm, NormedAddCommGroup,
-- Tendsto, ENNReal arithmetic, Filter, ProbabilityTheory, MeasureTheory.Measure,
-- AEStronglyMeasurable, IsProbabilityMeasure, MeasurableSpace), so the
-- specific-import list is long and brittle to Mathlib refactors. Keeping
-- the umbrella import is the pragmatic Mathlib-style choice for a
-- "common imports" module.
import Mathlib

/-!
# LevyStochCalc.Basic

Project-wide imports and milestone-tagging primitive.

A `levyStochCalc_milestone` attribute (analogous to the main dissertation's
`dissertation_axiom`) will be added when the first headline theorem of a
layer is proved CLEAN; until then there is nothing to register.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

/-- **Reverse triangle for `eLpNorm` in `tsub` form.** Standard consequence of
`MeasureTheory.eLpNorm_add_le`: for `1 ≤ p`,
`eLpNorm f p μ - eLpNorm g p μ ≤ eLpNorm (f - g) p μ` (ENNReal truncated). -/
lemma eLpNorm_sub_eLpNorm_le_eLpNorm_sub
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
`ENNReal.Tendsto.sub`); squeeze closes the proof.

This is a generic version, namespace-shared between Brownian and Compensated chains. -/
lemma eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
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

/-- **Bridge: nested-lintegral-of-squared-norm = `eLpNorm²` on (binary) product measure.**

For any `ℝ`-valued measurable `h : α × β → ℝ` and SFinite `μ`, `ν`,
`∫⁻ x, ∫⁻ y, ‖h (x, y)‖₊² ∂ν ∂μ = eLpNorm h 2 (μ.prod ν) ^ (2:ℝ)`.

Tonelli + `eLpNorm_nnreal_pow_eq_lintegral` (instantiated at `p = 2`). -/
lemma lintegral_sq_eq_eLpNorm_sq_on_prod
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure α} {ν : Measure β} [SFinite μ] [SFinite ν]
    (h : α × β → ℝ) (hh : Measurable h) :
    ∫⁻ x, ∫⁻ y, (‖h (x, y)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂μ
      = MeasureTheory.eLpNorm h 2 (μ.prod ν) ^ (2 : ℝ) := by
  set μν := μ.prod ν with hμν
  have h_aem_sq : AEMeasurable
      (fun p : α × β => (‖h p‖₊ : ℝ≥0∞) ^ 2) μν :=
    (hh.enorm.pow_const 2).aemeasurable
  -- Tonelli on the squared integrand.
  have h_Tonelli :
      ∫⁻ x, ∫⁻ y, (‖h (x, y)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂μ
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
  rw [h_pow_lemma]
  refine lintegral_congr (fun p => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl

/-- **Bridge: triple-nested-lintegral-of-squared-norm = `eLpNorm²` on (ternary) product measure.**

For any `ℝ`-valued measurable `h : α × β × γ → ℝ` and SFinite `μ`, `ν`, `η`,
`∫⁻ x, ∫⁻ y, ∫⁻ z, ‖h (x, y, z)‖₊² ∂η ∂ν ∂μ = eLpNorm h 2 (μ.prod (ν.prod η)) ^ (2:ℝ)`.

Iterated Tonelli + `eLpNorm_nnreal_pow_eq_lintegral`. Used by Compensated chain. -/
lemma lintegral_sq_eq_eLpNorm_sq_on_triple_prod
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    {μ : Measure α} {ν : Measure β} {η : Measure γ}
    [SFinite μ] [SFinite ν] [SFinite η]
    (h : α × β × γ → ℝ) (hh : Measurable h) :
    ∫⁻ x, ∫⁻ y, ∫⁻ z, (‖h (x, y, z)‖₊ : ℝ≥0∞) ^ 2 ∂η ∂ν ∂μ
      = MeasureTheory.eLpNorm h 2 (μ.prod (ν.prod η)) ^ (2 : ℝ) := by
  set μνη := μ.prod (ν.prod η) with hμνη
  have h_aem_sq : AEMeasurable
      (fun p : α × β × γ => (‖h p‖₊ : ℝ≥0∞) ^ 2) μνη :=
    (hh.enorm.pow_const 2).aemeasurable
  -- Two iterated Tonellis: outer (μ over ν.prod η), inner (ν.prod η = ν over η).
  have h_outer :
      ∫⁻ p, (‖h p‖₊ : ℝ≥0∞) ^ 2 ∂μνη
        = ∫⁻ x, ∫⁻ q, (‖h (x, q)‖₊ : ℝ≥0∞) ^ 2 ∂(ν.prod η) ∂μ :=
    MeasureTheory.lintegral_prod _ h_aem_sq
  have h_aem_sq_inner : ∀ x : α, AEMeasurable
      (fun q : β × γ => (‖h (x, q)‖₊ : ℝ≥0∞) ^ 2) (ν.prod η) := fun x => by
    have hh_x : Measurable (fun q : β × γ => h (x, q)) := hh.comp (by fun_prop)
    exact (hh_x.enorm.pow_const 2).aemeasurable
  have h_inner_each : ∀ x : α,
      ∫⁻ q, (‖h (x, q)‖₊ : ℝ≥0∞) ^ 2 ∂(ν.prod η)
        = ∫⁻ y, ∫⁻ z, (‖h (x, y, z)‖₊ : ℝ≥0∞) ^ 2 ∂η ∂ν := fun x =>
    MeasureTheory.lintegral_prod _ (h_aem_sq_inner x)
  have h_iterated :
      ∫⁻ p, (‖h p‖₊ : ℝ≥0∞) ^ 2 ∂μνη
        = ∫⁻ x, ∫⁻ y, ∫⁻ z, (‖h (x, y, z)‖₊ : ℝ≥0∞) ^ 2 ∂η ∂ν ∂μ := by
    rw [h_outer]
    refine lintegral_congr (fun x => ?_)
    exact h_inner_each x
  -- Bridge eLpNorm² ↔ ∫⁻ p, (...)^2.
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := μνη) (p := (2 : NNReal)) (f := h)
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  -- ∫⁻ p, ‖h p‖ₑ ^ (2:ℝ) ∂μνη = ∫⁻ x, ∫⁻ y, ∫⁻ z, (‖h (x, y, z)‖₊ : ℝ≥0∞) ^ 2 ∂η ∂ν ∂μ
  have h_pw : (fun p : α × β × γ => (‖h p‖ₑ : ℝ≥0∞) ^ ((2 : ℝ) : ℝ))
              = (fun p : α × β × γ => (‖h p‖₊ : ℝ≥0∞) ^ 2) := by
    funext p
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rfl
  rw [show ((2 : ℝ) : ℝ) = (2 : ℝ) from rfl] at h_pw
  rw [show (∫⁻ (p : α × β × γ), ‖h p‖ₑ ^ ((2 : ℝ) : ℝ) ∂μνη)
        = ∫⁻ p, (‖h p‖₊ : ℝ≥0∞) ^ 2 ∂μνη from by
    refine lintegral_congr (fun p => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rfl]
  exact h_iterated.symm

/-- **General eval-norm-tendsto from diff-norm-tendsto, binary-product (Brownian-shape).**

For any sequence of jointly-measurable `(p ↦ ev_n p.2 p.1)` and jointly-measurable
target `H` such that `∫⁻ x, ∫⁻ y in [0,T], ‖H x y - ev_n y x‖₊² → 0`, we have
`∫⁻ x, ∫⁻ y in [0,T], ‖ev_n y x‖₊² → ∫⁻ x, ∫⁻ y in [0,T], ‖H x y‖₊²`.

Pipeline: bridge to eLpNorm² via Tonelli (`lintegral_sq_eq_eLpNorm_sq_on_prod` after
restriction); square root → reverse triangle continuity → square back → bridge back.

Generic version, namespace-shared between Brownian and Compensated chains. -/
lemma lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian_shape
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [SFinite μ]
    {T : ℝ}
    (H : α → ℝ → ℝ) (h_H_meas : Measurable (Function.uncurry H))
    (ev : ℕ → ℝ → α → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : α × ℝ) => ev n p.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
        (‖H x y - ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
        (‖ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
        (‖H x y‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)) := by
  set μν := μ.prod (volume.restrict (Set.Icc (0 : ℝ) T)) with hμν
  set F : α × ℝ → ℝ := fun p => H p.1 p.2 with hF_def
  set Fn : ℕ → α × ℝ → ℝ := fun n p => ev n p.2 p.1 with hFn_def
  have h_F_meas : Measurable F := h_H_meas
  have h_Fn_meas : ∀ n, Measurable (Fn n) := h_ev_meas
  have h_F_aestrong : MeasureTheory.AEStronglyMeasurable F μν :=
    h_F_meas.stronglyMeasurable.aestronglyMeasurable
  have h_Fn_aestrong : ∀ n, MeasureTheory.AEStronglyMeasurable (Fn n) μν :=
    fun n => (h_Fn_meas n).stronglyMeasurable.aestronglyMeasurable
  have h_diff_meas : ∀ n, Measurable (F - Fn n) := fun n => h_F_meas.sub (h_Fn_meas n)
  -- Bridge each lintegral_sq form to its eLpNorm² counterpart.
  have h_F_bridge : ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
      (‖H x y‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm F 2 μν ^ (2 : ℝ) :=
    lintegral_sq_eq_eLpNorm_sq_on_prod (μ := μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      F h_F_meas
  have h_Fn_bridge : ∀ n, ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
      (‖ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_prod (μ := μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      (Fn n) (h_Fn_meas n)
  have h_diff_bridge : ∀ n, ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
      (‖H x y - ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ
        = MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_prod (μ := μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      (F - Fn n) (h_diff_meas n)
  -- Convert L²-converges (lintegral form) into eLpNorm² → 0.
  have h_eLpNorm_sq_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μν ^ (2 : ℝ))
        = (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
            (‖H x y - ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ) := by
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
  have h_eq_func : (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T,
        (‖ev n y x‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂μ)
      = (fun n => MeasureTheory.eLpNorm (Fn n) 2 μν ^ (2 : ℝ)) := funext h_Fn_bridge
  rw [h_eq_func, h_F_bridge]
  exact h_eLpNorm_sq_Fn_tendsto

/-- **General eval-norm-tendsto from diff-norm-tendsto, ternary-product (Compensated-shape).**

For any sequence of jointly-measurable `(p ↦ ev_n p.2.1 p.2.2 p.1)` and jointly-measurable
target `H` such that `∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖H ω s e - ev_n s e ω‖₊² → 0`, we have
`∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖ev_n s e ω‖₊² → ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖H ω s e‖₊²`.

Same pipeline as the binary-product version, but lifting via the ternary-product
Tonelli bridge `lintegral_sq_eq_eLpNorm_sq_on_triple_prod`. -/
lemma lintegral_sq_eval_tendsto_of_diff_tendsto_zero_compensated_shape
    {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    {μ : Measure α} {η : Measure γ} [SFinite μ] [SFinite η]
    {T : ℝ}
    (H : α → ℝ → γ → ℝ)
    (h_H_meas : Measurable (fun (p : α × ℝ × γ) => H p.1 p.2.1 p.2.2))
    (ev : ℕ → ℝ → γ → α → ℝ)
    (h_ev_meas : ∀ n, Measurable (fun (p : α × ℝ × γ) => ev n p.2.1 p.2.2 p.1))
    (h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖H x y z - ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ)
      Filter.atTop
      (nhds (∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖H x y z‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ)) := by
  set μνη := μ.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod η) with hμνη
  set F : α × ℝ × γ → ℝ := fun p => H p.1 p.2.1 p.2.2 with hF_def
  set Fn : ℕ → α × ℝ × γ → ℝ := fun n p => ev n p.2.1 p.2.2 p.1 with hFn_def
  have h_F_meas : Measurable F := h_H_meas
  have h_Fn_meas : ∀ n, Measurable (Fn n) := h_ev_meas
  have h_F_aestrong : MeasureTheory.AEStronglyMeasurable F μνη :=
    h_F_meas.stronglyMeasurable.aestronglyMeasurable
  have h_Fn_aestrong : ∀ n, MeasureTheory.AEStronglyMeasurable (Fn n) μνη :=
    fun n => (h_Fn_meas n).stronglyMeasurable.aestronglyMeasurable
  have h_diff_meas : ∀ n, Measurable (F - Fn n) := fun n => h_F_meas.sub (h_Fn_meas n)
  -- Triple Tonelli bridge applied to F, Fn n, F - Fn n.
  have h_F_bridge : ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
      (‖H x y z‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ
        = MeasureTheory.eLpNorm F 2 μνη ^ (2 : ℝ) :=
    lintegral_sq_eq_eLpNorm_sq_on_triple_prod
      (μ := μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T)) (η := η)
      F h_F_meas
  have h_Fn_bridge : ∀ n, ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
      (‖ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ
        = MeasureTheory.eLpNorm (Fn n) 2 μνη ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_triple_prod
      (μ := μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T)) (η := η)
      (Fn n) (h_Fn_meas n)
  have h_diff_bridge : ∀ n, ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
      (‖H x y z - ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ
        = MeasureTheory.eLpNorm (F - Fn n) 2 μνη ^ (2 : ℝ) := fun n =>
    lintegral_sq_eq_eLpNorm_sq_on_triple_prod
      (μ := μ) (ν := volume.restrict (Set.Icc (0 : ℝ) T)) (η := η)
      (F - Fn n) (h_diff_meas n)
  -- L²-converges → eLpNorm² → 0.
  have h_eLpNorm_sq_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μνη ^ (2 : ℝ))
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μνη ^ (2 : ℝ))
        = (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
            (‖H x y z - ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ) := by
      funext n
      exact (h_diff_bridge n).symm
    rw [h_eq]
    exact h_L2_diff
  -- Square root.
  have h_eLpNorm_diff_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μνη)
      Filter.atTop (nhds 0) := by
    have h_rpow : (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μνη)
        = (fun n => (MeasureTheory.eLpNorm (F - Fn n) 2 μνη ^ (2 : ℝ)) ^ ((1 / 2 : ℝ))) := by
      funext n
      rw [← ENNReal.rpow_mul, show ((2 : ℝ) * (1 / 2)) = 1 from by norm_num,
          ENNReal.rpow_one]
    rw [h_rpow]
    have h := h_eLpNorm_sq_diff_tendsto.ennrpow_const (1 / 2 : ℝ)
    simpa [ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] using h
  -- Swap diff: eLpNorm (Fn - F) = eLpNorm (F - Fn).
  have h_diff_swap : ∀ n,
      MeasureTheory.eLpNorm (Fn n - F) 2 μνη
        = MeasureTheory.eLpNorm (F - Fn n) 2 μνη := by
    intro n
    have h_neg : Fn n - F = -(F - Fn n) := by ext p; simp [sub_eq_neg_add]
    rw [h_neg, MeasureTheory.eLpNorm_neg]
  have h_eLpNorm_diff_swap_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μνη)
      Filter.atTop (nhds 0) := by
    have h_eq : (fun n => MeasureTheory.eLpNorm (Fn n - F) 2 μνη)
        = (fun n => MeasureTheory.eLpNorm (F - Fn n) 2 μνη) := funext h_diff_swap
    rw [h_eq]
    exact h_eLpNorm_diff_tendsto
  -- Continuity squeeze.
  have h_eLpNorm_Fn_tendsto :=
    eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
      (one_le_two : (1 : ℝ≥0∞) ≤ 2) h_F_aestrong h_Fn_aestrong h_eLpNorm_diff_swap_tendsto
  -- Square back.
  have h_eLpNorm_sq_Fn_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (Fn n) 2 μνη ^ (2 : ℝ))
      Filter.atTop (nhds (MeasureTheory.eLpNorm F 2 μνη ^ (2 : ℝ))) :=
    h_eLpNorm_Fn_tendsto.ennrpow_const 2
  -- Convert back via bridges.
  have h_eq_func : (fun n => ∫⁻ x, ∫⁻ y in Set.Icc (0 : ℝ) T, ∫⁻ z,
        (‖ev n y z x‖₊ : ℝ≥0∞) ^ 2 ∂η ∂volume ∂μ)
      = (fun n => MeasureTheory.eLpNorm (Fn n) 2 μνη ^ (2 : ℝ)) := funext h_Fn_bridge
  rw [h_eq_func, h_F_bridge]
  exact h_eLpNorm_sq_Fn_tendsto

end LevyStochCalc
