/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Basic

/-!
# Layer 1.5a: Brownian motion construction

A 1-dimensional Brownian motion is a process `W : ℝ → Ω → ℝ` (interpreted on
`t ≥ 0`) with the standard Wiener properties (zero start, Gaussian
independent increments, continuous paths).

The "no Degenne dep" decision (see project plan) means we build this
in-project from Mathlib only. Strategy outlined as named sub-lemmas below.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.2.
* Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Springer 2016, Ch 2.
* User's dissertation, ch02 §"Probability-space prerequisites" at
  `D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex` lines 13-18.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A *Brownian motion* on the probability space `(Ω, P)`: an `ℝ`-indexed
process (interpreted on `t ≥ 0`) with the three defining properties (zero
start, Gaussian independent increments, continuous paths a.s.). -/
structure BrownianMotion (P : Measure Ω) [IsProbabilityMeasure P] where
  /-- The path map `(t, ω) ↦ W_t(ω)`. -/
  W : ℝ → Ω → ℝ
  /-- For each `t : ℝ`, `ω ↦ W_t(ω)` is measurable. -/
  measurable_eval : ∀ t : ℝ, Measurable (W t)
  /-- The path map is jointly measurable in `(t, ω)`. Required for the
  L²-Itô integral against `W` (Karatzas-Shreve §3.2 implicitly assumes
  this; L10 fix 2026-05-22 per red-team P04). The Wiener-measure construction
  delivers this directly via the projective limit's product σ-algebra. -/
  joint_measurable : Measurable (Function.uncurry W)
  /-- `W₀ = 0` almost surely under `P`. -/
  initial_zero : ∀ᵐ ω ∂P, W 0 ω = 0
  /-- For `0 ≤ s < t`, the law of the increment `W_t − W_s` is `𝒩(0, t − s)`. -/
  increment_gaussian :
    ∀ {s t : ℝ} (_hs : 0 ≤ s) (hst : s < t),
      P.map (fun ω => W t ω - W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩
  /-- For any `0 ≤ u ≤ s < t`, the past value `W_u` is independent (under `P`)
  of the increment `W_t − W_s`. -/
  increment_independent :
    ∀ {u s t : ℝ}, 0 ≤ u → u ≤ s → s < t →
      ProbabilityTheory.IndepFun (W u) (fun ω => W t ω - W s ω) P
  /-- Almost surely, `t ↦ W_t(ω)` is continuous on `[0, ∞)`. -/
  continuous_paths : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => W t ω)
  /-- For `s < 0`, the structure extends `W` trivially: `W_s = 0` almost surely.
  This is a convention that makes the natural filtration well-defined for all
  real `s` and lets `(W_s)_{s ≥ 0}` be viewed as an `ℝ`-indexed process. -/
  negative_zero : ∀ s : ℝ, s < 0 → ∀ᵐ ω ∂P, W s ω = 0
  /-- **σ-algebra-level joint independence of past and future increment.** For
  `0 ≤ s < t`, the σ-algebra `⨆ u ≤ s, σ(W_u)` (which is the natural filtration
  at time `s`) is independent of `σ(W_t − W_s)`. This is strictly stronger
  than the pairwise `increment_independent` and is needed to apply
  `MeasureTheory.condExp_indep_eq` to derive the conditional-expectation
  identities `𝔼[W_t − W_s | ℱ_s] = 0` and `𝔼[(W_t − W_s)² | ℱ_s] = t − s`.
  For Brownian motion this follows from joint Gaussianity; we package it as
  a structural hypothesis since the eventual `BrownianMotion.exists` will
  provide it directly via `iIndepFun_pi` on the increment family. -/
  joint_increment_independent :
    ∀ {s t : ℝ}, 0 ≤ s → s < t →
      ProbabilityTheory.Indep
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W j) inferInstance)
        (MeasurableSpace.comap (fun ω => W t ω - W s ω) inferInstance)
        P

/-! ## Sub-lemmas of `BrownianMotion.exists`

The construction proceeds in stages, each as a named lemma. -/

/-- **Measurability of `gaussianReal` in the mean parameter.** The map
`m ↦ gaussianReal m v` is measurable as a function `ℝ → Measure ℝ`.

Proof: rewrite `gaussianReal m v = (gaussianReal 0 v).map (· + m)`. For any
Borel `s ⊆ ℝ`, `(gaussianReal m v) s = (gaussianReal 0 v) ((· + m) ⁻¹' s)
= ∫⁻ x, s.indicator 1 (x + m) ∂(gaussianReal 0 v)`. The integrand is jointly
measurable in `(x, m)`, so the parameter integral is measurable in `m` by
`Measurable.lintegral_prod_left'` (Tonelli). -/
lemma measurable_gaussianReal (v : ℝ≥0) :
    Measurable (fun m : ℝ => ProbabilityTheory.gaussianReal m v) := by
  refine MeasureTheory.Measure.measurable_of_measurable_coe _ ?_
  intro s hs
  have h_eq : ∀ m, (ProbabilityTheory.gaussianReal m v) s
      = (ProbabilityTheory.gaussianReal 0 v) ((· + m) ⁻¹' s) := by
    intro m
    rw [show ProbabilityTheory.gaussianReal m v
        = (ProbabilityTheory.gaussianReal 0 v).map (· + m) from by
      rw [ProbabilityTheory.gaussianReal_map_add_const]; simp]
    exact MeasureTheory.Measure.map_apply (by fun_prop) hs
  rw [show (fun m => (ProbabilityTheory.gaussianReal m v) s)
      = (fun m => (ProbabilityTheory.gaussianReal 0 v) ((· + m) ⁻¹' s)) from
    funext h_eq]
  have h_lint_eq : ∀ m,
      (ProbabilityTheory.gaussianReal 0 v) ((· + m) ⁻¹' s)
        = ∫⁻ x, s.indicator (fun _ => (1 : ENNReal)) (x + m)
            ∂(ProbabilityTheory.gaussianReal 0 v) := by
    intro m
    have h_set : MeasurableSet ((· + m) ⁻¹' s) := measurable_add_const m hs
    rw [show (ProbabilityTheory.gaussianReal 0 v) ((· + m) ⁻¹' s)
        = ∫⁻ x in ((· + m) ⁻¹' s), 1 ∂(ProbabilityTheory.gaussianReal 0 v) from
          (MeasureTheory.setLIntegral_one _).symm]
    rw [← MeasureTheory.lintegral_indicator h_set]
    apply MeasureTheory.lintegral_congr
    intro x
    by_cases h : x + m ∈ s
    · rw [Set.indicator_of_mem (show x ∈ ((· + m) ⁻¹' s) from h),
          Set.indicator_of_mem h]
    · rw [Set.indicator_of_notMem (show x ∉ ((· + m) ⁻¹' s) from h),
          Set.indicator_of_notMem h]
  rw [show (fun m => (ProbabilityTheory.gaussianReal 0 v) ((· + m) ⁻¹' s))
      = (fun m => ∫⁻ x, s.indicator (fun _ => (1 : ENNReal)) (x + m)
          ∂(ProbabilityTheory.gaussianReal 0 v)) from funext h_lint_eq]
  have h_meas : Measurable (fun (xm : ℝ × ℝ) =>
      s.indicator (fun _ => (1 : ENNReal)) (xm.1 + xm.2)) := by
    apply Measurable.indicator measurable_const
    exact (measurable_fst.add measurable_snd) hs
  exact h_meas.lintegral_prod_left' (μ := ProbabilityTheory.gaussianReal 0 v)

/-- **Step 1: Markov kernel for Brownian increments.** `K(x, ·) := gaussianReal x v`,
the Gaussian kernel that increments `x` by a `𝒩(0, v)`-distributed step. -/
noncomputable def brownianKernel (v : ℝ≥0) :
    ProbabilityTheory.Kernel ℝ ℝ where
  toFun x := ProbabilityTheory.gaussianReal x v
  measurable' := measurable_gaussianReal v

-- 2026-05-22 (deleted): two `True`-valued / trivial-witness stub lemmas
-- (`brownian_dyadicTime_exists`, `brownian_extend_to_real`). Both were
-- documentation placeholders for stages of the KC construction; both had
-- no callers; both contributed only vacuous proof-state misrepresentation.
-- The actual Brownian construction is delivered by `BrownianMotion.exists`
-- (Tier 1 cited axiom #1). Removed per red-team finding M1.

/-- **CITED AXIOM: Wiener measure construction.**

There exists a probability space carrying a 1-dimensional Brownian motion.

**Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
Springer 1991, Theorem 2.1.5; Le Gall, J.-F. *Brownian Motion, Martingales and
Stochastic Calculus*, Springer 2016, Definition 2.1 / Definition 2.12 / Corollary 2.11
(correcting the previous "Theorem 2.1" citation — Le Gall 2016 has no "Theorem 2.1";
the existence is stated through the definition + the Wiener-measure construction
in Chapter 2; see red-team finding M13 / P11).

**Standard proof outline**: Apply the Kolmogorov extension theorem (Mathlib:
`MeasureTheory.IsProjectiveLimit`) to the projective family of finite-dimensional
Gaussian distributions on path space `ℝ^[0,∞)`. The resulting measure is
Wiener measure. The coordinate process has Gaussian increments and is continuous
on a co-null set by the Kolmogorov-Chentsov continuity theorem (also CITED AXIOM
in `Brownian.Continuity`).

**Replacement plan**: when Mathlib gains `MeasureTheory.WienerMeasure` or
equivalent, replace this `axiom` with a `theorem` forwarding to it. Tracked
in `tools/cited_axioms.md`. -/
axiom BrownianMotion.exists :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P)

end LevyStochCalc.Brownian
