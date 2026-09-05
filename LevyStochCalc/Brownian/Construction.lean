/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Kernel.Defs

/-!
# Brownian motion construction

A 1-dimensional Brownian motion is a process `W : ℝ → Ω → ℝ` (interpreted on
`t ≥ 0`) with the standard Wiener properties (zero start, Gaussian
independent increments, continuous paths).

The "no Degenne dep" decision (see project plan) means we build this
in-project from Mathlib only. Strategy outlined as named sub-lemmas below.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.2.
* Le Gall, *Brownian Motion, Martingales, and Stochastic Calculus*, Springer 2016, Ch 2.
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
  this). The Wiener-measure construction delivers this directly via the
  projective limit's product σ-algebra. -/
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

end LevyStochCalc.Brownian
