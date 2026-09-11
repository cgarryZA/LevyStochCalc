/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.BigJumpDiffusion
import LevyStochCalc.Ito.PicardWindow

/-!
# SDE data from a family of window solutions

A jump diffusion that satisfies the jump-diffusion integral equation on every window `[0, T]`
relative to a filtration `ℱ` carries SDE data whose filtration is that same `ℱ`: the six
admissibility hypotheses are the corresponding fields of any one window solution, and the
integral equation at a nonnegative time `t` is the window equation at `T = t`.

## Main definitions

* `LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn` — the SDE data of a jump diffusion that
  solves the equation on every window relative to a given filtration.

## Main statements

* `LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn_ℱ` — that SDE data has the given filtration.
* `LevyStochCalc.Ito.BigJump.exists_sdeData_of_solvesOn` — a jump diffusion solving the
  equation on every window relative to `ℱ` carries SDE data with filtration `ℱ`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.BigJump

universe u v

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}
variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The SDE data of a jump diffusion that satisfies the integral equation on every window
`[0, T]` relative to the filtration `ℱ`. -/
def SdeData.ofSolvesOn (X : JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X.X s ω i)
    (hsolves : ∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ X.X T) :
    SdeData X where
  ℱ := ℱ
  isBrownian := hℱW
  isPoisson := hℱN
  X_prog := hXa
  σ_meas := (hsolves 0).h_σ_meas
  σ_prog := (hsolves 0).h_σ_progMeas
  σ_sq := (hsolves 0).h_σ_sq
  γ_meas := (hsolves 0).h_γ_meas
  γ_prog := (hsolves 0).h_γ_progMeas
  γ_sq := (hsolves 0).h_γ_sq
  sde := fun t ht => (hsolves t).eqn t ⟨ht, le_rfl⟩

/-- The SDE data assembled from a family of window solutions has the given filtration. -/
@[simp] theorem SdeData.ofSolvesOn_ℱ (X : JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X.X s ω i)
    (hsolves : ∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ X.X T) :
    (SdeData.ofSolvesOn X ℱ hℱW hℱN hXa hsolves).ℱ = ℱ :=
  rfl

/-- A jump diffusion that solves the integral equation on every window relative to `ℱ` carries
SDE data with filtration `ℱ`. -/
theorem exists_sdeData_of_solvesOn (X : JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    (hXa : ∀ i : Fin n, Probability.ProgressivelyMeasurable ℱ fun ω s => X.X s ω i)
    (hsolves : ∀ T : ℝ, LevyStochCalc.Ito.Picard.SolvesOn W N ℱ hℱW hℱN coeffs x₀ X.X T) :
    ∃ S : SdeData X, S.ℱ = ℱ :=
  ⟨SdeData.ofSolvesOn X ℱ hℱW hℱN hXa hsolves, rfl⟩

end LevyStochCalc.Ito.BigJump
