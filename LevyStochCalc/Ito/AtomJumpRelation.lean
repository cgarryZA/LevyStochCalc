/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSumIdentity
import LevyStochCalc.Ito.JumpSplittingPath

/-!
# The left-limit jump sum as a step function of the arrival times

Over a window of finite intensity a Poisson random measure is a finite sum of Dirac masses
carried by pairwise distinct times, so the integral of a function against it over an initial
segment of the window is the plain sum of the function's values at the atoms whose time has been
reached. Read at the jump coefficient along the left limits of a path, this writes the
left-limit jump sum over the window as a step function of the arrival times.

## Main statements

* `LevyStochCalc.Poisson.setIntegral_Ioc_prod_eq_sum_filter` — the integral over an initial
  segment of the window is the sum over the atoms whose time has been reached.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jumpSumLeftAt_eq_sum` — the left-limit
  jump sum over the window is that step function.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v w

section Restriction

variable {E : Type v} [MeasurableSpace E]

/-- The integral over an initial segment of a window whose integrals against a measure are finite
sums over the window's atoms is the sum over the atoms whose time has been reached. -/
theorem setIntegral_Ioc_prod_eq_sum_filter {μ : Measure (ℝ × E)} {A : Set E}
    (hA : MeasurableSet A) {T : ℝ} {K : ℕ} {θ : Fin K → ℝ} {ε : Fin K → E}
    (hmem : ∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂μ = ∑ j : Fin K, g (θ j, ε j))
    {t : ℝ} (ht : t ≤ T) (g : ℝ × E → ℝ) :
    ∫ p in Set.Ioc (0 : ℝ) t ×ˢ A, g p ∂μ
      = ∑ j ∈ Finset.univ.filter fun j => θ j ≤ t, g (θ j, ε j) := by
  classical
  have hms : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hsub : Set.Ioc (0 : ℝ) t ×ˢ A ⊆ Set.Ioc (0 : ℝ) T ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_right ht) subset_rfl
  have hind : ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A,
      Set.indicator (Set.Ioc (0 : ℝ) t ×ˢ A) g p ∂μ
      = ∫ p in Set.Ioc (0 : ℝ) t ×ˢ A, g p ∂μ := by
    rw [setIntegral_indicator hms, Set.inter_eq_self_of_subset_right hsub]
  rw [← hind, hsum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : θ j ≤ t
  · have hp : ((θ j, ε j) : ℝ × E) ∈ Set.Ioc (0 : ℝ) t ×ˢ A :=
      ⟨⟨(hmem j).1.1, hj⟩, (hmem j).2⟩
    rw [if_pos hj, Set.indicator_of_mem hp]
  · have hp : ((θ j, ε j) : ℝ × E) ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hp => hj hp.1.2
    rw [if_neg hj, Set.indicator_of_notMem hp]

end Restriction

end LevyStochCalc.Poisson

namespace LevyStochCalc.Ito.JumpSplitting

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

/-- **The left-limit jump sum over a window of finite intensity is a step function of the arrival
times.** Almost surely there are finitely many atoms in the window, carried by strictly
increasing times, and at every time of the window the jump sum is the sum of the jump
coefficients at the atoms whose time has been reached, each read at the left limit of the path
there. -/
theorem ae_exists_atomEnum_jumpSumLeftAt_eq_sum
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{u, v, w} P ν)
    (Xp : ℝ → Ω → Fin n → ℝ) (A : Set E) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      ∀ t ≤ T, ∀ i : Fin n,
        jumpSumLeftAt coeffs N Xp A t ω i
          = ∑ j ∈ Finset.univ.filter fun j => θ j ≤ t,
              coeffs.γ (θ j) (leftLimPathAt Xp (θ j) ω) (ε j) i := by
  classical
  filter_upwards [LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N A hA hAν T]
    with ω hω
  obtain ⟨K, θ, ε, hmono, -, hmem, hsum⟩ := hω
  refine ⟨K, θ, ε, hmono, hmem, fun t ht i => ?_⟩
  exact LevyStochCalc.Poisson.setIntegral_Ioc_prod_eq_sum_filter hA hmem hsum ht
    fun q => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i

end LevyStochCalc.Ito.JumpSplitting
