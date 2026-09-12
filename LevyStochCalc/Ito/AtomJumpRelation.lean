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
* `LevyStochCalc.Ito.JumpSplitting.tendsto_nhdsLT_sum_filter_le` — the left limit of a step
  function with finitely many steps drops the steps at the point itself.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jumpSumLeftAt_eq_sum` — the left-limit
  jump sum over the window is that step function.
* `LevyStochCalc.Ito.JumpSplitting.ae_exists_atomEnum_jump_eq_gamma` — the increment of a path
  across an arrival time is the jump coefficient at the left limit there.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

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

/-- **The left limit of a step function with finitely many steps.** The sum of the weights whose
step time has been reached converges, from the left of a point, to the sum of the weights whose
step time is strictly below that point. -/
theorem tendsto_nhdsLT_sum_filter_le {K : ℕ} (θ : Fin K → ℝ) (c : Fin K → ℝ) (b : ℝ) :
    Tendsto (fun t => ∑ j ∈ Finset.univ.filter fun j => θ j ≤ t, c j)
      (𝓝[<] b) (𝓝 (∑ j ∈ Finset.univ.filter fun j => θ j < b, c j)) := by
  classical
  obtain ⟨a, hab, hmax⟩ :
      ∃ a : ℝ, a < b ∧ ∀ j ∈ Finset.univ.filter fun j => θ j < b, θ j ≤ a := by
    set S : Finset ℝ := insert (b - 1) ((Finset.univ.filter fun j => θ j < b).image θ) with hS
    have hne : S.Nonempty := ⟨b - 1, Finset.mem_insert_self _ _⟩
    refine ⟨S.max' hne, ?_, fun j hj => Finset.le_max' _ _ ?_⟩
    · rw [Finset.max'_lt_iff]
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy'
      · linarith
      · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hy'
        exact (Finset.mem_filter.mp hk).2
    · exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem θ hj)
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsLT hab] with t ht
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    exact le_trans (hmax j (by simp [hj])) ht.1.le
  · intro hj
    exact lt_of_le_of_lt hj ht.2

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

/-- **The jump of a path across an arrival time.** If a path is, at every nonnegative time, the
sum of a continuous process and the left-limit jump sum over a mark set of finite intensity, then
almost surely its increment across each arrival time in the window is the jump coefficient read
at the left limit there, for the mark carried at that time. -/
theorem ae_exists_atomEnum_jump_eq_gamma
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{u, v, w} P ν)
    (Xp : ℝ → Ω → Fin n → ℝ) (A : Set E) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (V : ℝ → Ω → Fin n → ℝ) (hVc : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Xp t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      ∀ j : Fin K,
        Xp (θ j) ω
          = leftLimPathAt Xp (θ j) ω + coeffs.γ (θ j) (leftLimPathAt Xp (θ j) ω) (ε j) := by
  classical
  filter_upwards [ae_exists_atomEnum_jumpSumLeftAt_eq_sum coeffs N Xp A hA hAν T, hVc, hsplit]
    with ω hstep hVω hsp
  obtain ⟨K, θ, ε, hmono, hmem, hsum⟩ := hstep
  refine ⟨K, θ, ε, hmono, hmem, fun j => ?_⟩
  -- the left limit of the path at the arrival time: the continuous part plus the earlier steps
  have hlim : ∀ i : Fin n, Tendsto (fun t => Xp t ω i) (𝓝[<] (θ j))
      (𝓝 (V (θ j) ω i + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
        coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i)) := by
    intro i
    have hVlim : Tendsto (fun t => V t ω i) (𝓝[<] (θ j)) (𝓝 (V (θ j) ω i)) :=
      (((continuous_apply i).comp hVω).tendsto (θ j)).mono_left nhdsWithin_le_nhds
    have hstepl := tendsto_nhdsLT_sum_filter_le θ
      (fun k => coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i) (θ j)
    refine (hVlim.add hstepl).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (hmem j).1.1] with t ht
    rw [hsp t ht.1.le i, hsum t (le_trans ht.2.le (hmem j).1.2) i]
  have hleft : leftLimPathAt Xp (θ j) ω
      = fun i => V (θ j) ω i + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
          coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i :=
    leftLimPathAt_eq_of_tendsto hlim
  -- the step at the arrival time splits off the earlier ones
  have hsplitj : (Finset.univ.filter fun k => θ k ≤ θ j)
      = insert j (Finset.univ.filter fun k => θ k < θ j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      hmono.le_iff_le, hmono.lt_iff_lt]
    exact le_iff_eq_or_lt
  have hnotmem : j ∉ Finset.univ.filter fun k => θ k < θ j := by simp
  funext i
  have hleft_i : leftLimPathAt Xp (θ j) ω i
      = V (θ j) ω i + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
          coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i := by
    rw [hleft]
  simp only [Pi.add_apply]
  rw [hsp (θ j) (hmem j).1.1.le i, hsum (θ j) (hmem j).1.2 i, hsplitj,
    Finset.sum_insert hnotmem, hleft_i]
  ring

end LevyStochCalc.Ito.JumpSplitting
