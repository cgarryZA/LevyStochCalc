/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion

/-!
# The jump side of the finite-activity Itô–Lévy formula

Capping the arrival times of a mark set at the horizon leaves an increasing chain of stopping
times starting at the origin, and strictly between two consecutive capped arrival times the
accumulated jumps are constant, so the jump path is its continuous part translated by them. The
jump sum of the telescope over that chain is therefore the sum, over the strictly monotone
enumeration of the window's atom times, of the increments of the state function across the jumps,
read at the left limits of the path, both for the state coordinates themselves and after
prepending coordinates to them.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedChain

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

/-- The `k`-th arrival time of a mark set capped at the horizon. -/
noncomputable def cappedJumpTime (T : ℝ) (k : ℕ) (ω : Ω) : WithTop ℝ :=
  min (LevyStochCalc.Poisson.jumpTime N A k ω) ((T : ℝ) : WithTop ℝ)

/-- The capped chain starts at the origin. -/
theorem cappedJumpTime_zero {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    cappedJumpTime N A T 0 ω = ((0 : ℝ) : WithTop ℝ) := by
  rw [cappedJumpTime, LevyStochCalc.Poisson.jumpTime_zero, min_eq_left]
  exact_mod_cast hT

/-- The capped chain increases with the index. -/
theorem cappedJumpTime_le_succ (T : ℝ) (k : ℕ) (ω : Ω) :
    cappedJumpTime N A T k ω ≤ cappedJumpTime N A T (k + 1) ω :=
  min_le_min (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω) le_rfl

/-- The capped chain passes the horizon exactly where the arrival times do. -/
theorem le_cappedJumpTime_iff (T : ℝ) (m : ℕ) (ω : Ω) :
    ((T : ℝ) : WithTop ℝ) ≤ cappedJumpTime N A T m ω
      ↔ ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω := by
  simp [cappedJumpTime]

/-- Clipping at the horizon does not distinguish the capped chain from the arrival times. -/
theorem clipTime_cappedJumpTime (T : ℝ) (k : ℕ) (ω : Ω) :
    LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T k) T ω
      = LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω := by
  simp only [LevyStochCalc.Brownian.Ito.clipTime, cappedJumpTime]
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω
  · rw [min_eq_right h, if_pos le_rfl, if_pos h]
  · rw [min_eq_left (le_of_lt (not_le.mp h)), if_neg h]

/-- **The chain data of the capped arrival times.** For a filtration whose time-zero
`σ`-algebra contains the `P`-null sets and a mark set of finite intensity, the arrival times
capped at the horizon are stopping times, they increase with the index, and the zeroth is the
origin. -/
theorem cappedJumpTime_chain_of_complete {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {T : ℝ} (hT : 0 ≤ T) :
    (∀ k : ℕ, MeasureTheory.IsStoppingTime ℱ (cappedJumpTime N A T k))
      ∧ (∀ (k : ℕ) (ω : Ω), cappedJumpTime N A T k ω ≤ cappedJumpTime N A T (k + 1) ω)
      ∧ ∀ ω : Ω, cappedJumpTime N A T 0 ω = ((0 : ℝ) : WithTop ℝ) :=
  ⟨fun k =>
      (LevyStochCalc.Poisson.isStoppingTime_jumpTime_of_complete N A hℱ hA hAν hnull k).min_const T,
    cappedJumpTime_le_succ N A T, cappedJumpTime_zero N A hT⟩

variable {N A}

/-- **The capped jump sum is the jump sum strictly between consecutive capped arrival times.**
No mark of the set arrives strictly between consecutive arrival times, so the accumulated jumps
do not move there. -/
theorem ae_forall_jumpSum_eq_cappedJumpSum
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      ∀ i : Fin n, LevyStochCalc.Ito.JumpSplitting.jumpSum X A s ω i
        = cappedJumpSum X A T k ω i := by
  classical
  filter_upwards [LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N A hA hAν T]
    with ω hω
  obtain ⟨K, θ, ε, -, hrange, hmem, hsum⟩ := hω
  intro k s h1 h2 i
  -- Below the horizon the capped time is the arrival time itself.
  have hkT : LevyStochCalc.Poisson.jumpTime N A k ω < ((T : ℝ) : WithTop ℝ) := by
    by_contra hcon
    have hk : cappedJumpTime N A T k ω = ((T : ℝ) : WithTop ℝ) :=
      min_eq_right (not_lt.mp hcon)
    have hk1 : cappedJumpTime N A T (k + 1) ω = ((T : ℝ) : WithTop ℝ) :=
      min_eq_right ((not_lt.mp hcon).trans
        (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))
    rw [hk] at h1
    rw [hk1] at h2
    exact absurd (h1.trans h2) (lt_irrefl _)
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (lt_trans hkT (WithTop.coe_lt_top T)).ne
  have hqT : q < T := by
    have := hkT
    rw [← hq] at this
    exact_mod_cast this
  have hkeq : cappedJumpTime N A T k ω = ((q : ℝ) : WithTop ℝ) := by
    rw [cappedJumpTime, ← hq, min_eq_left (le_of_lt (by exact_mod_cast hqT))]
  have hqs : q < s := by
    rw [hkeq] at h1
    exact_mod_cast h1
  have hsucc : ((s : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω :=
    lt_of_lt_of_le h2 (min_le_left _ _)
  have hsT : s ≤ T := by
    have := lt_of_lt_of_le h2 (min_le_right _ _)
    exact le_of_lt (by exact_mod_cast this)
  have hqT' : q ≤ T := le_of_lt hqT
  -- The capped jump sum at index `k` is the jump sum at the arrival time.
  have hcap : cappedJumpSum X A T k ω i
      = LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω i := by
    rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
      min_eq_right hqT']
  -- No enumerated atom time lies in the interval.
  have hkey : ∀ j : Fin K, θ j ≤ s ↔ θ j ≤ q := by
    intro j
    constructor
    · intro hjs
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i', hi', -, -⟩ := hmemj
      rcases le_or_gt i' k with hik | hik
      · have := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi', ← hq] at this
        exact_mod_cast this
      · have := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi'] at this
        exact absurd (lt_of_lt_of_le hsucc this) (not_lt.mpr (by exact_mod_cast hjs))
    · intro hjq
      exact le_of_lt (lt_of_le_of_lt hjq hqs)
  rw [hcap, jumpSum_eq_sum_atomEnum X hA hmem hsum hsT i,
    jumpSum_eq_sum_atomEnum X hA hmem hsum hqT' i]
  exact Finset.sum_congr rfl fun j _ => by
    by_cases hj : θ j ≤ s
    · rw [if_pos hj, if_pos ((hkey j).mp hj)]
    · rw [if_neg hj, if_neg (fun hc => hj ((hkey j).mpr hc))]

/-- **The piecewise translation between consecutive capped arrival times.** Strictly between
consecutive capped arrival times the jump path is the continuous part translated by the capped
jump sum. -/
theorem ae_forall_add_cappedJumpSum_eq
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + LevyStochCalc.Ito.JumpSplitting.jumpSum X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω :=
  LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall hsplit
    (cappedJumpTime_zero N A hT) (cappedJumpTime_le_succ N A T)
    (ae_forall_jumpSum_eq_cappedJumpSum X hA hAν T)

end CappedChain

section JumpSideAssembly

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- Past the horizon the capped jump sum does not move across an index. -/
theorem cappedJumpSum_succ_eq_of_horizon_lt (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ} (hk : ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω) :
    cappedJumpSum X A T (k + 1) ω = cappedJumpSum X A T k ω := by
  classical
  have h1 : cappedJumpSum X A T (k + 1) ω
      = LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω := cappedJumpSum_of_le X A hk.le
  by_cases hkT : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω
  · rw [h1, cappedJumpSum_of_le X A hkT]
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
      (lt_trans (not_le.mp hkT) (WithTop.coe_lt_top T)).ne
    have hqT : q < T := by
      have hlt := not_le.mp hkT
      rw [← hq] at hlt
      exact_mod_cast hlt
    have h2 : cappedJumpSum X A T k ω
        = LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω := by
      rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
        min_eq_right (le_of_lt hqT)]
    rw [h1, h2]
    funext i
    rw [jumpSum_eq_sum_atomEnum X hA hmem hsum le_rfl i,
      jumpSum_eq_sum_atomEnum X hA hmem hsum (le_of_lt hqT) i]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hjq : θ j ≤ q := by
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i', hi', -, hjT⟩ := hmemj
      rcases le_or_gt i' k with hik | hik
      · have hle := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi', ← hq] at hle
        exact_mod_cast hle
      · have hge := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi'] at hge
        exact absurd (lt_of_lt_of_le hk hge) (not_lt.mpr (by exact_mod_cast hjT))
    rw [if_pos (hmem j).1.2, if_pos hjq]

/-- **The telescope's jump sum is the atom sum of the increments of the state function across
the jumps.** Each in-window index contributes the increment of the state function at the left
limit of the path, and the indices past the horizon contribute nothing. -/
theorem sum_range_jumpTerm_eq_sum_atomEnum (f : (Fin n → ℝ) → ℝ)
    {V : ℝ → Ω → Fin n → ℝ} {m : ℕ} (hA : MeasurableSet A) (hmonoθ : StrictMono θ)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    (hV : Continuous fun t => V t ω)
    (hstrict : ∀ i : ℕ, LevyStochCalc.Poisson.jumpTime N A (i + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      LevyStochCalc.Poisson.jumpTime N A i ω < LevyStochCalc.Poisson.jumpTime N A (i + 1) ω)
    (hshift : ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
            + coeffs.γ (θ j) (X.X (θ j) ω) (ε j))
          - f (Function.leftLim (fun s => X.X s ω) (θ j))) := by
  classical
  have hrw : (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T k ω)))
      = ∑ k ∈ Finset.range m,
        (if LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) then
          f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSum X A T (k + 1) ω)
            - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                + cappedJumpSum X A T k ω)
          else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)
    · rw [if_pos hp]
    · rw [if_neg hp,
        cappedJumpSum_succ_eq_of_horizon_lt X hA hmem hsum hrange (not_le.mp hp), sub_self]
  rw [hrw]
  refine sum_range_ite_eq_sum_atomEnum_exists hmonoθ (fun j => (hmem j).1) hrange
    (fun i j hij => LevyStochCalc.Poisson.jumpTime_mono N A hij ω)
    (LevyStochCalc.Poisson.jumpTime_zero N A ω) hstrict hm _ _ ?_
  intro k hp
  obtain ⟨j, hj, hinc⟩ := cappedJumpSum_succ_eq_add_gamma X hA hmem hsum hmonoθ.injective
    hrange (hstrict k hp) hp
  refine ⟨j, hj, ?_⟩
  have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((T : ℝ) : WithTop ℝ) :=
    le_of_lt (lt_of_lt_of_le (hstrict k hp) hp)
  have hcap1 : cappedJumpTime N A T (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) := by
    rw [cappedJumpTime, min_eq_left hp, hj]
  have hltcap : cappedJumpTime N A T k ω < cappedJumpTime N A T (k + 1) ω := by
    simp only [cappedJumpTime, min_eq_left hkle, min_eq_left hp]
    exact hstrict k hp
  have hsub : cappedJumpSum X A T (k + 1) ω - cappedJumpSum X A T k ω
      = coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
    rw [hinc]
    abel
  rw [LevyStochCalc.Brownian.Ito.jumpTerm_eq_leftLim_increment f hV hcap1 (hmem j).1.2
    hltcap (fun s h1 h2 => hshift k s h1 h2), hsub]

/-- **The telescope's jump sum in any dimension.** The same identification of the telescope's
jump sum with the atom sum, for an arbitrary translated path whose translation is constant past
the horizon and gains a prescribed vector at each in-window arrival time. -/
theorem sum_range_jumpTerm_eq_sum_atomEnum_of_shift {N' : ℕ} (f : (Fin N' → ℝ) → ℝ)
    {V Y : ℝ → Ω → Fin N' → ℝ} {c : ℕ → Ω → Fin N' → ℝ} {jump : Fin K → Fin N' → ℝ} {m : ℕ}
    (hmonoθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    (hV : Continuous fun t => V t ω)
    (hstrict : ∀ i : ℕ, LevyStochCalc.Poisson.jumpTime N A (i + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      LevyStochCalc.Poisson.jumpTime N A i ω < LevyStochCalc.Poisson.jumpTime N A (i + 1) ω)
    (hshift : ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω → V s ω + c k ω = Y s ω)
    (hczero : ∀ k : ℕ, ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω →
      c (k + 1) ω = c k ω)
    (hcinc : ∀ k : ℕ, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
      ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ)
        ∧ c (k + 1) ω = c k ω + jump j)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => Y s ω) (θ j) + jump j)
          - f (Function.leftLim (fun s => Y s ω) (θ j))) := by
  classical
  have hrw : (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c k ω)))
      = ∑ k ∈ Finset.range m,
        (if LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) then
          f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + c (k + 1) ω)
            - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                + c k ω)
          else 0) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hp : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)
    · rw [if_pos hp]
    · rw [if_neg hp, hczero k (not_le.mp hp), sub_self]
  rw [hrw]
  refine sum_range_ite_eq_sum_atomEnum_exists hmonoθ hmemθ hrange
    (fun i j hij => LevyStochCalc.Poisson.jumpTime_mono N A hij ω)
    (LevyStochCalc.Poisson.jumpTime_zero N A ω) hstrict hm _ _ ?_
  · intro k hp
    obtain ⟨j, hj, hinc⟩ := hcinc k hp
    refine ⟨j, hj, ?_⟩
    have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((T : ℝ) : WithTop ℝ) :=
      le_of_lt (lt_of_lt_of_le (hstrict k hp) hp)
    have hcap1 : cappedJumpTime N A T (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) := by
      rw [cappedJumpTime, min_eq_left hp, hj]
    have hltcap : cappedJumpTime N A T k ω < cappedJumpTime N A T (k + 1) ω := by
      simp only [cappedJumpTime, min_eq_left hkle, min_eq_left hp]
      exact hstrict k hp
    have hsub : c (k + 1) ω - c k ω = jump j := by
      rw [hinc]
      abel
    rw [LevyStochCalc.Brownian.Ito.jumpTerm_eq_leftLim_increment f hV hcap1 (hmemθ j).2
      hltcap (fun s h1 h2 => hshift k s h1 h2), hsub]

end JumpSideAssembly

section MarkIdentificationAe

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- **The atoms of the window carry the increments of the capped jump sum.** Almost surely the
window of finite intensity carries a strictly increasing enumeration of its atoms which computes
every integral over the window, whose values sum to the jump sum over the window, and along
which the capped jump sum gains, between consecutive arrival times inside the window, exactly
the jump coefficient evaluated at the later arrival time and its mark. -/
theorem ae_exists_atomEnum_cappedJumpSum_succ
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω
        = ∑ j : Fin K, coeffs.γ (θ j) (X.X (θ j) ω) (ε j) ∧
      ∀ k : ℕ, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
        ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
          cappedJumpSum X A T (k + 1) ω
            = cappedJumpSum X A T k ω + coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  filter_upwards [LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N A hA hAν T,
    LevyStochCalc.Poisson.ae_jumpTime_lt_jumpTime_succ N A hA hAν T] with ω hω hstrict
  obtain ⟨K, θ, ε, hmono, hrange, hmem, hsum⟩ := hω
  refine ⟨K, θ, ε, hmono, hmem, hsum,
    jumpSum_eq_sum_atomEnum_horizon X hA hmem hsum, fun k hk => ?_⟩
  exact cappedJumpSum_succ_eq_add_gamma X hA hmem hsum hmono.injective hrange
    (hstrict k hk) hk

/-- **The telescope's jump sum against the atom enumeration, almost surely.** Almost surely the
window carries a strictly increasing enumeration of its atoms computing every integral over the
window, along which the telescope's jump sum over any range past the horizon is the sum of the
increments of the state function across the jumps, read at the left limits of the path. -/
theorem ae_exists_atomEnum_sum_range_jumpTerm (f : (Fin n → ℝ) → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSum X A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSum X A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
                + coeffs.γ (θ j) (X.X (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) := by
  filter_upwards [LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N A hA hAν T,
    LevyStochCalc.Poisson.ae_jumpTime_lt_jumpTime_succ N A hA hAν T, hV, hshift]
    with ω hω hstrict hVω hshiftω
  obtain ⟨K, θ, ε, hmonoθ, hrange, hmem, hsum⟩ := hω
  exact ⟨K, θ, ε, hmem, hsum, fun m hm =>
    sum_range_jumpTerm_eq_sum_atomEnum X f hA hmonoθ hmem hsum hrange hVω hstrict hshiftω hm⟩

end MarkIdentificationAe

end LevyStochCalc.Ito.JumpFormula
