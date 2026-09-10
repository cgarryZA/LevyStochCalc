/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaFiniteActivity
import LevyStochCalc.Ito.JumpSplittingLeftLim

/-!
# The capped jump layer over a prescribed evaluation path

The pathwise sum of the jumps carried by a mark set reads the jump coefficient at a prescribed
path of states; the point values of a jump diffusion and its left limits are the two cases of
interest. Capping the arrival times at the horizon turns that sum into the piecewise translation
carrying the jump path, and the identities describing the capped sum — its value once the arrival
time has passed the horizon, its increment across an arrival time inside the window, its
constancy strictly between consecutive arrival times — are statements about the ordering of the
arrival times and the atomic structure of the random measure, so they hold for every evaluation
path. The telescope's jump sum is accordingly the sum, over the enumerated atoms of the window,
of the increments of the state function taken at the left limits of the jump path and displaced
by the jump coefficient read at the prescribed states.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.jumpSumAt` — the pathwise sum of the jumps carried by a mark set
  over a window, with the jump coefficient evaluated along a prescribed path of states.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt` — those jumps accumulated up to an arrival time
  capped at the horizon.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.jumpSumAt_path`,
  `LevyStochCalc.Ito.JumpFormula.jumpSumAt_leftLimPath` — the point-evaluated and left-limit jump
  sums as the two instances of the prescribed-path jump sum.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_of_le`,
  `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq` — past the horizon the capped jump sum
  is the jump sum over the whole window and no longer moves with the index.
* `LevyStochCalc.Ito.JumpFormula.jumpSumAt_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.jumpSumAt_eq_sum_atomEnum_horizon` — the jump sum over a
  sub-window as the sum of the jump coefficient over the enumerated atoms it contains.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_add_gamma` — between consecutive arrival
  times inside the window the capped jump sum gains the jump coefficient carried by the later
  arrival time and its mark.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSumAt_eq_cappedJumpSumAt`,
  `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumAt_eq` — strictly between consecutive
  capped arrival times the jump path is the continuous part translated by the capped jump sum.
* `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTermAt_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermAt` — the telescope's jump
  sum as the atom sum of the increments of the state function across the jumps.
* `LevyStochCalc.Ito.JumpFormula.add_shift_eq_of_ae_forall_at_of_path`,
  `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumAt_eq_of_path` — the same piecewise
  translation for any path that splits into a continuous part and that jump sum.
* `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTermAt_eq_sum_atomEnum_of_path`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermAt_of_path` — the same
  identification of the telescope's jump sum, the base points being the left limits of the
  translated path and the jump coefficient still being read along the prescribed path of states.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumLeft_eq`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermLeft` — the same two
  conclusions for the jump sum evaluated along the left limits of the path, whose jump
  coefficient is read at the same state as the base point of each increment.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumLeft_eq_of_path`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermLeft_of_path` — those two
  conclusions for a translated path carrying the left-limit jump sum, whose base points are the
  left limits of that path.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumPoint_eq`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermPoint` — the same two
  conclusions for the point-evaluated jump sum.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Defs

/-- The pathwise sum of the jumps carried by the mark set `A` over the window `(0, t]`, with the
jump coefficient evaluated along the path of states `Y`. -/
noncomputable def jumpSumAt (_X : Setting.JumpDiffusion W N coeffs x₀)
    (Y : ℝ → Ω → Fin n → ℝ) (A : Set E) (t : ℝ) (ω : Ω) (i : Fin n) : ℝ :=
  ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (Y q.1 ω) q.2 i ∂(N.N ω)

/-- Along the path itself the prescribed-path jump sum is the point-evaluated jump sum. -/
theorem jumpSumAt_path (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    jumpSumAt X X.X A = JumpSplitting.jumpSum X A := rfl

/-- Along the left limits the prescribed-path jump sum is the left-limit jump sum. -/
theorem jumpSumAt_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    jumpSumAt X (JumpSplitting.leftLimPath X) A = JumpSplitting.jumpSumLeft X A := rfl

/-- The prescribed-path jump sum over the degenerate window vanishes. -/
theorem jumpSumAt_zero (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ)
    (A : Set E) (ω : Ω) (i : Fin n) : jumpSumAt X Y A 0 ω i = 0 := by
  simp [jumpSumAt]

/-- The jumps of a mark set accumulated up to the `k`-th arrival time capped at the horizon, with
the jump coefficient evaluated along the path of states `Y`. -/
noncomputable def cappedJumpSumAt (X : Setting.JumpDiffusion W N coeffs x₀)
    (Y : ℝ → Ω → Fin n → ℝ) (A : Set E) (T : ℝ) (k : ℕ) (ω : Ω) : Fin n → ℝ :=
  jumpSumAt X Y A
    (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω) ω

/-- Along the path itself the prescribed-path capped jump sum is the point-evaluated one. -/
theorem cappedJumpSumAt_path (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    cappedJumpSumAt X X.X A = cappedJumpSum X A := rfl

/-- Along the left limits the prescribed-path capped jump sum reads the jump coefficient at the
left limits of the path. -/
theorem cappedJumpSumAt_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E)
    (T : ℝ) (k : ℕ) (ω : Ω) :
    cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω
      = JumpSplitting.jumpSumLeft X A
          (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω) ω :=
  rfl

end Defs

section GeneralShift

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (A : Set E)

/-- The capped jump sum at the zeroth arrival time vanishes. -/
theorem cappedJumpSumAt_zero {T : ℝ} (hT : 0 ≤ T) (ω : Ω) :
    cappedJumpSumAt X Y A T 0 ω = 0 := by
  funext i
  rw [cappedJumpSumAt,
    LevyStochCalc.Brownian.Ito.clipTime_eq_zero hT (LevyStochCalc.Poisson.jumpTime_zero N A ω),
    jumpSumAt_zero]
  rfl

/-- Past the horizon the capped jump sum is the jump sum over the whole window. -/
theorem cappedJumpSumAt_of_le {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSumAt X Y A T k ω = jumpSumAt X Y A T ω := by
  rw [cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_of_le hk]

/-- Past the horizon the capped jump sum no longer moves with the index. -/
theorem cappedJumpSumAt_succ_eq {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSumAt X Y A T (k + 1) ω = cappedJumpSumAt X Y A T k ω := by
  rw [cappedJumpSumAt_of_le X Y A hk,
    cappedJumpSumAt_of_le X Y A
      (hk.trans (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))]

/-- Past the horizon the telescope's jump term vanishes. -/
theorem jumpTermAt_eq_zero_of_le {T : ℝ} {k : ℕ} {ω : Ω} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ)
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    f (y + cappedJumpSumAt X Y A T (k + 1) ω) - f (y + cappedJumpSumAt X Y A T k ω) = 0 := by
  rw [cappedJumpSumAt_succ_eq X Y A hk, sub_self]

/-- The chain of capped shifts reaches the whole jump sum at any index whose arrival time has
passed the horizon, so a path that splits at the horizon is the translated Itô path there. -/
theorem eq_add_cappedJumpSumAt_of_le {T : ℝ} {m : ℕ} {ω : Ω} {V : ℝ → Ω → Fin n → ℝ}
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω)
    (hsplit : ∀ i : Fin n, X.X T ω i = V T ω i + jumpSumAt X Y A T ω i) (i : Fin n) :
    V T ω i + cappedJumpSumAt X Y A T m ω i = X.X T ω i := by
  rw [cappedJumpSumAt_of_le X Y A hm, hsplit i]

end GeneralShift

section MarkIdentification

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- The jump sum over a sub-window of an enumerated window is the sum of the jump coefficient
over the enumerated atoms whose times lie in the sub-window. -/
theorem jumpSumAt_eq_sum_atomEnum (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    {t : ℝ} (ht : t ≤ T) (i : Fin n) :
    jumpSumAt X Y A t ω i
      = ∑ j : Fin K, if θ j ≤ t then coeffs.γ (θ j) (Y (θ j) ω) (ε j) i else 0 := by
  classical
  have hmt : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hsub : (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ (Set.Ioc (0 : ℝ) t ×ˢ A) = Set.Ioc (0 : ℝ) t ×ˢ A :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)
  have hind := hsum ((Set.Ioc (0 : ℝ) t ×ˢ A).indicator
    fun q : ℝ × E => coeffs.γ q.1 (Y q.1 ω) q.2 i)
  rw [setIntegral_indicator hmt, hsub] at hind
  simp only [jumpSumAt]
  rw [hind]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : θ j ≤ t
  · have hmemj : ((θ j, ε j) : ℝ × E) ∈ Set.Ioc (0 : ℝ) t ×ˢ A :=
      Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨(hmem j).1.1, hj⟩, (hmem j).2⟩
    rw [if_pos hj, Set.indicator_of_mem hmemj]
  · have hnot : ((θ j, ε j) : ℝ × E) ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hc =>
      hj (Set.mem_Ioc.mp (Set.mem_prod.mp hc).1).2
    rw [if_neg hj, Set.indicator_of_notMem hnot]

/-- The jump sum over the whole enumerated window is the sum of the jump coefficient over the
enumerated atoms. -/
theorem jumpSumAt_eq_sum_atomEnum_horizon (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) :
    jumpSumAt X Y A T ω = ∑ j : Fin K, coeffs.γ (θ j) (Y (θ j) ω) (ε j) := by
  classical
  funext i
  rw [Finset.sum_apply, jumpSumAt_eq_sum_atomEnum X Y hA hmem hsum le_rfl i]
  exact Finset.sum_congr rfl fun j _ => if_pos (hmem j).1.2

/-- Between consecutive arrival times inside the window the capped jump sum gains exactly the
jump coefficient carried by the later arrival time and its mark. -/
theorem cappedJumpSumAt_succ_eq_add_gamma (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hθ : Function.Injective θ)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ}
    (hlt : LevyStochCalc.Poisson.jumpTime N A k ω
      < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω)
    (hle : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)) :
    ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
      cappedJumpSumAt X Y A T (k + 1) ω
        = cappedJumpSumAt X Y A T k ω + coeffs.γ (θ j) (Y (θ j) ω) (ε j) := by
  classical
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    (hle.trans_lt (WithTop.coe_lt_top T)).ne
  have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((r : ℝ) : WithTop ℝ) := by
    rw [hr]; exact hlt.le
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (lt_of_le_of_lt hkle (WithTop.coe_lt_top r)).ne
  have hqr : q < r := by
    have := hlt
    rw [← hq, ← hr] at this
    exact_mod_cast this
  have hrT : r ≤ T := by
    have := hle
    rw [← hr] at this
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ q := by
    have := LevyStochCalc.Poisson.coe_zero_le_jumpTime N A k ω
    rw [← hq] at this
    exact_mod_cast this
  have hqT : q ≤ T := le_of_lt (lt_of_lt_of_le hqr hrT)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt hq0 hqr
  have hmemr : r ∈ Set.range θ := by
    rw [hrange]
    exact ⟨k + 1, hr.symm, hr0, hrT⟩
  obtain ⟨j₀, hj₀⟩ := hmemr
  refine ⟨j₀, by rw [← hr, hj₀], ?_⟩
  have hck1 : cappedJumpSumAt X Y A T (k + 1) ω = jumpSumAt X Y A r ω := by
    rw [cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, min_eq_right hrT]
  have hck : cappedJumpSumAt X Y A T k ω = jumpSumAt X Y A q ω := by
    rw [cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm, min_eq_right hqT]
  have hkey : ∀ j : Fin K, j ≠ j₀ → (θ j ≤ r ↔ θ j ≤ q) := by
    intro j hj
    constructor
    · intro hjr
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i, hi, -, -⟩ := hmemj
      rcases le_or_gt i k with hik | hik
      · have := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi, ← hq] at this
        exact_mod_cast this
      · have := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi, ← hr] at this
        have hrj : r ≤ θ j := by exact_mod_cast this
        exact absurd (hθ (hj₀.trans (le_antisymm hrj hjr))).symm hj
    · intro hjq
      exact le_of_lt (lt_of_le_of_lt hjq hqr)
  funext i
  have h1 := jumpSumAt_eq_sum_atomEnum X Y hA hmem hsum hrT i
  have h2 := jumpSumAt_eq_sum_atomEnum X Y hA hmem hsum hqT i
  have hdiff : jumpSumAt X Y A r ω i - jumpSumAt X Y A q ω i
      = coeffs.γ (θ j₀) (Y (θ j₀) ω) (ε j₀) i := by
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine (Finset.sum_eq_single j₀ ?_ ?_).trans ?_
    · intro j _ hj
      by_cases hjr : θ j ≤ r
      · rw [if_pos hjr, if_pos ((hkey j hj).mp hjr), sub_self]
      · rw [if_neg hjr, if_neg (fun hc => hjr ((hkey j hj).mpr hc)), sub_self]
    · intro hj
      exact absurd (Finset.mem_univ j₀) hj
    · rw [if_pos (le_of_eq hj₀), if_neg (by rw [hj₀]; exact not_le.mpr hqr), sub_zero]
  rw [hck1, hck]
  simp only [Pi.add_apply]
  linarith

end MarkIdentification

section CappedChain

/-- Strictly between consecutive members of a chain of times starting at `0`, a path that splits
at all nonnegative times into a continuous part and the jump sum along a prescribed evaluation
path agrees with that continuous part translated by the value of the jump sum on that
interval. -/
theorem add_shift_eq_of_ae_forall_at_of_path {X : Setting.JumpDiffusion W N coeffs x₀}
    {Y Z : ℝ → Ω → Fin n → ℝ} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumAt X Y A t ω i)
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ}
    (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hc : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → ∀ i : Fin n, jumpSumAt X Y A s ω i = c k ω i) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = Z s ω := by
  have hnn : ∀ (k : ℕ) (ω : Ω), ((0 : ℝ) : WithTop ℝ) ≤ σ k ω := by
    intro k ω
    induction k with
    | zero => exact le_of_eq (h0 ω).symm
    | succ k ih => exact ih.trans (hmono k ω)
  filter_upwards [hsplit, hc] with ω hs hcω
  intro k s h1 h2
  have hlt : ((0 : ℝ) : WithTop ℝ) < ((s : ℝ) : WithTop ℝ) := lt_of_le_of_lt (hnn k ω) h1
  have hs0 : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hlt)
  funext i
  simp only [Pi.add_apply]
  rw [hs s hs0 i, hcω k s h1 h2 i]

/-- Strictly between consecutive members of a chain of times starting at `0`, a jump diffusion
that splits at all nonnegative times along a prescribed evaluation path agrees with the
continuous part translated by the value of the jump sum on that interval. -/
theorem add_shift_eq_of_ae_forall_at {X : Setting.JumpDiffusion W N coeffs x₀}
    {Y : ℝ → Ω → Fin n → ℝ} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumAt X Y A t ω i)
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ}
    (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hc : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → ∀ i : Fin n, jumpSumAt X Y A s ω i = c k ω i) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = X.X s ω :=
  add_shift_eq_of_ae_forall_at_of_path hsplit h0 hmono hc

variable {A : Set E}

/-- **The capped jump sum is the jump sum strictly between consecutive capped arrival times.**
No mark of the set arrives strictly between consecutive arrival times, so the accumulated jumps
do not move there. -/
theorem ae_forall_jumpSumAt_eq_cappedJumpSumAt
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      ∀ i : Fin n, jumpSumAt X Y A s ω i = cappedJumpSumAt X Y A T k ω i := by
  classical
  filter_upwards [LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N A hA hAν T]
    with ω hω
  obtain ⟨K, θ, ε, -, hrange, hmem, hsum⟩ := hω
  intro k s h1 h2 i
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
  have hcap : cappedJumpSumAt X Y A T k ω i = jumpSumAt X Y A q ω i := by
    rw [cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
      min_eq_right hqT']
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
  rw [hcap, jumpSumAt_eq_sum_atomEnum X Y hA hmem hsum hsT i,
    jumpSumAt_eq_sum_atomEnum X Y hA hmem hsum hqT' i]
  exact Finset.sum_congr rfl fun j _ => by
    by_cases hj : θ j ≤ s
    · rw [if_pos hj, if_pos ((hkey j).mp hj)]
    · rw [if_neg hj, if_neg (fun hc => hj ((hkey j).mpr hc))]

/-- **The piecewise translation between consecutive capped arrival times.** Strictly between
consecutive capped arrival times a path splitting into a continuous part and the jump sum along
a prescribed path of states is that continuous part translated by the capped jump sum. -/
theorem ae_forall_add_cappedJumpSumAt_eq_of_path
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {X : Setting.JumpDiffusion W N coeffs x₀} {Y Z : ℝ → Ω → Fin n → ℝ}
    {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumAt X Y A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = Z s ω :=
  add_shift_eq_of_ae_forall_at_of_path hsplit
    (cappedJumpTime_zero N A hT) (cappedJumpTime_le_succ N A T)
    (ae_forall_jumpSumAt_eq_cappedJumpSumAt X Y hA hAν T)

/-- **The piecewise translation between consecutive capped arrival times of a jump diffusion.**
Strictly between consecutive capped arrival times the jump path is the continuous part translated
by the capped jump sum evaluated along the prescribed path of states. -/
theorem ae_forall_add_cappedJumpSumAt_eq
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {X : Setting.JumpDiffusion W N coeffs x₀} {Y : ℝ → Ω → Fin n → ℝ}
    {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumAt X Y A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = X.X s ω :=
  ae_forall_add_cappedJumpSumAt_eq_of_path hsplit hA hAν hT

end CappedChain

section JumpSideAssembly

variable (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- Past the horizon the capped jump sum does not move across an index. -/
theorem cappedJumpSumAt_succ_eq_of_horizon_lt (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ} (hk : ((T : ℝ) : WithTop ℝ) < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω) :
    cappedJumpSumAt X Y A T (k + 1) ω = cappedJumpSumAt X Y A T k ω := by
  classical
  have h1 : cappedJumpSumAt X Y A T (k + 1) ω = jumpSumAt X Y A T ω :=
    cappedJumpSumAt_of_le X Y A hk.le
  by_cases hkT : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω
  · rw [h1, cappedJumpSumAt_of_le X Y A hkT]
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
      (lt_trans (not_le.mp hkT) (WithTop.coe_lt_top T)).ne
    have hqT : q < T := by
      have hlt := not_le.mp hkT
      rw [← hq] at hlt
      exact_mod_cast hlt
    have h2 : cappedJumpSumAt X Y A T k ω = jumpSumAt X Y A q ω := by
      rw [cappedJumpSumAt, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm,
        min_eq_right (le_of_lt hqT)]
    rw [h1, h2]
    funext i
    rw [jumpSumAt_eq_sum_atomEnum X Y hA hmem hsum le_rfl i,
      jumpSumAt_eq_sum_atomEnum X Y hA hmem hsum (le_of_lt hqT) i]
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
limit of the translated path `Z`, displaced by the jump coefficient read along the prescribed
path of states, and the indices past the horizon contribute nothing. -/
theorem sum_range_jumpTermAt_eq_sum_atomEnum_of_path (f : (Fin n → ℝ) → ℝ)
    (Z : ℝ → Ω → Fin n → ℝ)
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
      V s ω + cappedJumpSumAt X Y A T k ω = Z s ω)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => Z s ω) (θ j)
            + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
          - f (Function.leftLim (fun s => Z s ω) (θ j))) :=
  sum_range_jumpTerm_eq_sum_atomEnum_of_shift (Y := Z)
    (c := cappedJumpSumAt X Y A T) (jump := fun j => coeffs.γ (θ j) (Y (θ j) ω) (ε j)) f
    hmonoθ (fun j => (hmem j).1) hrange hV hstrict hshift
    (fun _k hk => cappedJumpSumAt_succ_eq_of_horizon_lt X Y hA hmem hsum hrange hk)
    (fun k hk => cappedJumpSumAt_succ_eq_add_gamma X Y hA hmem hsum hmonoθ.injective hrange
      (hstrict k hk) hk)
    hm

/-- **The telescope's jump sum of a jump diffusion is the atom sum of the increments of the state
function across the jumps.** Each in-window index contributes the increment of the state function
at the left limit of the path, displaced by the jump coefficient read along the prescribed path
of states, and the indices past the horizon contribute nothing. -/
theorem sum_range_jumpTermAt_eq_sum_atomEnum (f : (Fin n → ℝ) → ℝ)
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
      V s ω + cappedJumpSumAt X Y A T k ω = X.X s ω)
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m,
        (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T (k + 1) ω)
          - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
              + cappedJumpSumAt X Y A T k ω)))
      = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
            + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
          - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  sum_range_jumpTermAt_eq_sum_atomEnum_of_path X Y f X.X hA hmonoθ hmem hsum hrange hV hstrict
    hshift hm

end JumpSideAssembly

section MarkIdentificationAe

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The telescope's jump sum against the atom enumeration, almost surely.** Almost surely the
window carries a strictly increasing enumeration of its atoms computing every integral over the
window, along which the telescope's jump sum over any range past the horizon is the sum of the
increments of the state function across the jumps, read at the left limits of the translated path
`Z` and displaced by the jump coefficient taken along the prescribed path of states. -/
theorem ae_exists_atomEnum_sum_range_jumpTermAt_of_path (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) (Y Z : ℝ → Ω → Fin n → ℝ) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = Z s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => Z s ω) (θ j)
                + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => Z s ω) (θ j))) := by
  filter_upwards [LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N A hA hAν T,
    LevyStochCalc.Poisson.ae_jumpTime_lt_jumpTime_succ N A hA hAν T, hV, hshift]
    with ω hω hstrict hVω hshiftω
  obtain ⟨K, θ, ε, hmonoθ, hrange, hmem, hsum⟩ := hω
  exact ⟨K, θ, ε, hmem, hsum, fun m hm =>
    sum_range_jumpTermAt_eq_sum_atomEnum_of_path X Y f Z hA hmonoθ hmem hsum hrange hVω hstrict
      hshiftω hm⟩

/-- **The telescope's jump sum of a jump diffusion against the atom enumeration, almost surely.**
Almost surely the window carries a strictly increasing enumeration of its atoms computing every
integral over the window, along which the telescope's jump sum over any range past the horizon is
the sum of the increments of the state function across the jumps, read at the left limits of the
path and displaced by the jump coefficient taken along the prescribed path of states. -/
theorem ae_exists_atomEnum_sum_range_jumpTermAt (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) (Y : ℝ → Ω → Fin n → ℝ) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X Y A T k ω = X.X s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X Y A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
                + coeffs.γ (θ j) (Y (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt_of_path f X Y X.X hA hAν T hV hshift

end MarkIdentificationAe

section Instances

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **The piecewise translation between consecutive capped arrival times, along the left
limits.** Strictly between consecutive capped arrival times a path splitting into a continuous
part and the left-limit jump sum is that continuous part translated by the capped left-limit
jump sum. -/
theorem ae_forall_add_cappedJumpSumLeft_eq
    {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + JumpSplitting.jumpSumLeft X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = X.X s ω :=
  ae_forall_add_cappedJumpSumAt_eq (Y := JumpSplitting.leftLimPath X) hsplit hA hAν hT

/-- **The piecewise translation between consecutive capped arrival times of a translated path
carrying the left-limit jump sum.** Strictly between consecutive capped arrival times a path
splitting into a continuous part and the left-limit jump sum is that continuous part translated
by the capped left-limit jump sum. -/
theorem ae_forall_add_cappedJumpSumLeft_eq_of_path
    {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E} {Z V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + JumpSplitting.jumpSumLeft X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = Z s ω :=
  ae_forall_add_cappedJumpSumAt_eq_of_path (Y := JumpSplitting.leftLimPath X) hsplit hA hAν hT

/-- **The piecewise translation between consecutive capped arrival times, at the point values.**
Strictly between consecutive capped arrival times a path splitting into a continuous part and the
point-evaluated jump sum is that continuous part translated by the capped jump sum. -/
theorem ae_forall_add_cappedJumpSumPoint_eq
    {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E} {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + JumpSplitting.jumpSum X A t ω i)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSum X A T k ω = X.X s ω :=
  ae_forall_add_cappedJumpSumAt_eq (Y := X.X) hsplit hA hAν hT

/-- **The telescope's jump sum against the atom enumeration, along the left limits.** The jump
coefficient of each increment is read at the same left limit of the path as the base point of
that increment. -/
theorem ae_exists_atomEnum_sum_range_jumpTermLeft (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = X.X s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => X.X s ω) (θ j)
                + coeffs.γ (θ j) (JumpSplitting.leftLimPath X (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt f X (JumpSplitting.leftLimPath X) hA hAν T hV hshift

/-- **The telescope's jump sum against the atom enumeration for a translated path carrying the
left-limit jump sum.** The base point of each increment is the left limit of the translated path
`Z`, while the jump coefficient is read at the left limits of the jump diffusion `X`. -/
theorem ae_exists_atomEnum_sum_range_jumpTermLeft_of_path (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) (Z : ℝ → Ω → Fin n → ℝ) {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (hV : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ),
      cappedJumpTime N A T k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < cappedJumpTime N A T (k + 1) ω →
      V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω = Z s ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E),
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
        (∑ k ∈ Finset.range m,
            (f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T (k + 1) ω)
              - f (V (LevyStochCalc.Brownian.Ito.clipTime (cappedJumpTime N A T (k + 1)) T ω) ω
                  + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)))
          = ∑ j : Fin K, (f (Function.leftLim (fun s => Z s ω) (θ j)
                + coeffs.γ (θ j) (JumpSplitting.leftLimPath X (θ j) ω) (ε j))
              - f (Function.leftLim (fun s => Z s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt_of_path f X (JumpSplitting.leftLimPath X) Z
    hA hAν T hV hshift

/-- **The telescope's jump sum against the atom enumeration, at the point values.** The jump
coefficient of each increment is read at the point value of the path at the arrival time, while
the base point of that increment is the left limit there. -/
theorem ae_exists_atomEnum_sum_range_jumpTermPoint (f : (Fin n → ℝ) → ℝ)
    (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
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
              - f (Function.leftLim (fun s => X.X s ω) (θ j))) :=
  ae_exists_atomEnum_sum_range_jumpTermAt f X X.X hA hAν T hV hshift

end Instances

end LevyStochCalc.Ito.JumpFormula
