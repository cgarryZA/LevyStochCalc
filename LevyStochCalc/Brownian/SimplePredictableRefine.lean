import LevyStochCalc.Brownian.Ito

/-!
# SimplePredictable refinement and diff isometry (C0b infrastructure)

This file builds the partition-refinement machinery needed to upgrade
`itoIntegral_brownian` from its provisional constant-function definition
(A3/A4) to the genuine L²-completion via `LinearIsometry.extend`.

## Roadmap

* `SimplePredictable.refine` — lift `H : SimplePredictable Ω T` from its
  partition `π` onto a finer partition `π'`. The user supplies an index
  map `idxMap : Fin M → Fin H.N` saying which old piece each new piece
  belongs to.
* `SimplePredictable.refine_eval` — `(H.refine ...).eval = H.eval`
  pointwise.
* `SimplePredictable.simpleIntegral_refine` — refining preserves
  `simpleIntegral`.
* `SimplePredictable.commonRefinement` — common refinement of two
  `SimplePredictable`s sharing the same final partition point.
* `simpleIntegral_diff_isometry_simple` — the diff isometry on simples.
* `cauchy_of_L2_dense_simple` — Cauchy property of the simple integrals
  for an L²-Cauchy approximating sequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Refine** a simple predictable to a finer partition. Given
`H : SimplePredictable Ω T` (on partition `π`) and a finer partition `π'`
of length `M + 1`, plus an index map `idxMap : Fin M → Fin H.N` and
inclusion proofs that each new piece `(π' j.castSucc, π' j.succ]` is
contained in the `idxMap j`-th old piece
`(H.partition (idxMap j).castSucc, H.partition (idxMap j).succ]`,
return the refined `SimplePredictable` on `π'` whose `ξ` agrees with `H.ξ`
under `idxMap`.

Requires `π'` to end at the same point as `H.partition` (`h_last`); the
common refinement of two `SimplePredictable`s sharing this endpoint
satisfies this naturally. -/
noncomputable def SimplePredictable.refine
    {T : ℝ} (H : SimplePredictable Ω T)
    (M : ℕ) (π' : Fin (M + 1) → ℝ)
    (h_zero : π' 0 = 0)
    (h_last : π' (Fin.last M) = H.partition (Fin.last H.N))
    (h_strictMono : StrictMono π')
    (idxMap : Fin M → Fin H.N)
    (_h_idx_le : ∀ j : Fin M,
      H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (_h_idx_ge : ∀ j : Fin M,
      π' j.succ ≤ H.partition (idxMap j).succ) :
    SimplePredictable Ω T where
  N := M
  partition := π'
  partition_zero := h_zero
  partition_le_T := h_last ▸ H.partition_le_T
  partition_strictMono := h_strictMono
  ξ := fun j ω => H.ξ (idxMap j) ω
  ξ_bounded := fun j => H.ξ_bounded (idxMap j)
  ξ_measurable := fun j => H.ξ_measurable (idxMap j)

/-- **A strictly monotone `Fin (M + 1) → ℝ` partitions its image:**
for any `s` strictly above the start and ≤ the end, there exists an interval
`(π' j.castSucc, π' j.succ]` containing `s`. -/
private lemma strictMono_partition_tiles
    {M : ℕ} {π' : Fin (M + 1) → ℝ} (h_mono : StrictMono π')
    {s : ℝ} (hs_pos : π' 0 < s) (hs_le_last : s ≤ π' (Fin.last M)) :
    ∃ j : Fin M, π' j.castSucc < s ∧ s ≤ π' j.succ := by
  let validSet : Finset (Fin (M + 1)) := Finset.univ.filter (fun k => s ≤ π' k)
  have h_nonempty : validSet.Nonempty :=
    ⟨Fin.last M, by simp [validSet, hs_le_last]⟩
  let k_min : Fin (M + 1) := validSet.min' h_nonempty
  have h_k_min_in : k_min ∈ validSet := validSet.min'_mem h_nonempty
  have h_s_le_pi : s ≤ π' k_min := (Finset.mem_filter.mp h_k_min_in).2
  have h_k_min_pos : 0 < k_min.val := by
    by_contra h_not
    push_neg at h_not
    have h_zero_val : k_min.val = 0 := Nat.le_zero.mp h_not
    have h_eq : k_min = (0 : Fin (M + 1)) := Fin.ext (by simp [h_zero_val])
    rw [h_eq] at h_s_le_pi
    exact absurd hs_pos (not_lt.mpr h_s_le_pi)
  have h_M_pos : 0 < M := by
    by_contra h_not
    push_neg at h_not
    interval_cases M
    -- M = 0: Fin (0 + 1) = Fin 1; the only Fin 1 element is 0 (by val).
    have : k_min.val = 0 := Nat.lt_one_iff.mp k_min.isLt
    omega
  have hj_lt : k_min.val - 1 < M := by omega
  let j : Fin M := ⟨k_min.val - 1, hj_lt⟩
  have hj_succ_val : j.succ.val = k_min.val := by
    simp [j, Fin.succ]; omega
  have hj_castSucc_val : j.castSucc.val = k_min.val - 1 := by
    simp [j, Fin.castSucc]
  have hj_succ_eq : (j.succ : Fin (M + 1)) = k_min := Fin.ext hj_succ_val
  have h_castSucc_lt : π' j.castSucc < s := by
    by_contra h_not
    push_neg at h_not
    have h_in : j.castSucc ∈ validSet := by
      simp [validSet, h_not]
    have h_ge : k_min ≤ j.castSucc := validSet.min'_le _ h_in
    have h_castSucc_lt_k : j.castSucc.val < k_min.val := by
      rw [hj_castSucc_val]; omega
    rw [Fin.le_iff_val_le_val] at h_ge
    omega
  refine ⟨j, h_castSucc_lt, ?_⟩
  rw [hj_succ_eq]
  exact h_s_le_pi

/-- **`refine` preserves `eval`.** For any `s ω`, the refined eval equals the
original eval. Requires the inclusion hypotheses (`h_idx_le`, `h_idx_ge`):
each new piece is contained in the corresponding old piece. -/
lemma SimplePredictable.refine_eval
    {T : ℝ} (H : SimplePredictable Ω T)
    (M : ℕ) (π' : Fin (M + 1) → ℝ)
    (h_zero : π' 0 = 0)
    (h_last : π' (Fin.last M) = H.partition (Fin.last H.N))
    (h_strictMono : StrictMono π')
    (idxMap : Fin M → Fin H.N)
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    (s : ℝ) (ω : Ω) :
    (H.refine M π' h_zero h_last h_strictMono idxMap h_idx_le h_idx_ge).eval s ω
      = H.eval s ω := by
  show (∑ j : Fin M, if π' j.castSucc < s ∧ s ≤ π' j.succ
      then H.ξ (idxMap j) ω else 0)
    = ∑ i : Fin H.N, if H.partition i.castSucc < s ∧ s ≤ H.partition i.succ
        then H.ξ i ω else 0
  by_cases h_any_new : ∃ j : Fin M, π' j.castSucc < s ∧ s ≤ π' j.succ
  · -- s is in some new piece j₀; the LHS picks out the j₀-th term.
    obtain ⟨j₀, hj₀⟩ := h_any_new
    have h_unique_j : ∀ k : Fin M, k ≠ j₀ →
        ¬ (π' k.castSucc < s ∧ s ≤ π' k.succ) := by
      intro k hk ⟨hk_lt, hk_le⟩
      rcases lt_trichotomy k j₀ with h | h | h
      · -- k < j₀ ⇒ π' k.succ ≤ π' j₀.castSucc < s, contradicting hk_le.
        have h_succ_le : π' k.succ ≤ π' j₀.castSucc := by
          have h_succ_le_castSucc : k.succ ≤ j₀.castSucc :=
            Fin.succ_le_castSucc_iff.mpr h
          exact h_strictMono.monotone h_succ_le_castSucc
        have : π' k.succ < s := h_succ_le.trans_lt hj₀.1
        exact absurd hk_le (not_le.mpr this)
      · exact hk h
      · -- k > j₀ ⇒ π' j₀.succ ≤ π' k.castSucc < s.
        have h_succ_le : π' j₀.succ ≤ π' k.castSucc := by
          have : j₀.succ ≤ k.castSucc := Fin.succ_le_castSucc_iff.mpr h
          exact h_strictMono.monotone this
        have : s ≤ π' k.castSucc := hj₀.2.trans h_succ_le
        exact absurd this (not_le.mpr hk_lt)
    have h_lhs : (∑ j : Fin M, if π' j.castSucc < s ∧ s ≤ π' j.succ
        then H.ξ (idxMap j) ω else 0) = H.ξ (idxMap j₀) ω := by
      rw [Finset.sum_eq_single j₀]
      · rw [if_pos hj₀]
      · intro k _ hk; rw [if_neg (h_unique_j k hk)]
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    -- s is in old piece (idxMap j₀); RHS picks out the (idxMap j₀)-th term.
    have hs_in_old : H.partition (idxMap j₀).castSucc < s ∧
        s ≤ H.partition (idxMap j₀).succ :=
      ⟨lt_of_le_of_lt (h_idx_le j₀) hj₀.1, hj₀.2.trans (h_idx_ge j₀)⟩
    have h_unique_i : ∀ k : Fin H.N, k ≠ idxMap j₀ →
        ¬ (H.partition k.castSucc < s ∧ s ≤ H.partition k.succ) := by
      intro k hk ⟨hk_lt, hk_le⟩
      rcases lt_trichotomy k (idxMap j₀) with h | h | h
      · have h_succ_le : H.partition k.succ ≤ H.partition (idxMap j₀).castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have : H.partition k.succ < s := h_succ_le.trans_lt hs_in_old.1
        exact absurd hk_le (not_le.mpr this)
      · exact hk h
      · have h_succ_le : H.partition (idxMap j₀).succ ≤ H.partition k.castSucc :=
          H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h)
        have : s ≤ H.partition k.castSucc := hs_in_old.2.trans h_succ_le
        exact absurd this (not_le.mpr hk_lt)
    have h_rhs : (∑ i : Fin H.N, if H.partition i.castSucc < s ∧
        s ≤ H.partition i.succ then H.ξ i ω else 0) = H.ξ (idxMap j₀) ω := by
      rw [Finset.sum_eq_single (idxMap j₀)]
      · rw [if_pos hs_in_old]
      · intro k _ hk; rw [if_neg (h_unique_i k hk)]
      · intro h_not; exact absurd (Finset.mem_univ _) h_not
    rw [h_lhs, h_rhs]
  · -- s not in any new piece.
    have h_lhs_zero : (∑ j : Fin M, if π' j.castSucc < s ∧ s ≤ π' j.succ
        then H.ξ (idxMap j) ω else 0) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [if_neg (fun hjp => h_any_new ⟨j, hjp⟩)]
    -- Use `strictMono_partition_tiles` to derive `s ≤ π' 0` or `s > π' Fin.last`.
    have hs_out : s ≤ π' 0 ∨ π' (Fin.last M) < s := by
      by_contra h_inside
      push_neg at h_inside
      obtain ⟨hs_pos, hs_le_last⟩ := h_inside
      exact h_any_new (strictMono_partition_tiles h_strictMono hs_pos hs_le_last)
    rcases hs_out with hs_le0 | hs_gt_last
    · have h_rhs_zero : (∑ i : Fin H.N, if H.partition i.castSucc < s ∧
          s ≤ H.partition i.succ then H.ξ i ω else 0) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [if_neg]
        intro ⟨h_lt, _⟩
        have : H.partition 0 ≤ H.partition i.castSucc :=
          H.partition_strictMono.monotone (Fin.zero_le _)
        rw [H.partition_zero] at this
        rw [h_zero] at hs_le0
        exact absurd (this.trans_lt h_lt) (not_lt.mpr hs_le0)
      rw [h_lhs_zero, h_rhs_zero]
    · have hs_gt : H.partition (Fin.last H.N) < s := by
        rw [← h_last]; exact hs_gt_last
      have h_rhs_zero : (∑ i : Fin H.N, if H.partition i.castSucc < s ∧
          s ≤ H.partition i.succ then H.ξ i ω else 0) = 0 := by
        refine Finset.sum_eq_zero (fun i _ => ?_)
        rw [if_neg]
        intro ⟨_, h_le⟩
        have : H.partition i.succ ≤ H.partition (Fin.last H.N) :=
          H.partition_strictMono.monotone (Fin.le_last _)
        exact absurd (h_le.trans this) (not_le.mpr hs_gt)
      rw [h_lhs_zero, h_rhs_zero]

end LevyStochCalc.Brownian.Ito
