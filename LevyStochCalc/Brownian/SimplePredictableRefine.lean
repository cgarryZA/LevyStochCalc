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
open scoped NNReal ENNReal

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

/-- **Telescoping helper:** `∑ k ∈ range n, (g (k + 1) - g k) = g n - g 0`.
Used in `simpleIntegral_refine` for within-fiber telescoping. -/
private lemma sum_range_telescope_real (n : ℕ) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.range n, (g (k + 1) - g k) = g n - g 0 := by
  induction n with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Shifted real-valued telescoping:**
`∑ k ∈ Finset.Ico a b, (g (k + 1) - g k) = g b - g a` for `a ≤ b`.
Direct corollary of `sum_range_telescope_real` via `Finset.sum_Ico_eq_sum_range`. -/
private lemma sum_Ico_telescope_real (a b : ℕ) (h : a ≤ b) (g : ℕ → ℝ) :
    ∑ k ∈ Finset.Ico a b, (g (k + 1) - g k) = g b - g a := by
  rw [Finset.sum_Ico_eq_sum_range]
  -- ∑ k in range (b - a), (g (a + k + 1) - g (a + k)) = g b - g a
  have h_eq : (∑ k ∈ Finset.range (b - a),
      (g (a + k + 1) - g (a + k)))
      = (fun m => g (a + m)) (b - a) - (fun m => g (a + m)) 0 := by
    have := sum_range_telescope_real (b - a) (fun m => g (a + m))
    simpa [add_assoc] using this
  rw [h_eq]
  simp
  congr 1
  omega

/-- **Identity refinement preserves `simpleIntegral`:** when `M = H.N`,
`π' = H.partition`, and `idxMap = id`, the refined SimplePredictable
is structurally equal to `H`, so the simple integral is trivially
preserved. -/
lemma SimplePredictable.simpleIntegral_refine_id
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω) :
    simpleIntegral W (H.refine H.N H.partition H.partition_zero rfl
      H.partition_strictMono id (fun _ => le_refl _) (fun _ => le_refl _)) T ω
      = simpleIntegral W H T ω := rfl

/-- **Disjoint Ioc partition pieces:** for `i ≠ j` in `Fin H.N`, the
intervals `(H.partition i.castSucc, H.partition i.succ]` and
`(H.partition j.castSucc, H.partition j.succ]` are disjoint. Used by
the upcoming `simpleIntegral_refine` to derive `idxMap j = i` from
the inclusion hypotheses + a witness point. -/
lemma SimplePredictable.partition_Ioc_disjoint_of_ne {T : ℝ}
    (H : SimplePredictable Ω T) {i j : Fin H.N} (h_ne : i ≠ j) :
    Disjoint
      (Set.Ioc (H.partition i.castSucc) (H.partition i.succ))
      (Set.Ioc (H.partition j.castSucc) (H.partition j.succ)) := by
  rcases lt_trichotomy i j with h | h | h
  · exact Set.Ioc_disjoint_Ioc_of_le
      (H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h))
  · exact absurd h h_ne
  · exact (Set.Ioc_disjoint_Ioc_of_le
      (H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr h))).symm

/-- **Inversion: a Nat in `[k_lo.val, k_hi.val)` lifts to a `Fin M`
whose `idxMap` is the target old index `i`.** Specifically, when:
* `π'` refines `H.partition` with `π' k_lo = H.partition i.castSucc`
  and `π' k_hi = H.partition i.succ`,
* `π'` is strictly monotone,
* the inclusion hypotheses `h_idx_le, h_idx_ge` hold,
* `n ∈ [k_lo.val, k_hi.val)` (so the corresponding `Fin M` element
  exists),

then `idxMap ⟨n, _⟩ = i` (the unique old piece containing the new piece).
Used by `simpleIntegral_refine`'s fiber/Ico bijection. -/
lemma SimplePredictable.idxMap_of_mem_Ico
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    {i : Fin H.N} {k_lo k_hi : Fin (M + 1)}
    (hk_lo : π' k_lo = H.partition i.castSucc)
    (hk_hi : π' k_hi = H.partition i.succ)
    {n : ℕ} (h_lt : n < M) (hn_lo : k_lo.val ≤ n) (hn_hi : n < k_hi.val) :
    idxMap ⟨n, h_lt⟩ = i := by
  let j : Fin M := ⟨n, h_lt⟩
  have h_le : H.partition i.castSucc ≤ π' j.castSucc := by
    rw [← hk_lo]
    apply h_strictMono.monotone
    rw [Fin.le_iff_val_le_val]
    show k_lo.val ≤ j.castSucc.val
    have : j.castSucc.val = n := by simp [Fin.castSucc, j]
    rw [this]; exact hn_lo
  have h_ge : π' j.succ ≤ H.partition i.succ := by
    rw [← hk_hi]
    apply h_strictMono.monotone
    rw [Fin.le_iff_val_le_val]
    show j.succ.val ≤ k_hi.val
    have : j.succ.val = n + 1 := by simp [Fin.succ, j]
    rw [this]; omega
  have h_idxMap_le : H.partition (idxMap j).castSucc ≤ π' j.castSucc := h_idx_le j
  have h_idxMap_ge : π' j.succ ≤ H.partition (idxMap j).succ := h_idx_ge j
  by_contra h_ne
  have h_lt_succ : π' j.castSucc < π' j.succ := h_strictMono Fin.castSucc_lt_succ
  let s_test : ℝ := (π' j.castSucc + π' j.succ) / 2
  have h_test_lo : π' j.castSucc < s_test := by
    show π' j.castSucc < (π' j.castSucc + π' j.succ) / 2; linarith
  have h_test_hi : s_test < π' j.succ := by
    show (π' j.castSucc + π' j.succ) / 2 < π' j.succ; linarith
  have h_in_i : s_test ∈ Set.Ioc (H.partition i.castSucc) (H.partition i.succ) :=
    ⟨lt_of_le_of_lt h_le h_test_lo, le_trans h_test_hi.le h_ge⟩
  have h_in_idx : s_test ∈ Set.Ioc (H.partition (idxMap j).castSucc)
      (H.partition (idxMap j).succ) :=
    ⟨lt_of_le_of_lt h_idxMap_le h_test_lo, le_trans h_test_hi.le h_idxMap_ge⟩
  exact Set.disjoint_iff.mp (H.partition_Ioc_disjoint_of_ne (Ne.symm h_ne)) ⟨h_in_i, h_in_idx⟩

/-- **Fiber-to-Ico forward direction:** if `j : Fin M` is in the fiber
`{j | idxMap j = i}` and `π' k_lo = H.partition i.castSucc`,
`π' k_hi = H.partition i.succ`, then `j.val ∈ [k_lo.val, k_hi.val)`.
Used by `simpleIntegral_refine` for the bijection between the fiber
and the Ico. -/
lemma SimplePredictable.val_mem_Ico_of_idxMap_eq
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    {i : Fin H.N} {k_lo k_hi : Fin (M + 1)}
    (hk_lo : π' k_lo = H.partition i.castSucc)
    (hk_hi : π' k_hi = H.partition i.succ)
    {j : Fin M} (hj_eq : idxMap j = i) :
    j.val ∈ Finset.Ico k_lo.val k_hi.val := by
  have h_le : H.partition (idxMap j).castSucc ≤ π' j.castSucc := h_idx_le j
  have h_ge : π' j.succ ≤ H.partition (idxMap j).succ := h_idx_ge j
  rw [hj_eq, ← hk_lo] at h_le
  rw [hj_eq, ← hk_hi] at h_ge
  have h_k_lo_le : k_lo.val ≤ j.castSucc.val := h_strictMono.le_iff_le.mp h_le
  have h_succ_le_k_hi : j.succ.val ≤ k_hi.val := h_strictMono.le_iff_le.mp h_ge
  rw [Finset.mem_Ico]
  refine ⟨?_, ?_⟩
  · simpa [Fin.castSucc] using h_k_lo_le
  · have := h_succ_le_k_hi; simp [Fin.succ] at this; omega

/-- **Per-fiber telescope (W-version):** define
`g : ℕ → ℝ := fun n => W (π' ⟨n, h⟩) ω if h : n < M+1 else 0`. Then
`∑ n ∈ Finset.Ico a b, (g (n+1) - g n) = g b - g a` by
`sum_Ico_telescope_real`. The `simpleIntegral_refine` general proof
sets up this `g`, equates the per-fiber Ico-sum to `g (k_hi) - g (k_lo)`,
then matches `g (k_hi) = W (π' k_hi) ω = W (H.partition i.succ) ω` via
`hk_hi`. -/
lemma SimplePredictable.W_telescope_via_g
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {M : ℕ} (π' : Fin (M + 1) → ℝ) (ω : Ω)
    (a b : ℕ) (hab : a ≤ b) (hb_le : b ≤ M) :
    (∑ n ∈ Finset.Ico a b,
      ((fun n : ℕ => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0) (n + 1)
        - (fun n : ℕ => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0) n))
      = W.W (π' ⟨b, by omega⟩) ω - W.W (π' ⟨a, by omega⟩) ω := by
  rw [sum_Ico_telescope_real a b hab
    (fun n : ℕ => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0)]
  have h_b_lt : b < M + 1 := by omega
  have h_a_lt : a < M + 1 := by omega
  simp only [h_b_lt, h_a_lt, dif_pos]

/-- **Per-fiber telescope assembly:** for `i : Fin H.N`, the sum
`∑ j ∈ filter (idxMap j = i), H.ξ (idxMap j) ω · (W (π' j.succ) ω - W (π' j.castSucc) ω)`
telescopes to `H.ξ i ω · (W (H.partition i.succ) ω - W (H.partition i.castSucc) ω)`,
under the standard refinement hypotheses. -/
lemma SimplePredictable.fiber_sum_telescope
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    {M : ℕ} {π' : Fin (M + 1) → ℝ}
    (h_strictMono : StrictMono π')
    {idxMap : Fin M → Fin H.N}
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    (h_refines : ∀ i : Fin (H.N + 1), ∃ k : Fin (M + 1), π' k = H.partition i)
    (i : Fin H.N) (ω : Ω) :
    (∑ j ∈ (Finset.univ : Finset (Fin M)).filter (fun j => idxMap j = i),
        H.ξ (idxMap j) ω * (W.W (π' j.succ) ω - W.W (π' j.castSucc) ω))
      = H.ξ i ω
          * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω) := by
  obtain ⟨k_lo, hk_lo⟩ := h_refines i.castSucc
  obtain ⟨k_hi, hk_hi⟩ := h_refines i.succ
  have hk_lo_lt_hi : k_lo.val < k_hi.val := by
    have h1 : π' k_lo < π' k_hi := by
      rw [hk_lo, hk_hi]; exact H.partition_strictMono Fin.castSucc_lt_succ
    exact h_strictMono.lt_iff_lt.mp h1
  have hk_hi_le_M : k_hi.val ≤ M := Nat.lt_succ_iff.mp k_hi.isLt
  -- Define the W-valued g function for telescoping.
  set g : ℕ → ℝ := fun n => if h : n < M + 1 then W.W (π' ⟨n, h⟩) ω else 0 with hg_def
  -- Convert the fiber sum to an Ico sum via Finset.sum_bij.
  -- Target: ∑ n ∈ Ico k_lo.val k_hi.val, H.ξ i ω · (g (n+1) - g n).
  have h_bij_eq : (∑ j ∈ (Finset.univ : Finset (Fin M)).filter
      (fun j => idxMap j = i),
      H.ξ (idxMap j) ω * (W.W (π' j.succ) ω - W.W (π' j.castSucc) ω))
      = ∑ n ∈ Finset.Ico k_lo.val k_hi.val, H.ξ i ω * (g (n + 1) - g n) := by
    refine Finset.sum_bij
      (i := fun (j : Fin M) (_ : j ∈ (Finset.univ : Finset (Fin M)).filter
        (fun j => idxMap j = i)) => j.val)
      (fun j hj => H.val_mem_Ico_of_idxMap_eq h_strictMono h_idx_le h_idx_ge
        hk_lo hk_hi (Finset.mem_filter.mp hj).2)
      (fun j₁ _ j₂ _ h => Fin.ext h)
      (fun n hn => by
        rw [Finset.mem_Ico] at hn
        have h_lt : n < M := lt_of_lt_of_le hn.2 hk_hi_le_M
        refine ⟨⟨n, h_lt⟩, ?_, rfl⟩
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        exact H.idxMap_of_mem_Ico h_strictMono h_idx_le h_idx_ge hk_lo hk_hi
          h_lt hn.1 hn.2)
      ?_
    intro j hj
    have hj_eq : idxMap j = i := (Finset.mem_filter.mp hj).2
    have h_lt_jval : j.val < M := j.isLt
    have h_succ_lt : j.val + 1 < M + 1 := by omega
    have h_lt_M1 : j.val < M + 1 := by omega
    have h_succ_eq : j.succ = (⟨j.val + 1, h_succ_lt⟩ : Fin (M + 1)) :=
      Fin.ext (by simp [Fin.succ])
    have h_castSucc_eq : j.castSucc = (⟨j.val, h_lt_M1⟩ : Fin (M + 1)) :=
      Fin.ext (by simp [Fin.castSucc])
    rw [hj_eq, h_succ_eq, h_castSucc_eq]
    -- Goal: H.ξ i ω · (W (π' ⟨j.val + 1, _⟩) ω - W (π' ⟨j.val, _⟩) ω)
    --     = H.ξ i ω · (g (j.val + 1) - g j.val)
    show H.ξ i ω * (W.W (π' ⟨j.val + 1, h_succ_lt⟩) ω
        - W.W (π' ⟨j.val, h_lt_M1⟩) ω)
      = H.ξ i ω * (g (j.val + 1) - g j.val)
    have hg_succ : g (j.val + 1) = W.W (π' ⟨j.val + 1, h_succ_lt⟩) ω := by
      rw [hg_def]; exact dif_pos h_succ_lt
    have hg_val : g j.val = W.W (π' ⟨j.val, h_lt_M1⟩) ω := by
      rw [hg_def]; exact dif_pos h_lt_M1
    rw [hg_succ, hg_val]
  rw [h_bij_eq]
  -- Now: ∑ n ∈ Ico, H.ξ i ω · (g (n+1) - g n)
  -- = H.ξ i ω · ∑ (g (n+1) - g n)
  -- = H.ξ i ω · (W (π' ⟨k_hi.val, _⟩) ω - W (π' ⟨k_lo.val, _⟩) ω)  [W_telescope_via_g]
  -- = H.ξ i ω · (W (H.partition i.succ) ω - W (H.partition i.castSucc) ω)  [hk_hi, hk_lo]
  rw [← Finset.mul_sum]
  rw [SimplePredictable.W_telescope_via_g (Ω := Ω) (P := P) W π' ω k_lo.val k_hi.val
    (le_of_lt hk_lo_lt_hi) hk_hi_le_M]
  congr 2
  · rw [show (⟨k_hi.val, by omega⟩ : Fin (M + 1)) = k_hi from Fin.ext rfl, hk_hi]
  · rw [show (⟨k_lo.val, by omega⟩ : Fin (M + 1)) = k_lo from Fin.ext rfl, hk_lo]

/-- **C0b.3: `refine` preserves `simpleIntegral` (pointwise).** Under
the hypothesis that `π'` refines `H.partition` (every `H.partition i`
is some `π' k`), the simple integral evaluated at time `T` is unchanged
by refining.

Assembly:
* `simpleIntegral_eq_sum` reduces both sides to plain sums (no
  `min ... T` clauses, since `H.partition_le_T`).
* `Finset.sum_fiberwise_of_maps_to` groups the LHS by `idxMap j = i`.
* For each `i`, `fiber_sum_telescope` collapses the fiber sum to
  `H.ξ i ω · (W (H.partition i.succ) ω - W (H.partition i.castSucc) ω)`,
  which is the `i`-th term of the RHS. -/
lemma SimplePredictable.simpleIntegral_refine
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (M : ℕ) (π' : Fin (M + 1) → ℝ)
    (h_zero : π' 0 = 0)
    (h_last : π' (Fin.last M) = H.partition (Fin.last H.N))
    (h_strictMono : StrictMono π')
    (idxMap : Fin M → Fin H.N)
    (h_idx_le : ∀ j : Fin M, H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (h_idx_ge : ∀ j : Fin M, π' j.succ ≤ H.partition (idxMap j).succ)
    (h_refines : ∀ i : Fin (H.N + 1), ∃ k : Fin (M + 1), π' k = H.partition i)
    (ω : Ω) :
    simpleIntegral W (H.refine M π' h_zero h_last h_strictMono idxMap h_idx_le h_idx_ge) T ω
      = simpleIntegral W H T ω := by
  rw [simpleIntegral_eq_sum, simpleIntegral_eq_sum]
  show (∑ j : Fin M, H.ξ (idxMap j) ω
        * (W.W (π' j.succ) ω - W.W (π' j.castSucc) ω))
    = ∑ i : Fin H.N, H.ξ i ω
        * (W.W (H.partition i.succ) ω - W.W (H.partition i.castSucc) ω)
  rw [← Finset.sum_fiberwise_of_maps_to (g := idxMap)
      (fun (j : Fin M) (_ : j ∈ (Finset.univ : Finset (Fin M))) => Finset.mem_univ _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact H.fiber_sum_telescope W h_strictMono h_idx_le h_idx_ge h_refines i ω

/-- **C0b.4-pre1: Merged partition points.** The union of the two
SimplePredictables' partition images, as a `Finset ℝ`. The cardinality
of this Finset will become `M + 1` for the common refinement. -/
noncomputable def SimplePredictable.mergedPartitionPoints
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) : Finset ℝ :=
  (Finset.univ.image H₁.partition) ∪ (Finset.univ.image H₂.partition)

/-- **C0b.4-pre2: `0` is in the merged set.** Both partitions start at
`0` (`partition_zero`), so `0 = H₁.partition 0` is a member. -/
lemma SimplePredictable.zero_mem_mergedPartitionPoints
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    (0 : ℝ) ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, H₁.partition_zero⟩))

/-- **C0b.4-pre3a: every `H₁.partition i` is in the merged set.** -/
lemma SimplePredictable.partition_mem_mergedPartitionPoints_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₁.N + 1)) :
    H₁.partition i ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inl
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- **C0b.4-pre3b: every `H₂.partition i` is in the merged set.** -/
lemma SimplePredictable.partition_mem_mergedPartitionPoints_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₂.N + 1)) :
    H₂.partition i ∈ H₁.mergedPartitionPoints H₂ := by
  rw [SimplePredictable.mergedPartitionPoints]
  exact Finset.mem_union.mpr (Or.inr
    (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩))

/-- **C0b.4-pre4: number of tiles in the common refinement.** Equals
the cardinality of the merged set minus one. -/
noncomputable def SimplePredictable.mergedM
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) : ℕ :=
  (H₁.mergedPartitionPoints H₂).card - 1

/-- **C0b.4-pre5: cardinality vs. `mergedM`.** Since `0` is in the
merged set, the cardinality is at least 1, so
`card = mergedM + 1` (rearranging `mergedM = card - 1`). -/
lemma SimplePredictable.mergedM_card_eq
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    (H₁.mergedPartitionPoints H₂).card = H₁.mergedM H₂ + 1 := by
  have h_pos : 0 < (H₁.mergedPartitionPoints H₂).card :=
    Finset.card_pos.mpr ⟨0, H₁.zero_mem_mergedPartitionPoints H₂⟩
  rw [SimplePredictable.mergedM]
  omega

/-- **C0b.4-pre6: the common-refinement partition function.** The
strictly-monotone enumeration of the merged Finset, with domain
`Fin (mergedM + 1)`. -/
noncomputable def SimplePredictable.mergedπ
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    Fin (H₁.mergedM H₂ + 1) → ℝ :=
  fun k => (H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂) k

/-- **C0b.4-pre7: `mergedπ` is strictly monotone.** Direct from
`orderEmbOfFin` being an order embedding. -/
lemma SimplePredictable.mergedπ_strictMono
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    StrictMono (H₁.mergedπ H₂) :=
  ((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)).strictMono

/-- **C0b.4-pre8: every partition value is non-negative.** Since
`partition 0 = 0` and `partition` is strictly monotone, every later
value dominates `0`. -/
lemma SimplePredictable.partition_nonneg
    {T : ℝ} (H : SimplePredictable Ω T) (i : Fin (H.N + 1)) :
    0 ≤ H.partition i := by
  rw [← H.partition_zero]
  exact H.partition_strictMono.monotone (Fin.zero_le i)

/-- **C0b.4-pre9: every element of the merged set is non-negative.** -/
lemma SimplePredictable.mem_mergedPartitionPoints_nonneg
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) {x : ℝ}
    (hx : x ∈ H₁.mergedPartitionPoints H₂) : 0 ≤ x := by
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]; exact H₁.partition_nonneg i
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]; exact H₂.partition_nonneg i

/-- **C0b.4-pre10: `mergedπ 0 = 0`.** Apply `orderEmbOfFin_zero` to
reduce to `min' = 0`; the latter follows since `0` is in the merged
set and is a lower bound. -/
lemma SimplePredictable.mergedπ_zero
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) :
    H₁.mergedπ H₂ 0 = 0 := by
  unfold SimplePredictable.mergedπ
  have hz : (0 : ℕ) < H₁.mergedM H₂ + 1 := Nat.succ_pos _
  have h_zero_eq : (0 : Fin (H₁.mergedM H₂ + 1)) = ⟨0, hz⟩ := rfl
  rw [h_zero_eq]
  rw [Finset.orderEmbOfFin_zero (H₁.mergedM_card_eq H₂) hz]
  -- Now goal: min' (mergedPartitionPoints) ⋯ = 0
  have h_zero_mem : (0 : ℝ) ∈ H₁.mergedPartitionPoints H₂ :=
    H₁.zero_mem_mergedPartitionPoints H₂
  apply le_antisymm
  · exact Finset.min'_le _ _ h_zero_mem
  · exact H₁.mem_mergedPartitionPoints_nonneg H₂
      (Finset.min'_mem _ _)

/-- **C0b.4-pre11: every element ≤ the (shared) endpoint.** Under
the assumption that both partitions end at the same point. -/
lemma SimplePredictable.mem_mergedPartitionPoints_le_endpoint
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    {x : ℝ} (hx : x ∈ H₁.mergedPartitionPoints H₂) :
    x ≤ H₁.partition (Fin.last H₁.N) := by
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    exact H₁.partition_strictMono.monotone (Fin.le_last i)
  · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
    rw [← hi]
    rw [h_eq]
    exact H₂.partition_strictMono.monotone (Fin.le_last i)

/-- **C0b.4-pre12: `mergedπ` at the last index equals the (shared)
endpoint.** Apply `orderEmbOfFin_last` to reduce to `max' = endpoint`;
the latter follows since the endpoint is in the merged set and is an
upper bound (via `mem_mergedPartitionPoints_le_endpoint`). -/
lemma SimplePredictable.mergedπ_last
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    H₁.mergedπ H₂ (Fin.last (H₁.mergedM H₂)) =
      H₁.partition (Fin.last H₁.N) := by
  unfold SimplePredictable.mergedπ
  have hz : (0 : ℕ) < H₁.mergedM H₂ + 1 := Nat.succ_pos _
  have h_last_eq : (Fin.last (H₁.mergedM H₂) : Fin (H₁.mergedM H₂ + 1))
      = ⟨H₁.mergedM H₂ + 1 - 1, by omega⟩ := by
    apply Fin.ext; simp
  rw [h_last_eq]
  rw [Finset.orderEmbOfFin_last (H₁.mergedM_card_eq H₂) hz]
  -- Goal: max' (mergedPartitionPoints) ⋯ = H₁.partition (Fin.last H₁.N)
  have h_endpt_mem : H₁.partition (Fin.last H₁.N) ∈ H₁.mergedPartitionPoints H₂ :=
    H₁.partition_mem_mergedPartitionPoints_left H₂ (Fin.last H₁.N)
  apply le_antisymm
  · -- max' ≤ endpoint, since endpoint is an upper bound
    apply Finset.max'_le
    intro x hx
    exact H₁.mem_mergedPartitionPoints_le_endpoint H₂ h_eq hx
  · -- endpoint ≤ max', since endpoint is a member
    exact Finset.le_max' _ _ h_endpt_mem

/-- **C0b.4-pre13: every `H₁.partition i` is in the range of `mergedπ`.**
The range of `orderEmbOfFin` is the underlying Finset (via
`Finset.range_orderEmbOfFin`). -/
lemma SimplePredictable.mergedπ_refines_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₁.N + 1)) :
    ∃ k : Fin (H₁.mergedM H₂ + 1), H₁.mergedπ H₂ k = H₁.partition i := by
  unfold SimplePredictable.mergedπ
  have h_in_range : H₁.partition i ∈ Set.range
      ⇑((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast H₁.partition_mem_mergedPartitionPoints_left H₂ i
  exact h_in_range

/-- **C0b.4-pre14: every `H₂.partition i` is in the range of `mergedπ`.** -/
lemma SimplePredictable.mergedπ_refines_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T) (i : Fin (H₂.N + 1)) :
    ∃ k : Fin (H₁.mergedM H₂ + 1), H₁.mergedπ H₂ k = H₂.partition i := by
  unfold SimplePredictable.mergedπ
  have h_in_range : H₂.partition i ∈ Set.range
      ⇑((H₁.mergedPartitionPoints H₂).orderEmbOfFin (H₁.mergedM_card_eq H₂)) := by
    rw [Finset.range_orderEmbOfFin]
    exact_mod_cast H₁.partition_mem_mergedPartitionPoints_right H₂ i
  exact h_in_range

/-- **C0b.4-pre15: existence of left index map.** For each merged tile `j`,
there is an `H₁` tile `i` whose interval contains the merged tile.

Proof: apply `strictMono_partition_tiles` to `H₁.partition` with
`s = mergedπ j.succ` to get `i` with `H₁.partition i.castSucc < s` and
`s ≤ H₁.partition i.succ`. This gives the right inclusion.
For the left inclusion, suppose for contradiction
`mergedπ j.castSucc < H₁.partition i.castSucc`. Since `H₁.partition i.castSucc`
is in the merged set, it equals `mergedπ k` for some `k`. Then
`mergedπ j.castSucc < mergedπ k < mergedπ j.succ`, so `j.castSucc < k < j.succ`,
contradicting `j.succ.val = j.castSucc.val + 1`. -/
private lemma SimplePredictable.exists_mergedIdxMap_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    ∃ i : Fin H₁.N,
      H₁.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₁.partition i.succ := by
  -- Bounds on s = mergedπ j.succ to apply strictMono_partition_tiles
  have h_pos : H₁.partition 0 < H₁.mergedπ H₂ j.succ := by
    rw [H₁.partition_zero, ← H₁.mergedπ_zero H₂]
    exact (H₁.mergedπ_strictMono H₂) (Fin.succ_pos j)
  have h_le_endpt : H₁.mergedπ H₂ j.succ ≤ H₁.partition (Fin.last H₁.N) := by
    rw [← H₁.mergedπ_last H₂ h_eq]
    exact (H₁.mergedπ_strictMono H₂).monotone (Fin.le_last j.succ)
  obtain ⟨i, h_lt, h_le⟩ :=
    strictMono_partition_tiles H₁.partition_strictMono h_pos h_le_endpt
  refine ⟨i, ?_, h_le⟩
  by_contra h_not
  push_neg at h_not
  -- h_not : H₁.mergedπ H₂ j.castSucc < H₁.partition i.castSucc
  obtain ⟨k, hk⟩ := H₁.mergedπ_refines_left H₂ i.castSucc
  rw [← hk] at h_not h_lt
  have h_jcs_lt_k : j.castSucc < k :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_not
  have h_k_lt_jsc : k < j.succ :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_lt
  have hj_cs_val : j.castSucc.val = j.val := Fin.val_castSucc j
  have hj_succ_val : j.succ.val = j.val + 1 := Fin.val_succ j
  have h1 : j.castSucc.val < k.val := h_jcs_lt_k
  have h2 : k.val < j.succ.val := h_k_lt_jsc
  omega

/-- **C0b.4-pre16: existence of right index map.** Mirror of
`exists_mergedIdxMap_left` for the second SimplePredictable. -/
private lemma SimplePredictable.exists_mergedIdxMap_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    ∃ i : Fin H₂.N,
      H₂.partition i.castSucc ≤ H₁.mergedπ H₂ j.castSucc ∧
      H₁.mergedπ H₂ j.succ ≤ H₂.partition i.succ := by
  have h_pos : H₂.partition 0 < H₁.mergedπ H₂ j.succ := by
    rw [H₂.partition_zero, ← H₁.mergedπ_zero H₂]
    exact (H₁.mergedπ_strictMono H₂) (Fin.succ_pos j)
  have h_le_endpt : H₁.mergedπ H₂ j.succ ≤ H₂.partition (Fin.last H₂.N) := by
    rw [← h_eq, ← H₁.mergedπ_last H₂ h_eq]
    exact (H₁.mergedπ_strictMono H₂).monotone (Fin.le_last j.succ)
  obtain ⟨i, h_lt, h_le⟩ :=
    strictMono_partition_tiles H₂.partition_strictMono h_pos h_le_endpt
  refine ⟨i, ?_, h_le⟩
  by_contra h_not
  push_neg at h_not
  obtain ⟨k, hk⟩ := H₁.mergedπ_refines_right H₂ i.castSucc
  rw [← hk] at h_not h_lt
  have h_jcs_lt_k : j.castSucc < k :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_not
  have h_k_lt_jsc : k < j.succ :=
    (H₁.mergedπ_strictMono H₂).lt_iff_lt.mp h_lt
  have hj_cs_val : j.castSucc.val = j.val := Fin.val_castSucc j
  have hj_succ_val : j.succ.val = j.val + 1 := Fin.val_succ j
  have h1 : j.castSucc.val < k.val := h_jcs_lt_k
  have h2 : k.val < j.succ.val := h_k_lt_jsc
  omega

/-- **C0b.4-pre17: left index map.** For each merged tile `j`, the
unique `H₁` tile whose interval contains it. Extracted via Choice
from `exists_mergedIdxMap_left`. -/
noncomputable def SimplePredictable.mergedIdxMap_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) : Fin H₁.N :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose

/-- **C0b.4-pre18: left idxMap inclusion (left endpoint).** -/
lemma SimplePredictable.mergedIdxMap_left_idx_le
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.partition (H₁.mergedIdxMap_left H₂ h_eq j).castSucc
      ≤ H₁.mergedπ H₂ j.castSucc :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose_spec.1

/-- **C0b.4-pre19: left idxMap inclusion (right endpoint).** -/
lemma SimplePredictable.mergedIdxMap_left_idx_ge
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.mergedπ H₂ j.succ
      ≤ H₁.partition (H₁.mergedIdxMap_left H₂ h_eq j).succ :=
  (H₁.exists_mergedIdxMap_left H₂ h_eq j).choose_spec.2

/-- **C0b.4-pre20: right index map.** Mirror of `mergedIdxMap_left`. -/
noncomputable def SimplePredictable.mergedIdxMap_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) : Fin H₂.N :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose

/-- **C0b.4-pre21: right idxMap inclusion (left endpoint).** -/
lemma SimplePredictable.mergedIdxMap_right_idx_le
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₂.partition (H₁.mergedIdxMap_right H₂ h_eq j).castSucc
      ≤ H₁.mergedπ H₂ j.castSucc :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose_spec.1

/-- **C0b.4-pre22: right idxMap inclusion (right endpoint).** -/
lemma SimplePredictable.mergedIdxMap_right_idx_ge
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (j : Fin (H₁.mergedM H₂)) :
    H₁.mergedπ H₂ j.succ
      ≤ H₂.partition (H₁.mergedIdxMap_right H₂ h_eq j).succ :=
  (H₁.exists_mergedIdxMap_right H₂ h_eq j).choose_spec.2

/-- **C0b.4: common refinement of `H₁` (the left input).** Refine
`H₁` onto the merged partition `mergedπ`, using `mergedIdxMap_left`
to map merged tiles back to `H₁`-tiles. The resulting SimplePredictable
has `N = H₁.mergedM H₂`, partition `mergedπ`, and `ξ_j = H₁.ξ (idxMap j)`. -/
noncomputable def SimplePredictable.commonRefinement_left
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T :=
  H₁.refine (H₁.mergedM H₂) (H₁.mergedπ H₂)
    (H₁.mergedπ_zero H₂)
    (H₁.mergedπ_last H₂ h_eq)
    (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_left H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
    (H₁.mergedIdxMap_left_idx_ge H₂ h_eq)

/-- **C0b.4: common refinement of `H₂` (the right input).** Mirror of
`commonRefinement_left`, refining `H₂` onto the same `mergedπ`. The
two refinements share `N` and `partition` but differ in `ξ`. -/
noncomputable def SimplePredictable.commonRefinement_right
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T :=
  H₂.refine (H₁.mergedM H₂) (H₁.mergedπ H₂)
    (H₁.mergedπ_zero H₂)
    (h_eq ▸ H₁.mergedπ_last H₂ h_eq)
    (H₁.mergedπ_strictMono H₂)
    (H₁.mergedIdxMap_right H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
    (H₁.mergedIdxMap_right_idx_ge H₂ h_eq)

/-- **C0b.5: compatibility of the two common refinements.** They have
the same `N` (both equal to `mergedM`) and the same `partition` function
(both equal to `mergedπ`). This is what allows pointwise subtraction
of their `ξ` values to form `sub_on_common`. -/
lemma SimplePredictable.commonRefinement_compat
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    (H₁.commonRefinement_left H₂ h_eq).N
        = (H₁.commonRefinement_right H₂ h_eq).N
      ∧ HEq (H₁.commonRefinement_left H₂ h_eq).partition
            (H₁.commonRefinement_right H₂ h_eq).partition := by
  refine ⟨rfl, HEq.rfl⟩

/-- **C0b.6: subtraction on common refinement.** Given two
SimplePredictables sharing endpoint, the difference SimplePredictable
on the common refinement: same partition (`mergedπ`), with
`ξ_j ω = H₁.ξ (idxMap_left j) ω - H₂.ξ (idxMap_right j) ω`.

Boundedness uses `abs_sub` (`|a-b| ≤ |a|+|b|`) with the sum of bounds.
Measurability uses `Measurable.sub`. -/
noncomputable def SimplePredictable.sub_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N)) :
    SimplePredictable Ω T where
  N := H₁.mergedM H₂
  partition := H₁.mergedπ H₂
  partition_zero := H₁.mergedπ_zero H₂
  partition_le_T := (H₁.mergedπ_last H₂ h_eq) ▸ H₁.partition_le_T
  partition_strictMono := H₁.mergedπ_strictMono H₂
  ξ := fun j ω => H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
    - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω
  ξ_bounded := fun j => by
    obtain ⟨C₁, hC₁⟩ := H₁.ξ_bounded (H₁.mergedIdxMap_left H₂ h_eq j)
    obtain ⟨C₂, hC₂⟩ := H₂.ξ_bounded (H₁.mergedIdxMap_right H₂ h_eq j)
    exact ⟨C₁ + C₂, fun ω =>
      (abs_sub _ _).trans (add_le_add (hC₁ ω) (hC₂ ω))⟩
  ξ_measurable := fun j =>
    (H₁.ξ_measurable _).sub (H₂.ξ_measurable _)

/-- **C0b.7: linearity on common refinement.** The simple integral of
`sub_on_common H₁ H₂` equals the difference of the simple integrals of
`H₁` and `H₂`.

Proof: expand both `simpleIntegral`s via `simpleIntegral_eq_sum`,
distribute `(a-b)·c = a·c - b·c`, split the sum, then recognize each
sub-sum as the simple integral of `H_i` via `simpleIntegral_refine`
applied with the appropriate `idxMap`. -/
lemma SimplePredictable.simpleIntegral_sub_on_common
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (ω : Ω) :
    simpleIntegral W (H₁.sub_on_common H₂ h_eq) T ω
      = simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω := by
  rw [simpleIntegral_eq_sum]
  show (∑ j : Fin (H₁.mergedM H₂),
        (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
          - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        * (W.W (H₁.mergedπ H₂ j.succ) ω - W.W (H₁.mergedπ H₂ j.castSucc) ω))
      = simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · -- LHS sum = simpleIntegral W H₁ T ω
    have h_left := H₁.simpleIntegral_refine W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      (H₁.mergedπ_zero H₂) (H₁.mergedπ_last H₂ h_eq) (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_left H₂ h_eq) (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) (H₁.mergedπ_refines_left H₂) ω
    rw [← h_left, simpleIntegral_eq_sum]
    exact Finset.sum_congr rfl (fun _ _ => rfl)
  · -- RHS sum = simpleIntegral W H₂ T ω
    have h_right := H₂.simpleIntegral_refine W (H₁.mergedM H₂) (H₁.mergedπ H₂)
      (H₁.mergedπ_zero H₂) (h_eq ▸ H₁.mergedπ_last H₂ h_eq)
      (H₁.mergedπ_strictMono H₂)
      (H₁.mergedIdxMap_right H₂ h_eq) (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
      (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) (H₁.mergedπ_refines_right H₂) ω
    rw [← h_right, simpleIntegral_eq_sum]
    exact Finset.sum_congr rfl (fun _ _ => rfl)

/-- **C0b.7-aux: pointwise evaluation of `sub_on_common`.** The eval
of the difference SimplePredictable equals the pointwise difference of
the evals.

Proof: rewrite both `H₁.eval` and `H₂.eval` as evals of their respective
common refinements (via `refine_eval`), so all three `.eval` expressions
share the partition `mergedπ`. Then both sides are sums of if-then-else
indexed by `Fin (mergedM)`; case-splitting on the if-condition reduces
to a trivial arithmetic equality. -/
lemma SimplePredictable.eval_sub_on_common
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (s : ℝ) (ω : Ω) :
    (H₁.sub_on_common H₂ h_eq).eval s ω
      = H₁.eval s ω - H₂.eval s ω := by
  rw [← H₁.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂)
        (H₁.mergedπ_zero H₂) (H₁.mergedπ_last H₂ h_eq)
        (H₁.mergedπ_strictMono H₂) (H₁.mergedIdxMap_left H₂ h_eq)
        (H₁.mergedIdxMap_left_idx_le H₂ h_eq)
        (H₁.mergedIdxMap_left_idx_ge H₂ h_eq) s ω]
  rw [← H₂.refine_eval (H₁.mergedM H₂) (H₁.mergedπ H₂)
        (H₁.mergedπ_zero H₂) (h_eq ▸ H₁.mergedπ_last H₂ h_eq)
        (H₁.mergedπ_strictMono H₂) (H₁.mergedIdxMap_right H₂ h_eq)
        (H₁.mergedIdxMap_right_idx_le H₂ h_eq)
        (H₁.mergedIdxMap_right_idx_ge H₂ h_eq) s ω]
  unfold SimplePredictable.eval
  show (∑ j : Fin (H₁.mergedM H₂),
        if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
        then (H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω
              - H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω)
        else 0)
      = (∑ j : Fin (H₁.mergedM H₂),
          if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
          then H₁.ξ (H₁.mergedIdxMap_left H₂ h_eq j) ω else 0)
        - (∑ j : Fin (H₁.mergedM H₂),
          if H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
          then H₂.ξ (H₁.mergedIdxMap_right H₂ h_eq j) ω else 0)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h_cond : H₁.mergedπ H₂ j.castSucc < s ∧ s ≤ H₁.mergedπ H₂ j.succ
  · simp [h_cond]
  · simp [h_cond]

/-- **C0b.8-pre: adaptedness of `sub_on_common`.** If both inputs are
adapted to the natural filtration of `W`, so is `sub_on_common`. The
proof: for each merged tile `j`, the input adaptedness gives StronglyMeas
at `H_k.partition (idxMap_k j).castSucc`. By `Filtration.mono` and
`mergedIdxMap_k_idx_le` (which says `H_k.partition (idxMap_k j).castSucc
≤ mergedπ j.castSucc`), this upgrades to StronglyMeas at the merged
partition point. The difference is StronglyMeas via `StronglyMeasurable.sub`. -/
lemma SimplePredictable.sub_on_common_adapt
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∀ j : Fin (H₁.sub_on_common H₂ h_eq).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((H₁.sub_on_common H₂ h_eq).partition j.castSucc))
        ((H₁.sub_on_common H₂ h_eq).ξ j) := by
  intro j
  have h_mono₁ := (LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono
    (H₁.mergedIdxMap_left_idx_le H₂ h_eq j)
  have h_mono₂ := (LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono
    (H₁.mergedIdxMap_right_idx_le H₂ h_eq j)
  have h₁ := (h_adapt₁ (H₁.mergedIdxMap_left H₂ h_eq j)).mono h_mono₁
  have h₂ := (h_adapt₂ (H₁.mergedIdxMap_right H₂ h_eq j)).mono h_mono₂
  exact h₁.sub h₂

/-- **C0b.8: L² isometry on the difference of simples (`diff isometry`).**
For two adapted simple integrands `H₁, H₂` sharing endpoint, the L² norm
squared of `∫H₁ dW − ∫H₂ dW` equals the (joint) L² norm squared of
`H₁.eval − H₂.eval` over `[0,T] × Ω`.

Direct consequence of `simpleIntegral_isometry` applied to `sub_on_common`,
combined with `simpleIntegral_sub_on_common` (LHS rewrite) and
`eval_sub_on_common` (RHS rewrite). The adaptedness of `sub_on_common`
follows from `sub_on_common_adapt`. -/
theorem SimplePredictable.diff_isometry_simple
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₂.partition i.castSucc)) (H₂.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_LHS :
      ∫⁻ ω, (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖simpleIntegral W (H₁.sub_on_common H₂ h_eq) T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P := by
    refine MeasureTheory.lintegral_congr (fun ω => ?_)
    rw [SimplePredictable.simpleIntegral_sub_on_common W H₁ H₂ h_eq ω]
  have h_RHS :
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖((H₁.sub_on_common H₂ h_eq).eval s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    refine MeasureTheory.lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc
      (fun s _ => ?_)
    rw [SimplePredictable.eval_sub_on_common H₁ H₂ h_eq s ω]
  rw [h_LHS, h_RHS]
  exact simpleIntegral_isometry W hT (H₁.sub_on_common H₂ h_eq)
    (SimplePredictable.sub_on_common_adapt W H₁ H₂ h_eq h_adapt₁ h_adapt₂)

/-- **C0b.9: Cauchy preservation for `simpleIntegral`.** If an
eval-sequence of adapted simple integrands sharing a common endpoint is
`L²(λ⊗P)`-Cauchy (in ε-`N` form on the squared `lintegral`), then the
sequence of `simpleIntegral`s is `L²(P)`-Cauchy.

Direct corollary of `diff_isometry_simple` applied pairwise: each
pairwise distance on the integral side equals the corresponding pairwise
distance on the eval side, so the eval-Cauchy ε-`N` witness `N` works
verbatim for the integrals. -/
theorem cauchy_of_L2_dense_simple
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, (‖simpleIntegral W (G n) T ω - simpleIntegral W (G m) T ω‖₊
              : ℝ≥0∞) ^ 2 ∂P < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_cauchy_eval ε hε
  refine ⟨N, fun n m hn hm => ?_⟩
  rw [SimplePredictable.diff_isometry_simple W hT (G n) (G m)
        (h_eq n m) (h_adapt n) (h_adapt m)]
  exact hN n m hn hm

/-- **C0b.10-pre1: `simpleIntegral` has finite `L²(P)` norm.** For any
adapted `SimplePredictable`, the squared `lintegral` of the integral
against `P` is finite. Direct from `simpleIntegral_isometry` (giving
`= ∫⁻ ω ∫⁻ s ‖H.eval s ω‖²`) plus `lintegral_eval_sq_outer` (giving
`= ∑_i Δt_i · ∫⁻ ω ‖H.ξ i ω‖²`), each summand bounded by
`Δt_i · M_i² ≤ T · M_i² < ∞` via `ξ_bounded`.

This is the boundedness fact needed to lift `simpleIntegral W H T` to
an element of `Lp ℝ 2 P` for the `L²` extension in `C0b.10`. -/
lemma simpleIntegral_lintegral_sq_finite_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [simpleIntegral_isometry W hT H h_adapt]
  rw [lintegral_eval_sq_outer H]
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_M_nn : 0 ≤ max M 0 := le_max_right _ _
  have h_bound : ∀ ω, |H.ξ i ω| ≤ max M 0 :=
    fun ω => le_trans (hM ω) (le_max_left _ _)
  have h_norm_le : ∀ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (max M 0) := by
    intro ω
    rw [show (‖H.ξ i ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.ξ i ω‖
          from (ofReal_norm_eq_enorm _).symm]
    exact ENNReal.ofReal_le_ofReal
      (Real.norm_eq_abs _ ▸ h_bound ω)
  calc ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ _ω, (ENNReal.ofReal (max M 0)) ^ 2 ∂P := by
        refine MeasureTheory.lintegral_mono (fun ω => ?_)
        exact pow_le_pow_left' (h_norm_le ω) 2
    _ = (ENNReal.ofReal (max M 0)) ^ 2 * P Set.univ := by
        rw [MeasureTheory.lintegral_const]
    _ < ⊤ := by
        rw [MeasureTheory.measure_univ, mul_one]
        exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/-- **C0b.10-pre2: `simpleIntegral W H T` is in `L²(P)`.** Combines
the AEStronglyMeasurability of `simpleIntegral` (via `Finset.sum`
of measurable terms) with `simpleIntegral_lintegral_sq_finite_brownian`
(C0b.10-pre1) to produce a `MemLp 2 P` witness. This is the lift
of `simpleIntegral` into Mathlib's `Lp` framework, needed for the
L²-Cauchy completion in C0b.10. -/
lemma simpleIntegral_memLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H T ω) 2 P := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable: simpleIntegral W H T = ∑_i ξ_i · ΔW_i
    -- is a finite sum of products of measurable functions.
    refine Measurable.aestronglyMeasurable ?_
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul (H.ξ_measurable i) ?_
    exact (W.measurable_eval _).sub (W.measurable_eval _)
  · -- eLpNorm < ⊤: from C0b.10-pre1 (∫⁻ ‖simpleIntegral‖² < ⊤) via
    -- eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top.
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h_two_toReal]
    have h_pre := simpleIntegral_lintegral_sq_finite_brownian W hT H h_adapt
    -- Bridge ‖x‖ₑ ^ (2:ℝ) vs (‖x‖₊ : ℝ≥0∞) ^ (2:ℕ)
    have h_rewrite : ∀ ω : Ω,
        (‖simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          = (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [show (fun ω => (‖simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2) from
        funext h_rewrite]
    exact h_pre

/-- **C0b.10-pre3: simpleIntegral lifted to `Lp ℝ 2 P`.** Packages the
`simpleIntegral_memLp_brownian` witness via `MemLp.toLp` to give a
genuine `Lp` element. This is the function that gets fed to
`MeasureTheory.Lp.completeSpace` for the L² limit construction in
C0b.10. -/
noncomputable def simpleIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Lp ℝ 2 P :=
  (simpleIntegral_memLp_brownian W hT H h_adapt).toLp

/-- **C0b.10-pre4: `simpleIntegralLp_brownian` `coeFn` matches `simpleIntegral`.**
The coercion of `simpleIntegralLp_brownian W hT H h_adapt` back to a
function `Ω → ℝ` is a.e.-equal to `fun ω => simpleIntegral W H T ω`. -/
lemma coeFn_simpleIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    (simpleIntegralLp_brownian W hT H h_adapt : Ω → ℝ)
      =ᵐ[P] (fun ω => simpleIntegral W H T ω) :=
  MeasureTheory.MemLp.coeFn_toLp _

/-- **C0b.10-pre5: `eLpNorm` of the `simpleIntegral` difference,
rpow-form.** `eLpNorm (...)^(2:ℝ) = ∫⁻ ‖eval diff‖² over [0,T]×Ω`.

This is `diff_isometry_simple` rephrased in `eLpNorm` form using the
real-valued exponent `(2:ℝ)`, ready for use with the L²-Cauchy
completion machinery. -/
lemma eLpNorm_simpleIntegral_sub_rpow_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₂.partition i.castSucc)) (H₂.ξ i)) :
    MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := P) (p := (2 : NNReal))
    (f := fun ω => simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω)
    (by norm_num : (2 : NNReal) ≠ 0)
  -- h_pow_lemma : eLpNorm f (↑(2:NNReal)) P ^ ↑(2:NNReal)
  --              = ∫⁻ ω, ‖f ω‖ₑ ^ ↑(2:NNReal) ∂P
  -- The ↑(2:NNReal) on the LHS-base is (2:ℝ≥0∞); on exponents it's (2:ℝ).
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  -- Goal: ∫⁻ ω, ‖simpleIntegral H₁ - simpleIntegral H₂‖ₑ ^ (2:ℝ) ∂P
  --     = ∫⁻ ω, ∫⁻ s, ‖eval diff‖₊² ∂vol ∂P
  -- Convert (2:ℝ) exponent to (2:ℕ) via ENNReal.rpow_natCast,
  -- then bridge ‖.‖ₑ = (‖.‖₊ : ℝ≥0∞).
  have h_pointwise : (fun ω : Ω =>
        (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
      = (fun ω : Ω =>
        (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖₊ : ℝ≥0∞) ^ 2) := by
    funext ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
        ENNReal.rpow_natCast]
    rfl
  rw [h_pointwise]
  exact SimplePredictable.diff_isometry_simple W hT H₁ H₂ h_eq h_adapt₁ h_adapt₂

/-- **C0b.10-pre6: `simpleIntegralLp_brownian` is a `CauchySeq` in
`Lp ℝ 2 P` whenever the eval-sequence is L²-Cauchy.**

Direct application of the eLpNorm-form diff isometry
(`eLpNorm_simpleIntegral_sub_rpow_brownian`) plus
`ENNReal.rpow_lt_rpow_iff` to convert `eLpNorm^(2:ℝ) < ε^(2:ℝ)` to
`eLpNorm < ε`. The L²-Cauchy hypothesis on evals provides the matching
`∫⁻ < ε^(2:ℝ)` bound. -/
theorem cauchySeq_simpleIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    CauchySeq (fun n => simpleIntegralLp_brownian W hT (G n) (h_adapt n)) := by
  -- Step 1: establish that edist of the Lp elements equals the eLpNorm of the
  -- raw simpleIntegral function difference (via Lp.edist_toLp_toLp).
  have h_edist_eq : ∀ m n : ℕ,
      edist (simpleIntegralLp_brownian W hT (G m) (h_adapt m))
            (simpleIntegralLp_brownian W hT (G n) (h_adapt n))
        = MeasureTheory.eLpNorm
            (fun ω => simpleIntegral W (G m) T ω - simpleIntegral W (G n) T ω) 2 P := by
    intro m n
    show edist
      ((simpleIntegral_memLp_brownian W hT (G m) (h_adapt m)).toLp)
      ((simpleIntegral_memLp_brownian W hT (G n) (h_adapt n)).toLp) = _
    exact MeasureTheory.Lp.edist_toLp_toLp _ _ _ _
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · -- ε = ⊤: edist always finite (Lp norms are < ⊤).
    obtain ⟨N, _⟩ := h_cauchy_eval 1 (by norm_num : (0 : ℝ≥0∞) < 1)
    refine ⟨N, fun m _ n _ => ?_⟩
    rw [hε_top, h_edist_eq]
    -- eLpNorm of MemLp function is finite.
    have h_memLp : MeasureTheory.MemLp
        (fun ω => simpleIntegral W (G m) T ω - simpleIntegral W (G n) T ω) 2 P :=
      (simpleIntegral_memLp_brownian W hT (G m) (h_adapt m)).sub
        (simpleIntegral_memLp_brownian W hT (G n) (h_adapt n))
    exact lt_of_le_of_ne le_top h_memLp.eLpNorm_ne_top
  · -- ε < ⊤. Pick δ = ε ^ (2:ℝ).
    set δ : ℝ≥0∞ := ε ^ (2 : ℝ) with hδ
    have hδ_pos : 0 < δ := by
      rw [hδ]
      exact ENNReal.rpow_pos hε hε_top
    obtain ⟨N, hN⟩ := h_cauchy_eval δ hδ_pos
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [h_edist_eq]
    have h_iso := eLpNorm_simpleIntegral_sub_rpow_brownian W hT (G m) (G n)
      (h_eq m n) (h_adapt m) (h_adapt n)
    have h_lt := hN m n hm hn
    rw [← h_iso] at h_lt
    rw [hδ] at h_lt
    exact (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h_lt

/-- **C0b.10: `itoIntegralLp_brownian` — the L²-limit of `simpleIntegralLp_brownian`
along a Cauchy approximating sequence.**

This is the genuine L²-extended Itô integral against Brownian motion,
defined as `Filter.limUnder Filter.atTop (simpleIntegralLp_brownian ∘ G)`
for any approximating sequence `G : ℕ → SimplePredictable` whose evals
are L²-Cauchy and which are adapted with shared endpoints.

The convergence (and unique-limit identification) follows from
`Lp.completeSpace` + `cauchySeq_simpleIntegralLp_brownian` (C0b.10-pre6)
+ `CauchySeq.tendsto_limUnder`. Properties of `itoIntegralLp_brownian`
(L² isometry, etc.) are proved in subsequent lemmas. -/
noncomputable def itoIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (_hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (_h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (_h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    MeasureTheory.Lp ℝ 2 P :=
  Filter.limUnder Filter.atTop
    (fun n => simpleIntegralLp_brownian W _hT (G n) (h_adapt n))

/-- **C0b.10-post1: `simpleIntegralLp_brownian` converges to `itoIntegralLp_brownian`
in `Lp ℝ 2 P`.** Direct from `cauchySeq_simpleIntegralLp_brownian` +
`CauchySeq.tendsto_limUnder` (using `Lp.completeSpace`). -/
theorem itoIntegralLp_brownian_tendsto
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => simpleIntegralLp_brownian W hT (G n) (h_adapt n))
      Filter.atTop
      (nhds (itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval)) :=
  (cauchySeq_simpleIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval).tendsto_limUnder

/-- **C0b.10-post2: `eLpNorm` of `simpleIntegralLp` rpow-form, the
single-function version of the diff isometry.**

`eLpNorm (simpleIntegralLp ...) 2 P ^ (2:ℝ) = ∫⁻ ω ∫⁻ s ‖H.eval s ω‖₊² ∂vol ∂P`.

Direct from `simpleIntegral_isometry` (single-function version) plus
the same `eLpNorm_nnreal_pow_eq_lintegral` bridge as the diff form. -/
lemma eLpNorm_simpleIntegralLp_brownian_rpow_eq
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT H h_adapt) : Ω → ℝ) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Step 1: replace ↑↑(toLp ...) with the original simpleIntegral function (a.e.).
  have h_aeeq := coeFn_simpleIntegralLp_brownian W hT H h_adapt
  rw [MeasureTheory.eLpNorm_congr_ae h_aeeq]
  -- Goal: eLpNorm (fun ω => simpleIntegral W H T ω) 2 P ^ (2:ℝ)
  --     = ∫⁻ ω, ∫⁻ s, ‖H.eval s ω‖₊² ∂vol ∂P
  -- Step 2: eLpNorm^(2:ℝ) = ∫⁻ ‖.‖_e² via eLpNorm_nnreal_pow_eq_lintegral.
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := P) (p := (2 : NNReal))
    (f := fun ω => simpleIntegral W H T ω)
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  -- Goal: ∫⁻ ω, ‖simpleIntegral W H T ω‖_e ^ (2:ℝ) ∂P
  --     = ∫⁻ ω, ∫⁻ s, ‖H.eval s ω‖₊² ∂vol ∂P
  -- Step 3: ‖.‖_e ^ (2:ℝ) = (‖.‖₊ : ℝ≥0∞) ^ 2 (via ENNReal.rpow_natCast).
  have h_pointwise : (fun ω : Ω =>
        (‖simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
      = (fun ω : Ω => (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2) := by
    funext ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
        ENNReal.rpow_natCast]
    rfl
  rw [h_pointwise]
  -- Goal: ∫⁻ ω, ‖simpleIntegral W H T ω‖₊² ∂P
  --     = ∫⁻ ω, ∫⁻ s, ‖H.eval s ω‖₊² ∂vol ∂P
  -- Step 4: simpleIntegral_isometry.
  exact simpleIntegral_isometry W hT H h_adapt

/-- **C0b.10-post3: ‖simpleIntegralLp_brownian (G n)‖ converges to
‖itoIntegralLp_brownian‖ in ℝ.** Direct from the convergence of
`simpleIntegralLp_brownian (G n) → itoIntegralLp_brownian` in `Lp`
plus continuity of the norm. -/
theorem norm_simpleIntegralLp_tendsto_norm_itoIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => ‖simpleIntegralLp_brownian W hT (G n) (h_adapt n)‖)
      Filter.atTop
      (nhds ‖itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval‖) :=
  (itoIntegralLp_brownian_tendsto W hT G h_eq h_adapt h_cauchy_eval).norm

/-- **C0b.10-post4: `eLpNorm (↑↑(simpleIntegralLp (G n))) 2 P` converges
to `eLpNorm (↑↑(itoIntegralLp ...)) 2 P` in `ℝ≥0∞`.** ENNReal-valued
companion to `norm_simpleIntegralLp_tendsto_norm_itoIntegralLp_brownian`,
via `Filter.Tendsto.enorm` and `Lp.enorm_def`. -/
theorem eLpNorm_simpleIntegralLp_tendsto_eLpNorm_itoIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P)
      Filter.atTop
      (nhds (MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ) 2 P)) := by
  have h_tendsto :=
    (itoIntegralLp_brownian_tendsto W hT G h_eq h_adapt h_cauchy_eval).enorm
  -- h_tendsto : Tendsto (fun n => ‖Lp_n‖ₑ) atTop (nhds ‖Lp_lim‖ₑ)
  -- Use Lp.enorm_def to convert ‖f‖ₑ = eLpNorm (↑↑f) p μ.
  simp only [MeasureTheory.Lp.enorm_def] at h_tendsto
  exact h_tendsto

/-- **C0b.10-post5: `eLpNorm (simpleIntegralLp (G n)) ^ (2:ℝ)` converges
to `eLpNorm (itoIntegralLp ...) ^ (2:ℝ)` in `ℝ≥0∞`.** Direct application
of `Filter.Tendsto.ennrpow_const` to the eLpNorm convergence (post4). -/
theorem eLpNorm_rpow_simpleIntegralLp_tendsto_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P ^ (2 : ℝ))
      Filter.atTop
      (nhds (MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ) 2 P ^ (2 : ℝ))) :=
  (eLpNorm_simpleIntegralLp_tendsto_eLpNorm_itoIntegralLp_brownian
    W hT G h_eq h_adapt h_cauchy_eval).ennrpow_const 2

end LevyStochCalc.Brownian.Ito
