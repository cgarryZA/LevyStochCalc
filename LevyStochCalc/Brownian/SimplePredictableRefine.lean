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
    push Not at h_not
    have h_zero_val : k_min.val = 0 := Nat.le_zero.mp h_not
    have h_eq : k_min = (0 : Fin (M + 1)) := Fin.ext (by simp [h_zero_val])
    rw [h_eq] at h_s_le_pi
    exact absurd hs_pos (not_lt.mpr h_s_le_pi)
  have h_M_pos : 0 < M := by
    by_contra h_not
    push Not at h_not
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
    push Not at h_not
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
  change (∑ j : Fin M, if π' j.castSucc < s ∧ s ≤ π' j.succ
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
      push Not at h_inside
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
    change π' j.castSucc < (π' j.castSucc + π' j.succ) / 2; linarith
  have h_test_hi : s_test < π' j.succ := by
    change (π' j.castSucc + π' j.succ) / 2 < π' j.succ; linarith
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
    change H.ξ i ω * (W.W (π' ⟨j.val + 1, h_succ_lt⟩) ω
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
  change (∑ j : Fin M, H.ξ (idxMap j) ω
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
  push Not at h_not
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
  push Not at h_not
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
  change (∑ j : Fin (H₁.mergedM H₂),
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
  change (∑ j : Fin (H₁.mergedM H₂),
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
    change edist
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

/-- **C0b.10-post6: lintegral-of-squared-eval converges to `eLpNorm²` of
`itoIntegralLp_brownian`.**

Substitutes `eLpNorm_simpleIntegralLp_brownian_rpow_eq` (post2) into
`eLpNorm_rpow_simpleIntegralLp_tendsto_brownian` (post5) to express
the convergence in pure-lintegral form. -/
theorem lintegral_sq_eval_tendsto_eLpNorm_itoIntegralLp_brownian
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
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ) 2 P ^ (2 : ℝ))) := by
  have h_tendsto := eLpNorm_rpow_simpleIntegralLp_tendsto_brownian
    W hT G h_eq h_adapt h_cauchy_eval
  -- h_tendsto : Tendsto (fun n => eLpNorm² (simpleIntegralLp (G n))) atTop
  --              (nhds (eLpNorm² (itoIntegralLp ...)))
  -- Substitute eLpNorm² = lintegral via post2.
  have h_subst : ∀ n : ℕ,
      MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun n => eLpNorm_simpleIntegralLp_brownian_rpow_eq W hT (G n) (h_adapt n)
  -- Rewrite the function inside the Tendsto.
  have h_eqv : (fun n => MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P ^ (2 : ℝ))
      = (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
    funext h_subst
  rw [h_eqv] at h_tendsto
  exact h_tendsto

/-- **C0b.10-post7: L² isometry on `itoIntegralLp_brownian`.**

Conditional on the approximating sequence's `lintegral_sq` of `(G n).eval`
converging to `∫⁻ ω ∫⁻ s ‖H ω s‖₊² ∂vol ∂P`, we obtain
`eLpNorm² (itoIntegralLp ...) = ∫⁻ ω ∫⁻ s ‖H ω s‖₊² ∂vol ∂P`.

By uniqueness of limits in `ℝ≥0∞`, combining the two `Tendsto` statements
(the `(G n).eval`-form from `lintegral_sq_eval_tendsto_...` and the
hypothesised convergence to `∫⁻ ‖H‖²`) forces equality of the limits. -/
theorem itoIntegralLp_brownian_L2_isometry
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
          ∂volume ∂P < ε)
    (H : Ω → ℝ → ℝ)
    (h_eval_norm_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) :
    MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ) 2 P
          ^ (2 : ℝ)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Both Tendsto statements have the same source filter and source function;
  -- their target nhds-points must coincide by uniqueness of limits.
  have h_to_eLpNorm := lintegral_sq_eval_tendsto_eLpNorm_itoIntegralLp_brownian
    W hT G h_eq h_adapt h_cauchy_eval
  exact (tendsto_nhds_unique h_to_eLpNorm h_eval_norm_tendsto)

/-- **C0b.10-post8: `simpleIntegral W H t` is StronglyAdapted at `t`
to `naturalFiltration W`.**

For each `t : ℝ` and adapted SimplePredictable `H`, the function
`ω ↦ simpleIntegral W H t ω` is StronglyMeasurable wrt the natural
filtration's σ-algebra at `t`. Direct from
`martingale_simpleIntegral_brownian` (which establishes adaptedness as
its first conjunct). -/
lemma simpleIntegral_stronglyAdapted_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
      (fun ω => simpleIntegral W H t ω) :=
  (martingale_simpleIntegral_brownian W H h_adapt).stronglyAdapted t

/-- **C0b.10-post9: `simpleIntegral W H t` is in `Lp ℝ 1 P`** (integrable).

Direct from `Lp 2 ⊆ Lp 1` for finite measures (`MemLp.mono_exponent`)
applied to `simpleIntegral_memLp_brownian` (post2). Used in martingale
property checks where integrability (Lp¹) is required. -/
lemma simpleIntegral_integrable_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Integrable (fun ω => simpleIntegral W H T ω) P := by
  have h_memLp := simpleIntegral_memLp_brownian W hT H h_adapt
  -- MemLp 2 P implies MemLp 1 P (= Integrable) when measure is finite.
  exact (h_memLp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable
    (le_refl 1)

/-- **C0b.10-post10: cond-exp identity for `simpleIntegral`.** Direct
extraction of the cond-exp clause from `martingale_simpleIntegral_brownian`
for downstream use without unpacking the Martingale structure. -/
lemma simpleIntegral_condExp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => simpleIntegral W H t ω
        | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s]
      =ᵐ[P] (fun ω => simpleIntegral W H s ω) :=
  (martingale_simpleIntegral_brownian W H h_adapt).condExp_ae_eq hst

/-- **C0b.10-final: existence of an L²-isometric process for adapted-approximated H.**

Conditional on:
- `H` being approximated in `L²(λ⊗P)` by an adapted approximating
  sequence `(G n)` of `SimplePredictable`s sharing common endpoint, AND
- the lintegral_sq of `(G n).eval` converging to lintegral_sq of `H`,

we get an `L²(P)`-element `M` (the L²-extended Itô integral) satisfying
the L² isometry `eLpNorm² M = lintegral_sq H` over `[0,T] × Ω`.

This is the existence content extracted from the C0b chain, without
the additional martingale + quadVar conjuncts of the full strong-exists.
For closing the full strong-exists, one needs (a) extending C0b.9 to
general time `t < T`, (b) the limit-of-martingales + limit-of-quadVar
arguments for the time-parametrized version. -/
theorem exists_itoIntegralL2_brownian
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
          ∂volume ∂P < ε)
    (H : Ω → ℝ → ℝ)
    (h_eval_norm_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) :
    ∃ M : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑M : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  ⟨itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval,
   itoIntegralLp_brownian_L2_isometry W hT G h_eq h_adapt h_cauchy_eval H
     h_eval_norm_tendsto⟩

/-- **Bounded progressively-measurable existence.** For bounded progressively-measurable
`g : Ω → ℝ → ℝ` with explicit bound `M`, there exists an `Lp ℝ 2 P` element whose
squared `eLpNorm` over `P` equals the full `L²(P × ds)` norm of `g` over `[0,T]`.

Construction: feed the explicit `predictableDyadicSimple_brownian` sequence into
`exists_itoIntegralL2_brownian`. All four prerequisites are dyadic-specific lemmas
already in `Brownian.Ito`:

* `_partition_last` for `h_eq` (constant endpoint = T).
* `_adapted` for `h_adapt` (under progressive measurability).
* `L2_cauchy_of_L2_tendsto_brownian` applied to `_L2_converges` for `h_cauchy_eval`.
* `_eval_norm_tendsto_bounded` for `h_eval_norm_tendsto`. -/
theorem exists_itoIntegralL2_brownian_progMeas_bounded
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => g p.1 p.2))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Mlp : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set G : ℕ → SimplePredictable Ω T :=
    fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n with hG
  have h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N) := by
    intro n m
    rw [predictableDyadicSimple_brownian_partition_last hT g h_meas M h_bound n,
        predictableDyadicSimple_brownian_partition_last hT g h_meas M h_bound m]
  have h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i) :=
    fun n => predictableDyadicSimple_brownian_adapted W hT g h_meas M h_bound h_progMeas n
  have h_norm_tendsto :=
    predictableDyadicSimple_brownian_eval_norm_tendsto_bounded
      (P := P) hT g h_meas M h_bound
  -- L²-Cauchy: from L²-Tendsto via the generic helper.
  have h_L2_diff := predictableDyadicSimple_brownian_L2_converges
    (P := P) hT g h_meas M h_bound
  have h_eval_meas : ∀ n,
      Measurable (fun (p : Ω × ℝ) => (G n).eval p.2 p.1) :=
    fun n => predictableDyadicSimple_brownian_eval_jointly_measurable
      hT g h_meas M h_bound n
  have h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε :=
    L2_cauchy_of_L2_tendsto_brownian (P := P) (T := T)
      G g h_eval_meas h_meas h_L2_diff
  exact exists_itoIntegralL2_brownian (P := P) W hT G h_eq h_adapt h_cauchy_eval g
    h_norm_tendsto

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Unbounded progressively-measurable existence.** For progressively-measurable
`H : Ω → ℝ → ℝ` in `L²(Ω × [0,T], dP ⊗ ds)` (no bound assumed), there exists an
`Lp ℝ 2 P` element whose squared `eLpNorm` over `P` equals the full `L²(P × ds)`
norm of `H` over `[0,T]`.

Construction: diagonal lift across truncations. For each `n : ℕ`, the bounded
existence applied to `clip_n H` gives an explicit dyadic SimplePredictable
sequence; pick the diagonal index `max n (N_seq n)` with `N_seq n` chosen so that
the bounded approximation is within `1/(n+1)` of `clip_n H` in L². Combine
truncation L²-convergence with the diagonal estimate via the standard
`(a+b)² ≤ 2(a²+b²)` triangle. Then apply the bounded theorem with `clip_n H`
on the diagonal sequence + `exists_itoIntegralL2_brownian`. -/
theorem exists_itoIntegralL2_brownian_progMeas
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Mlp : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Truncation helpers (mirrored from adaptedSimple_dense_L2_brownian).
  have h_clip_bound : ∀ M : ℕ, ∀ ω s,
      |max (-(M : ℝ)) (min (M : ℝ) (H ω s))| ≤ (M : ℝ) := by
    intro M ω s
    have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have h_clip_meas : ∀ M : ℕ, Measurable
      (Function.uncurry (fun (ω : Ω) (s : ℝ) =>
        max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
    intro M
    have h : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact h.comp h_meas
  have h_clip_progMeas : ∀ M : ℕ, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))) := by
    intro M t
    have h_clip_cont : Continuous (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by
      fun_prop
    exact h_clip_cont.comp_stronglyMeasurable (h_progMeas t)
  -- Bounded existence on each clipped function.
  have h_bdd : ∀ M : ℕ, ∃ Mlp_M : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp_M : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun M => exists_itoIntegralL2_brownian_progMeas_bounded W hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (h_clip_progMeas M) (M : ℝ) (h_clip_bound M)
  -- Pick N_seq for the diagonal: for each n, choose k ≥ N_seq n such that the
  -- L²-distance from clip_n H to the dyadic eval at depth k is ≤ 1/(n+1).
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s)) -
          (predictableDyadicSimple_brownian hT
            (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
            (h_clip_meas n) (n : ℝ) (h_clip_bound n) k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    have h_L2 := predictableDyadicSimple_brownian_L2_converges (P := P) hT
      (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (h_clip_meas n) (n : ℝ) (h_clip_bound n)
    exact (ENNReal.tendsto_atTop_zero.mp h_L2) _ h_eps
  choose N_seq h_N_seq using h_N
  -- Diagonal sequence: G n = dyadic for clip_n H at depth (max n (N_seq n)).
  set G : ℕ → SimplePredictable Ω T := fun n =>
    predictableDyadicSimple_brownian hT
      (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (h_clip_meas n) (n : ℝ) (h_clip_bound n) (max n (N_seq n)) with hG_def
  -- Properties of G.
  have h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N) := by
    intro n m
    rw [hG_def]
    rw [predictableDyadicSimple_brownian_partition_last hT _
          (h_clip_meas n) (n : ℝ) (h_clip_bound n) (max n (N_seq n)),
        predictableDyadicSimple_brownian_partition_last hT _
          (h_clip_meas m) (m : ℝ) (h_clip_bound m) (max m (N_seq m))]
  have h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i) := by
    intro n i
    exact predictableDyadicSimple_brownian_adapted W hT _
      (h_clip_meas n) (n : ℝ) (h_clip_bound n) (h_clip_progMeas n) (max n (N_seq n)) i
  have h_eval_meas : ∀ n,
      Measurable (fun (p : Ω × ℝ) => (G n).eval p.2 p.1) :=
    fun n => SimplePredictable.eval_jointly_measurable (G n)
  -- L²-convergence of G to H: diagonal lift.
  have h_trunc := truncation_L2_converges_brownian H h_meas h_sq_int (T := T)
  have h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_atTop_zero] at h_trunc ⊢
    intro ε hε_pos
    have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
      rw [ENNReal.div_pos_iff]
      refine ⟨hε_pos.ne', ?_⟩
      decide
    obtain ⟨N₁, hN₁⟩ := h_trunc (ε / 4) hε4_pos
    have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
        Filter.atTop (nhds 0) := by
      have h := ENNReal.tendsto_inv_nat_nhds_zero
      have hcomp : Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
        h.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Nat.cast_add, Nat.cast_one] using hcomp
    obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) (ε / 4) hε4_pos
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn
    have hn₁ : N₁ ≤ n := le_of_max_le_left hn
    have hn₂ : N₂ ≤ n := le_of_max_le_right hn
    -- Pointwise (a + b)² ≤ 2(a² + b²) splitting:
    -- ‖H - (G n).eval‖² ≤ 2 ‖H - clip_n H‖² + 2 ‖clip_n H - (G n).eval‖².
    have h_pointwise : ∀ ω s,
        (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
              + (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s
      have h_sum : (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
          + (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
              - (G n).eval s ω)
          = H ω s - (G n).eval s ω := by ring
      have := sq_nnnorm_add_le_two_mul_brownian
        (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
        (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
          - (G n).eval s ω)
      rw [h_sum] at this
      exact this
    set A : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 with hA
    set B : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                      - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
    set C : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
    have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
    have h_s_le : ∀ ω,
        (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
          2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
      intro ω
      calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
            MeasureTheory.lintegral_mono (h_C_le ω)
        _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
            rw [MeasureTheory.lintegral_const_mul']
            simp
        _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
            congr 1
            rw [MeasureTheory.lintegral_add_left']
            have h_meas_A_s : Measurable (fun s => A ω s) := by
              simp only [hA]
              exact ((by fun_prop : Measurable (fun s =>
                ‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊)).coe_nnreal_ennreal).pow_const 2
            exact h_meas_A_s.aemeasurable
    have h_double_le :
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
      calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
          ≤ ∫⁻ ω,
              2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
                + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
            MeasureTheory.lintegral_mono h_s_le
        _ = 2 * ∫⁻ ω,
              ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
                + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
            rw [MeasureTheory.lintegral_const_mul']
            simp
        _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
            + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
            congr 1
            rw [MeasureTheory.lintegral_add_left']
            have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
              simp only [hA]
              exact ((by fun_prop : Measurable (fun (q : Ω × ℝ) =>
                ‖H q.1 q.2 - max (-(n : ℝ)) (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal).pow_const 2
            exact (Measurable.lintegral_prod_right'
              (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
    have h_first : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ε / 4 := hN₁ n hn₁
    have h_second : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ε / 4 := by
      have h_max_ge : N_seq n ≤ max n (N_seq n) := le_max_right _ _
      exact (h_N_seq n (max n (N_seq n)) h_max_ge).trans (hN₂ n hn₂)
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        ≤ 2 * (ε / 4 + ε / 4) := by
          refine h_double_le.trans ?_
          exact mul_le_mul_left' (add_le_add h_first h_second) _
      _ = ε := by
          rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
          exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)
  -- L²-Cauchy from L²-convergence.
  have h_cauchy_eval := L2_cauchy_of_L2_tendsto_brownian (P := P) (T := T)
    G H h_eval_meas h_meas h_L2_diff
  -- Norm-tendsto from the general lemma.
  have h_norm_tendsto := lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian
    (μ := P) (T := T) H h_meas (fun n => (G n).eval) h_eval_meas h_L2_diff
  -- Apply exists_itoIntegralL2_brownian.
  exact exists_itoIntegralL2_brownian (P := P) W hT G h_eq h_adapt h_cauchy_eval H
    h_norm_tendsto

/-- **L²-Itô isometry via existence (Brownian).** For progressively-measurable
`H ∈ L²(Ω × [0,T], dP ⊗ ds)`, there is a `(stochasticInt : Ω → ℝ) ∈ L²(P)`
satisfying the Itô L² isometry on `[0,T]`:
`∫⁻ ω, ‖stochasticInt ω‖₊² = ∫⁻ ω, ∫⁻ s in Icc 0 T, ‖H ω s‖₊²`.

This is a direct extraction from `exists_itoIntegralL2_brownian_progMeas`, with
`stochasticInt` exposed as an `Ω → ℝ` function (rather than an `Lp` element) plus
the AEStronglyMeasurable + isometry conjuncts.

This is the existence form of the Itô isometry — it does **not** define a single
`stochasticIntegral : ℝ → Ω → ℝ` across all `t`. Constructing such a unified
process (with the additional martingale + quadVar properties) is the strong-exists
task; this lemma delivers conjunct 3 (isometry) at fixed `T` axiom-cleanly. -/
theorem itoIsometry_brownian_existence
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ stochasticInt : Ω → ℝ,
      MeasureTheory.AEStronglyMeasurable stochasticInt P ∧
      ∫⁻ ω, (‖stochasticInt ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  obtain ⟨Mlp, h_isometry⟩ :=
    exists_itoIntegralL2_brownian_progMeas W hT H h_meas h_progMeas h_sq_int
  refine ⟨↑↑Mlp, (MeasureTheory.Lp.aestronglyMeasurable Mlp), ?_⟩
  -- ∫⁻ ‖↑↑Mlp ω‖₊² ∂P = eLpNorm² Mlp 2 P (via eLpNorm_nnreal_pow_eq_lintegral) = ∫⁻ ‖H‖² (h_isometry).
  rw [show (∫⁻ ω, (‖(↑↑Mlp : Ω → ℝ) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ) from ?_]
  · exact h_isometry
  -- Bridge eLpNorm² to lintegral_sq.
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := P) (p := (2 : NNReal)) (f := (↑↑Mlp : Ω → ℝ))
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl

/-- **Conjunct-3 strong-exists for Brownian Itô (isometry at all T).**

For progressively-measurable `H ∈ ⋂_T L²(Ω × [0,T], dP ⊗ ds)`, there is a process
`F : ℝ → Ω → ℝ` satisfying the Itô L² isometry at every `T > 0`:
`∫⁻ ω, ‖F T ω‖₊² = ∫⁻ ω, ∫⁻ s in Icc 0 T, ‖H ω s‖₊²`.

Construction: per-`T` independent extraction from
`exists_itoIntegralL2_brownian_progMeas`. The resulting `F` does **not** carry
the martingale property (different `T`'s give independent Lp witnesses), but
delivers the isometry conjunct.

This is the **conjunct 3** of `stochasticIntegral_strong_exists_brownian` —
the isometry-only existential. Pairing with future conjunct-1/2 lemmas
(L²-limit-of-martingales + L²-limit-of-quadVar) closes the full strong-exists. -/
theorem stochasticIntegral_isometry_only_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : ℝ → Ω → ℝ,
      ∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Per-T extraction: for each T, get an Ω → ℝ function with the isometry.
  refine ⟨fun T ω =>
    if hT : 0 < T then
      Classical.choose
        (itoIsometry_brownian_existence W hT H h_meas h_progMeas
          (h_sq_int_global T hT)) ω
    else 0, ?_⟩
  intro T hT
  simp only [dif_pos hT]
  exact (Classical.choose_spec
    (itoIsometry_brownian_existence W hT H h_meas h_progMeas
      (h_sq_int_global T hT))).2

/-- **CITED AXIOM: Unified L²-Itô integral with martingale + quadVar + isometry.**

For predictable square-integrable `H : Ω → ℝ → ℝ`, there exists a process
`F : ℝ → Ω → ℝ` and a filtration `Filt` such that:

* `F` is a martingale wrt `Filt`,
* `(F t)² − ∫_0^t H² ds` is a martingale wrt `Filt` (quadVar identity),
* `∫⁻ ω, ‖F T‖₊² ∂P = ∫⁻ ω, ∫⁻ s in [0, T], ‖H ω s‖₊² ∂volume ∂P` for every `T > 0`
  (L²-isometry).

`F` is the canonical L²-Itô integral `t ↦ ∫_0^t H_s dW_s`. The 3-conjunct strong
existence consolidates Karatzas–Shreve Thm 3.2.6.

**Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
Springer 1991, **Theorem 3.2.6** (unified martingale + quadratic variation +
L²-isometry of the L² Itô integral); Le Gall, J.-F. *Brownian Motion, Martingales
and Stochastic Calculus*, Springer 2016, **Theorem 5.4** + equation **(5.8)**
(correcting the previous "Theorem 5.13" citation — Le Gall 2016 p. 121
"Theorem 5.13" is Dambis–Dubins–Schwarz, not the L² Itô isometry; see red-team
finding H8 / P11).

**Standard proof outline**: Construct `F` as the L²-limit (across the natural
filtration's progressive σ-algebras) of `simpleIntegral W (G n) t` for an adapted
Cauchy approximating sequence `G n` (e.g., `predictableDyadicSimple_brownian`).
Each `simpleIntegral W (G n) ·` is a martingale (proven as
`martingale_simpleIntegral_brownian`). The L²-limit of martingales is a
martingale via L²-continuity of conditional expectation. The quadVar identity
holds at simple level (orthogonal-increments calculation: cross terms vanish,
diagonal gives `Δt`) and passes to the limit. The L²-isometry is preserved
through `Filter.limUnder` (already proven for the per-T case via
`itoIntegralLp_brownian_L2_isometry`).

**Replacement plan**: when the unified F-construction-across-all-t is fully
formalized (the simple-level partial isometry at varying t + L²-Cauchy at varying
t + cond-exp continuity application), this `axiom` becomes a `theorem`. Tracked
in `tools/cited_axioms.md` Tier 1. -/
axiom itoIsometry_brownian_unified_existence
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      (∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)

/-- The *L² Itô integral* `M_t = ∫_0^t H_s dW_s` against a Brownian motion `W`.

**Refactored** (UNIFIED, 2026-05-10): defined via `Classical.choose` on the
3-conjunct unified existence axiom `itoIsometry_brownian_unified_existence`.
The resulting `F : ℝ → Ω → ℝ` satisfies the L²-isometry at every `T > 0` AND
is a martingale (via the unified strong-exists). -/
noncomputable def stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  Classical.choose
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas h_sq_int_global) T

/-- **Itô L² isometry.**

  `𝔼[ (∫_0^T H_s dW_s)² ] = 𝔼[ ∫_0^T |H_s|² ds ]`

for predictable square-integrable `H`. ENNReal form (matches the dissertation's
`I02` style).

**Refactored** (Option β-prime, 2026-05-09): now extracts directly from
`stochasticIntegral_isometry_only_brownian` (axiom-clean) rather than the
sorry'd full strong-exists. Same statement, same hypotheses; downstream callers
unchanged. -/
theorem itoIsometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegral W H h_meas h_progMeas h_sq_int_global T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞))^2 ∂volume ∂P := by
  -- Extract conjunct 3 (isometry) from the unified existence.
  unfold stochasticIntegral
  exact (Classical.choose_spec
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
      h_sq_int_global)).choose_spec.2.2 T hT

/-- **Quadratic variation of the L² Itô integral.**

For predictable square-integrable `H`, the process `t ↦ (M_t)² − ∫_0^t |H_s|² ds`
is a martingale, where `M_t = ∫_0^t H_s dW_s`.

**Refactored** (UNIFIED, 2026-05-10): now PROVEN as a theorem (no longer a cited
axiom). Extracts conjunct 2 from `itoIsometry_brownian_unified_existence`. -/
theorem quadVar_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral W H h_meas h_progMeas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2)
        F P := by
  -- Extract Filt + conjunct 2 (martingale of F²-∫H²) from the unified existence.
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
      h_sq_int_global)).choose,
    (Classical.choose_spec
      (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
        h_sq_int_global)).choose_spec.2.1⟩

/-- **The L² Itô integral is a martingale.**

The Itô integral `M_t = ∫_0^t H_s dW_s` is a square-integrable continuous
martingale w.r.t. the natural filtration of `W`.

**Refactored** (UNIFIED, 2026-05-10): now PROVEN as a theorem (no longer a cited
axiom). Extracts conjunct 1 from `itoIsometry_brownian_unified_existence`. -/
theorem martingale_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral W H h_meas h_progMeas h_sq_int_global t) F P := by
  -- Extract Filt + conjunct 1 (martingale of F) from the unified existence.
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
      h_sq_int_global)).choose,
    (Classical.choose_spec
      (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
        h_sq_int_global)).choose_spec.1⟩

end LevyStochCalc.Brownian.Ito
