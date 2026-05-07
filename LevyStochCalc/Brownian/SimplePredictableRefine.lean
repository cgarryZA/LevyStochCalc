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

end LevyStochCalc.Brownian.Ito
