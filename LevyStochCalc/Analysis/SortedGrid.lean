/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic

/-!
# The increasing enumeration of a finite family of times

`sortedGrid S` lists the elements of a finite set `S ⊆ ℝ` in increasing order at the indices
`1, …, S.card`, and takes the value `0` at index `0` and beyond `S.card`. When every element of
`S` is positive it is strictly increasing on `{0, …, S.card}`.

A finite family of (coordinate, time) pairs carrying real weights is thereby rewritten as a sum
over such a grid: `posTimes` collects the strictly positive times of the family and `weightAt`
collects the weights sharing a coordinate and a time.
-/

namespace LevyStochCalc.Analysis

open Finset

/-- The increasing enumeration of `S`, extended by `0` at index `0` and beyond `S.card`. -/
noncomputable def sortedGrid (S : Finset ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if h : n < S.card then S.orderEmbOfFin rfl ⟨n, h⟩ else 0

variable (S : Finset ℝ)

@[simp] theorem sortedGrid_zero : sortedGrid S 0 = 0 := rfl

theorem sortedGrid_succ_of_lt {n : ℕ} (h : n < S.card) :
    sortedGrid S (n + 1) = S.orderEmbOfFin rfl ⟨n, h⟩ := by
  simp only [sortedGrid]
  rw [dif_pos h]

theorem sortedGrid_succ_mem {n : ℕ} (h : n < S.card) : sortedGrid S (n + 1) ∈ S := by
  rw [sortedGrid_succ_of_lt S h]
  exact S.orderEmbOfFin_mem rfl _

/-- On a set of positive reals the enumeration is strictly increasing from the origin. -/
theorem sortedGrid_lt_succ (hpos : ∀ x ∈ S, 0 < x) {n : ℕ} (hn : n < S.card) :
    sortedGrid S n < sortedGrid S (n + 1) := by
  cases n with
  | zero =>
      rw [sortedGrid_zero]
      exact hpos _ (sortedGrid_succ_mem S hn)
  | succ j =>
      have hj : j < S.card := Nat.lt_of_succ_lt hn
      rw [sortedGrid_succ_of_lt S hj, sortedGrid_succ_of_lt S hn]
      exact (S.orderEmbOfFin rfl).strictMono (by exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self j))

/-- A sum over `S` is a sum along the grid indices `1, …, S.card`. -/
theorem sum_Ico_sortedGrid {M : Type*} [AddCommMonoid M] (f : ℝ → M) :
    ∑ k ∈ Finset.Ico 1 (S.card + 1), f (sortedGrid S k) = ∑ x ∈ S, f x := by
  have h1 : ∑ k ∈ Finset.Ico 1 (S.card + 1), f (sortedGrid S k)
      = ∑ i ∈ Finset.range S.card, f (sortedGrid S (i + 1)) := by
    rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
    exact Finset.sum_congr rfl fun i _ => by rw [Nat.add_comm]
  have h2 : ∑ i ∈ Finset.range S.card, f (sortedGrid S (i + 1))
      = ∑ i : Fin S.card, f (S.orderEmbOfFin rfl i) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => f (sortedGrid S (i + 1))) S.card]
    exact Finset.sum_congr rfl fun i _ => by rw [sortedGrid_succ_of_lt S i.isLt]
  have h3 : ∑ i : Fin S.card, f (S.orderEmbOfFin rfl i) = ∑ x ∈ S, f x := by
    rw [← Finset.sum_coe_sort S f]
    exact Fintype.sum_equiv (S.orderIsoOfFin rfl).toEquiv _ _ fun i =>
      congrArg f (Finset.coe_orderIsoOfFin_apply S rfl i).symm
  rw [h1, h2, h3]

variable {d : ℕ} {T : ℝ}

/-- The strictly positive times occurring in a finite family of (coordinate, time) pairs. -/
noncomputable def posTimes (F : Finset (Fin d × Set.Iic T)) : Finset ℝ :=
  (F.filter fun p => 0 < (p.2 : ℝ)).image fun p => (p.2 : ℝ)

theorem pos_of_mem_posTimes {F : Finset (Fin d × Set.Iic T)} {x : ℝ} (hx : x ∈ posTimes F) :
    0 < x := by
  rw [posTimes, Finset.mem_image] at hx
  obtain ⟨p, hp, rfl⟩ := hx
  exact (Finset.mem_filter.mp hp).2

theorem mem_posTimes {F : Finset (Fin d × Set.Iic T)} {p : Fin d × Set.Iic T} (hp : p ∈ F)
    (hx : 0 < (p.2 : ℝ)) : ((p.2 : ℝ)) ∈ posTimes F :=
  Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, hx⟩, rfl⟩

theorem le_of_mem_posTimes {F : Finset (Fin d × Set.Iic T)} {x : ℝ} (hx : x ∈ posTimes F) :
    x ≤ T := by
  rw [posTimes, Finset.mem_image] at hx
  obtain ⟨p, -, rfl⟩ := hx
  exact p.2.2

/-- The total weight carried by the coordinate `i` at the time `x`. -/
noncomputable def weightAt (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ) (x : ℝ) (i : Fin d) :
    ℝ :=
  ∑ p : F, if p.1.1 = i ∧ (p.1.2 : ℝ) = x then w p else 0

theorem sum_weightAt_mul (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ) (v : Fin d → ℝ → ℝ)
    (x : ℝ) :
    (∑ i, weightAt F w x i * v i x)
      = ∑ p : F, (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) := by
  have h1 : ∀ i : Fin d, weightAt F w x i * v i x
      = ∑ p : F, (if p.1.1 = i then
          (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) else 0) := by
    intro i
    rw [weightAt, Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases hc : p.1.1 = i
    · by_cases hx : (p.1.2 : ℝ) = x
      · simp [hc, hx]
      · simp [hc, hx]
    · simp [hc]
  rw [Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h1 i, Finset.sum_comm]
  exact Finset.sum_congr rfl fun p _ => by simp

/-- **Sorting a weighted family of times into a grid.** A finite family of (coordinate, time)
pairs with real weights, whose values vanish at nonpositive times, sums to a double sum over the
coordinates and the increasing enumeration of the positive times of the family. -/
theorem sum_weight_eq_sum_grid (F : Finset (Fin d × Set.Iic T)) (w : F → ℝ)
    (v : Fin d → ℝ → ℝ) (hv : ∀ p : F, (p.1.2 : ℝ) ≤ 0 → v p.1.1 (p.1.2 : ℝ) = 0)
    {S : Finset ℝ} (hS : posTimes F ⊆ S) (hSpos : ∀ x ∈ S, 0 < x) :
    ∑ p : F, v p.1.1 (p.1.2 : ℝ) * w p
      = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          weightAt F w (sortedGrid S k) i * v i (sortedGrid S k) := by
  calc ∑ p : F, v p.1.1 (p.1.2 : ℝ) * w p
      = ∑ p : F, (if (p.1.2 : ℝ) ∈ S then w p * v p.1.1 (p.1.2 : ℝ) else 0) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        by_cases hpos : 0 < (p.1.2 : ℝ)
        · rw [if_pos (hS (mem_posTimes p.2 hpos))]
          exact mul_comm _ _
        · rw [if_neg fun hmem => absurd (hSpos _ hmem) hpos,
            hv p (not_lt.mp hpos), zero_mul]
    _ = ∑ p : F, ∑ x ∈ S,
          (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) :=
        Finset.sum_congr rfl fun p _ => (Finset.sum_ite_eq S ((p.1.2 : ℝ))
          fun _ => w p * v p.1.1 (p.1.2 : ℝ)).symm
    _ = ∑ x ∈ S, ∑ p : F,
          (if (p.1.2 : ℝ) = x then w p * v p.1.1 (p.1.2 : ℝ) else 0) := Finset.sum_comm
    _ = ∑ x ∈ S, ∑ i, weightAt F w x i * v i x :=
        Finset.sum_congr rfl fun x _ => (sum_weightAt_mul F w v x).symm
    _ = ∑ k ∈ Finset.Ico 1 (S.card + 1), ∑ i,
          weightAt F w (sortedGrid S k) i * v i (sortedGrid S k) :=
        (sum_Ico_sortedGrid _ fun x => ∑ i, weightAt F w x i * v i x).symm
    _ = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          weightAt F w (sortedGrid S k) i * v i (sortedGrid S k) :=
        Finset.sum_comm

/-- The last point of the sorted grid of a nonempty finite set belongs to it. -/
theorem sortedGrid_card_mem {S : Finset ℝ} (hS : S.Nonempty) : sortedGrid S S.card ∈ S := by
  obtain ⟨x, hx⟩ := hS
  obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by
    have : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
    omega⟩
  have hns : n < S.card := by omega
  rw [hn]
  exact sortedGrid_succ_mem S hns

/-- Every element of a nonempty finite set is at most the last point of its sorted grid. -/
theorem le_sortedGrid_card {S : Finset ℝ} {x : ℝ} (hx : x ∈ S) :
    x ≤ sortedGrid S S.card := by
  have hpos : 0 < S.card := Finset.card_pos.mpr ⟨x, hx⟩
  set n := S.card - 1 with hn
  have hcard : S.card = n + 1 := by omega
  have hns : n < S.card := by omega
  have hgrid : sortedGrid S S.card = S.orderEmbOfFin rfl ⟨n, hns⟩ := by
    conv_lhs => rw [hcard]
    exact sortedGrid_succ_of_lt S hns
  rw [hgrid]
  obtain ⟨j, hj⟩ : ∃ j : Fin S.card, S.orderEmbOfFin rfl j = x := by
    have hmem : x ∈ Set.range (S.orderEmbOfFin (rfl : S.card = S.card)) := by
      rw [Finset.range_orderEmbOfFin]
      exact hx
    exact hmem
  rw [← hj]
  have hjle : (j : ℕ) ≤ n := by
    have := j.isLt
    omega
  exact (S.orderEmbOfFin rfl).monotone (Fin.le_def.mpr hjle)

end LevyStochCalc.Analysis
