/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.PRPCell

/-!
# The predictable representation over a grid

Iterating the one-window statement over the cells of a grid: a square-integrable weight of mean
zero and orthogonal to every Itô integral is orthogonal to every character of the increments of a
Brownian motion along a grid.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Grid

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

/-- The character of the increments of `W` along the first `n` cells of a grid. -/
noncomputable def gridCharacter (W : LevyStochCalc.Brownian.BrownianMotion P) (τ : ℕ → ℝ)
    (lam : ℕ → ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  ∏ k ∈ Finset.range n,
    Complex.exp (((lam k * (W.W (τ (k + 1)) ω - W.W (τ k) ω) : ℝ) : ℂ) * Complex.I)

theorem norm_gridCharacter (W : LevyStochCalc.Brownian.BrownianMotion P) (τ lam : ℕ → ℝ)
    (n : ℕ) (ω : Ω) : ‖gridCharacter W τ lam n ω‖ = 1 := by
  rw [gridCharacter, norm_prod]
  exact Finset.prod_eq_one fun k _ => Complex.norm_exp_ofReal_mul_I _

/-- A grid that increases up to index `n` is monotone up to index `n`. -/
theorem grid_le {τ : ℕ → ℝ} {n : ℕ} (h : ∀ k, k < n → τ k ≤ τ (k + 1)) :
    ∀ {i j : ℕ}, i ≤ j → j ≤ n → τ i ≤ τ j := by
  intro i j hij hjn
  induction j with
  | zero => rw [Nat.le_zero.mp hij]
  | succ j ih =>
      rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hij) with hlt | heq
      · exact (ih (Nat.lt_succ_iff.mp hlt) (le_of_lt hjn)).trans
          (h j (Nat.lt_of_succ_le hjn))
      · rw [heq]

include hℱ in
/-- The character of the first `n` cells is measurable for the filtration at the `n`-th grid
point. -/
theorem measurable_gridCharacter {τ : ℕ → ℝ} {n : ℕ} (hτ : ∀ k, k < n → τ k ≤ τ (k + 1))
    (lam : ℕ → ℝ) : Measurable[ℱ (τ n)] (gridCharacter W τ lam n) := by
  refine Finset.measurable_prod _ fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  have hk1 : τ (k + 1) ≤ τ n := grid_le hτ hkn (le_refl n)
  have hk0 : τ k ≤ τ n := grid_le hτ hkn.le (le_refl n)
  have hW1 : Measurable[ℱ (τ n)] (W.W (τ (k + 1))) :=
    (hℱ.measurable _).mono (ℱ.mono hk1) le_rfl
  have hW0 : Measurable[ℱ (τ n)] (W.W (τ k)) := (hℱ.measurable _).mono (ℱ.mono hk0) le_rfl
  exact Complex.measurable_exp.comp
    ((Complex.measurable_ofReal.comp ((hW1.sub hW0).const_mul (lam k))).mul measurable_const)

include hℱ in
/-- **The grid induction.** A square-integrable weight of mean zero, orthogonal to every Itô
integral, is orthogonal to the character of the Brownian increments along any grid. -/
theorem pairing_gridCharacter_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (lam : ℕ → ℝ) :
    ∀ n : ℕ, (∀ k, k < n → τ k < τ (k + 1)) →
      ∫ ω, Z ω * gridCharacter W τ lam n ω ∂P = 0 := by
  intro n
  induction n with
  | zero =>
      intro _
      have h1 : ∀ ω : Ω, Z ω * gridCharacter W τ lam 0 ω = Z ω := by
        intro ω; rw [gridCharacter]; simp
      simpa only [h1] using hZ0
  | succ n ih =>
      intro hlt
      have hlt' : ∀ k, k < n → τ k < τ (k + 1) := fun k hk => hlt k (Nat.lt_succ_of_lt hk)
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt' k hk).le
      have hτn0 : 0 ≤ τ n := by
        rw [← hτ0]; exact grid_le hle' (Nat.zero_le n) le_rfl
      have hstep := pairing_cell_eq_zero (W := W) (ℱ := ℱ) (hℱ := hℱ) hℱ0 hnull hτn0
        (hlt n (Nat.lt_succ_self n)) hZm hZ2 hZp
        (V := gridCharacter W τ lam n)
        ((measurable_gridCharacter (hℱ := hℱ) hle' lam).mono (ℱ.le _) le_rfl)
        (Mv := 1) zero_le_one (fun ω => le_of_eq (norm_gridCharacter W τ lam n ω))
        (measurable_gridCharacter (hℱ := hℱ) hle' lam).stronglyMeasurable (ih hlt') (lam n)
      have hrw : ∀ ω : Ω, Z ω * gridCharacter W τ lam (n + 1) ω
          = Z ω * gridCharacter W τ lam n ω
            * Complex.exp (((lam n * (W.W (τ (n + 1)) ω - W.W (τ n) ω) : ℝ) : ℂ)
              * Complex.I) := by
        intro ω
        rw [gridCharacter, gridCharacter, Finset.prod_range_succ]
        ring
      simpa only [hrw] using hstep

/-- The character of the increments is the character of a single sum. -/
theorem gridCharacter_eq_exp (W : LevyStochCalc.Brownian.BrownianMotion P) (τ lam : ℕ → ℝ)
    (n : ℕ) (ω : Ω) :
    gridCharacter W τ lam n ω
      = Complex.exp (((∑ k ∈ Finset.range n,
          lam k * (W.W (τ (k + 1)) ω - W.W (τ k) ω) : ℝ) : ℂ) * Complex.I) := by
  rw [gridCharacter, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]

end Grid

section Abel

/-- **Abel summation.** A weighted sum of the values of a sequence vanishing at zero is a
weighted sum of its increments, with weights the tail sums. -/
theorem sum_tail_mul_sub (c : ℕ → ℝ) {Wv : ℕ → ℝ} (h0 : Wv 0 = 0) (n : ℕ) :
    ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
      = ∑ k ∈ Finset.Ico 1 (n + 1), c k * Wv k := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : ∀ k ∈ Finset.range (n + 1),
          (∑ j ∈ Finset.Ico (k + 1) (n + 2), c j) * (Wv (k + 1) - Wv k)
            = (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
              + c (n + 1) * (Wv (k + 1) - Wv k) := by
        intro k hk
        have hk' : k + 1 ≤ n + 1 := Finset.mem_range.mp hk
        rw [Finset.sum_Ico_succ_top hk', add_mul]
      rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib]
      have hlast : ∑ k ∈ Finset.range (n + 1),
          (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k)
          = ∑ k ∈ Finset.range n,
            (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) * (Wv (k + 1) - Wv k) := by
        rw [Finset.sum_range_succ]
        simp
      have htel : ∑ k ∈ Finset.range (n + 1), c (n + 1) * (Wv (k + 1) - Wv k)
          = c (n + 1) * Wv (n + 1) := by
        rw [← Finset.mul_sum, Finset.sum_range_sub, h0, sub_zero]
      rw [hlast, ih, htel]
      exact (Finset.sum_Ico_succ_top (by omega : 1 ≤ n + 1) _).symm

end Abel

section Values

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

include hℱ in
/-- **Value characters along a grid.** A square-integrable weight of mean zero, orthogonal to
every Itô integral, is orthogonal to every character of the values of `W` at the points of a
grid. -/
theorem pairing_value_character_eq_zero
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → ℝ) (n : ℕ) (hlt : ∀ k, k < n → τ k < τ (k + 1)) :
    ∫ ω, Z ω * Complex.exp (((∑ k ∈ Finset.Ico 1 (n + 1), c k * W.W (τ k) ω : ℝ) : ℂ)
      * Complex.I) ∂P = 0 := by
  have hkey := pairing_gridCharacter_eq_zero hℱ0 hnull hτ0 hZm hZ2 hZp hZ0
    (fun k => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j) n hlt
  refine Eq.trans (integral_congr_ae ?_) hkey
  filter_upwards [W.initial_zero] with ω hω
  have heq : (∑ k ∈ Finset.Ico 1 (n + 1), c k * W.W (τ k) ω)
      = ∑ k ∈ Finset.range n, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j)
          * (W.W (τ (k + 1)) ω - W.W (τ k) ω) :=
    (sum_tail_mul_sub c (Wv := fun k => W.W (τ k) ω) (by rw [hτ0]; exact hω) n).symm
  rw [gridCharacter_eq_exp, heq]

end Values

end LevyStochCalc.Brownian.Ito
