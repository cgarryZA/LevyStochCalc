/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellComplex
import LevyStochCalc.Brownian.PRPGrid

/-!
# The joint character of a grid of cells

Counts are additive over the cells of a grid, so the Poisson character at a grid point is the
product of the characters of the families cut by the cells. Pairing that product with the
character of the Brownian increments along the same grid gives the joint grid character, which
the induction of the joint predictable representation consumes one cell at a time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section CellFamily

/-- The family cut to the `k`-th cell of a grid. -/
def cellFam (Bfam : ι → Set (ℝ × E)) (τ : ℕ → ℝ) (k : ℕ) : ι → Set (ℝ × E) :=
  fun j => Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ Set.univ

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [Fintype ι] in
theorem measurableSet_cellFam {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (τ : ℕ → ℝ) (k : ℕ) (j : ι) : MeasurableSet (cellFam Bfam τ k j) :=
  (hBm j).inter (measurableSet_Ioc.prod MeasurableSet.univ)

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] [Fintype ι] in
theorem cellFam_subset {Bfam : ι → Set (ℝ × E)} {A : Set E} {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) (τ : ℕ → ℝ) (k : ℕ) (j : ι) :
    cellFam Bfam τ k j ⊆ Set.Ioc (τ k) (τ (k + 1)) ×ˢ A := by
  rintro p ⟨hpB, hp⟩
  exact ⟨hp.1, (hBsub j hpB).2⟩

omit [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] [Fintype ι] in
/-- Cutting the `k`-th cell's family to the window up to the cell's right endpoint returns the
part of the family in the cell. -/
theorem cellFam_inter_Ioc {Bfam : ι → Set (ℝ × E)} {τ : ℕ → ℝ} {k : ℕ} (hτk : 0 ≤ τ k)
    (j : ι) :
    cellFam Bfam τ k j ∩ Set.Ioc (0 : ℝ) (τ (k + 1)) ×ˢ (Set.univ : Set E)
      = Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E) := by
  refine Set.Subset.antisymm (fun p hp => ⟨hp.1.1, hp.1.2⟩) (fun p hp => ⟨hp, ?_⟩)
  exact ⟨⟨lt_of_le_of_lt hτk hp.2.1.1, hp.2.1.2⟩, Set.mem_univ _⟩

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **Counts are additive over the cells of a grid.** -/
theorem count_inter_Ioc_sum (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) (ω : Ω) :
    ∀ n : ℕ, (∀ k, k < n → τ k ≤ τ (k + 1)) →
      N.N ω (B ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ (Set.univ : Set E))
        = ∑ k ∈ Finset.range n,
            N.N ω (B ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E)) := by
  intro n
  induction n with
  | zero =>
      intro _
      rw [hτ0, Set.Ioc_self, Set.empty_prod, Set.inter_empty]
      simp
  | succ n ih =>
      intro hle
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => hle k (Nat.lt_succ_of_lt hk)
      have hτn : 0 ≤ τ n := by
        rw [← hτ0]
        clear ih
        induction n with
        | zero => exact le_rfl
        | succ m ihm =>
            exact (ihm (fun k hk => hle k (Nat.lt_succ_of_lt hk))
              (fun k hk => hle' k (Nat.lt_succ_of_lt hk))).trans
              (hle m (Nat.lt_succ_of_lt (Nat.lt_succ_self m)))
      have hsplit : Set.Ioc (0 : ℝ) (τ (n + 1))
          = Set.Ioc (0 : ℝ) (τ n) ∪ Set.Ioc (τ n) (τ (n + 1)) :=
        (Set.Ioc_union_Ioc_eq_Ioc hτn (hle n (Nat.lt_succ_self n))).symm
      have hdisj : Disjoint (B ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ (Set.univ : Set E))
          (B ∩ Set.Ioc (τ n) (τ (n + 1)) ×ˢ (Set.univ : Set E)) := by
        refine Set.disjoint_left.mpr fun p hp hq => ?_
        exact absurd hq.2.1.1 (not_lt.mpr hp.2.1.2)
      have hm2 : MeasurableSet (B ∩ Set.Ioc (τ n) (τ (n + 1)) ×ˢ (Set.univ : Set E)) :=
        hB.inter (measurableSet_Ioc.prod MeasurableSet.univ)
      rw [hsplit, Set.union_prod, Set.inter_union_distrib_left,
        measure_union hdisj hm2, ih hle', Finset.sum_range_succ]

/-- Every grid point of a grid starting at the origin is nonnegative. -/
theorem grid_nonneg {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) {n : ℕ} (hτ : ∀ k, k < n → τ k ≤ τ (k + 1))
    {k : ℕ} (hk : k ≤ n) : 0 ≤ τ k := by
  rw [← hτ0]
  exact grid_le hτ (Nat.zero_le k) hk

/-- **The Poisson character factorises over the cells of a grid.** -/
theorem ae_charAt_eq_prod_cellFam (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ}
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {τ : ℕ → ℝ} (hτ0 : τ 0 = 0) {n : ℕ}
    (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) :
    ∀ᵐ ω ∂P, charAt N w Bfam (τ n) ω
      = ∏ k ∈ Finset.range n, charAt N w (cellFam Bfam τ k) (τ (k + 1)) ω := by
  filter_upwards [count_Ioc_ne_top N hA hAν T] with ω hfin
  have hne : ∀ (j : ι) (k : ℕ),
      N.N ω (Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E)) ≠ ⊤ := by
    intro j k
    refine ne_top_of_le_ne_top hfin (measure_mono ?_)
    rintro p ⟨hpB, -⟩
    exact hBsub j hpB
  have hcount : ∀ j : ι,
      (N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ (Set.univ : Set E))).toReal
        = ∑ k ∈ Finset.range n,
            (N.N ω (Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E))).toReal := by
    intro j
    rw [count_inter_Ioc_sum N (hBm j) hτ0 ω n hτ, ENNReal.toReal_sum]
    exact fun k _ => hne j k
  have hswap : (∑ j, w j * (N.N ω (Bfam j ∩ Set.Ioc (0 : ℝ) (τ n) ×ˢ
        (Set.univ : Set E))).toReal)
      = ∑ k ∈ Finset.range n, ∑ j, w j *
          (N.N ω (Bfam j ∩ Set.Ioc (τ k) (τ (k + 1)) ×ˢ (Set.univ : Set E))).toReal := by
    simp_rw [hcount, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [charAt, hswap, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun k hk => ?_
  rw [charAt]
  congr 2
  refine Complex.ofReal_inj.mpr (Finset.sum_congr rfl fun j _ => ?_)
  rw [cellFam_inter_Ioc (grid_nonneg hτ0 hτ (Finset.mem_range.mp hk).le) j]

end CellFamily

section JointGrid

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The joint character of the Brownian increments and the Poisson counts along the first `n`
cells of a grid. -/
noncomputable def jointGridCharacter (W : LevyStochCalc.Brownian.BrownianMotion P)
    (N : PoissonRandomMeasure P ν) (τ lam : ℕ → ℝ) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (n : ℕ) (ω : Ω) : ℂ :=
  ∏ k ∈ Finset.range n,
    (Complex.exp (Complex.I * ((lam k * (W.W (τ (k + 1)) ω - W.W (τ k) ω) : ℝ) : ℂ))
      * charAt N w (cellFam Bfam τ k) (τ (k + 1)) ω)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_jointGridCharacter (W : LevyStochCalc.Brownian.BrownianMotion P)
    (N : PoissonRandomMeasure P ν) (τ lam : ℕ → ℝ) (w : ι → ℝ) (Bfam : ι → Set (ℝ × E))
    (n : ℕ) (ω : Ω) : ‖jointGridCharacter W N τ lam w Bfam n ω‖ = 1 := by
  rw [jointGridCharacter, norm_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, charAt,
    Complex.norm_exp_I_mul_ofReal, one_mul]

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The joint character of the first `n` cells is measurable for the filtration at the `n`-th
grid point. -/
theorem measurable_jointGridCharacter {W : LevyStochCalc.Brownian.BrownianMotion P}
    (hℱW : IsBrownianFiltration W ℱ) (N : PoissonRandomMeasure P ν)
    (hℱN : IsPoissonFiltration N ℱ) {τ : ℕ → ℝ} {n : ℕ}
    (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) (lam : ℕ → ℝ) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) :
    Measurable[ℱ (τ n)] (jointGridCharacter W N τ lam w Bfam n) := by
  refine Finset.measurable_prod _ fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  have hk1 : τ (k + 1) ≤ τ n := grid_le hτ hkn (le_refl n)
  have hk0 : τ k ≤ τ n := grid_le hτ hkn.le (le_refl n)
  have hW1 : Measurable[ℱ (τ n)] (W.W (τ (k + 1))) :=
    (hℱW.measurable _).mono (ℱ.mono hk1) le_rfl
  have hW0 : Measurable[ℱ (τ n)] (W.W (τ k)) := (hℱW.measurable _).mono (ℱ.mono hk0) le_rfl
  have hbm : Measurable[ℱ (τ n)] fun ω =>
      Complex.exp (Complex.I * ((lam k * (W.W (τ (k + 1)) ω - W.W (τ k) ω) : ℝ) : ℂ)) :=
    Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp ((hW1.sub hW0).const_mul (lam k))))
  have hcount : ∀ j : ι, Measurable[ℱ (τ n)] fun ω =>
      N.N ω (cellFam Bfam τ k j ∩ Set.Ioc (0 : ℝ) (τ (k + 1)) ×ˢ (Set.univ : Set E)) := by
    intro j
    refine (hℱN.measurable (t := τ (k + 1)) ?_ ?_).mono (ℱ.mono hk1) le_rfl
    · exact fun p hp => ⟨hp.2.1.2, Set.mem_univ _⟩
    · exact (measurableSet_cellFam hBm τ k j).inter
        (measurableSet_Ioc.prod MeasurableSet.univ)
  have hpm : Measurable[ℱ (τ n)] (charAt N w (cellFam Bfam τ k) (τ (k + 1))) := by
    refine Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun j _ => ?_)))
    exact ((hcount j).ennreal_toReal).const_mul (w j)
  exact hbm.mul hpm

end JointGrid

end LevyStochCalc.Driver
