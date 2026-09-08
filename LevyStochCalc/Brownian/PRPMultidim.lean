/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.PRPGrid
import LevyStochCalc.Brownian.ItoDriverLinear

/-!
# One window of the multidimensional Brownian predictable representation

A weight orthogonal to every coordinate's Itô integrals is orthogonal to the integrals against
any unit linear combination of the coordinates, so the one-window statement transfers, and a
multidimensional cell character is a scalar character of the combination.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- Orthogonality to each coordinate's Itô integrals gives orthogonality to the integrals
against a unit linear combination. -/
theorem perpItoIntegrals_combineBM (W : Multidim.MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱB : IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    {Z : Ω → ℂ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z) :
    PerpItoIntegrals (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB Z := by
  constructor
  intro K hm hp hq t ht
  have hlin := stochasticIntegralBrownian_combineBM W hc ℱ hℱB hℱi K hm hp hq ht.le
  have hint : ∀ i : Fin d, Integrable
      (fun ω => Z ω * ((stochasticIntegralBrownian (W.W i) ℱ (hℱi i) K hm hp hq t ω : ℝ) : ℂ))
      P := fun i =>
    hZ2.integrable_mul (memLp_ofReal (stochasticIntegralBrownian_memLp (W.W i) ℱ (hℱi i)
      K hm hp hq t))
  have hcong : ∫ ω, Z ω * ((stochasticIntegralBrownian
        (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB K hm hp hq t ω : ℝ) : ℂ) ∂P
      = ∫ ω, ∑ i, ((c i : ℝ) : ℂ)
        * (Z ω * ((stochasticIntegralBrownian (W.W i) ℱ (hℱi i) K hm hp hq t ω : ℝ) : ℂ)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hlin] with ω hω
    rw [hω]
    push_cast
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hcong, integral_finsetSum _ fun i _ => (hint i).const_mul _]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [integral_const_mul, (hperp i).perp K hm hp hq t ht, mul_zero]

/-- **One window, multidimensional.** A square-integrable weight orthogonal to every
coordinate's Itô integrals, times a bounded weight measurable before the window and of mean
zero, is orthogonal to the character of the vector of Brownian increments across the window. -/
theorem pairing_cell_multidim_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    (hZV : ∫ ω, Z ω * V ω ∂P = 0) (lam : Fin d → ℝ) :
    ∫ ω, Z ω * V ω * Complex.exp
      (((∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω) : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
  classical
  by_cases hzero : ∀ i, lam i = 0
  · have h1 : ∀ ω : Ω, Complex.exp
        (((∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω) : ℝ) : ℂ) * Complex.I) = 1 := by
      intro ω
      have hs : (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω)) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_mul]
      rw [hs]
      simp
    simpa only [h1, mul_one] using hZV
  · obtain ⟨j, hj⟩ := not_forall.mp hzero
    have hsum_pos : 0 < ∑ i, lam i ^ 2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
      rcases lt_trichotomy (lam j) 0 with h | h | h
      · nlinarith
      · exact absurd h hj
      · nlinarith
    have hn_pos : 0 < Real.sqrt (∑ i, lam i ^ 2) := Real.sqrt_pos.mpr hsum_pos
    have hc : ∑ i, (lam i / Real.sqrt (∑ k, lam k ^ 2)) ^ 2 = 1 := by
      simp only [div_pow]
      rw [← Finset.sum_div, Real.sq_sqrt hsum_pos.le]
      exact div_self hsum_pos.ne'
    have hexp : ∀ ω : Ω, (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω))
        = Real.sqrt (∑ k, lam k ^ 2)
          * (Multidim.MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) b ω
            - Multidim.MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) a ω) := by
      intro ω
      rw [Multidim.MultidimBrownianMotion.combine_sub, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have hcell := pairing_cell_eq_zero (W := Multidim.MultidimBrownianMotion.combineBM W hc)
      (ℱ := ℱ) (hℱ := hℱB hc) hℱ0 hnull ha hab hZm hZ2
      (perpItoIntegrals_combineBM W hc ℱ (hℱB hc) hℱi hZ2 hperp)
      hVm hMv0 hVb hVa hZV (Real.sqrt (∑ k, lam k ^ 2))
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) hcell
    simp only [hexp ω]
    rfl

/-- The character of the vector of increments of `W` along the first `n` cells of a grid. -/
noncomputable def gridCharacterMultidim (W : Multidim.MultidimBrownianMotion P d) (τ : ℕ → ℝ)
    (lam : ℕ → Fin d → ℝ) (n : ℕ) (ω : Ω) : ℂ :=
  ∏ k ∈ Finset.range n, Complex.exp
    (((∑ i, lam k i * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω) : ℝ) : ℂ) * Complex.I)

theorem norm_gridCharacterMultidim (W : Multidim.MultidimBrownianMotion P d) (τ : ℕ → ℝ)
    (lam : ℕ → Fin d → ℝ) (n : ℕ) (ω : Ω) : ‖gridCharacterMultidim W τ lam n ω‖ = 1 := by
  rw [gridCharacterMultidim, norm_prod]
  exact Finset.prod_eq_one fun k _ => Complex.norm_exp_ofReal_mul_I _

/-- The character of the first `n` cells is measurable for the filtration at the `n`-th grid
point. -/
theorem measurable_gridCharacterMultidim (W : Multidim.MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    {τ : ℕ → ℝ} {n : ℕ} (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) (lam : ℕ → Fin d → ℝ) :
    Measurable[ℱ (τ n)] (gridCharacterMultidim W τ lam n) := by
  refine Finset.measurable_prod _ fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  have hk1 : τ (k + 1) ≤ τ n := grid_le hτ hkn (le_refl n)
  have hk0 : τ k ≤ τ n := grid_le hτ hkn.le (le_refl n)
  refine Complex.measurable_exp.comp ((Complex.measurable_ofReal.comp ?_).mul measurable_const)
  refine Finset.measurable_sum _ fun i _ => Measurable.const_mul ?_ _
  exact (((hℱi i).measurable _).mono (ℱ.mono hk1) le_rfl).sub
    (((hℱi i).measurable _).mono (ℱ.mono hk0) le_rfl)

/-- **The multidimensional grid induction.** -/
theorem pairing_gridCharacterMultidim_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (lam : ℕ → Fin d → ℝ) :
    ∀ n : ℕ, (∀ k, k < n → τ k < τ (k + 1)) →
      ∫ ω, Z ω * gridCharacterMultidim W τ lam n ω ∂P = 0 := by
  intro n
  induction n with
  | zero =>
      intro _
      have h1 : ∀ ω : Ω, Z ω * gridCharacterMultidim W τ lam 0 ω = Z ω := by
        intro ω; rw [gridCharacterMultidim]; simp
      simpa only [h1] using hZ0
  | succ n ih =>
      intro hlt
      have hlt' : ∀ k, k < n → τ k < τ (k + 1) := fun k hk => hlt k (Nat.lt_succ_of_lt hk)
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt' k hk).le
      have hτn0 : 0 ≤ τ n := by
        rw [← hτ0]; exact grid_le hle' (Nat.zero_le n) le_rfl
      have hstep := pairing_cell_multidim_eq_zero W ℱ hℱi hℱB hℱ0 hnull hτn0
        (hlt n (Nat.lt_succ_self n)) hZm hZ2 hperp
        (V := gridCharacterMultidim W τ lam n)
        ((measurable_gridCharacterMultidim W hℱi hle' lam).mono (ℱ.le _) le_rfl)
        (Mv := 1) zero_le_one
        (fun ω => le_of_eq (norm_gridCharacterMultidim W τ lam n ω))
        (measurable_gridCharacterMultidim W hℱi hle' lam).stronglyMeasurable (ih hlt') (lam n)
      have hrw : ∀ ω : Ω, Z ω * gridCharacterMultidim W τ lam (n + 1) ω
          = Z ω * gridCharacterMultidim W τ lam n ω
            * Complex.exp (((∑ i, lam n i
                * ((W.W i).W (τ (n + 1)) ω - (W.W i).W (τ n) ω) : ℝ) : ℂ) * Complex.I) := by
        intro ω
        rw [gridCharacterMultidim, gridCharacterMultidim, Finset.prod_range_succ]
        ring
      simpa only [hrw] using hstep

/-- The character of the increments is the character of a single sum. -/
theorem gridCharacterMultidim_eq_exp (W : Multidim.MultidimBrownianMotion P d) (τ : ℕ → ℝ)
    (lam : ℕ → Fin d → ℝ) (n : ℕ) (ω : Ω) :
    gridCharacterMultidim W τ lam n ω
      = Complex.exp (((∑ k ∈ Finset.range n, ∑ i, lam k i
          * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω) : ℝ) : ℂ) * Complex.I) := by
  rw [gridCharacterMultidim, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]

/-- **Value characters along a grid, multidimensional.** A square-integrable weight of mean zero,
orthogonal to every coordinate's Itô integrals, is orthogonal to every character of the values of
the coordinates at the points of a grid. -/
theorem pairing_value_characterMultidim_eq_zero (W : Multidim.MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {Z : Ω → ℂ} (hZm : Measurable Z) (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) Z)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) :
    ∫ ω, Z ω * Complex.exp (((∑ i, ∑ k ∈ Finset.Ico 1 (n + 1),
      c k i * (W.W i).W (τ k) ω : ℝ) : ℂ) * Complex.I) ∂P = 0 := by
  have hkey := pairing_gridCharacterMultidim_eq_zero W ℱ hℱi hℱB hℱ0 hnull hτ0 hZm hZ2 hperp hZ0
    (fun k i => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i) n hlt
  refine Eq.trans (integral_congr_ae ?_) hkey
  have hinit : ∀ᵐ ω ∂P, ∀ i : Fin d, (W.W i).W 0 ω = 0 :=
    ae_all_iff.mpr fun i => (W.W i).initial_zero
  filter_upwards [hinit] with ω hω
  have heq : (∑ k ∈ Finset.range n, ∑ i, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i)
        * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω))
      = ∑ i, ∑ k ∈ Finset.Ico 1 (n + 1), c k i * (W.W i).W (τ k) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      sum_tail_mul_sub (fun k => c k i) (Wv := fun k => (W.W i).W (τ k) ω)
        (by rw [hτ0]; exact hω i) n
  rw [gridCharacterMultidim_eq_exp, heq]

end LevyStochCalc.Brownian.Ito



