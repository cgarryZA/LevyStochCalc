/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointGrid
import LevyStochCalc.Brownian.PRPMultidim

/-!
# The mixed cell lemma for a multidimensional Brownian motion

A character of a vector of Brownian increments across a cell is the character of the increment
of a unit combination, scaled by the length of the weight vector, so the mixed cell lemma for a
single Brownian motion carries over to the multidimensional driver with the Poisson character
riding along unchanged.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι]

section Cell

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- **One cell, multidimensional.** The pairing of a real weight orthogonal to every
coordinate's Itô integrals and to every compensated integral, times a bounded complex factor
measurable before the cell and of vanishing mean, with the character of the vector of Brownian
increments across the cell and the Poisson character at its right endpoint, vanishes. -/
theorem pairing_cell_multidim_joint_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℂ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, ‖V ω‖ ≤ Mv) (hZV : ∫ ω, ((Z ω : ℝ) : ℂ) * V ω ∂P = 0) (lam : Fin d → ℝ) :
    ∫ ω, ((Z ω : ℝ) : ℂ) * V ω
      * (Complex.exp (Complex.I
          * ((∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω) : ℝ) : ℂ))
        * charAt N w Bfam b ω) ∂P = 0 := by
  classical
  by_cases hzero : ∀ i, lam i = 0
  · set c : Fin d → ℝ := fun i => if i = (⟨0, hd⟩ : Fin d) then 1 else 0 with hcdef
    have hc : ∑ i, c i ^ 2 = 1 := by
      simp [hcdef]
    have hcell := pairing_cell_joint_eq_zero N hℱN (MultidimBrownianMotion.combineBM W hc)
      (hℱB hc) hℱ0 hnull ha hab 0 hT hbT hA hAν w hBm hBsub he₀ hZ2
      (perpItoIntegrals_combineBM W hc ℱ (hℱB hc) hℱi (memLp_ofReal hZ2) hperp)
      hZcomp hVa hMv0 hVb hZV
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) hcell
    have hs : (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω)) = 0 :=
      Finset.sum_eq_zero fun i _ => by rw [hzero i, zero_mul]
    simp [hs]
  · obtain ⟨j, hj⟩ := not_forall.mp hzero
    have hsum_pos : 0 < ∑ i, lam i ^ 2 := by
      refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
      rcases lt_trichotomy (lam j) 0 with h | h | h
      · nlinarith
      · exact absurd h hj
      · nlinarith
    have hc : ∑ i, (lam i / Real.sqrt (∑ k, lam k ^ 2)) ^ 2 = 1 := by
      simp only [div_pow]
      rw [← Finset.sum_div, Real.sq_sqrt hsum_pos.le]
      exact div_self hsum_pos.ne'
    have hexp : ∀ ω : Ω, (∑ i, lam i * ((W.W i).W b ω - (W.W i).W a ω))
        = Real.sqrt (∑ k, lam k ^ 2)
          * (MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) b ω
            - MultidimBrownianMotion.combine W
              (fun i => lam i / Real.sqrt (∑ k, lam k ^ 2)) a ω) := by
      intro ω
      rw [MultidimBrownianMotion.combine_sub, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have hcell := pairing_cell_joint_eq_zero N hℱN (MultidimBrownianMotion.combineBM W hc)
      (hℱB hc) hℱ0 hnull ha hab (Real.sqrt (∑ k, lam k ^ 2)) hT hbT hA hAν w hBm hBsub he₀
      hZ2 (perpItoIntegrals_combineBM W hc ℱ (hℱB hc) hℱi (memLp_ofReal hZ2) hperp)
      hZcomp hVa hMv0 hVb hZV
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)) hcell
    simp only [hexp ω]
    rfl

end Cell

section Grid

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)

/-- The joint character of the vector of Brownian increments and the Poisson counts along the
first `n` cells of a grid. -/
noncomputable def jointGridCharacterMultidim (τ : ℕ → ℝ) (lam : ℕ → Fin d → ℝ) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (n : ℕ) (ω : Ω) : ℂ :=
  ∏ k ∈ Finset.range n,
    (Complex.exp (Complex.I
        * ((∑ i, lam k i * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω) : ℝ) : ℂ))
      * charAt N w (cellFam Bfam τ k) (τ (k + 1)) ω)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem norm_jointGridCharacterMultidim (τ : ℕ → ℝ) (lam : ℕ → Fin d → ℝ) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (n : ℕ) (ω : Ω) :
    ‖jointGridCharacterMultidim W N τ lam w Bfam n ω‖ = 1 := by
  rw [jointGridCharacterMultidim, norm_prod]
  refine Finset.prod_eq_one fun k _ => ?_
  rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, charAt,
    Complex.norm_exp_I_mul_ofReal, one_mul]

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- The joint character of the first `n` cells is measurable for the filtration at the `n`-th
grid point. -/
theorem measurable_jointGridCharacterMultidim {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ) (hℱN : IsPoissonFiltration N ℱ)
    {τ : ℕ → ℝ} {n : ℕ} (hτ : ∀ k, k < n → τ k ≤ τ (k + 1)) (lam : ℕ → Fin d → ℝ) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j)) :
    Measurable[ℱ (τ n)] (jointGridCharacterMultidim W N τ lam w Bfam n) := by
  refine Finset.measurable_prod _ fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  have hk1 : τ (k + 1) ≤ τ n := grid_le hτ hkn (le_refl n)
  have hk0 : τ k ≤ τ n := grid_le hτ hkn.le (le_refl n)
  have hbm : Measurable[ℱ (τ n)] fun ω => Complex.exp (Complex.I
      * ((∑ i, lam k i * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω) : ℝ) : ℂ)) := by
    refine Complex.measurable_exp.comp (measurable_const.mul
      (Complex.measurable_ofReal.comp (Finset.measurable_sum _ fun i _ => ?_)))
    exact Measurable.const_mul ((((hℱi i).measurable _).mono (ℱ.mono hk1) le_rfl).sub
      (((hℱi i).measurable _).mono (ℱ.mono hk0) le_rfl)) _
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

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- **The multidimensional joint grid induction.** -/
theorem pairing_jointGridCharacterMultidim_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (lam : ℕ → Fin d → ℝ) :
    ∀ n : ℕ, (∀ k, k < n → τ k < τ (k + 1)) → τ n < T →
      ∫ ω, ((Z ω : ℝ) : ℂ) * jointGridCharacterMultidim W N τ lam w Bfam n ω ∂P = 0 := by
  intro n
  induction n with
  | zero =>
      intro _ _
      have h1 : ∀ ω : Ω, ((Z ω : ℝ) : ℂ)
          * jointGridCharacterMultidim W N τ lam w Bfam 0 ω = ((Z ω : ℝ) : ℂ) := by
        intro ω; rw [jointGridCharacterMultidim]; simp
      simp_rw [h1]
      rw [show ∫ ω, ((Z ω : ℝ) : ℂ) ∂P = ((∫ ω, Z ω ∂P : ℝ) : ℂ) from integral_ofReal, hZ0]
      simp
  | succ n ih =>
      intro hlt hTn
      have hlt' : ∀ k, k < n → τ k < τ (k + 1) := fun k hk => hlt k (Nat.lt_succ_of_lt hk)
      have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt' k hk).le
      have hcell : τ n < τ (n + 1) := hlt n (Nat.lt_succ_self n)
      have hτn0 : 0 ≤ τ n := grid_nonneg hτ0 hle' (le_refl n)
      have hmeas := measurable_jointGridCharacterMultidim W N hℱi hℱN hle' lam w hBm
      have hstep := pairing_cell_multidim_joint_eq_zero W N ℱ hd hℱi hℱB hℱN hℱ0 hnull
        hτn0 hcell hT hTn hA hAν w (measurableSet_cellFam hBm τ n)
        (cellFam_subset hBsub τ n) he₀ hZ2 hperp hZcomp
        (V := jointGridCharacterMultidim W N τ lam w Bfam n) hmeas.stronglyMeasurable
        (Mv := 1) zero_le_one
        (fun ω => le_of_eq (norm_jointGridCharacterMultidim W N τ lam w Bfam n ω))
        (ih hlt' (lt_trans hcell hTn)) (lam n)
      have hrw : ∀ ω : Ω, ((Z ω : ℝ) : ℂ)
          * jointGridCharacterMultidim W N τ lam w Bfam (n + 1) ω
          = ((Z ω : ℝ) : ℂ) * jointGridCharacterMultidim W N τ lam w Bfam n ω
            * (Complex.exp (Complex.I * ((∑ i, lam n i
                * ((W.W i).W (τ (n + 1)) ω - (W.W i).W (τ n) ω) : ℝ) : ℂ))
              * charAt N w (cellFam Bfam τ n) (τ (n + 1)) ω) := by
        intro ω
        rw [jointGridCharacterMultidim, jointGridCharacterMultidim, Finset.prod_range_succ]
        ring
      simpa only [hrw] using hstep

/-- **Value characters along a joint grid, multidimensional.** -/
theorem pairing_joint_value_characterMultidim_eq_zero (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    {τ : ℕ → ℝ} (hτ0 : τ 0 = 0)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (c : ℕ → Fin d → ℝ) (n : ℕ)
    (hlt : ∀ k, k < n → τ k < τ (k + 1)) (hTn : τ n < T) :
    ∫ ω, ((Z ω : ℝ) : ℂ)
        * (Complex.exp (Complex.I * ((∑ i, ∑ k ∈ Finset.Ico 1 (n + 1),
            c k i * (W.W i).W (τ k) ω : ℝ) : ℂ))
          * charAt N w Bfam (τ n) ω) ∂P = 0 := by
  have hle' : ∀ k, k < n → τ k ≤ τ (k + 1) := fun k hk => (hlt k hk).le
  have hkey := pairing_jointGridCharacterMultidim_eq_zero W N ℱ hd hℱi hℱB hℱN hℱ0 hnull hτ0
    hT hA hAν w hBm hBsub he₀ hZ2 hperp hZcomp hZ0
    (fun k i => ∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i) n hlt hTn
  refine Eq.trans (integral_congr_ae ?_) hkey
  have hinit : ∀ᵐ ω ∂P, ∀ i : Fin d, (W.W i).W 0 ω = 0 :=
    ae_all_iff.mpr fun i => (W.W i).initial_zero
  filter_upwards [hinit, ae_charAt_eq_prod_cellFam N w hBm hA hAν hBsub hτ0 hle'] with ω hω hprod
  have heq : (∑ k ∈ Finset.range n, ∑ i, (∑ j ∈ Finset.Ico (k + 1) (n + 1), c j i)
        * ((W.W i).W (τ (k + 1)) ω - (W.W i).W (τ k) ω))
      = ∑ i, ∑ k ∈ Finset.Ico 1 (n + 1), c k i * (W.W i).W (τ k) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ =>
      sum_tail_mul_sub (fun k => c k i) (Wv := fun k => (W.W i).W (τ k) ω)
        (by rw [hτ0]; exact hω i) n
  rw [← heq, hprod, jointGridCharacterMultidim, Finset.prod_mul_distrib, ← Complex.exp_sum,
    Complex.ofReal_sum, Finset.mul_sum]

end Grid

end LevyStochCalc.Driver
