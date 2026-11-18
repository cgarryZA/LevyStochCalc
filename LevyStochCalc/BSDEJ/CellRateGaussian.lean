/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CellRateGaussianAverage

/-!
# The first-order cell-projection rate for a Gaussian terminal datum

Let `W` be the Brownian motion of a Lévy driver with one Brownian coordinate, `ℱ` a Brownian
filtration for it, and `(Y, Z)` solve, for `t ∈ [0, T]`,

  `Y_t = g(ξ₀ + W_T σ) + ∫_t^T h − (∫_0^T Z dW − ∫_0^t Z dW)`

for a terminal datum that is an `L`-Lipschitz function `g` of `ξ₀ + W_T σ`, with `ξ₀`
square-integrable and measurable at `0` and `σ ∈ ℝⁿ`, and a deterministic driver `h`, `Y`
adapted. Then for every `N ≥ 1`

  `Σ_i E ∫_{t_i}^{t_{i+1}} |Z_t − Z̄_i|² dt ≤ L² ‖σ‖² T / N`,

and `E |Z_t|² ≤ L² ‖σ‖²` for almost every `t ∈ [0, T]`; over the augmented joint filtration of
the driver this is `CellRegularity` with constant `L² ‖σ‖²` for the Brownian part.

The conditional cell average on `[t_i, t_{i+1}]` is `N_{t_i}`, the conditional average over the
remaining horizon, whose second moment `m` is nondecreasing and at most `L² ‖σ‖²`. Refining
each cell into `k` cells, Pythagoras and the convergence of the cell-projection error give
`E ∫_{t_i}^{t_{i+1}} |Z|² ≤ τ m(t_{i+1})` (with `m(T) := L² ‖σ‖²`); Pythagoras on the cell then
bounds the error on it by `τ (m(t_{i+1}) − m(t_i))`, and the sum telescopes.

## Main statements

* `cellProjError_le_of_gaussianTerminal` — the first-order rate.
* `ae_lintegral_sq_le_of_gaussianTerminal` — the bound on the second moment.
* `cellRegularity_of_gaussianTerminal` — the instance of `CellRegularity`.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.PathRegularity

open LevyStochCalc.BSDEJ.Solves (augJoint)

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [MeasurableSpace Ω] in
/-- Consecutive cells `[(m + j) δ, (m + j + 1) δ]`, `j < k`, of the uniform grid of step
`δ ≥ 0` tile `[m δ, (m + k) δ]` for the Lebesgue integral. -/
theorem lintegral_sum_cells_from (g : ℝ → ℝ≥0∞) {δ : ℝ} (hδ : 0 ≤ δ) (m k : ℕ) :
    ∑ j ∈ Finset.range k,
        ∫⁻ s in Set.Icc (((m + j : ℕ) : ℝ) * δ) ((((m + j : ℕ) : ℝ) + 1) * δ), g s
      = ∫⁻ s in Set.Icc ((m : ℝ) * δ) (((m + k : ℕ) : ℝ) * δ), g s := by
  induction k with
  | zero => simp [Set.Icc_self]
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    have h0 : (m : ℝ) * δ ≤ ((m + k : ℕ) : ℝ) * δ := by
      gcongr; exact_mod_cast Nat.le_add_right m k
    have h1 : ((m + k : ℕ) : ℝ) * δ ≤ (((m + k : ℕ) : ℝ) + 1) * δ := by nlinarith
    have e : ((m + (k + 1) : ℕ) : ℝ) * δ = (((m + k : ℕ) : ℝ) + 1) * δ := by push_cast; ring
    rw [e, setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume) (a := (m : ℝ) * δ)
        (b := ((m + k : ℕ) : ℝ) * δ)).symm,
      setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume) (a := ((m + k : ℕ) : ℝ) * δ)
        (b := (((m + k : ℕ) : ℝ) + 1) * δ)).symm,
      setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume) (a := (m : ℝ) * δ)
        (b := (((m + k : ℕ) : ℝ) + 1) * δ)).symm,
      ← Set.Ioc_union_Ioc_eq_Ioc h0 h1, lintegral_union measurableSet_Ioc]
    exact Set.disjoint_left.mpr fun x hx hy => absurd hx.2 (not_le.mpr hy.1)

section Gaussian

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  (D : Driver.LevyDriver.{u, v, w} P 1 ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {Z : ℝ → Ω → (Fin 1 → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
  (hZs : ∀ k, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc 0 T', (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {T : ℝ} {n : ℕ} {ξ₀ : Ω → (Fin n → ℝ)} {σ : Fin n → ℝ} {g : (Fin n → ℝ) → ℝ}
  {L : ℝ≥0} {h : ℝ → ℝ} {Y : ℝ → Ω → ℝ}

include hcoord in
/-- On a cell `[p δ, (p + 1) δ] ⊆ [0, T]` the second moment of the conditional cell average is
that of the conditional average over the remaining horizon at the left endpoint. -/
theorem lintegral_condCellAvg_sq_eq_of_gaussianTerminal
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hpT : ((p : ℝ) + 1) * δ ≤ T) :
    ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P δ Z p ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal
          (∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) ((p : ℝ) * δ) ω ^ 2 ∂P) := by
  have ht : 0 ≤ (p : ℝ) * δ := by positivity
  have htr : (p : ℝ) * δ < ((p : ℝ) + 1) * δ := by nlinarith
  have htT : (p : ℝ) * δ < T := htr.trans_le hpT
  have hT : 0 < T := ht.trans_lt htT
  have hcond := condAvg_eq_condAvg_terminal D ℱ hcoord hZm hZp hZs hξm hξ hg hYa heq ht htr hpT
  have hlen : ((p : ℝ) + 1) * δ - (p : ℝ) * δ = δ := by ring
  rw [hlen] at hcond
  rw [← lintegral_nnnorm_sq_eq_ofReal (memLp_condAvgToHorizon ℱ (hZm 0) (hZs 0 T hT) ht htT)]
  simp only [Fin.sum_univ_one]
  refine lintegral_congr_ae ?_
  filter_upwards [hcond] with ω hω
  simp only [condCellAvg, condAvgToHorizon] at hω ⊢
  rw [hω]

include hcoord in
/-- **The second moment of the control process for a Gaussian terminal datum.** For almost every
`t ∈ [0, T]`, `E |Z_t|² ≤ L² ‖σ‖²`. -/
theorem ae_lintegral_sq_le_of_gaussianTerminal (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ‖σ‖ ^ 2) := by
  refine ae_lintegral_sq_le_of_condCellAvg_le ℱ hT hZm hZp (fun k => hZs k T hT) ?_
  intro N hN i hi
  have hδ : 0 < T / N := div_pos hT (by exact_mod_cast hN)
  have hsub := cell_subset_Icc hT.le hi
  have hab : (i : ℝ) * (T / N) ≤ ((i : ℝ) + 1) * (T / N) := by nlinarith
  have hpT : ((i : ℝ) + 1) * (T / N) ≤ T := (hsub ⟨hab, le_rfl⟩).2
  rw [lintegral_condCellAvg_sq_eq_of_gaussianTerminal D ℱ hcoord hZm hZp hZs hξm hξ hg hYa heq
    hδ hpT]
  refine ENNReal.ofReal_le_ofReal (integral_condAvgToHorizon_sq_le D ℱ hcoord hZm hZp hZs hξm hξ
    hg hYa heq
    (by positivity) ?_)
  have : (i : ℝ) * (T / N) < ((i : ℝ) + 1) * (T / N) := by nlinarith
  linarith

include hcoord in
/-- **The energy of the control process on a cell.** If the second moment of the conditional
average over the remaining horizon is at most `β` at every time of `[0, t_{i+1})`, the energy of
`Z` on the cell `[t_i, t_{i+1}]` of the uniform grid of `N` cells is at most `β T / N`. -/
theorem lintegral_cell_sq_le_of_gaussianTerminal (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) {β : ℝ}
    (hβ : ∀ t, 0 ≤ t → t < ((i : ℝ) + 1) * (T / N) →
      ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω ^ 2 ∂P ≤ β) :
    ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * (T / N)) (((i : ℝ) + 1) * (T / N)),
        ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (T / N * β) := by
  set τ : ℝ := T / N with hτdef
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hGm : Measurable (Function.uncurry fun ω s => ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2) :=
    Finset.measurable_sum _ fun k _ => (hZm k).nnnorm.coe_nnreal_ennreal.pow_const 2
  -- the bound after refining each cell into `q` cells
  have hk : ∀ q : ℕ, 0 < q → ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ cellProjError ℱ P T (q * N) Z + ENNReal.ofReal (τ * β) := by
    intro q hq0
    have hkpos : (0 : ℝ) < q := by exact_mod_cast hq0
    set δ : ℝ := T / ((q * N : ℕ) : ℝ) with hδdef
    have hδ : 0 < δ := div_pos hT (by positivity)
    have hkδ : (q : ℝ) * δ = τ := by rw [hδdef, hτdef]; push_cast; field_simp
    have hcell : Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ)
        = Set.Icc (((i * q : ℕ) : ℝ) * δ) (((i * q + q : ℕ) : ℝ) * δ) := by
      rw [← hkδ]; push_cast; ring_nf
    have hsubT : ∀ j < q, (((i * q + j : ℕ) : ℝ) + 1) * δ ≤ T := by
      intro j hj
      have h1 : i * q + j + 1 ≤ q * N := by nlinarith
      have h2 : (((i * q + j : ℕ) : ℝ) + 1) ≤ ((q * N : ℕ) : ℝ) := by exact_mod_cast h1
      calc (((i * q + j : ℕ) : ℝ) + 1) * δ ≤ ((q * N : ℕ) : ℝ) * δ := by gcongr
        _ = T := by rw [hδdef]; field_simp
    have hleft : ∀ j < q, ((i * q + j : ℕ) : ℝ) * δ < ((i : ℝ) + 1) * τ := by
      intro j hj
      have h1 : (((i * q + j : ℕ) : ℝ)) < ((i : ℝ) + 1) * q := by
        have : i * q + j < (i + 1) * q := by nlinarith
        exact_mod_cast this
      calc ((i * q + j : ℕ) : ℝ) * δ < ((i : ℝ) + 1) * q * δ := by gcongr
        _ = ((i : ℝ) + 1) * τ := by rw [mul_assoc, hkδ]
    have hm : ∀ j ∈ Finset.range q, Measurable fun ω =>
        ∫⁻ s in Set.Icc (((i * q + j : ℕ) : ℝ) * δ) ((((i * q + j : ℕ) : ℝ) + 1) * δ),
          ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume := fun j _ => hGm.lintegral_prod_right'
    rw [hcell]
    have htile : ∫⁻ ω, ∫⁻ s in Set.Icc (((i * q : ℕ) : ℝ) * δ) (((i * q + q : ℕ) : ℝ) * δ),
          ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = ∑ j ∈ Finset.range q, ∫⁻ ω,
          ∫⁻ s in Set.Icc (((i * q + j : ℕ) : ℝ) * δ) ((((i * q + j : ℕ) : ℝ) + 1) * δ),
            ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      rw [← lintegral_finsetSum _ hm]
      exact lintegral_congr fun ω => (lintegral_sum_cells_from _ hδ.le (i * q) q).symm
    rw [htile]
    have hsub : ∀ j ∈ Finset.range q, ∫⁻ ω,
        ∫⁻ s in Set.Icc (((i * q + j : ℕ) : ℝ) * δ) ((((i * q + j : ℕ) : ℝ) + 1) * δ),
          ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (((i * q + j : ℕ) : ℝ) * δ) ((((i * q + j : ℕ) : ℝ) + 1) * δ),
            ∑ k, (‖Z s ω k - condCellAvg ℱ P δ Z (i * q + j) ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
          + ENNReal.ofReal (δ * β) := by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      have hZc : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc (((i * q + j : ℕ) : ℝ) * δ)
          ((((i * q + j : ℕ) : ℝ) + 1) * δ), (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
        intro k'
        refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set ?_) (hZs k' T hT)
        exact Set.Icc_subset_Icc (by positivity) (hsubT j hj')
      rw [lintegral_cell_sq_eq ℱ hδ hZm hZc, lintegral_condCellAvg_sq_eq_of_gaussianTerminal D ℱ
        hcoord hZm hZp hZs hξm hξ hg hYa heq hδ (hsubT j hj'), ← ENNReal.ofReal_mul hδ.le]
      gcongr
      exact hβ _ (by positivity) (hleft j hj')
    refine (Finset.sum_le_sum hsub).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    refine add_le_add ?_ (le_of_eq ?_)
    · have hIco := Finset.sum_Ico_eq_sum_range (fun p => ∫⁻ ω,
          ∫⁻ s in Set.Icc ((p : ℝ) * δ) (((p : ℝ) + 1) * δ),
            ∑ k, (‖Z s ω k - condCellAvg ℱ P δ Z p ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) (i * q) (i * q + q)
      rw [show i * q + q - i * q = q by omega] at hIco
      rw [cellProjError, ← hδdef, ← hIco]
      refine Finset.sum_le_sum_of_subset fun p hp => ?_
      have := Finset.mem_Ico.mp hp
      exact Finset.mem_range.mpr (by nlinarith)
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg q), ← mul_assoc, hkδ]
  -- the limit along the refinements
  have hlim : Tendsto (fun q : ℕ => cellProjError ℱ P T (q * N) Z + ENNReal.ofReal (τ * β))
      atTop (𝓝 (0 + ENNReal.ofReal (τ * β))) := by
    refine Tendsto.add ?_ tendsto_const_nhds
    refine (tendsto_cellProjError_zero ℱ hT hZm hZp (fun k => hZs k T hT)).comp ?_
    exact tendsto_id.atTop_mul_const' hN
  rw [zero_add] at hlim
  refine ge_of_tendsto hlim ?_
  filter_upwards [eventually_gt_atTop 0] with q hq0 using hk q hq0

include hcoord in
/-- **The first-order cell-projection rate for a Gaussian terminal datum.** For every `N ≥ 1`
the cell-projection error of `Z` on the uniform grid of `N` cells of `[0, T]` is at most
`L² ‖σ‖² T / N`. -/
theorem cellProjError_le_of_gaussianTerminal (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {N : ℕ} (hN : 0 < N) :
    cellProjError ℱ P T N Z ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ‖σ‖ ^ 2 * (T / N)) := by
  set τ : ℝ := T / N with hτdef
  have hτ : 0 < τ := div_pos hT (by exact_mod_cast hN)
  have hNτ : (N : ℝ) * τ = T := by rw [hτdef]; field_simp
  set B : ℝ := (L : ℝ) ^ 2 * ‖σ‖ ^ 2 with hBdef
  set m : ℝ → ℝ := fun t => ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω ^ 2 ∂P
    with hmdef
  set μ : ℝ → ℝ := fun t => if t < T then m t else B with hμdef
  have hmB : ∀ t, 0 ≤ t → t < T → m t ≤ B := fun t ht htT =>
    integral_condAvgToHorizon_sq_le D ℱ hcoord hZm hZp hZs hξm hξ hg hYa heq ht htT
  have hμB : ∀ t, 0 ≤ t → μ t ≤ B := by
    intro t ht
    simp only [hμdef]
    split_ifs with htT
    · exact hmB t ht htT
    · exact le_rfl
  have hμmono : ∀ a b, 0 ≤ a → a ≤ b → μ a ≤ μ b := by
    intro a b ha hab
    by_cases hbT : b < T
    · have haT : a < T := hab.trans_lt hbT
      simp only [hμdef, if_pos haT, if_pos hbT]
      exact integral_condAvgToHorizon_sq_mono D ℱ hcoord hZm hZp hZs hξm hξ hg hYa heq ha hab hbT
    · simp only [hμdef, if_neg hbT]
      exact hμB a ha
  have hgrid : ∀ i < N, 0 ≤ (i : ℝ) * τ ∧ (i : ℝ) * τ < T ∧ ((i : ℝ) + 1) * τ ≤ T := by
    intro i hi
    have hsub := cell_subset_Icc hT.le hi
    have hab : (i : ℝ) * τ < ((i : ℝ) + 1) * τ := by nlinarith
    have h2 : ((i : ℝ) + 1) * τ ≤ T := (hsub ⟨hab.le, le_rfl⟩).2
    exact ⟨by positivity, hab.trans_le h2, h2⟩
  have hcell : ∀ i < N, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      ∑ k, (‖Z s ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (τ * (μ (((i : ℝ) + 1) * τ) - μ ((i : ℝ) * τ))) := by
    intro i hi
    obtain ⟨h0, h1, h2⟩ := hgrid i hi
    have hZc : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun k =>
      lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc h0 h2))
        (hZs k T hT)
    have hE := lintegral_cell_sq_le_of_gaussianTerminal D ℱ hcoord hZm hZp hZs hT hξm hξ hg hYa
      heq hN hi
      (β := μ (((i : ℝ) + 1) * τ)) (fun t ht htl => by
        have hm : m t = μ t := by simp only [hμdef, if_pos (htl.trans_le h2)]
        have := hμmono t _ ht htl.le
        rw [← hm] at this
        exact this)
    rw [lintegral_cell_sq_eq ℱ hτ hZm hZc, lintegral_condCellAvg_sq_eq_of_gaussianTerminal D ℱ
      hcoord hZm hZp hZs hξm hξ hg hYa heq hτ h2, ← ENNReal.ofReal_mul hτ.le] at hE
    have hmi : 0 ≤ m ((i : ℝ) * τ) := integral_nonneg fun ω => sq_nonneg _
    have hμi : μ ((i : ℝ) * τ) = m ((i : ℝ) * τ) := by simp only [hμdef, if_pos h1]
    rw [hμi, mul_sub, ENNReal.ofReal_sub _ (mul_nonneg hτ.le hmi)]
    exact ENNReal.le_sub_of_add_le_right ENNReal.ofReal_ne_top hE
  rw [cellProjError, ← hτdef]
  refine (Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.mp hi)).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun i hi => mul_nonneg hτ.le (sub_nonneg.mpr
    (hμmono _ _ (hgrid i (Finset.mem_range.mp hi)).1 (by nlinarith)))]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [← Finset.mul_sum]
  have htel : ∑ i ∈ Finset.range N, (μ (((i : ℝ) + 1) * τ) - μ ((i : ℝ) * τ))
      = μ ((N : ℝ) * τ) - μ 0 := by
    have := Finset.sum_range_sub (fun j : ℕ => μ ((j : ℝ) * τ)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at this
    exact this
  rw [htel, hNτ]
  have hμ0 : 0 ≤ μ 0 := by
    simp only [hμdef, if_pos hT]
    exact integral_nonneg fun ω => sq_nonneg _
  have := hμB T hT.le
  nlinarith

include hcoord in
/-- **`CellRegularity` for a Gaussian terminal datum.** Over the augmented joint filtration of a
Lévy driver with one Brownian coordinate, a solution of the backward equation with a terminal
datum that is an `L`-Lipschitz function of `ξ₀ + W_T σ` and a deterministic driver has the
`L²` path-regularity rate with constant `L² ‖σ‖²`, given that rate for the marked integrals. -/
theorem cellRegularity_of_gaussianTerminal (hℱ : ℱ = augJoint D) (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {m : ℕ} {U : ℝ → Ω → E → ℝ} {A : Fin m → Set E}
    (hU : ∀ N : ℕ, 0 < N →
      ∑ i ∈ Finset.range N, ∫⁻ ω,
        ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
          ∑ k : Fin m,
            (‖(∫ e in A k, U s ω e ∂ν)
              - condCellAverage_U D (T / (N : ℝ)) U A i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ‖σ‖ ^ 2 * (T / (N : ℝ)))) :
    CellRegularity D T Z U A ((L : ℝ) ^ 2 * ‖σ‖ ^ 2) := by
  refine (cellRegularity_iff D T Z U A _).mpr ⟨by positivity, fun N hN => ?_, hU⟩
  have h := cellProjError_le_of_gaussianTerminal D ℱ hcoord hZm hZp hZs hT hξm hξ hg hYa heq hN
  subst hℱ
  exact h

end Gaussian

end LevyStochCalc.BSDEJ.PathRegularity
