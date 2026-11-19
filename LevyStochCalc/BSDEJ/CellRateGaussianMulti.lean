/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CellRateGaussianMultiAverage
import LevyStochCalc.BSDEJ.CellRateHorizon
import LevyStochCalc.Driver.JointFuture

/-!
# The first-order cell-projection rate for a Gaussian terminal datum in several coordinates

Let `W` be the `d`-dimensional Brownian motion of a Lévy driver, `ℱ` a filtration that is
Brownian for every coordinate and such that `ℱ s` is independent of the increments after `s` of
all the coordinates, and `(Y, Z)` solve, for `t ∈ [0, T]`,

  `Y_t = g(ξ₀ + Σ_j Wʲ_T σ_j) + ∫_t^T h − (∫_0^T Z dW − ∫_0^t Z dW)`

for a terminal datum that is an `L`-Lipschitz function `g` on `ℝⁿ` of `ξ₀ + Σ_j Wʲ_T σ_j`, with
`ξ₀` square-integrable and measurable at `0` and `σ_j ∈ ℝⁿ`, and a deterministic driver `h`, `Y`
adapted. Then for every `N ≥ 1`

  `Σ_i E ∫_{t_i}^{t_{i+1}} ‖Z_t − Z̄_i‖² dt ≤ L² (Σ_j ‖σ_j‖²) T / N`,

and `E ‖Z_t‖² ≤ L² Σ_j ‖σ_j‖²` for almost every `t ∈ [0, T]`; over the augmented joint filtration
of the driver, which has the independence property, this is `CellRegularity` with constant
`L² Σ_j ‖σ_j‖²` for the Brownian part.

The argument is that of the one-coordinate case, coordinate by coordinate: the conditional cell
average of `Zᵏ` on `[t_i, t_{i+1}]` is `Nᵏ_{t_i}`, the conditional average over the remaining
horizon, and `m(t) = Σ_k E (Nᵏ_t)²` is nondecreasing and at most `L² Σ_j ‖σ_j‖²`; refining the
cells bounds the energy of `Z` on a cell by `τ m(t_{i+1})`, Pythagoras bounds the error on it by
`τ (m(t_{i+1}) − m(t_i))`, and the sum telescopes.

## Main statements

* `cellProjError_le_of_gaussianTerminal_multi` — the first-order rate.
* `ae_lintegral_sq_le_of_gaussianTerminal_multi` — the bound on the second moment.
* `cellRegularity_of_gaussianTerminal_multi` — the instance of `CellRegularity`.
* `cellProjError_le_of_gaussianTerminal_multi_horizon`,
  `ae_lintegral_sq_le_of_gaussianTerminal_multi_horizon`,
  `cellRegularity_of_gaussianTerminal_multi_horizon` — the same under hypotheses on `[0, T]`
  only, through the truncation `horizonTrunc`.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.PathRegularity

open LevyStochCalc.BSDEJ.Solves (augJoint)

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Gaussian

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  (D : Driver.LevyDriver.{u, v, w} P d ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hjoint : ∀ ⦃s : ℝ⦄, 0 ≤ s → Indep (ℱ s) (⨆ i : Fin d, ⨆ t ∈ Set.Ioi s,
    MeasurableSpace.comap (fun ω => (D.W.W i).W t ω - (D.W.W i).W s ω) inferInstance) P)
  {Z : ℝ → Ω → (Fin d → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
  (hZs : ∀ k, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc 0 T', (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {T : ℝ} {n : ℕ} {ξ₀ : Ω → (Fin n → ℝ)} {σ : Fin d → (Fin n → ℝ)}
  {g : (Fin n → ℝ) → ℝ} {L : ℝ≥0} {h : ℝ → ℝ} {Y : ℝ → Ω → ℝ}

include hcoord hjoint in
/-- On a cell `[p δ, (p + 1) δ] ⊆ [0, T]` the second moment of the conditional cell average is
the sum over the coordinates of the second moments of the conditional averages over the
remaining horizon at the left endpoint. -/
theorem lintegral_condCellAvg_sq_eq_of_gaussianTerminal_multi
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {δ : ℝ} (hδ : 0 < δ) {p : ℕ} (hpT : ((p : ℝ) + 1) * δ ≤ T) :
    ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P δ Z p ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (∑ k,
          ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω k) ((p : ℝ) * δ) ω ^ 2 ∂P) := by
  have ht : 0 ≤ (p : ℝ) * δ := by positivity
  have htr : (p : ℝ) * δ < ((p : ℝ) + 1) * δ := by nlinarith
  have htT : (p : ℝ) * δ < T := htr.trans_le hpT
  have hT : 0 < T := ht.trans_lt htT
  have hlen : ((p : ℝ) + 1) * δ - (p : ℝ) * δ = δ := by ring
  have hterm : ∀ k, ∫⁻ ω, (‖condCellAvg ℱ P δ Z p ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal
          (∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω k) ((p : ℝ) * δ) ω ^ 2 ∂P) := by
    intro k
    have hcond := condAvg_eq_condAvg_terminal_multi D ℱ hcoord hjoint hZm hZp hZs hξm hξ hg hYa
      heq k ht htr hpT
    rw [hlen] at hcond
    rw [← lintegral_nnnorm_sq_eq_ofReal (memLp_condAvgToHorizon ℱ (hZm k) (hZs k T hT) ht htT)]
    refine lintegral_congr_ae ?_
    filter_upwards [hcond] with ω hω
    simp only [condCellAvg, condAvgToHorizon] at hω ⊢
    rw [hω]
  have hmeas : ∀ k ∈ Finset.univ,
      AEMeasurable (fun ω => (‖condCellAvg ℱ P δ Z p ω k‖₊ : ℝ≥0∞) ^ 2) P := by
    intro k _
    have hm : StronglyMeasurable[ℱ ((p : ℝ) * δ)] fun ω => condCellAvg ℱ P δ Z p ω k :=
      stronglyMeasurable_condExp.const_mul _
    exact ((hm.mono (ℱ.le _)).measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable
  rw [lintegral_finsetSum' _ hmeas,
    ENNReal.ofReal_sum_of_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _]
  exact Finset.sum_congr rfl fun k _ => hterm k

include hcoord hjoint in
/-- **The second moment of the control process for a Gaussian terminal datum in several
coordinates.** For almost every `t ∈ [0, T]`, `E ‖Z_t‖² ≤ L² Σ_j ‖σ_j‖²`. -/
theorem ae_lintegral_sq_le_of_gaussianTerminal_multi (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ∑ j, ‖σ j‖ ^ 2) := by
  refine ae_lintegral_sq_le_of_condCellAvg_le ℱ hT hZm hZp (fun k => hZs k T hT) ?_
  intro N hN i hi
  have hδ : 0 < T / N := div_pos hT (by exact_mod_cast hN)
  have hsub := cell_subset_Icc hT.le hi
  have hab : (i : ℝ) * (T / N) ≤ ((i : ℝ) + 1) * (T / N) := by nlinarith
  have hpT : ((i : ℝ) + 1) * (T / N) ≤ T := (hsub ⟨hab, le_rfl⟩).2
  have hlt : (i : ℝ) * (T / N) < T := by
    have : (i : ℝ) * (T / N) < ((i : ℝ) + 1) * (T / N) := by nlinarith
    linarith
  rw [lintegral_condCellAvg_sq_eq_of_gaussianTerminal_multi D ℱ hcoord hjoint hZm hZp hZs hξm
    hξ hg hYa heq hδ hpT, Finset.mul_sum]
  exact ENNReal.ofReal_le_ofReal (Finset.sum_le_sum fun k _ =>
    integral_condAvgToHorizon_sq_le_multi D ℱ hcoord hjoint hZm hZp hZs hξm hξ hg hYa heq k
      (by positivity) hlt)

include hcoord hjoint in
/-- **The energy of the control process on a cell.** If `Σ_k E (Nᵏ_t)²` is at most `β` at every
time of `[0, t_{i+1})`, the energy of `Z` on the cell `[t_i, t_{i+1}]` of the uniform grid of `N`
cells is at most `β T / N`. -/
theorem lintegral_cell_sq_le_of_gaussianTerminal_multi (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) {β : ℝ}
    (hβ : ∀ t, 0 ≤ t → t < ((i : ℝ) + 1) * (T / N) →
      ∑ k, ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω k) t ω ^ 2 ∂P ≤ β) :
    ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * (T / N)) (((i : ℝ) + 1) * (T / N)),
        ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (T / N * β) := by
  set τ : ℝ := T / N with hτdef
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
      rw [lintegral_cell_sq_eq ℱ hδ hZm hZc, lintegral_condCellAvg_sq_eq_of_gaussianTerminal_multi
        D ℱ hcoord hjoint hZm hZp hZs hξm hξ hg hYa heq hδ (hsubT j hj'),
        ← ENNReal.ofReal_mul hδ.le]
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

include hcoord hjoint in
/-- **The first-order cell-projection rate for a Gaussian terminal datum in several
coordinates.** For every `N ≥ 1` the cell-projection error of `Z` on the uniform grid of `N`
cells of `[0, T]` is at most `L² (Σ_j ‖σ_j‖²) T / N`. -/
theorem cellProjError_le_of_gaussianTerminal_multi (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {N : ℕ} (hN : 0 < N) :
    cellProjError ℱ P T N Z ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * (∑ j, ‖σ j‖ ^ 2) * (T / N)) := by
  set τ : ℝ := T / N with hτdef
  have hτ : 0 < τ := div_pos hT (by exact_mod_cast hN)
  have hNτ : (N : ℝ) * τ = T := by rw [hτdef]; field_simp
  set B : ℝ := (L : ℝ) ^ 2 * ∑ j, ‖σ j‖ ^ 2 with hBdef
  set m : ℝ → ℝ := fun t => ∑ k, ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω k) t ω ^ 2 ∂P
    with hmdef
  set μ : ℝ → ℝ := fun t => if t < T then m t else B with hμdef
  have hm0 : ∀ t, 0 ≤ m t := fun t =>
    Finset.sum_nonneg fun k _ => integral_nonneg fun ω => sq_nonneg _
  have hmB : ∀ t, 0 ≤ t → t < T → m t ≤ B := fun t ht htT => by
    simp only [hmdef, hBdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ =>
      integral_condAvgToHorizon_sq_le_multi D ℱ hcoord hjoint hZm hZp hZs hξm hξ hg hYa heq k ht
        htT
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
      simp only [hμdef, if_pos haT, if_pos hbT, hmdef]
      exact Finset.sum_le_sum fun k _ =>
        integral_condAvgToHorizon_sq_mono_multi D ℱ hcoord hjoint hZm hZp hZs hξm hξ hg hYa heq k
          ha hab hbT
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
    have hE := lintegral_cell_sq_le_of_gaussianTerminal_multi D ℱ hcoord hjoint hZm hZp hZs hT
      hξm hξ hg hYa heq hN hi
      (β := μ (((i : ℝ) + 1) * τ)) (fun t ht htl => by
        have hm : m t = μ t := by simp only [hμdef, if_pos (htl.trans_le h2)]
        have := hμmono t _ ht htl.le
        rw [← hm] at this
        exact this)
    rw [lintegral_cell_sq_eq ℱ hτ hZm hZc, lintegral_condCellAvg_sq_eq_of_gaussianTerminal_multi
      D ℱ hcoord hjoint hZm hZp hZs hξm hξ hg hYa heq hτ h2, ← ENNReal.ofReal_mul hτ.le] at hE
    have hμi : μ ((i : ℝ) * τ) = m ((i : ℝ) * τ) := by simp only [hμdef, if_pos h1]
    rw [hμi, mul_sub, ENNReal.ofReal_sub _ (mul_nonneg hτ.le (hm0 _))]
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
    exact hm0 0
  have := hμB T hT.le
  nlinarith

include hcoord in
/-- **`CellRegularity` for a Gaussian terminal datum in several coordinates.** Over the
augmented joint filtration of a Lévy driver, a solution of the backward equation with a
terminal datum that is an `L`-Lipschitz function of `ξ₀ + Σ_j Wʲ_T σ_j` and a deterministic
driver has the `L²` path-regularity rate with constant `L² Σ_j ‖σ_j‖²`, given that rate for the
marked integrals. -/
theorem cellRegularity_of_gaussianTerminal_multi (hℱ : ℱ = augJoint D) (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
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
        ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * (∑ j, ‖σ j‖ ^ 2) * (T / (N : ℝ)))) :
    CellRegularity D T Z U A ((L : ℝ) ^ 2 * ∑ j, ‖σ j‖ ^ 2) := by
  have hjoint : ∀ ⦃s : ℝ⦄, 0 ≤ s → Indep (ℱ s) (⨆ i : Fin d, ⨆ t ∈ Set.Ioi s,
      MeasurableSpace.comap (fun ω => (D.W.W i).W t ω - (D.W.W i).W s ω) inferInstance) P := by
    intro s hs
    rw [hℱ]
    exact D.indep_augFiltration_iSup_future hs
  refine (cellRegularity_iff D T Z U A _).mpr ⟨by positivity, fun N hN => ?_, hU⟩
  have h := cellProjError_le_of_gaussianTerminal_multi D ℱ hcoord hjoint hZm hZp hZs hT hξm hξ
    hg hYa heq hN
  subst hℱ
  exact h

end Gaussian

section GaussianHorizon

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  (D : Driver.LevyDriver.{u, v, w} P d ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hjoint : ∀ ⦃s : ℝ⦄, 0 ≤ s → Indep (ℱ s) (⨆ i : Fin d, ⨆ t ∈ Set.Ioi s,
    MeasurableSpace.comap (fun ω => (D.W.W i).W t ω - (D.W.W i).W s ω) inferInstance) P)
  {T : ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => horizonTrunc T Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => horizonTrunc T Z s ω k)
  (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {n : ℕ} {ξ₀ : Ω → (Fin n → ℝ)} {σ : Fin d → (Fin n → ℝ)} {g : (Fin n → ℝ) → ℝ}
  {L : ℝ≥0} {h : ℝ → ℝ} {Y : ℝ → Ω → ℝ}

include hjoint in
/-- **The first-order rate for a Gaussian terminal datum in several coordinates, on the
horizon.** Let `Z` have jointly and progressively measurable truncation `Zᵀ = 1_{[0, T]} Z` and
finite energy on `[0, T]`, and let
`Y_t = g(ξ₀ + Σ_j Wʲ_T σ_j) + ∫_t^T h − (∫_0^T Zᵀ dW − ∫_0^t Zᵀ dW)` for `t ∈ [0, T]`, with `g`
`L`-Lipschitz, `ξ₀` square-integrable and measurable at `0` and `Y` adapted. For every `N ≥ 1`
the cell-projection error of `Z` on the uniform grid of `N` cells of `[0, T]` is at most
`L² (Σ_j ‖σ_j‖²) T / N`. -/
theorem cellProjError_le_of_gaussianTerminal_multi_horizon (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) t ω))
    {N : ℕ} (hN : 0 < N) :
    cellProjError ℱ P T N Z ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * (∑ j, ‖σ j‖ ^ 2) * (T / N)) := by
  rw [← cellProjError_horizonTrunc ℱ hT.le]
  exact cellProjError_le_of_gaussianTerminal_multi D ℱ hcoord hjoint hZm hZp
    (sq_int_global_horizonTrunc_pi hZs) hT hξm hξ hg hYa heq hN

include hjoint in
/-- **The second moment of the control for a Gaussian terminal datum in several coordinates, on
the horizon.** Under the hypotheses of `cellProjError_le_of_gaussianTerminal_multi_horizon`,
`E ‖Z_t‖² ≤ L² Σ_j ‖σ_j‖²` for almost every `t ∈ [0, T]`. -/
theorem ae_lintegral_sq_le_of_gaussianTerminal_multi_horizon (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) t ω)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ∑ j, ‖σ j‖ ^ 2) := by
  have h1 := ae_lintegral_sq_le_of_gaussianTerminal_multi D ℱ hcoord hjoint hZm hZp
    (sq_int_global_horizonTrunc_pi hZs) hT hξm hξ hg hYa heq
  filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with t h2 ht
  rwa [horizonTrunc_eq_of_mem Z ht] at h2

/-- **`CellRegularity` for a Gaussian terminal datum in several coordinates, on the horizon.**
Over the augmented joint filtration of a Lévy driver, under the hypotheses of
`cellProjError_le_of_gaussianTerminal_multi_horizon`, the pair `(Z, U)` has the `L²`
path-regularity rate with constant `L² Σ_j ‖σ_j‖²`, given that rate for the marked integrals. -/
theorem cellRegularity_of_gaussianTerminal_multi_horizon (hℱ : ℱ = augJoint D) (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + ∑ j, (D.W.W j).W T ω • σ j)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) t ω))
    {m : ℕ} {U : ℝ → Ω → E → ℝ} {A : Fin m → Set E}
    (hU : ∀ N : ℕ, 0 < N →
      ∑ i ∈ Finset.range N, ∫⁻ ω,
        ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
          ∑ k : Fin m,
            (‖(∫ e in A k, U s ω e ∂ν)
              - condCellAverage_U D (T / (N : ℝ)) U A i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * (∑ j, ‖σ j‖ ^ 2) * (T / (N : ℝ)))) :
    CellRegularity D T Z U A ((L : ℝ) ^ 2 * ∑ j, ‖σ j‖ ^ 2) :=
  (cellRegularity_horizonTrunc_iff D hT.le Z U A _).mp
    (cellRegularity_of_gaussianTerminal_multi D ℱ hcoord hZm hZp
      (sq_int_global_horizonTrunc_pi hZs) hℱ hT hξm hξ hg hYa heq hU)

end GaussianHorizon

end LevyStochCalc.BSDEJ.PathRegularity
