/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc

/-!
# The path-regularity rate for the terminal datum `|W¹_1 + W²_1|`

Over a Lévy driver with two Brownian coordinates and jump intensity `0` on the marks `ℝ`, the
backward equation

  `Y_t = |W¹_1 + W²_1| − ∫_t^1 Z_s · dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

with generator `0` and horizon `1` has a solution triple (`exists_unique_solvesBSDEJ`). Its
terminal datum is the `1`-Lipschitz function `x ↦ |x|` of `ξ₀ + W¹_1 σ_1 + W²_1 σ_2` with
`ξ₀ = 0` and `σ_1 = σ_2 = 1`, it depends on both coordinates, and the jump integral vanishes
because the intensity does. So `cellRegularity_of_gaussianTerminal_multi` applies, and every
solution triple satisfies `CellRegularity D 1 Z U A 2` for every family of marks, and
`E ‖Z_t‖² ≤ 2` for almost every `t ∈ [0, 1]`. The same holds, through the finite-horizon forms,
for every process that agrees with `Z` on `[0, 1]`.

## Main statements

* `cellRegularity_of_solvesBSDEJ_absSum` — every solution triple obeys the rate with constant
  `2`.
* `cellRegularity_of_eqOn_absSum` — so does every process agreeing with the control on `[0, 1]`.
* `exists_solvesBSDEJ_absSum_cellRegularity` — on some probability space the equation has a
  solution triple, and every solution triple obeys the rate and the moment bound.
-/

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.NonvacuityMulti

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.BSDEJ.PathRegularity
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The terminal function `x ↦ |x 0|` on `ℝ¹`. -/
noncomputable def absCoord (x : Fin 1 → ℝ) : ℝ := |x 0|

theorem lipschitzWith_absCoord : LipschitzWith 1 absCoord := by
  have h := (LipschitzWith.eval (α := fun _ : Fin 1 => ℝ) (0 : Fin 1))
  have e : absCoord = (fun y : ℝ => ‖y‖) ∘ Function.eval 0 := by
    funext x; simp [absCoord]
  rw [e]
  have h2 := LipschitzWith.comp (lipschitzWith_one_norm (E := ℝ)) h
  rw [mul_one] at h2
  exact h2

/-- The two directions `σ_1 = σ_2 = 1` in `ℝ¹`. -/
def ones : Fin 2 → (Fin 1 → ℝ) := fun _ _ => 1

theorem sum_norm_ones_sq : ∑ j, ‖ones j‖ ^ 2 = 2 := by
  simp [ones, Pi.norm_def]

/-- With jump intensity `0` the compensated integral of every admissible integrand vanishes
almost surely at every nonnegative time. -/
theorem compensated_eq_zero {d : ℕ} (D : LevyDriver P d (0 : Measure ℝ)) (φ : Ω → ℝ → ℝ → ℝ)
    (hm : Measurable fun p : Ω × ℝ × ℝ => φ p.1 p.2.1 p.2.2)
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D) φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂(0 : Measure ℝ) ∂volume ∂P < ⊤) {t : ℝ} (ht : 0 ≤ t) :
    Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug φ hm hp
      hq t =ᵐ[P] 0 := by
  set J := Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug φ
    hm hp hq t with hJ
  have hJm : Measurable J :=
    ((Poisson.Compensated.stochasticIntegral_adapted D.N (augJoint D) D.isPoissonFiltration_aug
      φ hm hp hq t).mono ((augJoint D).rightCont.le t) le_rfl)
  have h0 : ∫⁻ ω, (‖J ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
    rw [lintegral_congr_ae (by
      filter_upwards [Poisson.Compensated.stochasticIntegral_ae_eq_process D.N (augJoint D)
        D.isPoissonFiltration_aug φ hm hp hq t] with ω hω
      rw [hJ, hω]),
      Poisson.Compensated.process_lintegral_sq' D.N (augJoint D) D.isPoissonFiltration_aug φ hm
        hp hq ht]
    simp
  have hae := (lintegral_eq_zero_iff (hJm.nnnorm.coe_nnreal_ennreal.pow_const 2)).mp h0
  filter_upwards [hae] with ω hω
  simpa using hω

/-- A solution triple of the backward equation with generator `0`, terminal datum
`|W¹_1 + W²_1|` and horizon `1` over a Lévy driver with jump intensity `0` solves, at every time
of `[0, 1]`, the Brownian equation `Y_t = |W¹_1 + W²_1| − (∫_0^1 Z dW − ∫_0^t Z dW)`. -/
theorem eqn_absSum_of_solvesBSDEJ (D : LevyDriver P 2 (0 : Measure ℝ))
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 2 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => 0) (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) 1
      Y Z U) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, Y t =ᵐ[P] fun ω =>
      absCoord ((fun _ => (0 : Fin 1 → ℝ)) ω + ∑ j, (D.W.W j).W 1 ω • ones j)
      + (∫ s in Set.Icc t 1, (fun _ : ℝ => (0 : ℝ)) s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
          D.isBrownianFiltration_aug Z h.Z_meas h.Z_prog
          (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) 1 ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
          D.isBrownianFiltration_aug Z h.Z_meas h.Z_prog
          (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t ω) := by
  intro t ht
  filter_upwards [h.eqn t ht, compensated_eq_zero D _ h.U_meas h.U_prog
    (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) zero_le_one,
    compensated_eq_zero D _ h.U_meas h.U_prog
    (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) ht.1] with ω hω h1 h2
  rw [hω, Pi.zero_apply] at *
  rw [h1, h2]
  simp [absCoord, ones, Fin.sum_univ_two]

/-- The value of a solution triple of the `|W¹_1 + W²_1|` equation is adapted to the augmented
joint filtration at every time of `[0, 1]`. -/
theorem adapted_absSum_of_solvesBSDEJ (D : LevyDriver P 2 (0 : Measure ℝ))
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 2 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => 0) (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) 1
      Y Z U) :
    ∀ t ∈ Set.Icc (0 : ℝ) 1, StronglyMeasurable[augJoint D t] (Y t) := by
  intro t ht
  have := (h.Y_adapted t).stronglyMeasurable
  rwa [D.rightCont_augFiltration_eq ht.1] at this

/-- Every solution triple of the backward equation with generator `0`, terminal datum
`|W¹_1 + W²_1|` and horizon `1` over a Lévy driver with jump intensity `0` obeys the `L²`
path-regularity rate with constant `2`, for every finite family of marks, and its Brownian
integrand has second moment at most `2` at almost every time of the horizon. -/
theorem cellRegularity_of_solvesBSDEJ_absSum (D : LevyDriver P 2 (0 : Measure ℝ))
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin 2 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => 0) (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) 1
      Y Z U)
    {m : ℕ} (A : Fin m → Set ℝ) : CellRegularity D 1 Z U A 2 ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 2 := by
  have hξm : StronglyMeasurable[augJoint D 0] (fun _ : Ω => (0 : Fin 1 → ℝ)) :=
    stronglyMeasurable_const
  have hrate := cellRegularity_of_gaussianTerminal_multi D (augJoint D)
    D.isBrownianFiltration_aug h.Z_meas h.Z_prog _ rfl one_pos hξm (memLp_const 0)
    lipschitzWith_absCoord (adapted_absSum_of_solvesBSDEJ D h) (eqn_absSum_of_solvesBSDEJ D h)
    (A := A) (U := U)
    (fun N _ => by
      refine le_of_eq_of_le ?_ zero_le
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [condCellAverage_U])
  have hmom := ae_lintegral_sq_le_of_gaussianTerminal_multi D (augJoint D)
    D.isBrownianFiltration_aug (fun s hs => D.indep_augFiltration_iSup_future hs) h.Z_meas
    h.Z_prog _ one_pos hξm (memLp_const 0) lipschitzWith_absCoord
    (adapted_absSum_of_solvesBSDEJ D h) (eqn_absSum_of_solvesBSDEJ D h)
  simp only [sum_norm_ones_sq, NNReal.coe_one, one_pow, one_mul] at hrate hmom
  refine ⟨hrate, ?_⟩
  simpa using hmom

/-- **The rate under hypotheses on the horizon only.** Let `(Y, Z, U)` solve the
`|W¹_1 + W²_1|` equation, and let `Z'` be any process equal to `Z` at every time of `[0, 1]`.
Through `cellRegularity_of_gaussianTerminal_multi_horizon` and
`ae_lintegral_sq_le_of_gaussianTerminal_multi_horizon`, `(Z', U)` obeys the `L²`
path-regularity rate with constant `2` and `E ‖Z'_t‖² ≤ 2` for almost every `t ∈ [0, 1]`. -/
theorem cellRegularity_of_eqOn_absSum (D : LevyDriver P 2 (0 : Measure ℝ))
    {Y : ℝ → Ω → ℝ} {Z Z' : ℝ → Ω → (Fin 2 → ℝ)} {U : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => 0) (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) 1
      Y Z U)
    (hZZ : ∀ s ∈ Set.Icc (0 : ℝ) 1, Z' s = Z s) {m : ℕ} (A : Fin m → Set ℝ) :
    CellRegularity D 1 Z' U A 2 ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
        ∫⁻ ω, ∑ k, (‖Z' t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 2 := by
  have htr : horizonTrunc 1 Z' = Z := by
    funext s ω
    by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
    · rw [horizonTrunc_of_mem Z' hs, hZZ s hs]
    · rw [horizonTrunc_of_notMem Z' hs, h.Z_vanish ω s hs]
  have hZm : ∀ k, Measurable (Function.uncurry fun ω s => horizonTrunc 1 Z' s ω k) := by
    rw [htr]; exact h.Z_meas
  have hZp : ∀ k, LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D)
      fun ω s => horizonTrunc 1 Z' s ω k := by
    rw [htr]; exact h.Z_prog
  have hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖Z' s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro k
    rw [← lintegral_horizonTrunc_pi_eq k, htr]
    exact sq_int_global_of_vanishing h.Z_vanish h.Z_sq k 1 one_pos
  have key : ∀ (Z₁ : ℝ → Ω → (Fin 2 → ℝ)) (e : Z₁ = Z) hm hp hq (t : ℝ),
      Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
          D.isBrownianFiltration_aug Z₁ hm hp hq t
        = Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
          D.isBrownianFiltration_aug Z h.Z_meas h.Z_prog
          (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) t := by
    intro Z₁ e _ _ _ _
    subst e
    rfl
  have heq : ∀ t ∈ Set.Icc (0 : ℝ) 1, Y t =ᵐ[P] fun ω =>
      absCoord ((fun _ => (0 : Fin 1 → ℝ)) ω + ∑ j, (D.W.W j).W 1 ω • ones j)
      + (∫ s in Set.Icc t 1, (fun _ : ℝ => (0 : ℝ)) s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
          D.isBrownianFiltration_aug (horizonTrunc 1 Z') hZm hZp
          (sq_int_global_horizonTrunc_pi hZs) 1 ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
          D.isBrownianFiltration_aug (horizonTrunc 1 Z') hZm hZp
          (sq_int_global_horizonTrunc_pi hZs) t ω) := by
    intro t ht
    rw [key _ htr, key _ htr]
    exact eqn_absSum_of_solvesBSDEJ D h t ht
  have hξm : StronglyMeasurable[augJoint D 0] (fun _ : Ω => (0 : Fin 1 → ℝ)) :=
    stronglyMeasurable_const
  have hrate := cellRegularity_of_gaussianTerminal_multi_horizon D (augJoint D)
    D.isBrownianFiltration_aug hZm hZp hZs rfl one_pos hξm (memLp_const 0)
    lipschitzWith_absCoord (adapted_absSum_of_solvesBSDEJ D h) heq (A := A) (U := U)
    (fun N _ => by
      refine le_of_eq_of_le ?_ zero_le
      refine Finset.sum_eq_zero fun i _ => ?_
      simp [condCellAverage_U])
  have hmom := ae_lintegral_sq_le_of_gaussianTerminal_multi_horizon D (augJoint D)
    D.isBrownianFiltration_aug (fun s hs => D.indep_augFiltration_iSup_future hs) hZm hZp hZs
    one_pos hξm (memLp_const 0) lipschitzWith_absCoord (adapted_absSum_of_solvesBSDEJ D h) heq
  simp only [sum_norm_ones_sq, NNReal.coe_one, one_pow, one_mul] at hrate hmom
  refine ⟨hrate, ?_⟩
  simpa using hmom

/-- On some probability space there are a Lévy driver with two Brownian coordinates and jump
intensity `0` and a solution triple of the backward equation with generator `0`, terminal datum
`|W¹_1 + W²_1|` and horizon `1`; every solution triple of that equation obeys the `L²`
path-regularity rate with constant `2` for every family of marks, and its Brownian integrand
has second moment at most `2` at almost every time of the horizon. -/
theorem exists_solvesBSDEJ_absSum_cellRegularity :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 2 (0 : Measure ℝ)),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 2 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => 0) (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) 1
            Y Z U) ∧
        ∀ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 2 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => 0) (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) 1
            Y Z U →
            (∀ (m : ℕ) (A : Fin m → Set ℝ), CellRegularity D 1 Z U A 2) ∧
            ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
              ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ 2 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyStochCalc.Driver.LevyDriver.exists 2 ℝ (0 : Measure ℝ)
  have hξ2 : MemLp (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) 2 P :=
    ((memLp_brownian_eval (D.W.W 0) zero_le_one).add
      (memLp_brownian_eval (D.W.W 1) zero_le_one)).abs
  have hξm : AEStronglyMeasurable[augJoint D 1]
      (fun ω => |(D.W.W 0).W 1 ω + (D.W.W 1).W 1 ω|) P := by
    have hcoord : ∀ j : Fin 2, StronglyMeasurable[augJoint D 1] ((D.W.W j).W 1) := fun j =>
      ((D.isBrownianFiltration_aug j).measurable 1).stronglyMeasurable
    exact ((hcoord 0).add (hcoord 1)).norm.aestronglyMeasurable
  obtain ⟨hex, -⟩ := exists_unique_solvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) le_rfl
    (fun _ => measurable_const) (fun _ _ _ _ _ _ _ => by simp) one_pos (by simp) hξ2 hξm
  exact ⟨Ω, inferInstance, P, inferInstance, D, hex, fun _ _ _ h =>
    ⟨fun _ A => (cellRegularity_of_solvesBSDEJ_absSum D h A).1,
      (cellRegularity_of_solvesBSDEJ_absSum D h (fun _ : Fin 0 => ∅)).2⟩⟩

end LevyStochCalc.Examples.NonvacuityMulti
