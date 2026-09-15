/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc
import NonvacuityBSDEJ
import NonvacuityBSDEJExp

/-!
# The cell-average rate for the backward equation with the identity generator

For the scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

of `NonvacuityBSDEJExp`, the Brownian integrand of every solution triple agrees `P ⊗ dt`-almost
everywhere on `Ω × [0, 1]` with the windowed weight `e^{1-s} 1_{(0, 1]}(s)`, hence with the
globally Lipschitz clamped weight `s ↦ e^{1 - max s 0}`. Transporting the deterministic bound
`LevyStochCalc.BSDEJ.PathRegularity.energy_sub_conditionalTimeAverage_le_of_lipschitz` along that
agreement gives, for every solution triple and every strictly monotone partition of `[0, 1]` of
mesh at most `δ`, the energy bound `(e δ) ^ 2` for the difference between the integrand and its
pathwise cell average.

The average subtracted here is the pathwise cell average `conditionalTimeAverage_Z`, not the
`ℱ_{t_n}`-conditional projection; the equation is the single equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`.

## Main statements

* `abs_expWeightClamp_sub_le` — the clamped weight `s ↦ e^{1 - max s 0}` is Lipschitz with
  constant `e`.
* `ae_eq_expZ_of_solvesBSDEJ` — the Brownian integrand of a solution triple agrees with `expZ`
  almost everywhere for `P ⊗ dt` on `Ω × [0, 1]`.
* `energy_sub_cellAverage_le_of_solvesBSDEJ` — the cell-average error of the Brownian integrand
  of a solution triple has energy at most `(e δ) ^ 2` on the horizon.
* `exists_solvesBSDEJ_cellAverage_rate` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple obeys that bound.

## References

* Bouchard, B. & Elie, R., *Discrete-time approximation of decoupled Forward-Backward SDE with
  jumps*, Stochastic Processes Appl. **118(1)**, 2008, pp. 53–75.
* Delong, Ł., *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.BSDEJ.PathRegularity
open LevyStochCalc.Driver (LevyDriver)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The clamped exponential weight -/

/-- The exponential weight `e^{1-s}` clamped at the origin, `s ↦ e^{1 - max s 0}`. -/
noncomputable def expWeightClamp : ℝ → ℝ := fun s => Real.exp (1 - max s 0)

/-- At a nonnegative time the clamped weight is the exponential weight. -/
theorem expWeightClamp_of_nonneg {s : ℝ} (hs : 0 ≤ s) :
    expWeightClamp s = Real.exp (1 - s) := by
  show Real.exp (1 - max s 0) = Real.exp (1 - s)
  rw [max_eq_left hs]

/-- On `[0, ∞)` the decrements of `s ↦ e^{1-s}` are at most `e` times the increments of `s`. -/
theorem exp_sub_exp_le_of_le {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    Real.exp (1 - a) - Real.exp (1 - b) ≤ Real.exp 1 * (b - a) := by
  have hexp : Real.exp (1 - a) * Real.exp (a - b) = Real.exp (1 - b) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hfac : Real.exp (1 - a) - Real.exp (1 - b)
      = Real.exp (1 - a) * (1 - Real.exp (a - b)) := by
    rw [mul_sub, mul_one, hexp]
  have hone : 1 - Real.exp (a - b) ≤ b - a := by
    have h := Real.add_one_le_exp (a - b)
    linarith
  have hnn : 0 ≤ 1 - Real.exp (a - b) := by
    have h : Real.exp (a - b) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_zero] at h
    linarith
  have hle : Real.exp (1 - a) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by linarith)
  rw [hfac]
  exact mul_le_mul hle hone hnn (Real.exp_pos 1).le

/-- The clamped weight `s ↦ e^{1 - max s 0}` obeys the Lipschitz bound with constant `e`. -/
theorem abs_expWeightClamp_sub_le (s t : ℝ) :
    |expWeightClamp s - expWeightClamp t| ≤ Real.exp 1 * |s - t| := by
  have key : ∀ x y : ℝ, x ≤ y → expWeightClamp x - expWeightClamp y ≤ Real.exp 1 * (y - x) := by
    intro x y hxy
    have hx : (0 : ℝ) ≤ max x 0 := le_max_right _ _
    have hxy' : max x 0 ≤ max y 0 := max_le_max hxy le_rfl
    have hdiff : max y 0 - max x 0 ≤ y - x := by
      have h1 : y ≤ max x 0 + (y - x) := by
        have hml := le_max_left x (0 : ℝ)
        linarith
      have h2 : (0 : ℝ) ≤ max x 0 + (y - x) := by
        have hmr := le_max_right x (0 : ℝ)
        linarith
      have h3 := max_le h1 h2
      linarith
    have hE : Real.exp (1 - max x 0) - Real.exp (1 - max y 0)
        ≤ Real.exp 1 * (max y 0 - max x 0) := exp_sub_exp_le_of_le hx hxy'
    show Real.exp (1 - max x 0) - Real.exp (1 - max y 0) ≤ Real.exp 1 * (y - x)
    exact hE.trans (mul_le_mul_of_nonneg_left hdiff (Real.exp_pos 1).le)
  rcases le_total s t with h | h
  · have hmon : expWeightClamp t ≤ expWeightClamp s := by
      show Real.exp (1 - max t 0) ≤ Real.exp (1 - max s 0)
      have hst : max s 0 ≤ max t 0 := max_le_max h le_rfl
      exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ expWeightClamp s - expWeightClamp t),
      abs_of_nonpos (by linarith : s - t ≤ 0), neg_sub]
    exact key s t h
  · have hmon : expWeightClamp s ≤ expWeightClamp t := by
      show Real.exp (1 - max s 0) ≤ Real.exp (1 - max t 0)
      have hst : max t 0 ≤ max s 0 := max_le_max h le_rfl
      exact Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonpos (by linarith : expWeightClamp s - expWeightClamp t ≤ 0),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - t), neg_sub]
    exact key t s h

/-- On the window `(0, 1]` the windowed weight `expZ` is the clamped weight. -/
theorem expZ_eq_expWeightClamp {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) (ω : Ω) (i : Fin 1) :
    expZ Ω s ω i = expWeightClamp s := by
  rw [expZ_apply, Set.indicator_of_mem hs, expWeightClamp_of_nonneg hs.1.le]

/-! ### The Brownian integrand of a solution -/

/-- The Brownian integrand of a solution of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` agrees with `expZ` almost everywhere
for the product of the sample measure with Lebesgue measure on `[0, 1]`. -/
theorem ae_eq_expZ_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U') :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) 1))),
      Z' p.2 p.1 0 = expZ Ω p.2 p.1 0 := by
  obtain ⟨Y, hY, -⟩ := exists_solvesBSDEJ_expZ D
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
    rw [lintegral_generator_id_zero]
    exact ENNReal.zero_lt_top
  obtain ⟨-, huniq⟩ := exists_unique_solvesBSDEJ D (fun _ y _ _ => y) (L := 1) zero_le_one
    measurable_generator_id lipschitz_generator_id one_pos hf0 (memLp_brownian_one D.W)
    (aestronglyMeasurable_brownian_one_augJoint D)
  have hzero := (huniq Y' Y Z' (expZ Ω) U' (fun _ _ _ => (0 : ℝ)) h hY).2.1 0
  have hmZ : Measurable (Function.uncurry fun ω s => Z' s ω 0) := h.Z_meas 0
  have hmE : Measurable (Function.uncurry fun (ω : Ω) s => expZ Ω s ω 0) := expZ_meas 0
  have hmd : Measurable (Function.uncurry fun ω s => Z' s ω 0 - expZ Ω s ω 0) := hmZ.sub hmE
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ => Z' p.2 p.1 0 - expZ Ω p.2 p.1 0) 2
      (Brownian.Ito.energyMeasure P 1) = 0 := (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hmeas : Brownian.Ito.energyMeasure P 1
      = P.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) := rfl
  rw [hmeas] at hae
  filter_upwards [hae] with p hp
  have hp' : Z' p.2 p.1 0 - expZ Ω p.2 p.1 0 = 0 := hp
  linarith

/-! ### The pathwise cell average of a solution -/

omit [IsProbabilityMeasure P] in
/-- A Brownian integrand agreeing with `expZ` almost everywhere for the product of the sample
measure with Lebesgue measure on `[0, 1]` has, almost surely, the pathwise cell averages of the
clamped weight over every strictly monotone partition of `[0, 1]`. -/
theorem conditionalTimeAverage_eq_of_ae_eq {M : ℕ} {π : Fin (M + 1) → ℝ}
    {Z' : ℝ → Ω → (Fin 1 → ℝ)} (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = 1)
    (hZ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) 1))),
      Z' p.2 p.1 0 = expZ Ω p.2 p.1 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, conditionalTimeAverage_Z π Z' s ω 0
      = conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin 1) => expWeightClamp u) s ω 0 := by
  have hsub : ∀ n : Fin M, Set.Icc (π n.castSucc) (π n.succ) ⊆ Set.Icc (0 : ℝ) 1 := by
    intro n
    refine Set.Icc_subset_Icc ?_ ?_
    · rw [← h0]
      exact hmono.monotone (Fin.zero_le _)
    · rw [← hT]
      exact hmono.monotone (Fin.le_last _)
  filter_upwards [Measure.ae_ae_of_ae_prod hZ] with ω hω
  have hω' : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ Set.Icc (0 : ℝ) 1 → Z' u ω 0 = expZ Ω u ω 0 :=
    (ae_restrict_iff' measurableSet_Icc).mp hω
  have hint : ∀ n : Fin M, ∫ u in Set.Icc (π n.castSucc) (π n.succ), Z' u ω 0
      = ∫ u in Set.Icc (π n.castSucc) (π n.succ), expWeightClamp u := by
    intro n
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [hω', compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with u hu hu0 humem
    have hmem : u ∈ Set.Icc (0 : ℝ) 1 := hsub n humem
    have hne : u ≠ 0 := by simpa using hu0
    have hIoc : u ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hmem.1 (Ne.symm hne), hmem.2⟩
    rw [hu hmem, expZ_eq_expWeightClamp hIoc ω 0]
  intro s
  simp only [conditionalTimeAverage_Z]
  refine Finset.sum_congr rfl fun n _ => ?_
  by_cases hc : π n.castSucc < s ∧ s ≤ π n.succ
  · rw [if_pos hc, if_pos hc, hint n]
  · rw [if_neg hc, if_neg hc]

/-! ### The rate -/

/-- The cell-average error of the Brownian integrand of a solution of the backward equation with
generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`, over a strictly monotone
partition of `[0, 1]` of mesh at most `δ`, has energy at most `(e δ) ^ 2 * 1` on the horizon. -/
theorem energy_sub_cellAverage_le_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    {M : ℕ} {π : Fin (M + 1) → ℝ} {δ : ℝ} (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = 1) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ) :
    Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0 - conditionalTimeAverage_Z π Z' s ω 0)
      ≤ ENNReal.ofReal ((Real.exp 1 * δ) ^ 2 * 1) := by
  have hZ := ae_eq_expZ_of_solvesBSDEJ D h
  have hCA := conditionalTimeAverage_eq_of_ae_eq hmono h0 hT hZ
  have hnull : (volume.restrict (Set.Icc (0 : ℝ) 1)) {(0 : ℝ)} = 0 := by simp
  have hkey : Brownian.Ito.energy P 1
        (fun ω s => Z' s ω 0 - conditionalTimeAverage_Z π Z' s ω 0)
      = Brownian.Ito.energy P 1 (fun ω s => expWeightClamp s
          - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin 1) => expWeightClamp u)
              s ω 0) := by
    simp only [Brownian.Ito.energy]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hZ, hCA] with ω h1 h2
    refine lintegral_congr_ae ?_
    filter_upwards [h1, compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with
      s hs1 hs0 hsmem
    have hne : s ≠ 0 := by simpa using hs0
    have hIoc : s ∈ Set.Ioc (0 : ℝ) 1 := ⟨lt_of_le_of_ne hsmem.1 (Ne.symm hne), hsmem.2⟩
    rw [hs1, expZ_eq_expWeightClamp hIoc ω 0, h2 s]
  rw [hkey]
  exact energy_sub_conditionalTimeAverage_le_of_lipschitz P hmono h0 hT hδ
    abs_expWeightClamp_sub_le (0 : Fin 1)

/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a solution triple of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`; for every solution triple of that
equation and every strictly monotone partition of `[0, 1]` of mesh at most `δ`, the energy of
the difference between the Brownian integrand and its pathwise cell average over the partition
is at most `(e δ) ^ 2`. -/
theorem exists_solvesBSDEJ_cellAverage_rate :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            ∀ (M : ℕ) (π : Fin (M + 1) → ℝ) (δ : ℝ), StrictMono π → π 0 = 0 →
              π (Fin.last M) = 1 → (∀ n : Fin M, π n.succ - π n.castSucc ≤ δ) →
                Brownian.Ito.energy P 1
                    (fun ω s => Z' s ω 0 - conditionalTimeAverage_Z π Z' s ω 0)
                  ≤ ENNReal.ofReal ((Real.exp 1 * δ) ^ 2) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_generator_id D,
    fun Y' Z' U' h M π δ hmono h0 hT hδ => ?_⟩
  have hrate := energy_sub_cellAverage_le_of_solvesBSDEJ D h hmono h0 hT hδ
  rwa [mul_one] at hrate

/-! ### The uniform partition -/

/-- The uniform partition `n ↦ n / M` of the horizon `[0, 1]` into `M` cells. -/
noncomputable def uniformPartition (M : ℕ) : Fin (M + 1) → ℝ := fun n => (n : ℝ) / M

variable {M : ℕ}

/-- The uniform partition of `[0, 1]` into a positive number of cells is strictly monotone. -/
theorem strictMono_uniformPartition (hM : 0 < M) : StrictMono (uniformPartition M) := by
  intro a b hab
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hlt : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := Nat.cast_lt.mpr (Fin.lt_def.mp hab)
  exact div_lt_div_of_pos_right hlt hMpos

/-- The uniform partition starts at the left endpoint of `[0, 1]`. -/
theorem uniformPartition_zero : uniformPartition M 0 = 0 := by
  show (((0 : Fin (M + 1)) : ℕ) : ℝ) / M = 0
  simp

/-- The uniform partition into a positive number of cells ends at the right endpoint of
`[0, 1]`. -/
theorem uniformPartition_last (hM : 0 < M) : uniformPartition M (Fin.last M) = 1 := by
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  show (((Fin.last M : Fin (M + 1)) : ℕ) : ℝ) / M = 1
  rw [Fin.val_last, div_self hMne]

/-- Every cell of the uniform partition into `M` cells has length `1 / M`. -/
theorem uniformPartition_mesh_eq (hM : 0 < M) (n : Fin M) :
    uniformPartition M n.succ - uniformPartition M n.castSucc = 1 / M := by
  have hMne : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  show (((n.succ : Fin (M + 1)) : ℕ) : ℝ) / M - (((n.castSucc : Fin (M + 1)) : ℕ) : ℝ) / M
    = 1 / M
  rw [Fin.val_succ, Fin.val_castSucc, div_sub_div_same]
  push_cast
  ring_nf

/-- The mesh of the uniform partition into `M` cells is at most `1 / M`. -/
theorem uniformPartition_mesh (hM : 0 < M) (n : Fin M) :
    uniformPartition M n.succ - uniformPartition M n.castSucc ≤ 1 / M :=
  (uniformPartition_mesh_eq hM n).le

/-! ### The rate along the uniform partitions -/

/-- The cell-average error of the Brownian integrand of a solution of the backward equation with
generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`, over the uniform partition
of `[0, 1]` into `M` cells, has energy at most `(e / M) ^ 2` on the horizon. -/
theorem energy_sub_cellAverage_le_of_solvesBSDEJ_uniform
    (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U')
    (hM : 0 < M) :
    Brownian.Ito.energy P 1
        (fun ω s => Z' s ω 0 - conditionalTimeAverage_Z (uniformPartition M) Z' s ω 0)
      ≤ ENNReal.ofReal ((Real.exp 1 / M) ^ 2) := by
  have hrate := energy_sub_cellAverage_le_of_solvesBSDEJ D h (strictMono_uniformPartition hM)
    uniformPartition_zero (uniformPartition_last hM) (uniformPartition_mesh hM)
  have heq : (Real.exp 1 * (1 / M)) ^ 2 * 1 = (Real.exp 1 / M) ^ 2 := by
    rw [mul_one, mul_one_div]
  rwa [heq] at hrate

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1` and a solution triple of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1`; for every solution triple of that
equation and every positive `M`, the energy of the difference between the Brownian integrand and
its pathwise cell average over the uniform partition of `[0, 1]` into `M` cells is at most
`(e / M) ^ 2`. -/
theorem exists_solvesBSDEJ_cellAverage_rate_uniform :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin 1 → ℝ)) (U : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y Z U) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            ∀ M : ℕ, 0 < M →
              Brownian.Ito.energy P 1
                  (fun ω s => Z' s ω 0
                    - conditionalTimeAverage_Z (uniformPartition M) Z' s ω 0)
                ≤ ENNReal.ofReal ((Real.exp 1 / M) ^ 2) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_generator_id D,
    fun _ _ _ h M hM => energy_sub_cellAverage_le_of_solvesBSDEJ_uniform D h hM⟩

end LevyStochCalc.Examples.Nonvacuity
