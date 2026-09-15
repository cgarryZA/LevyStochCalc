/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc
import NonvacuityDrivers
import NonvacuityBSDEJZ

/-!
# A backward equation with jumps whose jump integrand carries positive energy

The scalar backward equation

  `Y_t = ξ − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1`, the jump integrand
is the window indicator `1_{(0, 1]}`, constant in the mark, and the terminal datum is its
compensated integral over the whole horizon, so the value process is that compensated integral
and the Brownian integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_jump` — the equation is solved by a càdlàg version of the compensated
  integral of `1_{(0, 1]}` together with the integrand pair `(0, 1_{(0, 1]})`.
* `markedEnergy_jumpU` — the marked energy of `1_{(0, 1]}` on `[0, 1]` for the intensity `δ_1`
  is `1`.
* `markedEnergy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has jump
  integrand of marked energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_markedEnergy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has jump integrand of nonzero marked
  energy on the horizon.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

/-- A deterministic time indicator, constant in the sample point and in the mark, is marked
progressively measurable for every filtration. -/
theorem markedProgressivelyMeasurable_window {E : Type v} [MeasurableSpace E]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {S : Set ℝ} (hS : MeasurableSet S) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun (_ : Ω) (s : ℝ) (_ : E) => Set.indicator S (fun _ => (1 : ℝ)) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hg : Measurable fun r : ℝ =>
      (Set.Iic t).indicator (fun s => Set.indicator S (fun _ => (1 : ℝ)) s) r :=
    (measurable_const.indicator hS).indicator measurableSet_Iic
  exact (hg.comp measurable_snd.fst).stronglyMeasurable

/-- The indicator of the window `(0, 1]`, read as a jump integrand constant in the mark. -/
noncomputable def jumpU (Ω : Type u) : ℝ → Ω → ℝ → ℝ :=
  fun s _ _ => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s

omit [MeasurableSpace Ω] in
/-- The value of `jumpU` at a time is the indicator of `(0, 1]` at that time. -/
theorem jumpU_apply (s : ℝ) (ω : Ω) (e : ℝ) :
    jumpU Ω s ω e = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s := rfl

/-- The zero one-dimensional Brownian integrand. -/
def zeroZ (Ω : Type u) : ℝ → Ω → (Fin 1 → ℝ) := fun _ _ _ => (0 : ℝ)

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

/-- `jumpU` is jointly measurable in the sample point, the time and the mark. -/
theorem jumpU_meas : Measurable fun p : Ω × ℝ × ℝ => jumpU Ω p.2.1 p.1 p.2.2 := by
  have h : Measurable fun s : ℝ => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s :=
    measurable_const.indicator measurableSet_Ioc
  exact h.comp measurable_snd.fst

/-- `jumpU` is marked progressively measurable for the augmented joint filtration. -/
theorem jumpU_prog :
    Probability.MarkedProgressivelyMeasurable (augJoint D) fun ω s e => jumpU Ω s ω e :=
  markedProgressivelyMeasurable_window (E := ℝ) (augJoint D) (S := Set.Ioc (0 : ℝ) 1)
    measurableSet_Ioc

omit [MeasurableSpace Ω] in
/-- `jumpU` vanishes off the horizon `[0, 1]`. -/
theorem jumpU_vanish (ω : Ω) (s e : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) : jumpU Ω s ω e = 0 := by
  have hs' : s ∉ Set.Ioc (0 : ℝ) 1 := fun h => hs ⟨h.1.le, h.2⟩
  simp [jumpU, Set.indicator_of_notMem hs']

/-- The marked energy of `jumpU` on the horizon `[0, 1]` for the intensity `δ_1` is `1`. -/
theorem markedEnergy_jumpU :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => jumpU Ω s ω e) = 1 := by
  have hpt : ∀ (ω : Ω) (s : ℝ),
      ∫⁻ e, (‖jumpU Ω s ω e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)
        = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) s := by
    intro ω s
    rw [lintegral_dirac]
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [jumpU, hs]
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
      (∫⁻ e, (‖jumpU Ω s ω e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)) ∂volume = 1 := by
    intro ω
    simp only [hpt]
    rw [lintegral_indicator measurableSet_Ioc, lintegral_one,
      Measure.restrict_apply_univ, Measure.restrict_apply' measurableSet_Icc]
    rw [Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self, Real.volume_Ioc]
    simp
  rw [Poisson.Compensated.markedEnergy]
  simp only [hinner]
  simp

/-- `jumpU` has finite marked energy on the horizon `[0, 1]`. -/
theorem jumpU_sq : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
    (fun ω s e => jumpU Ω s ω e) ≠ ⊤ := by
  rw [markedEnergy_jumpU]
  exact ENNReal.one_ne_top

/-- Each coordinate of `zeroZ` is jointly measurable. -/
theorem zeroZ_meas (i : Fin 1) :
    Measurable (Function.uncurry fun (ω : Ω) s => zeroZ Ω s ω i) := measurable_const

/-- Each coordinate of `zeroZ` is progressively measurable for the augmented joint
filtration. -/
theorem zeroZ_prog (i : Fin 1) :
    Probability.ProgressivelyMeasurable (augJoint D) fun (ω : Ω) s => zeroZ Ω s ω i :=
  Probability.progressivelyMeasurable_zero (augJoint D)

omit [MeasurableSpace Ω] in
/-- `zeroZ` vanishes off the horizon `[0, 1]`. -/
theorem zeroZ_vanish (ω : Ω) (s : ℝ) (_hs : s ∉ Set.Icc (0 : ℝ) 1) : zeroZ Ω s ω = 0 := rfl

/-- Each coordinate of `zeroZ` has finite energy on the horizon `[0, 1]`. -/
theorem zeroZ_sq (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun (ω : Ω) s => zeroZ Ω s ω i) ≠ ⊤ := by
  simp [Brownian.Ito.energy, zeroZ]

/-- The compensated Itô–Lévy integral of `jumpU` for the augmented joint filtration of `D`. -/
noncomputable def jumpLeg : ℝ → Ω → ℝ :=
  Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
    (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
    (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq)

/-- The Brownian leg of `zeroZ` vanishes almost surely at every time. -/
theorem brownianLeg_zeroZ_ae_zero (t : ℝ) :
    ∀ᵐ ω ∂P, Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
      D.isBrownianFiltration_aug (zeroZ Ω) zeroZ_meas (zeroZ_prog D)
      (sq_int_global_of_vanishing zeroZ_vanish zeroZ_sq) t ω = 0 := by
  filter_upwards [Brownian.Ito.stochasticIntegralBrownian_ae_zero (D.W.W 0) (augJoint D)
    (D.isBrownianFiltration_aug 0) (zeroZ_meas 0) (zeroZ_prog D 0)
    (sq_int_global_of_vanishing zeroZ_vanish zeroZ_sq 0) t] with ω hω
  show Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
      D.isBrownianFiltration_aug (zeroZ Ω) zeroZ_meas (zeroZ_prog D)
      (sq_int_global_of_vanishing zeroZ_vanish zeroZ_sq) t ω = 0
  rw [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, Fin.sum_univ_one]
  exact hω

/-- The compensated integral of `jumpU` at the horizon is square integrable. -/
theorem memLp_jumpLeg_one : MemLp (jumpLeg D 1) 2 P :=
  Poisson.Compensated.stochasticIntegral_memLp D.N (augJoint D) D.isPoissonFiltration_aug
    (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
    (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq) 1

/-- The compensated integral of `jumpU` at the horizon is measurable for the augmented joint
filtration at the horizon. -/
theorem aestronglyMeasurable_jumpLeg_one :
    AEStronglyMeasurable[augJoint D 1] (jumpLeg D 1) P :=
  ((Poisson.Compensated.process_stronglyAdapted D.N (augJoint D) D.isPoissonFiltration_aug
      (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
      (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq) 1).aestronglyMeasurable).congr
    (Poisson.Compensated.stochasticIntegral_ae_eq_process D.N (augJoint D)
      D.isPoissonFiltration_aug (fun ω s e => jumpU Ω s ω e) jumpU_meas (jumpU_prog D)
      (marked_sq_int_global_of_vanishing jumpU_vanish jumpU_sq) 1).symm

end Fields

/-! ### A solution triple with a nonzero jump integrand -/

/-- The backward equation with vanishing generator, terminal datum the compensated integral of
`1_{(0, 1]}` at time `1` and horizon `1` is solved by a càdlàg version of that compensated
integral, the zero Brownian integrand and the jump integrand `1_{(0, 1]}`. -/
theorem exists_solvesBSDEJ_jump (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y (zeroZ Ω) (jumpU Ω) ∧
        ∀ t, Y t =ᵐ[P] jumpLeg D t := by
  obtain ⟨M, hadapt, hmeas, hae, hcadlag, -, -, hsup⟩ :=
    exists_cadlag_poissonLeg D 1 zero_le_one (jumpU Ω) jumpU_meas (jumpU_prog D)
      jumpU_vanish jumpU_sq
  refine ⟨M, ?_, hae⟩
  refine
    { Z_meas := zeroZ_meas
      Z_prog := zeroZ_prog D
      Z_vanish := zeroZ_vanish
      Z_sq := zeroZ_sq
      U_meas := jumpU_meas
      U_prog := jumpU_prog D
      U_vanish := jumpU_vanish
      U_sq := jumpU_sq
      Y_meas := hmeas
      Y_adapted := hadapt
      Y_cadlag := hcadlag
      Y_sup := hsup
      eqn := ?_ }
  intro t ht
  filter_upwards [brownianLeg_zeroZ_ae_zero D 1, brownianLeg_zeroZ_ae_zero D t,
    hae t] with ω e1 e2 e3
  rw [e1, e2, e3, integral_zero]
  simp only [jumpLeg]
  ring

/-! ### The marked energy of the jump integrand -/

/-- The jump integrand of a solution of the backward equation with vanishing generator,
terminal datum the compensated integral of `1_{(0, 1]}` at time `1` and horizon `1` has marked
energy `1` on `[0, 1]`. -/
theorem markedEnergy_eq_one_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U') :
    Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
      (fun ω s e => U' s ω e) = 1 := by
  obtain ⟨Y, hY, -⟩ := exists_solvesBSDEJ_jump D
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by simp
  obtain ⟨-, huniq⟩ := exists_unique_solvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (L := 0) le_rfl
    measurable_generator_zero lipschitz_generator_zero zero_lt_one hf0 (memLp_jumpLeg_one D)
    (aestronglyMeasurable_jumpLeg_one D)
  have hzero := (huniq Y' Y Z' (zeroZ Ω) U' (jumpU Ω) h hY).2.2
  have hmU : Measurable fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2 := h.U_meas
  have hmJ : Measurable fun p : Ω × ℝ × ℝ => jumpU Ω p.2.1 p.1 p.2.2 := jumpU_meas
  have hmd : Measurable fun p : Ω × ℝ × ℝ =>
      U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2 := hmU.sub hmJ
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq
    (φ := fun ω s e => U' s ω e - jumpU Ω s ω e) hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2) 2
      (Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (1 : ℝ)) 1) = 0 :=
    (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hae2 : (fun p : Ω × ℝ × ℝ => U' p.2.1 p.1 p.2.2)
      =ᵐ[Poisson.Compensated.markedEnergyMeasure P (Measure.dirac (1 : ℝ)) 1]
        fun p : Ω × ℝ × ℝ => jumpU Ω p.2.1 p.1 p.2.2 := by
    filter_upwards [hae] with p hp
    have hp' : U' p.2.1 p.1 p.2.2 - jumpU Ω p.2.1 p.1 p.2.2 = 0 := hp
    linarith
  rw [Poisson.Compensated.markedEnergy_eq_eLpNorm_sq (φ := fun ω s e => U' s ω e) hmU 1,
    eLpNorm_congr_ae hae2, ← Poisson.Compensated.markedEnergy_eq_eLpNorm_sq
      (φ := fun ω s e => jumpU Ω s ω e) hmJ 1]
  exact markedEnergy_jumpU

/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1`, and a solution triple of the backward equation with vanishing generator,
terminal datum the compensated integral of `1_{(0, 1]}` at time `1` and horizon `1` whose jump
integrand is `1_{(0, 1]}`, of marked energy `1` on the horizon; the jump integrand of every
solution triple of that equation has nonzero marked energy on the horizon. -/
theorem exists_solvesBSDEJ_markedEnergy_ne_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ Y : ℝ → Ω → ℝ,
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y (zeroZ Ω) (jumpU Ω) ∧
            ∀ t, Y t =ᵐ[P] jumpLeg D t) ∧
        Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
            (fun ω s e => jumpU Ω s ω e) = 1 ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (jumpLeg D 1) 1 Y' Z' U' →
            Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
              (fun ω s e => U' s ω e) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_jump D, markedEnergy_jumpU,
    fun _ _ _ h => by rw [markedEnergy_eq_one_of_solvesBSDEJ D h]; exact one_ne_zero⟩

end LevyStochCalc.Examples.Nonvacuity
