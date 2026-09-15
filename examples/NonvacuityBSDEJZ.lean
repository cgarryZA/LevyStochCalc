/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc
import NonvacuityDrivers

/-!
# A backward equation with jumps whose Brownian integrand carries positive energy

The scalar backward equation

  `Y_t = W_1 − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator vanishes, the horizon is `T = 1` and the terminal
datum is the Brownian value `W_1`, so the value process is the Brownian motion itself, the
Brownian integrand is the indicator `1_{(0, 1]}` of the horizon and the jump integrand is `0`.

## Main statements

* `exists_solvesBSDEJ_windowZ` — the equation is solved by a continuous modification of the
  Brownian motion together with the integrand pair `(1_{(0, 1]}, 0)`.
* `energy_windowZ` — the energy of `1_{(0, 1]}` on `[0, 1]` is `1`.
* `energy_eq_one_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand
  of energy `1` on `[0, 1]`.
* `exists_solvesBSDEJ_energy_ne_zero` — on a probability space carrying such a driver the
  equation has a solution triple and every solution triple has Brownian integrand of nonzero
  energy.

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

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The integrands of the equation -/

/-- The indicator of the window `(0, 1]`, read as a one-dimensional Brownian integrand. -/
noncomputable def windowZ (Ω) [MeasurableSpace Ω] : ℝ → Ω → (Fin 1 → ℝ) :=
  fun s ω _ => Brownian.Ito.indIoc Ω 0 1 ω s

/-- The value of `windowZ` at a time is the indicator of `(0, 1]` at that time. -/
theorem windowZ_apply (s : ℝ) (ω : Ω) (i : Fin 1) :
    windowZ Ω s ω i = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ)) s := rfl

section Fields

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

/-- Each coordinate of `windowZ` is jointly measurable. -/
theorem windowZ_meas (i : Fin 1) :
    Measurable (Function.uncurry fun (ω : Ω) s => windowZ Ω s ω i) :=
  Brownian.Ito.measurable_uncurry_indIoc 0 1

/-- Each coordinate of `windowZ` is progressively measurable for the augmented joint
filtration. -/
theorem windowZ_prog (i : Fin 1) :
    Probability.ProgressivelyMeasurable (augJoint D) fun ω s => windowZ Ω s ω i :=
  Brownian.Ito.progressivelyMeasurable_indIoc₀ (augJoint D) zero_lt_one

/-- `windowZ` vanishes off the horizon `[0, 1]`. -/
theorem windowZ_vanish (ω : Ω) (s : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) : windowZ Ω s ω = 0 := by
  have hs' : s ∉ Set.Ioc (0 : ℝ) 1 := fun h => hs ⟨h.1.le, h.2⟩
  funext i
  simp [windowZ, Brownian.Ito.indIoc, Set.indicator_of_notMem hs']

/-- Each coordinate of `windowZ` has finite energy on the horizon `[0, 1]`. -/
theorem windowZ_sq (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => windowZ Ω s ω i) ≠ ⊤ :=
  (Brownian.Ito.lintegral_sq_indIoc_lt_top P 0 1 1 zero_lt_one).ne

/-- The zero jump integrand is jointly measurable in the sample point, the time and the mark. -/
theorem zeroU_meas : Measurable fun _p : Ω × ℝ × ℝ => (0 : ℝ) := measurable_const

/-- The zero jump integrand is marked progressively measurable for the augmented joint
filtration. -/
theorem zeroU_prog : Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ) :=
  Poisson.Compensated.markedProgressivelyMeasurable_zero (augJoint D)

/-- The zero jump integrand has finite marked energy on the horizon `[0, 1]`. -/
theorem zeroU_sq : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
    (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) ≠ ⊤ := by
  simp [Poisson.Compensated.markedEnergy]

end Fields

/-! ### A solution triple with the indicator integrand -/

/-- The backward equation with vanishing generator, terminal datum `W_1` and horizon `1` is
solved by a continuous modification of the Brownian motion, the integrand `1_{(0, 1]}` in the
Brownian coordinate and the zero jump integrand. -/
theorem exists_solvesBSDEJ_windowZ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y (windowZ Ω)
          (fun _ _ _ => (0 : ℝ)) ∧
        ∀ t, Y t =ᵐ[P] fun ω => (D.W.W 0).W t ω := by
  obtain ⟨N, hsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (MeasureTheory.ae_iff.1 (D.W.W 0).continuous_paths)
  have hnotN : ∀ᵐ ω ∂P, ω ∈ Nᶜ := by
    rw [MeasureTheory.ae_iff]
    simpa using hNnull
  refine ⟨fun t => Set.indicator Nᶜ ((D.W.W 0).W t), ?_, ?_⟩
  · refine
      { Z_meas := windowZ_meas
        Z_prog := windowZ_prog D
        Z_vanish := windowZ_vanish
        Z_sq := windowZ_sq
        U_meas := zeroU_meas
        U_prog := zeroU_prog D
        U_vanish := fun _ _ _ _ => rfl
        U_sq := zeroU_sq
        Y_meas := ?_
        Y_adapted := ?_
        Y_cadlag := ?_
        Y_sup := ?_
        eqn := ?_ }
    · have hfun : (Function.uncurry fun t => Set.indicator Nᶜ ((D.W.W 0).W t))
          = Set.indicator (Prod.snd ⁻¹' Nᶜ) (Function.uncurry (D.W.W 0).W) := by
        funext p
        by_cases hp : p.2 ∈ Nᶜ
        · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Nᶜ from hp)]
          exact Set.indicator_of_mem hp _
        · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Nᶜ from hp)]
          exact Set.indicator_of_notMem hp _
      rw [hfun]
      exact (D.W.W 0).joint_measurable.indicator (measurable_snd hNmeas.compl)
    · intro t
      have hle0 : augJoint D 0 ≤ augJoint D t := by
        rcases le_total (0 : ℝ) t with h | h
        · exact (augJoint D).mono h
        · exact D.augFiltration_le_of_nonpos h
      have hNt : MeasurableSet[augJoint D t] Nᶜ :=
        (hle0 _ (D.measurableSet_augFiltration_of_null hNmeas hNnull)).compl
      have hW : Measurable[augJoint D t] ((D.W.W 0).W t) :=
        (D.isBrownianFiltration_aug 0).measurable t
      exact (hW.indicator hNt).mono ((augJoint D).le_rightCont t) le_rfl
    · intro ω t
      by_cases hω : ω ∈ N
      · have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = 0 :=
          fun s => Set.indicator_of_notMem (by simpa using hω) _
        simp only [hpt]
        exact ⟨tendsto_const_nhds, 0, tendsto_const_nhds⟩
      · have hcont : Continuous fun s => (D.W.W 0).W s ω := by
          by_contra hc
          exact hω (hsub hc)
        have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = (D.W.W 0).W s ω :=
          fun s => Set.indicator_of_mem hω _
        simp only [hpt]
        exact ⟨(hcont.tendsto t).mono_left nhdsWithin_le_nhds, (D.W.W 0).W t ω,
          (hcont.tendsto t).mono_left nhdsWithin_le_nhds⟩
    · have hcongr : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1,
          (‖Set.indicator Nᶜ ((D.W.W 0).W t) ω‖₊ : ℝ≥0∞) ^ 2) ∂P
          = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) 1, (‖(D.W.W 0).W t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hnotN] with ω hω
        exact iSup_congr fun t => iSup_congr fun _ => by rw [Set.indicator_of_mem hω]
      have hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, Filter.Tendsto (fun s => (D.W.W 0).W s ω)
          (nhdsWithin t (Set.Ioi t)) (nhds ((D.W.W 0).W t ω)) := by
        filter_upwards [(D.W.W 0).continuous_paths] with ω hω t
        exact (hω.tendsto t).mono_left nhdsWithin_le_nhds
      have hdoob := BSDEJ.SupBound.lintegral_biSup_sq_le_of_martingale (μ := P)
        (Brownian.Martingale.brownian_martingale_natural (D.W.W 0)) zero_le_one hcad
      rw [hcongr]
      refine lt_of_le_of_lt hdoob ?_
      rw [lintegral_nnnorm_sq_brownian (D.W.W 0) zero_lt_one]
      exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
    · intro t ht
      have hI : ∀ t' : ℝ, 0 ≤ t' → ∀ᵐ ω ∂P,
          Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
              D.isBrownianFiltration_aug (windowZ Ω) windowZ_meas (windowZ_prog D)
              (sq_int_global_of_vanishing windowZ_vanish windowZ_sq) t' ω
            = (D.W.W 0).W (min 1 t') ω - (D.W.W 0).W (min 0 t') ω := by
        intro t' ht'
        filter_upwards [Brownian.Ito.stochasticIntegralBrownian_indIoc (D.W.W 0) (augJoint D)
          (D.isBrownianFiltration_aug 0) (a := 0) (b := 1) le_rfl zero_lt_one
          (windowZ_meas 0) (windowZ_prog D 0)
          (sq_int_global_of_vanishing windowZ_vanish windowZ_sq 0) ht'] with ω hω
        have hsum : Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
              D.isBrownianFiltration_aug (windowZ Ω) windowZ_meas (windowZ_prog D)
              (sq_int_global_of_vanishing windowZ_vanish windowZ_sq) t' ω
            = Brownian.Ito.stochasticIntegralBrownian (D.W.W 0) (augJoint D)
              (D.isBrownianFiltration_aug 0) (Brownian.Ito.indIoc Ω 0 1) (windowZ_meas 0)
              (windowZ_prog D 0) (sq_int_global_of_vanishing windowZ_vanish windowZ_sq 0)
              t' ω := by
          simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
            Fin.sum_univ_one]
          rfl
        rw [hsum]
        exact hω
      have hJ : ∀ t' : ℝ, 0 ≤ t' → ∀ᵐ ω ∂P,
          Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
              (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) zeroU_meas (zeroU_prog D)
              (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) zeroU_sq) t' ω = 0 := by
        intro t' ht'
        filter_upwards [Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing D.N
          D.isPoissonFiltration_aug (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) zeroU_meas
          (zeroU_prog D) (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) zeroU_sq)
          ht' (fun _ _ _ _ => rfl)] with ω hω
        simpa using hω
      filter_upwards [hI 1 zero_le_one, hI t ht.1, hJ 1 zero_le_one, hJ t ht.1,
        (D.W.W 0).initial_zero, hnotN] with ω e1 e2 e3 e4 e5 e6
      rw [min_self, min_eq_left zero_le_one] at e1
      rw [min_eq_right ht.2, min_eq_left ht.1] at e2
      rw [Set.indicator_of_mem e6, integral_zero]
      linarith
  · intro t
    filter_upwards [hnotN] with ω hω
    exact Set.indicator_of_mem hω _

/-! ### The energy of the Brownian integrand -/

/-- The energy of `windowZ` on the horizon `[0, 1]` is `1`. -/
theorem energy_windowZ (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => windowZ Ω s ω i) = 1 := by
  have hpt : ∀ (ω : Ω) (s : ℝ), (‖windowZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2
      = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun _ => (1 : ℝ≥0∞)) s := by
    intro ω s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [windowZ, Brownian.Ito.indIoc, hs]
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
      (‖windowZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume = 1 := by
    intro ω
    simp only [hpt]
    rw [lintegral_indicator measurableSet_Ioc, lintegral_one,
      Measure.restrict_apply_univ, Measure.restrict_apply' measurableSet_Icc]
    rw [Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self, Real.volume_Ioc]
    simp
  rw [Brownian.Ito.energy]
  simp [hinner]

/-- The vanishing generator is measurable in `(s, y, z)` at each fixed jump variable. -/
theorem measurable_generator_zero (_u : ℝ → ℝ) :
    Measurable fun _r : ℝ × ℝ × (Fin 1 → ℝ) => (0 : ℝ) := measurable_const

/-- The vanishing generator obeys the `L²(ν)` Lipschitz bound with constant `0`. -/
theorem lipschitz_generator_zero (_s y₁ y₂ : ℝ) (z₁ z₂ : Fin 1 → ℝ) (u₁ u₂ : ℝ → ℝ) :
    (‖(0 : ℝ) - (0 : ℝ)‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal 0 *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂Measure.dirac (1 : ℝ)) ^ (1 / 2 : ℝ)) := by
  simp

/-- The Brownian integrand of a solution of the backward equation with vanishing generator,
terminal datum `W_1` and horizon `1` has energy `1` on `[0, 1]`. -/
theorem energy_eq_one_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U') :
    Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0) = 1 := by
  obtain ⟨Y, hY, -⟩ := exists_solvesBSDEJ_windowZ D
  have hξ2 : MemLp (fun ω => (D.W.W 0).W 1 ω) 2 P :=
    Brownian.Martingale.brownianMotion_memLp_2 (D.W.W 0) 1
  have hξm : AEStronglyMeasurable[augJoint D 1] (fun ω => (D.W.W 0).W 1 ω) P := by
    have hnat : StronglyMeasurable[Brownian.Martingale.naturalFiltration (D.W.W 0) 1]
        ((D.W.W 0).W 1) :=
      MeasureTheory.Filtration.stronglyAdapted_natural
        (u := (D.W.W 0).W) (fun t => ((D.W.W 0).measurable_eval t).stronglyMeasurable) 1
    have hle : Brownian.Martingale.naturalFiltration (D.W.W 0) 1 ≤ augJoint D 1 :=
      ((D.W.naturalFiltration_coord_le 0 1).trans (D.naturalFiltration_brownian_le 1)).trans
        (Brownian.le_augFiltration D.filtration P 1)
    exact (hnat.mono hle).aestronglyMeasurable
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by simp
  obtain ⟨-, huniq⟩ := exists_unique_solvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (L := 0) le_rfl
    measurable_generator_zero lipschitz_generator_zero zero_lt_one hf0 hξ2 hξm
  have hzero := (huniq Y' Y Z' (windowZ Ω) U' (fun _ _ _ => (0 : ℝ)) h hY).2.1 0
  have hmZ : Measurable (Function.uncurry fun ω s => Z' s ω 0) := h.Z_meas 0
  have hmW : Measurable (Function.uncurry fun (ω : Ω) s => windowZ Ω s ω 0) := windowZ_meas 0
  have hmd : Measurable (Function.uncurry fun ω s => Z' s ω 0 - windowZ Ω s ω 0) := hmZ.sub hmW
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ => Z' p.2 p.1 0 - windowZ Ω p.2 p.1 0) 2
      (Brownian.Ito.energyMeasure P 1) = 0 := (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hae2 : (fun p : Ω × ℝ => Z' p.2 p.1 0)
      =ᵐ[Brownian.Ito.energyMeasure P 1] fun p : Ω × ℝ => windowZ Ω p.2 p.1 0 := by
    filter_upwards [hae] with p hp
    have hp' : Z' p.2 p.1 0 - windowZ Ω p.2 p.1 0 = 0 := hp
    linarith
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmZ 1, eLpNorm_congr_ae hae2,
    ← Brownian.Ito.energy_eq_eLpNorm_sq hmW 1]
  exact energy_windowZ 0

/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1`, and a solution triple of the backward equation with vanishing generator,
terminal datum `W_1` and horizon `1` whose Brownian integrand is `1_{(0, 1]}`, of energy `1` on
the horizon; the Brownian integrand of every solution triple of that equation has nonzero energy
on the horizon. -/
theorem exists_solvesBSDEJ_energy_ne_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ Y : ℝ → Ω → ℝ,
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y (windowZ Ω)
              (fun _ _ _ => (0 : ℝ)) ∧
            ∀ t, Y t =ᵐ[P] fun ω => (D.W.W 0).W t ω) ∧
        Brownian.Ito.energy P 1 (fun ω s => windowZ Ω s ω 0) = 1 ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ _ _ _ => (0 : ℝ)) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  exact ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_windowZ D, energy_windowZ 0,
    fun _ _ _ h => by rw [energy_eq_one_of_solvesBSDEJ D h]; exact one_ne_zero⟩

end LevyStochCalc.Examples.Nonvacuity
