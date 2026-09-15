/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc
import NonvacuityItoLevy

/-!
# The value at time `1` of the jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`

For the coefficients `coeffs` (`μ = 0`, `σ = 1`, `γ(s, x, e) = e`) and the jump intensity
`δ₁`, a path solving the jump-diffusion integral equation from `0` relative to a filtration
carrying both driver properties has second moment `2` in its single coordinate at time `1`:
the drift vanishes, the Brownian leg contributes `∫_0^1 1 ds = 1`, the compensated leg
contributes `∫_0^1 ∫_ℝ e² δ₁(de) ds = 1`, and the two legs are orthogonal. In particular that
coordinate is not almost surely `0` at time `1`.

The second moment is the expectation form of the quadratic Itô formula,
`LevyStochCalc.Ito.SecondMoment.integral_mul_self_eq_of_isItoLevyProcess`, whose orthogonality
input is a cross witness for the filtration; `crossWitnessAugRightCont` carries the driver's
own witness to the augmented right-continuation of the joint filtration, the filtration at
which `LevyStochCalc.Ito.Picard.exists_globalSolution` produces a solution.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Ito.Picard (SolvesOn eqn_sum_form exists_globalSolution)
open LevyStochCalc.Ito.Setting (IsItoLevyProcess)

universe u v

/-- The drift of the coefficients of the scalar jump diffusion `dX_t = dW_t + ∫_ℝ e Ñ(dt, de)`
vanishes. -/
theorem coeffs_mu_apply (s : ℝ) (x : Fin 1 → ℝ) (i : Fin 1) : coeffs.μ s x i = 0 := rfl

/-! ### A cross witness at the augmented right-continuation -/

/-- The right-continuation of a filtration is monotone in the filtration. -/
theorem rightCont_mono_of_le {Ω : Type u} {m : MeasurableSpace Ω}
    {ℱ 𝒢 : MeasureTheory.Filtration ℝ m} (h : ∀ t : ℝ, ℱ t ≤ 𝒢 t) (t : ℝ) :
    ℱ.rightCont t ≤ 𝒢.rightCont t := by
  rw [ℱ.rightCont_eq t, 𝒢.rightCont_eq t]
  exact iInf₂_mono fun j _ => h j

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The cross witness of a Lévy driver at the filtration obtained by right-continuing and then
augmenting by the null sets. -/
noncomputable def crossWitnessAugRightCont {E : Type v} [MeasurableSpace E] {ν : Measure E}
    [SigmaFinite ν] {d : ℕ} {D : LevyDriver P d ν}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} (𝒲 : D.CrossWitness ℱ) :
    D.CrossWitness (Brownian.augFiltration ℱ.rightCont P) where
  poissonLarger := Brownian.augFiltration 𝒲.poissonLarger.rightCont P
  poisson_le := fun _ => Probability.aug_mono (rightCont_mono_of_le 𝒲.poisson_le _)
  isPoisson := Poisson.isPoissonFiltration_augFiltration 𝒲.isPoisson.rightCont
  measurable_increment := fun i s p q =>
    (𝒲.measurable_increment i s p q).mono
      ((𝒲.poissonLarger.le_rightCont s).trans
        (Brownian.le_augFiltration 𝒲.poissonLarger.rightCont P s)) le_rfl
  brownianLarger := Brownian.augFiltration 𝒲.brownianLarger.rightCont P
  brownian_le := fun _ => Probability.aug_mono (rightCont_mono_of_le 𝒲.brownian_le _)
  isBrownian := fun i => Brownian.isBrownianFiltration_augFiltration (𝒲.isBrownian i).rightCont
  stronglyMeasurable_compensated := fun s _ hB =>
    (𝒲.stronglyMeasurable_compensated s hB).mono
      ((𝒲.brownianLarger.le_rightCont s).trans
        (Brownian.le_augFiltration 𝒲.brownianLarger.rightCont P s))

/-! ### The second moment of a solution at time `1` -/

section Solution

variable {D : LevyDriver P 1 jumpIntensity}
  {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin 1, Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : Poisson.IsPoissonFiltration D.N ℱ} {X : ℝ → Ω → (Fin 1 → ℝ)}

/-- The single coordinate of a path solving the jump-diffusion equation of `coeffs` from `0`,
with its drift, diffusion and jump coefficients along the path, is an Itô–Lévy process. -/
theorem isItoLevyProcess_of_solvesOn (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) X T) :
    IsItoLevyProcess D.W D.N ℱ hℱW hℱN (fun t ω => X t ω 0) (fun _ => (0 : ℝ))
      (fun s ω => coeffs.μ s (X s ω) 0) (fun s ω => coeffs.σ s (X s ω) 0)
      (fun ω s e => coeffs.γ s (X s ω) e 0) := by
  refine ⟨hXm.eval, fun j => (hXsol 0).h_σ_meas 0 j, fun j => (hXsol 0).h_σ_progMeas 0 j,
    fun j => (hXsol 0).h_σ_sq 0 j, (hXsol 0).h_γ_meas 0, (hXsol 0).h_γ_progMeas 0,
    (hXsol 0).h_γ_sq 0, ?_⟩
  intro t ht
  filter_upwards [eqn_sum_form D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) (hXsol t)
    ⟨ht, le_rfl⟩] with ω hω
  exact hω 0

/-- The second moment of the single coordinate at time `1` of a path solving the
jump-diffusion equation of `coeffs` from `0` is `2`. -/
theorem integral_sq_solvesOn_one (𝒲 : D.CrossWitness ℱ)
    (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) X T) :
    ∫ ω, X 1 ω 0 * X 1 ω 0 ∂P = 2 := by
  have hbeq : (Function.uncurry fun (ω : Ω) (s : ℝ) => coeffs.μ s (X s ω) 0)
      = fun _ : Ω × ℝ => (0 : ℝ) := rfl
  have hbm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => coeffs.μ s (X s ω) 0) := by
    rw [hbeq]; exact measurable_const
  have hbp : Probability.ProgressivelyMeasurable ℱ
      fun (ω : Ω) (s : ℝ) => coeffs.μ s (X s ω) 0 :=
    Brownian.Ito.progressivelyMeasurable_const ℱ 0
  have hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X s ω) 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T _
    simp [coeffs]
  have e2 : ∀ s : ℝ, ∫ ω, X s ω 0 * coeffs.μ s (X s ω) 0 ∂P = 0 := by
    intro s
    simp [coeffs_mu_apply]
  have e3 : ∀ j : Fin 1, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1,
      (‖coeffs.σ s (X s ω) 0 j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) = 1 := by
    intro j
    have hpt : ∀ (ω : Ω) (s : ℝ), (‖coeffs.σ s (X s ω) 0 j‖₊ : ℝ≥0∞) ^ 2 = 1 := by
      intro ω s
      rw [coeffs_sigma_apply]
      simp
    simp only [hpt, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have e4 : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) 1, ∫⁻ e,
      (‖coeffs.γ s (X s ω) e 0‖₊ : ℝ≥0∞) ^ 2 ∂jumpIntensity ∂volume ∂P) = 1 := by
    have hpt : ∀ (ω : Ω) (s : ℝ), (∫⁻ e, (‖coeffs.γ s (X s ω) e 0‖₊ : ℝ≥0∞) ^ 2
        ∂jumpIntensity) = 1 := by
      intro ω s
      simp only [jumpIntensity, coeffs_gamma_apply]
      rw [lintegral_dirac]
      simp
    simp only [hpt, lintegral_const, measure_univ, mul_one, Measure.restrict_apply_univ,
      Real.volume_Icc, sub_zero, ENNReal.ofReal_one]
  have key := Ito.SecondMoment.integral_mul_self_eq_of_isItoLevyProcess
    (isItoLevyProcess_of_solvesOn hXm hXsol) 𝒲 stronglyMeasurable_const (memLp_const (0 : ℝ))
    hbm hbp hbq (T := 1) one_pos
  rw [key]
  simp only [e3, e4, Fin.sum_univ_one, ENNReal.toReal_one]
  simp_rw [e2]
  norm_num

/-- The single coordinate at time `1` of a path solving the jump-diffusion equation of `coeffs`
from `0` is not almost surely `0`. -/
theorem solvesOn_value_one_not_ae_zero (𝒲 : D.CrossWitness ℱ)
    (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N ℱ hℱW hℱN coeffs (0 : Fin 1 → ℝ) X T) :
    ¬ ((fun ω => X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) := by
  intro h
  have hzero : (fun ω => X 1 ω 0 * X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [h] with ω hω
    simp [hω]
  have h0 : ∫ ω, X 1 ω 0 * X 1 ω 0 ∂P = 0 := by
    rw [integral_congr_ae hzero, integral_zero]
  rw [integral_sq_solvesOn_one 𝒲 hXm hXsol] at h0
  norm_num at h0

end Solution

/-! ### The filtration of the construction -/

variable (D : LevyDriver P 1 jumpIntensity)

/-- Every coordinate of the driver's Brownian motion is a Brownian motion for the augmented
right-continuation of the joint filtration. -/
theorem isBrownianFiltration_augRightCont (j : Fin 1) :
    Brownian.IsBrownianFiltration (D.W.W j)
      (Brownian.augFiltration D.filtration.rightCont P) :=
  Brownian.isBrownianFiltration_augFiltration (D.isBrownianFiltration j).rightCont

/-- The driver's Poisson random measure is a Poisson random measure for the augmented
right-continuation of the joint filtration. -/
theorem isPoissonFiltration_augRightCont :
    Poisson.IsPoissonFiltration D.N (Brownian.augFiltration D.filtration.rightCont P) :=
  Poisson.isPoissonFiltration_augFiltration D.isPoissonFiltration.rightCont

/-- The single coordinate at time `1` of a path solving the jump-diffusion equation of `coeffs`
from `0` relative to the augmented right-continuation of the driver's joint filtration is not
almost surely `0`. -/
theorem solvesOn_augRightCont_value_one_not_ae_zero {X : ℝ → Ω → (Fin 1 → ℝ)}
    (hXm : Measurable (Function.uncurry X))
    (hXsol : ∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
      (0 : Fin 1 → ℝ) X T) :
    ¬ ((fun ω => X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) :=
  solvesOn_value_one_not_ae_zero (crossWitnessAugRightCont D.crossWitness) hXm hXsol

/-! ### The witness -/

/-- **The realised path of the Itô–Lévy example is not almost surely `0` at time `1`.** On some
probability space there are a Lévy driver with intensity `δ₁` and a path `X` solving, at every
horizon and relative to the augmented right-continuation of the driver's joint filtration, the
jump-diffusion equation of `coeffs` from `0`, whose single coordinate at time `1` is not
almost surely `0`. -/
theorem exists_solvesOn_value_one_not_ae_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 jumpIntensity) (X : ℝ → Ω → (Fin 1 → ℝ)),
      Measurable (Function.uncurry X)
        ∧ (∀ T : ℝ, SolvesOn D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
            (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs
            (0 : Fin 1 → ℝ) X T)
        ∧ ¬ ((fun ω => X 1 ω 0) =ᵐ[P] fun _ => (0 : ℝ)) := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ := LevyDriver.exists 1 ℝ jumpIntensity
  haveI hFrc : (Brownian.augFiltration D.filtration.rightCont P).IsRightContinuous :=
    Brownian.isRightContinuous_augFiltration D.filtration P
  have hℱ0 : ∀ t : ℝ, t ≤ 0 → Brownian.augFiltration D.filtration.rightCont P 0
      ≤ Brownian.augFiltration D.filtration.rightCont P t := fun t ht =>
    le_of_eq (Brownian.augFiltration_of_nonpos D.filtration.rightCont P ht).symm
  have hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 →
      MeasurableSet[Brownian.augFiltration D.filtration.rightCont P 0] s := fun s hs h0 =>
    Brownian.measurableSet_augFiltration_of_null D.filtration.rightCont P hs h0
  obtain ⟨Xp, hXm, _hXa, _hX0, _hXcad, _hXS, hXsol⟩ :=
    exists_globalSolution D.W D.N (Brownian.augFiltration D.filtration.rightCont P)
      (isBrownianFiltration_augRightCont D) (isPoissonFiltration_augRightCont D) coeffs hℱ0
      hnull coeffs_isRegular coeffs_isLipschitz (0 : Fin 1 → ℝ)
  exact ⟨Ω, inferInstance, P, inferInstance, D, Xp, hXm, hXsol,
    solvesOn_augRightCont_value_one_not_ae_zero D hXm hXsol⟩

end LevyStochCalc.Examples.Nonvacuity
