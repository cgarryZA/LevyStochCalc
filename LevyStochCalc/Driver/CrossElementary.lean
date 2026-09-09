/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CrossFiltration
import LevyStochCalc.Driver.JointFiltration
import LevyStochCalc.Poisson.CompensatedPullOut
import LevyStochCalc.Poisson.CompensatedDensity
import LevyStochCalc.Brownian.ItoFourthMoment

/-!
# One cross term between the two drivers

A Brownian increment weighted at its left endpoint, against a compensated mass weighted at its
left endpoint, has zero mean: whichever of the two cells starts later, its increment is centred
given an enlargement of the filtration carrying the whole path of the other driver, and the
remaining factor is measurable there.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

/-- Two enlargements of a filtration `ℱ` making a cross term conditionable: one for which `N` is
a Poisson random measure and every Brownian increment is measurable, and one for which every
coordinate is a Brownian motion and every compensated mass is measurable. -/
structure CrossWitness (D : LevyDriver.{u, v, w} P d ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) where
  /-- The enlargement carrying the whole Brownian path. -/
  poissonLarger : Filtration ℝ ‹MeasurableSpace Ω›
  /-- It contains `ℱ`. -/
  poisson_le : ∀ s, ℱ s ≤ poissonLarger s
  /-- `N` is a Poisson random measure for it. -/
  isPoisson : Poisson.IsPoissonFiltration D.N poissonLarger
  /-- Brownian increments are measurable there at every time. -/
  measurable_increment : ∀ (i : Fin d) (s p q : ℝ),
    Measurable[poissonLarger s] fun ω => (D.W.W i).W q ω - (D.W.W i).W p ω
  /-- The enlargement carrying the whole Poisson path. -/
  brownianLarger : Filtration ℝ ‹MeasurableSpace Ω›
  /-- It contains `ℱ`. -/
  brownian_le : ∀ s, ℱ s ≤ brownianLarger s
  /-- Every coordinate is a Brownian motion for it. -/
  isBrownian : ∀ i, Brownian.IsBrownianFiltration (D.W.W i) brownianLarger
  /-- Compensated masses are measurable there at every time. -/
  stronglyMeasurable_compensated : ∀ (s : ℝ) {B : Set (ℝ × E)}, MeasurableSet B →
    StronglyMeasurable[brownianLarger s] fun ω => D.N.compensated B ω

/-- The joint natural filtration is witnessed by the two enlargements. -/
noncomputable def crossWitness (D : LevyDriver.{u, v, w} P d ν) : CrossWitness D D.filtration where
  poissonLarger := D.crossPoissonFiltration
  poisson_le := D.filtration_le_crossPoisson
  isPoisson := D.isPoissonFiltration_crossPoisson
  measurable_increment := D.measurable_increment_crossPoisson
  brownianLarger := D.crossBrownianFiltration
  brownian_le := D.filtration_le_crossBrownian
  isBrownian := D.isBrownianFiltration_crossBrownian
  stronglyMeasurable_compensated := fun s _ hB => D.stronglyMeasurable_compensated_crossBrownian s hB

/-- Augmenting by the null sets preserves a witness. -/
noncomputable def CrossWitness.aug {D : LevyDriver.{u, v, w} P d ν}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (𝒲 : CrossWitness D ℱ) :
    CrossWitness D (Brownian.augFiltration ℱ P) where
  poissonLarger := Brownian.augFiltration 𝒲.poissonLarger P
  poisson_le := fun _ => Probability.aug_mono (𝒲.poisson_le _)
  isPoisson := Poisson.isPoissonFiltration_augFiltration 𝒲.isPoisson
  measurable_increment := fun i s p q =>
    (𝒲.measurable_increment i s p q).mono
      (Brownian.le_augFiltration 𝒲.poissonLarger P s) le_rfl
  brownianLarger := Brownian.augFiltration 𝒲.brownianLarger P
  brownian_le := fun _ => Probability.aug_mono (𝒲.brownian_le _)
  isBrownian := fun i => Brownian.isBrownianFiltration_augFiltration (𝒲.isBrownian i)
  stronglyMeasurable_compensated := fun s _ hB =>
    (𝒲.stronglyMeasurable_compensated s hB).mono
      (Brownian.le_augFiltration 𝒲.brownianLarger P s)

section CrossTerm

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The cross term vanishes, when the compensated cell starts last.** -/
theorem integral_cross_term_eq_zero_of_le (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ) {Mξ : ℝ}
    (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η) {Mη : ℝ}
    (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) ∂P = 0 := by
  have hBmeas : MeasurableSet (Set.Ioc r v ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : Poisson.referenceIntensity ν (Set.Ioc r v ×ˢ A) ≠ ⊤ :=
    Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAν
  have hNm : Measurable fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω := by
    show Measurable fun ω => (D.N.N ω (Set.Ioc r v ×ˢ A)).toReal
      - (Poisson.referenceIntensity ν (Set.Ioc r v ×ˢ A)).toReal
    exact ((D.N.measurable_eval hBmeas).ennreal_toReal).sub_const _
  have hN2 : MemLp (fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω) 2 P :=
    Poisson.Compensated.compensated_memLp D.N hBmeas hfin
  have hNint : Integrable (fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω) P :=
    hN2.integrable one_le_two
  have hΔm : Measurable fun ω => (D.W.W i).W q ω - (D.W.W i).W p ω :=
    ((D.W.W i).measurable_eval q).sub ((D.W.W i).measurable_eval p)
  have hY2 : MemLp (fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))) 2 P :=
    Poisson.Compensated.memLp_bdd_mul hηm hηb
      (Brownian.Ito.memLp_mul_increment (D.W.W i) hp hpq 2 (by simp) hξm hξb)
  have hYsm : StronglyMeasurable[𝒲.poissonLarger r]
      fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω)) :=
    (hη.mono (𝒲.poisson_le r)).mul
      ((hξ.mono ((ℱ.mono hpr).trans (𝒲.poisson_le r))).mul
        (𝒲.measurable_increment i r p q).stronglyMeasurable)
  have hprod : Integrable (fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * D.N.compensated (Set.Ioc r v ×ˢ A) ω) P :=
    Poisson.Compensated.integrable_mul_of_memLp_two hY2 hN2
  have hrw : (fun ω => (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω))
      = fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * D.N.compensated (Set.Ioc r v ×ˢ A) ω := by
    funext ω; ring
  rw [hrw, ← integral_condExp (𝒲.poissonLarger.le r)]
  have hpull : P[fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * D.N.compensated (Set.Ioc r v ×ˢ A) ω | 𝒲.poissonLarger r]
      =ᵐ[P] (fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω)))
        * P[fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω | 𝒲.poissonLarger r] :=
    condExp_mul_of_aestronglyMeasurable_left (m := 𝒲.poissonLarger r)
      (f := fun ω => η ω * (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω)))
      (g := fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω) hYsm.aestronglyMeasurable hprod hNint
  have hcond := Poisson.Compensated.compensated_condExp_future_eq_zero D.N 𝒲.poissonLarger
    𝒲.isPoisson hr hrv hA hAν
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hpull, hcond] with ω e1 e2
  rw [e1, Pi.mul_apply, e2, mul_zero]
  rfl

/-- **The cross term vanishes, when the Brownian cell starts last.** -/
theorem integral_cross_term_eq_zero_of_ge (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hrp : r ≤ p) {A : Set E} (hA : MeasurableSet A)
    {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ)
    (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η) :
    ∫ ω, (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) ∂P = 0 := by
  have hBmeas : MeasurableSet (Set.Ioc r v ×ˢ A) := measurableSet_Ioc.prod hA
  have hNm : Measurable fun ω => D.N.compensated (Set.Ioc r v ×ˢ A) ω := by
    show Measurable fun ω => (D.N.N ω (Set.Ioc r v ×ˢ A)).toReal
      - (Poisson.referenceIntensity ν (Set.Ioc r v ×ˢ A)).toReal
    exact ((D.N.measurable_eval hBmeas).ennreal_toReal).sub_const _
  have hYsm : StronglyMeasurable[𝒲.brownianLarger p]
      fun ω => ξ ω * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) :=
    (hξ.mono (𝒲.brownian_le p)).mul
      ((hη.mono ((ℱ.mono hrp).trans (𝒲.brownian_le p))).mul
        (𝒲.stronglyMeasurable_compensated p hBmeas))
  have hYm : Measurable fun ω => ξ ω * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) :=
    hξm.mul (hηm.mul hNm)
  have hrw : (fun ω => (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
        * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω))
      = fun ω => (ξ ω * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω))
        * ((D.W.W i).W q ω - (D.W.W i).W p ω) ^ 1 := by
    funext ω; rw [pow_one]; ring
  rw [hrw, Brownian.Ito.integral_mul_increment_pow (D.W.W i) 𝒲.brownianLarger (𝒲.isBrownian i)
      hp hpq hYsm hYm 1,
    Brownian.Ito.integral_increment_pow_odd (D.W.W i) hp hpq odd_one, mul_zero]

/-- **The cross term vanishes.** -/
theorem integral_cross_term_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrv : r < v) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ)
    {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω) ∂P = 0 := by
  rcases le_or_gt p r with hpr | hrp
  · exact integral_cross_term_eq_zero_of_le 𝒲 hp hpq hr hrv hpr hA hAν hξ hξm hξb hη hηm hηb
  · exact integral_cross_term_eq_zero_of_ge 𝒲 hp hpq hrp.le hA hξ hξm hη hηm

end CrossTerm

end LevyDriver

end LevyStochCalc.Driver
