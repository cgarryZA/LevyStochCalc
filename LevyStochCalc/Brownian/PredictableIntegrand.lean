/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.PredictableModification
import LevyStochCalc.Brownian.ItoRange

/-!
# Admissible integrands have predictable versions

An admissible integrand agrees almost everywhere with a predictable process; cutting that process
to the horizon keeps it predictable and makes it admissible, and the two integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability

/-- The predictable σ-algebra is coarser than the product σ-algebra. -/
theorem predictableSigma_le (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    predictableSigma ℱ ≤ (inferInstance : MeasurableSpace (ℝ × Ω)) := by
  refine MeasurableSpace.generateFrom_le ?_
  rintro - (⟨A, hA, rfl⟩ | ⟨r, A, hA, rfl⟩)
  · exact measurableSet_Iic.prod (ℱ.le 0 _ hA)
  · exact measurableSet_Ioi.prod (ℱ.le r _ hA)

/-- A predictable process is jointly measurable. -/
theorem measurable_uncurry_of_predictable {K : Ω → ℝ → ℝ} (hK : Predictable ℱ K) :
    Measurable (Function.uncurry K) :=
  ((hK.mono (predictableSigma_le ℱ)).measurable).comp measurable_swap

/-- Cutting a predictable process to a horizon keeps it predictable. -/
theorem predictable_indicator_Ioc {K : Ω → ℝ → ℝ} (hK : Predictable ℱ K) {T : ℝ} (hT : 0 ≤ T) :
    Predictable ℱ fun ω s => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K ω s) s := by
  have hset : MeasurableSet[predictableSigma ℱ] (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set Ω)) :=
    measurableSet_predictableSigma_Ioc_prod hT MeasurableSet.univ
  have hrw : (fun p : ℝ × Ω => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K p.2 p.1) p.1)
      = (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set Ω)).indicator fun p : ℝ × Ω => K p.2 p.1 := by
    funext p
    by_cases hp : p.1 ∈ Set.Ioc (0 : ℝ) T
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem (Set.mk_mem_prod hp (Set.mem_univ _))]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem fun h => hp h.1]
  show StronglyMeasurable[predictableSigma ℱ]
    fun p : ℝ × Ω => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K p.2 p.1) p.1
  rw [hrw]
  exact hK.indicator hset

/-- The times outside a left-open horizon are null for the energy measure. -/
theorem ae_mem_Ioc_energyMeasure {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂(energyMeasure P T), p.2 ∈ Set.Ioc (0 : ℝ) T := by
  have hmeas : MeasurableSet ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T)ᶜ) :=
    MeasurableSet.univ.prod measurableSet_Ioc.compl
  have hnull : (energyMeasure P T) ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T)ᶜ) = 0 := by
    have hset : ((Set.Ioc (0 : ℝ) T)ᶜ ∩ Set.Icc (0 : ℝ) T) = {(0 : ℝ)} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_Ioc, Set.mem_Icc,
        Set.mem_singleton_iff, not_and, not_le]
      constructor
      · rintro ⟨h1, h2, h3⟩
        rcases eq_or_lt_of_le h2 with h | h
        · exact h.symm
        · exact absurd h3 (not_le.mpr (h1 h))
      · rintro rfl
        exact ⟨fun h => absurd h (lt_irrefl 0), le_rfl, hT⟩
    rw [energyMeasure, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc.compl, hset]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) hnull
  exact Set.mk_mem_prod (Set.mem_univ _) hp

/-- **An admissible integrand has an admissible predictable version with the same integral.** -/
theorem exists_predictable_horizonIntegrand (W : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration W ℱ) (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) {T : ℝ} (hT : 0 < T)
    (G : HorizonIntegrand P ℱ T) :
    ∃ G' : HorizonIntegrand P ℱ T, Predictable ℱ G'.toFun ∧
      G'.integral W hℱ =ᵐ[P] G.integral W hℱ := by
  obtain ⟨K, hKpred, hKae⟩ :=
    exists_predictable_ae_eq ℱ G.measurable_uncurry G.progressive hT G.energy_ne_top
  set K' : Ω → ℝ → ℝ := fun ω s => (Set.Ioc (0 : ℝ) T).indicator (fun _ => K ω s) s with hK'def
  have hK'pred : Predictable ℱ K' := predictable_indicator_Ioc hKpred hT.le
  have hK'meas : Measurable (Function.uncurry K') := measurable_uncurry_of_predictable hK'pred
  have hK'prog : ProgressivelyMeasurable ℱ K' := hK'pred.progressivelyMeasurable hℱ0
  have hK'ae : (fun p : Ω × ℝ => G.toFun p.1 p.2)
      =ᵐ[energyMeasure P T] fun p : Ω × ℝ => K' p.1 p.2 := by
    refine hKae.trans ?_
    filter_upwards [ae_mem_Ioc_energyMeasure (P := P) hT.le] with p hp
    exact (Set.indicator_of_mem hp fun _ => K p.1 p.2).symm
  have hfin : energy P T K' ≠ ⊤ := by
    rw [energy_eq_eLpNorm_sq hK'meas T, ← eLpNorm_congr_ae hK'ae,
      ← energy_eq_eLpNorm_sq G.measurable_uncurry T]
    exact G.energy_ne_top
  have hvanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → K' ω s = 0 := fun ω s hs =>
    Set.indicator_of_notMem (fun h => hs ⟨h.1.le, h.2⟩) _
  refine ⟨⟨K', hK'meas, hK'prog, hvanish, hfin⟩, hK'pred, ?_⟩
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K' ω s - G.toFun ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
    have hdiff : (fun p : Ω × ℝ => K' p.1 p.2 - G.toFun p.1 p.2)
        =ᵐ[energyMeasure P T] fun _ => (0 : ℝ) := by
      filter_upwards [hK'ae] with p hp
      rw [hp, sub_self]
    have hE : energy P T (fun ω s => K' ω s - G.toFun ω s)
        = eLpNorm (fun p : Ω × ℝ => K' p.1 p.2 - G.toFun p.1 p.2) 2 (energyMeasure P T) ^ 2 :=
      energy_eq_eLpNorm_sq (hK'meas.sub G.measurable_uncurry) T
    have : energy P T (fun ω s => K' ω s - G.toFun ω s) = 0 := by
      rw [hE, eLpNorm_congr_ae hdiff]
      simp
    exact this
  have hiso := isometry_diff_stochasticIntegralBrownian W ℱ hℱ K' G.toFun hK'meas
    G.measurable_uncurry hK'prog G.progressive
    (HorizonIntegrand.sq_int_global ⟨K', hK'meas, hK'prog, hvanish, hfin⟩) G.sq_int_global hT
  rw [hzero] at hiso
  have hL1 : MemLp ((⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      HorizonIntegrand P ℱ T).integral W hℱ) 2 P := HorizonIntegrand.memLp W hℱ _
  have hL2 : MemLp (G.integral W hℱ) 2 P := HorizonIntegrand.memLp W hℱ G
  have hae : AEMeasurable (fun ω => (‖(⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      HorizonIntegrand P ℱ T).integral W hℱ ω - G.integral W hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hL1.sub hL2).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖(⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      HorizonIntegrand P ℱ T).integral W hℱ ω - G.integral W hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : (⟨K', hK'meas, hK'prog, hvanish, hfin⟩ :
      HorizonIntegrand P ℱ T).integral W hℱ ω - G.integral W hℱ ω = 0 := by simpa using h2
  linarith

end LevyStochCalc.Brownian.Ito
