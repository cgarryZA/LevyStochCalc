/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.MarkedPredictableModification
import LevyStochCalc.Poisson.Compensated

/-!
# Admissible marked integrands have predictable versions

An admissible marked integrand agrees almost everywhere with a predictable process; cutting that
process to the horizon keeps it predictable — the horizon strip is a countable union of windows
of finite mark measure — and makes it admissible, and the two compensated integrals agree almost
surely because the energy of their difference vanishes.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Probability

/-- The horizon strip is predictable: it is the countable union of the windows of a σ-finite
exhaustion of the marks. -/
theorem measurableSet_markedPredictable_strip (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (ν : Measure E) [SigmaFinite ν] (T : ℝ) :
    MeasurableSet[markedPredictableSigma ℱ ν]
      ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))) := by
  have hrw : (Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
      = ⋃ n : ℕ, ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν n)) := by
    ext p
    simp only [Set.mem_prod, Set.mem_univ, true_and, Set.mem_iUnion, and_true]
    constructor
    · intro hs
      have hmem : p.2.2 ∈ ⋃ n, spanningSets ν n := by
        rw [iUnion_spanningSets ν]; trivial
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
      exact ⟨n, hs, hn⟩
    · rintro ⟨n, hs, -⟩
      exact hs
  rw [hrw]
  exact MeasurableSet.iUnion fun n => measurableSet_univ_prod_window_self ℱ T
    (measurableSet_spanningSets ν n) (measure_spanningSets_lt_top ν n).ne

/-- Cutting a marked predictable process to a horizon keeps it predictable. -/
theorem markedPredictable_indicator_Ioc {ψ : Ω → ℝ → E → ℝ} (hψ : MarkedPredictable ℱ ν ψ)
    (T : ℝ) :
    MarkedPredictable ℱ ν fun ω s e => (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ ω s e) s := by
  have hset := measurableSet_markedPredictable_strip ℱ ν T
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ p.1 p.2.1 p.2.2) p.2.1)
      = ((Set.univ : Set Ω) ×ˢ (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))).indicator
        fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Ioc (0 : ℝ) T
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem
        (Set.mk_mem_prod (Set.mem_univ _) (Set.mk_mem_prod hp (Set.mem_univ _)))]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem fun h => hp h.2.1]
  show Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ p.1 p.2.1 p.2.2) p.2.1
  rw [hrw]
  exact hψ.indicator hset

/-- The times outside a left-open horizon are null for the marked energy measure. -/
theorem ae_mem_Ioc_markedEnergyMeasure {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ p ∂(markedEnergyMeasure P ν T), p.2.1 ∈ Set.Ioc (0 : ℝ) T := by
  have hnull : (markedEnergyMeasure P ν T)
      ((Set.univ : Set Ω) ×ˢ ((Set.Ioc (0 : ℝ) T)ᶜ ×ˢ (Set.univ : Set E))) = 0 := by
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
    rw [markedEnergyMeasure, Measure.prod_prod, Measure.prod_prod,
      Measure.restrict_apply measurableSet_Ioc.compl, hset]
    simp
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) hnull
  exact Set.mk_mem_prod (Set.mem_univ _) (Set.mk_mem_prod hp (Set.mem_univ _))

/-- **An admissible marked integrand has an admissible predictable version with the same
integral.** -/
theorem exists_markedPredictable_markedHorizonIntegrand
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∃ G' : MarkedHorizonIntegrand P ν ℱ T, MarkedPredictable ℱ ν G'.toFun ∧
      G'.integral N hℱ =ᵐ[P] G.integral N hℱ := by
  obtain ⟨ψ, hψpred, hψae⟩ := exists_markedPredictable_ae_eq N hℱ G.measurable_uncurry
    G.progressive hT G.energy_ne_top
  set ψ' : Ω → ℝ → E → ℝ :=
    fun ω s e => (Set.Ioc (0 : ℝ) T).indicator (fun _ => ψ ω s e) s with hψ'def
  have hψ'pred : MarkedPredictable ℱ ν ψ' := markedPredictable_indicator_Ioc hψpred T
  have hψ'meas : Measurable fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 :=
    hψ'pred.mono (markedPredictableSigma_le ℱ ν) le_rfl
  have hψ'prog : MarkedProgressivelyMeasurable ℱ ψ' :=
    hψ'pred.markedProgressivelyMeasurable
  have hψ'ae : (fun p : Ω × ℝ × E => G.toFun p.1 p.2.1 p.2.2)
      =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 := by
    refine hψae.trans ?_
    filter_upwards [ae_mem_Ioc_markedEnergyMeasure (P := P) (ν := ν) hT.le] with p hp
    exact (Set.indicator_of_mem hp fun _ => ψ p.1 p.2.1 p.2.2).symm
  have hfin : markedEnergy P ν T ψ' ≠ ⊤ := by
    rw [markedEnergy_eq_eLpNorm_sq hψ'meas T, ← eLpNorm_congr_ae hψ'ae,
      ← markedEnergy_eq_eLpNorm_sq G.measurable_uncurry T]
    exact G.energy_ne_top
  have hvanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → ψ' ω s e = 0 := fun ω s e hs =>
    Set.indicator_of_notMem (fun h => hs ⟨h.1.le, h.2⟩) _
  refine ⟨⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩, hψ'pred, ?_⟩
  have hzero : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ' ω s e - G.toFun ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P = 0 := by
    have hdiff : (fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 - G.toFun p.1 p.2.1 p.2.2)
        =ᵐ[markedEnergyMeasure P ν T] fun _ => (0 : ℝ) := by
      filter_upwards [hψ'ae] with p hp
      rw [hp, sub_self]
    have hE : markedEnergy P ν T (fun ω s e => ψ' ω s e - G.toFun ω s e)
        = eLpNorm (fun p : Ω × ℝ × E => ψ' p.1 p.2.1 p.2.2 - G.toFun p.1 p.2.1 p.2.2) 2
          (markedEnergyMeasure P ν T) ^ 2 :=
      markedEnergy_eq_eLpNorm_sq (hψ'meas.sub G.measurable_uncurry) T
    have hz : markedEnergy P ν T (fun ω s e => ψ' ω s e - G.toFun ω s e) = 0 := by
      rw [hE, eLpNorm_congr_ae hdiff]
      simp
    exact hz
  have hiso := itoIsometry_diff_compensated N ℱ hℱ ψ' G.toFun hψ'meas G.measurable_uncurry
    hψ'prog G.progressive
    (MarkedHorizonIntegrand.sq_int_global ⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩)
    G.sq_int_global T hT
  rw [hzero] at hiso
  have hL1 : MemLp ((⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      MarkedHorizonIntegrand P ν ℱ T).integral N hℱ) 2 P :=
    MarkedHorizonIntegrand.memLp N hℱ _
  have hL2 : MemLp (G.integral N hℱ) 2 P := MarkedHorizonIntegrand.memLp N hℱ G
  have hae : AEMeasurable (fun ω => (‖(⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      MarkedHorizonIntegrand P ν ℱ T).integral N hℱ ω - G.integral N hℱ ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hL1.sub hL2).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖(⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      MarkedHorizonIntegrand P ν ℱ T).integral N hℱ ω - G.integral N hℱ ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : (⟨ψ', hψ'meas, hψ'prog, hvanish, hfin⟩ :
      MarkedHorizonIntegrand P ν ℱ T).integral N hℱ ω - G.integral N hℱ ω = 0 := by
    simpa using h2
  linarith

end LevyStochCalc.Poisson.Compensated
