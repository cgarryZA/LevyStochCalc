/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.MarkedPredictable
import LevyStochCalc.Poisson.CompensatedApprox
import LevyStochCalc.Poisson.CompensatedIntegrandComplete
import LevyStochCalc.Poisson.CompensatedRange

/-!
# Predictable representatives of marked progressive integrands

A mark-step integrand adapted at the left endpoints of its cells is predictable on the time–mark
space, and the marked predictable processes are closed under pointwise upper limits. The
mark-step integrands are dense in the marked progressive integrands of finite energy, so such an
integrand agrees with a predictable one almost everywhere in time, mark and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {ℱ : Filtration ℝ mΩ}

open LevyStochCalc.Poisson.Compensated

/-- **An adapted mark-step integrand is predictable.** -/
theorem markedPredictable_markStepEval {g : TimeGrid} (G : MarkStep Ω E ν g)
    (hG : G.Adapted ℱ) : MarkedPredictable ℱ ν fun ω s e => G.eval s e ω := by
  have hrw : (fun p : Ω × ℝ × E => G.eval p.2.1 p.2.2 p.1)
      = fun p : Ω × ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) (p.2.1, p.2.2) := by
    funext p
    rw [MarkStep.eval]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hs : p.2.1 ∈ Set.Ioc (g.p i) (g.p (i + 1))
    · rw [Set.indicator_of_mem hs, one_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases he : p.2.2 ∈ G.B k
      · rw [Set.indicator_of_mem he, Set.indicator_of_mem (Set.mk_mem_prod hs he), mul_one]
      · rw [Set.indicator_of_notMem he,
          Set.indicator_of_notMem (fun hp => he hp.2), mul_zero]
    · rw [Set.indicator_of_notMem hs, zero_mul]
      refine (Finset.sum_eq_zero fun k _ => ?_).symm
      exact Set.indicator_of_notMem (fun hp => hs hp.1) _
  show Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E => G.eval p.2.1 p.2.2 p.1
  rw [hrw]
  refine Finset.measurable_sum _ fun i hi => Finset.measurable_sum _ fun k _ => ?_
  exact markedPredictable_rectIndicator (g.p_nonneg (Finset.mem_range.mp hi).le)
    (G.B_measurable k) (G.B_finite k) (hG i (Finset.mem_range.mp hi) k).measurable

omit [SigmaFinite ν] in
/-- **Marked predictable processes are closed under pointwise upper limits.** -/
theorem MarkedPredictable.limsup {ψ : ℕ → Ω → ℝ → E → ℝ}
    (h : ∀ n, MarkedPredictable ℱ ν (ψ n)) :
    MarkedPredictable ℱ ν fun ω s e => Filter.limsup (fun n => ψ n ω s e) atTop :=
  Measurable.limsup fun n => h n

/-- The pointwise upper limit along a subsequence of mark-step integrands. -/
noncomputable def limsupMarkStepEval {g : ℕ → TimeGrid} (G : ∀ n, MarkStep Ω E ν (g n))
    (ns : ℕ → ℕ) : Ω → ℝ → E → ℝ :=
  fun ω s e => limsup (fun i => (G (ns i)).eval s e ω) atTop

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- **A marked progressive integrand of finite energy agrees with a predictable one almost
everywhere in time, mark and sample point.** -/
theorem exists_markedPredictable_ae_eq (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : MarkedProgressivelyMeasurable ℱ φ) {T : ℝ} (hT : 0 < T)
    (hfin : markedEnergy P ν T φ ≠ ⊤) :
    ∃ ψ : Ω → ℝ → E → ℝ, MarkedPredictable ℱ ν ψ ∧
      (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
        =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 := by
  classical
  have hex : ∀ n : ℕ, ∃ ℓ : ℕ, ∃ G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ), G.Adapted ℱ ∧
      markedEnergy P ν T (fun ω s e => φ ω s e - G.eval s e ω) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    obtain ⟨ℓ, -, G, hGa, hGe⟩ := exists_markStep_close N ℱ hℱ φ hm hp hT
      (lt_top_iff_ne_top.mpr hfin) 0 (ε := ((n : ℝ≥0∞) + 1)⁻¹) (ENNReal.inv_pos.mpr (by simp))
    exact ⟨ℓ, G, hGa, hGe⟩
  choose ℓ G hGadapt hGerr using hex
  have hGm : ∀ n, Measurable fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1 := fun n =>
    (G n).eval_measurable
  have hφmem : MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) :=
    memLp_of_markedEnergy_ne_top hm hfin
  have hDmem : ∀ n, MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - (G n).eval p.2.1 p.2.2 p.1) 2
      (markedEnergyMeasure P ν T) := fun n =>
    memLp_of_markedEnergy_ne_top (φ := fun ω s e => φ ω s e - (G n).eval s e ω)
      (hm.sub (hGm n)) (ne_top_of_lt (hGerr n))
  have hGmem : ∀ n, MemLp (fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1) 2
      (markedEnergyMeasure P ν T) := by
    intro n
    refine (hφmem.sub (hDmem n)).ae_eq (Filter.Eventually.of_forall fun p => ?_)
    simp
  have hsq : ∀ n, eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) ^ 2
        < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hcomm : eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T)
        = eLpNorm (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 - (G n).eval p.2.1 p.2.2 p.1) 2
          (markedEnergyMeasure P ν T) := by
      rw [← eLpNorm_neg]
      refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp
    rw [hcomm, ← markedEnergy_eq_eLpNorm_sq (φ := fun ω s e => φ ω s e - (G n).eval s e ω)
      (hm.sub (hGm n)) T]
    exact hGerr n
  have htend : Tendsto (fun n => eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
      - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T)) atTop (𝓝 0) := by
    refine ENNReal.tendsto_atTop_zero.mpr fun ε hε => ?_
    obtain ⟨M, hM⟩ := ENNReal.exists_inv_nat_lt (a := ε ^ 2) (by positivity)
    refine ⟨M, fun n hn => ?_⟩
    by_contra hcon
    have hle : ε ≤ eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) :=
      le_of_not_ge hcon
    have h1 : ε ^ 2 ≤ eLpNorm ((fun p : Ω × ℝ × E => (G n).eval p.2.1 p.2.2 p.1)
        - fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2 (markedEnergyMeasure P ν T) ^ 2 :=
      pow_le_pow_left' hle 2
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ ((M : ℝ≥0∞))⁻¹ := by
      refine ENNReal.inv_le_inv.mpr ?_
      have hMn : (M : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
      exact hMn.trans le_self_add
    exact absurd (lt_of_le_of_lt h1 ((hsq n).trans_le (h2.trans hM.le))) (lt_irrefl _)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm
    (μ := markedEnergyMeasure P ν T) (p := 2) (by norm_num)
    (fun n => (hGmem n).aestronglyMeasurable) hφmem.aestronglyMeasurable
    htend).exists_seq_tendsto_ae
  refine ⟨limsupMarkStepEval G ns, MarkedPredictable.limsup fun i =>
    markedPredictable_markStepEval (G (ns i)) (hGadapt (ns i)), ?_⟩
  filter_upwards [hae] with p hp'
  exact hp'.limsup_eq.symm

/-- **An admissible marked horizon integrand has a predictable version.** -/
theorem exists_markedPredictable_ae_eq_markedHorizonIntegrand
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T)
    (G : MarkedHorizonIntegrand P ν ℱ T) :
    ∃ ψ : Ω → ℝ → E → ℝ, MarkedPredictable ℱ ν ψ ∧
      (fun p : Ω × ℝ × E => G.toFun p.1 p.2.1 p.2.2)
        =ᵐ[markedEnergyMeasure P ν T] fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 :=
  exists_markedPredictable_ae_eq N hℱ G.measurable_uncurry G.progressive hT G.energy_ne_top

end LevyStochCalc.Probability
