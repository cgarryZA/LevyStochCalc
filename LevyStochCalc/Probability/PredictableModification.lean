/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.Predictable
import LevyStochCalc.Brownian.ItoL2Completion
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.Brownian.ItoRange

/-!
# Predictable representatives of progressive integrands

The elementary integrands of the `L²` theory — finite sums of a coefficient measurable at the
left endpoint of a cell, carried on that cell — are predictable, and the predictable processes
are closed under pointwise upper limits. Since the elementary integrands are dense in the
progressive integrands of finite energy, a progressive integrand agrees with a predictable one
almost everywhere in time and sample point.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}

section Cells

/-- The strip below a nonnegative time is predictable. -/
theorem measurableSet_predictableSigma_Iic_univ {r : ℝ} (hr : 0 ≤ r) :
    MeasurableSet[predictableSigma ℱ] (Set.Iic r ×ˢ (Set.univ : Set Ω)) := by
  have h : Set.Iic r ×ˢ (Set.univ : Set Ω)
      = (Set.Iic (0 : ℝ) ×ˢ (Set.univ : Set Ω)) ∪
        ((Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set Ω)) \ (Set.Ioi r ×ˢ (Set.univ : Set Ω))) := by
    ext ⟨s, ω⟩
    simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_union, Set.mem_sdiff, Set.mem_Iic,
      Set.mem_Ioi]
    constructor
    · intro hs
      rcases le_or_gt s 0 with h0 | h0
      · exact Or.inl h0
      · exact Or.inr ⟨h0, not_lt.mpr hs⟩
    · rintro (h0 | ⟨-, h1⟩)
      · exact h0.trans hr
      · exact not_lt.mp h1
  rw [h]
  exact (measurableSet_predictableSigma_Iic_prod MeasurableSet.univ).union
    ((measurableSet_predictableSigma_Ioi_prod MeasurableSet.univ).diff
      (measurableSet_predictableSigma_Ioi_prod MeasurableSet.univ))

/-- A left-open cell with a coefficient set measurable at its left endpoint is predictable. -/
theorem measurableSet_predictableSigma_Ioc_prod {r q : ℝ} (hrq : r ≤ q) {A : Set Ω}
    (hA : MeasurableSet[ℱ r] A) :
    MeasurableSet[predictableSigma ℱ] (Set.Ioc r q ×ˢ A) := by
  have h : Set.Ioc r q ×ˢ A = (Set.Ioi r ×ˢ A) \ (Set.Ioi q ×ˢ A) := by
    ext ⟨s, ω⟩
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_Ioi, Set.mem_sdiff, not_and]
    constructor
    · rintro ⟨⟨h1, h2⟩, hω⟩
      exact ⟨⟨h1, hω⟩, fun h3 => absurd h2 (not_le.mpr h3)⟩
    · rintro ⟨⟨h1, hω⟩, h2⟩
      refine ⟨⟨h1, ?_⟩, hω⟩
      by_contra hc
      exact h2 (not_le.mp hc) hω
  rw [h]
  exact (measurableSet_predictableSigma_Ioi_prod hA).diff
    (measurableSet_predictableSigma_Ioi_prod (ℱ.mono hrq _ hA))

/-- The complement of a cell above the origin is predictable. -/
theorem measurableSet_predictableSigma_compl_Ioc {r q : ℝ} (hr : 0 ≤ r) :
    MeasurableSet[predictableSigma ℱ] ((Set.Ioc r q)ᶜ ×ˢ (Set.univ : Set Ω)) := by
  have h : ((Set.Ioc r q)ᶜ) ×ˢ (Set.univ : Set Ω)
      = (Set.Iic r ×ˢ (Set.univ : Set Ω)) ∪ (Set.Ioi q ×ˢ (Set.univ : Set Ω)) := by
    ext ⟨s, ω⟩
    simp only [Set.mem_prod, Set.mem_univ, and_true, Set.mem_union, Set.mem_compl_iff,
      Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi, not_and, not_le]
    constructor
    · intro hs
      rcases le_or_gt s r with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (hs h0)
    · rintro (h0 | h0)
      · exact fun h1 => absurd h0 (not_le.mpr h1)
      · exact fun _ => h0
  rw [h]
  exact (measurableSet_predictableSigma_Iic_univ hr).union
    (measurableSet_predictableSigma_Ioi_prod MeasurableSet.univ)

/-- A coefficient measurable at the left endpoint of a cell, carried on that cell, is
predictable. -/
theorem measurable_predictableSigma_cell {r q : ℝ} (hr : 0 ≤ r) (hrq : r ≤ q) {ξ : Ω → ℝ}
    (hξ : Measurable[ℱ r] ξ) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => if r < p.1 ∧ p.1 ≤ q then ξ p.2 else 0 := by
  intro U hU
  by_cases h0 : (0 : ℝ) ∈ U
  · have hpre : (fun p : ℝ × Ω => if r < p.1 ∧ p.1 ≤ q then ξ p.2 else 0) ⁻¹' U
        = (Set.Ioc r q ×ˢ (ξ ⁻¹' U)) ∪ ((Set.Ioc r q)ᶜ ×ˢ (Set.univ : Set Ω)) := by
      ext ⟨s, ω⟩
      by_cases hs : r < s ∧ s ≤ q <;>
        simp [hs, h0, Set.mem_Ioc, Set.mem_preimage, Set.mem_prod]
    rw [hpre]
    exact (measurableSet_predictableSigma_Ioc_prod hrq (hξ hU)).union
      (measurableSet_predictableSigma_compl_Ioc hr)
  · have hpre : (fun p : ℝ × Ω => if r < p.1 ∧ p.1 ≤ q then ξ p.2 else 0) ⁻¹' U
        = Set.Ioc r q ×ˢ (ξ ⁻¹' U) := by
      ext ⟨s, ω⟩
      by_cases hs : r < s ∧ s ≤ q <;>
        simp [hs, h0, Set.mem_Ioc, Set.mem_preimage, Set.mem_prod]
    rw [hpre]
    exact measurableSet_predictableSigma_Ioc_prod hrq (hξ hU)

/-- **An adapted elementary integrand is predictable.** -/
theorem predictable_simpleEval {T : ℝ} (G : Brownian.Ito.SimplePredictable Ω T)
    (hG : ∀ i : Fin G.N, StronglyMeasurable[ℱ (G.partition i.castSucc)] (G.ξ i)) :
    Predictable ℱ fun ω s => G.eval s ω := by
  have hnn : ∀ i : Fin G.N, 0 ≤ G.partition i.castSucc := fun i => by
    have h := G.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [G.partition_zero] at h
  have hle : ∀ i : Fin G.N, G.partition i.castSucc ≤ G.partition i.succ := fun i =>
    (G.partition_strictMono Fin.castSucc_lt_succ).le
  refine stronglyMeasurable_iff_measurable.mpr ?_
  have hrw : (fun p : ℝ × Ω => G.eval p.1 p.2)
      = fun p : ℝ × Ω => ∑ i : Fin G.N,
        (if G.partition i.castSucc < p.1 ∧ p.1 ≤ G.partition i.succ then G.ξ i p.2 else 0) := rfl
  rw [hrw]
  exact Finset.measurable_sum _ fun i _ =>
    measurable_predictableSigma_cell (hnn i) (hle i) (hG i).measurable

/-- **Predictable processes are closed under pointwise upper limits.** -/
theorem Predictable.limsup {H : ℕ → Ω → ℝ → ℝ} (h : ∀ k, Predictable ℱ (H k)) :
    Predictable ℱ fun ω s => Filter.limsup (fun k => H k ω s) Filter.atTop := by
  refine stronglyMeasurable_iff_measurable.mpr (Measurable.limsup fun k => ?_)
  exact (h k).measurable

end Cells

section Modification

open Brownian.Ito

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The pointwise upper limit along a subsequence of elementary integrands. -/
noncomputable def limsupSimpleEval {T : ℝ} (G : ℕ → SimplePredictable Ω T) (ns : ℕ → ℕ) :
    Ω → ℝ → ℝ := fun ω s => limsup (fun i => (G (ns i)).eval s ω) atTop

/-- **A progressive integrand of finite energy agrees with a predictable one almost everywhere
in time and sample point.** -/
theorem exists_predictable_ae_eq (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (hp : ProgressivelyMeasurable ℱ H)
    {T : ℝ} (hT : 0 < T) (hfin : energy P T H ≠ ⊤) :
    ∃ K : Ω → ℝ → ℝ, Predictable ℱ K ∧
      (fun p : Ω × ℝ => H p.1 p.2) =ᵐ[energyMeasure P T] fun p : Ω × ℝ => K p.1 p.2 := by
  classical
  have hex : ∀ n : ℕ, ∃ G : SimplePredictable Ω T,
      (∀ i : Fin G.N, StronglyMeasurable[ℱ (G.partition i.castSucc)] (G.ξ i)) ∧
      energy P T (fun ω s => H ω s - G.eval s ω) < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hpos : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
      ENNReal.inv_pos.mpr (by simp)
    exact exists_adaptedSimple_within ℱ H hm hp hT (lt_top_iff_ne_top.mpr hfin) hpos
  choose G hGadapt hGerr using hex
  have hHmem : MemLp (fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) :=
    memLp_of_energy_ne_top hm hfin
  have hDmem : ∀ n, MemLp (fun p : Ω × ℝ => H p.1 p.2 - (G n).eval p.2 p.1) 2
      (energyMeasure P T) := fun n =>
    memLp_of_energy_ne_top (H := fun ω s => H ω s - (G n).eval s ω)
      (hm.sub (G n).eval_jointly_measurable) (ne_top_of_lt (hGerr n))
  have hGmem : ∀ n, MemLp (fun p : Ω × ℝ => (G n).eval p.2 p.1) 2 (energyMeasure P T) := by
    intro n
    refine (hHmem.sub (hDmem n)).ae_eq (Filter.Eventually.of_forall fun p => ?_)
    simp
  have hsq : ∀ n, eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
      - fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) ^ 2 < ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have hcomm : eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
        - fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T)
        = eLpNorm (fun p : Ω × ℝ => H p.1 p.2 - (G n).eval p.2 p.1) 2 (energyMeasure P T) := by
      rw [← eLpNorm_neg]
      refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      simp
    rw [hcomm, ← energy_eq_eLpNorm_sq (H := fun ω s => H ω s - (G n).eval s ω)
      (hm.sub (G n).eval_jointly_measurable) T]
    exact hGerr n
  have htend : Tendsto (fun n => eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
      - fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T)) atTop (𝓝 0) := by
    refine ENNReal.tendsto_atTop_zero.mpr fun ε hε => ?_
    obtain ⟨N, hN⟩ := ENNReal.exists_inv_nat_lt (a := ε ^ 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    by_contra hcon
    have hle : ε ≤ eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
        - fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) := le_of_not_ge hcon
    have h1 : ε ^ 2 ≤ eLpNorm ((fun p : Ω × ℝ => (G n).eval p.2 p.1)
        - fun p : Ω × ℝ => H p.1 p.2) 2 (energyMeasure P T) ^ 2 := pow_le_pow_left' hle 2
    have h2 : ((n : ℝ≥0∞) + 1)⁻¹ ≤ ((N : ℝ≥0∞))⁻¹ := by
      refine ENNReal.inv_le_inv.mpr ?_
      have hNn : (N : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by exact_mod_cast hn
      exact hNn.trans le_self_add
    exact absurd (lt_of_le_of_lt h1 ((hsq n).trans_le (h2.trans hN.le))) (lt_irrefl _)
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (μ := energyMeasure P T) (p := 2)
    (by norm_num) (fun n => (hGmem n).aestronglyMeasurable) hHmem.aestronglyMeasurable
    htend).exists_seq_tendsto_ae
  refine ⟨limsupSimpleEval G ns, Predictable.limsup fun i =>
    predictable_simpleEval (G (ns i)) (hGadapt (ns i)), ?_⟩
  filter_upwards [hae] with p hp'
  exact hp'.limsup_eq.symm

/-- **An admissible horizon integrand has a predictable version.** -/
theorem exists_predictable_ae_eq_horizonIntegrand (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ}
    (hT : 0 < T) (G : HorizonIntegrand P ℱ T) :
    ∃ K : Ω → ℝ → ℝ, Predictable ℱ K ∧
      (fun p : Ω × ℝ => G.toFun p.1 p.2) =ᵐ[energyMeasure P T] fun p : Ω × ℝ => K p.1 p.2 :=
  exists_predictable_ae_eq ℱ G.measurable_uncurry G.progressive hT G.energy_ne_top

end Modification

end LevyStochCalc.Probability
