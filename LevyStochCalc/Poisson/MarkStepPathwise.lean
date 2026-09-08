/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.MarkStep
import LevyStochCalc.Poisson.Compensator

/-!
# The mark-step approximants are pathwise and predictable

The approximants the compensated integral is built from are finite combinations of indicators of
time–mark rectangles with coefficients known at the left endpoint of their piece. Their integral
against any measure finite on those rectangles is the matching finite combination, so over the
whole horizon the approximant's compensated integral is the difference of its integrals against
the random measure and against the reference intensity. Adaptedness of the coefficients makes the
approximant predictable, which is what the compensator identity asks for.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P] {g : TimeGrid}

namespace MarkStep

/-- The mark-step integrand as a finite combination of rectangle indicators. -/
theorem eval_eq_sum_indicator (G : MarkStep Ω E ν g) (q : ℝ × E) (ω : Ω) :
    G.eval q.1 q.2 ω = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
      (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator (fun _ : ℝ × E => G.ξ i k ω) q := by
  classical
  rw [MarkStep.eval]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hs : q.1 ∈ Set.Ioc (g.p i) (g.p (i + 1))
  · by_cases he : q.2 ∈ G.B k
    · rw [Set.indicator_of_mem (Set.mem_prod.mpr ⟨hs, he⟩), Set.indicator_of_mem hs,
        Set.indicator_of_mem he]
      ring
    · rw [Set.indicator_of_notMem (fun h => he (Set.mem_prod.mp h).2),
        Set.indicator_of_notMem he]
      ring
  · rw [Set.indicator_of_notMem (fun h => hs (Set.mem_prod.mp h).1),
      Set.indicator_of_notMem hs]
    ring

/-- The integral of a mark-step integrand against a measure finite on its rectangles. -/
theorem integral_eval_eq_sum (G : MarkStep Ω E ν g) (μ : Measure (ℝ × E))
    (hfin : ∀ i k, μ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤) (ω : Ω) :
    ∫ q, G.eval q.1 q.2 ω ∂μ
      = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
          (μ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k)).toReal * G.ξ i k ω := by
  classical
  have hrectm : ∀ i (k : Fin G.K),
      MeasurableSet (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) :=
    fun i k => measurableSet_Ioc.prod (G.B_measurable k)
  have hrw : (fun q : ℝ × E => G.eval q.1 q.2 ω)
      = fun q : ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k ω) q := funext fun q => G.eval_eq_sum_indicator q ω
  rw [hrw, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_indicator_const _ (hrectm i k), smul_eq_mul, measureReal_def]
    · intro k _
      rw [integrable_indicator_iff (hrectm i k)]
      exact integrableOn_const (hfin i k)
  · intro i _
    refine integrable_finsetSum _ fun k _ => ?_
    rw [integrable_indicator_iff (hrectm i k)]
    exact integrableOn_const (hfin i k)

/-- **The mark-step compensated integral over the horizon is pathwise.** -/
theorem full_eq_sub_integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (ω : Ω)
    (hfin : ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤) :
    G.full N ω = (∫ q, G.eval q.1 q.2 ω ∂(N.N ω))
      - ∫ q, G.eval q.1 q.2 ω ∂(referenceIntensity ν) := by
  have hIfin : ∀ i (k : Fin G.K),
      referenceIntensity ν (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤ :=
    fun i k => referenceIntensity_Ioc_prod_ne_top' (G.B_finite k) _ _
  rw [G.integral_eval_eq_sum (N.N ω) hfin ω,
    G.integral_eval_eq_sum (referenceIntensity ν) hIfin ω, ← Finset.sum_sub_distrib,
    MarkStep.full]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PoissonRandomMeasure.compensated]
  ring

/-- A time interval cut at `t` is the interval between the cut endpoints. -/
theorem Ioc_inter_Iic (a b t : ℝ) :
    Set.Ioc a b ∩ Set.Iic t = Set.Ioc (min a t) (min b t) := by
  ext x
  have hnot : x ≤ t → ¬ t < x := fun h => not_lt.mpr h
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Iic, min_lt_iff, le_min_iff]
  tauto

/-- The rectangle of a mark-step integrand cut at `t`. -/
theorem fullRect_inter_Iic (G : MarkStep Ω E ν g) (i : ℕ) (k : Fin G.K) (t : ℝ) :
    (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ∩ (Set.Iic t ×ˢ (Set.univ : Set E))
      = Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k := by
  rw [Set.prod_inter_prod, Ioc_inter_Iic, Set.inter_univ]

/-- The mark-step integrand cut at `t`, as a finite combination of cut-rectangle indicators. -/
theorem evalTo_eq_sum_indicator (G : MarkStep Ω E ν g) (t : ℝ) (q : ℝ × E) (ω : Ω) :
    (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω
      = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k ω) q := by
  classical
  rw [G.eval_eq_sum_indicator q ω, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← G.fullRect_inter_Iic i k t]
  by_cases hq : q.1 ∈ Set.Iic t
  · rw [Set.indicator_of_mem hq, one_mul]
    by_cases hr : q ∈ Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k
    · rw [Set.indicator_of_mem hr,
        Set.indicator_of_mem (Set.mem_inter hr (Set.mem_prod.mpr ⟨hq, Set.mem_univ q.2⟩))]
    · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem fun h => hr h.1]
  · rw [Set.indicator_of_notMem hq, zero_mul,
      Set.indicator_of_notMem fun h => hq (Set.mem_prod.mp h.2).1]

/-- The integral of a cut mark-step integrand against a measure finite on the cut rectangles. -/
theorem integral_evalTo_eq_sum (G : MarkStep Ω E ν g) (t : ℝ) (μ : Measure (ℝ × E))
    (hfin : ∀ i (k : Fin G.K),
      μ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤) (ω : Ω) :
    ∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω ∂μ
      = ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
          (μ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k)).toReal * G.ξ i k ω := by
  classical
  have hrectm : ∀ i (k : Fin G.K),
      MeasurableSet (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) :=
    fun i k => measurableSet_Ioc.prod (G.B_measurable k)
  have hrw : (fun q : ℝ × E =>
        (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω)
      = fun q : ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k ω) q :=
    funext fun q => G.evalTo_eq_sum_indicator t q ω
  rw [hrw, integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [integral_indicator_const _ (hrectm i k), smul_eq_mul, measureReal_def]
    · intro k _
      rw [integrable_indicator_iff (hrectm i k)]
      exact integrableOn_const (hfin i k)
  · intro i _
    refine integrable_finsetSum _ fun k _ => ?_
    rw [integrable_indicator_iff (hrectm i k)]
    exact integrableOn_const (hfin i k)

/-- **The mark-step compensated integral up to any time is pathwise.** -/
theorem integral_eq_sub_integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ω : Ω) (hfin : ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤) :
    G.integral N t ω
      = (∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω ∂(N.N ω))
        - ∫ q, (Set.Iic t).indicator (fun _ => (1 : ℝ)) q.1 * G.eval q.1 q.2 ω
            ∂(referenceIntensity ν) := by
  have hIfin : ∀ i (k : Fin G.K),
      referenceIntensity ν
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤ :=
    fun i k => referenceIntensity_Ioc_prod_ne_top' (G.B_finite k) _ _
  rw [G.integral_evalTo_eq_sum t (N.N ω) hfin ω,
    G.integral_evalTo_eq_sum t (referenceIntensity ν) hIfin ω, ← Finset.sum_sub_distrib,
    MarkStep.integral]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PoissonRandomMeasure.compensated]
  ring

/-- The counts on the rectangles of a mark-step integrand are almost surely finite. -/
theorem ae_count_rect_ne_top (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) :
    ∀ᵐ ω ∂P, ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ≠ ⊤ := by
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro k
  filter_upwards [N.integer_valued (measurableSet_Ioc.prod (G.B_measurable k))
    (referenceIntensity_Ioc_prod_ne_top' (G.B_finite k) _ _)] with ω hω
  obtain ⟨n, hn⟩ := hω
  rw [hn]
  exact ENNReal.natCast_ne_top n

/-- The counts on the clamped rectangles are almost surely finite. -/
theorem ae_count_clamped_rect_ne_top (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
    (t : ℝ) :
    ∀ᵐ ω ∂P, ∀ i (k : Fin G.K),
      N.N ω (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ≠ ⊤ := by
  filter_upwards [ae_count_rect_ne_top N G] with ω hω i k
  refine ne_top_of_le_ne_top (hω i k) (measure_mono ?_)
  rw [← G.fullRect_inter_Iic i k t]
  exact Set.inter_subset_left

/-- The pathwise form of the mark-step compensated integral, almost surely. -/
theorem ae_full_eq_sub_integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) :
    ∀ᵐ ω ∂P, G.full N ω = (∫ q, G.eval q.1 q.2 ω ∂(N.N ω))
      - ∫ q, G.eval q.1 q.2 ω ∂(referenceIntensity ν) := by
  filter_upwards [ae_count_rect_ne_top N G] with ω hω
  exact full_eq_sub_integral N G ω hω

/-- **An adapted mark-step integrand is predictable.** -/
theorem markedPredictable_eval (G : MarkStep Ω E ν g)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hG : G.Adapted ℱ) :
    Probability.MarkedPredictable ℱ ν fun ω s e => G.eval s e ω := by
  classical
  have hterm : ∀ i, i < g.N₀ → ∀ k : Fin G.K,
      Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
        (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2 := by
    intro i hi k U hU
    have hξU : MeasurableSet[ℱ (g.p i)] (G.ξ i k ⁻¹' U) := (hG i hi k).measurable hU
    have hbig : MeasurableSet[Probability.markedPredictableSigma ℱ ν]
        ((G.ξ i k ⁻¹' U) ×ˢ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k)) :=
      MeasurableSpace.measurableSet_generateFrom
        ⟨g.p i, g.p (i + 1), _, _, g.p_nonneg hi.le, hξU, G.B_measurable k, G.B_finite k, rfl⟩
    have huniv : MeasurableSet[Probability.markedPredictableSigma ℱ ν]
        ((Set.univ : Set Ω) ×ˢ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k)) :=
      MeasurableSpace.measurableSet_generateFrom
        ⟨g.p i, g.p (i + 1), _, _, g.p_nonneg hi.le, MeasurableSet.univ, G.B_measurable k,
          G.B_finite k, rfl⟩
    by_cases h0 : (0 : ℝ) ∈ U
    · have hset : (fun p : Ω × ℝ × E => (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2) ⁻¹' U
          = ((G.ξ i k ⁻¹' U) ×ˢ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k))
            ∪ ((Set.univ : Set Ω) ×ˢ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k))ᶜ := by
        ext p
        by_cases hp : p.2 ∈ Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k
        · have hL := Set.indicator_of_mem hp fun _ : ℝ × E => G.ξ i k p.1
          constructor
          · intro h
            rw [Set.mem_preimage, hL] at h
            exact Or.inl (Set.mem_prod.mpr ⟨h, hp⟩)
          · intro h
            rw [Set.mem_preimage, hL]
            rcases h with h | h
            · exact (Set.mem_prod.mp h).1
            · exact absurd (Set.mem_prod.mpr ⟨Set.mem_univ p.1, hp⟩) h
        · have hL := Set.indicator_of_notMem hp fun _ : ℝ × E => G.ξ i k p.1
          constructor
          · intro _
            exact Or.inr fun h => hp (Set.mem_prod.mp h).2
          · intro _
            rw [Set.mem_preimage, hL]
            exact h0
      rw [hset]
      exact hbig.union huniv.compl
    · have hset : (fun p : Ω × ℝ × E => (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2) ⁻¹' U
          = (G.ξ i k ⁻¹' U) ×ˢ (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) := by
        ext p
        by_cases hp : p.2 ∈ Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k
        · have hL := Set.indicator_of_mem hp fun _ : ℝ × E => G.ξ i k p.1
          constructor
          · intro h
            rw [Set.mem_preimage, hL] at h
            exact Set.mem_prod.mpr ⟨h, hp⟩
          · intro h
            rw [Set.mem_preimage, hL]
            exact (Set.mem_prod.mp h).1
        · have hL := Set.indicator_of_notMem hp fun _ : ℝ × E => G.ξ i k p.1
          constructor
          · intro h
            rw [Set.mem_preimage, hL] at h
            exact absurd h h0
          · intro h
            exact absurd (Set.mem_prod.mp h).2 hp
      rw [hset]
      exact hbig
  have hrw : (fun p : Ω × ℝ × E => G.eval p.2.1 p.2.2 p.1)
      = fun p : Ω × ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2 :=
    funext fun p => G.eval_eq_sum_indicator p.2 p.1
  change Measurable[Probability.markedPredictableSigma ℱ ν] _
  rw [hrw]
  exact Finset.measurable_sum _ fun i hi =>
    Finset.measurable_sum _ fun k _ => hterm i (Finset.mem_range.mp hi) k

/-- **An adapted mark-step integrand cut at a time is predictable.** -/
theorem markedPredictable_evalTo (G : MarkStep Ω E ν g)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hG : G.Adapted ℱ) (t : ℝ) :
    Probability.MarkedPredictable ℱ ν
      fun ω s e => (Set.Iic t).indicator (fun _ => (1 : ℝ)) s * G.eval s e ω := by
  classical
  have hterm : ∀ i, i < g.N₀ → ∀ k : Fin G.K,
      Measurable[Probability.markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2 := by
    intro i hi k
    rcases le_or_gt (min (g.p (i + 1)) t) (min (g.p i) t) with hle | hlt
    · have hempty : Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) = (∅ : Set ℝ) :=
        Set.Ioc_eq_empty (not_lt.mpr hle)
      have hzero : (fun p : Ω × ℝ × E =>
          (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
            (fun _ : ℝ × E => G.ξ i k p.1) p.2) = fun _ => (0 : ℝ) := by
        funext p
        rw [hempty, Set.empty_prod, Set.indicator_empty]
      rw [hzero]
      exact measurable_const
    · have hmin : min (g.p i) t = g.p i := by
        refine min_eq_left ?_
        by_contra hcon
        have hti : t < g.p i := not_le.mp hcon
        rw [min_eq_right hti.le] at hlt
        exact absurd (lt_of_lt_of_le hlt (min_le_right (g.p (i + 1)) t)) (lt_irrefl t)
      intro U hU
      have hξU : MeasurableSet[ℱ (min (g.p i) t)] (G.ξ i k ⁻¹' U) := by
        rw [hmin]
        exact (hG i hi k).measurable hU
      have hnn : 0 ≤ min (g.p i) t := by rw [hmin]; exact g.p_nonneg hi.le
      have hbig : MeasurableSet[Probability.markedPredictableSigma ℱ ν]
          ((G.ξ i k ⁻¹' U) ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k)) :=
        MeasurableSpace.measurableSet_generateFrom
          ⟨min (g.p i) t, min (g.p (i + 1)) t, _, _, hnn, hξU, G.B_measurable k,
            G.B_finite k, rfl⟩
      have huniv : MeasurableSet[Probability.markedPredictableSigma ℱ ν]
          ((Set.univ : Set Ω) ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k)) :=
        MeasurableSpace.measurableSet_generateFrom
          ⟨min (g.p i) t, min (g.p (i + 1)) t, _, _, hnn, MeasurableSet.univ,
            G.B_measurable k, G.B_finite k, rfl⟩
      by_cases h0 : (0 : ℝ) ∈ U
      · have hset : (fun p : Ω × ℝ × E =>
            (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
              (fun _ : ℝ × E => G.ξ i k p.1) p.2) ⁻¹' U
            = ((G.ξ i k ⁻¹' U)
                ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k))
              ∪ ((Set.univ : Set Ω)
                ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k))ᶜ := by
          ext p
          by_cases hp : p.2 ∈ Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k
          · have hL := Set.indicator_of_mem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro h
              rw [Set.mem_preimage, hL] at h
              exact Or.inl (Set.mem_prod.mpr ⟨h, hp⟩)
            · intro h
              rw [Set.mem_preimage, hL]
              rcases h with h | h
              · exact (Set.mem_prod.mp h).1
              · exact absurd (Set.mem_prod.mpr ⟨Set.mem_univ p.1, hp⟩) h
          · have hL := Set.indicator_of_notMem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro _
              exact Or.inr fun h => hp (Set.mem_prod.mp h).2
            · intro _
              rw [Set.mem_preimage, hL]
              exact h0
        rw [hset]
        exact hbig.union huniv.compl
      · have hset : (fun p : Ω × ℝ × E =>
            (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
              (fun _ : ℝ × E => G.ξ i k p.1) p.2) ⁻¹' U
            = (G.ξ i k ⁻¹' U)
                ×ˢ (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) := by
          ext p
          by_cases hp : p.2 ∈ Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k
          · have hL := Set.indicator_of_mem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro h
              rw [Set.mem_preimage, hL] at h
              exact Set.mem_prod.mpr ⟨h, hp⟩
            · intro h
              rw [Set.mem_preimage, hL]
              exact (Set.mem_prod.mp h).1
          · have hL := Set.indicator_of_notMem hp fun _ : ℝ × E => G.ξ i k p.1
            constructor
            · intro h
              rw [Set.mem_preimage, hL] at h
              exact absurd h h0
            · intro h
              exact absurd (Set.mem_prod.mp h).2 hp
        rw [hset]
        exact hbig
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun _ => (1 : ℝ)) p.2.1 * G.eval p.2.1 p.2.2 p.1)
      = fun p : Ω × ℝ × E => ∑ i ∈ Finset.range g.N₀, ∑ k : Fin G.K,
        (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k).indicator
          (fun _ : ℝ × E => G.ξ i k p.1) p.2 :=
    funext fun p => G.evalTo_eq_sum_indicator t p.2 p.1
  change Measurable[Probability.markedPredictableSigma ℱ ν] _
  rw [hrw]
  exact Finset.measurable_sum _ fun i hi =>
    Finset.measurable_sum _ fun k _ => hterm i (Finset.mem_range.mp hi) k

/-- A mark-step integrand vanishes at nonpositive times. -/
theorem eval_eq_zero_of_nonpos (G : MarkStep Ω E ν g) {s : ℝ} (hs : s ≤ 0) (e : E) (ω : Ω) :
    G.eval s e ω = 0 := by
  classical
  refine Finset.sum_eq_zero fun i hi => ?_
  have hnot : s ∉ Set.Ioc (g.p i) (g.p (i + 1)) := by
    intro hmem
    have h0 : 0 ≤ g.p i := g.p_nonneg (le_of_lt (Finset.mem_range.mp hi))
    exact absurd (lt_of_le_of_lt h0 hmem.1) (not_lt.mpr hs)
  rw [Set.indicator_of_notMem hnot, zero_mul]

section RestrictMarks

variable {A : Set E}

/-- A mark-step integrand with its mark sets cut down to `A`. -/
noncomputable def restrictMarks (G : MarkStep Ω E ν g) (hA : MeasurableSet A) :
    MarkStep Ω E ν g where
  K := G.K
  B := fun k => G.B k ∩ A
  B_measurable := fun k => (G.B_measurable k).inter hA
  B_finite := fun k => ne_top_of_le_ne_top (G.B_finite k) (measure_mono Set.inter_subset_left)
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable

theorem restrictMarks_B_subset (G : MarkStep Ω E ν g) (hA : MeasurableSet A) (k : Fin G.K) :
    (G.restrictMarks hA).B k ⊆ A := Set.inter_subset_right

theorem restrictMarks_adapted (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hG : G.Adapted ℱ) :
    (G.restrictMarks hA).Adapted ℱ := hG

theorem eval_restrictMarks_of_mem (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    (s : ℝ) {e : E} (he : e ∈ A) (ω : Ω) :
    (G.restrictMarks hA).eval s e ω = G.eval s e ω := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  change (G.B k ∩ A).indicator (fun _ => (1 : ℝ)) e = (G.B k).indicator (fun _ => (1 : ℝ)) e
  by_cases hb : e ∈ G.B k
  · rw [Set.indicator_of_mem (show e ∈ G.B k ∩ A from ⟨hb, he⟩),
      Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem (fun h => hb h.1), Set.indicator_of_notMem hb]

theorem eval_restrictMarks_of_notMem (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    (s : ℝ) {e : E} (he : e ∉ A) (ω : Ω) :
    (G.restrictMarks hA).eval s e ω = 0 := by
  classical
  refine Finset.sum_eq_zero fun i _ => ?_
  have hzero : ∑ k : Fin (G.restrictMarks hA).K, (G.restrictMarks hA).ξ i k ω
      * ((G.restrictMarks hA).B k).indicator (fun _ => (1 : ℝ)) e = 0 := by
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [Set.indicator_of_notMem (fun h => he h.2), mul_zero]
  rw [hzero, mul_zero]

/-- Cutting the marks down to a set the integrand is carried by cannot increase the error. -/
theorem abs_sub_eval_restrictMarks_le (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    {φ : Ω → ℝ → E → ℝ} (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) (ω : Ω) (s : ℝ) (e : E) :
    |φ ω s e - (G.restrictMarks hA).eval s e ω| ≤ |φ ω s e - G.eval s e ω| := by
  by_cases he : e ∈ A
  · rw [G.eval_restrictMarks_of_mem hA s he ω]
  · rw [G.eval_restrictMarks_of_notMem hA s he ω, hsupp ω s e he, sub_zero, abs_zero]
    exact abs_nonneg _

/-- **The mark-restricted approximant is at least as close in energy.** -/
theorem lintegral_sq_sub_eval_restrictMarks_le (G : MarkStep Ω E ν g) (hA : MeasurableSet A)
    {φ : Ω → ℝ → E → ℝ} (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) (T : ℝ)
    (P : Measure Ω) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - (G.restrictMarks hA).eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => ?_
  refine pow_le_pow_left' ?_ 2
  refine ENNReal.coe_le_coe.mpr ?_
  have habs := G.abs_sub_eval_restrictMarks_le hA hsupp ω s e
  rw [← Real.norm_eq_abs, ← Real.norm_eq_abs] at habs
  exact_mod_cast habs

/-- **Restricting the marks moves the compensated integral by at most the energy error.** -/
theorem lintegral_integral_sub_restrictMarks_le (N : PoissonRandomMeasure P ν)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hℱ : IsPoissonFiltration N ℱ)
    (G : MarkStep Ω E ν g) (hG : G.Adapted ℱ) (hA : MeasurableSet A)
    {φ : Ω → ℝ → E → ℝ} (hsupp : ∀ ω s e, e ∉ A → φ ω s e = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω - (G.restrictMarks hA).integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖φ ω s e - G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  rw [MarkStep.lintegral_integral_sub_sq_at N hℱ G (G.restrictMarks hA) hG
    (G.restrictMarks_adapted hA hG) ht]
  refine lintegral_mono fun ω => lintegral_mono fun e => lintegral_mono fun s => ?_
  refine pow_le_pow_left' (ENNReal.coe_le_coe.mpr ?_) 2
  by_cases he : e ∈ A
  · rw [G.eval_restrictMarks_of_mem hA s he ω, sub_self]
    simp
  · rw [G.eval_restrictMarks_of_notMem hA s he ω, sub_zero, hsupp ω s e he, zero_sub,
      nnnorm_neg]

end RestrictMarks

end MarkStep

end LevyStochCalc.Poisson.Compensated
