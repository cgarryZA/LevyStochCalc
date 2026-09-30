/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedProfileLinear
import LevyStochCalc.Poisson.CompensatedProfileRepr
import LevyStochCalc.Poisson.CompensatorL1

/-!
# The compensated integral of an integrable mark profile is pathwise

Let `N` be a Poisson random measure on `[0, ∞) × E` with `σ`-finite intensity `ν`, possibly
`ν(E) = ∞`, and let `f ∈ L¹(ν) ∩ L²(ν)` be a deterministic mark profile. Over a step `(a, b]`,
`0 ≤ a ≤ b`, almost surely `f` is integrable on `(a, b] × E` against `N(ω)` and the compensated
integral of `f` is the raw integral minus its compensator:

  `∫_E f(e) ΔÑ(de) = ∫_{(a, b] × E} f(e) N(ω)(ds, de) − (b − a) ∫_E f dν`.

The mean measure of `N` is its reference intensity (Campbell's formula), so the raw integral of
`|f|` over the step has mean `(b − a) ‖f‖_{L¹(ν)}`. At a simple profile the identity is the
definition of the compensated step integral. Simple functions converging to `f` both in `L¹(ν)`
and in `L²(ν)` then carry the identity to `f`: the compensated integrals converge in `L²(P)` and
the raw integrals minus their compensators converge in `L¹(P)`.

## Main statements

* `LevyStochCalc.Poisson.PoissonRandomMeasure.bind_N` — the mean measure of a Poisson random
  measure is its reference intensity.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.lintegral_lintegral_N` — Campbell's formula.
* `LevyStochCalc.Poisson.PoissonRandomMeasure.ae_integrableOn_cell` — an integrable mark profile
  is almost surely integrable on a step times the mark space.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_integral_sub` — the compensated integral of a
  mark profile in `L¹(ν) ∩ L²(ν)` is the raw integral minus its compensator.
* `LevyStochCalc.Poisson.compensatedProfileRepr_ae_eq_integral_sub` — the same for the
  representative of the compensated integral for a sub-σ-algebra.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The mean measure -/

/-- The reference intensity on a step times the mark space is Lebesgue measure on the step times
the intensity. -/
theorem referenceIntensity_restrict_Ioc_prod_univ {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    (referenceIntensity ν).restrict (Set.Ioc a b ×ˢ Set.univ)
      = (volume.restrict (Set.Ioc a b)).prod ν := by
  have hsub : Set.Ioc a b ∩ Set.Ici (0 : ℝ) = Set.Ioc a b := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => ha.trans h.1.le
  rw [referenceIntensity, ← Measure.prod_restrict, Measure.restrict_restrict measurableSet_Ioc,
    hsub, Measure.restrict_univ]

namespace PoissonRandomMeasure

variable (N : PoissonRandomMeasure P ν)

/-- A Poisson random measure is a measurable map into the measures on the time–mark space. -/
theorem measurable_N : Measurable N.N :=
  Measure.measurable_of_measurable_coe _ fun _ hB => N.measurable_eval hB

/-- The mean count of a measurable set is its reference intensity, finite or not. -/
theorem lintegral_N_apply {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    ∫⁻ ω, N.N ω B ∂P = referenceIntensity ν B := by
  by_cases hB' : referenceIntensity ν B = ⊤
  · rw [hB', lintegral_congr_ae (N.infinite_at_infinite_intensity hB hB'), lintegral_const,
      measure_univ, mul_one]
  · exact Compensated.lintegral_count_eq_referenceIntensity N hB hB'

/-- **The mean measure of a Poisson random measure is its reference intensity.** -/
theorem bind_N : P.bind N.N = referenceIntensity ν := by
  ext B hB
  rw [Measure.bind_apply hB N.measurable_N.aemeasurable, N.lintegral_N_apply hB]

/-- **Campbell's formula.** The mean integral of a measurable nonnegative function against a
Poisson random measure is its integral against the reference intensity. -/
theorem lintegral_lintegral_N {g : ℝ × E → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ ω, ∫⁻ q, g q ∂(N.N ω) ∂P = ∫⁻ q, g q ∂(referenceIntensity ν) := by
  rw [← N.bind_N, Measure.lintegral_bind N.measurable_N.aemeasurable hg.aemeasurable]

/-- The integral of a measurable nonnegative function over a measurable set against a Poisson
random measure is measurable in the sample point. -/
theorem measurable_setLIntegral_N {g : ℝ × E → ℝ≥0∞} (hg : Measurable g) {S : Set (ℝ × E)}
    (hS : MeasurableSet S) : Measurable fun ω => ∫⁻ q in S, g q ∂(N.N ω) := by
  simp_rw [← lintegral_indicator hS]
  exact (Measure.measurable_lintegral (hg.indicator hS)).comp N.measurable_N

/-- Campbell's formula on a measurable set. -/
theorem lintegral_setLIntegral_N {g : ℝ × E → ℝ≥0∞} (hg : Measurable g) {S : Set (ℝ × E)}
    (hS : MeasurableSet S) :
    ∫⁻ ω, ∫⁻ q in S, g q ∂(N.N ω) ∂P = ∫⁻ q in S, g q ∂(referenceIntensity ν) := by
  simp_rw [← lintegral_indicator hS]
  exact N.lintegral_lintegral_N (hg.indicator hS)

/-- Campbell's formula for a function of the mark on a step times the mark space. -/
theorem lintegral_setLIntegral_N_cell {g : E → ℝ≥0∞} (hg : Measurable g) {a : ℝ} (ha : 0 ≤ a)
    (b : ℝ) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc a b ×ˢ Set.univ, g q.2 ∂(N.N ω) ∂P
      = ENNReal.ofReal (b - a) * ∫⁻ e, g e ∂ν := by
  rw [N.lintegral_setLIntegral_N (g := fun q : ℝ × E => g q.2) (hg.comp measurable_snd)
      (S := Set.Ioc a b ×ˢ Set.univ) (measurableSet_Ioc.prod .univ),
    referenceIntensity_restrict_Ioc_prod_univ ha b,
    lintegral_prod (fun q : ℝ × E => g q.2) (hg.comp measurable_snd).aemeasurable]
  simp only [setLIntegral_const, Real.volume_Ioc]
  rw [mul_comm]

/-- Almost surely a Poisson random measure does not charge the time–mark sets over a null set of
marks, so functions of the mark equal `ν`-almost everywhere are equal `N(ω)`-almost
everywhere. -/
theorem ae_ae_eq_comp_snd {f g : E → ℝ} (hfg : f =ᵐ[ν] g) :
    ∀ᵐ ω ∂P, (fun q : ℝ × E => f q.2) =ᵐ[N.N ω] fun q => g q.2 := by
  obtain ⟨Z, hsub, hZ, hZ0⟩ := exists_measurable_superset_of_null (ae_iff.1 hfg)
  have hUZ : MeasurableSet ((Set.univ : Set ℝ) ×ˢ Z) := MeasurableSet.univ.prod hZ
  have h0 : ∫⁻ ω, N.N ω ((Set.univ : Set ℝ) ×ˢ Z) ∂P = 0 := by
    rw [N.lintegral_N_apply hUZ, referenceIntensity, Measure.prod_prod, hZ0, mul_zero]
  have hae := (lintegral_eq_zero_iff (N.measurable_eval hUZ)).1 h0
  filter_upwards [hae] with ω hω
  refine ae_iff.2 (measure_mono_null (fun q hq => ?_) hω)
  exact ⟨Set.mem_univ _, hsub hq⟩

/-- An integrable measurable mark profile is almost surely integrable on a step times the mark
space against a Poisson random measure. -/
theorem ae_integrableOn_cell_of_measurable {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω) := by
  have hmean : ∫⁻ ω, ∫⁻ q in Set.Ioc a b ×ˢ Set.univ, ‖f q.2‖ₑ ∂(N.N ω) ∂P ≠ ⊤ := by
    rw [N.lintegral_setLIntegral_N_cell hfm.enorm ha b]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hf.2.ne
  have hm := N.measurable_setLIntegral_N (g := fun q : ℝ × E => ‖f q.2‖ₑ)
    (hfm.comp measurable_snd).enorm (S := Set.Ioc a b ×ˢ Set.univ)
    (measurableSet_Ioc.prod MeasurableSet.univ)
  filter_upwards [ae_lt_top hm hmean] with ω hω
  exact ⟨(hfm.comp measurable_snd).aestronglyMeasurable, hω⟩

/-- **An integrable mark profile is almost surely integrable on a step times the mark space**
against a Poisson random measure. -/
theorem ae_integrableOn_cell {f : E → ℝ} (hf : Integrable f ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω) := by
  have hmk := hf.1.ae_eq_mk
  filter_upwards [N.ae_integrableOn_cell_of_measurable hf.1.stronglyMeasurable_mk.measurable
    (hf.congr hmk) ha b, N.ae_ae_eq_comp_snd hmk] with ω hω hωe
  exact hω.congr_fun_ae (ae_restrict_of_ae hωe.symm)

/-- The integral of a measurable mark profile on a step times the mark space against a Poisson
random measure is almost everywhere strongly measurable in the sample point. -/
theorem aestronglyMeasurable_setIntegral_cell {f : E → ℝ} (hfm : Measurable f)
    (hf : Integrable f ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    AEStronglyMeasurable (fun ω => ∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) P := by
  have hW : MeasurableSet (Set.Ioc a b ×ˢ (Set.univ : Set E)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hpos := N.measurable_setLIntegral_N
    (ENNReal.measurable_ofReal.comp (hfm.comp measurable_snd)) hW
  have hneg := N.measurable_setLIntegral_N
    (ENNReal.measurable_ofReal.comp (hfm.comp measurable_snd).neg) hW
  refine AEStronglyMeasurable.congr
    ((hpos.ennreal_toReal.sub hneg.ennreal_toReal).aestronglyMeasurable) ?_
  filter_upwards [N.ae_integrableOn_cell_of_measurable hfm hf ha b] with ω hω
  exact (integral_eq_lintegral_pos_part_sub_lintegral_neg_part hω).symm

end PoissonRandomMeasure

/-! ### Simple profiles -/

/-- The integral over a set `s ×ˢ univ` of the indicator of a mark set `B` is the measure of
`s ×ˢ B`. -/
private theorem setIntegral_indicator_snd (μ : Measure (ℝ × E)) (s : Set ℝ) {B : Set E}
    (hB : MeasurableSet B) :
    ∫ q in s ×ˢ Set.univ, B.indicator (fun _ => (1 : ℝ)) q.2 ∂μ = μ.real (s ×ˢ B) := by
  have hfun : (fun q : ℝ × E => B.indicator (fun _ => (1 : ℝ)) q.2)
      = (Prod.snd ⁻¹' B).indicator fun _ => (1 : ℝ) := by
    funext q
    by_cases hq : q.2 ∈ B
    · rw [Set.indicator_of_mem hq, Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' B from hq)]
    · rw [Set.indicator_of_notMem hq,
        Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' B from hq)]
  have hset : Prod.snd ⁻¹' B ∩ s ×ˢ Set.univ = s ×ˢ B := by
    ext q
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_univ, and_true]
    exact and_comm
  rw [hfun, integral_indicator_const _ (measurable_snd hB), smul_eq_mul, mul_one,
    measureReal_def, Measure.restrict_apply (measurable_snd hB), hset, measureReal_def]

/-- **At a simple profile the compensated step integral is the raw integral minus its
compensator.** -/
theorem SimpleProfile.stepIntegral_ae_eq_integral_sub (N : PoissonRandomMeasure P ν)
    (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) {b : ℝ} (hab : a ≤ b) :
    G.stepIntegral N a b =ᵐ[P] fun ω =>
      (∫ q in Set.Ioc a b ×ˢ Set.univ, G.toFun q.2 ∂(N.N ω)) - (b - a) * ∫ e, G.toFun e ∂ν := by
  have hfin : ∀ k, referenceIntensity ν (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ := fun k => by
    rw [referenceIntensity_Ioc_prod' _ ha]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k)
  have hcount : ∀ᵐ ω ∂P, ∀ k, N.N ω (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ := by
    refine ae_all_iff.2 fun k => ?_
    filter_upwards [N.integer_valued (measurableSet_Ioc.prod (G.B_measurable k)) (hfin k)]
      with ω hω
    obtain ⟨n, hn⟩ := hω
    rw [hn]
    exact ENNReal.natCast_ne_top n
  filter_upwards [hcount] with ω hω
  have hW : MeasurableSet (Set.Ioc a b ×ˢ (Set.univ : Set E)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hintN : ∀ k, Integrable (fun q : ℝ × E => G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) q.2)
      ((N.N ω).restrict (Set.Ioc a b ×ˢ Set.univ)) := by
    intro k
    refine Integrable.const_mul ?_ _
    have hfun : (fun q : ℝ × E => (G.B k).indicator (fun _ => (1 : ℝ)) q.2)
        = (Prod.snd ⁻¹' G.B k).indicator fun _ => (1 : ℝ) := by
      funext q
      by_cases hq : q.2 ∈ G.B k
      · rw [Set.indicator_of_mem hq,
          Set.indicator_of_mem (show q ∈ Prod.snd ⁻¹' G.B k from hq)]
      · rw [Set.indicator_of_notMem hq,
          Set.indicator_of_notMem (show q ∉ Prod.snd ⁻¹' G.B k from hq)]
    rw [hfun, integrable_indicator_iff (measurable_snd (G.B_measurable k))]
    refine integrableOn_const ?_
    rw [Measure.restrict_apply (measurable_snd (G.B_measurable k))]
    refine ne_top_of_le_ne_top (hω k) (measure_mono fun q hq => ?_)
    exact ⟨hq.2.1, hq.1⟩
  have hintν : ∀ k, Integrable (fun e => G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) e) ν :=
    fun k => (integrable_indicator_iff (G.B_measurable k)).2
      (integrableOn_const (G.B_finite k)) |>.const_mul _
  have hraw : ∫ q in Set.Ioc a b ×ˢ Set.univ, G.toFun q.2 ∂(N.N ω)
      = ∑ k, G.c k * (N.N ω (Set.Ioc a b ×ˢ G.B k)).toReal := by
    simp only [SimpleProfile.toFun]
    rw [integral_finsetSum _ fun k _ => hintN k]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, setIntegral_indicator_snd _ _ (G.B_measurable k),
      measureReal_def]
  have hcomp : (b - a) * ∫ e, G.toFun e ∂ν
      = ∑ k, G.c k * (referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal := by
    simp only [SimpleProfile.toFun]
    rw [integral_finsetSum _ fun k _ => hintν k, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_indicator_const _ (G.B_measurable k), smul_eq_mul, mul_one,
      referenceIntensity_Ioc_prod' _ ha, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (sub_nonneg.2 hab), measureReal_def]
    ring
  rw [hraw, hcomp, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [PoissonRandomMeasure.compensated, mul_sub]

/-! ### The pathwise identity -/

/-- The compensated integral of a measurable mark profile in `L¹(ν) ∩ L²(ν)` is the raw
integral minus its compensator. -/
theorem compensatedProfile_ae_eq_integral_sub_of_measurable (N : PoissonRandomMeasure P ν)
    {f : E → ℝ} (hfm : Measurable f) (hf1 : Integrable f ν) (hf2 : MemLp f 2 ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N f a b =ᵐ[P] fun ω =>
      (∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) - (b - a) * ∫ e, f e ∂ν := by
  set Φ : (E → ℝ) → Ω → ℝ := fun g ω =>
    (∫ q in Set.Ioc a b ×ˢ Set.univ, g q.2 ∂(N.N ω)) - (b - a) * ∫ e, g e ∂ν with hΦ
  -- simple functions converging to `f` in `L¹(ν)` and in `L²(ν)`
  set g : ℕ → SimpleFunc E ℝ := fun n =>
    SimpleFunc.approxOn f hfm Set.univ 0 (Set.mem_univ 0) n with hgdef
  have hg2 : ∀ n, MemLp (g n) 2 ν := fun n =>
    SimpleFunc.memLp_approxOn hfm hf2 (Set.mem_univ 0) MemLp.zero' n
  have hg1 : ∀ n, Integrable (g n) ν := fun n => memLp_one_iff_integrable.1
    (SimpleFunc.memLp_approxOn hfm (memLp_one_iff_integrable.2 hf1) (Set.mem_univ 0)
      MemLp.zero' n)
  have hL2 : Tendsto (fun n => eLpNorm (⇑(g n) - f) 2 ν) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hfm (Set.mem_univ 0) (by norm_num)
      (by simp) (by simpa using hf2.2)
  have hL1 : Tendsto (fun n => eLpNorm (⇑(g n) - f) 1 ν) atTop (𝓝 0) :=
    SimpleFunc.tendsto_approxOn_Lp_eLpNorm hfm (Set.mem_univ 0) (by norm_num)
      (by simp) (by simpa using (memLp_one_iff_integrable.2 hf1).2)
  set G : ℕ → SimpleProfile E ν := fun n => SimpleProfile.ofSimpleFunc (hg2 n) with hGdef
  have hGf : ∀ n, (G n).toFun = g n := fun n => funext fun e =>
    SimpleProfile.toFun_ofSimpleFunc (hg2 n) e
  have hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (𝓝 0) := by
    refine hL2.congr fun n => ?_
    rw [hGf n]
    rfl
  -- the compensated step integrals are pathwise
  have hstep : ∀ n, (G n).stepIntegral N a b =ᵐ[P] Φ (g n) := fun n => by
    have h := SimpleProfile.stepIntegral_ae_eq_integral_sub N (G n) ha hab
    rw [hGf n] at h
    exact h
  -- the `L¹(P)` bound on the pathwise functional
  have hbound : ∀ n, ∫⁻ ω, ‖Φ (g n) ω - Φ f ω‖ₑ ∂P
      ≤ ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν
        + ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν := by
    intro n
    have hdm : Measurable (⇑(g n) - f) := (g n).measurable.sub hfm
    have hpt : ∀ᵐ ω ∂P, ‖Φ (g n) ω - Φ f ω‖ₑ
        ≤ (∫⁻ q in Set.Ioc a b ×ˢ Set.univ, ‖(⇑(g n) - f) q.2‖ₑ ∂(N.N ω))
          + ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν := by
      filter_upwards [N.ae_integrableOn_cell_of_measurable (g n).measurable (hg1 n) ha b,
        N.ae_integrableOn_cell_of_measurable hfm hf1 ha b] with ω h1 h2
      have hsplit : Φ (g n) ω - Φ f ω
          = (∫ q in Set.Ioc a b ×ˢ Set.univ, (⇑(g n) - f) q.2 ∂(N.N ω))
            - (b - a) * ∫ e, (⇑(g n) - f) e ∂ν := by
        simp only [hΦ, Pi.sub_apply]
        rw [integral_sub h1 h2, integral_sub (hg1 n) hf1]
        ring
      rw [hsplit]
      refine enorm_sub_le.trans (add_le_add (enorm_integral_le_lintegral_enorm _) ?_)
      rw [enorm_mul, Real.enorm_of_nonneg (sub_nonneg.2 hab), eLpNorm_one_eq_lintegral_enorm]
      gcongr
      exact enorm_integral_le_lintegral_enorm _
    refine (lintegral_mono_ae hpt).trans (le_of_eq ?_)
    rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one,
      N.lintegral_setLIntegral_N_cell hdm.enorm ha b, eLpNorm_one_eq_lintegral_enorm]
  -- the two limits
  have hJm := (memLp_compensatedProfile N f a b).aestronglyMeasurable
  have hXm : ∀ n, AEStronglyMeasurable ((G n).stepIntegral N a b) P :=
    fun n => ((G n).memLp_stepIntegral N ha b).aestronglyMeasurable
  have hΦm : AEStronglyMeasurable (Φ f) P :=
    (N.aestronglyMeasurable_setIntegral_cell hfm hf1 ha b).sub aestronglyMeasurable_const
  have h1 : Tendsto (fun n => ∫⁻ ω, ‖compensatedProfile N f a b ω
      - (G n).stepIntegral N a b ω‖ₑ ∂P) atTop (𝓝 0) := by
    have hJ := tendsto_stepIntegral_compensatedProfile N hf2 ha hab G hG
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hJ (fun n => zero_le)
      fun n => ?_
    refine (lintegral_enorm_le_eLpNorm_two (hJm.sub (hXm n))).trans (le_of_eq ?_)
    exact eLpNorm_sub_comm _ _ 2 P
  have h2 : Tendsto (fun n => ∫⁻ ω, ‖(G n).stepIntegral N a b ω - Φ f ω‖ₑ ∂P)
      atTop (𝓝 0) := by
    have hlim : Tendsto (fun n => ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν
        + ENNReal.ofReal (b - a) * eLpNorm (⇑(g n) - f) 1 ν) atTop (𝓝 0) := by
      have hmul := ENNReal.Tendsto.const_mul hL1
        (Or.inr (show ENNReal.ofReal (b - a) ≠ ⊤ from ENNReal.ofReal_ne_top))
      rw [mul_zero] at hmul
      simpa using hmul.add hmul
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun n => zero_le)
      fun n => ?_
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hbound n)
    filter_upwards [hstep n] with ω hω
    rw [hω]
  exact ae_eq_of_tendsto_lintegral_enorm hJm hΦm hXm h1 h2

/-- **The compensated integral of a mark profile in `L¹(ν) ∩ L²(ν)` is the raw integral minus
its compensator.** Almost surely the profile is integrable on `(a, b] × E` against the Poisson
random measure and `∫_E f ΔÑ = ∫_{(a, b] × E} f(e) N(ds, de) − (b − a) ∫_E f dν`. -/
theorem compensatedProfile_ae_eq_integral_sub (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf1 : Integrable f ν) (hf2 : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω)
      ∧ compensatedProfile N f a b ω
        = (∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) - (b - a) * ∫ e, f e ∂ν := by
  set f' := hf1.1.mk f
  have hmk : f =ᵐ[ν] f' := hf1.1.ae_eq_mk
  have hfm : Measurable f' := hf1.1.stronglyMeasurable_mk.measurable
  filter_upwards [N.ae_integrableOn_cell hf1 ha b, N.ae_ae_eq_comp_snd hmk,
    compensatedProfile_ae_eq_integral_sub_of_measurable N hfm (hf1.congr hmk)
      (hf2.ae_eq hmk) ha hab] with ω hint hωe hω
  refine ⟨hint, ?_⟩
  rw [compensatedProfile_congr_ae N hmk a b, hω, integral_congr_ae hmk,
    integral_congr_ae (ae_restrict_of_ae hωe)]

section Repr

variable {Ω' : Type u} (m : MeasurableSpace Ω') [MeasurableSpace Ω'] {P' : Measure Ω'}
  [IsProbabilityMeasure P']

/-- The representative of the compensated integral of a mark profile in `L¹(ν) ∩ L²(ν)` for a
sub-σ-algebra is the raw integral minus its compensator. -/
theorem compensatedProfileRepr_ae_eq_integral_sub (N : PoissonRandomMeasure P' ν) {f : E → ℝ}
    (hf1 : Integrable f ν) (hf2 : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᵐ ω ∂P', IntegrableOn (fun q : ℝ × E => f q.2) (Set.Ioc a b ×ˢ Set.univ) (N.N ω)
      ∧ compensatedProfileRepr m N f a b ω
        = (∫ q in Set.Ioc a b ×ˢ Set.univ, f q.2 ∂(N.N ω)) - (b - a) * ∫ e, f e ∂ν := by
  filter_upwards [compensatedProfile_ae_eq_integral_sub N hf1 hf2 ha hab,
    compensatedProfileRepr_ae_eq m N f a b] with ω hω hr
  exact ⟨hω.1, hr.trans hω.2⟩

end Repr

end LevyStochCalc.Poisson
