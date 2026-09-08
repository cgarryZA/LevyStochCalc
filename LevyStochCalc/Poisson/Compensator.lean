/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedIsometry
import LevyStochCalc.Poisson.Filtered
import LevyStochCalc.Poisson.FiniteActivity
import LevyStochCalc.Probability.MarkedPredictable

/-!
# The reference intensity as compensator on a finite-activity window

On a predictable rectangle the count of the Poisson random measure is independent of the past
event carried by the rectangle, so its mean factorises as the probability of that event times
the intensity of the time–mark part. The sets on which the two mean occupations agree form a
Dynkin system — complements by subtracting from the finite occupation of the window, countable
disjoint unions by monotone convergence — so they agree on every predictable set.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- A time interval times a mark set of finite intensity has finite reference intensity. -/
theorem referenceIntensity_Ioc_prod_ne_top' {B : Set E} (hBν : ν B ≠ ⊤) (r q : ℝ) :
    referenceIntensity ν (Set.Ioc r q ×ˢ B) ≠ ⊤ := by
  rw [referenceIntensity, Measure.prod_prod]
  refine ENNReal.mul_ne_top ?_ hBν
  rw [Measure.restrict_apply measurableSet_Ioc]
  exact ne_top_of_le_ne_top (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
    (measure_mono Set.inter_subset_left)

section Rectangle

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **Independence factorises the mean count of a future rectangle over a past event.** -/
theorem setLIntegral_count_eq (hℱ : IsPoissonFiltration N ℱ) {r q : ℝ} (hr : 0 ≤ r)
    {F : Set Ω} (hF : MeasurableSet[ℱ r] F) {B : Set E} (hB : MeasurableSet B) (hBν : ν B ≠ ⊤) :
    ∫⁻ ω in F, N.N ω (Set.Ioc r q ×ˢ B) ∂P
      = P F * referenceIntensity ν (Set.Ioc r q ×ˢ B) := by
  rcases le_or_gt q r with hqr | hrq
  · have hempty : Set.Ioc r q = (∅ : Set ℝ) := Set.Ioc_eq_empty (not_lt.mpr hqr)
    simp [hempty]
  · have hmeas : Measurable fun ω => N.N ω (Set.Ioc r q ×ˢ B) :=
      N.measurable_eval (measurableSet_Ioc.prod hB)
    have hfin : referenceIntensity ν (Set.Ioc r q ×ˢ B) ≠ ⊤ :=
      referenceIntensity_Ioc_prod_ne_top' hBν r q
    have hidp := hℱ.indep hr hrq hB hBν
    have hmapeq : (P.restrict F).map (fun ω => N.N ω (Set.Ioc r q ×ˢ B))
        = P F • P.map (fun ω => N.N ω (Set.Ioc r q ×ˢ B)) := by
      ext U hU
      rw [Measure.map_apply hmeas hU, Measure.restrict_apply (hmeas hU), Measure.smul_apply,
        Measure.map_apply hmeas hU, smul_eq_mul, Set.inter_comm]
      exact (Indep_iff _ _ _).mp hidp F ((fun ω => N.N ω (Set.Ioc r q ×ˢ B)) ⁻¹' U) hF
        ⟨U, hU, rfl⟩
    calc ∫⁻ ω in F, N.N ω (Set.Ioc r q ×ˢ B) ∂P
        = ∫⁻ x, x ∂((P.restrict F).map fun ω => N.N ω (Set.Ioc r q ×ˢ B)) :=
          (lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' hmeas).symm
      _ = ∫⁻ x, x ∂(P F • P.map fun ω => N.N ω (Set.Ioc r q ×ˢ B)) := by rw [hmapeq]
      _ = P F * ∫⁻ x, x ∂(P.map fun ω => N.N ω (Set.Ioc r q ×ˢ B)) := by
          rw [lintegral_smul_measure, smul_eq_mul]
      _ = P F * ∫⁻ ω, N.N ω (Set.Ioc r q ×ˢ B) ∂P := by
          rw [lintegral_map (f := fun x : ℝ≥0∞ => x) measurable_id' hmeas]
      _ = P F * referenceIntensity ν (Set.Ioc r q ×ˢ B) := by
          rw [Compensated.lintegral_count_eq_referenceIntensity N
            (measurableSet_Ioc.prod hB) hfin]

end Rectangle

section Window

/-- The count of the slice of a set of the time–mark space, inside a window. -/
noncomputable def sliceCount (N : PoissonRandomMeasure P ν) (R : Set (ℝ × E))
    (S : Set (Ω × ℝ × E)) (ω : Ω) : ℝ≥0∞ := N.N ω (Prod.mk ω ⁻¹' S ∩ R)

/-- The reference intensity of the slice of a set of the time–mark space, inside a window. -/
noncomputable def sliceIntensity (ν : Measure E) (R : Set (ℝ × E)) (S : Set (Ω × ℝ × E))
    (ω : Ω) : ℝ≥0∞ := referenceIntensity ν (Prod.mk ω ⁻¹' S ∩ R)

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The reference intensity compensates the counts on predictable sets.** Over a window of
finite intensity the mean count of a predictable set equals its mean intensity. -/
theorem aemeasurable_and_lintegral_slice_eq (hℱ : IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {S : Set (Ω × ℝ × E)} (hS : MeasurableSet[Probability.markedPredictableSigma ℱ ν] S) :
    AEMeasurable (sliceCount N (Set.Ioc (0 : ℝ) T ×ˢ A) S) P
      ∧ Measurable (sliceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) S)
      ∧ ∫⁻ ω, sliceCount N (Set.Ioc (0 : ℝ) T ×ˢ A) S ω ∂P
          = ∫⁻ ω, sliceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) S ω ∂P := by
  classical
  set R : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hRdef
  have hRm : MeasurableSet R := measurableSet_Ioc.prod hA
  have hRfin : referenceIntensity ν R ≠ ⊤ := referenceIntensity_Ioc_prod_ne_top hAν T
  have hNR : ∫⁻ ω, N.N ω R ∂P = referenceIntensity ν R :=
    Compensated.lintegral_count_eq_referenceIntensity N hRm hRfin
  have hNRfin : ∀ᵐ ω ∂P, N.N ω R ≠ ⊤ := count_Ioc_ne_top N hA hAν T
  have hNRmeas : Measurable fun ω => N.N ω R := N.measurable_eval hRm
  have hIle : ∀ (S' : Set (Ω × ℝ × E)) (ω : Ω),
      sliceIntensity ν R S' ω ≤ referenceIntensity ν R :=
    fun _ _ => measure_mono Set.inter_subset_right
  have hIfin : ∀ S' : Set (Ω × ℝ × E), ∫⁻ ω, sliceIntensity ν R S' ω ∂P ≠ ⊤ := by
    intro S'
    refine ne_top_of_le_ne_top ?_ (lintegral_mono fun ω => hIle S' ω)
    rw [lintegral_const, measure_univ, mul_one]
    exact hRfin
  refine MeasurableSpace.induction_on_inter
    (C := fun S' _ => AEMeasurable (sliceCount N R S') P ∧ Measurable (sliceIntensity ν R S')
      ∧ ∫⁻ ω, sliceCount N R S' ω ∂P = ∫⁻ ω, sliceIntensity ν R S' ω ∂P)
    rfl (Probability.isPiSystem_markedPredictableRect ℱ ν) ?_ ?_ ?_ ?_ S hS
  · have h0 : sliceCount N R ∅ = fun _ : Ω => (0 : ℝ≥0∞) := by
      funext ω; simp [sliceCount]
    have h1 : sliceIntensity ν R ∅ = fun _ : Ω => (0 : ℝ≥0∞) := by
      funext ω; simp [sliceIntensity]
    rw [h0, h1]
    exact ⟨measurable_const.aemeasurable, measurable_const, rfl⟩
  · rintro _ ⟨r, q, F, B, hr, hF, hB, hBν, rfl⟩
    have hFm : MeasurableSet F := ℱ.le r _ hF
    have hBA : MeasurableSet (B ∩ A) := hB.inter hA
    have hBAν : ν (B ∩ A) ≠ ⊤ := ne_top_of_le_ne_top hBν (measure_mono Set.inter_subset_left)
    have hrectm : MeasurableSet (Set.Ioc r (min q T) ×ˢ (B ∩ A)) := measurableSet_Ioc.prod hBA
    have hslice : ∀ ω : Ω, Prod.mk ω ⁻¹' (F ×ˢ (Set.Ioc r q ×ˢ B)) ∩ R
        = if ω ∈ F then Set.Ioc r (min q T) ×ˢ (B ∩ A) else ∅ := by
      intro ω
      by_cases hω : ω ∈ F
      · rw [if_pos hω, hRdef]
        ext p
        have hpos : r < p.1 → (0 : ℝ) < p.1 := fun h => lt_of_le_of_lt hr h
        simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_prod, Set.mem_Ioc, le_min_iff,
          hω, true_and]
        tauto
      · rw [if_neg hω]
        ext p
        simp [hω]
    have hcount : sliceCount N R (F ×ˢ (Set.Ioc r q ×ˢ B))
        = F.indicator fun ω => N.N ω (Set.Ioc r (min q T) ×ˢ (B ∩ A)) := by
      funext ω
      rw [sliceCount, hslice ω]
      by_cases hω : ω ∈ F
      · rw [if_pos hω, Set.indicator_of_mem hω]
      · rw [if_neg hω, Set.indicator_of_notMem hω, measure_empty]
    have hint : sliceIntensity ν R (F ×ˢ (Set.Ioc r q ×ˢ B))
        = F.indicator fun _ => referenceIntensity ν (Set.Ioc r (min q T) ×ˢ (B ∩ A)) := by
      funext ω
      rw [sliceIntensity, hslice ω]
      by_cases hω : ω ∈ F
      · rw [if_pos hω, Set.indicator_of_mem hω]
      · rw [if_neg hω, Set.indicator_of_notMem hω, measure_empty]
    refine ⟨?_, ?_, ?_⟩
    · rw [hcount]
      exact ((N.measurable_eval hrectm).indicator hFm).aemeasurable
    · rw [hint]
      exact measurable_const.indicator hFm
    · rw [hcount, hint, lintegral_indicator hFm, lintegral_indicator hFm,
        setLIntegral_count_eq N hℱ hr hF hBA hBAν, setLIntegral_const]
      exact mul_comm _ _
  · rintro S' hSm ⟨ihc, ihi, ihe⟩
    have hXm : ∀ ω : Ω, MeasurableSet (Prod.mk ω ⁻¹' S') :=
      fun ω => Probability.measurableSet_slice hSm ω
    have hCfin : ∫⁻ ω, sliceCount N R S' ω ∂P ≠ ⊤ := by rw [ihe]; exact hIfin S'
    have hCle : ∀ᵐ ω ∂P, sliceCount N R S' ω ≤ N.N ω R :=
      Filter.Eventually.of_forall fun _ => measure_mono Set.inter_subset_right
    have hcompl' : sliceCount N R S'ᶜ =ᵐ[P] fun ω => N.N ω R - sliceCount N R S' ω := by
      filter_upwards [hNRfin] with ω hω
      have hsum : N.N ω (R ∩ Prod.mk ω ⁻¹' S') + N.N ω (R \ Prod.mk ω ⁻¹' S') = N.N ω R :=
        measure_inter_add_sdiff _ (hXm ω)
      have h1 : sliceCount N R S' ω = N.N ω (R ∩ Prod.mk ω ⁻¹' S') := by
        rw [sliceCount, Set.inter_comm]
      have h2 : sliceCount N R S'ᶜ ω = N.N ω (R \ Prod.mk ω ⁻¹' S') := by
        rw [sliceCount, Set.preimage_compl, Set.inter_comm, Set.sdiff_eq]
      rw [h1, h2, ← hsum]
      refine (ENNReal.add_sub_cancel_left ?_).symm
      exact ne_top_of_le_ne_top hω (measure_mono Set.inter_subset_left)
    have hicompl : sliceIntensity ν R S'ᶜ
        = fun ω => referenceIntensity ν R - sliceIntensity ν R S' ω := by
      funext ω
      have hsum : referenceIntensity ν (R ∩ Prod.mk ω ⁻¹' S')
          + referenceIntensity ν (R \ Prod.mk ω ⁻¹' S') = referenceIntensity ν R :=
        measure_inter_add_sdiff _ (hXm ω)
      have h1 : sliceIntensity ν R S' ω = referenceIntensity ν (R ∩ Prod.mk ω ⁻¹' S') := by
        rw [sliceIntensity, Set.inter_comm]
      have h2 : sliceIntensity ν R S'ᶜ ω = referenceIntensity ν (R \ Prod.mk ω ⁻¹' S') := by
        rw [sliceIntensity, Set.preimage_compl, Set.inter_comm, Set.sdiff_eq]
      rw [h1, h2, ← hsum]
      refine (ENNReal.add_sub_cancel_left ?_).symm
      exact ne_top_of_le_ne_top hRfin (measure_mono Set.inter_subset_left)
    refine ⟨?_, ?_, ?_⟩
    · exact (hNRmeas.aemeasurable.sub ihc).congr hcompl'.symm
    · rw [hicompl]
      exact measurable_const.sub ihi
    · rw [lintegral_congr_ae hcompl', hicompl, lintegral_sub' ihc hCfin hCle,
        lintegral_sub ihi (hIfin S') (Filter.Eventually.of_forall fun ω => hIle S' ω), hNR,
        lintegral_const, measure_univ, mul_one, ihe]
  · intro f hd hfm ih
    have hdisj : ∀ ω : Ω, Pairwise (Function.onFun Disjoint
        fun i => Prod.mk ω ⁻¹' f i ∩ R) := fun ω i j hij =>
      Disjoint.mono Set.inter_subset_left Set.inter_subset_left
        ((hd hij).preimage (Prod.mk ω))
    have hslice : ∀ ω : Ω, Prod.mk ω ⁻¹' (⋃ i, f i) ∩ R = ⋃ i, Prod.mk ω ⁻¹' f i ∩ R := by
      intro ω
      rw [Set.preimage_iUnion, Set.iUnion_inter]
    have hcount : sliceCount N R (⋃ i, f i) = fun ω => ∑' i, sliceCount N R (f i) ω := by
      funext ω
      rw [sliceCount, hslice ω,
        measure_iUnion (hdisj ω) fun i => (Probability.measurableSet_slice (hfm i) ω).inter hRm]
      rfl
    have hint : sliceIntensity ν R (⋃ i, f i) = fun ω => ∑' i, sliceIntensity ν R (f i) ω := by
      funext ω
      rw [sliceIntensity, hslice ω,
        measure_iUnion (hdisj ω) fun i => (Probability.measurableSet_slice (hfm i) ω).inter hRm]
      rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hcount]
      exact AEMeasurable.tsum fun i => (ih i).1
    · rw [hint]
      exact Measurable.tsum fun i => (ih i).2.1
    · rw [hcount, hint, lintegral_tsum fun i => (ih i).1,
        lintegral_tsum fun i => (ih i).2.1.aemeasurable]
      exact tsum_congr fun i => (ih i).2.2

/-- **The reference intensity compensates the counts on predictable functions.** Over a window
of finite intensity the mean lower integral of a predictable marked function against the random
measure equals its mean lower integral against the reference intensity. -/
theorem lintegral_lintegral_slice_eq (hℱ : IsPoissonFiltration N ℱ)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {Ψ : Ω × ℝ × E → ℝ≥0∞}
    (hΨ : Measurable[Probability.markedPredictableSigma ℱ ν] Ψ) :
    ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(N.N ω) ∂P
      = ∫⁻ ω, ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, Ψ (ω, p) ∂(referenceIntensity ν) ∂P := by
  classical
  set R : Set (ℝ × E) := Set.Ioc (0 : ℝ) T ×ˢ A with hRdef
  have hslicemeas : ∀ {G : Ω × ℝ × E → ℝ≥0∞},
      Measurable[Probability.markedPredictableSigma ℱ ν] G →
      ∀ ω : Ω, Measurable fun p : ℝ × E => G (ω, p) := by
    intro G hG ω
    exact (hG.mono (Probability.markedPredictableSigma_le ℱ ν) le_rfl).comp
      measurable_prodMk_left
  refine (@Measurable.ennreal_induction (Ω × ℝ × E)
    (Probability.markedPredictableSigma ℱ ν)
    (fun G => AEMeasurable (fun ω => ∫⁻ p in R, G (ω, p) ∂(N.N ω)) P
      ∧ Measurable (fun ω => ∫⁻ p in R, G (ω, p) ∂(referenceIntensity ν))
      ∧ ∫⁻ ω, ∫⁻ p in R, G (ω, p) ∂(N.N ω) ∂P
          = ∫⁻ ω, ∫⁻ p in R, G (ω, p) ∂(referenceIntensity ν) ∂P)
    ?_ ?_ ?_ Ψ hΨ).2.2
  · intro c S hS
    obtain ⟨hc, hi, he⟩ := aemeasurable_and_lintegral_slice_eq N hℱ hA hAν T hS
    have hXm : ∀ ω : Ω, MeasurableSet (Prod.mk ω ⁻¹' S) :=
      fun ω => Probability.measurableSet_slice hS ω
    have hpt : ∀ (μ : Measure (ℝ × E)) (ω : Ω),
        ∫⁻ p in R, (Set.indicator S fun _ => c) (ω, p) ∂μ = c * μ (Prod.mk ω ⁻¹' S ∩ R) := by
      intro μ ω
      have hfun : (fun p : ℝ × E => (Set.indicator S fun _ => c) (ω, p))
          = (Prod.mk ω ⁻¹' S).indicator fun _ => c := by
        funext p
        by_cases hp : (ω, p) ∈ S
        · rw [Set.indicator_of_mem hp,
            Set.indicator_of_mem (show p ∈ Prod.mk ω ⁻¹' S from hp)]
        · rw [Set.indicator_of_notMem hp,
            Set.indicator_of_notMem (show p ∉ Prod.mk ω ⁻¹' S from hp)]
      rw [hfun, lintegral_indicator (hXm ω), setLIntegral_const,
        Measure.restrict_apply (hXm ω), mul_comm]
    have hN : (fun ω => ∫⁻ p in R, (Set.indicator S fun _ => c) (ω, p) ∂(N.N ω))
        = fun ω => c * sliceCount N R S ω := funext fun ω => hpt (N.N ω) ω
    have hI : (fun ω => ∫⁻ p in R, (Set.indicator S fun _ => c) (ω, p) ∂(referenceIntensity ν))
        = fun ω => c * sliceIntensity ν R S ω := funext fun ω => hpt (referenceIntensity ν) ω
    refine ⟨?_, ?_, ?_⟩
    · rw [hN]; exact hc.const_mul c
    · rw [hI]; exact hi.const_mul c
    · rw [hN, hI, lintegral_const_mul'' c hc, lintegral_const_mul'' c hi.aemeasurable, he]
  · rintro f g - hf hg ⟨hcf, hif, hef⟩ ⟨hcg, hig, heg⟩
    have hsplit : ∀ (μ : Measure (ℝ × E)) (ω : Ω), Measurable (fun p : ℝ × E => f (ω, p)) →
        ∫⁻ p in R, (f + g) (ω, p) ∂μ
          = (∫⁻ p in R, f (ω, p) ∂μ) + ∫⁻ p in R, g (ω, p) ∂μ := by
      intro μ ω hfω
      exact lintegral_add_left hfω _
    have hN : (fun ω => ∫⁻ p in R, (f + g) (ω, p) ∂(N.N ω))
        = fun ω => (∫⁻ p in R, f (ω, p) ∂(N.N ω)) + ∫⁻ p in R, g (ω, p) ∂(N.N ω) :=
      funext fun ω => hsplit (N.N ω) ω (hslicemeas hf ω)
    have hI : (fun ω => ∫⁻ p in R, (f + g) (ω, p) ∂(referenceIntensity ν))
        = fun ω => (∫⁻ p in R, f (ω, p) ∂(referenceIntensity ν))
            + ∫⁻ p in R, g (ω, p) ∂(referenceIntensity ν) :=
      funext fun ω => hsplit (referenceIntensity ν) ω (hslicemeas hf ω)
    refine ⟨?_, ?_, ?_⟩
    · rw [hN]; exact hcf.add hcg
    · rw [hI]; exact hif.add hig
    · rw [hN, hI, lintegral_add_left' hcf, lintegral_add_left' hif.aemeasurable, hef, heg]
  · intro f hf hmono ih
    have hN : (fun ω => ∫⁻ p in R, (⨆ n, f n (ω, p)) ∂(N.N ω))
        = fun ω => ⨆ n, ∫⁻ p in R, f n (ω, p) ∂(N.N ω) := by
      funext ω
      exact lintegral_iSup (fun n => hslicemeas (hf n) ω)
        (fun m n hmn p => hmono hmn (ω, p))
    have hI : (fun ω => ∫⁻ p in R, (⨆ n, f n (ω, p)) ∂(referenceIntensity ν))
        = fun ω => ⨆ n, ∫⁻ p in R, f n (ω, p) ∂(referenceIntensity ν) := by
      funext ω
      exact lintegral_iSup (fun n => hslicemeas (hf n) ω)
        (fun m n hmn p => hmono hmn (ω, p))
    have hmonoN : ∀ ω : Ω, Monotone fun n => ∫⁻ p in R, f n (ω, p) ∂(N.N ω) :=
      fun ω m n hmn => lintegral_mono fun p => hmono hmn (ω, p)
    have hmonoI : ∀ ω : Ω, Monotone fun n => ∫⁻ p in R, f n (ω, p) ∂(referenceIntensity ν) :=
      fun ω m n hmn => lintegral_mono fun p => hmono hmn (ω, p)
    refine ⟨?_, ?_, ?_⟩
    · rw [hN]; exact AEMeasurable.iSup fun n => (ih n).1
    · rw [hI]; exact Measurable.iSup fun n => (ih n).2.1
    · rw [hN, hI, lintegral_iSup' (fun n => (ih n).1)
        (Filter.Eventually.of_forall hmonoN),
        lintegral_iSup' (fun n => ((ih n).2.1).aemeasurable)
        (Filter.Eventually.of_forall hmonoI)]
      exact iSup_congr fun n => (ih n).2.2

end Window

end LevyStochCalc.Poisson
