/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.ZeroIntensity

/-!
# Time-simplicity of a Poisson random measure on a finite-intensity set

On a set of finite reference intensity the count of a Poisson random measure exceeds one with
probability at most the square of the intensity. The reference intensity is a product with
Lebesgue measure in time, so the masses of the dyadic time slabs of such a set are the integrals
of an integrable density over intervals of vanishing length, and therefore have vanishing
supremum. A union bound then makes the probability that some slab of level `n` carries two or
more points tend to zero, so almost surely no two points share a time and every point is simple.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Tail

/-- The Poisson law of mean `r` puts mass at most `r ^ 2` on the counts of at least two. -/
theorem poissonMeasure_two_le_le (r : ℝ≥0) :
    ProbabilityTheory.poissonMeasure r {n : ℕ | 2 ≤ n} ≤ ENNReal.ofReal ((r : ℝ) ^ 2) := by
  have hms : MeasurableSet ({0, 1} : Set ℕ) :=
    (measurableSet_singleton 0).union (measurableSet_singleton 1)
  have hset : {n : ℕ | 2 ≤ n} = ({0, 1} : Set ℕ)ᶜ := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
    omega
  have hpair : ProbabilityTheory.poissonMeasure r ({0, 1} : Set ℕ)
      = ENNReal.ofReal (Real.exp (-(r : ℝ)) + Real.exp (-(r : ℝ)) * (r : ℝ)) := by
    rw [Set.insert_eq, measure_union (by simp) (measurableSet_singleton 1),
      ProbabilityTheory.poissonMeasure_singleton, ProbabilityTheory.poissonMeasure_singleton,
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    norm_num
  have hc0 : (0 : ℝ) ≤ Real.exp (-(r : ℝ)) + Real.exp (-(r : ℝ)) * (r : ℝ) := by positivity
  rw [hset, prob_compl_eq_one_sub hms, hpair, ← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub _ hc0]
  refine ENNReal.ofReal_le_ofReal ?_
  have hE : 1 - Real.exp (-(r : ℝ)) ≤ (r : ℝ) := by
    have h := Real.add_one_le_exp (-(r : ℝ))
    linarith
  have hr0 : (0 : ℝ) ≤ (r : ℝ) := r.coe_nonneg
  nlinarith [mul_nonneg hr0 (sub_nonneg.mpr hE)]

/-- **On a set of finite reference intensity a Poisson random measure carries two or more points
with probability at most the square of the intensity.** -/
theorem measure_two_le_count_le (N : PoissonRandomMeasure.{u, v, w} P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    P {ω | 2 ≤ N.N ω B} ≤ referenceIntensity ν B ^ 2 := by
  have hms : MeasurableSet {x : ℝ≥0∞ | 2 ≤ x} := measurableSet_le measurable_const measurable_id
  have hpre : ((↑) : ℕ → ℝ≥0∞) ⁻¹' {x : ℝ≥0∞ | 2 ≤ x} = {n : ℕ | 2 ≤ n} := by
    ext n
    simp [Set.mem_preimage, Set.mem_setOf_eq, Nat.ofNat_le_cast]
  have hlaw := N.poisson_law hB hfin
  have hpush : P {ω | 2 ≤ N.N ω B}
      = ProbabilityTheory.poissonMeasure (referenceIntensity ν B).toNNReal {n : ℕ | 2 ≤ n} := by
    rw [show {ω | 2 ≤ N.N ω B} = (fun ω => N.N ω B) ⁻¹' {x : ℝ≥0∞ | 2 ≤ x} from rfl,
      ← Measure.map_apply (N.measurable_eval hB) hms, hlaw, poissonMeasureENN,
      Measure.map_apply measurable_from_nat hms, hpre]
  rw [hpush]
  refine (poissonMeasure_two_le_le _).trans (le_of_eq ?_)
  rw [← NNReal.coe_pow, ENNReal.ofReal_coe_nnreal, ENNReal.coe_pow,
    ENNReal.coe_toNNReal hfin]

end Tail

section Mesh

/-- The `k`-th dyadic time slab of level `n`. -/
def timeSlab (n k : ℕ) : Set ℝ := Set.Ioc ((k : ℝ) / 2 ^ n) (((k : ℝ) + 1) / 2 ^ n)

theorem measurableSet_timeSlab (n k : ℕ) : MeasurableSet (timeSlab n k) := measurableSet_Ioc

theorem volume_timeSlab (n k : ℕ) :
    volume (timeSlab n k) = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
  rw [timeSlab, Real.volume_Ioc]
  congr 1
  rw [div_sub_div_same, add_sub_cancel_left, div_pow, one_pow]

theorem pairwiseDisjoint_timeSlab (n : ℕ) :
    Pairwise (Function.onFun Disjoint (timeSlab n)) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have key : ∀ i j : ℕ, i < j → Disjoint (timeSlab n i) (timeSlab n j) := by
    intro i j h
    have hij : ((i : ℝ) + 1) / 2 ^ n ≤ (j : ℝ) / 2 ^ n := by
      have hnum : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
      gcongr
    refine Set.disjoint_left.mpr fun x hxi hxj => ?_
    exact absurd (lt_of_le_of_lt (le_trans hxi.2 hij) hxj.1) (lt_irrefl _)
  intro i j hij
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h
  · exact (key j i h).symm

theorem iUnion_timeSlab (n : ℕ) : (⋃ k : ℕ, timeSlab n k) = Set.Ioi (0 : ℝ) := by
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  ext x
  simp only [Set.mem_iUnion, timeSlab, Set.mem_Ioc, Set.mem_Ioi]
  constructor
  · rintro ⟨k, hk1, -⟩
    exact lt_of_le_of_lt (by positivity) hk1
  · intro hx
    have hy : (0 : ℝ) < x * 2 ^ n := by positivity
    set m : ℕ := ⌈x * 2 ^ n⌉₊ with hm
    have hm1 : 1 ≤ m := Nat.one_le_ceil_iff.mpr hy
    refine ⟨m - 1, ?_, ?_⟩
    · rw [div_lt_iff₀ hpow]
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
      rw [hcast]
      have := Nat.ceil_lt_add_one hy.le
      rw [← hm] at this
      linarith
    · rw [le_div_iff₀ hpow]
      have hcast : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by
        rw [Nat.cast_sub hm1, Nat.cast_one]
        ring
      rw [hcast, hm]
      exact Nat.le_ceil _


/-- **The dyadic time mesh of an integrable density vanishes.** For a fine enough level every
slab carries at most `ε` of the density. -/
theorem exists_iSup_setLIntegral_timeSlab_le {f : ℝ → ℝ≥0∞} (hf : Measurable f)
    (hfin : ∫⁻ x, f x ≠ ⊤) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ n : ℕ, ⨆ k : ℕ, ∫⁻ x in timeSlab n k, f x ≤ ε := by
  set g : ℕ → ℝ → ℝ≥0∞ := fun M x => min (f x) (M : ℝ≥0∞) with hgdef
  have hgm : ∀ M, Measurable (g M) := fun M => hf.min measurable_const
  have hgle : ∀ M x, g M x ≤ f x := fun M x => min_le_left _ _
  have hgfin : ∀ M, ∫⁻ x, g M x ≠ ⊤ :=
    fun M => ne_top_of_le_ne_top hfin (lintegral_mono (hgle M))
  have hmono : Monotone g := fun a b hab x => min_le_min le_rfl (Nat.cast_le.mpr hab)
  have hpt : ∀ x : ℝ, ⨆ M : ℕ, g M x = f x := by
    intro x
    refine le_antisymm (iSup_le fun M => min_le_left _ _) ?_
    by_cases hx : f x = ⊤
    · have hgM : ∀ M : ℕ, g M x = (M : ℝ≥0∞) := by
        intro M
        simp only [hgdef]
        rw [hx, min_eq_right le_top]
      rw [hx, ← ENNReal.iSup_natCast]
      exact iSup_mono fun M => (hgM M).ge
    · obtain ⟨M, hM⟩ := ENNReal.exists_nat_gt hx
      exact le_iSup_of_le M (le_of_eq (min_eq_left hM.le).symm)
  have hsup : ⨆ M : ℕ, ∫⁻ x, g M x = ∫⁻ x, f x := by
    rw [← lintegral_iSup hgm hmono]
    exact lintegral_congr hpt
  obtain ⟨M, hM⟩ : ∃ M : ℕ, (∫⁻ x, f x) - ∫⁻ x, g M x ≤ ε / 2 := by
    by_cases h0 : ∫⁻ x, f x = 0
    · exact ⟨0, by rw [h0]; simp⟩
    have hlt : (∫⁻ x, f x) - ε / 2 < ⨆ M : ℕ, ∫⁻ x, g M x := by
      rw [hsup]
      exact ENNReal.sub_lt_self hfin h0 (ENNReal.half_pos hε).ne'
    obtain ⟨M, hMlt⟩ := lt_iSup_iff.mp hlt
    refine ⟨M, ?_⟩
    rw [tsub_le_iff_right]
    calc ∫⁻ x, f x ≤ ((∫⁻ x, f x) - ε / 2) + ε / 2 := le_tsub_add
      _ ≤ (∫⁻ x, g M x) + ε / 2 := by gcongr <;> exact hMlt.le
      _ = ε / 2 + ∫⁻ x, g M x := add_comm _ _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (M : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) ≤ ε / 2 := by
    have hreal : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hE : Tendsto (fun n : ℕ => ENNReal.ofReal ((1 / 2 : ℝ) ^ n)) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal hreal
    have hmul := ENNReal.Tendsto.const_mul hE (Or.inr (ENNReal.natCast_ne_top M))
    rw [mul_zero] at hmul
    exact ((ENNReal.tendsto_nhds_zero.mp hmul) (ε / 2) (ENNReal.half_pos hε)).exists
  refine ⟨n, iSup_le fun k => ?_⟩
  have hdecomp : ∫⁻ x in timeSlab n k, f x
      = (∫⁻ x in timeSlab n k, g M x) + ∫⁻ x in timeSlab n k, (f x - g M x) := by
    rw [← lintegral_add_left (hgm M) (fun x => f x - g M x)]
    exact lintegral_congr fun x => (add_tsub_cancel_of_le (hgle M x)).symm
  calc ∫⁻ x in timeSlab n k, f x
      = (∫⁻ x in timeSlab n k, g M x) + ∫⁻ x in timeSlab n k, (f x - g M x) := hdecomp
    _ ≤ (M : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) + ((∫⁻ x, f x) - ∫⁻ x, g M x) := by
        gcongr
        · calc ∫⁻ x in timeSlab n k, g M x
              ≤ ∫⁻ _ in timeSlab n k, (M : ℝ≥0∞) := lintegral_mono fun x => min_le_right _ _
            _ = (M : ℝ≥0∞) * volume (timeSlab n k) := by rw [setLIntegral_const]
            _ = (M : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by rw [volume_timeSlab]
        · calc ∫⁻ x in timeSlab n k, (f x - g M x)
              ≤ ∫⁻ x, (f x - g M x) := setLIntegral_le_lintegral _ _
            _ = (∫⁻ x, f x) - ∫⁻ x, g M x :=
                lintegral_sub (hgm M) (hgfin M) (Eventually.of_forall (hgle M))
    _ ≤ ε / 2 + ε / 2 := add_le_add hn hM
    _ = ε := ENNReal.add_halves ε

end Mesh

section Simple

/-- The mark measure of the time sections of a set, carried by the nonnegative times. -/
noncomputable def sectionDensity (ν : Measure E) (B : Set (ℝ × E)) (x : ℝ) : ℝ≥0∞ :=
  (Set.Ici (0 : ℝ)).indicator (fun y => ν (Prod.mk y ⁻¹' B)) x

theorem measurable_sectionDensity {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    Measurable (sectionDensity ν B) :=
  (measurable_measure_prodMk_left hB).indicator measurableSet_Ici

/-- The reference intensity of a time window of a set, as an integral of its section density. -/
theorem referenceIntensity_inter_time {B : Set (ℝ × E)} (hB : MeasurableSet B) {S : Set ℝ}
    (hS : MeasurableSet S) :
    referenceIntensity ν (B ∩ S ×ˢ Set.univ) = ∫⁻ x in S, sectionDensity ν B x := by
  have hpre : ∀ x : ℝ, ν (Prod.mk x ⁻¹' (B ∩ S ×ˢ Set.univ))
      = S.indicator (fun y => ν (Prod.mk y ⁻¹' B)) x := by
    intro x
    by_cases hx : x ∈ S
    · have hset : Prod.mk x ⁻¹' (B ∩ S ×ˢ Set.univ) = Prod.mk x ⁻¹' B := by
        ext e; simp [hx]
      rw [hset, Set.indicator_of_mem hx]
    · have hset : Prod.mk x ⁻¹' (B ∩ S ×ˢ Set.univ) = (∅ : Set E) := by
        ext e; simp [hx]
      rw [hset, Set.indicator_of_notMem hx, measure_empty]
  rw [referenceIntensity, Measure.prod_apply (hB.inter (hS.prod MeasurableSet.univ))]
  simp_rw [hpre]
  rw [lintegral_indicator hS, Measure.restrict_restrict hS]
  simp only [sectionDensity]
  rw [lintegral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici,
    Set.inter_comm]

theorem lintegral_sectionDensity {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    ∫⁻ x, sectionDensity ν B x = referenceIntensity ν B := by
  rw [← setLIntegral_univ, ← referenceIntensity_inter_time hB MeasurableSet.univ,
    Set.univ_prod_univ, Set.inter_univ]

/-- **The dyadic time slabs of a finite-intensity set eventually carry at most one point.** -/
theorem ae_exists_forall_count_timeSlab_le_one (N : PoissonRandomMeasure.{u, v, w} P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ n : ℕ, ∀ k : ℕ, N.N ω (B ∩ timeSlab n k ×ˢ Set.univ) ≤ 1 := by
  classical
  set C : ℕ → ℕ → Set (ℝ × E) := fun n k => B ∩ timeSlab n k ×ˢ Set.univ with hCdef
  have hCm : ∀ n k, MeasurableSet (C n k) := fun n k =>
    hB.inter ((measurableSet_timeSlab n k).prod MeasurableSet.univ)
  have hCfin : ∀ n k, referenceIntensity ν (C n k) ≠ ⊤ := fun n k =>
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  set R : ℕ → ℕ → ℝ≥0∞ := fun n k => referenceIntensity ν (C n k) with hRdef
  have hsum : ∀ n : ℕ, ∑' k : ℕ, R n k ≤ referenceIntensity ν B := by
    intro n
    have hdisj : Pairwise (Function.onFun Disjoint (C n)) := by
      intro i j hij
      refine Set.disjoint_left.mpr fun p hpi hpj => ?_
      exact Set.disjoint_left.mp (pairwiseDisjoint_timeSlab n hij) hpi.2.1 hpj.2.1
    have hunion : (⋃ k : ℕ, C n k) = B ∩ Set.Ioi (0 : ℝ) ×ˢ Set.univ := by
      rw [hCdef, ← Set.inter_iUnion, ← Set.iUnion_prod_const, iUnion_timeSlab]
    rw [hRdef, ← measure_iUnion hdisj (hCm n), hunion]
    exact measure_mono Set.inter_subset_left
  have hRint : ∀ n k, R n k = ∫⁻ x in timeSlab n k, sectionDensity ν B x := fun n k =>
    referenceIntensity_inter_time hB (measurableSet_timeSlab n k)
  set A : ℕ → Set Ω := fun n => ⋃ k : ℕ, {ω | 2 ≤ N.N ω (C n k)} with hAdef
  have hAle : ∀ n : ℕ, P (A n) ≤ (⨆ k : ℕ, R n k) * referenceIntensity ν B := by
    intro n
    calc P (A n) ≤ ∑' k : ℕ, P {ω | 2 ≤ N.N ω (C n k)} := measure_iUnion_le _
      _ ≤ ∑' k : ℕ, R n k ^ 2 :=
          ENNReal.tsum_le_tsum fun k => measure_two_le_count_le N (hCm n k) (hCfin n k)
      _ ≤ ∑' k : ℕ, (⨆ j : ℕ, R n j) * R n k := by
          refine ENNReal.tsum_le_tsum fun k => ?_
          rw [sq]
          gcongr
          exact le_iSup (R n) k
      _ = (⨆ j : ℕ, R n j) * ∑' k : ℕ, R n k := ENNReal.tsum_mul_left
      _ ≤ (⨆ j : ℕ, R n j) * referenceIntensity ν B := by gcongr; exact hsum n
  have hsmall : ∀ ε : ℝ≥0∞, ε ≠ 0 → ∃ n : ℕ, P (A n) ≤ ε := by
    intro ε hε
    by_cases hR : referenceIntensity ν B = 0
    · exact ⟨0, (hAle 0).trans (by rw [hR, mul_zero]; exact bot_le)⟩
    · have hδ0 : ε / referenceIntensity ν B ≠ 0 := by
        intro h
        rcases ENNReal.div_eq_zero_iff.mp h with h1 | h1
        · exact hε h1
        · exact hfin h1
      obtain ⟨n, hn⟩ := exists_iSup_setLIntegral_timeSlab_le
        (measurable_sectionDensity (ν := ν) hB)
        (by rw [lintegral_sectionDensity hB]; exact hfin) hδ0
      refine ⟨n, (hAle n).trans ?_⟩
      have hsupδ : (⨆ k : ℕ, R n k) ≤ ε / referenceIntensity ν B := by
        refine iSup_le fun k => ?_
        rw [hRint n k]
        exact le_trans
          (le_iSup (fun j : ℕ => ∫⁻ x in timeSlab n j, sectionDensity ν B x) k) hn
      calc (⨆ k : ℕ, R n k) * referenceIntensity ν B
          ≤ (ε / referenceIntensity ν B) * referenceIntensity ν B := by gcongr
        _ = ε := ENNReal.div_mul_cancel hR hfin
  have hzero : P (⋂ n : ℕ, A n) = 0 := by
    by_contra hne
    obtain ⟨c, hc0, hcx⟩ := exists_between (pos_iff_ne_zero.mpr hne)
    obtain ⟨n, hn⟩ := hsmall c hc0.ne'
    exact absurd (le_trans (measure_mono (Set.iInter_subset _ n)) hn) (not_le.mpr hcx)
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ n : ℕ, A n := by
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hzero
  have hint : ∀ᵐ ω ∂P, ∀ n k : ℕ, ∃ m : ℕ, N.N ω (C n k) = m := by
    rw [ae_all_iff]
    intro n
    rw [ae_all_iff]
    intro k
    exact N.integer_valued (hCm n k) (hCfin n k)
  filter_upwards [hae, hint] with ω hω hωint
  simp only [Set.mem_iInter, not_forall] at hω
  obtain ⟨n, hn⟩ := hω
  simp only [hAdef, Set.mem_iUnion, not_exists, Set.mem_setOf_eq] at hn
  refine ⟨n, fun k => ?_⟩
  obtain ⟨m, hm⟩ := hωint n k
  have hnk := hn k
  rw [hm] at hnk ⊢
  have hm2 : m < 2 := by
    by_contra hc
    exact hnk (by exact_mod_cast Nat.le_of_not_lt hc)
  exact_mod_cast Nat.lt_succ_iff.mp hm2

/-- **A Poisson random measure of finite intensity is time-simple:** almost surely no two of its
points share a time and every point is simple. -/
theorem ae_count_time_singleton_le_one (N : PoissonRandomMeasure.{u, v, w} P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, N.N ω (B ∩ {s} ×ˢ Set.univ) ≤ 1 := by
  filter_upwards [ae_exists_forall_count_timeSlab_le_one N hB hfin,
    ae_count_Iic_zero_eq_zero N hB] with ω hω h0 s
  obtain ⟨n, hn⟩ := hω
  rcases le_or_gt s 0 with hs | hs
  · calc N.N ω (B ∩ {s} ×ˢ Set.univ)
        ≤ N.N ω (B ∩ Set.Iic (0 : ℝ) ×ˢ Set.univ) :=
          measure_mono (Set.inter_subset_inter_right _
            (Set.prod_mono (Set.singleton_subset_iff.mpr (Set.mem_Iic.mpr hs)) le_rfl))
      _ = 0 := h0
      _ ≤ 1 := bot_le
  · have hmem : s ∈ ⋃ k : ℕ, timeSlab n k := by
      rw [iUnion_timeSlab]
      exact hs
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmem
    refine le_trans (measure_mono ?_) (hn k)
    exact Set.inter_subset_inter_right _
      (Set.prod_mono (Set.singleton_subset_iff.mpr hk) le_rfl)

end Simple

end LevyStochCalc.Poisson
