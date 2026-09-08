/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Simplicity
import LevyStochCalc.Poisson.JumpSum

/-!
# The jump chain rule for a Poisson random measure

A product over a finite set whose factors are ordered by a key telescopes: the product minus one
is the sum, over the factors, of the product of the earlier ones times the increment of that
factor. On a set of finite reference intensity a Poisson random measure is a finite sum of unit
masses at distinct times, so the exponential of an integral against it obeys that telescoping,
which is the chain rule the exponential family needs.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

section Telescope

variable {α : Type*} [DecidableEq α] {K : Type*} [LinearOrder K] {M : Type*} [CommRing M]

open scoped Classical in
/-- **A product over a key-ordered finite set telescopes.** -/
theorem prod_sub_one_eq_sum (key : α → K) (z : α → M) :
    ∀ s : Finset α, Set.InjOn key (s : Set α) →
      (∏ p ∈ s, z p) - 1
        = ∑ p ∈ s, (∏ q ∈ s.filter (fun q => key q < key p), z q) * (z p - 1) := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hinj
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp
    obtain ⟨p₀, hp₀, hmax⟩ := s.exists_max_image key hne
    have hss' : s.erase p₀ ⊂ s := Finset.erase_ssubset hp₀
    have hinj' : Set.InjOn key ((s.erase p₀ : Finset α) : Set α) := by
      refine hinj.mono ?_
      intro x hx
      exact Finset.mem_of_mem_erase hx
    have hlt : ∀ p ∈ s.erase p₀, key p < key p₀ := by
      intro p hp
      have hps : p ∈ s := Finset.mem_of_mem_erase hp
      have hne' : p ≠ p₀ := Finset.ne_of_mem_erase hp
      refine lt_of_le_of_ne (hmax p hps) fun h => hne' (hinj hps hp₀ h)
    have hfilter0 : s.filter (fun q => key q < key p₀) = s.erase p₀ := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hq, hqlt⟩
        exact ⟨fun h => absurd (h ▸ hqlt) (lt_irrefl _), hq⟩
      · rintro ⟨hq1, hq2⟩
        exact ⟨hq2, hlt q (Finset.mem_erase.mpr ⟨hq1, hq2⟩)⟩
    have hfilter : ∀ p ∈ s.erase p₀,
        s.filter (fun q => key q < key p) = (s.erase p₀).filter (fun q => key q < key p) := by
      intro p hp
      ext q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hq, hqlt⟩
        refine ⟨⟨?_, hq⟩, hqlt⟩
        rintro rfl
        exact absurd hqlt (not_lt.mpr (hlt p hp).le)
      · rintro ⟨⟨-, hq⟩, hqlt⟩
        exact ⟨hq, hqlt⟩
    have hsplit : (∑ p ∈ s, (∏ q ∈ s.filter (fun q => key q < key p), z q) * (z p - 1))
        = (∑ p ∈ s.erase p₀,
            (∏ q ∈ (s.erase p₀).filter (fun q => key q < key p), z q) * (z p - 1))
          + (∏ q ∈ s.erase p₀, z q) * (z p₀ - 1) := by
      rw [← Finset.sum_erase_add s _ hp₀, hfilter0]
      congr 1
      exact Finset.sum_congr rfl fun p hp => by rw [hfilter p hp]
    rw [hsplit, ← ih (s.erase p₀) hss' hinj', ← Finset.prod_erase_mul s z hp₀]
    ring

end Telescope

section Pathwise

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The Bochner integral against a finite sum of Dirac masses, in a normed space. -/
theorem integral_of_eq_sum_dirac' {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {μ : Measure α} [IsFiniteMeasure μ]
    {s : Finset α} (hμ : μ = ∑ p ∈ s, μ {p} • Measure.dirac p) (g : α → F) :
    ∫ a, g a ∂μ = ∑ p ∈ s, (μ {p}).toReal • g p := by
  conv_lhs => rw [hμ]
  rw [integral_finsetSum_measure fun p _ =>
    (integrable_dirac (by simp)).smul_measure (measure_ne_top μ _)]
  exact Finset.sum_congr rfl fun p _ => by rw [integral_smul_measure, integral_dirac]

/-- The integral of `h` against the points of `B` in `(0, t]`. -/
noncomputable def windowSum (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (h : ℝ × E → ℝ)
    (t : ℝ) (ω : Ω) : ℝ :=
  ∫ p in B ∩ Set.Ioc (0 : ℝ) t ×ˢ Set.univ, h p ∂(N.N ω)

/-- The integral of `h` against the points of `B` strictly before `t`. -/
noncomputable def windowSumStrict (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E))
    (h : ℝ × E → ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  ∫ p in B ∩ Set.Ioo (0 : ℝ) t ×ˢ Set.univ, h p ∂(N.N ω)

omit [MeasurableSpace.CountablyGenerated E] in
open scoped Classical in
/-- **The jump chain rule on a time window, at a sample point.** For a window `B ∩ J ×ˢ univ`
with `J ⊆ (0, ∞)` an initial segment of the positive reals, at a sample point where the random
measure restricted to the window is a finite sum of point masses, integer valued, with no two
points sharing a time, the exponential of the integral of `h` over the window telescopes over
the points. -/
theorem exp_windowSum_sub_one_of_repr (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (h : ℝ × E → ℝ) {J : Set ℝ} (hJm : MeasurableSet J)
    (hJ0 : J ⊆ Set.Ioi 0) (hJ : ∀ u ∈ J, Set.Ioo (0 : ℝ) u ⊆ J) (ω : Ω)
    (hsrepex : ∃ s : Finset (ℝ × E), (N.N ω).restrict (B ∩ J ×ˢ Set.univ)
      = ∑ p ∈ s, ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)) {p} • Measure.dirac p)
    (hn : ∃ k : ℕ, N.N ω (B ∩ J ×ˢ Set.univ) = k)
    (hIV : Probability.IsIntegerValued ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)))
    (hsimple : ∀ t : ℝ, N.N ω (B ∩ ({t} : Set ℝ) ×ˢ Set.univ) ≤ 1) :
    Complex.exp (Complex.I * ((∫ p in B ∩ J ×ˢ Set.univ, h p ∂(N.N ω) : ℝ) : ℂ)) - 1
      = ∫ p in B ∩ J ×ˢ Set.univ,
          Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by
  have hRm : MeasurableSet (B ∩ J ×ˢ Set.univ) := hB.inter (hJm.prod MeasurableSet.univ)
  obtain ⟨s, hsrep⟩ := hsrepex
  haveI : IsFiniteMeasure ((N.N ω).restrict (B ∩ J ×ˢ Set.univ)) := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, hk]
    exact ENNReal.natCast_lt_top k
  set R : Set (ℝ × E) := B ∩ J ×ˢ Set.univ with hRdef
  set m : ℝ × E → ℝ≥0∞ := fun p => ((N.N ω).restrict R) {p} with hmdef
  have hmapp : ∀ p : ℝ × E, m p = (N.N ω) ({p} ∩ R) := fun p => by
    rw [hmdef]
    exact Measure.restrict_apply (measurableSet_singleton p)
  have hmself : ∀ p : ℝ × E, m p ≤ (N.N ω) {p} := fun p =>
    Measure.le_iff'.mp Measure.restrict_le_self {p}
  have hmle : ∀ p : ℝ × E, m p ≤ 1 := by
    intro p
    calc m p = (N.N ω) ({p} ∩ R) := hmapp p
      _ ≤ (N.N ω) (B ∩ ({p.1} : Set ℝ) ×ˢ Set.univ) := by
          refine measure_mono fun q hq => ?_
          obtain ⟨hq1, hq2⟩ := hq
          rw [Set.mem_singleton_iff] at hq1
          subst hq1
          exact ⟨hq2.1, ⟨rfl, Set.mem_univ _⟩⟩
      _ ≤ 1 := hsimple p.1
  set s₁ : Finset (ℝ × E) := s.filter (fun p => m p ≠ 0) with hs₁def
  have hs₁sub : s₁ ⊆ s := Finset.filter_subset _ _
  have hm1 : ∀ p ∈ s₁, m p = 1 := by
    intro p hp
    have hne : m p ≠ 0 := (Finset.mem_filter.mp hp).2
    obtain ⟨k, hk⟩ := hIV ({p} : Set (ℝ × E)) (measurableSet_singleton p)
    have hkm : m p = (k : ℝ≥0∞) := hk
    rcases Nat.lt_or_ge k 1 with hk1 | hk1
    · exact absurd (by rw [hkm, Nat.lt_one_iff.mp hk1]; simp) hne
    · rcases Nat.lt_or_ge k 2 with hk2 | hk2
      · have : k = 1 := by omega
        rw [hkm, this]
        norm_num
      · exfalso
        have : (2 : ℝ≥0∞) ≤ m p := by
          rw [hkm]
          exact_mod_cast hk2
        exact absurd (this.trans (hmle p)) (by norm_num)
  have hmR : ∀ p ∈ s₁, p ∈ R := by
    intro p hp
    by_contra hpR
    have : ({p} : Set (ℝ × E)) ∩ R = ∅ := by
      ext q
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false,
        not_and]
      rintro rfl
      exact hpR
    have hz : m p = 0 := by rw [hmapp p, this, measure_empty]
    exact (Finset.mem_filter.mp hp).2 hz
  have hinj : Set.InjOn Prod.fst (s₁ : Set (ℝ × E)) := by
    intro p hp q hq hpq
    by_contra hne
    have hp1 : m p = 1 := hm1 p hp
    have hq1 : m q = 1 := hm1 q hq
    have hpR : p ∈ R := hmR p hp
    have hqR : q ∈ R := hmR q hq
    have hdisj : Disjoint ({p} : Set (ℝ × E)) {q} := by
      simp only [Set.disjoint_singleton]
      exact hne
    have hsub : ({p} : Set (ℝ × E)) ∪ {q} ⊆ B ∩ ({p.1} : Set ℝ) ×ˢ Set.univ := by
      rintro x (hx | hx) <;> rw [Set.mem_singleton_iff] at hx <;> subst hx
      · exact ⟨hpR.1, ⟨rfl, Set.mem_univ _⟩⟩
      · exact ⟨hqR.1, ⟨hpq.symm, Set.mem_univ _⟩⟩
    have h2 : (2 : ℝ≥0∞) ≤ (N.N ω) (B ∩ ({p.1} : Set ℝ) ×ˢ Set.univ) := by
      calc (2 : ℝ≥0∞) = m p + m q := by rw [hp1, hq1]; norm_num
        _ ≤ (N.N ω) {p} + (N.N ω) {q} := add_le_add (hmself p) (hmself q)
        _ = (N.N ω) (({p} : Set (ℝ × E)) ∪ {q}) :=
            (measure_union hdisj (measurableSet_singleton q)).symm
        _ ≤ _ := measure_mono hsub
    exact absurd (h2.trans (hsimple p.1)) (by norm_num)
  -- the window sums as finite sums over the atoms
  have hsumR : ∀ (S : Set (ℝ × E)), MeasurableSet S → S ⊆ R →
      ∫ p in S, h p ∂(N.N ω) = ∑ p ∈ s₁, S.indicator h p := by
    intro S hSm hSR
    have hrw : ∫ p in S, h p ∂(N.N ω) = ∫ p, S.indicator h p ∂((N.N ω).restrict R) := by
      rw [integral_indicator hSm, Measure.restrict_restrict hSm,
        Set.inter_eq_self_of_subset_left hSR]
    rw [hrw, integral_of_eq_sum_dirac' hsrep]
    have hdrop : ∑ p ∈ s, (m p).toReal • S.indicator h p
        = ∑ p ∈ s₁, (m p).toReal • S.indicator h p := by
      refine (Finset.sum_subset hs₁sub ?_).symm
      intro x hx hxn
      have hz : m x = 0 := by
        by_contra hc
        exact hxn (Finset.mem_filter.mpr ⟨hx, hc⟩)
      rw [hz]
      simp
    rw [hdrop]
    exact Finset.sum_congr rfl fun p hp => by rw [hm1 p hp]; simp
  have hwindow : (∫ p in R, h p ∂(N.N ω)) = ∑ p ∈ s₁, h p := by
    rw [hsumR R hRm le_rfl]
    exact Finset.sum_congr rfl fun p hp => Set.indicator_of_mem (hmR p hp) h
  have hstrict : ∀ p ∈ s₁, windowSumStrict N B h p.1 ω
      = ∑ q ∈ s₁.filter (fun q => q.1 < p.1), h q := by
    intro p hp
    have hpR : p ∈ R := hmR p hp
    have hJp : Set.Ioo (0 : ℝ) p.1 ⊆ J := hJ p.1 hpR.2.1
    have hSm : MeasurableSet (B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ) :=
      hB.inter (measurableSet_Ioo.prod MeasurableSet.univ)
    have hSR : B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ ⊆ R := by
      intro q hq
      exact ⟨hq.1, ⟨hJp hq.2.1, Set.mem_univ _⟩⟩
    rw [windowSumStrict, hsumR _ hSm hSR]
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun q hq => ?_
    have hqR : q ∈ R := hmR q hq
    by_cases hlt : q.1 < p.1
    · have hmem : q ∈ B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ :=
        ⟨hqR.1, ⟨⟨hJ0 hqR.2.1, hlt⟩, Set.mem_univ _⟩⟩
      rw [if_pos hlt, Set.indicator_of_mem hmem]
    · have hnmem : q ∉ B ∩ Set.Ioo (0 : ℝ) p.1 ×ˢ Set.univ := fun hmem => hlt hmem.2.1.2
      rw [if_neg hlt, Set.indicator_of_notMem hnmem]
  -- the right-hand integral as a finite sum over the atoms
  have hRHS : ∫ p in R, Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
        * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω)
      = ∑ p ∈ s₁, Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
        * (Complex.exp (Complex.I * (h p : ℂ)) - 1) := by
    rw [show (N.N ω).restrict R = (N.N ω).restrict R from rfl,
      show ∫ p in R, Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
          * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω)
        = ∫ p, Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
          * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂((N.N ω).restrict R) from rfl,
      integral_of_eq_sum_dirac' hsrep]
    have hdrop : ∑ p ∈ s, (m p).toReal • (Complex.exp (Complex.I *
          (windowSumStrict N B h p.1 ω : ℂ)) * (Complex.exp (Complex.I * (h p : ℂ)) - 1))
        = ∑ p ∈ s₁, (m p).toReal • (Complex.exp (Complex.I *
          (windowSumStrict N B h p.1 ω : ℂ)) * (Complex.exp (Complex.I * (h p : ℂ)) - 1)) := by
      refine (Finset.sum_subset hs₁sub ?_).symm
      intro x hx hxn
      have hz : m x = 0 := by
        by_contra hc
        exact hxn (Finset.mem_filter.mpr ⟨hx, hc⟩)
      rw [hz]
      simp
    rw [hdrop]
    exact Finset.sum_congr rfl fun p hp => by rw [hm1 p hp]; simp
  rw [hRHS, hwindow]
  have hprod := prod_sub_one_eq_sum (M := ℂ) Prod.fst
    (fun p => Complex.exp (Complex.I * (h p : ℂ))) s₁ hinj
  rw [← Complex.exp_sum] at hprod
  have hcast : ∀ t : Finset (ℝ × E),
      ∑ p ∈ t, Complex.I * (h p : ℂ) = Complex.I * ((∑ p ∈ t, h p : ℝ) : ℂ) := by
    intro t
    rw [← Finset.mul_sum]
    norm_cast
  rw [hcast] at hprod
  rw [hprod]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [← Complex.exp_sum, hcast, hstrict p hp]

open scoped Classical in
/-- **The jump chain rule for a Poisson random measure of finite intensity.** -/
theorem ae_exp_windowSum_sub_one (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (h : ℝ × E → ℝ) (T : ℝ) :
    ∀ᵐ ω ∂P, Complex.exp (Complex.I * (windowSum N B h T ω : ℂ)) - 1
      = ∫ p in B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
          Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
            * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by
  have hRm : MeasurableSet (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) :=
    hB.inter (measurableSet_Ioc.prod MeasurableSet.univ)
  have hRfin : referenceIntensity ν (B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ) ≠ ⊤ :=
    ne_top_of_le_ne_top hfin (measure_mono Set.inter_subset_left)
  filter_upwards [ae_exists_eq_sum_dirac N hRm hRfin, N.integer_valued hRm hRfin,
    ae_isIntegerValued_restrict N hRm hRfin, ae_count_time_singleton_le_one N hB hfin]
    with ω hsrepex hn hIV hsimple
  exact exp_windowSum_sub_one_of_repr N hB h measurableSet_Ioc (fun x hx => hx.1)
    (fun u hu x hx => ⟨hx.1, hx.2.le.trans hu.2⟩) ω hsrepex hn hIV hsimple

/-- Restricting a finite sum of point masses to a measurable subset of its window. -/
theorem restrict_eq_sum_dirac_of_subset {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] {μ : Measure α} {B R : Set α} (hRm : MeasurableSet R)
    (hRB : R ⊆ B) {s : Finset α}
    (hs : μ.restrict B = ∑ p ∈ s, (μ.restrict B) {p} • Measure.dirac p) :
    μ.restrict R = ∑ p ∈ s, (μ.restrict R) {p} • Measure.dirac p := by
  classical
  ext A hA
  have h1 : (μ.restrict R) A = (μ.restrict B) (A ∩ R) := by
    rw [Measure.restrict_apply hA, Measure.restrict_apply (hA.inter hRm),
      Set.inter_eq_left.mpr (Set.inter_subset_right.trans hRB)]
  rw [h1, hs, Measure.coe_finset_sum, Finset.sum_apply, Measure.coe_finset_sum,
    Finset.sum_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Measure.smul_apply, Measure.smul_apply, Measure.dirac_apply' _ (hA.inter hRm),
    Measure.dirac_apply' _ hA, smul_eq_mul, smul_eq_mul,
    Measure.restrict_apply (measurableSet_singleton p),
    Measure.restrict_apply (measurableSet_singleton p)]
  by_cases hpR : p ∈ R
  · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr (hRB hpR)),
      Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hpR)]
    by_cases hpA : p ∈ A
    · simp [hpA, hpR]
    · simp [hpA]
  · rw [Set.indicator_of_notMem (fun hm => hpR hm.2), Set.singleton_inter_eq_empty.mpr hpR,
      measure_empty, mul_zero, zero_mul]

/-- **The jump chain rule at all times simultaneously.** Outside one null set, at every time `T`
the exponential of the window sum up to `T`, and that of the strict-past window sum, telescope
over the points of the window before `T`. -/
theorem ae_forall_exp_windowSum_sub_one (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (h : ℝ × E → ℝ) :
    ∀ᵐ ω ∂P, ∀ T : ℝ,
      (Complex.exp (Complex.I * (windowSum N B h T ω : ℂ)) - 1
        = ∫ p in B ∩ Set.Ioc (0 : ℝ) T ×ˢ Set.univ,
            Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω))
      ∧ (Complex.exp (Complex.I * (windowSumStrict N B h T ω : ℂ)) - 1
        = ∫ p in B ∩ Set.Ioo (0 : ℝ) T ×ˢ Set.univ,
            Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω)) := by
  filter_upwards [ae_exists_eq_sum_dirac N hB hfin, ae_isIntegerValued_restrict N hB hfin,
    ae_count_time_singleton_le_one N hB hfin] with ω hsrepex hIV hsimple
  obtain ⟨s, hs⟩ := hsrepex
  have key : ∀ (J : Set ℝ), MeasurableSet J → J ⊆ Set.Ioi 0 →
      (∀ u ∈ J, Set.Ioo (0 : ℝ) u ⊆ J) →
      Complex.exp (Complex.I * ((∫ p in B ∩ J ×ˢ Set.univ, h p ∂(N.N ω) : ℝ) : ℂ)) - 1
        = ∫ p in B ∩ J ×ˢ Set.univ,
            Complex.exp (Complex.I * (windowSumStrict N B h p.1 ω : ℂ))
              * (Complex.exp (Complex.I * (h p : ℂ)) - 1) ∂(N.N ω) := by
    intro J hJm hJ0 hJ
    have hRm : MeasurableSet (B ∩ J ×ˢ Set.univ) := hB.inter (hJm.prod MeasurableSet.univ)
    have hRB : B ∩ J ×ˢ Set.univ ⊆ B := Set.inter_subset_left
    refine exp_windowSum_sub_one_of_repr N hB h hJm hJ0 hJ ω
      ⟨s, restrict_eq_sum_dirac_of_subset hRm hRB hs⟩ ?_ ?_ hsimple
    · obtain ⟨k, hk⟩ := hIV _ hRm
      refine ⟨k, ?_⟩
      rw [Measure.restrict_apply hRm, Set.inter_eq_left.mpr hRB] at hk
      exact hk
    · intro A hA
      obtain ⟨k, hk⟩ := hIV (A ∩ (B ∩ J ×ˢ Set.univ)) (hA.inter hRm)
      refine ⟨k, ?_⟩
      rw [Measure.restrict_apply (hA.inter hRm),
        Set.inter_eq_left.mpr (Set.inter_subset_right.trans hRB)] at hk
      rw [Measure.restrict_apply hA]
      exact hk
  intro T
  exact ⟨key _ measurableSet_Ioc (fun x hx => hx.1) (fun u hu x hx => ⟨hx.1, hx.2.le.trans hu.2⟩),
    key _ measurableSet_Ioo (fun x hx => hx.1) (fun u hu x hx => ⟨hx.1, hx.2.trans hu.2⟩)⟩


end Pathwise

end LevyStochCalc.Poisson
