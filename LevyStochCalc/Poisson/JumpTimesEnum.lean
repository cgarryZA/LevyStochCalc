/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.JumpTimes
import LevyStochCalc.Poisson.Simplicity

/-!
# Arrival times as the atom times of a Poisson random measure

The counting process `arrivalCount N A` splits at a positive time into the mass strictly before
that time and the mass carried by the time itself, so on a window on which the restricted measure
is integer-valued a time in `(0, T]` carries mass in the mark set `A` exactly when it is one of
the arrival times `jumpTime N A i`. Such a time therefore lies among the times of any finite atom
set of the restricted measure. Every arrival time of positive index is strictly positive, the
arrival times of a time-simple measure strictly increase, and the chain of arrival times passes
any horizon at which the count is finite.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section Singleton

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- The count over `(0, u]` splits into the count over `(0, u)` and the mass carried by `u`. -/
theorem arrivalCount_eq_add_count_singleton (hA : MeasurableSet A) {u : ℝ} (hu : 0 < u) (ω : Ω) :
    arrivalCount N A u ω
      = N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) + N.N ω (({u} : Set ℝ) ×ˢ A) := by
  have hdisj : Disjoint (Set.Ioo (0 : ℝ) u ×ˢ A) (({u} : Set ℝ) ×ˢ A) := by
    rw [Set.disjoint_left]
    rintro ⟨x, e⟩ hmem hmem'
    have h1 : x < u := (Set.mem_prod.mp hmem).1.2
    have h2 : x = u := (Set.mem_prod.mp hmem').1
    linarith
  have hunion : Set.Ioc (0 : ℝ) u ×ˢ A
      = (Set.Ioo (0 : ℝ) u ×ˢ A) ∪ (({u} : Set ℝ) ×ˢ A) := by
    rw [← Set.union_prod]
    congr 1
    ext x
    simp only [Set.mem_Ioc, Set.mem_union, Set.mem_Ioo, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      rcases lt_or_eq_of_le h2 with h | h
      · exact Or.inl ⟨h1, h⟩
      · exact Or.inr h
    · rintro (⟨h1, h2⟩ | h)
      · exact ⟨h1, h2.le⟩
      · subst h
        exact ⟨hu, le_rfl⟩
  rw [arrivalCount, hunion, measure_union hdisj ((measurableSet_singleton u).prod hA)]

/-- The count at a time strictly below `u` together with the mass carried by `u` is at most the
count at `u`. -/
theorem arrivalCount_add_count_singleton_le (hA : MeasurableSet A) {t u : ℝ} (hu : 0 < u)
    (htu : t < u) (ω : Ω) :
    arrivalCount N A t ω + N.N ω (({u} : Set ℝ) ×ˢ A) ≤ arrivalCount N A u ω := by
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) t ×ˢ A) (({u} : Set ℝ) ×ˢ A) := by
    rw [Set.disjoint_left]
    rintro ⟨x, e⟩ hmem hmem'
    have h1 : x ≤ t := (Set.mem_prod.mp hmem).1.2
    have h2 : x = u := (Set.mem_prod.mp hmem').1
    linarith
  have hsub : (Set.Ioc (0 : ℝ) t ×ˢ A) ∪ (({u} : Set ℝ) ×ˢ A) ⊆ Set.Ioc (0 : ℝ) u ×ˢ A := by
    refine Set.union_subset (Set.prod_mono (Set.Ioc_subset_Ioc_right htu.le) le_rfl) ?_
    exact Set.prod_mono (Set.singleton_subset_iff.mpr ⟨hu, le_rfl⟩) le_rfl
  rw [arrivalCount, arrivalCount,
    ← measure_union hdisj ((measurableSet_singleton u).prod hA)]
  exact measure_mono hsub

/-- A bound valid for the counts at all times strictly below `u` bounds the mass on `(0, u)`. -/
theorem count_Ioo_le_of_forall_lt {u : ℝ} (hu : 0 < u) {ω : Ω}
    {M : ℝ≥0∞} (hM : ∀ t : ℝ, t < u → arrivalCount N A t ω ≤ M) :
    N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) ≤ M := by
  obtain ⟨r, hrmono, hrmem, hrtend⟩ := exists_seq_strictMono_tendsto' hu
  have hmono : Monotone fun n : ℕ => Set.Ioc (0 : ℝ) (r n) ×ˢ A := fun m n hmn =>
    Set.prod_mono (Set.Ioc_subset_Ioc_right (hrmono.monotone hmn)) le_rfl
  have hsub : Set.Ioo (0 : ℝ) u ×ˢ A ⊆ ⋃ n : ℕ, Set.Ioc (0 : ℝ) (r n) ×ˢ A := by
    rintro ⟨x, e⟩ hmem
    obtain ⟨hx, he⟩ := Set.mem_prod.mp hmem
    obtain ⟨n, hn⟩ := (hrtend.eventually_const_lt hx.2).exists
    exact Set.mem_iUnion.mpr ⟨n, ⟨⟨hx.1, hn.le⟩, he⟩⟩
  calc N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A)
      ≤ N.N ω (⋃ n : ℕ, Set.Ioc (0 : ℝ) (r n) ×ˢ A) := measure_mono hsub
    _ = ⨆ n : ℕ, N.N ω (Set.Ioc (0 : ℝ) (r n) ×ˢ A) := hmono.measure_iUnion
    _ ≤ M := iSup_le fun n => hM (r n) (hrmem n).2

end Singleton

section IntegerValued

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- On a window carrying integer mass the count at each earlier time is a natural number. -/
theorem exists_nat_arrivalCount (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)))
    {t : ℝ} (ht : t ≤ T) : ∃ n : ℕ, arrivalCount N A t ω = n := by
  obtain ⟨n, hn⟩ := hint (Set.Ioc (0 : ℝ) t ×ˢ A) (measurableSet_Ioc.prod hA)
  rw [Measure.restrict_apply (measurableSet_Ioc.prod hA),
    Set.inter_eq_self_of_subset_left
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)] at hn
  exact ⟨n, hn⟩

/-- On a window carrying integer mass every time of the window carries a natural mass. -/
theorem exists_nat_count_singleton (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)))
    {u : ℝ} (hu : 0 < u) (huT : u ≤ T) : ∃ n : ℕ, N.N ω (({u} : Set ℝ) ×ˢ A) = n := by
  obtain ⟨n, hn⟩ := hint ((({u} : Set ℝ) ×ˢ A)) ((measurableSet_singleton u).prod hA)
  rw [Measure.restrict_apply ((measurableSet_singleton u).prod hA),
    Set.inter_eq_self_of_subset_left
      (Set.prod_mono (Set.singleton_subset_iff.mpr (Set.mem_Ioc.mpr ⟨hu, huT⟩)) le_rfl)] at hn
  exact ⟨n, hn⟩

/-- On a window carrying integer mass the count at each earlier time is finite. -/
theorem arrivalCount_ne_top_of_isIntegerValued (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)))
    {t : ℝ} (ht : t ≤ T) : arrivalCount N A t ω ≠ ⊤ := by
  obtain ⟨n, hn⟩ := exists_nat_arrivalCount N A hA hint ht
  rw [hn]
  exact ENNReal.natCast_ne_top n

end IntegerValued

section Positivity

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- Arrival times of positive index are strictly positive. -/
theorem coe_zero_lt_jumpTime (hA : MeasurableSet A) {i : ℕ} (hi : i ≠ 0) {ω : Ω}
    (hfin : arrivalCount N A 1 ω ≠ ⊤) : ((0 : ℝ) : WithTop ℝ) < jumpTime N A i ω := by
  refine lt_of_le_of_ne (coe_zero_le_jumpTime N A i ω) fun hcon => ?_
  have hfin' : arrivalCount N A ((0 : ℝ) + 1) ω ≠ ⊤ := by simpa using hfin
  have h := (jumpTime_le_iff N A hA (le_refl (0 : ℝ)) hfin').mp (le_of_eq hcon.symm)
  rw [arrivalCount_of_nonpos N A (le_refl (0 : ℝ)) ω] at h
  exact hi (by exact_mod_cast le_antisymm h zero_le)

end Positivity

section AtomTimes

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- Before the `i`-th arrival time of a window carrying integer mass the count is at most
`i - 1`. -/
theorem arrivalCount_le_of_jumpTime_eq (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    {i : ℕ} {u : ℝ} (hiu : jumpTime N A i ω = (u : WithTop ℝ)) (huT : u ≤ T) {t : ℝ}
    (htu : t < u) : arrivalCount N A t ω ≤ ((i - 1 : ℕ) : ℝ≥0∞) := by
  rcases le_or_gt t 0 with ht0 | ht0
  · rw [arrivalCount_of_nonpos N A ht0 ω]
    exact zero_le
  · by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := exists_nat_arrivalCount N A hA hint (show t ≤ T + 1 by linarith)
    rw [hn] at hcon
    have hin : i ≤ n := by
      have hlt : i - 1 < n := by exact_mod_cast hcon
      omega
    have hge : (i : ℝ≥0∞) ≤ arrivalCount N A t ω := by
      rw [hn]
      exact_mod_cast hin
    have hlt : jumpTime N A i ω < (u : WithTop ℝ) :=
      (jumpTime_lt_iff N A i u ω).mpr ⟨t, ht0.le, htu, hge⟩
    rw [hiu] at hlt
    exact lt_irrefl _ hlt

/-- The mass strictly before the `i`-th arrival time of a window carrying integer mass is at most
`i - 1`. -/
theorem count_Ioo_le_of_jumpTime_eq (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    {i : ℕ} {u : ℝ} (hu : 0 < u) (hiu : jumpTime N A i ω = (u : WithTop ℝ)) (huT : u ≤ T) :
    N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) ≤ ((i - 1 : ℕ) : ℝ≥0∞) :=
  count_Ioo_le_of_forall_lt N A hu fun _ htu =>
    arrivalCount_le_of_jumpTime_eq N A hA hint hiu huT htu

/-- **The arrival times are the atom times.** On a window carrying integer mass the arrival times
in `(0, T]` are exactly the times of `(0, T]` carrying mass in the mark set. -/
theorem setOf_jumpTime_eq_setOf_count_singleton_ne_zero (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A))) :
    {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T}
      = {u : ℝ | (0 < u ∧ u ≤ T) ∧ N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0} := by
  ext u
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨i, hiu, hu0, huT⟩
    refine ⟨⟨hu0, huT⟩, fun hzero => ?_⟩
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [jumpTime_zero] at hiu
      have h0 : (0 : ℝ) = u := by exact_mod_cast hiu
      linarith
    have hfinu : arrivalCount N A (u + 1) ω ≠ ⊤ :=
      arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    have hle : (i : ℝ≥0∞) ≤ arrivalCount N A u ω :=
      (jumpTime_le_iff N A hA hu0.le hfinu).mp (le_of_eq hiu)
    have hIoo := count_Ioo_le_of_jumpTime_eq N A hA hint hu0 hiu huT
    have hdec := arrivalCount_eq_add_count_singleton N A hA hu0 ω
    rw [hzero, add_zero] at hdec
    have hcontr : (i : ℝ≥0∞) ≤ ((i - 1 : ℕ) : ℝ≥0∞) := hle.trans (hdec.trans_le hIoo)
    have hnat : i ≤ i - 1 := by exact_mod_cast hcontr
    omega
  · rintro ⟨⟨hu0, huT⟩, hne⟩
    obtain ⟨n, hn⟩ := exists_nat_arrivalCount N A hA hint (show u ≤ T + 1 by linarith)
    have hfinu : arrivalCount N A (u + 1) ω ≠ ⊤ :=
      arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    refine ⟨n, le_antisymm ((jumpTime_le_iff N A hA hu0.le hfinu).mpr (le_of_eq hn.symm)) ?_,
      hu0, huT⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨t, ht0, htu, hcount⟩ := (jumpTime_lt_iff N A n u ω).mp hcon
    have hct : arrivalCount N A t ω ≠ ⊤ :=
      arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    have hstrict : arrivalCount N A t ω < arrivalCount N A u ω :=
      lt_of_lt_of_le (ENNReal.lt_add_right hct hne)
        (arrivalCount_add_count_singleton_le N A hA hu0 htu ω)
    rw [hn] at hstrict
    exact absurd hcount (not_le.mpr hstrict)

/-- **The arrival times of a time-simple measure strictly increase.** -/
theorem jumpTime_lt_jumpTime_succ (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    (hint : Probability.IsIntegerValued ((N.N ω).restrict (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A)))
    (hsimple : ∀ u : ℝ, 0 < u → u ≤ T → N.N ω (({u} : Set ℝ) ×ˢ A) ≤ 1) {i : ℕ}
    (hi : jumpTime N A (i + 1) ω ≤ (T : WithTop ℝ)) :
    jumpTime N A i ω < jumpTime N A (i + 1) ω := by
  obtain ⟨u, hu⟩ :=
    WithTop.ne_top_iff_exists.mp (lt_of_le_of_lt hi (WithTop.coe_lt_top T)).ne
  have huT : u ≤ T := by
    have hcast : ((u : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) := by rw [hu]; exact hi
    exact_mod_cast hcast
  have hT0 : 0 ≤ T := by
    have hcast : ((0 : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) :=
      (coe_zero_le_jumpTime N A (i + 1) ω).trans hi
    exact_mod_cast hcast
  have hfin1 : arrivalCount N A 1 ω ≠ ⊤ :=
    arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
  have hu0 : 0 < u := by
    have hpos := coe_zero_lt_jumpTime N A hA (Nat.succ_ne_zero i) hfin1
    rw [← hu] at hpos
    exact_mod_cast hpos
  refine lt_of_le_of_ne (jumpTime_mono N A (Nat.le_succ i) ω) fun heq => ?_
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · rw [jumpTime_zero, ← hu] at heq
    have h0 : (0 : ℝ) = u := by exact_mod_cast heq
    linarith
  · have hiu : jumpTime N A i ω = ((u : ℝ) : WithTop ℝ) := by rw [heq, ← hu]
    have hIoo := count_Ioo_le_of_jumpTime_eq N A hA hint hu0 hiu huT
    have hdec := arrivalCount_eq_add_count_singleton N A hA hu0 ω
    have hsum : ((i - 1 : ℕ) : ℝ≥0∞) + 1 = (i : ℝ≥0∞) := by
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp
    have hcu : arrivalCount N A u ω ≤ (i : ℝ≥0∞) := by
      rw [hdec]
      calc N.N ω (Set.Ioo (0 : ℝ) u ×ˢ A) + N.N ω (({u} : Set ℝ) ×ˢ A)
          ≤ ((i - 1 : ℕ) : ℝ≥0∞) + 1 := add_le_add hIoo (hsimple u hu0 huT)
        _ = (i : ℝ≥0∞) := hsum
    have hfinu : arrivalCount N A (u + 1) ω ≠ ⊤ :=
      arrivalCount_ne_top_of_isIntegerValued N A hA hint (by linarith)
    have hge : ((i + 1 : ℕ) : ℝ≥0∞) ≤ arrivalCount N A u ω :=
      (jumpTime_le_iff N A hA hu0.le hfinu).mp (le_of_eq hu.symm)
    have hnat : i + 1 ≤ i := by exact_mod_cast hge.trans hcu
    omega

end AtomTimes

section Chain

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- **The chain of arrival times passes any horizon of finite count.** -/
theorem exists_coe_le_jumpTime {T : ℝ} {ω : Ω} (hfin : arrivalCount N A T ω ≠ ⊤) :
    ∃ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ jumpTime N A m ω := by
  refine ⟨⌈(arrivalCount N A T ω).toReal⌉₊ + 1, ?_⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨s, hs0, hsT, hle⟩ :=
    (jumpTime_lt_iff N A (⌈(arrivalCount N A T ω).toReal⌉₊ + 1) T ω).mp hcon
  have h1 : ((⌈(arrivalCount N A T ω).toReal⌉₊ + 1 : ℕ) : ℝ≥0∞) ≤ arrivalCount N A T ω :=
    hle.trans (arrivalCount_mono N A ω hsT.le)
  have h2 : ((⌈(arrivalCount N A T ω).toReal⌉₊ + 1 : ℕ) : ℝ) ≤ (arrivalCount N A T ω).toReal := by
    have h2' := ENNReal.toReal_mono hfin h1
    rwa [ENNReal.toReal_natCast] at h2'
  have h3 := Nat.le_ceil (arrivalCount N A T ω).toReal
  push_cast at h2
  linarith

/-- The chain of arrival times starts at the origin and passes any horizon of finite count. -/
theorem jumpTime_chain_of_ne_top {T : ℝ} {ω : Ω} (hfin : arrivalCount N A T ω ≠ ⊤) :
    jumpTime N A 0 ω ≤ ((0 : ℝ) : WithTop ℝ) ∧
      ∃ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ jumpTime N A m ω :=
  ⟨le_of_eq (jumpTime_zero N A ω), exists_coe_le_jumpTime N A hfin⟩

/-- Only finitely many arrival times fall in the window `(0, T]` when the count is finite. -/
theorem finite_setOf_arrivalTime (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T}.Finite := by
  obtain ⟨k, e, -, hrange⟩ := exists_strictMono_enum_jumpTime N A hA hT hfin
  refine Set.Finite.subset (hrange ▸ Set.finite_range e) ?_
  rintro u ⟨i, hiu, -, huT⟩
  exact ⟨i, hiu, huT⟩

/-- The arrival times in the window `(0, T]` carry a strictly monotone enumeration. -/
theorem exists_strictMono_enum_arrivalTime (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧
      Set.range e = {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T} := by
  obtain ⟨k, e, he, hrange⟩ :=
    exists_strictMono_enum (finite_setOf_arrivalTime N A hA hT hfin).toFinset
  exact ⟨k, e, he, by rwa [Set.Finite.coe_toFinset] at hrange⟩

end Chain

section AtomFinset

variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- A time of the window carrying mass in the mark set is one of the times of an atom finset of
the restricted measure. -/
theorem mem_jumpTimes_of_count_singleton_ne_zero (hA : MeasurableSet A) {T : ℝ} {ω : Ω}
    {s : Finset (ℝ × E)}
    (hs : ∀ g : ℝ × E → ℝ≥0∞,
      ∫⁻ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω)
        = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} * g p)
    {u : ℝ} (hu0 : 0 < u) (huT : u ≤ T) (hne : N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0) :
    u ∈ jumpTimes s := by
  classical
  have hmeas : MeasurableSet ((({u} : Set ℝ) ×ˢ A : Set (ℝ × E))) :=
    (measurableSet_singleton u).prod hA
  have hkey := hs ((({u} : Set ℝ) ×ˢ A).indicator 1)
  rw [lintegral_indicator_one hmeas, Measure.restrict_apply hmeas,
    Set.inter_eq_self_of_subset_left
      (Set.prod_mono (Set.singleton_subset_iff.mpr (Set.mem_Ioc.mpr ⟨hu0, huT⟩))
        le_rfl)] at hkey
  have hsum : (∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p}
      * (({u} : Set ℝ) ×ˢ A).indicator 1 p) ≠ 0 := by
    rw [← hkey]
    exact hne
  obtain ⟨p, hps, hp0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hpmem : p ∈ ((({u} : Set ℝ) ×ˢ A) : Set (ℝ × E)) := by
    by_contra hc
    exact hp0 (by rw [Set.indicator_of_notMem hc, mul_zero])
  exact Finset.mem_image.mpr ⟨p, hps, (Set.mem_prod.mp hpmem).1⟩

end AtomFinset

section AlmostEverywhere

variable [MeasurableSpace.CountablyGenerated E]
variable (N : PoissonRandomMeasure.{u, v, w} P ν) (A : Set E)

/-- Almost surely the arrival times in `(0, T]` are exactly the times of `(0, T]` carrying mass in
the mark set. -/
theorem ae_setOf_jumpTime_eq_setOf_count_singleton_ne_zero (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (T : ℝ) :
    ∀ᵐ ω ∂P, {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T}
      = {u : ℝ | (0 < u ∧ u ≤ T) ∧ N.N ω (({u} : Set ℝ) ×ˢ A) ≠ 0} := by
  filter_upwards [ae_isIntegerValued_restrict N (measurableSet_Ioc.prod hA)
    (referenceIntensity_Ioc_prod_ne_top hAν (T + 1))] with ω hint
  exact setOf_jumpTime_eq_setOf_count_singleton_ne_zero N A hA hint

/-- Almost surely the arrival times of the mark set strictly increase inside a window. -/
theorem ae_jumpTime_lt_jumpTime_succ (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ i : ℕ, jumpTime N A (i + 1) ω ≤ (T : WithTop ℝ) →
      jumpTime N A i ω < jumpTime N A (i + 1) ω := by
  have hB : MeasurableSet (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : referenceIntensity ν (Set.Ioc (0 : ℝ) (T + 1) ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAν (T + 1)
  filter_upwards [ae_isIntegerValued_restrict N hB hfin,
    ae_count_time_singleton_le_one N hB hfin] with ω hint hsimple i hi
  refine jumpTime_lt_jumpTime_succ N A hA hint (fun x hx0 hxT => ?_) hi
  have hset : Set.Ioc (0 : ℝ) (T + 1) ×ˢ A ∩ ({x} : Set ℝ) ×ˢ (Set.univ : Set E)
      = ({x} : Set ℝ) ×ˢ A := by
    rw [Set.prod_inter_prod, Set.inter_univ,
      Set.inter_eq_self_of_subset_right
        (Set.singleton_subset_iff.mpr (Set.mem_Ioc.mpr ⟨hx0, by linarith⟩))]
  exact hset ▸ hsimple x

omit [MeasurableSpace.CountablyGenerated E] in
/-- Almost surely the chain of arrival times starts at the origin and passes the horizon `T`. -/
theorem ae_jumpTime_chain (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, jumpTime N A 0 ω ≤ ((0 : ℝ) : WithTop ℝ) ∧
      ∃ m : ℕ, ((T : ℝ) : WithTop ℝ) ≤ jumpTime N A m ω := by
  filter_upwards [count_Ioc_ne_top N hA hAν T] with ω hω
  exact jumpTime_chain_of_ne_top N A hω

variable [MeasurableSingletonClass E]

/-- Almost surely the arrival times in `(0, T]` lie among the times of an atom finset of the
restricted measure. -/
theorem ae_exists_finset_setOf_jumpTime_subset (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      {u : ℝ | ∃ i : ℕ, jumpTime N A i ω = (u : WithTop ℝ) ∧ 0 < u ∧ u ≤ T}
        ⊆ (jumpTimes s : Set ℝ) := by
  filter_upwards [ae_exists_finset_integral_eq_sum_Ioc N hA hAν T,
    ae_isIntegerValued_restrict N (measurableSet_Ioc.prod hA)
      (referenceIntensity_Ioc_prod_ne_top hAν (T + 1))] with ω hω hint
  obtain ⟨s, hs, -, -⟩ := hω
  refine ⟨s, fun x hx => ?_⟩
  rw [setOf_jumpTime_eq_setOf_count_singleton_ne_zero N A hA hint] at hx
  obtain ⟨⟨hx0, hxT⟩, hne⟩ := hx
  exact Finset.mem_coe.mpr (mem_jumpTimes_of_count_singleton_ne_zero N A hA hs hx0 hxT hne)

end AlmostEverywhere

end LevyStochCalc.Poisson

section TempAudit
#print axioms LevyStochCalc.Poisson.setOf_jumpTime_eq_setOf_count_singleton_ne_zero
#print axioms LevyStochCalc.Poisson.coe_zero_lt_jumpTime
#print axioms LevyStochCalc.Poisson.jumpTime_lt_jumpTime_succ
#print axioms LevyStochCalc.Poisson.exists_coe_le_jumpTime
#print axioms LevyStochCalc.Poisson.mem_jumpTimes_of_count_singleton_ne_zero
#print axioms LevyStochCalc.Poisson.ae_setOf_jumpTime_eq_setOf_count_singleton_ne_zero
#print axioms LevyStochCalc.Poisson.ae_jumpTime_lt_jumpTime_succ
#print axioms LevyStochCalc.Poisson.ae_exists_finset_setOf_jumpTime_subset
#print axioms LevyStochCalc.Poisson.exists_strictMono_enum_arrivalTime
#print axioms LevyStochCalc.Poisson.ae_jumpTime_chain
end TempAudit
