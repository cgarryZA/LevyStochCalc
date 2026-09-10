/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Filtered
import LevyStochCalc.Poisson.JumpSum
import Mathlib.Probability.Process.Stopping

/-!
# Arrival times of a Poisson random measure on a mark set

`arrivalCount N A t ω` is the number of points of a Poisson random measure `N` whose time lies in
`(0, t]` and whose mark lies in `A`. It is monotone in the time, measurable for every filtration
for which `N` is a Poisson random measure, and right-continuous at every time from which it stays
finite. The `i`-th arrival time `jumpTime N A i` is the first nonnegative time at which the count
reaches `i`, and `⊤` when the count never reaches `i`; it is a stopping time for the
right-continuous filtration `ℱ₊`, and for `ℱ` itself when the counting process is everywhere
finite. Over a window on which the count is finite only finitely many arrival times occur, and
they carry a strictly monotone enumeration.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section MarkCount

/-- The number of points of the Poisson random measure `N` with time in `(0, t]` and mark in the
set `A`. -/
noncomputable def arrivalCount (N : PoissonRandomMeasure P ν) (A : Set E) (t : ℝ) (ω : Ω) : ℝ≥0∞ :=
  N.N ω (Set.Ioc (0 : ℝ) t ×ˢ A)

variable (N : PoissonRandomMeasure P ν) (A : Set E)

/-- The counting process vanishes at nonpositive times. -/
theorem arrivalCount_of_nonpos {t : ℝ} (ht : t ≤ 0) (ω : Ω) : arrivalCount N A t ω = 0 := by
  rw [arrivalCount, Set.Ioc_eq_empty (not_lt.mpr ht), Set.empty_prod, measure_empty]

/-- The counting process is monotone in the time. -/
theorem arrivalCount_mono (ω : Ω) : Monotone fun t => arrivalCount N A t ω := fun _ _ hst =>
  measure_mono (Set.prod_mono (Set.Ioc_subset_Ioc_right hst) le_rfl)

/-- The counting process on a measurable mark set is measurable for the time-`t` σ-algebra of any
filtration for which `N` is a Poisson random measure. -/
theorem measurable_arrivalCount {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (t : ℝ) :
    Measurable[ℱ t] (arrivalCount N A t) :=
  hℱ.measurable (Set.prod_mono Set.Ioc_subset_Iic_self (Set.subset_univ A))
    (measurableSet_Ioc.prod hA)

/-- The counting process on a measurable mark set is adapted to any filtration for which `N` is a
Poisson random measure. -/
theorem adapted_arrivalCount {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) :
    Adapted ℱ (arrivalCount N A) :=
  fun t => measurable_arrivalCount N A hℱ hA t

/-- **Right-continuity of the counting process.** At a time from which the count stays finite the
count is the infimum of the counts at later times. -/
theorem iInf_arrivalCount_gt (hA : MeasurableSet A) {t u : ℝ} (htu : t < u) {ω : Ω}
    (hu : arrivalCount N A u ω ≠ ⊤) :
    ⨅ s ∈ Set.Ioi t, arrivalCount N A s ω = arrivalCount N A t ω := by
  refine le_antisymm ?_ (le_iInf₂ fun s hs => arrivalCount_mono N A ω (le_of_lt hs))
  obtain ⟨r, hr_anti, hr_mem, hr_tend⟩ := exists_seq_strictAnti_tendsto' htu
  have hanti : Antitone fun n : ℕ => Set.Ioc (0 : ℝ) (r n) ×ˢ A := fun _ _ hmn =>
    Set.prod_mono (Set.Ioc_subset_Ioc_right (hr_anti.antitone hmn)) le_rfl
  have hInter : (⋂ n, Set.Ioc (0 : ℝ) (r n) ×ˢ A) = Set.Ioc (0 : ℝ) t ×ˢ A := by
    ext x
    simp only [Set.mem_iInter, Set.mem_prod, Set.mem_Ioc]
    exact ⟨fun h => ⟨⟨(h 0).1.1, ge_of_tendsto' hr_tend fun n => (h n).1.2⟩, (h 0).2⟩,
      fun h n => ⟨⟨h.1.1, h.1.2.trans (hr_mem n).1.le⟩, h.2⟩⟩
  have hfin : ∃ n, N.N ω (Set.Ioc (0 : ℝ) (r n) ×ˢ A) ≠ ⊤ := by
    refine ⟨0, fun hcon => hu ?_⟩
    have hle : arrivalCount N A (r 0) ω ≤ arrivalCount N A u ω :=
      arrivalCount_mono N A ω (hr_mem 0).2.le
    exact top_le_iff.mp (hcon ▸ hle)
  have hkey := hanti.measure_iInter
    (fun _ => (measurableSet_Ioc.prod hA).nullMeasurableSet) hfin
  rw [hInter] at hkey
  calc ⨅ s ∈ Set.Ioi t, arrivalCount N A s ω
      ≤ ⨅ n : ℕ, arrivalCount N A (r n) ω :=
        le_iInf fun n => iInf₂_le (r n) (Set.mem_Ioi.mpr (hr_mem n).1)
    _ = arrivalCount N A t ω := hkey.symm

/-- The counting process on a mark set of finite intensity is almost surely finite at every
time. -/
theorem ae_forall_arrivalCount_ne_top (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, arrivalCount N A t ω ≠ ⊤ := by
  have h : ∀ n : ℕ, ∀ᵐ ω ∂P, N.N ω (Set.Ioc (0 : ℝ) (n : ℝ) ×ˢ A) ≠ ⊤ :=
    fun n => count_Ioc_ne_top N hA hAν (n : ℝ)
  filter_upwards [ae_all_iff.mpr h] with ω hω t
  obtain ⟨n, hn⟩ := exists_nat_gt t
  exact fun hcon => hω n (top_le_iff.mp (hcon ▸ arrivalCount_mono N A ω hn.le))

end MarkCount

section JumpTime

/-- The nonnegative times by which at least `i` points of `N` with mark in `A` have arrived. -/
def jumpTimeSet (N : PoissonRandomMeasure P ν) (A : Set E) (i : ℕ) (ω : Ω) : Set ℝ :=
  {t : ℝ | 0 ≤ t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A t ω}

open scoped Classical in
/-- The `i`-th arrival time of `N` in the mark set `A`: the first nonnegative time at which the
number of points with mark in `A` reaches `i`, and `⊤` when it never does. -/
noncomputable def jumpTime (N : PoissonRandomMeasure P ν) (A : Set E) (i : ℕ) (ω : Ω) :
    WithTop ℝ :=
  if (jumpTimeSet N A i ω).Nonempty then ((sInf (jumpTimeSet N A i ω) : ℝ) : WithTop ℝ) else ⊤

variable (N : PoissonRandomMeasure P ν) (A : Set E)

theorem bddBelow_jumpTimeSet (i : ℕ) (ω : Ω) : BddBelow (jumpTimeSet N A i ω) :=
  ⟨0, fun _ ht => ht.1⟩

/-- Arrival times are nonnegative. -/
theorem coe_zero_le_jumpTime (i : ℕ) (ω : Ω) : ((0 : ℝ) : WithTop ℝ) ≤ jumpTime N A i ω := by
  rw [jumpTime]
  split_ifs with h
  · exact_mod_cast le_csInf h fun _ hr => hr.1
  · exact le_top

theorem jumpTimeSet_zero (ω : Ω) : jumpTimeSet N A 0 ω = Set.Ici (0 : ℝ) := by
  ext t
  simp [jumpTimeSet]

/-- The zeroth arrival time is the origin. -/
theorem jumpTime_zero (ω : Ω) : jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ) := by
  have hInf : sInf (Set.Ici (0 : ℝ)) = 0 :=
    le_antisymm (csInf_le bddBelow_Ici Set.self_mem_Ici)
      (le_csInf Set.nonempty_Ici fun _ hx => hx)
  rw [jumpTime, jumpTimeSet_zero, if_pos Set.nonempty_Ici, hInf]

theorem jumpTimeSet_subset {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    jumpTimeSet N A j ω ⊆ jumpTimeSet N A i ω := fun _ ht =>
  ⟨ht.1, le_trans (by exact_mod_cast hij) ht.2⟩

/-- Arrival times increase with the index. -/
theorem jumpTime_mono {i j : ℕ} (hij : i ≤ j) (ω : Ω) :
    jumpTime N A i ω ≤ jumpTime N A j ω := by
  rw [jumpTime, jumpTime]
  split_ifs with h1 h2 h2
  · exact_mod_cast csInf_le_csInf (bddBelow_jumpTimeSet N A i ω) h2
      (jumpTimeSet_subset N A hij ω)
  · exact le_top
  · exact absurd (h2.mono (jumpTimeSet_subset N A hij ω)) h1
  · exact le_rfl

/-- The `i`-th arrival time is strictly below `t` exactly when the count reaches `i` at some
nonnegative time strictly below `t`. -/
theorem jumpTime_lt_iff (i : ℕ) (t : ℝ) (ω : Ω) :
    jumpTime N A i ω < (t : WithTop ℝ)
      ↔ ∃ s : ℝ, 0 ≤ s ∧ s < t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A s ω := by
  rw [jumpTime]
  split_ifs with hne
  · constructor
    · intro hlt
      have hst : sInf (jumpTimeSet N A i ω) < t := by exact_mod_cast hlt
      obtain ⟨s, hs, hst'⟩ := exists_lt_of_csInf_lt hne hst
      exact ⟨s, hs.1, hst', hs.2⟩
    · rintro ⟨s, hs0, hst, hcount⟩
      have hle : sInf (jumpTimeSet N A i ω) ≤ s :=
        csInf_le (bddBelow_jumpTimeSet N A i ω) ⟨hs0, hcount⟩
      exact_mod_cast lt_of_le_of_lt hle hst
  · constructor
    · intro hlt
      exact absurd hlt (by simp)
    · rintro ⟨s, hs0, _, hcount⟩
      exact absurd ⟨s, hs0, hcount⟩ hne

/-- The `i`-th arrival time is strictly below `t` exactly when the count reaches `i` at some
nonnegative rational time strictly below `t`. -/
theorem jumpTime_lt_iff_rat (i : ℕ) (t : ℝ) (ω : Ω) :
    jumpTime N A i ω < (t : WithTop ℝ)
      ↔ ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ (i : ℝ≥0∞) ≤ arrivalCount N A (q : ℝ) ω := by
  rw [jumpTime_lt_iff]
  constructor
  · rintro ⟨s, hs0, hst, hcount⟩
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hst
    exact ⟨q, hs0.trans hq1.le, hq2, hcount.trans (arrivalCount_mono N A ω hq1.le)⟩
  · rintro ⟨q, h0, h1, h2⟩
    exact ⟨(q : ℝ), h0, h1, h2⟩

/-- The event that the `i`-th arrival time is strictly below `t` is known at time `t`. -/
theorem measurableSet_jumpTime_lt {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (i : ℕ) (t : ℝ) :
    MeasurableSet[ℱ t] {ω | jumpTime N A i ω < (t : WithTop ℝ)} := by
  have hset : {ω | jumpTime N A i ω < (t : WithTop ℝ)}
      = ⋃ q : {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) < t},
          {ω | (i : ℝ≥0∞) ≤ arrivalCount N A ((q : ℚ) : ℝ) ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Subtype.exists]
    rw [jumpTime_lt_iff_rat]
    exact ⟨fun ⟨q, h0, h1, h2⟩ => ⟨q, ⟨h0, h1⟩, h2⟩, fun ⟨q, ⟨h0, h1⟩, h2⟩ => ⟨q, h0, h1, h2⟩⟩
  have hq : ∀ q : {q : ℚ // 0 ≤ (q : ℝ) ∧ (q : ℝ) < t},
      MeasurableSet[ℱ t] {ω | (i : ℝ≥0∞) ≤ arrivalCount N A ((q : ℚ) : ℝ) ω} := fun q =>
    ℱ.mono q.2.2.le _ (measurable_arrivalCount N A hℱ hA ((q : ℚ) : ℝ) measurableSet_Ici)
  rw [hset]
  exact MeasurableSet.iUnion (m := ℱ t) hq

/-- **The arrival times are stopping times.** For a Poisson random measure adapted to `ℱ`, the
`i`-th arrival time in a measurable mark set is a stopping time for the right-continuous
filtration `ℱ₊`. -/
theorem isStoppingTime_jumpTime_rightCont {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A) (i : ℕ) :
    IsStoppingTime ℱ.rightCont (jumpTime N A i) :=
  MeasureTheory.isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    fun t => ℱ.le_rightCont t _ (measurableSet_jumpTime_lt N A hℱ hA i t)

/-- Where the counting process stays finite, the `i`-th arrival time is at most `t` exactly when
the count has reached `i` by time `t`. -/
theorem jumpTime_le_iff (hA : MeasurableSet A) {i : ℕ} {t : ℝ} (ht : 0 ≤ t) {ω : Ω}
    (hfin : arrivalCount N A (t + 1) ω ≠ ⊤) :
    jumpTime N A i ω ≤ (t : WithTop ℝ) ↔ (i : ℝ≥0∞) ≤ arrivalCount N A t ω := by
  constructor
  · intro hle
    rw [jumpTime] at hle
    split_ifs at hle with hne
    · have hst : sInf (jumpTimeSet N A i ω) ≤ t := by exact_mod_cast hle
      rw [← iInf_arrivalCount_gt N A hA (lt_add_one t) hfin]
      refine le_iInf₂ fun s hs => ?_
      obtain ⟨w, hw, hws⟩ := exists_lt_of_csInf_lt hne (lt_of_le_of_lt hst hs)
      exact hw.2.trans (arrivalCount_mono N A ω hws.le)
    · exact absurd hle (by simp)
  · intro hcount
    rw [jumpTime, if_pos ⟨t, ht, hcount⟩]
    exact_mod_cast csInf_le (bddBelow_jumpTimeSet N A i ω) ⟨ht, hcount⟩

/-- **The arrival times are stopping times for `ℱ` itself** when the counting process is finite
at every time and every sample point. -/
theorem isStoppingTime_jumpTime {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hℱ : IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), arrivalCount N A t ω ≠ ⊤) (i : ℕ) :
    IsStoppingTime ℱ (jumpTime N A i) := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hempty : {ω | jumpTime N A i ω ≤ (t : WithTop ℝ)} = (∅ : Set Ω) := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hle
      have h0 : ((0 : ℝ) : WithTop ℝ) ≤ (t : WithTop ℝ) :=
        (coe_zero_le_jumpTime N A i ω).trans hle
      exact absurd (by exact_mod_cast h0 : (0 : ℝ) ≤ t) (not_le.mpr ht)
    rw [hempty]
    exact @MeasurableSet.empty Ω (ℱ t)
  · have hset : {ω | jumpTime N A i ω ≤ (t : WithTop ℝ)}
        = {ω | (i : ℝ≥0∞) ≤ arrivalCount N A t ω} := by
      ext ω
      exact jumpTime_le_iff N A hA ht (hfin ω (t + 1))
    rw [hset]
    exact measurable_arrivalCount N A hℱ hA t measurableSet_Ici

end JumpTime

section Finiteness

variable (N : PoissonRandomMeasure P ν) (A : Set E)

/-- Only finitely many arrival times fall inside a window on which the count is finite. -/
theorem finite_setOf_jumpTime_le (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    {i : ℕ | jumpTime N A i ω ≤ (T : WithTop ℝ)}.Finite := by
  have hcT : arrivalCount N A T ω ≠ ⊤ := by
    intro hcon
    exact hfin (top_le_iff.mp (hcon ▸ arrivalCount_mono N A ω (by linarith : T ≤ T + 1)))
  refine Set.Finite.subset (Set.finite_Iic ⌈(arrivalCount N A T ω).toReal⌉₊) fun i hi => ?_
  have hle : (i : ℝ≥0∞) ≤ arrivalCount N A T ω := (jumpTime_le_iff N A hA hT hfin).mp hi
  have hre : (i : ℝ) ≤ (arrivalCount N A T ω).toReal := by
    simpa using ENNReal.toReal_mono hcT hle
  exact Nat.cast_le.mp (hre.trans (Nat.le_ceil _))

/-- Almost surely only finitely many arrival times fall inside a window, for a mark set of finite
intensity. -/
theorem ae_finite_setOf_jumpTime_le (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ω ∂P, {i : ℕ | jumpTime N A i ω ≤ (T : WithTop ℝ)}.Finite := by
  filter_upwards [count_Ioc_ne_top N hA hAν (T + 1)] with ω hω
  exact finite_setOf_jumpTime_le N A hA hT hω

/-- The arrival times inside a window on which the count is finite carry a strictly monotone
enumeration. -/
theorem exists_strictMono_enum_jumpTime (hA : MeasurableSet A) {T : ℝ} (hT : 0 ≤ T) {ω : Ω}
    (hfin : arrivalCount N A (T + 1) ω ≠ ⊤) :
    ∃ (k : ℕ) (e : Fin k → ℝ), StrictMono e ∧
      Set.range e = {s : ℝ | ∃ i : ℕ, jumpTime N A i ω = (s : WithTop ℝ) ∧ s ≤ T} := by
  have himg : {s : ℝ | ∃ i : ℕ, jumpTime N A i ω = (s : WithTop ℝ) ∧ s ≤ T}
      = (fun i => sInf (jumpTimeSet N A i ω)) ''
          {i : ℕ | jumpTime N A i ω ≤ (T : WithTop ℝ)} := by
    ext s
    constructor
    · rintro ⟨i, hi, hsT⟩
      refine ⟨i, ?_, ?_⟩
      · show jumpTime N A i ω ≤ (T : WithTop ℝ)
        rw [hi]
        exact_mod_cast hsT
      · rw [jumpTime] at hi
        split_ifs at hi with hne
        · exact_mod_cast hi
        · exact absurd hi (by simp)
    · rintro ⟨i, hi, rfl⟩
      have hi' : jumpTime N A i ω ≤ (T : WithTop ℝ) := hi
      have hne : (jumpTimeSet N A i ω).Nonempty := by
        by_contra hcon
        rw [jumpTime, if_neg hcon] at hi'
        exact absurd hi' (by simp)
      refine ⟨i, ?_, ?_⟩
      · rw [jumpTime, if_pos hne]
      · rw [jumpTime, if_pos hne] at hi'
        exact_mod_cast hi'
  rw [himg]
  obtain ⟨k, e, he, hrange⟩ := exists_strictMono_enum
    ((finite_setOf_jumpTime_le N A hA hT hfin).image
      fun i => sInf (jumpTimeSet N A i ω)).toFinset
  exact ⟨k, e, he, by rwa [Set.Finite.coe_toFinset] at hrange⟩

end Finiteness

end LevyStochCalc.Poisson
