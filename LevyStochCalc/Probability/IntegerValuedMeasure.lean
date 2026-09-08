/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.PiSystem

/-!
# Integer-valued finite measures

A measure is integer-valued when every measurable set carries a natural mass. On a measurable
space with a countable separating family such a measure, if finite, is a finite sum of Dirac
masses: a binary search along the separating family isolates a point of mass at least one, and
removing it lowers the total mass by at least one, so the recursion terminates.

Integrality on a generating π-system already gives integrality everywhere, since the sets of
natural mass form a Dynkin system as soon as the ambient measure is finite.
-/

namespace LevyStochCalc.Probability

open MeasureTheory Filter Set
open scoped ENNReal Topology

variable {α : Type*} [MeasurableSpace α]

/-- A measure is *integer-valued* when every measurable set carries a natural mass. -/
def IsIntegerValued (μ : Measure α) : Prop := ∀ B, MeasurableSet B → ∃ n : ℕ, μ B = n

section PiSystem

/-- A finite measure whose mass on a generating π-system is natural is integer-valued. -/
theorem isIntegerValued_of_isPiSystem {μ : Measure α} [IsFiniteMeasure μ] {C : Set (Set α)}
    (hgen : ‹MeasurableSpace α› = MeasurableSpace.generateFrom C) (hpi : IsPiSystem C)
    (hC : ∀ B ∈ C, ∃ n : ℕ, μ B = n) (huniv : ∃ N : ℕ, μ Set.univ = N) :
    IsIntegerValued μ := by
  intro B hB
  refine MeasurableSpace.induction_on_inter (C := fun t _ => ∃ n : ℕ, μ t = n) hgen hpi
    ⟨0, by simp⟩ (fun t ht => hC t ht) ?_ ?_ B hB
  · rintro t htm ⟨n, hn⟩
    obtain ⟨N, hN⟩ := huniv
    have hle : n ≤ N := by
      have hmono : (n : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by
        rw [← hn, ← hN]; exact measure_mono (Set.subset_univ t)
      exact_mod_cast hmono
    refine ⟨N - n, ?_⟩
    have hsum : (n : ℝ≥0∞) + ((N - n : ℕ) : ℝ≥0∞) = (N : ℝ≥0∞) := by
      rw [← Nat.cast_add, Nat.add_sub_cancel' hle]
    have hcancel : (n : ℝ≥0∞) + μ tᶜ = (n : ℝ≥0∞) + ((N - n : ℕ) : ℝ≥0∞) := by
      rw [hsum, ← hN, ← measure_add_measure_compl htm, hn]
    exact (ENNReal.add_right_inj (by simp)).mp hcancel
  · intro f hdisj hfm hf
    choose g hg using hf
    obtain ⟨N, hN⟩ := huniv
    have hpart : ∀ k : ℕ, ((∑ i ∈ Finset.range k, g i : ℕ) : ℝ≥0∞)
        = μ (⋃ i ∈ Finset.range k, f i) := by
      intro k
      rw [measure_biUnion_finset (fun i _ j _ hij => hdisj hij) fun i _ => hfm i]
      push_cast
      exact Finset.sum_congr rfl fun i _ => (hg i).symm
    have hFle : ∀ k : ℕ, (∑ i ∈ Finset.range k, g i) ≤ N := by
      intro k
      have h2 : μ (⋃ i ∈ Finset.range k, f i) ≤ (N : ℝ≥0∞) :=
        hN ▸ measure_mono (Set.subset_univ _)
      have h3 : ((∑ i ∈ Finset.range k, g i : ℕ) : ℝ≥0∞) ≤ (N : ℝ≥0∞) := (hpart k).symm ▸ h2
      exact_mod_cast h3
    have hbdd : BddAbove (Set.range fun k => ∑ i ∈ Finset.range k, g i) :=
      ⟨N, by rintro _ ⟨k, rfl⟩; exact hFle k⟩
    have hmem := Nat.sSup_mem (Set.range_nonempty _) hbdd
    obtain ⟨k₀, hk₀⟩ := hmem
    refine ⟨∑ i ∈ Finset.range k₀, g i, ?_⟩
    rw [measure_iUnion hdisj hfm, ENNReal.tsum_eq_iSup_nat]
    refine le_antisymm (iSup_le fun k => ?_) ?_
    · have hsum : ∑ i ∈ Finset.range k, μ (f i) = ((∑ i ∈ Finset.range k, g i : ℕ) : ℝ≥0∞) := by
        push_cast
        exact Finset.sum_congr rfl fun i _ => hg i
      rw [hsum]
      have hk₀' : (∑ i ∈ Finset.range k₀, g i)
          = sSup (Set.range fun k => ∑ i ∈ Finset.range k, g i) := hk₀
      have hle' : (∑ i ∈ Finset.range k, g i) ≤ ∑ i ∈ Finset.range k₀, g i := by
        rw [hk₀']; exact le_csSup hbdd ⟨k, rfl⟩
      exact_mod_cast hle'
    · have hsum : ∑ i ∈ Finset.range k₀, μ (f i) = ((∑ i ∈ Finset.range k₀, g i : ℕ) : ℝ≥0∞) := by
        push_cast
        exact Finset.sum_congr rfl fun i _ => hg i
      exact hsum ▸ le_iSup (fun k => ∑ i ∈ Finset.range k, μ (f i)) k₀

/-- The finite intersections of a sequence of sets. -/
def finInters (s : ℕ → Set α) : Set (Set α) :=
  Set.range fun t : Finset ℕ => ⋂ i ∈ t, s i

omit [MeasurableSpace α] in
theorem mem_finInters_iff {s : ℕ → Set α} {B : Set α} :
    B ∈ finInters s ↔ ∃ t : Finset ℕ, (⋂ i ∈ t, s i) = B := Iff.rfl

omit [MeasurableSpace α] in
theorem countable_finInters (s : ℕ → Set α) : (finInters s).Countable :=
  Set.countable_range _

omit [MeasurableSpace α] in
theorem isPiSystem_finInters (s : ℕ → Set α) : IsPiSystem (finInters s) := by
  rintro _ ⟨t₁, rfl⟩ _ ⟨t₂, rfl⟩ _
  refine ⟨t₁ ∪ t₂, ?_⟩
  change (⋂ i ∈ t₁ ∪ t₂, s i) = (⋂ i ∈ t₁, s i) ∩ (⋂ i ∈ t₂, s i)
  ext x
  constructor
  · intro hx
    exact ⟨Set.mem_iInter₂.mpr fun i hi =>
        Set.mem_iInter₂.mp hx i (Finset.mem_union_left _ hi),
      Set.mem_iInter₂.mpr fun i hi =>
        Set.mem_iInter₂.mp hx i (Finset.mem_union_right _ hi)⟩
  · rintro ⟨h1, h2⟩
    refine Set.mem_iInter₂.mpr fun i hi => ?_
    rcases Finset.mem_union.mp hi with h | h
    · exact Set.mem_iInter₂.mp h1 i h
    · exact Set.mem_iInter₂.mp h2 i h

theorem measurableSet_of_mem_finInters {s : ℕ → Set α} (hs : ∀ i, MeasurableSet (s i)) :
    ∀ B ∈ finInters s, MeasurableSet B := by
  rintro _ ⟨t, rfl⟩
  exact MeasurableSet.biInter t.countable_toSet fun i _ => hs i

omit [MeasurableSpace α] in
theorem generateFrom_finInters (s : ℕ → Set α) :
    MeasurableSpace.generateFrom (finInters s)
      = MeasurableSpace.generateFrom (Set.range s) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le ?_)
    (MeasurableSpace.generateFrom_mono ?_)
  · rintro _ ⟨t, rfl⟩
    exact MeasurableSet.biInter t.countable_toSet fun i _ =>
      MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self i)
  · rintro _ ⟨i, rfl⟩
    exact ⟨{i}, by simp⟩

end PiSystem

section Atom

variable [MeasurableSpace.CountablySeparated α]

/-- A nonzero integer-valued finite measure has a point of mass at least one. -/
theorem exists_one_le_measure_singleton (μ : Measure α) [IsFiniteMeasure μ]
    (hint : IsIntegerValued μ) (hpos : μ Set.univ ≠ 0) : ∃ x : α, 1 ≤ μ {x} := by
  classical
  obtain ⟨S, hSne, hScount, hSmeas, hSsep⟩ :=
    exists_nonempty_countable_separating α (p := MeasurableSet) MeasurableSet.univ Set.univ
  obtain ⟨f, hf⟩ := hScount.exists_eq_range hSne
  have hfS : ∀ k, f k ∈ S := fun k => by rw [hf]; exact Set.mem_range_self k
  have hfm : ∀ k, MeasurableSet (f k) := fun k => hSmeas _ (hfS k)
  set B : ℕ → Set α := fun k => Nat.recAux Set.univ
    (fun k Bk => if 1 ≤ μ (Bk ∩ f k) then Bk ∩ f k else Bk \ f k) k with hBdef
  have hB0 : B 0 = Set.univ := rfl
  have hBs : ∀ k, B (k + 1) = if 1 ≤ μ (B k ∩ f k) then B k ∩ f k else B k \ f k :=
    fun _ => rfl
  have hBm : ∀ k, MeasurableSet (B k) := by
    intro k
    induction k with
    | zero => rw [hB0]; exact MeasurableSet.univ
    | succ k ih =>
      rw [hBs k]
      by_cases hc : 1 ≤ μ (B k ∩ f k)
      · rw [if_pos hc]; exact ih.inter (hfm k)
      · rw [if_neg hc]; exact ih.diff (hfm k)
  have hBanti : Antitone B := by
    refine antitone_nat_of_succ_le fun k => ?_
    rw [hBs k]
    by_cases hc : 1 ≤ μ (B k ∩ f k)
    · rw [if_pos hc]; exact Set.inter_subset_left
    · rw [if_neg hc]; exact Set.sdiff_subset
  have hBpos : ∀ k, 1 ≤ μ (B k) := by
    intro k
    induction k with
    | zero =>
      rw [hB0]
      obtain ⟨n, hn⟩ := hint Set.univ MeasurableSet.univ
      rcases Nat.eq_zero_or_pos n with h | h
      · exact absurd (by rw [hn, h]; simp) hpos
      · rw [hn]; exact_mod_cast h
    | succ k ih =>
      rw [hBs k]
      by_cases hc : 1 ≤ μ (B k ∩ f k)
      · rw [if_pos hc]; exact hc
      · rw [if_neg hc]
        obtain ⟨m, hm⟩ := hint (B k ∩ f k) ((hBm k).inter (hfm k))
        have hm0 : μ (B k ∩ f k) = 0 := by
          rcases Nat.eq_zero_or_pos m with h | h
          · rw [hm, h]; simp
          · exact absurd (by rw [hm]; exact_mod_cast h) hc
        have hsplit : μ (B k ∩ f k) + μ (B k \ f k) = μ (B k) :=
          measure_inter_add_sdiff _ (hfm k)
        rw [hm0, zero_add] at hsplit
        rw [hsplit]; exact ih
  have hInter : 1 ≤ μ (⋂ k, B k) := by
    rw [hBanti.measure_iInter (fun k => (hBm k).nullMeasurableSet) ⟨0, measure_ne_top _ _⟩]
    exact le_iInf hBpos
  have hsub : ∀ x y, x ∈ ⋂ k, B k → y ∈ ⋂ k, B k → x = y := by
    intro x y hx hy
    refine hSsep x (Set.mem_univ x) y (Set.mem_univ y) fun s hs => ?_
    obtain ⟨k, rfl⟩ : ∃ k, f k = s := by rw [hf] at hs; exact hs
    have hxk : x ∈ B (k + 1) := Set.mem_iInter.mp hx (k + 1)
    have hyk : y ∈ B (k + 1) := Set.mem_iInter.mp hy (k + 1)
    rw [hBs k] at hxk hyk
    by_cases hc : 1 ≤ μ (B k ∩ f k)
    · rw [if_pos hc] at hxk hyk
      exact iff_of_true hxk.2 hyk.2
    · rw [if_neg hc] at hxk hyk
      exact iff_of_false hxk.2 hyk.2
  have hne : (⋂ k, B k).Nonempty := by
    rcases Set.eq_empty_or_nonempty (⋂ k, B k) with h | h
    · rw [h] at hInter; simp at hInter
    · exact h
  obtain ⟨x, hx⟩ := hne
  exact ⟨x, le_trans hInter (measure_mono fun y hy => hsub y x hy hx)⟩

private theorem exists_finset_ae_mem_aux :
    ∀ n : ℕ, ∀ μ : Measure α, μ Set.univ = n → IsIntegerValued μ →
      ∃ s : Finset α, ∀ᵐ a ∂μ, a ∈ s := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro μ hn hint
    classical
    haveI : IsFiniteMeasure μ := ⟨by rw [hn]; exact ENNReal.natCast_lt_top n⟩
    haveI : MeasurableSingletonClass α :=
      MeasurableSpace.measurableSingletonClass_of_countablySeparated
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · refine ⟨∅, ?_⟩
      have huniv : μ Set.univ = 0 := by rw [hn, h0]; simp
      rw [MeasureTheory.Measure.measure_univ_eq_zero.mp huniv]
      simp
    · have hne0 : μ Set.univ ≠ 0 := by rw [hn]; exact_mod_cast hpos.ne'
      obtain ⟨x, hx⟩ := exists_one_le_measure_singleton μ hint hne0
      have hxm : MeasurableSet ({x} : Set α) := measurableSet_singleton x
      have hint' : IsIntegerValued (μ.restrict {x}ᶜ) := by
        intro B hB
        rw [Measure.restrict_apply hB]
        exact hint _ (hB.inter hxm.compl)
      obtain ⟨m, hm⟩ := hint' Set.univ MeasurableSet.univ
      have hmlt : m < n := by
        have h1 : (μ.restrict {x}ᶜ) Set.univ = μ {x}ᶜ := by
          rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]
        have h2 : μ {x} + μ {x}ᶜ = (n : ℝ≥0∞) := by
          rw [measure_add_measure_compl hxm, hn]
        have h3 : (1 : ℝ≥0∞) + (m : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
          rw [← h2]
          exact add_le_add hx (le_of_eq (by rw [← h1, hm]))
        have h4 : (1 + m : ℕ) ≤ n := by exact_mod_cast h3
        omega
      obtain ⟨s', hs'⟩ := ih m hmlt (μ.restrict {x}ᶜ) hm hint'
      refine ⟨insert x s', ?_⟩
      filter_upwards [(ae_restrict_iff' hxm.compl).mp hs'] with a ha
      by_cases hax : a = x
      · simp [hax]
      · exact Finset.mem_insert_of_mem (ha (by simpa using hax))

/-- An integer-valued measure on a countably separated space is carried by a finite set. -/
theorem exists_finset_ae_mem {μ : Measure α} (hint : IsIntegerValued μ) :
    ∃ s : Finset α, ∀ᵐ a ∂μ, a ∈ s := by
  obtain ⟨n, hn⟩ := hint Set.univ MeasurableSet.univ
  exact exists_finset_ae_mem_aux n μ hn hint

/-- **An integer-valued measure on a countably separated space is a finite sum of Dirac
masses.** -/
theorem exists_eq_sum_dirac {μ : Measure α} (hint : IsIntegerValued μ) :
    ∃ s : Finset α, μ = ∑ a ∈ s, μ {a} • Measure.dirac a := by
  haveI : MeasurableSingletonClass α :=
    MeasurableSpace.measurableSingletonClass_of_countablySeparated
  obtain ⟨s, hs⟩ := exists_finset_ae_mem hint
  exact ⟨s, Measure.ae_mem_finset_iff.mp hs⟩

end Atom

end LevyStochCalc.Probability
