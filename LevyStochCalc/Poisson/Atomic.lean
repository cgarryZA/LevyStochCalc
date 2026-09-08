/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.FiniteActivity
import LevyStochCalc.Probability.IntegerValuedMeasure

/-!
# Atomicity of a Poisson random measure on a finite-activity window

A Poisson random measure carries a natural mass on each measurable set of finite intensity, one
set at a time and only almost surely. Over a window of finite intensity the counts on a countable
generating π-system are simultaneously natural on a single event of full measure, and the sets of
natural mass form a Dynkin system, so on that event the restricted measure is integer-valued. On
a countably separated mark space it is then a finite sum of Dirac masses.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

section CountablyGenerated

variable [MeasurableSpace.CountablyGenerated E]

/-- A countable π-system generating the σ-algebra of the time–mark space. -/
noncomputable def markPiSystem (E : Type v) [MeasurableSpace E]
    [MeasurableSpace.CountablyGenerated E] : Set (Set (ℝ × E)) :=
  Probability.finInters (MeasurableSpace.natGeneratingSequence (ℝ × E))

theorem generateFrom_markPiSystem :
    MeasurableSpace.generateFrom (markPiSystem E)
      = (inferInstance : MeasurableSpace (ℝ × E)) := by
  rw [markPiSystem, Probability.generateFrom_finInters,
    MeasurableSpace.generateFrom_natGeneratingSequence]

theorem isPiSystem_markPiSystem : IsPiSystem (markPiSystem E) :=
  Probability.isPiSystem_finInters _

/-- On a set of finite intensity the restricted Poisson random measure is almost surely
integer-valued. -/
theorem ae_isIntegerValued_restrict (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, Probability.IsIntegerValued ((N.N ω).restrict R) := by
  classical
  have hcell : ∀ t : Finset ℕ,
      MeasurableSet (⋂ i ∈ t, MeasurableSpace.natGeneratingSequence (ℝ × E) i) :=
    fun t => MeasurableSet.biInter t.countable_toSet
      fun i _ => MeasurableSpace.measurableSet_natGeneratingSequence i
  have hgen : ∀ t : Finset ℕ, ∀ᵐ ω ∂P, ∃ n : ℕ,
      N.N ω ((⋂ i ∈ t, MeasurableSpace.natGeneratingSequence (ℝ × E) i) ∩ R) = n := by
    intro t
    refine N.integer_valued ((hcell t).inter hRm) ?_
    exact ne_top_of_le_ne_top hRfin (measure_mono Set.inter_subset_right)
  have huniv : ∀ᵐ ω ∂P, ∃ n : ℕ, N.N ω R = n := N.integer_valued hRm hRfin
  filter_upwards [ae_all_iff.mpr hgen, huniv] with ω hω hωu
  have hmass : ∃ n : ℕ, ((N.N ω).restrict R) Set.univ = n := by
    obtain ⟨n, hn⟩ := hωu
    exact ⟨n, by rw [Measure.restrict_apply MeasurableSet.univ, Set.univ_inter]; exact hn⟩
  haveI : IsFiniteMeasure ((N.N ω).restrict R) := by
    obtain ⟨n, hn⟩ := hmass
    exact ⟨by rw [hn]; exact ENNReal.natCast_lt_top n⟩
  refine Probability.isIntegerValued_of_isPiSystem (C := markPiSystem E)
    generateFrom_markPiSystem.symm isPiSystem_markPiSystem ?_ hmass
  intro B hB
  obtain ⟨t, rfl⟩ := Probability.mem_finInters_iff.mp hB
  obtain ⟨n, hn⟩ := hω t
  exact ⟨n, by rw [Measure.restrict_apply (hcell t)]; exact hn⟩

end CountablyGenerated

section Atomic

variable [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

/-- **Atomicity on a set of finite intensity.** The Poisson random measure restricted to a set of
finite intensity is almost surely a finite sum of Dirac masses. -/
theorem ae_exists_eq_sum_dirac (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      (N.N ω).restrict R = ∑ p ∈ s, ((N.N ω).restrict R) {p} • Measure.dirac p := by
  filter_upwards [ae_isIntegerValued_restrict N hRm hRfin] with ω hω
  exact Probability.exists_eq_sum_dirac hω

/-- A set of finite intensity almost surely carries the Poisson random measure on finitely many
time–mark points. -/
theorem ae_exists_finset_support (N : PoissonRandomMeasure P ν) {R : Set (ℝ × E)}
    (hRm : MeasurableSet R) (hRfin : referenceIntensity ν R ≠ ⊤) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E), N.N ω (R \ (s : Set (ℝ × E))) = 0 := by
  filter_upwards [ae_isIntegerValued_restrict N hRm hRfin] with ω hω
  obtain ⟨s, hs⟩ := Probability.exists_finset_ae_mem hω
  refine ⟨s, ?_⟩
  rw [MeasureTheory.ae_iff, Measure.restrict_apply] at hs
  · rw [← hs]
    congr 1
    ext p
    simp [and_comm]
  · exact s.measurableSet.compl

/-- **Atomicity on a finite-activity window.** Over a bounded time window and a mark set of finite
intensity, the Poisson random measure is almost surely a finite sum of Dirac masses. -/
theorem ae_exists_eq_sum_dirac_Ioc (N : PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      (N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)
        = ∑ p ∈ s, ((N.N ω).restrict (Set.Ioc (0 : ℝ) T ×ˢ A)) {p} • Measure.dirac p :=
  ae_exists_eq_sum_dirac N (measurableSet_Ioc.prod hA)
    (referenceIntensity_Ioc_prod_ne_top hAν T)

/-- **Finite activity, support half.** Over a bounded time window and a mark set of finite
intensity, the Poisson random measure is almost surely carried by finitely many time–mark
points. -/
theorem ae_exists_finset_support_Ioc (N : PoissonRandomMeasure P ν) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ s : Finset (ℝ × E),
      N.N ω ((Set.Ioc (0 : ℝ) T ×ˢ A) \ (s : Set (ℝ × E))) = 0 :=
  ae_exists_finset_support N (measurableSet_Ioc.prod hA)
    (referenceIntensity_Ioc_prod_ne_top hAν T)

end Atomic

end LevyStochCalc.Poisson
