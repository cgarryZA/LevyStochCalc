/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CharacterCell

/-!
# The strict-past character as a progressively measurable process

The predictable representative of the strictly-past window sum, evaluated at a fixed mark of the
window and at the time clamped to the horizon, is a jointly measurable and progressively
measurable process. For a family carried strictly before the horizon it is exactly the exponent
of the strict-past character at every time, so the strict-past character is itself progressively
measurable.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Evaluation

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Evaluating a marked progressively measurable process at a fixed mark. -/
theorem progressivelyMeasurable_eval_mark {ψ : Ω → ℝ → E → ℝ}
    (h : Probability.MarkedProgressivelyMeasurable ℱ ψ) (e : E) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => ψ ω s e := by
  intro t
  have hg : @Measurable (Ω × ℝ) (Ω × ℝ × E)
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance)
      fun p : Ω × ℝ => (p.1, (p.2, e)) :=
    Measurable.prodMk measurable_fst (measurable_snd.prodMk measurable_const)
  exact (h t).comp_measurable hg

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- Clamping the time preserves progressive measurability. -/
theorem progressivelyMeasurable_comp_min {f : Ω → ℝ → ℝ}
    (h : Probability.ProgressivelyMeasurable ℱ f) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => f ω (min s T) := by
  intro t
  have hg : @Measurable (Ω × ℝ) (Ω × ℝ)
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      fun p : Ω × ℝ => (p.1, min p.2 T) :=
    Measurable.prodMk measurable_fst (measurable_snd.min measurable_const)
  have hcomp := (h t).comp_measurable hg
  have hind : @StronglyMeasurable (Ω × ℝ) ℝ _
      (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      fun p : Ω × ℝ => (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) p.2 :=
    (stronglyMeasurable_const.indicator (measurableSet_Iic (a := t))).comp_measurable
      measurable_snd
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => f p.1 (min s T)) p.2)
      = fun p : Ω × ℝ => (Set.Iic t).indicator (fun _ : ℝ => (1 : ℝ)) p.2
          * (Set.Iic t).indicator (fun s => f p.1 s) (min p.2 T) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · have hmin : min p.2 T ∈ Set.Iic t := Set.mem_Iic.mpr ((min_le_left p.2 T).trans hp)
      rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hmin, one_mul]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, zero_mul]
  rw [heq]
  exact hind.mul hcomp

end Evaluation

section Clamped

variable (N : PoissonRandomMeasure P ν) (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)}
  {A : Set E} {b T : ℝ}

/-- The predictable representative of the strict-past character: the exponent evaluated at a
fixed mark of the window, with the time clamped to the horizon. -/
noncomputable def charStrictPred (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) (e₀ : E) (s : ℝ) (ω : Ω) : ℂ :=
  Complex.exp (Complex.I * (predStrict N w Bfam A T ω (min s T) e₀ : ℂ))

theorem predStrict_of_nonpos (Bfam : ι → Set (ℝ × E)) (A : Set E) (T : ℝ) {s : ℝ}
    (hs : s ≤ 0) (e : E) (ω : Ω) : predStrict N w Bfam A T ω s e = 0 := by
  classical
  have hzero : ∀ C : Set (ℝ × E), strictCount N C A T ω s e = 0 := by
    intro C
    refine le_antisymm (iSup_le fun n => le_of_eq ?_) (by positivity)
    refine Finset.sum_eq_zero fun i _ => Set.indicator_of_notMem (fun hmem => ?_) _
    have h1 : ((i : ℝ) / 2 ^ n) < s := hmem.1.1
    have h2 : (0 : ℝ) ≤ (i : ℝ) / 2 ^ n := by positivity
    linarith
  simp [predStrict, hzero]

/-- For a family carried strictly before the horizon the predictable representative is the
strict-past character at every time. -/
theorem charStrictPred_eq (N : PoissonRandomMeasure P ν) (w : ι → ℝ)
    {Bfam : ι → Set (ℝ × E)} {A : Set E} {b T : ℝ} (hT : 0 < T) (hbT : b < T)
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A) (s : ℝ) (ω : Ω) :
    charStrictPred N w Bfam A T e₀ s ω = charStrict N w Bfam s ω := by
  rcases le_or_gt s 0 with hs | hs
  · have hmin : min s T = s := min_eq_left (hs.trans hT.le)
    have hz : ∀ j, Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ (Set.univ : Set E) = ∅ := by
      intro j
      refine Set.eq_empty_iff_forall_notMem.mpr fun p hp => ?_
      exact absurd (hp.2.1.2.trans_le hs) (not_lt.mpr hp.2.1.1.le)
    rw [charStrictPred, hmin, predStrict_of_nonpos N w Bfam A T hs e₀ ω, charStrict]
    simp [hz]
  · rcases le_or_gt s T with hsT | hsT
    · rw [charStrictPred, min_eq_left hsT, predStrict_eq N w Bfam hs hsT he₀ ω, charStrict]
    · have hmin : min s T = T := min_eq_right hsT.le
      have hTpos : (0 : ℝ) < T := hT
      have hsame : ∀ j, Bfam j ∩ Set.Ioo (0 : ℝ) T ×ˢ (Set.univ : Set E)
          = Bfam j ∩ Set.Ioo (0 : ℝ) s ×ˢ (Set.univ : Set E) := by
        intro j
        refine Set.Subset.antisymm (fun p hp => ⟨hp.1, ⟨hp.2.1.1, hp.2.1.2.trans hsT⟩,
          Set.mem_univ _⟩) (fun p hp => ⟨hp.1, ⟨(hBsub j hp.1).1.1,
            lt_of_le_of_lt (hBsub j hp.1).1.2 hbT⟩, Set.mem_univ _⟩)
      rw [charStrictPred, hmin, predStrict_eq N w Bfam hTpos le_rfl he₀ ω, charStrict]
      simp_rw [hsame]

end Clamped

end LevyStochCalc.Poisson
