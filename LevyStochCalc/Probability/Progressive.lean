/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Process.Adapted
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Progressively measurable real processes

`ProgressivelyMeasurable ℱ H` says that the process `H : Ω → ℝ → E`, viewed as a function of
`(ω, s)`, is `ℱ t ⊗ Borel`-measurable on the time window `s ≤ t`, for every `t`. This is
the progressive measurability of Mathlib's `IsStronglyProgressive`, phrased on `Ω × ℝ` by
truncating the time variable at `t`, which is the form in which the stochastic integrals of
this library consume it; `isStronglyProgressive` and `of_isStronglyProgressive` relate the
two.
-/

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}

section General

variable [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]

/-- The process `H` is progressively measurable for `ℱ`: for every time `t`, the map
`(ω, s) ↦ H ω s` restricted to times `s ≤ t` (and `0` after `t`) is
`ℱ t ⊗ Borel`-measurable. -/
def ProgressivelyMeasurable (ℱ : Filtration ℝ mΩ) (H : Ω → ℝ → E) : Prop :=
  ∀ t : ℝ,
    @StronglyMeasurable (Ω × ℝ) E _ (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2

namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

/-- A progressively measurable process is adapted. -/
theorem stronglyMeasurable_eval (h : ProgressivelyMeasurable ℱ H) (t : ℝ) :
    StronglyMeasurable[ℱ t] fun ω => H ω t := by
  letI : MeasurableSpace Ω := ℱ t
  have := (h t).comp_measurable (measurable_prodMk_right (y := t))
  simpa [Function.comp_def] using this

/-- Composition with a continuous map fixing `0` preserves progressive measurability. -/
theorem _root_.Continuous.comp_progressivelyMeasurable {φ : E → F} (hφ : Continuous φ)
    (hφ0 : φ 0 = 0) (h : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ fun ω s => φ (H ω s) := by
  intro t
  have : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => φ (H p.1 s)) p.2)
      = fun p : Ω × ℝ => φ ((Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    exact congrFun (Set.indicator_comp_of_zero (f := H p.1) (s := Set.Iic t) hφ0) p.2
  rw [this]
  exact hφ.comp_stronglyMeasurable (h t)

/-- A progressively measurable process is strongly progressive in the sense of Mathlib. -/
theorem isStronglyProgressive (h : ProgressivelyMeasurable ℱ H) :
    IsStronglyProgressive ℱ fun s ω => H ω s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have he : Measurable fun q : Set.Iic t × Ω => (q.2, (q.1 : ℝ)) :=
    measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst)
  have := (h t).comp_measurable he
  have heq : (fun q : Set.Iic t × Ω => H q.2 q.1)
      = (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) ∘ fun q : Set.Iic t × Ω =>
        (q.2, (q.1 : ℝ)) := by
    funext q
    exact (Set.indicator_of_mem q.1.2 _).symm
  rw [heq]
  exact this

/-- A strongly progressive process in the sense of Mathlib is progressively measurable. -/
theorem of_isStronglyProgressive (h : IsStronglyProgressive ℱ fun s ω => H ω s) :
    ProgressivelyMeasurable ℱ H := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  let e : Ω × ℝ → Set.Iic t × Ω := fun p => (⟨min p.2 t, Set.mem_Iic.mpr (min_le_right _ _)⟩, p.1)
  have he : Measurable e :=
    ((measurable_snd.min measurable_const).subtype_mk).prodMk measurable_fst
  have : (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2)
      = (Set.univ ×ˢ Set.Iic t).indicator
        ((fun q : Set.Iic t × Ω => H q.2 q.1) ∘ e) := by
    funext p
    by_cases hp : p.2 ≤ t
    · simp [e, hp]
    · simp [e, hp]
  rw [this]
  exact ((h t).comp_measurable he).indicator (MeasurableSet.univ.prod measurableSet_Iic)

end ProgressivelyMeasurable

end General

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

/-- The integral of a progressively measurable process over a measurable set of times `≤ t`
is `ℱ t`-measurable. -/
theorem ProgressivelyMeasurable.stronglyMeasurable_setIntegral (h : ProgressivelyMeasurable ℱ H)
    {t : ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hSt : S ⊆ Set.Iic t) (μ : Measure ℝ)
    [SFinite μ] : StronglyMeasurable[ℱ t] fun ω => ∫ s in S, H ω s ∂μ := by
  letI : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun ω => ∫ s in S, (Set.Iic t).indicator (H ω) s ∂μ :=
    (h t).integral_prod_right' (ν := μ.restrict S)
  have : (fun ω => ∫ s in S, H ω s ∂μ)
      = fun ω => ∫ s in S, (Set.Iic t).indicator (H ω) s ∂μ := by
    funext ω
    exact setIntegral_congr_fun hS fun s hs => (Set.indicator_of_mem (hSt hs) _).symm
  rw [this]
  exact h1

end Integral

end LevyStochCalc.Probability
