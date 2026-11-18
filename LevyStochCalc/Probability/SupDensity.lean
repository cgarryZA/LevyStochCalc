/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.SetIntegralPiSystem
import LevyStochCalc.Probability.IndepJoin
import LevyStochCalc.Probability.AugmentationMeasurable
import Mathlib.MeasureTheory.Function.ConditionalExpectation.AEMeasurable
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Products of indicators are dense for a join of two σ-algebras

For σ-algebras `m₁, m₂ ≤ m₀` the intersections `A ∩ B`, `A ∈ m₁`, `B ∈ m₂`, form a π-system
generating `m₁ ⊔ m₂`. An integrable function measurable for `m₁ ⊔ m₂`, or for its augmentation by
the null sets, that integrates to zero over every such intersection vanishes almost everywhere.
Equivalently, in `L²` of a finite measure the linear span of the products `1_A · 1_B` is dense in
the closed subspace of `m₁ ⊔ m₂`-measurable classes.

## Main statements

* `LevyStochCalc.Probability.ae_eq_zero_of_setIntegral_inter_eq_zero`: the separation statement
  for `m₁ ⊔ m₂`.
* `LevyStochCalc.Probability.ae_eq_zero_of_setIntegral_inter_eq_zero_aug`: the same for the
  augmentation of `m₁ ⊔ m₂`.
* `LevyStochCalc.Probability.mem_topologicalClosure_span_indicatorConstLp_inter`: the density
  statement in `L²`.
-/

open MeasureTheory
open scoped ENNReal

namespace LevyStochCalc.Probability

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

variable {m₁ m₂ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- **Separation by products of indicators.** An integrable function, measurable for `m₁ ⊔ m₂`
up to a null set, that integrates to zero over every `A ∩ B` with `A ∈ m₁`, `B ∈ m₂`, vanishes
almost everywhere. -/
theorem ae_eq_zero_of_setIntegral_inter_eq_zero (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ) {f : Ω → E}
    (hf : Integrable f μ) (hfm : AEStronglyMeasurable[m₁ ⊔ m₂] f μ)
    (h : ∀ A B, MeasurableSet[m₁] A → MeasurableSet[m₂] B → ∫ x in A ∩ B, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  set g := hfm.mk f with hg
  have hfg : f =ᵐ[μ] g := hfm.ae_eq_mk
  have hgi : Integrable g μ := hf.congr hfg
  have hset : ∀ s, ∫ x in s, g x ∂μ = ∫ x in s, f x ∂μ := fun s =>
    integral_congr_ae (ae_restrict_of_ae hfg.symm)
  have hmem : ∀ s ∈ interSets m₁ m₂, ∫ x in s, g x ∂μ = 0 := by
    rintro _ ⟨A, B, hA, hB, rfl⟩
    rw [hset]
    exact h A B hA hB
  have huniv : ∫ x, g x ∂μ = 0 := by
    have := hmem Set.univ ⟨Set.univ, Set.univ, .univ, .univ, (Set.inter_univ _).symm⟩
    simpa using this
  have hg0 := ae_eq_zero_of_forall_setIntegral_eq_zero_isPiSystem (sup_le hm₁ hm₂)
    sup_eq_generateFrom_interSets isPiSystem_interSets hgi
    hfm.stronglyMeasurable_mk huniv hmem
  exact hfg.trans hg0

/-- **Separation by products of indicators, augmented form.** The same statement for a function
measurable, up to a null set, for the augmentation of `m₁ ⊔ m₂` by the `μ`-null sets. -/
theorem ae_eq_zero_of_setIntegral_inter_eq_zero_aug (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {f : Ω → E} (hf : Integrable f μ) (hfm : AEStronglyMeasurable[aug (m₁ ⊔ m₂) mΩ μ] f μ)
    (h : ∀ A B, MeasurableSet[m₁] A → MeasurableSet[m₂] B → ∫ x in A ∩ B, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  obtain ⟨g, hgm, hfg⟩ := hfm
  have hg' : AEStronglyMeasurable[m₁ ⊔ m₂] g μ := aestronglyMeasurable_of_stronglyMeasurable_aug hgm
  exact ae_eq_zero_of_setIntegral_inter_eq_zero hm₁ hm₂ hf
    (hg'.congr hfg.symm) h

/-- The indicator `1_{A ∩ B}` in `L²`, for `A ∈ m₁` and `B ∈ m₂`. -/
noncomputable def indicatorInterLp (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ) {A B : Set Ω}
    (hA : MeasurableSet[m₁] A) (hB : MeasurableSet[m₂] B) : Lp ℝ 2 μ :=
  indicatorConstLp 2 ((hm₁ A hA).inter (hm₂ B hB)) (measure_ne_top μ _) (1 : ℝ)

/-- **Density of products of indicators.** In `L²(μ)`, every class measurable for `m₁ ⊔ m₂` up to
a null set lies in the closed linear span of the indicators `1_{A ∩ B} = 1_A · 1_B`, `A ∈ m₁`,
`B ∈ m₂`. -/
theorem mem_topologicalClosure_span_indicatorConstLp_inter (hm₁ : m₁ ≤ mΩ) (hm₂ : m₂ ≤ mΩ)
    {f : Lp ℝ 2 μ} (hfm : AEStronglyMeasurable[m₁ ⊔ m₂] f μ) :
    f ∈ (Submodule.span ℝ {u : Lp ℝ 2 μ | ∃ (A B : Set Ω) (hA : MeasurableSet[m₁] A)
      (hB : MeasurableSet[m₂] B), u = indicatorInterLp hm₁ hm₂ hA hB}).topologicalClosure := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set S : Set (Lp ℝ 2 μ) := {u | ∃ (A B : Set Ω) (hA : MeasurableSet[m₁] A)
    (hB : MeasurableSet[m₂] B), u = indicatorInterLp hm₁ hm₂ hA hB} with hS
  set K := (Submodule.span ℝ S).topologicalClosure with hK
  haveI : CompleteSpace K := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  have hle : K ≤ lpMeas ℝ ℝ (m₁ ⊔ m₂) 2 μ := by
    refine Submodule.topologicalClosure_minimal _ ?_ ?_
    · refine Submodule.span_le.mpr ?_
      rintro u ⟨A, B, hA, hB, rfl⟩
      refine mem_lpMeas_iff_aestronglyMeasurable.mpr ?_
      have hAB : MeasurableSet[m₁ ⊔ m₂] (A ∩ B) :=
        (le_sup_left (a := m₁) (b := m₂) A hA).inter (le_sup_right (a := m₁) (b := m₂) B hB)
      exact (stronglyMeasurable_const.indicator hAB).aestronglyMeasurable.congr
        indicatorConstLp_coeFn.symm
    · exact isClosed_aestronglyMeasurable (sup_le hm₁ hm₂)
  obtain ⟨y, hy, z, hz, hyz⟩ := K.exists_add_mem_mem_orthogonal f
  have hzm : AEStronglyMeasurable[m₁ ⊔ m₂] (z : Ω → ℝ) μ := by
    have hym : AEStronglyMeasurable[m₁ ⊔ m₂] (y : Ω → ℝ) μ :=
      mem_lpMeas_iff_aestronglyMeasurable.mp (hle hy)
    have hzeq : z = f - y := by rw [hyz]; abel
    rw [hzeq]
    exact (hfm.sub hym).congr (Lp.coeFn_sub f y).symm
  have hz0 : (z : Ω → ℝ) =ᵐ[μ] 0 := by
    refine ae_eq_zero_of_setIntegral_inter_eq_zero hm₁ hm₂
      ((Lp.memLp z).integrable (by norm_num)) hzm fun A B hA hB => ?_
    have hmemK : indicatorInterLp (μ := μ) hm₁ hm₂ hA hB ∈ K :=
      Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨A, B, hA, hB, rfl⟩)
    have hinner := (Submodule.mem_orthogonal K z).mp hz _ hmemK
    rw [indicatorInterLp, L2.inner_indicatorConstLp_one] at hinner
    exact hinner
  have hzz : z = 0 := (Lp.eq_zero_iff_ae_eq_zero).mpr hz0
  rw [hyz, hzz, add_zero]
  exact hy

end LevyStochCalc.Probability
