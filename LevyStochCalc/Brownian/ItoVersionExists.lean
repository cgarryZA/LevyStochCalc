/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoProcessVersion
import LevyStochCalc.Brownian.ItoQuadVarSum

/-!
# Existence of a continuous adapted version of an Itô process

The Itô integral has an a.e.-continuous modification by Kolmogorov–Chentsov. Zeroing its paths
on a null set makes them continuous everywhere, and the resulting process stays adapted exactly
when the filtration contains the null sets — the usual conditions. Adding a measurable initial
value and the drift's (Lipschitz, hence continuous) window integral gives an `IsItoVersion`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_of_ae_eq_of_null_mem` — a σ-algebra of the filtration
  containing the null sets does not distinguish a.e.-equal functions.
* `LevyStochCalc.Brownian.Ito.exists_isItoVersion` — a continuous adapted version exists.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- If a sub-σ-algebra of a filtration contains every `μ`-null set, a function a.e.-equal to a
measurable function for it is itself measurable for it. -/
theorem measurable_of_ae_eq_of_null_mem {μ : Measure Ω}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (u : ℝ)
    (hnull : ∀ s : Set Ω, (∃ N, MeasurableSet N ∧ μ N = 0 ∧ s ⊆ N) → MeasurableSet[ℱ u] s)
    {f g : Ω → ℝ} (hg : Measurable[ℱ u] g) (hfg : f =ᵐ[μ] g) : Measurable[ℱ u] f := by
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hfg)
  have hNm : MeasurableSet[ℱ u] N := hnull N ⟨N, hNmeas, hNzero, Set.Subset.rfl⟩
  intro A hA
  have hset : f ⁻¹' A = (g ⁻¹' A \ N) ∪ (f ⁻¹' A ∩ N) := by
    ext ω
    by_cases hω : ω ∈ N
    · simp [hω]
    · have hfgω : f ω = g ω := by
        by_contra hne
        exact hω (hNsub hne)
      simp [hω, hfgω]
  rw [hset]
  exact MeasurableSet.union (MeasurableSet.diff (hg hA) hNm)
    (hnull _ ⟨N, hNmeas, hNzero, Set.inter_subset_right⟩)

/-- A measurable null set outside which an almost-everywhere property holds. -/
theorem exists_measurable_null_of_ae {μ : Measure Ω} {p : Ω → Prop} (h : ∀ᵐ ω ∂μ, p ω) :
    ∃ N : Set Ω, MeasurableSet N ∧ μ N = 0 ∧ ∀ ω, ω ∉ N → p ω := by
  obtain ⟨N, hsub, hmeas, hzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp h)
  exact ⟨N, hmeas, hzero, fun ω hω => by_contra fun hp => hω (hsub hp)⟩

section Exists

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- **A continuous adapted version of an Itô process exists** when the filtration is constant
before time `0` and contains the null sets. -/
theorem exists_isItoVersion
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, (∃ N, MeasurableSet N ∧ P N = 0 ∧ s ⊆ N) → MeasurableSet[ℱ 0] s)
    {X₀ : Ω → ℝ} (hX₀ : Measurable[ℱ 0] X₀)
    (bdrift : Ω → ℝ → ℝ) (hbm : Measurable (Function.uncurry bdrift))
    (hbp : Probability.ProgressivelyMeasurable ℱ bdrift)
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (ω : Ω) (s : ℝ), |bdrift ω s| ≤ B) :
    ∃ X : ℝ → Ω → ℝ, IsItoVersion W ℱ hℱ H hm hp hq X₀ bdrift X := by
  classical
  obtain ⟨Y, hYcont, hYmod⟩ :=
    exists_continuous_modification_stochasticIntegralBrownian W ℱ hℱ H hm hp hq hC0 hCH
  obtain ⟨N, hNmeas, hNzero, hNcont⟩ := exists_measurable_null_of_ae hYcont
  -- `ℱ t` contains `ℱ 0` at every time
  have hle0 : ∀ t : ℝ, ℱ 0 ≤ ℱ t := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact ℱ.mono ht
    · exact hℱ0 t ht.le
  have hNm : ∀ t : ℝ, MeasurableSet[ℱ t] N := fun t =>
    hle0 t N (hnull N ⟨N, hNmeas, hNzero, Set.Subset.rfl⟩)
  -- the Kolmogorov modification is adapted once the null sets are in the filtration
  have hYadapt : ∀ u : ℝ, 0 ≤ u → Measurable[ℱ u] (Y u) := by
    intro u hu
    have hnullu : ∀ s : Set Ω, (∃ N, MeasurableSet N ∧ P N = 0 ∧ s ⊆ N) →
        MeasurableSet[ℱ u] s := fun s hs => ℱ.mono hu _ (hnull s hs)
    have hSI : Measurable[ℱ u] (stochasticIntegralBrownian W ℱ hℱ H hm hp hq u) :=
      (stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq u).measurable
    exact measurable_of_ae_eq_of_null_mem ℱ u hnullu hSI (hYmod u hu)
  have hYt : ∀ t : ℝ, Measurable[ℱ t] fun ω => Y (max t 0) ω := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · rw [max_eq_left ht]
      exact hYadapt t ht
    · rw [max_eq_right ht.le]
      exact fun A hA => hle0 t _ (hYadapt 0 le_rfl hA)
  refine ⟨fun t ω => if ω ∈ N then 0 else X₀ ω
      + (∫ s in Set.Icc (0 : ℝ) t, bdrift ω s ∂volume) + Y (max t 0) ω, ?_, ?_, ?_⟩
  · intro ω
    by_cases hω : ω ∈ N
    · simpa [hω] using continuous_const
    · simp only [hω, if_false]
      refine (continuous_const.add
        (continuous_setIntegral_Icc (Measurable.of_uncurry_left hbm) hB0 (hB ω))).add ?_
      exact (hNcont ω hω).comp (continuous_id.max continuous_const)
  · intro t
    refine Measurable.stronglyMeasurable ?_
    refine Measurable.ite (hNm t) measurable_const ?_
    refine Measurable.add (Measurable.add ?_ ?_) (hYt t)
    · exact fun A hA => hle0 t _ (hX₀ hA)
    · exact ((hbp.stronglyMeasurable_setIntegral measurableSet_Icc
        Set.Icc_subset_Iic_self volume).mono le_rfl).measurable
  · intro t ht
    filter_upwards [hYmod t ht,
      MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω hωN
    rw [if_neg hωN, max_eq_left ht, hω]
    rfl

end Exists

end LevyStochCalc.Brownian.Ito
