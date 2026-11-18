/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.FiniteHorizonIncrements
import LevyStochCalc.Ito.SecondMomentToolkit

/-!
# Square-integrable drifts on a finite window

For a drift `f : ℝ → Ω → E` with values in a complete real inner product space, square integrable
for the product of a measure `P` and Lebesgue measure on the window `[0, t]`, the time integral
`∫_0^t f_s ds` is square integrable, and so is the running integral `(ω, s) ↦ ∫_0^s f_r(ω) dr`
for the product measure when `f` is strongly measurable. The pairing of the time integral against
a square-integrable variable `ξ` is the time integral of the pairings,
`𝔼⟪∫_0^t f_s ds, ξ⟫ = ∫_0^t 𝔼⟪f_s, ξ⟫ ds`.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Pairing

/-- A square-integrable variable, read at the sample point, is square integrable for the product
measure with a bounded window. -/
theorem memLp_comp_fst [IsFiniteMeasure P] {ξ : Ω → E} (hξ : MemLp ξ 2 P) (t : ℝ) :
    MemLp (fun p : Ω × ℝ => ξ p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
  (LevyStochCalc.Ito.SecondMoment.memLp_two_prod_fst hξ.norm (T := t)).of_le
    (hξ.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
    (Eventually.of_forall fun p => (norm_norm (ξ p.1)).ge)

/-- Square integrability for the product measure with a window passes to a shorter window. -/
theorem memLp_prod_Icc_mono [IsFiniteMeasure P] {F : Ω × ℝ → E} {t T : ℝ} (htT : t ≤ T)
    (hF : MemLp F 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))) :
    MemLp F 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
  hF.mono_measure (Measure.prod_mono le_rfl
    (Measure.restrict_mono (Set.Icc_subset_Icc le_rfl htT) le_rfl))

/-- The pairing of a function on a measure space against a constant, under the integral. -/
theorem integral_inner_const_right {μ : Measure ℝ} {u : ℝ → E} (hu : Integrable u μ) (c : E) :
    ∫ r, ⟪u r, c⟫ ∂μ = ⟪∫ r, u r ∂μ, c⟫ := by
  calc ∫ r, ⟪u r, c⟫ ∂μ = ∫ r, ⟪c, u r⟫ ∂μ :=
        integral_congr_ae (Eventually.of_forall fun r => real_inner_comm _ _)
    _ = ⟪c, ∫ r, u r ∂μ⟫ := integral_inner hu c
    _ = ⟪∫ r, u r ∂μ, c⟫ := real_inner_comm _ _

/-- A square-integrable drift on a window is integrable on the window along almost every
sample path. -/
theorem ae_integrableOn_of_memLp [IsFiniteMeasure P] {f : ℝ → Ω → E} {t : ℝ}
    (hf : MemLp (fun p : Ω × ℝ => f p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))) :
    ∀ᵐ ω ∂P, IntegrableOn (fun s => f s ω) (Set.Icc (0 : ℝ) t) :=
  (hf.integrable one_le_two).prod_right_ae

/-- **The pairing of a time integral against a square-integrable variable is the time integral
of the pairings.** -/
theorem integral_inner_setIntegral [IsFiniteMeasure P] {f : ℝ → Ω → E} {t : ℝ}
    (hf : MemLp (fun p : Ω × ℝ => f p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))))
    {ξ : Ω → E} (hξ : MemLp ξ 2 P) :
    ∫ ω, ⟪∫ s in Set.Icc (0 : ℝ) t, f s ω, ξ ω⟫ ∂P
      = ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, ⟪f s ω, ξ ω⟫ ∂P := by
  have hint : Integrable (fun p : Ω × ℝ => ⟪f p.2 p.1, ξ p.1⟫)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
    integrable_inner_of_memLp hf (memLp_comp_fst hξ t)
  calc ∫ ω, ⟪∫ s in Set.Icc (0 : ℝ) t, f s ω, ξ ω⟫ ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, ⟪f s ω, ξ ω⟫ ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [ae_integrableOn_of_memLp hf] with ω hω
        exact (integral_inner_const_right hω (ξ ω)).symm
    _ = ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, ⟪f s ω, ξ ω⟫ ∂P :=
        integral_integral_swap (f := fun ω s => ⟪f s ω, ξ ω⟫) hint

/-- The pairing of a square-integrable variable against a time integral. -/
theorem integral_inner_setIntegral' [IsFiniteMeasure P] {f : ℝ → Ω → E} {t : ℝ}
    (hf : MemLp (fun p : Ω × ℝ => f p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))))
    {ξ : Ω → E} (hξ : MemLp ξ 2 P) :
    ∫ ω, ⟪ξ ω, ∫ s in Set.Icc (0 : ℝ) t, f s ω⟫ ∂P
      = ∫ s in Set.Icc (0 : ℝ) t, ∫ ω, ⟪ξ ω, f s ω⟫ ∂P := by
  have e1 : ∫ ω, ⟪ξ ω, ∫ s in Set.Icc (0 : ℝ) t, f s ω⟫ ∂P
      = ∫ ω, ⟪∫ s in Set.Icc (0 : ℝ) t, f s ω, ξ ω⟫ ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => real_inner_comm _ _)
  rw [e1, integral_inner_setIntegral hf hξ]
  refine integral_congr_ae (Eventually.of_forall fun s => ?_)
  exact integral_congr_ae (Eventually.of_forall fun ω => real_inner_comm _ _)

end Pairing

section Running

/-- The running integral `∫_0^s f_r dr`, written as an integral over the fixed window `[0, t]` so
that it is jointly measurable in the sample point and the time. -/
noncomputable def runningIntegral (f : ℝ → Ω → E) (t : ℝ) (p : Ω × ℝ) : E :=
  ∫ r in Set.Icc (0 : ℝ) t, (Set.Iic p.2).indicator (fun r => f r p.1) r

variable {f : ℝ → Ω → E} {t : ℝ}

omit [CompleteSpace E] in
theorem Iic_inter_Icc_eq {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) :
    Set.Iic s ∩ Set.Icc (0 : ℝ) t = Set.Icc (0 : ℝ) s := by
  ext r
  simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2, _⟩
    exact ⟨h2, h1⟩
  · rintro ⟨h2, h1⟩
    exact ⟨h1, h2, h1.trans hs.2⟩

theorem runningIntegral_eq {ω : Ω} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t) :
    runningIntegral f t (ω, s) = ∫ r in Set.Icc (0 : ℝ) s, f r ω := by
  rw [runningIntegral, integral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Iic_inter_Icc_eq hs]

theorem stronglyMeasurable_runningIntegral
    (hf : StronglyMeasurable fun p : Ω × ℝ => f p.2 p.1) :
    StronglyMeasurable (runningIntegral f t) := by
  have hfun : (fun q : (Ω × ℝ) × ℝ => (Set.Iic q.1.2).indicator (fun r => f r q.1.1) q.2)
      = {q : (Ω × ℝ) × ℝ | q.2 ≤ q.1.2}.indicator fun q => f q.2 q.1.1 := by
    funext q
    by_cases hq : q.2 ≤ q.1.2 <;> simp [Set.indicator, hq]
  have hm : StronglyMeasurable fun q : (Ω × ℝ) × ℝ =>
      (Set.Iic q.1.2).indicator (fun r => f r q.1.1) q.2 := by
    rw [hfun]
    exact (hf.comp_measurable (measurable_fst.fst.prodMk measurable_snd)).indicator
      (measurableSet_le measurable_snd measurable_fst.snd)
  exact hm.integral_prod_right'

/-- Along a path integrable on the window, the running integral is bounded by the total
variation `∫_0^t ‖f_r‖ dr` of the path. -/
theorem norm_runningIntegral_le {ω : Ω} (hω : IntegrableOn (fun r => f r ω) (Set.Icc (0 : ℝ) t))
    (s : ℝ) :
    ‖runningIntegral f t (ω, s)‖ ≤ ∫ r in Set.Icc (0 : ℝ) t, ‖f r ω‖ := by
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun r => norm_nonneg _) hω.norm
    (Eventually.of_forall fun r => ?_)
  exact norm_indicator_le_norm_self (fun r => f r ω) r

/-- The total variation of a square-integrable drift on a window is square integrable. -/
theorem memLp_integral_norm [IsFiniteMeasure P] (hf : StronglyMeasurable fun p : Ω × ℝ => f p.2 p.1)
    (hf2 : MemLp (fun p : Ω × ℝ => f p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))))
    (ht : 0 ≤ t) :
    MemLp (fun ω => ∫ r in Set.Icc (0 : ℝ) t, ‖f r ω‖) 2 P := by
  have hm : Measurable (Function.uncurry fun ω s => ‖f s ω‖) := hf.norm.measurable
  have hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖‖f s ω‖‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    have h := LevyStochCalc.Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hf2.norm
    rwa [lintegral_prod _ (hm.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable] at h
  exact LevyStochCalc.Ito.SecondMoment.memLp_two_setIntegral hm ht hq

/-- **The time integral of a square-integrable drift is square integrable.** -/
theorem memLp_setIntegral [IsFiniteMeasure P] (hf : StronglyMeasurable fun p : Ω × ℝ => f p.2 p.1)
    (hf2 : MemLp (fun p : Ω × ℝ => f p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))))
    (ht : 0 ≤ t) :
    MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) t, f s ω) 2 P := by
  have hfun : (fun ω => ∫ s in Set.Icc (0 : ℝ) t, f s ω) = fun ω => runningIntegral f t (ω, t) :=
    funext fun ω => (runningIntegral_eq ⟨ht, le_rfl⟩).symm
  refine (memLp_integral_norm hf hf2 ht).of_le ?_ (Eventually.of_forall fun ω => ?_)
  · rw [hfun]
    exact ((stronglyMeasurable_runningIntegral hf).comp_measurable
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (integral_nonneg fun r => norm_nonneg _)]
    exact norm_integral_le_integral_norm _

/-- **The running integral of a square-integrable drift is square integrable for the product
measure on the window.** -/
theorem memLp_runningIntegral [IsFiniteMeasure P]
    (hf : StronglyMeasurable fun p : Ω × ℝ => f p.2 p.1)
    (hf2 : MemLp (fun p : Ω × ℝ => f p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))))
    (ht : 0 ≤ t) :
    MemLp (runningIntegral f t) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  refine (LevyStochCalc.Ito.SecondMoment.memLp_two_prod_fst (memLp_integral_norm hf hf2 ht)
    (T := t)).of_le
    (stronglyMeasurable_runningIntegral hf).aestronglyMeasurable ?_
  have h := Measure.quasiMeasurePreserving_fst (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) t)) |>.ae (ae_integrableOn_of_memLp hf2)
  filter_upwards [h] with p hp
  rw [Real.norm_of_nonneg (integral_nonneg fun r => norm_nonneg _)]
  exact norm_runningIntegral_le hp p.2

end Running

end LevyStochCalc.Ito.FiniteHorizon
