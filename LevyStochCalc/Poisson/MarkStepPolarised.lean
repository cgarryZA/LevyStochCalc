/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.MarkStepWeight

/-!
# The bilinear form of the `L²` isometry for mark-step integrands

For two adapted mark-step integrands `G, G'` on a common time grid, the expectation of the
product of their compensated integrals up to a time `t ≥ 0` is the expectation of the time-mark
integral of the product of the integrands,
`E[(∫_0^t ∫_E G dÑ)(∫_0^t ∫_E G' dÑ)] = E[∫_E ∫_0^t G(s, e) G'(s, e) ds ν(de)]`, and the same
identity holds for the integrals over the whole horizon. It comes from the isometry for a
difference applied to the pairs `G, G'` and `G, G'.neg`, together with the polarisation identity
`4 a a' = (a + a') ^ 2 - (a - a') ^ 2`. Splitting the nested integral of that identity into its
two halves uses the boundedness of a mark-step integrand and the finite intensity of its mark
sets.

## Main statements

* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_mul_at` — the bilinear identity up to a
  time `t ≥ 0`.
* `LevyStochCalc.Poisson.Compensated.MarkStep.integral_full_mul` — the bilinear identity for the
  integrals over the whole horizon.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

namespace MarkStep

section Polarisation

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- Integrability at each of the three levels of the nested integral
`∫_Ω ∫_E ∫_{[0, T]}`, for a jointly measurable function bounded by `C` and vanishing for marks
outside a set `S` of finite `ν`-measure. -/
private lemma triple_integrable {T : ℝ} (h : Ω → ℝ → E → ℝ)
    (hmeas : Measurable fun q : Ω × ℝ × E => h q.1 q.2.1 q.2.2)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ ω s e, |h ω s e| ≤ C)
    {S : Set E} (hS : MeasurableSet S) (hSfin : ν S ≠ ⊤)
    (hsupp : ∀ ω s e, e ∉ S → h ω s e = 0) :
    (∀ ω e, Integrable (fun s => h ω s e) (volume.restrict (Set.Icc (0 : ℝ) T)))
      ∧ (∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume) ν)
      ∧ Integrable (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume ∂ν) P := by
  classical
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hsm : ∀ ω e, Measurable fun s => h ω s e := fun ω e =>
    hmeas.comp (by fun_prop : Measurable fun s : ℝ => ((ω, s, e) : Ω × ℝ × E))
  have h1 : ∀ ω e, Integrable (fun s => h ω s e) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun ω e => Integrable.mono' (integrable_const C) (hsm ω e).aestronglyMeasurable
      (Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hC ω s e)
  obtain ⟨D, hD0, hDb⟩ : ∃ D : ℝ, 0 ≤ D
      ∧ ∀ ω e, ‖∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume‖ ≤ D := by
    refine ⟨C * (volume.restrict (Set.Icc (0 : ℝ) T)).real Set.univ,
      mul_nonneg hC0 measureReal_nonneg, fun ω e => ?_⟩
    exact norm_integral_le_of_norm_le_const
      (Filter.Eventually.of_forall fun s => by rw [Real.norm_eq_abs]; exact hC ω s e)
  have hDs : ∀ ω e, e ∉ S → (∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume) = 0 := by
    intro ω e he
    have hz : ∀ s, h ω s e = 0 := fun s => hsupp ω s e he
    simp only [hz, integral_zero]
  have hDm : Measurable fun q : Ω × E => ∫ s in Set.Icc (0 : ℝ) T, h q.1 s q.2 ∂volume := by
    have hr : Measurable fun p : (Ω × E) × ℝ => h p.1.1 p.2 p.1.2 :=
      hmeas.comp (by fun_prop : Measurable fun p : (Ω × E) × ℝ =>
        ((p.1.1, p.2, p.1.2) : Ω × ℝ × E))
    exact (hr.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))).measurable
  have hdom : Integrable (S.indicator fun _ => D) ν :=
    (integrable_indicator_iff hS).2 (integrableOn_const hSfin)
  have hpt : ∀ ω e, ‖∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume‖
      ≤ S.indicator (fun _ => D) e := by
    intro ω e
    by_cases he : e ∈ S
    · rw [Set.indicator_of_mem he]
      exact hDb ω e
    · rw [Set.indicator_of_notMem he, hDs ω e he, norm_zero]
  have h2 : ∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume) ν :=
    fun ω => Integrable.mono' hdom (hDm.comp measurable_prodMk_left).aestronglyMeasurable
      (Filter.Eventually.of_forall (hpt ω))
  refine ⟨h1, h2, Integrable.mono' (integrable_const (D * (ν S).toReal))
    ((hDm.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω => ?_)⟩
  calc ‖∫ e, ∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume ∂ν‖
      ≤ ∫ e, ‖∫ s in Set.Icc (0 : ℝ) T, h ω s e ∂volume‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ e, S.indicator (fun _ => D) e ∂ν := integral_mono (h2 ω).norm hdom (hpt ω)
    _ = D * (ν S).toReal := by
        rw [integral_indicator hS, setIntegral_const, smul_eq_mul, mul_comm, measureReal_def]

variable (N : PoissonRandomMeasure P ν) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  (hℱ : IsPoissonFiltration N ℱ) (G G' : MarkStep Ω E ν g)

include hℱ in
/-- The expectation of the product of the compensated integrals of two adapted mark-step
integrands on a common grid, up to a time `t ≥ 0`, is the expectation of the time-mark integral
of the product of the integrands. -/
theorem integral_mul_at (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, G.integral N t ω * G'.integral N t ω ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          G.eval s e ω * G'.eval s e ω ∂volume ∂ν) ∂P := by
  classical
  -- the two isometries, for the sum and for the difference
  have hminus := integral_sub_sq_at N hℱ G G' hG hG' ht
  have hplus := integral_sub_sq_at N hℱ G G'.neg hG hG'.neg ht
  simp only [integral_neg, eval_neg, sub_neg_eq_add] at hplus
  -- the left-hand sides combine by polarisation
  have hiA : Integrable (fun ω => (G.integral N t ω + G'.integral N t ω) ^ 2) P := by
    have h := (memLp_integral N (G.append G') t).integrable_sq
    simp only [integral_append] at h
    exact h
  have hiD : Integrable (fun ω => (G.integral N t ω - G'.integral N t ω) ^ 2) P := by
    have h := (memLp_integral N (G.append G'.neg) t).integrable_sq
    simp only [integral_append, integral_neg, ← sub_eq_add_neg] at h
    exact h
  have hlhs : ∫ ω, (G.integral N t ω + G'.integral N t ω) ^ 2 ∂P
      - ∫ ω, (G.integral N t ω - G'.integral N t ω) ^ 2 ∂P
      = 4 * ∫ ω, G.integral N t ω * G'.integral N t ω ∂P := by
    rw [← integral_sub hiA hiD, show (fun ω => (G.integral N t ω + G'.integral N t ω) ^ 2
        - (G.integral N t ω - G'.integral N t ω) ^ 2)
      = fun ω => 4 * (G.integral N t ω * G'.integral N t ω) from funext fun ω => by ring,
      integral_const_mul]
  -- the right-hand sides combine by splitting the nested integral
  obtain ⟨C₁, hC₁⟩ := G.eval_bounded
  obtain ⟨C₂, hC₂⟩ := G'.eval_bounded
  set S : Set E := (⋃ k, G.B k) ∪ ⋃ k, G'.B k with hSdef
  have hS : MeasurableSet S := G.measurableSet_iUnion_B.union G'.measurableSet_iUnion_B
  have hSfin : ν S ≠ ⊤ := ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨G.measure_iUnion_B_ne_top, G'.measure_iUnion_B_ne_top⟩)
    (measure_union_le _ _)
  have hzero : ∀ ω s e, e ∉ S → G.eval s e ω = 0 ∧ G'.eval s e ω = 0 := by
    intro ω s e he
    exact ⟨G.eval_support ω s e fun hk => he (Or.inl hk),
      G'.eval_support ω s e fun hk => he (Or.inr hk)⟩
  have hbound : ∀ (σ : ℝ), |σ| = 1 → ∀ ω s e,
      |(G.eval s e ω + σ * G'.eval s e ω) ^ 2| ≤ (|C₁| + |C₂|) ^ 2 := by
    intro σ hσ ω s e
    have h1 : |G.eval s e ω| ≤ |C₁| := (hC₁ ω s e).trans (le_abs_self _)
    have h2 : |σ * G'.eval s e ω| ≤ |C₂| := by
      rw [abs_mul, hσ, one_mul]
      exact (hC₂ ω s e).trans (le_abs_self _)
    have h3 : |G.eval s e ω + σ * G'.eval s e ω| ≤ |C₁| + |C₂| :=
      (abs_add_le _ _).trans (add_le_add h1 h2)
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (G.eval s e ω + σ * G'.eval s e ω),
      sq_abs (G.eval s e ω + σ * G'.eval s e ω), abs_nonneg C₁, abs_nonneg C₂]
  have hmeasG : Measurable fun q : Ω × ℝ × E => G.eval q.2.1 q.2.2 q.1 := G.eval_measurable
  have hmeasG' : Measurable fun q : Ω × ℝ × E => G'.eval q.2.1 q.2.2 q.1 := G'.eval_measurable
  obtain ⟨hp1, hp2, hp3⟩ := triple_integrable (T := t) (P := P)
    (fun ω s e => (G.eval s e ω + G'.eval s e ω) ^ 2)
    ((hmeasG.add hmeasG').pow_const 2) (sq_nonneg _)
    (fun ω s e => by simpa using hbound 1 (by norm_num) ω s e) hS hSfin
    (fun ω s e he => by
      obtain ⟨ha, hb⟩ := hzero ω s e he
      rw [ha, hb]; ring)
  obtain ⟨hm1, hm2, hm3⟩ := triple_integrable (T := t) (P := P)
    (fun ω s e => (G.eval s e ω - G'.eval s e ω) ^ 2)
    ((hmeasG.sub hmeasG').pow_const 2) (sq_nonneg _)
    (fun ω s e => by
      have h := hbound (-1) (by norm_num) ω s e
      simpa [sub_eq_add_neg] using h) hS hSfin
    (fun ω s e he => by
      obtain ⟨ha, hb⟩ := hzero ω s e he
      rw [ha, hb]; ring)
  have hp1' : ∀ ω e, Integrable (fun s => (G.eval s e ω + G'.eval s e ω) ^ 2)
    (volume.restrict (Set.Icc (0 : ℝ) t)) := hp1
  have hp2' : ∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω + G'.eval s e ω) ^ 2 ∂volume) ν := hp2
  have hp3' : Integrable (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω + G'.eval s e ω) ^ 2 ∂volume ∂ν) P := hp3
  have hm1' : ∀ ω e, Integrable (fun s => (G.eval s e ω - G'.eval s e ω) ^ 2)
    (volume.restrict (Set.Icc (0 : ℝ) t)) := hm1
  have hm2' : ∀ ω, Integrable (fun e => ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume) ν := hm2
  have hm3' : Integrable (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) t,
    (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume ∂ν) P := hm3
  have hrhs : (∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
        (G.eval s e ω + G'.eval s e ω) ^ 2 ∂volume ∂ν) ∂P)
      - ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
        (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume ∂ν) ∂P
      = 4 * ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
        G.eval s e ω * G'.eval s e ω ∂volume ∂ν) ∂P := by
    rw [← integral_sub hp3' hm3', ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only []
    rw [← integral_sub (hp2' ω) (hm2' ω), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
    simp only []
    rw [← integral_sub (hp1' ω e) (hm1' ω e), ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
    simp only []
    ring
  rw [hplus, hminus] at hlhs
  rw [hrhs] at hlhs
  linarith [hlhs]

include hℱ in
/-- The expectation of the product of the compensated integrals of two adapted mark-step
integrands on a common grid, over the whole horizon, is the expectation of the time-mark integral
of the product of the integrands. -/
theorem integral_full_mul (hG : G.Adapted ℱ) (hG' : G'.Adapted ℱ) {T : ℝ}
    (hT : g.horizon ≤ T) :
    ∫ ω, G.full N ω * G'.full N ω ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
          G.eval s e ω * G'.eval s e ω ∂volume ∂ν) ∂P := by
  have hT0 : 0 ≤ T := g.horizon_nonneg.trans hT
  have h := integral_mul_at N hℱ G G' hG hG' hT0
  simp only [G.integral_eq_full_of_horizon_le N hT, G'.integral_eq_full_of_horizon_le N hT] at h
  exact h

end Polarisation

end MarkStep

end LevyStochCalc.Poisson.Compensated
