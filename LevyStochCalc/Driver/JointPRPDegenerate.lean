/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointPRP
import LevyStochCalc.Brownian.PRPBrownian

/-!
# The degenerate cases of the joint representation

Without Brownian coordinates the joint filtration is the Poisson one and the representation is
the compensated integral alone; without marks the Poisson random measure carries no information
and the representation is the Brownian one alone. Splitting on the two cases removes the
implementation hypotheses `0 < d` and `Nonempty E` from the representation theorem.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

section Trivial

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- With no marks the Poisson random measure generates nothing. -/
theorem naturalFiltration_poisson_eq_bot [IsEmpty E] (N : Poisson.PoissonRandomMeasure P ν)
    (t : ℝ) : Poisson.naturalFiltration N t = ⊥ := by
  refine le_bot_iff.mp (iSup₂_le fun B _ => ?_)
  have hconst : (fun ω => N.N ω B) = fun _ => (0 : ℝ≥0∞) := by
    funext ω
    rw [Set.eq_empty_of_isEmpty B]
    simp
  rw [hconst]
  have hm : Measurable[(⊥ : MeasurableSpace Ω)] fun _ : Ω => (0 : ℝ≥0∞) := measurable_const
  exact hm.comap_le

/-- With no coordinates the Brownian motion generates nothing. -/
theorem naturalFiltration_brownian_eq_bot
    (W : Brownian.Multidim.MultidimBrownianMotion P 0) (t : ℝ) :
    W.naturalFiltration t = ⊥ := by
  rw [naturalFiltration_apply]
  exact iSup_of_empty _

end Trivial

section Degenerate

/-- **The representation with no Brownian coordinates.** -/
theorem exists_jointIntegral_augFiltration_of_dim_zero (D : LevyDriver.{u, v, w} P 0 ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin 0, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  have hfe : Brownian.augFiltration D.filtration P T
      = Probability.aug (Poisson.naturalFiltration D.N T) ‹MeasurableSpace Ω› P := by
    change Probability.aug (D.filtration (max T 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left hT.le, filtration_apply, naturalFiltration_brownian_eq_bot, bot_sup_eq]
  refine exists_jointIntegral_of_mean_zero (fun k => D.isBrownianFiltration_aug k)
    D.isPoissonFiltration_aug (LevyDriver.crossWitness D).aug hT ?_ hZ2 hZm hZ0
  intro r hr2 hrm hr0 _ hrN
  exact Poisson.ae_eq_zero_of_integral_mul_compensated_eq_zero D.N D.isPoissonFiltration_aug hT
    (le_of_eq hfe) hr2 hrm hr0 hrN

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **The representation with no marks.** -/
theorem exists_jointIntegral_augFiltration_of_isEmpty [IsEmpty E] (D : LevyDriver.{u, v, w} P d ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  have hfe : Brownian.augFiltration D.filtration P T
      = Probability.aug (D.W.naturalFiltration T) ‹MeasurableSpace Ω› P := by
    change Probability.aug (D.filtration (max T 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left hT.le, filtration_apply, naturalFiltration_poisson_eq_bot, sup_bot_eq]
  refine exists_jointIntegral_of_mean_zero (fun k => D.isBrownianFiltration_aug k)
    D.isPoissonFiltration_aug (LevyDriver.crossWitness D).aug hT ?_ hZ2 hZm hZ0
  intro r hr2 hrm hr0 hrB _
  obtain ⟨r₁, hr₁m, hrr₁⟩ := hrm
  rw [hfe] at hr₁m
  obtain ⟨Y, hYm, hY⟩ := Probability.aestronglyMeasurable_of_stronglyMeasurable_aug hr₁m
  have hrY : r =ᵐ[P] Y := hrr₁.trans hY
  have hY2 : MemLp Y 2 P := hr2.ae_eq hrY
  have hY0 : ∫ ω, Y ω ∂P = 0 := by rw [← integral_congr_ae hrY]; exact hr0
  have hYmeas : Measurable Y := (hYm.mono (D.W.naturalFiltration.le T)).measurable
  have hYB : ∀ (i : Fin d) (G : HorizonIntegrand P (Brownian.augFiltration D.filtration P) T),
      ∫ ω, Y ω * G.integral (D.W.W i) (D.isBrownianFiltration_aug i) ω ∂P = 0 := by
    intro i G
    rw [← hrB i G]
    refine integral_congr_ae ?_
    filter_upwards [hrY] with ω e
    simp only [e]
  have hYaug : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Y P :=
    (hYm.mono ((D.naturalFiltration_brownian_le T).trans
      (Brownian.le_augFiltration D.filtration P T))).aestronglyMeasurable
  have hYc2 : MemLp (fun ω => ((Y ω : ℝ) : ℂ)) 2 P := by
    refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hY2.1, ?_⟩
    rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => Complex.norm_real (Y ω))]
    exact hY2.2
  have hYc0 : ∫ ω, ((Y ω : ℝ) : ℂ) ∂P = 0 := by
    rw [integral_complex_ofReal, hY0, Complex.ofReal_zero]
  have hperp : ∀ i : Fin d, PerpItoIntegrals (D.W.W i) (Brownian.augFiltration D.filtration P)
      (D.isBrownianFiltration_aug i) fun ω => ((Y ω : ℝ) : ℂ) := by
    intro i
    refine ⟨fun K hm hp hq t ht => ?_⟩
    have hreal := integral_mul_stochasticIntegral_eq_zero (D.W.W i)
      (D.isBrownianFiltration_aug i) hT hY2 hYaug (hYB i) K hm hp hq ht
    have hcast : (fun ω => ((Y ω : ℝ) : ℂ) * ((stochasticIntegralBrownian (D.W.W i)
          (Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ))
        = fun ω => ((Y ω * stochasticIntegralBrownian (D.W.W i)
          (Brownian.augFiltration D.filtration P) (D.isBrownianFiltration_aug i)
          K hm hp hq t ω : ℝ) : ℂ) := by
      funext ω
      rw [Complex.ofReal_mul]
    rw [hcast, integral_complex_ofReal, hreal, Complex.ofReal_zero]
  have hzero := ae_eq_zero_of_perpItoIntegrals D.W (Brownian.augFiltration D.filtration P)
    (fun k => D.isBrownianFiltration_aug k) (fun hc => D.isBrownianFiltration_combineBM_aug hc)
    (fun _ ht => D.augFiltration_le_of_nonpos ht)
    (fun _ hs h0 => D.measurableSet_augFiltration_of_null hs h0)
    (Complex.measurable_ofReal.comp hYmeas) hYc2 hperp hYc0
    (Complex.continuous_ofReal.comp_stronglyMeasurable hYm)
  refine hrY.trans ?_
  filter_upwards [hzero] with ω hω
  have hc : ((Y ω : ℝ) : ℂ) = 0 := hω
  exact_mod_cast hc

/-- **The predictable representation property of a Lévy driver, in every case.** -/
theorem exists_jointIntegral_augFiltration_of_mean_zero (D : LevyDriver.{u, v, w} P d ν)
    {T : ℝ} (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P (Brownian.augFiltration D.filtration P) T)
      (K : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T),
      Z =ᵐ[P] jointIntegral (fun k => D.isBrownianFiltration_aug k)
        D.isPoissonFiltration_aug G K := by
  rcases isEmpty_or_nonempty E with hE | hE
  · exact exists_jointIntegral_augFiltration_of_isEmpty D hT hZ2 hZm hZ0
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · exact exists_jointIntegral_augFiltration_of_dim_zero D hT hZ2 hZm hZ0
    · exact exists_jointIntegral_augFiltration D hd hT hZ2 hZm hZ0

end Degenerate

end LevyDriver

end LevyStochCalc.Driver
