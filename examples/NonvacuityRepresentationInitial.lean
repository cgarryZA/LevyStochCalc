/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc

/-!
# Martingale representation with a random initial value

On `Ω × ℝ` under `P ⊗ 𝒩(0, 1)`, a `d`-dimensional Brownian motion read off the first coordinate
is independent of the σ-algebra `𝒢₀ = σ(Prod.snd)` of the second coordinate, so the hypotheses
of the representation theorem over the augmentation of `𝒢₀ ⊔ ℱ^W` hold. The second coordinate
`ξ = Prod.snd` is square integrable and measurable at every time; its representation
`ξ = 𝔼[ξ | ℱ₀] + ∫₀ᵀ G dW` has an initial term that is not almost surely constant. Over a trivial
initial σ-algebra the initial term is the constant `𝔼 ξ`, so the theorem is used here with
genuinely random initial information. The product `1_{ξ > 0} · W⁰_T` of a bounded
`𝒢₀`-measurable weight and a Brownian value also satisfies the hypotheses.

## Main statements

* `indep_comap_snd_iSup_naturalFiltration_comap_fst`: the independence hypothesis.
* `exists_representation_snd`: the representation of `Prod.snd`, with an initial term that is
  not almost surely constant.
* `exists_representation_mul_brownian`: the representation of `1_{ξ > 0} · W⁰_T`.
* `exists_representation_random_initial`: the same on a probability space that exists for every
  `d`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.Brownian.Multidim (MultidimBrownianMotion)
open LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
open LevyStochCalc.Brownian.Ito (HorizonIntegrand)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The Brownian motion on `Ω × ℝ` read off the first coordinate. -/
noncomputable abbrev fstBM (W : MultidimBrownianMotion P d) :
    MultidimBrownianMotion (P.prod (gaussianReal 0 1)) d :=
  W.comap (measurePreserving_fst (μ := P) (ν := gaussianReal 0 1))

/-- The σ-algebra of the second coordinate. -/
abbrev sndSigma (Ω : Type u) [MeasurableSpace Ω] : MeasurableSpace (Ω × ℝ) :=
  MeasurableSpace.comap Prod.snd inferInstance

theorem sndSigma_le : sndSigma Ω ≤ (inferInstance : MeasurableSpace (Ω × ℝ)) :=
  measurable_snd.comap_le

/-- The second coordinate is independent of the natural filtration of the Brownian motion read
off the first coordinate. -/
theorem indep_comap_snd_iSup_naturalFiltration_comap_fst (W : MultidimBrownianMotion P d) :
    Indep (sndSigma Ω) (⨆ t, (fstBM W).naturalFiltration t) (P.prod (gaussianReal 0 1)) := by
  have hprod : Indep (sndSigma Ω) (MeasurableSpace.comap (Prod.fst : Ω × ℝ → Ω) inferInstance)
      (P.prod (gaussianReal 0 1)) :=
    (indepFun_prod (μ := P) (ν := gaussianReal 0 1) (X := id) (Y := id) measurable_id
      measurable_id).symm
  refine indep_of_indep_of_le_right hprod (iSup_le fun t => ?_)
  rw [naturalFiltration_comap]
  exact MeasurableSpace.comap_mono (W.naturalFiltration.le t)

/-- **The representation of a random initial value.** `Prod.snd = 𝔼[Prod.snd | ℱ₀] + ∫₀ᵀ G dW`
over the augmentation of `σ(Prod.snd) ⊔ ℱ^W`, and the initial term is not almost surely
constant. -/
theorem exists_representation_snd (W : MultidimBrownianMotion P d) {T : ℝ} (hT : 0 < T) :
    ∃ G : ∀ _ : Fin d, HorizonIntegrand (P.prod (gaussianReal 0 1))
        ((fstBM W).augInitialFiltration (sndSigma Ω) sndSigma_le) T,
      (Prod.snd : Ω × ℝ → ℝ) =ᵐ[P.prod (gaussianReal 0 1)] (fun ω =>
        (P.prod (gaussianReal 0 1))[Prod.snd |
          (fstBM W).augInitialFiltration (sndSigma Ω) sndSigma_le 0] ω
        + vectorIntegral (fstBM W) ((fstBM W).isBrownianFiltration_augInitial sndSigma_le
          (indep_comap_snd_iSup_naturalFiltration_comap_fst W)) G ω) ∧
      ¬ ∃ c : ℝ, (P.prod (gaussianReal 0 1))[Prod.snd |
          (fstBM W).augInitialFiltration (sndSigma Ω) sndSigma_le 0]
        =ᵐ[P.prod (gaussianReal 0 1)] fun _ => c := by
  set ℱ := (fstBM W).augInitialFiltration (sndSigma Ω) sndSigma_le with hℱ
  have hsm : ∀ t, StronglyMeasurable[ℱ t] (Prod.snd : Ω × ℝ → ℝ) := fun t =>
    (Measurable.of_comap_le (le_refl (sndSigma Ω)) :
      Measurable[sndSigma Ω] (Prod.snd : Ω × ℝ → ℝ)).stronglyMeasurable.mono
      ((fstBM W).le_augFiltration_initialFiltration sndSigma_le t)
  have h2 := Driver.memLp_snd_prod_gaussianReal (P := P) 0 1
  obtain ⟨G, hG⟩ := exists_vectorIntegral_augInitial (fstBM W) sndSigma_le
    (indep_comap_snd_iSup_naturalFiltration_comap_fst W) hT h2 (hsm T).aestronglyMeasurable
  refine ⟨G, hG, ?_⟩
  rintro ⟨c, hc⟩
  have hce : (P.prod (gaussianReal 0 1))[Prod.snd | ℱ 0] = Prod.snd :=
    condExp_of_stronglyMeasurable (ℱ.le 0) (hsm 0) (h2.integrable (by norm_num))
  rw [hce] at hc
  exact Driver.not_ae_const_snd_prod_gaussianReal (P := P) one_ne_zero ⟨c, hc⟩

/-- The weight `1_{ξ > 0}` of the second coordinate. -/
noncomputable abbrev sndPos (Ω : Type u) : Ω × ℝ → ℝ :=
  fun ω => (Set.Ioi (0 : ℝ)).indicator (fun _ => (1 : ℝ)) ω.2

/-- **A random weight times a Brownian value.** For `d ≥ 1`, `1_{ξ > 0} · W⁰_T` is square
integrable and measurable at time `T` for the augmentation of `σ(Prod.snd) ⊔ ℱ^W`, so it is
`𝔼[· | ℱ₀]` plus a sum of Itô integrals on `[0, T]`. -/
theorem exists_representation_mul_brownian (W : MultidimBrownianMotion P (d + 1)) {T : ℝ}
    (hT : 0 < T) :
    ∃ G : ∀ _ : Fin (d + 1), HorizonIntegrand (P.prod (gaussianReal 0 1))
        ((fstBM W).augInitialFiltration (sndSigma Ω) sndSigma_le) T,
      (fun ω => sndPos Ω ω * ((fstBM W).W 0).W T ω) =ᵐ[P.prod (gaussianReal 0 1)] fun ω =>
        (P.prod (gaussianReal 0 1))[fun ω => sndPos Ω ω * ((fstBM W).W 0).W T ω |
          (fstBM W).augInitialFiltration (sndSigma Ω) sndSigma_le 0] ω
        + vectorIntegral (fstBM W) ((fstBM W).isBrownianFiltration_augInitial sndSigma_le
          (indep_comap_snd_iSup_naturalFiltration_comap_fst W)) G ω := by
  set ℱ := (fstBM W).augInitialFiltration (sndSigma Ω) sndSigma_le with hℱ
  have hcoord := (fstBM W).isBrownianFiltration_augInitial sndSigma_le
    (indep_comap_snd_iSup_naturalFiltration_comap_fst W)
  have hηm : Measurable[ℱ T] (sndPos Ω) := by
    have hm : Measurable[sndSigma Ω] (sndPos Ω) :=
      (measurable_const.indicator measurableSet_Ioi).comp
        (Measurable.of_comap_le (le_refl (sndSigma Ω)) :
      Measurable[sndSigma Ω] (Prod.snd : Ω × ℝ → ℝ))
    exact hm.mono ((fstBM W).le_augFiltration_initialFiltration sndSigma_le T) le_rfl
  have hWm : Measurable[ℱ T] (((fstBM W).W 0).W T) := (hcoord 0).measurable T
  have hW2 : MemLp (((fstBM W).W 0).W T) 2 (P.prod (gaussianReal 0 1)) := by
    refine (memLp_two_increment_of_le ((fstBM W).W 0) le_rfl hT.le).ae_eq ?_
    filter_upwards [((fstBM W).W 0).initial_zero] with ω e
    rw [e, sub_zero]
  have hξm : Measurable[ℱ T] fun ω => sndPos Ω ω * ((fstBM W).W 0).W T ω := hηm.mul hWm
  have hξ2 : MemLp (fun ω => sndPos Ω ω * ((fstBM W).W 0).W T ω) 2
      (P.prod (gaussianReal 0 1)) := by
    refine hW2.of_le (hξm.mono (ℱ.le T) le_rfl).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul]
    refine mul_le_of_le_one_left (abs_nonneg _) ?_
    by_cases h : ω.2 ∈ Set.Ioi (0 : ℝ)
    · simp [sndPos, Set.indicator_of_mem h]
    · simp [sndPos, Set.indicator_of_notMem h]
  exact exists_vectorIntegral_augInitial (fstBM W) sndSigma_le
    (indep_comap_snd_iSup_naturalFiltration_comap_fst W) hT hξ2
    hξm.stronglyMeasurable.aestronglyMeasurable

/-- **Non-vacuity on an existing probability space.** For every `d`, some probability space
carries a `d`-dimensional Brownian motion `W` and a σ-algebra `𝒢₀` independent of it, together
with a square-integrable variable whose representation over the augmentation of `𝒢₀ ⊔ ℱ^W` has
an initial term that is not almost surely constant. -/
theorem exists_representation_random_initial (d : ℕ) {T : ℝ} (hT : 0 < T) :
    ∃ (Ω' : Type u) (𝒢 : MeasurableSpace Ω') (_ : MeasurableSpace Ω') (P' : Measure Ω')
      (_ : IsProbabilityMeasure P') (W' : MultidimBrownianMotion P' d) (h𝒢 : 𝒢 ≤ ‹_›)
      (hind : Indep 𝒢 (⨆ t, W'.naturalFiltration t) P') (ξ : Ω' → ℝ)
      (G : ∀ _ : Fin d, HorizonIntegrand P' (W'.augInitialFiltration 𝒢 h𝒢) T),
      MemLp ξ 2 P' ∧
      ξ =ᵐ[P'] (fun ω => P'[ξ | W'.augInitialFiltration 𝒢 h𝒢 0] ω
        + vectorIntegral W' (W'.isBrownianFiltration_augInitial h𝒢 hind) G ω) ∧
      ¬ ∃ c : ℝ, P'[ξ | W'.augInitialFiltration 𝒢 h𝒢 0] =ᵐ[P'] fun _ => c := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, ⟨W₀⟩⟩ := MultidimBrownianMotion.exists.{u} d
  obtain ⟨G, hG, hne⟩ := exists_representation_snd W₀ hT
  exact ⟨Ω₀ × ℝ, sndSigma Ω₀, inferInstance, P₀.prod (gaussianReal 0 1), inferInstance,
    fstBM W₀, sndSigma_le, indep_comap_snd_iSup_naturalFiltration_comap_fst W₀, Prod.snd, G,
    Driver.memLp_snd_prod_gaussianReal 0 1, hG, hne⟩

end LevyStochCalc.Examples.Nonvacuity
