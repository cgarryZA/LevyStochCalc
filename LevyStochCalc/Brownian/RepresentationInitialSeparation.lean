/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.InitialFiltration
import LevyStochCalc.Brownian.HorizonFiltrationChange
import LevyStochCalc.Brownian.HorizonPullOut
import LevyStochCalc.Brownian.PRPMultidimAssembly
import LevyStochCalc.Probability.SupDensity

/-!
# Separation over the Brownian filtration with initial information

Let `𝒢₀` be independent of a multidimensional Brownian motion `W` and `ℱ` the augmentation of
`𝒢₀ ⊔ ℱ^W`. A square-integrable `ℱ_T`-measurable weight `r` that integrates to zero over every set
of `𝒢₀` and is orthogonal to every coordinate Itô integral on `[0, T]` vanishes.

For `A ∈ 𝒢₀` and `B ∈ ℱ^W_T` the Brownian representation writes `1_B = P(B) + ∫₀ᵀ G dW` over the
augmented natural filtration; the integrands stay admissible for `ℱ`, and the initial weight `1_A`
passes inside the integrals, so `1_{A ∩ B} = P(B) 1_A + ∫₀ᵀ 1_A G dW`. Both terms are orthogonal to
`r`, so `r` integrates to zero over every `A ∩ B`, and these sets generate `𝒢₀ ⊔ ℱ^W_T`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {d : ℕ}

/-- **Separation over the filtration with initial information.** A square-integrable weight,
measurable at time `T` for the augmentation of `𝒢₀ ⊔ ℱ^W`, that integrates to zero over every set
of `𝒢₀` and is orthogonal to every coordinate Itô integral on `[0, T]`, vanishes almost
surely. -/
theorem ae_eq_zero_of_perp_augInitial (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P)
    {T : ℝ} (hT : 0 < T) {r : Ω → ℝ} (hr2 : MemLp r 2 P)
    (hrm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ T] r P)
    (hr0 : ∀ A, MeasurableSet[𝒢₀] A → ∫ ω in A, r ω ∂P = 0)
    (hperp : ∀ (i : Fin d) (G : HorizonIntegrand P (W.augInitialFiltration 𝒢₀ h𝒢₀) T),
      ∫ ω, r ω * G.integral (W.W i) (W.isBrownianFiltration_augInitial h𝒢₀ hind i) ω ∂P = 0) :
    r =ᵐ[P] 0 := by
  set ℱ := W.augInitialFiltration 𝒢₀ h𝒢₀ with hℱ
  have hcoord := W.isBrownianFiltration_augInitial h𝒢₀ hind
  have hrm' : AEStronglyMeasurable[Probability.aug (𝒢₀ ⊔ W.naturalFiltration T)
      ‹MeasurableSpace Ω› P] r P := by
    rw [← W.augFiltration_initialFiltration_of_nonneg h𝒢₀ hT.le]
    exact hrm
  have hrint : Integrable r P := hr2.integrable (by norm_num)
  refine Probability.ae_eq_zero_of_setIntegral_inter_eq_zero_aug h𝒢₀
    (W.naturalFiltration.le T) hrint hrm' fun A B hA hB => ?_
  -- the Brownian representation of the centred indicator of `B`
  set F : Ω → ℝ := fun ω => B.indicator (fun _ => (1 : ℝ)) ω - P.real B with hF
  have hBm : MeasurableSet B := W.naturalFiltration.le T B hB
  have hF2 : MemLp F 2 P :=
    (memLp_indicator_const 2 hBm (1 : ℝ) (Or.inr (measure_ne_top P B))).sub (memLp_const _)
  have hFm : AEStronglyMeasurable[augFiltration W.naturalFiltration P T] F P := by
    have hBm' : MeasurableSet[augFiltration W.naturalFiltration P T] B :=
      le_augFiltration W.naturalFiltration P T B hB
    exact ((stronglyMeasurable_const.indicator hBm').sub
      stronglyMeasurable_const).aestronglyMeasurable
  have hF0 : ∫ ω, F ω ∂P = 0 := by
    rw [hF, integral_sub ((integrable_const (1 : ℝ)).indicator hBm) (integrable_const _),
      integral_indicator_const _ hBm]
    simp
  obtain ⟨G, hG⟩ := exists_vectorIntegral_augFiltration W hT hF2 hFm hF0
  -- the initial weight `1_A`
  set η : Ω → ℝ := A.indicator fun _ => (1 : ℝ) with hη
  have hηb : ∃ M : ℝ, ∀ ω, |η ω| ≤ M :=
    ⟨1, fun ω => by
      by_cases h : ω ∈ A
      · rw [hη, Set.indicator_of_mem h]; norm_num
      · rw [hη, Set.indicator_of_notMem h]; norm_num⟩
  have hηm : StronglyMeasurable[ℱ 0] η :=
    stronglyMeasurable_const.indicator (W.le_augFiltration_initialFiltration h𝒢₀ 0 A hA)
  have hle : ∀ t, augFiltration W.naturalFiltration P t ≤ ℱ t :=
    W.augFiltration_natural_le_initial h𝒢₀
  set K : Fin d → HorizonIntegrand P ℱ T := fun i => ((G i).ofLE hle).mulInitial hT hηb hηm
    with hK
  have hKae : ∀ i, (K i).integral (W.W i) (hcoord i)
      =ᵐ[P] fun ω => η ω * (G i).integral (W.W i) (W.isBrownianFiltration_augNatural i) ω := by
    intro i
    filter_upwards [HorizonIntegrand.integral_mulInitial (W.W i) (hcoord i) hT hηb hηm
      ((G i).ofLE hle), HorizonIntegrand.integral_ofLE (W.W i)
      (W.isBrownianFiltration_augNatural i) (hcoord i) hle (G i)] with ω e1 e2
    rw [e1, e2]
  have hall : ∀ᵐ ω ∂P, ∀ i, (K i).integral (W.W i) (hcoord i) ω
      = η ω * (G i).integral (W.W i) (W.isBrownianFiltration_augNatural i) ω :=
    ae_all_iff.mpr hKae
  have hpt : ∀ᵐ ω ∂P, (A ∩ B).indicator (fun _ => (1 : ℝ)) ω * r ω
      = ∑ i, r ω * (K i).integral (W.W i) (hcoord i) ω + P.real B * (η ω * r ω) := by
    filter_upwards [hG, hall] with ω e1 e2
    have hsplit : (A ∩ B).indicator (fun _ => (1 : ℝ)) ω = η ω * F ω + P.real B * η ω := by
      by_cases ha : ω ∈ A <;> by_cases hb : ω ∈ B <;>
        simp [hη, hF, ha, hb, Set.indicator_of_mem, Set.indicator_of_notMem]
    rw [hsplit, e1, Finset.sum_congr rfl fun i _ => by rw [e2 i], vectorIntegral,
      Finset.mul_sum]
    rw [add_mul, Finset.sum_mul]
    congr 1
    · exact Finset.sum_congr rfl fun i _ => by ring
    · ring
  rw [← integral_indicator ((h𝒢₀ A hA).inter hBm)]
  have hind_eq : (fun ω => (A ∩ B).indicator r ω)
      = fun ω => (A ∩ B).indicator (fun _ => (1 : ℝ)) ω * r ω := by
    funext ω
    by_cases h : ω ∈ A ∩ B
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hind_eq, integral_congr_ae hpt]
  have hint : ∀ i, Integrable (fun ω => r ω * (K i).integral (W.W i) (hcoord i) ω) P :=
    fun i => hr2.integrable_mul (HorizonIntegrand.memLp (W.W i) (hcoord i) (K i))
  have hηr : Integrable (fun ω => η ω * r ω) P := by
    refine (hrint.indicator (h𝒢₀ A hA)).congr (Filter.Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A
    · simp [hη, Set.indicator_of_mem h]
    · simp [hη, Set.indicator_of_notMem h]
  rw [integral_add (integrable_finsetSum _ fun i _ => hint i) (hηr.const_mul _),
    integral_finsetSum _ fun i _ => hint i, integral_const_mul]
  have hA0 : ∫ ω, η ω * r ω ∂P = 0 := by
    rw [← hr0 A hA, ← integral_indicator (h𝒢₀ A hA)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    by_cases h : ω ∈ A
    · simp [hη, Set.indicator_of_mem h]
    · simp [hη, Set.indicator_of_notMem h]
  rw [hA0, mul_zero, add_zero]
  exact Finset.sum_eq_zero fun i _ => hperp i (K i)

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
