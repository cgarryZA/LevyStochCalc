/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.RepresentationInitial
import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Vector-valued martingale representation with initial information

Over the augmentation `ℱ` of `𝒢₀ ⊔ ℱ^W`, with `𝒢₀` independent of the `d`-dimensional Brownian
motion `W`, every `ξ ∈ L²(ℱ_T; ℝ^m)` is `𝔼[ξ | ℱ₀] + ∫₀ᵀ Z dW`, where the `k`-th coordinate of the
integral is `∑ᵢ ∫₀ᵀ Z^{k i} dWⁱ` for admissible integrands `Z^{k i}`; the initial term and the
integrands are unique. The statement is the scalar one applied coordinatewise, since conditional
expectation commutes with the coordinate projections.
-/

open MeasureTheory ProbabilityTheory Filter

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {d m : ℕ}

/-- **Vector-valued martingale representation with initial information.** Every square-integrable
`ξ : Ω → ℝ^m` measurable at time `T > 0` for the augmentation of `𝒢₀ ⊔ ℱ^W` is `𝔼[ξ | ℱ₀]` plus a
matrix of Itô integrals: `ξ_k = 𝔼[ξ | ℱ₀]_k + ∑ᵢ ∫₀ᵀ Z^{k i} dWⁱ`. -/
theorem exists_vectorIntegral_augInitial_pi (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P)
    {T : ℝ} (hT : 0 < T) {ξ : Ω → Fin m → ℝ} (hξ2 : MemLp ξ 2 P)
    (hξm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ T] ξ P) :
    ∃ Z : Fin m → ∀ _ : Fin d, HorizonIntegrand P (W.augInitialFiltration 𝒢₀ h𝒢₀) T,
      ξ =ᵐ[P] fun ω => P[ξ | W.augInitialFiltration 𝒢₀ h𝒢₀ 0] ω
        + fun k => vectorIntegral W (W.isBrownianFiltration_augInitial h𝒢₀ hind) (Z k) ω := by
  have hk2 : ∀ k, MemLp (fun ω => ξ ω k) 2 P := hξ2.eval
  have hkm : ∀ k, AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ T] (fun ω => ξ ω k) P :=
    fun k => (continuous_apply k).comp_aestronglyMeasurable hξm
  choose Z hZ using fun k => exists_vectorIntegral_augInitial W h𝒢₀ hind hT (hk2 k) (hkm k)
  have hcomm : ∀ k, (fun ω => P[ξ | W.augInitialFiltration 𝒢₀ h𝒢₀ 0] ω k)
      =ᵐ[P] P[fun ω => ξ ω k | W.augInitialFiltration 𝒢₀ h𝒢₀ 0] := fun k =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) k).comp_condExp_comm
      (hξ2.integrable (by norm_num))
  refine ⟨Z, ?_⟩
  filter_upwards [ae_all_iff.mpr hZ, ae_all_iff.mpr hcomm] with ω e1 e2
  funext k
  rw [Pi.add_apply, e1 k, ← e2 k]

/-- **Uniqueness of the vector-valued representation.** Two representations
`η + ∫₀ᵀ Z dW = η' + ∫₀ᵀ Z' dW` with `ℱ₀`-measurable `η, η' : Ω → ℝ^m` have `η = η'` almost surely
and `Z^{k i} = Z'^{k i}` almost everywhere for `P ⊗ ds` on `Ω × [0, T]`. -/
theorem unique_vectorIntegral_augInitial_pi (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P)
    {T : ℝ} (hT : 0 < T) {η η' : Ω → Fin m → ℝ}
    (hηm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ 0] η P)
    (hη'm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ 0] η' P)
    (Z Z' : Fin m → ∀ _ : Fin d, HorizonIntegrand P (W.augInitialFiltration 𝒢₀ h𝒢₀) T)
    (h : (fun ω => η ω
        + fun k => vectorIntegral W (W.isBrownianFiltration_augInitial h𝒢₀ hind) (Z k) ω)
      =ᵐ[P] fun ω => η' ω
        + fun k => vectorIntegral W (W.isBrownianFiltration_augInitial h𝒢₀ hind) (Z' k) ω) :
    η =ᵐ[P] η' ∧ ∀ k i, (fun p : Ω × ℝ => (Z k i).toFun p.1 p.2)
      =ᵐ[energyMeasure P T] fun p => (Z' k i).toFun p.1 p.2 := by
  have hcoord : ∀ k, (fun ω => η ω k) =ᵐ[P] (fun ω => η' ω k) ∧
      ∀ i, (fun p : Ω × ℝ => (Z k i).toFun p.1 p.2)
        =ᵐ[energyMeasure P T] fun p => (Z' k i).toFun p.1 p.2 := by
    intro k
    refine unique_vectorIntegral_augInitial W h𝒢₀ hind hT
      ((continuous_apply k).comp_aestronglyMeasurable hηm)
      ((continuous_apply k).comp_aestronglyMeasurable hη'm) (Z k) (Z' k) ?_
    filter_upwards [h] with ω e
    exact congrFun e k
  refine ⟨?_, fun k i => (hcoord k).2 i⟩
  filter_upwards [ae_all_iff.mpr fun k => (hcoord k).1] with ω e
  funext k
  exact e k

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
