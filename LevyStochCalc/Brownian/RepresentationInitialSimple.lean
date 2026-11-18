/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.RepresentationInitial
import LevyStochCalc.Brownian.HorizonSimpleApprox

/-!
# The representing integral as a limit of elementary integrals

Over the augmentation `ℱ` of `𝒢₀ ⊔ ℱ^W`, with `𝒢₀` independent of `W`, the martingale part
`ξ − 𝔼[ξ | ℱ₀]` of a square-integrable `ℱ_T`-measurable `ξ` is the `L²(P)`-limit of sums of
elementary integrals `∑ᵢ ∑ⱼ ξⁱⱼ (Wⁱ_{t_{j+1}} − Wⁱ_{t_j})` of simple integrands adapted to `ℱ`.
This is the form in which the representation is used by an integral defined as the `L²`-limit of
elementary integrals of adapted simple integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {d : ℕ}

/-- **The representation as a limit of elementary integrals.** For `ξ` square integrable and
measurable at time `T > 0` for the augmentation of `𝒢₀ ⊔ ℱ^W`, there are simple integrands
`Hⁱₙ` adapted to that filtration with `∑ᵢ ∫₀ᵀ Hⁱₙ dWⁱ → ξ − 𝔼[ξ | ℱ₀]` in `L²(P)`. -/
theorem exists_simple_tendsto_augInitial (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P)
    {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ} (hξ2 : MemLp ξ 2 P)
    (hξm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ T] ξ P) :
    ∃ Hn : Fin d → ℕ → SimplePredictable Ω T,
      (∀ i n (j : Fin (Hn i n).N), StronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀
        ((Hn i n).partition j.castSucc)] ((Hn i n).ξ j)) ∧
      Tendsto (fun n => eLpNorm (fun ω => ξ ω - P[ξ | W.augInitialFiltration 𝒢₀ h𝒢₀ 0] ω
        - ∑ i, simpleIntegral (W.W i) (Hn i n) T ω) 2 P) atTop (𝓝 0) := by
  have hcoord := W.isBrownianFiltration_augInitial h𝒢₀ hind
  obtain ⟨G, hG⟩ := exists_vectorIntegral_augInitial W h𝒢₀ hind hT hξ2 hξm
  choose Hn hadapt _ htend using fun i =>
    HorizonIntegrand.exists_simple_tendsto (W.W i) (hcoord i) hT (G i)
  refine ⟨Hn, hadapt, ?_⟩
  set e : Fin d → ℕ → Ω → ℝ := fun i n ω =>
    (G i).integral (W.W i) (hcoord i) ω - simpleIntegral (W.W i) (Hn i n) T ω with he
  have hle : ∀ n, eLpNorm (fun ω => ξ ω - P[ξ | W.augInitialFiltration 𝒢₀ h𝒢₀ 0] ω
      - ∑ i, simpleIntegral (W.W i) (Hn i n) T ω) 2 P
      ≤ ∑ i, eLpNorm (fun ω => simpleIntegral (W.W i) (Hn i n) T ω
        - (G i).integral (W.W i) (hcoord i) ω) 2 P := by
    intro n
    have hae : (fun ω => ξ ω - P[ξ | W.augInitialFiltration 𝒢₀ h𝒢₀ 0] ω
        - ∑ i, simpleIntegral (W.W i) (Hn i n) T ω) =ᵐ[P] ∑ i, e i n := by
      filter_upwards [hG] with ω e1
      rw [e1, Finset.sum_apply, he, Finset.sum_sub_distrib, vectorIntegral]
      ring
    rw [eLpNorm_congr_ae hae]
    refine (eLpNorm_sum_le (fun i _ => ?_) (by norm_num)).trans
      (Finset.sum_le_sum fun i _ => (eLpNorm_sub_comm _ _ _ _).le)
    exact (HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)).aestronglyMeasurable.sub
      ((Finset.measurable_sum _ fun j _ => ((Hn i n).ξ_measurable j).mul
        (((W.W i).measurable_eval _).sub ((W.W i).measurable_eval _))).aestronglyMeasurable)
  have hsum : Tendsto (fun n => ∑ i, eLpNorm (fun ω => simpleIntegral (W.W i) (Hn i n) T ω
      - (G i).integral (W.W i) (hcoord i) ω) 2 P) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ => htend i
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun n => zero_le) hle

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
