/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoRange
import LevyStochCalc.Brownian.ItoAlgebraProduct
import LevyStochCalc.Brownian.ItoDensityUnbounded

/-!
# The Itô integral on a horizon as a limit of elementary integrals

Every admissible integrand `G` on the horizon `[0, T]` is the energy limit of adapted simple
integrands (`adaptedSimple_dense_L2_brownian`), and by the isometry between an elementary integral
and the `L²` integral the elementary integrals of those simple integrands converge to
`∫₀ᵀ G dW` in `L²(P)`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

/-- A sequence in `ℝ≥0∞` whose squares tend to `0` tends to `0`. -/
theorem tendsto_zero_of_sq_tendsto_zero {ι : Type*} {l : Filter ι} {x : ι → ℝ≥0∞}
    (h : Tendsto (fun n => x n ^ 2) l (𝓝 0)) : Tendsto x l (𝓝 0) := by
  have hc := ((ENNReal.continuous_rpow_const (y := (1 / 2 : ℝ))).tendsto 0).comp h
  rw [ENNReal.zero_rpow_of_pos (by norm_num)] at hc
  refine hc.congr fun n => ?_
  simp only [Function.comp_apply]
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

namespace HorizonIntegrand

/-- **Elementary approximation of the horizon integral.** For an admissible integrand `G` there
are simple integrands adapted to `ℱ` whose energy distance to `G` tends to `0` and whose
elementary integrals at `T` converge to `∫₀ᵀ G dW` in `L²(P)`. -/
theorem exists_simple_tendsto (W : BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
    (hT : 0 < T) (G : HorizonIntegrand P ℱ T) :
    ∃ Hn : ℕ → SimplePredictable Ω T,
      (∀ n (i : Fin (Hn n).N),
        StronglyMeasurable[ℱ ((Hn n).partition i.castSucc)] ((Hn n).ξ i)) ∧
      Tendsto (fun n => energy P T fun ω s => G.toFun ω s - (Hn n).eval s ω) atTop (𝓝 0) ∧
      Tendsto (fun n => eLpNorm (fun ω => simpleIntegral W (Hn n) T ω - G.integral W hℱ ω) 2 P)
        atTop (𝓝 0) := by
  obtain ⟨Hn, hadapt, htend⟩ := adaptedSimple_dense_L2_brownian ℱ hT G.toFun
    G.measurable_uncurry G.progressive (lt_top_iff_ne_top.mpr G.energy_ne_top)
  refine ⟨Hn, hadapt, htend, tendsto_zero_of_sq_tendsto_zero ?_⟩
  refine htend.congr fun n => ?_
  rw [eLpNorm_sq_eq_lintegral, integral, isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ
    (Hn n) (hadapt n) G.toFun G.measurable_uncurry G.progressive G.sq_int_global hT]
  refine lintegral_congr fun ω => lintegral_congr fun s => ?_
  rw [← nnnorm_neg, neg_sub]

end HorizonIntegrand

end LevyStochCalc.Brownian.Ito
