/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoRange
import LevyStochCalc.Brownian.ItoPullOut
import LevyStochCalc.Brownian.ItoAlgebraAssociativity

/-!
# Pulling an initial weight out of an Itô integral on a horizon

A bounded `ℱ₀`-measurable weight `η` passes through the Itô integral on the horizon `[0, T]`:
for an admissible integrand `G`, the process `η · 1_{(0, T]} · G` is admissible and its Itô
integral is `η · ∫₀ᵀ G dW` almost surely. The indicator only removes the time `0`, a null set of
times, and makes the weighted integrand progressively measurable without any hypothesis on the
filtration before time `0`. In particular `∫₀ᵀ G dW` integrates to zero over every set of `ℱ₀`.

## Main definitions

* `LevyStochCalc.Brownian.Ito.HorizonIntegrand.restrictIoc`: the integrand `1_{(0, T]} · G`.
* `LevyStochCalc.Brownian.Ito.HorizonIntegrand.mulInitial`: the integrand `η · 1_{(0, T]} · G`.

## Main statements

* `LevyStochCalc.Brownian.Ito.HorizonIntegrand.integral_mulInitial`: its integral is
  `η · ∫₀ᵀ G dW`.
* `LevyStochCalc.Brownian.Ito.HorizonIntegrand.setIntegral_integral_eq_zero`: the integral
  vanishes in mean over every set of `ℱ₀`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

namespace HorizonIntegrand

omit [IsProbabilityMeasure P] in
/-- An integrand dominated pointwise by an admissible one has finite energy. -/
theorem energy_ne_top_of_abs_le {K : Ω → ℝ → ℝ} (G : HorizonIntegrand P ℱ T) {c : ℝ}
    (hK : ∀ ω s, |K ω s| ≤ |c * G.toFun ω s|) : energy P T K ≠ ⊤ := by
  refine ne_top_of_le_ne_top (energy_const_mul_ne_top G.measurable_uncurry G.energy_ne_top c)
    (lintegral_mono fun ω => lintegral_mono fun s => ?_)
  refine pow_le_pow_left' ?_ 2
  rw [ENNReal.coe_le_coe, ← NNReal.coe_le_coe, coe_nnnorm, coe_nnnorm, Real.norm_eq_abs,
    Real.norm_eq_abs]
  exact hK ω s

/-- The admissible integrand `1_{(0, T]} · G`, for `0 < T`. -/
noncomputable def restrictIoc (hT : 0 < T) (G : HorizonIntegrand P ℱ T) :
    HorizonIntegrand P ℱ T where
  toFun ω s := indIoc Ω 0 T ω s * G.toFun ω s
  measurable_uncurry := (measurable_uncurry_indIoc 0 T).mul G.measurable_uncurry
  progressive := (progressivelyMeasurable_indIoc₀ ℱ hT).mul G.progressive
  vanishing ω s hs := by rw [G.vanishing ω s hs, mul_zero]
  energy_ne_top := G.energy_ne_top_of_abs_le (c := 1) fun ω s => by
    rw [abs_mul, one_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (indIoc_le_one 0 T ω s)

/-- Removing the time `0` does not change the Itô integral on the horizon. -/
theorem integral_restrictIoc (W : BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
    (hT : 0 < T) (G : HorizonIntegrand P ℱ T) :
    (G.restrictIoc hT).integral W hℱ =ᵐ[P] G.integral W hℱ := by
  have h := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ G.toFun G.measurable_uncurry
    G.progressive G.sq_int_global le_rfl hT (G.restrictIoc hT).measurable_uncurry
    (G.restrictIoc hT).progressive (G.restrictIoc hT).sq_int_global hT
  have h0 := stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ G.toFun G.measurable_uncurry
    G.progressive G.sq_int_global (le_refl (0 : ℝ))
  filter_upwards [h, h0] with ω e1 e2
  refine e1.trans ?_
  rw [min_self, min_eq_left hT.le, e2, Pi.zero_apply, sub_zero]
  rfl

variable {η : Ω → ℝ}

/-- The admissible integrand `η · 1_{(0, T]} · G`, for a bounded `ℱ₀`-measurable weight `η`. -/
noncomputable def mulInitial (hT : 0 < T) (hηb : ∃ M : ℝ, ∀ ω, |η ω| ≤ M)
    (hηm : StronglyMeasurable[ℱ 0] η) (G : HorizonIntegrand P ℱ T) :
    HorizonIntegrand P ℱ T where
  toFun ω s := η ω * indIoc Ω 0 T ω s * G.toFun ω s
  measurable_uncurry :=
    ((((hηm.mono (ℱ.le 0)).measurable).comp measurable_fst).mul
      (measurable_uncurry_indIoc 0 T)).mul G.measurable_uncurry
  progressive := (progressivelyMeasurable_mul_indIoc ℱ le_rfl hT hηb
    (hηm.mono (ℱ.le 0)).measurable hηm).mul G.progressive
  vanishing ω s hs := by rw [G.vanishing ω s hs, mul_zero]
  energy_ne_top := G.energy_ne_top_of_abs_le (c := hηb.choose) fun ω s => by
    rw [abs_mul, abs_mul, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |η ω| * |indIoc Ω 0 T ω s| ≤ |η ω| * 1 :=
          mul_le_mul_of_nonneg_left (indIoc_le_one 0 T ω s) (abs_nonneg _)
      _ ≤ |hηb.choose| := by rw [mul_one]; exact (hηb.choose_spec ω).trans (le_abs_self _)

/-- **An initial weight passes through the Itô integral.** For a bounded `ℱ₀`-measurable `η`,
the integral of `η · 1_{(0, T]} · G` is `η · ∫₀ᵀ G dW` almost surely. -/
theorem integral_mulInitial (W : BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
    (hT : 0 < T) (hηb : ∃ M : ℝ, ∀ ω, |η ω| ≤ M) (hηm : StronglyMeasurable[ℱ 0] η)
    (G : HorizonIntegrand P ℱ T) :
    (G.mulInitial hT hηb hηm).integral W hℱ =ᵐ[P] fun ω => η ω * G.integral W hℱ ω := by
  have h := mul_stochasticIntegralBrownian_indIoc W ℱ hℱ le_rfl hT hηb
    (hηm.mono (ℱ.le 0)).measurable hηm G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global (G.restrictIoc hT).measurable_uncurry (G.restrictIoc hT).progressive
    (G.restrictIoc hT).sq_int_global (G.mulInitial hT hηb hηm).measurable_uncurry
    (G.mulInitial hT hηb hηm).progressive (G.mulInitial hT hηb hηm).sq_int_global hT
  filter_upwards [h, integral_restrictIoc W hℱ hT G] with ω e1 e2
  exact e1.symm.trans (congrArg (η ω * ·) e2)

/-- The Itô integral on the horizon integrates to zero over every set of `ℱ₀`. -/
theorem setIntegral_integral_eq_zero (W : BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
    (hT : 0 < T) (G : HorizonIntegrand P ℱ T) {A : Set Ω} (hA : MeasurableSet[ℱ 0] A) :
    ∫ ω in A, G.integral W hℱ ω ∂P = 0 := by
  have hηb : ∃ M : ℝ, ∀ ω, |A.indicator (fun _ => (1 : ℝ)) ω| ≤ M :=
    ⟨1, fun ω => by
      by_cases h : ω ∈ A
      · rw [Set.indicator_of_mem h]; norm_num
      · rw [Set.indicator_of_notMem h]; norm_num⟩
  have hηm : StronglyMeasurable[ℱ 0] (A.indicator fun _ => (1 : ℝ)) :=
    stronglyMeasurable_const.indicator hA
  rw [← integral_indicator (ℱ.le 0 A hA)]
  have hmean := integral_mean_zero W hℱ hT.le (G.mulInitial hT hηb hηm)
  rw [integral_congr_ae (integral_mulInitial W hℱ hT hηb hηm G)] at hmean
  rw [← hmean]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  by_cases h : ω ∈ A
  · simp [Set.indicator_of_mem h]
  · simp [Set.indicator_of_notMem h]

end HorizonIntegrand

end LevyStochCalc.Brownian.Ito
