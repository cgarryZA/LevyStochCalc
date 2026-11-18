/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoRange
import LevyStochCalc.Brownian.ItoFiltrationChange

/-!
# Horizon integrands under an enlargement of the filtration

An admissible integrand on the horizon `[0, T]` for a filtration `ℱ` is admissible for every
larger filtration `𝒢`, and if the driver is a Brownian motion for both filtrations the two Itô
integrals agree almost everywhere.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}

namespace HorizonIntegrand

/-- An admissible integrand for `ℱ`, seen as one for a larger filtration `𝒢`. -/
def ofLE (hle : ∀ t, ℱ t ≤ 𝒢 t) (G : HorizonIntegrand P ℱ T) : HorizonIntegrand P 𝒢 T where
  toFun := G.toFun
  measurable_uncurry := G.measurable_uncurry
  progressive := G.progressive.mono hle
  vanishing := G.vanishing
  energy_ne_top := G.energy_ne_top

omit [IsProbabilityMeasure P] in
@[simp] theorem ofLE_toFun (hle : ∀ t, ℱ t ≤ 𝒢 t) (G : HorizonIntegrand P ℱ T) :
    (G.ofLE hle).toFun = G.toFun := rfl

/-- The Itô integral of an admissible integrand is unchanged, up to a null set, when the
filtration is enlarged to one for which the driver is still a Brownian motion. -/
theorem integral_ofLE (W : BrownianMotion P) (hℱ : IsBrownianFiltration W ℱ)
    (h𝒢 : IsBrownianFiltration W 𝒢) (hle : ∀ t, ℱ t ≤ 𝒢 t) (G : HorizonIntegrand P ℱ T) :
    (G.ofLE hle).integral W h𝒢 =ᵐ[P] G.integral W hℱ :=
  (stochasticIntegralBrownian_congr_filtration W ℱ 𝒢 hℱ h𝒢 hle G.toFun G.measurable_uncurry
    G.progressive (G.progressive.mono hle) G.sq_int_global T).symm

end HorizonIntegrand

end LevyStochCalc.Brownian.Ito
