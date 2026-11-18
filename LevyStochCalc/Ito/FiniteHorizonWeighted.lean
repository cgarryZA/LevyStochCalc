/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.FiniteHorizonBracket
import LevyStochCalc.Ito.SecondMomentWeighted

/-!
# The exponentially weighted energy of an Itô process on a finite horizon

For a square-integrable Itô process `X = X₀ + ∫ a ds + M` on `[0, T]` whose martingale part
satisfies the isometry `𝔼‖M_t‖² = 𝔼 ∫_0^t ‖H_s‖² ds`, the map `t ↦ 𝔼‖X_t‖²` is the initial
energy plus the time integral of the integrable rate `2 𝔼⟪X_s, a_s⟫ + 𝔼‖H_s‖²`, so integration by
parts against `e^{βs}` gives, for `0 < t ≤ T`,

`e^{βt} 𝔼‖X_t‖² = 𝔼‖X₀‖² + ∫_0^t e^{βs} (β 𝔼‖X_s‖² + 2 𝔼⟪X_s, a_s⟫ + 𝔼‖H_s‖²) ds`.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

variable {Ω E F : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {ℱ : Filtration ℝ m0} {T : ℝ} {X a M : ℝ → Ω → E} {X₀ : Ω → E} {H : ℝ → Ω → F}

/-- **The exponentially weighted energy identity on a finite horizon.** For a square-integrable
Itô process `X = X₀ + ∫ a ds + M` on `[0, T]` whose martingale part satisfies the isometry with
integrand `H`, `0 < t ≤ T` and `β : ℝ`,

`e^{βt} 𝔼‖X_t‖² = 𝔼‖X₀‖² + ∫_0^t e^{βs} (β 𝔼‖X_s‖² + 2 𝔼⟪X_s, a_s⟫ + 𝔼‖H_s‖²) ds`. -/
theorem exp_mul_integral_norm_sq_eq (hX : IsL2ItoProcessOn ℱ P T X X₀ a M)
    (hM : HasPolarisedIsometryOn P T M M H H) {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (β : ℝ) :
    Real.exp (β * t) * ∫ ω, ‖X t ω‖ ^ 2 ∂P
      = ∫ ω, ‖X₀ ω‖ ^ 2 ∂P
        + ∫ s in Set.Icc (0 : ℝ) t, Real.exp (β * s) * (β * ∫ ω, ‖X s ω‖ ^ 2 ∂P
            + (2 * ∫ ω, ⟪X s ω, a s ω⟫ ∂P + ∫ ω, ‖H s ω‖ ^ 2 ∂P)) := by
  have hHsq : Integrable (fun p : Ω × ℝ => ‖H p.2 p.1‖ ^ 2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (memLp_two_iff_integrable_sq_norm hM.integrand_left.1).1 hM.integrand_left
  have hHsq' : ∀ r, r ≤ T → Integrable (fun p : Ω × ℝ => ‖H p.2 p.1‖ ^ 2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) r))) := fun r hr =>
    hHsq.mono_measure (Measure.prod_mono le_rfl
      (Measure.restrict_mono (Set.Icc_subset_Icc le_rfl hr) le_rfl))
  have hg1 : IntegrableOn (fun s => 2 * ∫ ω, ⟪X s ω, a s ω⟫ ∂P) (Set.Icc (0 : ℝ) t) :=
    (integrableOn_rate hX hX ht.le htT).congr_fun (fun s _ => integral_inner_add_inner_eq s)
      measurableSet_Icc
  have hg2 : IntegrableOn (fun s => ∫ ω, ‖H s ω‖ ^ 2 ∂P) (Set.Icc (0 : ℝ) t) :=
    (hHsq' t htT).integral_prod_right
  have hg : IntegrableOn (fun s => 2 * ∫ ω, ⟪X s ω, a s ω⟫ ∂P + ∫ ω, ‖H s ω‖ ^ 2 ∂P)
      (Set.Icc (0 : ℝ) t) := hg1.add hg2
  refine LevyStochCalc.Ito.SecondMoment.exp_mul_eq_add_setIntegral
    (m := fun s => ∫ ω, ‖X s ω‖ ^ 2 ∂P) ht hg (fun s hs => ?_) β
  have hsub : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) t := Set.Icc_subset_Icc le_rfl hs.2
  rw [integral_norm_sq_eq hX hM hs.1.le (hs.2.trans htT),
    integral_add (hg1.mono_set hsub) (hg2.mono_set hsub), integral_const_mul,
    integral_integral_swap (f := fun ω r => ‖H r ω‖ ^ 2) (hHsq' s (hs.2.trans htT))]
  ring

end LevyStochCalc.Ito.FiniteHorizon
