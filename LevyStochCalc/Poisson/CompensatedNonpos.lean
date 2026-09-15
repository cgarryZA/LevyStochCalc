/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedCadlagMod
import LevyStochCalc.Brownian.MultidimIto

/-!
# Stochastic integrals at non-positive times

Both legs of a Lévy driver integrate over `(0, t]`, so both vanish almost surely once `t ≤ 0`.

For the compensated Poisson leg this is already recorded for the `L²` integral process
(`process_ae_zero_of_nonpos`) and for its càdlàg adapted modification
(`stochasticIntegral_ae_zero_of_nonpos`); here it is carried to the everywhere-càdlàg
modification `cadlagIntegral`.

For the Brownian leg it is recorded componentwise
(`Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos`); here it is summed over the
coordinates of a multidimensional Brownian motion.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Jump

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
  (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)

/-- The everywhere-càdlàg modification of the compensated integral vanishes almost surely at a
non-positive time. -/
theorem cadlagIntegral_ae_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    cadlagIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull t =ᵐ[P] 0 :=
  (cadlagIntegral_ae_eq N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hℱ0 hnull t).trans
    ((stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t).trans
      (process_ae_zero_of_nonpos N ℱ hℱ φ h_meas h_progMeas h_sq_int_global ht))

end Jump

end LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The multidimensional Brownian Itô integral vanishes almost surely at a non-positive time. -/
theorem stochasticIntegral_ae_zero_of_nonpos
    (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (h_meas : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (h_progMeas : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
    (h_sq_int_global : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : t ≤ 0) :
    stochasticIntegral W ℱ hℱ Z h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  have h : ∀ i : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (W.W i) ℱ (hℱ i)
        (fun ω' s => Z s ω' i) (h_meas i) (h_progMeas i) (h_sq_int_global i) t ω = 0 := fun i =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (W.W i) ℱ (hℱ i)
      (fun ω' s => Z s ω' i) (h_meas i) (h_progMeas i) (h_sq_int_global i) ht
  filter_upwards [ae_all_iff.2 h] with ω hω
  simp only [stochasticIntegral, LevyStochCalc.Brownian.Ito.stochasticIntegral, Pi.zero_apply]
  exact Finset.sum_eq_zero fun i _ => hω i

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
