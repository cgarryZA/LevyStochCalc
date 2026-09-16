/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.SecondMomentToolkit

/-!
# The quadratic second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. Summing over the coordinates gives the vector form, and
the cross witness carried by the driver gives the form over its augmented joint natural
filtration. The polarised isometry for the compensated integral, the expected product of two
compensated integrals at a time being the expected time integral of the product of their
integrands against the Lévy measure, is proved here alongside.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section PolarisedMarked

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] in
/-- The energy of a marked integrand on a window, as a lintegral for the product measure. -/
theorem lintegral_prod_marked {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) :
    ∫⁻ p, (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
        ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hmeas : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    hm.nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [lintegral_prod _ hmeas.aemeasurable]
  refine lintegral_congr fun ω => ?_
  exact lintegral_prod _ (hmeas.comp (measurable_prodMk_left (x := ω))).aemeasurable

omit [IsProbabilityMeasure P] in
/-- A marked integrand of finite energy on a window is square integrable for the product
measure. -/
theorem memLp_two_prod_marked {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    MemLp (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) 2
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hm.aestronglyMeasurable ?_
  rw [lintegral_prod_marked hm T]
  exact hq

omit [IsProbabilityMeasure P] in
/-- The energy of a marked integrand on a window is the integral of its square for the product
measure. -/
theorem toReal_lintegral_sq_marked_eq {φ : Ω → ℝ → E → ℝ}
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {T : ℝ}
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal
      = ∫ p, φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
  rw [← lintegral_prod_marked hm T, ← integral_mul_self_eq_toReal (memLp_two_prod_marked hm hq)]

/-- A Bochner integral for the product measure of a marked window, iterated. -/
theorem integral_prod_marked {F : Ω × ℝ × E → ℝ} {T : ℝ}
    (hF : Integrable F (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))) :
    ∫ p, F p ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, F (ω, (s, e)) ∂ν ∂volume ∂P := by
  rw [integral_prod _ hF]
  refine integral_congr_ae ?_
  filter_upwards [hF.prod_right_ae] with ω hω
  exact integral_prod _ hω

/-- **The polarised isometry of the compensated integral.** The pairing of two compensated
integrals at a positive time is the integral of the pairing of their integrands over the window
and the marks. -/
theorem integral_mul_stochasticIntegral (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    {φ ψ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hψp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, φ ω s e * ψ ω s e ∂ν ∂volume ∂P := by
  have hU2 := LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ φ hφm hφp hφq T
  have hV2 := LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp N ℱ hℱ ψ hψm hψp hψq T
  have hUV2 : MemLp (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) 2 P :=
    hU2.sub hV2
  have hdiff := LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated N ℱ hℱ φ ψ hφm hψm
    hφp hψp hφq hψq T hT
  have hdq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    rw [← hdiff]
    exact lintegral_sq_lt_top_of_memLp_two hUV2
  have hφ2 := memLp_two_prod_marked hφm (hφq T hT)
  have hψ2 := memLp_two_prod_marked hψm (hψq T hT)
  have hUU : ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω ∂P
      = ∫ p, φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
    rw [integral_mul_self_eq_toReal hU2,
      LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ φ hφm hφp hφq T hT]
    exact toReal_lintegral_sq_marked_eq hφm (hφq T hT)
  have hVV : ∫ ω, LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω ∂P
      = ∫ p, ψ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
    rw [integral_mul_self_eq_toReal hV2,
      LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T hT]
    exact toReal_lintegral_sq_marked_eq hψm (hψq T hT)
  have hDD : ∫ ω, (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
        * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) ∂P
      = ∫ p, (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2) * (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2)
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := by
    rw [integral_mul_self_eq_toReal hUV2, hdiff]
    exact toReal_lintegral_sq_marked_eq (φ := fun ω s e => φ ω s e - ψ ω s e) (hφm.sub hψm) hdq
  have iUU : Integrable (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω) P :=
    hU2.integrable_mul hU2
  have iVV : Integrable (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) P :=
    hV2.integrable_mul hV2
  have iDD : Integrable (fun ω =>
      (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
      * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)) P :=
    hUV2.integrable_mul hUV2
  have iS : Integrable (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω) P :=
    iUU.add iVV
  have hexp : (fun ω =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
      = fun ω =>
        (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
          * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
          * LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω
        - (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω)
        * (LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω))
        / 2 := by
    funext ω
    ring
  have iφφ : Integrable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := hφ2.integrable_mul hφ2
  have iψψ : Integrable (fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := hψ2.integrable_mul hψ2
  have iφψ : Integrable (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := hφ2.integrable_mul hψ2
  have iDD' : Integrable (fun p : Ω × ℝ × E =>
      (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2) * (φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2))
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) :=
    (hφ2.sub hψ2).integrable_mul (hφ2.sub hψ2)
  have iS' : Integrable (fun p : Ω × ℝ × E =>
      φ p.1 p.2.1 p.2.2 * φ p.1 p.2.1 p.2.2 + ψ p.1 p.2.1 p.2.2 * ψ p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) := iφφ.add iψψ
  rw [hexp, integral_div, integral_sub iS iDD, integral_add iUU iVV, hUU, hVV, hDD,
    ← integral_add iφφ iψψ, ← integral_sub iS' iDD', ← integral_div, ← integral_prod_marked iφψ]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

end PolarisedMarked

section Scalar

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- An Itô–Lévy process with a square-integrable initial value and a square-integrable drift is
square integrable at every nonnegative time. -/
theorem memLp_two_of_isItoLevyProcess
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (hX₀2 : MemLp X₀ 2 P) (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (X t) 2 P := by
  have hS2 : ∀ j : Fin d, MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ
      (hℱW j) (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t) 2 P := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hSsum2 : MemLp (fun ω => ∑ j, LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ
      (hℱW j) (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t ω) 2 P :=
    memLp_finsetSum Finset.univ fun j _ => hS2 j
  have hC2 : MemLp (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq t) 2 P :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hDr2 : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω) 2 P :=
    memLp_two_setIntegral (f := fun ω s => b s ω) hbm ht
      (energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq ht)
  refine (((hX₀2.add hDr2).add hSsum2).add hC2).ae_eq ?_
  exact Filter.EventuallyEq.symm (h.decomposition t ht)

/-- **The second moment of an Itô–Lévy process.** For an Itô–Lévy process over a Lévy driver
with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift,

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`. -/
theorem integral_mul_self_eq_of_isItoLevyProcess
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + 2 * (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P)
        + (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
  classical
  -- the three pieces of the decomposition
  set S : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) with hSdef
  set C : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq
    with hCdef
  set Dr : ℝ → Ω → ℝ := fun t ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω with hDrdef
  have hdec : ∀ t, 0 ≤ t → ∀ᵐ ω ∂P,
      X t ω = X₀ ω + Dr t ω + (∑ j, S j t ω) + C t ω := fun t ht => h.decomposition t ht
  -- square integrability of every piece
  have hS2 : ∀ (j : Fin d) (t : ℝ), MemLp (S j t) 2 P := fun j t =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hSsum2 : ∀ t, MemLp (fun ω => ∑ j, S j t ω) 2 P := fun t =>
    memLp_finsetSum Finset.univ fun j _ => hS2 j t
  have hC2 : ∀ t, MemLp (C t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hbq' : ∀ t, 0 ≤ t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun t ht => energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq ht
  have hDr2 : ∀ t, 0 ≤ t → MemLp (Dr t) 2 P := fun t ht =>
    memLp_two_setIntegral (f := fun ω s => b s ω) hbm ht (hbq' t ht)
  -- the isometries
  have hSiso : ∀ j, ∫ ω, S j T ω * S j T ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    intro j
    rw [integral_mul_self_eq_toReal (hS2 j T)]
    congr 1
    exact LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) hT
  have hCiso : ∫ ω, C T ω * C T ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
    rw [integral_mul_self_eq_toReal (hC2 T)]
    congr 1
    exact LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq T hT
  -- the orthogonalities
  have hSS : ∀ j k, j ≠ k → ∫ ω, S j T ω * S k T ω ∂P = 0 := fun j k hjk =>
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero
      D.W hjk hℱW (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) (h.σ_meas k) (h.σ_prog k) (h.σ_sq k) hT.le
  have hSC : ∀ j, ∫ ω, S j T ω * C T ω ∂P = 0 := fun j =>
    LevyStochCalc.Driver.LevyDriver.integral_stochasticIntegral_mul_compensated_eq_zero 𝒲 hℱW hℱN
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) h.γ_meas h.γ_prog h.γ_sq hT.le
  have hSsum_sq : ∫ ω, (∑ j, S j T ω) * (∑ j, S j T ω) ∂P
      = ∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    have hexp : (fun ω => (∑ j, S j T ω) * (∑ j, S j T ω))
        = fun ω => ∑ j, ∑ k, S j T ω * S k T ω := by
      funext ω
      exact Finset.sum_mul_sum _ _ _ _
    have hint : ∀ j k, Integrable (fun ω => S j T ω * S k T ω) P := fun j k =>
      (hS2 j T).integrable_mul (hS2 k T)
    have hint' : ∀ j, Integrable (fun ω => ∑ k, S j T ω * S k T ω) P := fun j =>
      integrable_finsetSum _ fun k _ => hint j k
    rw [hexp, integral_finsetSum _ fun j _ => hint' j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k,
      Finset.sum_eq_single j (fun k _ hkj => hSS j k (Ne.symm hkj))
        (fun hj => absurd (Finset.mem_univ j) hj)]
    exact hSiso j
  have hSsum_C : ∫ ω, (∑ j, S j T ω) * C T ω ∂P = 0 := by
    have hexp : (fun ω => (∑ j, S j T ω) * C T ω) = fun ω => ∑ j, S j T ω * C T ω := by
      funext ω
      exact Finset.sum_mul _ _ _
    have hint : ∀ j, Integrable (fun ω => S j T ω * C T ω) P := fun j =>
      (hS2 j T).integrable_mul (hC2 T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hSC j
  -- the martingale pieces are orthogonal to the initial value
  have hX₀S : ∀ j, ∫ ω, X₀ ω * S j T ω ∂P = 0 := fun j =>
    integral_mul_martingale_eq_zero
      (LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j))
      hT.le (hX₀.mono (ℱ.le_rightCont 0)) hX₀2 (hS2 j T)
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) le_rfl)
  have hX₀Ssum : ∫ ω, X₀ ω * (∑ j, S j T ω) ∂P = 0 := by
    have hexp : (fun ω => X₀ ω * (∑ j, S j T ω)) = fun ω => ∑ j, X₀ ω * S j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => X₀ ω * S j T ω) P := fun j =>
      hX₀2.integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hX₀S j
  have hCproc : ∀ t, C t =ᵐ[P]
      LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t :=
    fun t => LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN γ
      h.γ_meas h.γ_prog h.γ_sq t
  have hproc2 : ∀ t, MemLp (LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.process_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t
  have hmartC := LevyStochCalc.Poisson.Compensated.martingale_process D.N ℱ hℱN γ h.γ_meas
    h.γ_prog h.γ_sq
  have hproc0 := LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos D.N ℱ hℱN γ
    h.γ_meas h.γ_prog h.γ_sq (le_refl (0 : ℝ))
  have hX₀C : ∫ ω, X₀ ω * C T ω ∂P = 0 := by
    have h1 : (fun ω => X₀ ω * C T ω) =ᵐ[P] fun ω => X₀ ω
        * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
      filter_upwards [hCproc T] with ω hω
      rw [hω]
    rw [integral_congr_ae h1]
    exact integral_mul_martingale_eq_zero hmartC hT.le hX₀ hX₀2 (hproc2 T) hproc0
  -- the drift pairings at the horizon, as time integrals
  have hDrS : ∀ j, ∫ ω, Dr T ω * S j T ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * S j T ω ∂P :=
    fun j => integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hS2 j T)
  have hDrC : ∫ ω, Dr T ω * C T ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * C T ω ∂P :=
    integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hC2 T)
  have hDrX₀ : ∫ ω, Dr T ω * X₀ ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * X₀ ω ∂P :=
    integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) hX₀2
  have hDrDr : ∫ ω, Dr T ω * Dr T ω ∂P
      = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr s ω ∂P := by
    have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω) (Set.Icc (0 : ℝ) T) volume := by
      filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b s ω) hbm hbq] with ω hω
      exact hω T
    have hR := memLp_two_running (P := P) hbm (hbq T hT)
    have hint : Integrable (fun p : Ω × ℝ => b p.2 p.1 * running b T p)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
      (memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul hR
    have hpath : ∀ᵐ ω ∂P, Dr T ω * Dr T ω
        = 2 * ∫ s in Set.Icc (0 : ℝ) T, b s ω * running b T (ω, s) := by
      filter_upwards [hbint] with ω hω
      simp only [hDrdef]
      rw [mul_self_setIntegral_eq hω]
      congr 1
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      rw [running_eq hs, mul_comm]
    calc ∫ ω, Dr T ω * Dr T ω ∂P
        = ∫ ω, (2 * ∫ s in Set.Icc (0 : ℝ) T, b s ω * running b T (ω, s)) ∂P :=
          integral_congr_ae hpath
      _ = 2 * ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, b s ω * running b T (ω, s) ∂volume ∂P :=
          integral_const_mul _ _
      _ = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * running b T (ω, s) ∂P := by
          rw [integral_integral_swap (f := fun ω s => b s ω * running b T (ω, s)) hint]
      _ = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr s ω ∂P := by
          congr 1
          refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          exact congrArg (fun x => b s ω * x) (running_eq hs)
  -- at almost every time of the window, the pairing of the path with the drift expands
  have hbs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (fun ω => b s ω) 2 P :=
    ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT)
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hXb : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P
        + (∑ j, ∫ ω, b s ω * S j T ω ∂P) + ∫ ω, b s ω * C T ω ∂P := by
    filter_upwards [hbs, hsw] with s hs2 hs
    have hs0 : 0 ≤ s := hs.1
    have hbsm : StronglyMeasurable[ℱ.rightCont s] fun ω => b s ω :=
      (hbp.stronglyMeasurable_eval s).mono (ℱ.le_rightCont s)
    have hbsm' : StronglyMeasurable[ℱ s] fun ω => b s ω := hbp.stronglyMeasurable_eval s
    have h1 : ∫ ω, X s ω * b s ω ∂P
        = ∫ ω, (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * b s ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hdec s hs0] with ω hω
      rw [hω]
    have hexp : (fun ω => (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * b s ω)
        = fun ω => b s ω * X₀ ω + b s ω * Dr s ω + (∑ j, b s ω * S j s ω) + b s ω * C s ω := by
      funext ω
      rw [← Finset.mul_sum]
      ring
    have i1 : Integrable (fun ω => b s ω * X₀ ω) P := hs2.integrable_mul hX₀2
    have i2 : Integrable (fun ω => b s ω * Dr s ω) P := hs2.integrable_mul (hDr2 s hs0)
    have i3 : ∀ j, Integrable (fun ω => b s ω * S j s ω) P := fun j =>
      hs2.integrable_mul (hS2 j s)
    have i3' : Integrable (fun ω => ∑ j, b s ω * S j s ω) P :=
      integrable_finsetSum _ fun j _ => i3 j
    have i4 : Integrable (fun ω => b s ω * C s ω) P := hs2.integrable_mul (hC2 s)
    have i12 : Integrable (fun ω => b s ω * X₀ ω + b s ω * Dr s ω) P := i1.add i2
    have i123 : Integrable
        (fun ω => b s ω * X₀ ω + b s ω * Dr s ω + ∑ j, b s ω * S j s ω) P := i12.add i3'
    have hSj : ∀ j, ∫ ω, b s ω * S j s ω ∂P = ∫ ω, b s ω * S j T ω ∂P := fun j =>
      (integral_mul_martingale_eq
        (LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian (D.W.W j) ℱ
          (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j)) hs.2 hbsm hs2 (hS2 j T)).symm
    have hCs : ∫ ω, b s ω * C s ω ∂P = ∫ ω, b s ω * C T ω ∂P := by
      have e1 : (fun ω => b s ω * C s ω) =ᵐ[P] fun ω => b s ω
          * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq s ω := by
        filter_upwards [hCproc s] with ω hω
        rw [hω]
      have e2 : (fun ω => b s ω * C T ω) =ᵐ[P] fun ω => b s ω
          * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
        filter_upwards [hCproc T] with ω hω
        rw [hω]
      rw [integral_congr_ae e1, integral_congr_ae e2]
      exact (integral_mul_martingale_eq hmartC hs.2 hbsm' hs2 (hproc2 T)).symm
    rw [h1, hexp, integral_add i123 i4, integral_add i12 i3', integral_add i1 i2,
      integral_finsetSum _ fun j _ => i3 j, hCs]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun j _ => hSj j
  -- integrability in time of the pieces
  have hint_s : ∀ (g : Ω → ℝ), MemLp g 2 P →
      Integrable (fun s => ∫ ω, b s ω * g ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun g hg => ((memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
      (memLp_two_prod_fst hg)).integral_prod_right
  have hint_Dr : Integrable (fun s => ∫ ω, b s ω * Dr s ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : Integrable (fun s => ∫ ω, b s ω * running b T (ω, s) ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      ((memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
        (memLp_two_running (P := P) hbm (hbq T hT))).integral_prod_right
    refine h1.congr ?_
    filter_upwards [hsw] with s hs
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact congrArg (fun x => b s ω * x) (running_eq hs)
  have hXs_int : ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, Dr T ω * X₀ ω ∂P + (1 / 2) * ∫ ω, Dr T ω * Dr T ω ∂P
        + (∑ j, ∫ ω, Dr T ω * S j T ω ∂P) + ∫ ω, Dr T ω * C T ω ∂P := by
    have i1 := hint_s X₀ hX₀2
    have i3 : ∀ j, Integrable (fun s => ∫ ω, b s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := fun j => hint_s _ (hS2 j T)
    have i3' : Integrable (fun s => ∑ j, ∫ ω, b s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := integrable_finsetSum _ fun j _ => i3 j
    have i4 := hint_s _ (hC2 T)
    have i12 : Integrable (fun s => ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := i1.add hint_Dr
    have i123 : Integrable (fun s => ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P
        + ∑ j, ∫ ω, b s ω * S j T ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) := i12.add i3'
    rw [integral_congr_ae hXb, integral_add i123 i4, integral_add i12 i3', integral_add i1 hint_Dr,
      integral_finsetSum _ fun j _ => i3 j, hDrX₀, hDrDr, hDrC,
      Finset.sum_congr rfl fun j _ => hDrS j]
    ring
  -- the pairing of the initial value with the drift, and the drift with the Brownian sum
  have hcomm : ∫ ω, X₀ ω * Dr T ω ∂P = ∫ ω, Dr T ω * X₀ ω ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have hDrSsum : ∫ ω, Dr T ω * (∑ j, S j T ω) ∂P = ∑ j, ∫ ω, Dr T ω * S j T ω ∂P := by
    have hexp : (fun ω => Dr T ω * (∑ j, S j T ω)) = fun ω => ∑ j, Dr T ω * S j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => Dr T ω * S j T ω) P := fun j =>
      (hDr2 T hT.le).integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
  -- expand the square of the decomposition at the horizon
  have hL : ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, (X₀ ω + Dr T ω + ((∑ j, S j T ω) + C T ω))
          * (X₀ ω + Dr T ω + ((∑ j, S j T ω) + C T ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hdec T hT.le] with ω hω
    rw [hω]
    ring
  have hf1 : MemLp (fun ω => X₀ ω + Dr T ω) 2 P := hX₀2.add (hDr2 T hT.le)
  have hg1 : MemLp (fun ω => (∑ j, S j T ω) + C T ω) 2 P := (hSsum2 T).add (hC2 T)
  rw [hL, integral_mul_self_add hf1 hg1, integral_mul_self_add hX₀2 (hDr2 T hT.le),
    integral_mul_self_add (hSsum2 T) (hC2 T),
    integral_add_mul_add hX₀2 (hDr2 T hT.le) (hSsum2 T) (hC2 T),
    hSsum_sq, hCiso, hSsum_C, hX₀Ssum, hX₀C, hXs_int, hcomm, hDrSsum]
  ring

end Scalar

section Vector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

/-- **The second moment of a vector Itô–Lévy process**, coordinate by coordinate: the expected
squared norm at the horizon is the sum of the scalar identities of the coordinates. -/
theorem integral_sum_mul_self_eq_of_isItoLevyProcess
    (h : ∀ i, LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (X i) (X₀ i) (b i)
      (σ i) (γ i))
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : ∀ i, StronglyMeasurable[ℱ 0] (X₀ i)) (hX₀2 : ∀ i, MemLp (X₀ i) 2 P)
    (hbm : ∀ i, Measurable (Function.uncurry fun ω s => b i s ω))
    (hbp : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b i s ω)
    (hbq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, ∑ i, X i T ω * X i T ω ∂P
      = ∑ i, (∫ ω, X₀ i ω * X₀ i ω ∂P
        + 2 * (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X i s ω * b i s ω ∂P)
        + (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖γ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal) := by
  have hX2 : ∀ i, MemLp (X i T) 2 P := fun i =>
    memLp_two_of_isItoLevyProcess (h i) (hX₀2 i) (hbm i) (hbq i) hT.le
  have hint : ∀ i, Integrable (fun ω => X i T ω * X i T ω) P := fun i =>
    (hX2 i).integrable_mul (hX2 i)
  rw [integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_self_eq_of_isItoLevyProcess (h i) 𝒲 (hX₀ i) (hX₀2 i) (hbm i) (hbp i) (hbq i) hT

end Vector

section Augmented

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- The second moment of an Itô–Lévy process over the augmented joint natural filtration of the
driver, where the driver itself supplies the cross witness. -/
theorem integral_mul_self_eq_of_isItoLevyProcess_aug
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug X X₀ b σ γ)
    (hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] X₀)
    (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + 2 * (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P)
        + (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal :=
  integral_mul_self_eq_of_isItoLevyProcess h D.crossWitness.aug hX₀ hX₀2 hbm hbp hbq hT

end Augmented

end LevyStochCalc.Ito.SecondMoment
