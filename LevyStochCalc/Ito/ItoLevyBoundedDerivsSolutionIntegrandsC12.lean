/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands
import LevyStochCalc.Ito.JumpFormulaContinuityC12
import LevyStochCalc.Ito.C12Product

/-!
# Admissibility of the derived integrands of a `C^{1,2}` state function along a path

The two stochastic integrals of the Itô–Lévy formula carry the integrands `(∇u)ᵀσ` and
`u(x + γ) − u(x)` evaluated along a path. For a state function of class `C^{1,2}` with bounded
gradient and jointly measurable coefficients, each of these is jointly measurable, progressively
measurable in the sense its integral asks for, and of finite energy on every window on which the
coefficient along the path has; the compensator-drift integrand is jointly measurable and, for a
bounded Hessian, has finite mark energy on a window, almost surely.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurable_diffusionIntegrand_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_diffusionIntegrand_path_c12` — the
  admissibility of `(∇u)ᵀσ` along the path.
* `LevyStochCalc.Ito.JumpFormula.measurable_jumpIncrement_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_jumpIncrement_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_sq_jumpIncrement_path_lt_top_c12` — the admissibility
  of `u(x + γ) − u(x)` along the path.
* `LevyStochCalc.Ito.JumpFormula.measurable_compensatorDriftIntegrand_path_c12`,
  `LevyStochCalc.Ito.JumpFormula.ae_lintegral_compensatorDriftIntegrand_lt_top_c12` — the
  measurability and the mark integrability of the compensator-drift integrand along the path.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section DerivedIntegrands

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {coeffs : JumpDiffusionCoeffs n d E} {u : ℝ → (Fin n → ℝ) → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a `C^{1,2}` state function along a jointly measurable
path is jointly measurable. -/
theorem measurable_diffusionIntegrand_path_c12 (hu : IsC12 u)
    (hσ : Measurable (Function.uncurry coeffs.σ)) (hXm : Measurable (Function.uncurry X))
    (j : Fin d) :
    Measurable (Function.uncurry fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j) := by
  have hstate : Measurable fun p : Ω × ℝ => ((p.2, X p.2 p.1) : ℝ × (Fin n → ℝ)) :=
    measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst))
  change Measurable fun p : Ω × ℝ =>
    ∑ i, gradient u p.2 (X p.2 p.1) i * coeffs.σ p.2 (X p.2 p.1) i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (hu.continuous_gradient i).measurable.comp hstate
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)).comp hstate

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a `C^{1,2}` state function along a progressively
measurable path is progressively measurable. -/
theorem progressivelyMeasurable_diffusionIntegrand_path_c12
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : IsC12 u) (hσ : Measurable (Function.uncurry coeffs.σ))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) (j : Fin d) :
    ProgressivelyMeasurable ℱ fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j := by
  refine progressivelyMeasurable_comp_state hXa
    (f := fun s x => diffusionIntegrand u coeffs.σ s x j) ?_
  change Measurable fun q : ℝ × (Fin n → ℝ) => ∑ i, gradient u q.1 q.2 i * coeffs.σ q.1 q.2 i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (hu.continuous_gradient i).measurable
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The jump increment `u(x + γ) − u(x)` of a `C^{1,2}` state function along a jointly measurable
path is jointly measurable. -/
theorem measurable_jumpIncrement_path_c12 (hu : IsC12 u)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X)) :
    Measurable fun p : Ω × ℝ × E =>
      (fun ω' s e => u s (X s ω' + coeffs.γ s (X s ω') e) - u s (X s ω')) p.1 p.2.1 p.2.2 := by
  have hXp : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγp : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 :=
    hγ.comp (measurable_snd.fst.prodMk (hXp.prodMk measurable_snd.snd))
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  exact (hu'.comp (measurable_snd.fst.prodMk (hXp.add hγp))).sub
    (hu'.comp (measurable_snd.fst.prodMk hXp))

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The jump increment `u(x + γ) − u(x)` of a `C^{1,2}` state function along a progressively
measurable path is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_jumpIncrement_path_c12
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : IsC12 u)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) :
    MarkedProgressivelyMeasurable ℱ
      fun ω' s e => u s (X s ω' + coeffs.γ s (X s ω') e) - u s (X s ω') := by
  refine markedProgressivelyMeasurable_comp_state hXa
    (g := fun s x e => u s (x + coeffs.γ s x e) - u s x) ?_
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  exact (hu'.comp (measurable_fst.prodMk (measurable_snd.fst.add hγ))).sub
    (hu'.comp (measurable_fst.prodMk measurable_snd.fst))

omit [IsProbabilityMeasure P] in
/-- The jump increment `u(x + γ) − u(x)` of a `C^{1,2}` state function with a bounded gradient has
finite energy on every window on which the jump coefficient along the path has. -/
theorem lintegral_sq_jumpIncrement_path_lt_top_c12 (hu : IsC12 u) {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hγm : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖u s (X s ω + coeffs.γ s (X s ω) e) - u s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hK₁' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  refine lintegral_window_mark_sq_le_of_abs_le (a := fun i ω s e => coeffs.γ s (X s ω) e i)
    (c := n * max K₁ 0) (fun i => hγm i) (fun ω s e => ?_) T' (fun i => hγq i T' hT')
  exact abs_mixedJumpIncrement_le_c12 hu hK₁' (le_max_right _ _) s (X s ω) (X s ω) e

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator-drift integrand of a `C^{1,2}` state function along a jointly measurable path
is jointly measurable. -/
theorem measurable_compensatorDriftIntegrand_path_c12 (hu : IsC12 u)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X)) :
    Measurable fun p : Ω × ℝ × E =>
      compensatorDriftIntegrand u coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 := by
  have hXp : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγp : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 :=
    hγ.comp (measurable_snd.fst.prodMk (hXp.prodMk measurable_snd.snd))
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  have hstate : Measurable fun p : Ω × ℝ × E => ((p.2.1, X p.2.1 p.1) : ℝ × (Fin n → ℝ)) :=
    measurable_snd.fst.prodMk hXp
  change Measurable fun p : Ω × ℝ × E =>
    u p.2.1 (X p.2.1 p.1 + coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2) - u p.2.1 (X p.2.1 p.1)
      - ∑ i, coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i * gradient u p.2.1 (X p.2.1 p.1) i
  refine ((hu'.comp (measurable_snd.fst.prodMk (hXp.add hγp))).sub (hu'.comp hstate)).sub
    (Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_)
  · exact (measurable_pi_apply i).comp hγp
  · exact (hu.continuous_gradient i).measurable.comp hstate

omit [IsProbabilityMeasure P] in
/-- The compensator-drift integrand of a `C^{1,2}` state function with a bounded Hessian is
integrable over the marks and a window, almost surely, when the jump coefficient along the path
has finite energy on that window. -/
theorem ae_lintegral_compensatorDriftIntegrand_lt_top_c12 (hu : IsC12 u)
    {K₂ : ℝ} (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X))
    (hγm : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤ := by
  have hK₂' : ∀ s x i j, |hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  set C : ℝ := (n : ℝ) ^ 2 * max K₂ 0 * n with hC
  have hC0 : 0 ≤ C := by positivity
  -- the pointwise bound, in extended form
  have hpt : ∀ ω s e, (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal C * ∑ i, (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s e
    have hreal : |compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
        ≤ C * ∑ i, coeffs.γ s (X s ω) e i ^ 2 := by
      have h := abs_mixedCompensatorDriftIntegrand_le_c12 hu (γ := coeffs.γ) hK₂'
        (le_max_right _ _) s (X s ω) (X s ω) e
      rw [hC]
      calc |compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
          ≤ (n : ℝ) ^ 2 * max K₂ 0 * ((n : ℝ) * ∑ i, coeffs.γ s (X s ω) e i ^ 2) := h
        _ = (n : ℝ) ^ 2 * max K₂ 0 * n * ∑ i, coeffs.γ s (X s ω) e i ^ 2 := by ring
    rw [show ((‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞))
        = ‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖ₑ from rfl,
      Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
        ≤ ENNReal.ofReal (C * ∑ i, coeffs.γ s (X s ω) e i ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C * ∑ i, (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl fun i _ => (sq_coe_nnnorm_real _).symm)
  have hm : ∀ i, Measurable fun p : Ω × ℝ × E =>
      (‖coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (((hγm i).nnnorm).coe_nnreal_ennreal).pow_const 2
  -- the energy of the integrand is finite
  have houter : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt
      (lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e) ?_
    have hC' : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    simp_rw [lintegral_const_mul' _ _ hC']
    rw [lintegral_window_mark_sum
      (f := fun i ω s e => (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2) hm T]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.mpr fun i _ => hγq i T hT)
  have hfm : Measurable fun p : Ω × ℝ × E =>
      (‖compensatorDriftIntegrand u coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2‖₊ : ℝ≥0∞) :=
    (measurable_compensatorDriftIntegrand_path_c12 hu hγ hXm).nnnorm.coe_nnreal_ennreal
  exact ae_lt_top (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
    (f := fun ω s e => (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞)) hfm T)
    houter.ne

end DerivedIntegrands

end LevyStochCalc.Ito.JumpFormula
