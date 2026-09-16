/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivs
import LevyStochCalc.Ito.PicardWellPosed
import LevyStochCalc.Ito.PicardLocality
import LevyStochCalc.Ito.SdeDataOfSolvesOn

/-!
# Admissibility of the derived integrands along a path

The two stochastic integrals of the Itô–Lévy formula at bounded derivatives carry the integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` evaluated along a path. For a `C²` state function with bounded
gradient and coefficients that are regular and Lipschitz, each of these is jointly measurable,
progressively measurable in the sense its integral asks for, and of finite energy on every
window; along the path the drift is integrable and the compensator-drift integrand has finite
mark energy, almost surely.
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
/-- The diffusion integrand `(∇u)ᵀσ` of a `C²` state function along a jointly measurable path is
jointly measurable. -/
theorem measurable_diffusionIntegrand_path (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hσ : Measurable (Function.uncurry coeffs.σ)) (hXm : Measurable (Function.uncurry X))
    (j : Fin d) :
    Measurable (Function.uncurry fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j) := by
  have hstate : Measurable fun p : Ω × ℝ => ((p.2, X p.2 p.1) : ℝ × (Fin n → ℝ)) :=
    measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst))
  change Measurable fun p : Ω × ℝ =>
    ∑ i, gradient u p.2 (X p.2 p.1) i * coeffs.σ p.2 (X p.2 p.1) i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (continuous_gradient_uncurry hu i).measurable.comp hstate
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)).comp hstate

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a `C²` state function along a progressively measurable
path is progressively measurable. -/
theorem progressivelyMeasurable_diffusionIntegrand_path {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (hσ : Measurable (Function.uncurry coeffs.σ))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) (j : Fin d) :
    ProgressivelyMeasurable ℱ fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j := by
  refine progressivelyMeasurable_comp_state hXa
    (f := fun s x => diffusionIntegrand u coeffs.σ s x j) ?_
  change Measurable fun q : ℝ × (Fin n → ℝ) => ∑ i, gradient u q.1 q.2 i * coeffs.σ q.1 q.2 i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (continuous_gradient_uncurry hu i).measurable
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a state function with a bounded gradient has finite
energy on every window on which the diffusion coefficient along the path has. -/
theorem lintegral_sq_diffusionIntegrand_path_lt_top {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hσm : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j))
    (hσq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hK₁' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  refine lintegral_window_sq_le_of_abs_le (a := fun i ω s => coeffs.σ s (X s ω) i j)
    (c := max K₁ 0) (fun i => hσm i j) (fun ω s => ?_) T' (fun i => hσq i j T' hT')
  exact abs_mixedDiffusionIntegrand_le hK₁' s (X s ω) (X s ω) j

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The jump increment `u(x + γ) − u(x)` of a `C²` state function along a jointly measurable
path is jointly measurable. -/
theorem measurable_jumpIncrement_path (hu : ContDiff ℝ 2 (Function.uncurry u))
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
/-- The jump increment `u(x + γ) − u(x)` of a `C²` state function along a progressively
measurable path is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_jumpIncrement_path {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : ContDiff ℝ 2 (Function.uncurry u))
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
/-- The jump increment `u(x + γ) − u(x)` of a state function with a bounded gradient has finite
energy on every window on which the jump coefficient along the path has. -/
theorem lintegral_sq_jumpIncrement_path_lt_top (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₁ : ℝ}
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
  exact abs_mixedJumpIncrement_le hu hK₁' (le_max_right _ _) s (X s ω) (X s ω) e

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The drift along a path of finite drift energy is integrable on every window, almost surely.
-/
theorem ae_integrableOn_drift_path
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ i : Fin n, IntegrableOn (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) T) := by
  rw [ae_all_iff]
  intro i
  filter_upwards [ae_integrableOn_of_lintegral_sq (hμm i) (hμq i)] with ω hω
  exact hω T

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator-drift integrand of a `C²` state function along a jointly measurable path is
jointly measurable. -/
theorem measurable_compensatorDriftIntegrand_path (hu : ContDiff ℝ 2 (Function.uncurry u))
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
  · exact (continuous_gradient_uncurry hu i).measurable.comp hstate

omit [IsProbabilityMeasure P] in
/-- The compensator-drift integrand of a state function with a bounded Hessian is integrable over
the marks and a window, almost surely, when the jump coefficient along the path has finite energy
on that window. -/
theorem ae_lintegral_compensatorDriftIntegrand_lt_top (hu : ContDiff ℝ 2 (Function.uncurry u))
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
      have h := abs_mixedCompensatorDriftIntegrand_le hu (γ := coeffs.γ) hK₂' (le_max_right _ _)
        s (X s ω) (X s ω) e
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
    (measurable_compensatorDriftIntegrand_path hu hγ hXm).nnnorm.coe_nnreal_ennreal
  exact ae_lt_top (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
    (f := fun ω s e => (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞)) hfm T)
    houter.ne

end DerivedIntegrands

end LevyStochCalc.Ito.JumpFormula
