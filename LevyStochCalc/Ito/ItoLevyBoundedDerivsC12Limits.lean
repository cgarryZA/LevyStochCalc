/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.C12MollifyJoint
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands

/-!
# The Itô–Lévy integrands along a joint mollification

For a `C^{1,2}` function `u` of time and state and a family of bumps on `ℝ × (Fin n → ℝ)` whose
outer radii tend to `0`, the drift, diffusion, jump and compensator-drift integrands of the joint
mollifications of `u` converge pointwise to those of `u`, the time derivative, the gradient and
the Hessian of the mollification converging to their counterparts for `u`. When the derivatives
of `u` are bounded, the same bounds hold for every mollification, so along a jump diffusion the
drift integral over a window and the compensator-drift integral over a window and the mark space
converge almost surely, by dominated convergence against a bound built from the coefficients of
the equation alone.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.tendsto_diffusionIntegrand_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_sub_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegrand_mollifyJoint`,
  `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegrand_mollifyJoint` — pointwise
  convergence of the four integrands of the Itô–Lévy formula along the mollifications.
* `LevyStochCalc.Ito.JumpFormula.tendsto_driftIntegral_mollifyJoint` — almost-sure convergence of
  the drift integral along the path of a jump diffusion.
* `LevyStochCalc.Ito.JumpFormula.tendsto_compensatorDriftIntegral_mollifyJoint` — almost-sure
  convergence of the compensator-drift integral along the path of a jump diffusion.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Pointwise

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {u : ℝ → (Fin n → ℝ) → ℝ} {ι : Type*}
  {l : Filter ι} {φ : ι → ContDiffBump (0 : ℝ × (Fin n → ℝ))}

/-- Along a family of bumps whose outer radii tend to `0` the row product `(∇u)ᵀσ` of the joint
mollification of a `C^{1,2}` function converges to the row product of that function. -/
theorem tendsto_diffusionIntegrand_mollifyJoint (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0))
    (hu : IsC12 u) (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)) (s : ℝ) (x : Fin n → ℝ)
    (j : Fin d) :
    Tendsto (fun k => diffusionIntegrand (mollifyJoint u (φ k)) σ s x j) l
      (𝓝 (diffusionIntegrand u σ s x j)) := by
  simp only [diffusionIntegrand]
  exact tendsto_finsetSum _ fun i _ => (tendsto_gradient_mollifyJoint hφ hu s x i).mul_const _

/-- Along a family of bumps whose outer radii tend to `0` an increment of the joint mollification
of a `C^{1,2}` function converges to the corresponding increment of that function. -/
theorem tendsto_sub_mollifyJoint (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0)) (hu : IsC12 u)
    (s : ℝ) (y x : Fin n → ℝ) :
    Tendsto (fun k => mollifyJoint u (φ k) s y - mollifyJoint u (φ k) s x) l
      (𝓝 (u s y - u s x)) :=
  (tendsto_mollifyJoint hφ hu.continuous s y).sub (tendsto_mollifyJoint hφ hu.continuous s x)

omit [MeasurableSpace E] in
/-- Along a family of bumps whose outer radii tend to `0` the drift integrand `∂_t u + 𝓛u` of the
joint mollification of a `C^{1,2}` function converges to the drift integrand of that function. -/
theorem tendsto_driftIntegrand_mollifyJoint (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0))
    (hu : IsC12 u) (coeffs : JumpDiffusionCoeffs n d E) (s : ℝ) (x : Fin n → ℝ) :
    Tendsto (fun k => driftIntegrand (mollifyJoint u (φ k)) coeffs s x) l
      (𝓝 (driftIntegrand u coeffs s x)) := by
  simp only [driftIntegrand, levyGenerator]
  refine (tendsto_timeDeriv_mollifyJoint hφ hu s x).add (Tendsto.add ?_ ?_)
  · exact tendsto_finsetSum _ fun i _ => (tendsto_gradient_mollifyJoint hφ hu s x i).const_mul _
  · exact Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun m _ => (tendsto_hessian_mollifyJoint hφ hu s x i p).const_mul _)

omit [MeasurableSpace E] in
/-- Along a family of bumps whose outer radii tend to `0` the compensator-drift integrand of the
joint mollification of a `C^{1,2}` function converges to that of the function. -/
theorem tendsto_compensatorDriftIntegrand_mollifyJoint
    (hφ : Tendsto (fun k => (φ k).rOut) l (𝓝 0)) (hu : IsC12 u)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E) :
    Tendsto (fun k => compensatorDriftIntegrand (mollifyJoint u (φ k)) γ s x e) l
      (𝓝 (compensatorDriftIntegrand u γ s x e)) := by
  simp only [compensatorDriftIntegrand]
  refine ((tendsto_mollifyJoint hφ hu.continuous s (x + γ s x e)).sub
    (tendsto_mollifyJoint hφ hu.continuous s x)).sub ?_
  exact tendsto_finsetSum _ fun i _ => (tendsto_gradient_mollifyJoint hφ hu s x i).const_mul _

end Pointwise

section Integrals

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

/-- Along a family of bumps whose outer radii tend to `0` the drift integrals of the joint
mollifications of a `C^{1,2}` function with bounded derivatives converge almost surely to the
drift integral of that function along the solution. -/
theorem tendsto_driftIntegral_mollifyJoint (S : SdeData X) (hu : IsC12 u) {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀) (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) (φ : ℕ → ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ s in Set.Icc (0 : ℝ) T,
        driftIntegrand (mollifyJoint u (φ k)) coeffs s (X.X s ω)) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))) := by
  have hK₀' : ∀ s x, |timeDeriv u s x| ≤ max K₀ 0 :=
    fun s x => (hK₀ s x).trans (le_max_left _ _)
  have hK₁' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₂' : ∀ s x i j, |hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  have hvC : ∀ k, ContDiff ℝ 2 (Function.uncurry (mollifyJoint u (φ k))) :=
    fun k => contDiff_uncurry_mollifyJoint (N := 2) hu.continuous (φ k)
  have hv0 : ∀ k, ∀ s x, |timeDeriv (mollifyJoint u (φ k)) s x| ≤ max K₀ 0 :=
    fun k => abs_timeDeriv_mollifyJoint_le hu (φ k) hK₀'
  have hv1 : ∀ k, ∀ s x i, |gradient (mollifyJoint u (φ k)) s x i| ≤ max K₁ 0 :=
    fun k => abs_gradient_mollifyJoint_le hu (φ k) hK₁'
  have hv2 : ∀ k, ∀ s x i j, |hessian (mollifyJoint u (φ k)) s x i j| ≤ max K₂ 0 :=
    fun k => abs_hessian_mollifyJoint_le hu (φ k) hK₂'
  have hμint : ∀ᵐ ω ∂P, ∀ p : Fin n,
      IntegrableOn (fun s => coeffs.μ s (X.X s ω) p) (Set.Icc (0 : ℝ) T) :=
    MeasureTheory.ae_all_iff.mpr fun p =>
      ae_integrableOn_of_energy_lt_top (hμm p) (hμq p T hT)
  have hσsq : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d),
      IntegrableOn (fun s => coeffs.σ s (X.X s ω) p j ^ 2) (Set.Icc (0 : ℝ) T) := by
    refine MeasureTheory.ae_all_iff.mpr fun p => MeasureTheory.ae_all_iff.mpr fun j => ?_
    filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity (S.σ_meas p j) T)
      (S.σ_sq p j T hT).ne] with ω hω
    exact (LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
      (Measurable.of_uncurry_left (S.σ_meas p j)) hω).integrable_sq
  filter_upwards [hμint, hσsq] with ω hμω hσω
  have hXs : Measurable fun s => X.X s ω := X.measurable_path.of_uncurry_right
  refine tendsto_integral_of_dominated_convergence
    (fun s => max K₀ 0 + max K₁ 0 * ∑ p, |coeffs.μ s (X.X s ω) p|
      + (1 / 2) * max K₂ 0 * ∑ p, ∑ q, ∑ j,
        (coeffs.σ s (X.X s ω) p j ^ 2 + coeffs.σ s (X.X s ω) q j ^ 2) / 2) ?_ ?_ ?_ ?_
  · intro k
    refine Measurable.aestronglyMeasurable ?_
    change Measurable fun s => timeDeriv (mollifyJoint u (φ k)) s (X.X s ω)
      + ((∑ p, coeffs.μ s (X.X s ω) p * gradient (mollifyJoint u (φ k)) s (X.X s ω) p)
        + (1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s (X.X s ω) p j * coeffs.σ s (X.X s ω) q j
          * hessian (mollifyJoint u (φ k)) s (X.X s ω) p q)
    refine Measurable.add ((continuous_timeDeriv (hvC k)).measurable.comp
      (measurable_id.prodMk hXs)) (Measurable.add ?_ (measurable_const.mul ?_))
    · exact Finset.measurable_sum _ fun p _ => (Measurable.of_uncurry_left (hμm p)).mul
        ((continuous_gradient_uncurry (hvC k) p).measurable.comp (measurable_id.prodMk hXs))
    · refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
        Finset.measurable_sum _ fun j _ => ?_
      exact ((Measurable.of_uncurry_left (S.σ_meas p j)).mul
        (Measurable.of_uncurry_left (S.σ_meas q j))).mul
        ((continuous_hessian (hvC k) p q).measurable.comp (measurable_id.prodMk hXs))
  · refine Integrable.add (Integrable.add (integrable_const _) ?_) ?_
    · exact (integrable_finsetSum _ fun p _ => (hμω p).abs).const_mul _
    · refine Integrable.const_mul ?_ _
      refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
        integrable_finsetSum _ fun j _ => ?_
      exact ((hσω p j).add (hσω q j)).div_const 2
  · intro k
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact abs_mixedDriftIntegrand_le coeffs (le_max_right K₂ 0) (hv0 k) (hv1 k) (hv2 k) s _ _
  · exact Eventually.of_forall fun s =>
      tendsto_driftIntegrand_mollifyJoint hφ hu coeffs s (X.X s ω)

/-- Along a family of bumps whose outer radii tend to `0` the compensator-drift integrals of the
joint mollifications of a `C^{1,2}` function with a bounded Hessian converge almost surely to the
compensator-drift integral of that function along the solution. -/
theorem tendsto_compensatorDriftIntegral_mollifyJoint (S : SdeData X) (hu : IsC12 u) {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (T : ℝ) (hT : 0 < T)
    (φ : ℕ → ContDiffBump (0 : ℝ × (Fin n → ℝ)))
    (hφ : Tendsto (fun k => (φ k).rOut) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P, Tendsto (fun k => ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand (mollifyJoint u (φ k)) coeffs.γ s (X.X s ω) e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)) := by
  have hK₂' : ∀ s x i j, |hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  have hvC : ∀ k, ContDiff ℝ 2 (Function.uncurry (mollifyJoint u (φ k))) :=
    fun k => contDiff_uncurry_mollifyJoint (N := 2) hu.continuous (φ k)
  have hv2 : ∀ k, ∀ s x i j, |hessian (mollifyJoint u (φ k)) s x i j| ≤ max K₂ 0 :=
    fun k => abs_hessian_mollifyJoint_le hu (φ k) hK₂'
  have hγint : ∀ᵐ ω ∂P, ∀ i : Fin n, Integrable
      (fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 i ^ 2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [MeasureTheory.ae_lt_top (measurable_markEnergy
      (f := fun ω s e => (‖SmallJump.pathJumpCoeff coeffs X.X i ω s e‖₊ : ℝ≥0∞) ^ 2)
      (((S.γ_meas i).nnnorm.coe_nnreal_ennreal).pow_const 2) T) (S.γ_sq i T hT).ne]
      with ω hω
    have hm : Measurable fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 i :=
      (S.γ_meas i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
    have hfin : ∫⁻ p, (‖coeffs.γ p.1 (X.X p.1 ω) p.2 i‖₊ : ℝ≥0∞) ^ 2
        ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) < ⊤ := by
      rw [lintegral_prod _ ((hm.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable)]
      exact hω
    exact (memLp_two_of_lintegral_sq_lt_top hm.aestronglyMeasurable hfin).integrable_sq
  filter_upwards [hγint] with ω hγω
  have hγm : Measurable fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 :=
    measurable_pi_lambda _ fun i =>
      (S.γ_meas i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hmeas : ∀ k : ℕ, AEStronglyMeasurable (fun p : ℝ × E =>
      compensatorDriftIntegrand (mollifyJoint u (φ k)) coeffs.γ p.1 (X.X p.1 ω) p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) := by
    intro k
    refine Measurable.aestronglyMeasurable ?_
    have hX : Measurable fun p : ℝ × E => X.X p.1 ω :=
      X.measurable_path.of_uncurry_right.comp measurable_fst
    have hv : Measurable fun q : ℝ × (Fin n → ℝ) => mollifyJoint u (φ k) q.1 q.2 :=
      (hvC k).continuous.measurable
    change Measurable fun p : ℝ × E =>
      mollifyJoint u (φ k) p.1 (X.X p.1 ω + coeffs.γ p.1 (X.X p.1 ω) p.2)
        - mollifyJoint u (φ k) p.1 (X.X p.1 ω)
        - ∑ i, coeffs.γ p.1 (X.X p.1 ω) p.2 i * gradient (mollifyJoint u (φ k)) p.1
            (X.X p.1 ω) i
    refine Measurable.sub (Measurable.sub ?_ ?_) ?_
    · exact hv.comp (measurable_fst.prodMk (hX.add hγm))
    · exact hv.comp (measurable_fst.prodMk hX)
    · exact Finset.measurable_sum _ fun i _ => ((measurable_pi_apply i).comp hγm).mul
        ((continuous_gradient_uncurry (hvC k) i).measurable.comp (measurable_fst.prodMk hX))
  have hmain := tendsto_setIntegral_of_dominated (ν := ν) (T := T)
    (A := fun _ : ℕ => (∅ : Set E))
    (fs := fun k s e =>
      compensatorDriftIntegrand (mollifyJoint u (φ k)) coeffs.γ s (X.X s ω) e)
    (f := fun s e => compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e)
    (g := fun s e => (n : ℝ) ^ 2 * max K₂ 0 * ((n : ℝ) * ∑ i, coeffs.γ s (X.X s ω) e i ^ 2))
    (fun _ => MeasurableSet.empty)
    (Eventually.of_forall fun e => Eventually.of_forall fun _ => Set.notMem_empty e)
    hmeas ((((integrable_finsetSum _ fun i _ => hγω i).const_mul _).const_mul _))
    (fun k _s _hs e => abs_mixedCompensatorDriftIntegrand_le (hvC k) (hv2 k)
      (le_max_right K₂ 0) _ _ _ e)
    (fun s _hs e => tendsto_compensatorDriftIntegrand_mollifyJoint hφ hu coeffs.γ s
      (X.X s ω) e)
  simpa only [Set.compl_empty, Measure.restrict_univ] using hmain

end Integrals

end LevyStochCalc.Ito.JumpFormula
