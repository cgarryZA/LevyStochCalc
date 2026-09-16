/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.FiniteActivityMixedPrelims
import LevyStochCalc.Ito.ItoLevyMixedBounds
import LevyStochCalc.Ito.ItoFormulaMeasurableShift
import LevyStochCalc.Ito.JumpFormulaAssembly
import LevyStochCalc.Ito.JumpFormulaChainStopped
import LevyStochCalc.Ito.MarkedZeroExtension
import LevyStochCalc.Ito.JumpCoefficientPredictableZeroExt
import LevyStochCalc.Probability.MarkedPredictableComp

/-!
# Steps of the finite-activity Itô–Lévy identity in the mixed form

Regularity of the time-augmented path, window integrability of the mixed integrands, the
dictionary identifying the time-augmented drift and quadratic terms with the mixed drift
integrand, and the predictability and admissibility of the mixed jump increment read at the
left limits.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_timeAugProcess`
* `LevyStochCalc.Ito.JumpFormula.measurable_timeAugProcess_adapted`
* `LevyStochCalc.Ito.JumpFormula.tendsto_timeAugProcess_nhdsWithin_gt`
* `LevyStochCalc.Ito.JumpFormula.ae_integrableOn_mixed_window`
* `LevyStochCalc.Ito.JumpFormula.ae_setIntegral_timeAug_eq_mixedDrift`
* `LevyStochCalc.Ito.JumpFormula.admissible_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.ae_countable_setOf_leftLim_ne_pair`
* `LevyStochCalc.Ito.JumpFormula.markedPredictable_zeroExtPos_mixedJumpIncrement_leftLim`
* `LevyStochCalc.Ito.JumpFormula.lintegral_referenceIntensity_window_ne_top`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section TimeAug

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ} {y : ℝ → Ω → Fin n → ℝ}

/-- The time augmentation of a jointly measurable path is jointly measurable. -/
theorem measurable_uncurry_timeAugProcess (hy_m : Measurable (Function.uncurry y)) :
    Measurable (Function.uncurry fun ω s => timeAugProcess y s ω) := by
  refine measurable_pi_iff.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [Function.uncurry, timeAugProcess, Fin.cons_zero]
    exact measurable_snd
  | succ q =>
    simp only [Function.uncurry, timeAugProcess, Fin.cons_succ]
    exact (measurable_pi_apply q).comp (hy_m.comp (measurable_snd.prodMk measurable_fst))

/-- The time augmentation of a path adapted to a filtration is adapted to that filtration. -/
theorem measurable_timeAugProcess_adapted (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hy_ad : ∀ t : ℝ, Measurable[ℱ t] (y t)) (t : ℝ) :
    Measurable[ℱ t] (timeAugProcess y t) := by
  letI : MeasurableSpace Ω := ℱ t
  refine measurable_pi_iff.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugProcess, Fin.cons_zero]
    exact measurable_const
  | succ q =>
    simp only [timeAugProcess, Fin.cons_succ]
    exact (measurable_pi_apply q).comp (hy_ad t)

omit [MeasurableSpace Ω] in
/-- The time augmentation of a right-continuous path is right-continuous. -/
theorem tendsto_timeAugProcess_nhdsWithin_gt
    (hy_rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω)))
    (ω : Ω) (t : ℝ) :
    Tendsto (fun s => timeAugProcess y s ω) (𝓝[>] t) (𝓝 (timeAugProcess y t ω)) := by
  refine tendsto_pi_nhds.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugProcess, Fin.cons_zero]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  | succ q =>
    simp only [timeAugProcess, Fin.cons_succ]
    exact ((continuous_apply q).tendsto _).comp (hy_rc ω t)

end TimeAug

section Mixed

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- On a window `[0, T]` and a mark set `B` of finite intensity, the jump coefficient and the
mixed jump increment along `y` are almost surely integrable in the mark at almost every time,
and the mark integral of the mixed jump increment, the first-order term and the mixed drift
integrand are almost surely integrable in time. -/
theorem ae_integrableOn_mixed_window (S : SdeData X)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    {B : Set E} (hBν : ν B ≠ ⊤)
    (y : ℝ → Ω → Fin n → ℝ) (hy_m : Measurable (Function.uncurry y)) :
    ∀ᵐ ω ∂P,
      (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
        IntegrableOn (fun e => coeffs.γ s (X.X s ω) e i) B ν)
      ∧ (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) B ν)
      ∧ IntegrableOn (fun s => ∫ e in B, mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e ∂ν)
          (Set.Icc (0 : ℝ) T) volume
      ∧ IntegrableOn (fun s => ∑ i : Fin n,
          gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν)
          (Set.Icc (0 : ℝ) T) volume
      ∧ IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω))
          (Set.Icc (0 : ℝ) T) volume := by
  haveI hBfin : IsFiniteMeasure (ν.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hBν⟩
  have hK₁'' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₁0' : (0 : ℝ) ≤ max K₁ 0 := le_max_right _ _
  have hyω : ∀ ω : Ω, Measurable fun s => y s ω :=
    fun ω => hy_m.comp (measurable_id.prodMk measurable_const)
  have hγsec : ∀ (ω : Ω) (s : ℝ), Measurable fun e => coeffs.γ s (X.X s ω) e :=
    fun ω s => hγmeas.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  -- the jump coefficient at the point values is square integrable in the mark at a.e. time
  have hγL2 : ∀ i : Fin n, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∫⁻ e, (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν < ⊤ := by
    intro i
    filter_upwards [MeasureTheory.ae_lt_top (measurable_markEnergy
      (f := fun ω s e => (‖SmallJump.pathJumpCoeff coeffs X.X i ω s e‖₊ : ℝ≥0∞) ^ 2)
      (((S.γ_meas i).nnnorm.coe_nnreal_ennreal).pow_const 2) T) (S.γ_sq i T hT).ne] with ω hω
    exact MeasureTheory.ae_lt_top ((((S.γ_meas i).nnnorm.coe_nnreal_ennreal).pow_const 2).comp
      (by fun_prop :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).lintegral_prod_right' hω.ne
  have hγi : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (X.X s ω) e i) B ν := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hγL2] with ω hω
    filter_upwards [MeasureTheory.ae_all_iff.mpr hω] with s hs i
    exact ((memLp_two_of_lintegral_sq_lt_top
      ((measurable_pi_apply i).comp (hγsec ω s)).aestronglyMeasurable
      (hs i)).restrict B).integrable one_le_two
  -- the mark integrals of the point-evaluated jump coefficient and of its absolute value are
  -- integrable in time
  have hmarkInt : ∀ i : Fin n, ∀ᵐ ω ∂P,
      IntegrableOn (fun s => ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν) (Set.Icc (0 : ℝ) T)
        volume := by
    intro i
    refine ae_integrableOn_of_energy_lt_top
      (stronglyMeasurable_setIntegral_mark B (SmallJump.pathJumpCoeff coeffs X.X i)
        (S.γ_meas i)).measurable ?_
    exact lt_of_le_of_lt (lintegral_sq_setIntegral_mark_le hBν _ (S.γ_meas i) T)
      (ENNReal.mul_lt_top (S.γ_sq i T hT) (lt_top_iff_ne_top.mpr hBν))
  have hmarkAbs : ∀ i : Fin n, ∀ᵐ ω ∂P,
      IntegrableOn (fun s => ∫ e in B, |coeffs.γ s (X.X s ω) e i| ∂ν) (Set.Icc (0 : ℝ) T)
        volume := by
    intro i
    refine ae_integrableOn_of_energy_lt_top
      (stronglyMeasurable_setIntegral_mark B
        (fun ω s e => |SmallJump.pathJumpCoeff coeffs X.X i ω s e|)
        (S.γ_meas i).abs).measurable ?_
    refine lt_of_le_of_lt (lintegral_sq_setIntegral_mark_le hBν _ (S.γ_meas i).abs T) ?_
    refine ENNReal.mul_lt_top ?_ (lt_top_iff_ne_top.mpr hBν)
    simpa [SmallJump.pathJumpCoeff] using S.γ_sq i T hT
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
  have hΔm : Measurable fun p : Ω × ℝ × E =>
      mixedJumpIncrement u coeffs.γ p.2.1 (y p.2.1 p.1) (X.X p.2.1 p.1) p.2.2 := by
    have hy : Measurable fun p : Ω × ℝ × E => y p.2.1 p.1 :=
      hy_m.comp (measurable_snd.fst.prodMk measurable_fst)
    have hγ : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 :=
      measurable_pi_lambda _ fun i => S.γ_meas i
    exact (hu.continuous.measurable.comp (measurable_snd.fst.prodMk (hy.add hγ))).sub
      (hu.continuous.measurable.comp (measurable_snd.fst.prodMk hy))
  filter_upwards [hγi, MeasureTheory.ae_all_iff.mpr hmarkInt,
    MeasureTheory.ae_all_iff.mpr hmarkAbs, hμint, hσsq] with ω hγω hmiω hmaω hμω hσω
  have hΔω : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) B ν := by
    filter_upwards [hγω] with s hs
    refine Integrable.mono'
      (g := fun e => (n : ℝ) * max K₁ 0 * ∑ i, |coeffs.γ s (X.X s ω) e i|)
      ((integrable_finsetSum Finset.univ fun i _ => (hs i).abs).const_mul
        ((n : ℝ) * max K₁ 0)) ?_ ?_
    · exact ((hu.continuous.measurable.comp (measurable_const.prodMk
        (measurable_const.add (hγsec ω s)))).sub measurable_const).aestronglyMeasurable
    · filter_upwards with e
      rw [Real.norm_eq_abs]
      exact abs_mixedJumpIncrement_le hu hK₁'' hK₁0' s _ _ e
  refine ⟨hγω, hΔω, ?_, ?_, ?_⟩
  · -- the mark integral of the mixed jump increment is integrable in time
    refine Integrable.mono'
      (g := fun s => (n : ℝ) * max K₁ 0 * ∑ i, ∫ e in B, |coeffs.γ s (X.X s ω) e i| ∂ν)
      ((integrable_finsetSum Finset.univ fun i _ => hmaω i).const_mul
        ((n : ℝ) * max K₁ 0)) ?_ ?_
    · exact ((stronglyMeasurable_setIntegral_mark B
        (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) hΔm).comp_measurable
        measurable_prodMk_left).aestronglyMeasurable
    · filter_upwards [hγω] with s hs
      have hgint : Integrable (fun e => (n : ℝ) * max K₁ 0 * ∑ i, |coeffs.γ s (X.X s ω) e i|)
          (ν.restrict B) :=
        (integrable_finsetSum Finset.univ fun i _ => (hs i).abs).const_mul _
      refine (norm_integral_le_of_norm_le hgint ?_).trans (le_of_eq ?_)
      · filter_upwards with e
        rw [Real.norm_eq_abs]
        exact abs_mixedJumpIncrement_le hu hK₁'' hK₁0' s _ _ e
      · rw [integral_const_mul, integral_finsetSum _ fun i _ => (hs i).abs]
  · -- the first-order term is integrable in time
    refine integrable_finsetSum _ fun i _ => Integrable.bdd_mul (c := K₁) (hmiω i) ?_ ?_
    · exact ((continuous_gradient_uncurry hu i).measurable.comp
        (measurable_id.prodMk (hyω ω))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun s => by
        rw [Real.norm_eq_abs]; exact hK₁ s _ i
  · -- the mixed drift integrand is integrable in time
    have hK₀' : ∀ s x, |timeDeriv u s x| ≤ max K₀ 0 :=
      fun s x => (hK₀ s x).trans (le_max_left _ _)
    have hK₂'' : ∀ s x i j, |hessian u s x i j| ≤ max K₂ 0 :=
      fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
    have hK₂0 : (0 : ℝ) ≤ max K₂ 0 := le_max_right _ _
    refine Integrable.mono' (g := fun s => max K₀ 0 + max K₁ 0 * ∑ p, |coeffs.μ s (X.X s ω) p|
      + (1 / 2) * max K₂ 0 * ∑ p, ∑ q, ∑ j,
        (coeffs.σ s (X.X s ω) p j ^ 2 + coeffs.σ s (X.X s ω) q j ^ 2) / 2) ?_ ?_ ?_
    · refine Integrable.add (Integrable.add (integrable_const _) ?_) ?_
      · exact (integrable_finsetSum _ fun p _ => (hμω p).abs).const_mul _
      · refine Integrable.const_mul ?_ _
        refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
          integrable_finsetSum _ fun j _ => ?_
        exact ((hσω p j).add (hσω q j)).div_const 2
    · refine Measurable.aestronglyMeasurable ?_
      refine Measurable.add ((continuous_timeDeriv hu).measurable.comp
        (measurable_id.prodMk (hyω ω))) (Measurable.add ?_ (measurable_const.mul ?_))
      · exact Finset.measurable_sum _ fun p _ => (Measurable.of_uncurry_left (hμm p)).mul
          ((continuous_gradient_uncurry hu p).measurable.comp (measurable_id.prodMk (hyω ω)))
      · refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
          Finset.measurable_sum _ fun j _ => ?_
        exact ((Measurable.of_uncurry_left (S.σ_meas p j)).mul
          (Measurable.of_uncurry_left (S.σ_meas q j))).mul
          ((continuous_hessian hu p q).measurable.comp (measurable_id.prodMk (hyω ω)))
    · refine Filter.Eventually.of_forall fun s => ?_
      rw [Real.norm_eq_abs]
      exact abs_mixedDriftIntegrand_le coeffs hK₂0 hK₀' hK₁'' hK₂'' s _ _

/-- Along a càdlàg path, the time-augmented drift and quadratic integrals of a time-augmented
`C²` state function are the integral of the mixed drift integrand net of the compensator drift
over a mark set. -/
theorem ae_setIntegral_timeAug_eq_mixedDrift
    {f : (Fin (n + 1) → ℝ) → ℝ}
    {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
    {u : ℝ → (Fin n → ℝ) → ℝ} (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (B : Set E) (T : ℝ) (hT : 0 < T) (y : ℝ → Ω → Fin n → ℝ)
    (bdr : Fin n → Ω → ℝ → ℝ)
    (hbdr : ∀ (i : Fin n) (ω : Ω) (s : ℝ),
      bdr i ω s = continuousDriftLeftAt coeffs ν X.X B i ω s)
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hH : ∀ (i : Fin n) (j : Fin d) (ω : Ω) (s : ℝ), H i j ω s = coeffs.σ s (X.X s ω) i j)
    (hmD : ∀ p : Fin (n + 1), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s))
    (hqD : ∀ (p : Fin (n + 1)) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (timeAugProcess y s ω)
        * ∑ j : Fin d, timeAugDiffusion H p j ω s * timeAugDiffusion H q j ω s)
      (Set.Ioc (0 : ℝ) T) volume) :
    ∀ᵐ ω ∂P, (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (timeAugProcess y s ω)
              * (∑ j : Fin d, timeAugDiffusion H p j ω s * timeAugDiffusion H q j ω s) ∂volume
      = ∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω)
          - ∑ i : Fin n, gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν) := by
  have hDint : ∀ᵐ ω ∂P, ∀ p : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s)
      (Set.Ioc (0 : ℝ) T) volume :=
    MeasureTheory.ae_all_iff.mpr fun p => ae_integrableOn_Ioc_of_energy (hmD p) (hqD p T hT)
  filter_upwards [hDint, hQint, X.cadlag_paths] with ω hDω hQω hcadω
  set bpt : Fin (n + 1) → ℝ → ℝ := fun p s => timeAugDrift
    (fun q (_ : Ω) s => coeffs.μ s (X.X s ω) q - ∫ e in B, coeffs.γ s (X.X s ω) e q ∂ν) p ω s
    with hbptdef
  have hcount : {s : ℝ | 0 < s ∧ leftLimPathAt X.X s ω ≠ X.X s ω}.Countable :=
    countable_setOf_pos_leftLimPathAt_ne (fun t ht => (hcadω t ht).1)
      (fun t ht i => (hcadω t ht.le).2 i)
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), leftLimPathAt X.X s ω = X.X s ω :=
    ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self
      (LevyStochCalc.Ito.ae_restrict_eq_of_countable_ne hcount T)
  have hbeq : ∀ p : Fin (n + 1), ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s
        = coordDeriv f' p (timeAugProcess y s ω) * bpt p s := by
    intro p
    induction p using Fin.cases with
    | zero => exact Filter.Eventually.of_forall fun s => rfl
    | succ q =>
      filter_upwards [hae] with s hs
      simp only [bpt, timeAugDrift, Fin.cons_succ, hbdr, continuousDriftLeftAt, hs]
  have hD' : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv f' p (timeAugProcess y s ω) * bpt p s) (Set.Ioc (0 : ℝ) T) volume :=
    fun p => (hDω p).congr_fun_ae (hbeq p)
  have hdrift_eq : ∀ p : Fin (n + 1), (∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (timeAugProcess y s ω) * timeAugDrift bdr p ω s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (timeAugProcess y s ω) * bpt p s ∂volume :=
    fun p => integral_congr_ae (hbeq p)
  rw [Finset.sum_congr rfl fun p _ => hdrift_eq p, setIntegral_Icc_eq_setIntegral_Ioc]
  exact setIntegral_splitDrift_dictionary_mixed hfu hf hf' coeffs B T (fun s => y s ω)
    (fun s => X.X s ω) bpt (fun p j s => timeAugDiffusion H p j ω s) (fun s => rfl)
    (fun q s => rfl) (fun j s => rfl) (fun p j s => hH p j ω s) hD' hQω

/-- The mixed jump increment read at the left limits is jointly measurable, marked
progressively measurable, and of finite mark energy on every bounded window. -/
theorem admissible_mixedJumpIncrement_leftLim (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    {u : ℝ → (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₁ : ℝ} (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    {y : ℝ → Ω → Fin n → ℝ} (hy_m : Measurable (Function.uncurry y))
    (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L))
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Measurable (fun p : Ω × ℝ × E => mixedJumpIncrement u coeffs.γ p.2.1
        (leftLimPathAt y p.2.1 p.1) (leftLimPathAt X.X p.2.1 p.1) p.2.2)
      ∧ Probability.MarkedProgressivelyMeasurable S.ℱ (fun ω s e =>
          mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω) (leftLimPathAt X.X s ω) e)
      ∧ ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω)
            (leftLimPathAt X.X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hK₁'' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₁0' : (0 : ℝ) ≤ max K₁ 0 := le_max_right _ _
  have hyLm : Measurable fun q : ℝ × Ω => leftLimPathAt y q.1 q.2 :=
    measurable_uncurry_leftLimPathAt hy_m hy_left
  refine ⟨?_, ?_, fun T' hT' => ?_⟩
  · have hy : Measurable fun p : Ω × ℝ × E => leftLimPathAt y p.2.1 p.1 :=
      hyLm.comp (measurable_snd.fst.prodMk measurable_fst)
    have hγ : Measurable fun p : Ω × ℝ × E =>
        coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 :=
      measurable_pi_lambda _ fun i => hγmL i
    exact (hu.continuous.measurable.comp (measurable_snd.fst.prodMk (hy.add hγ))).sub
      (hu.continuous.measurable.comp (measurable_snd.fst.prodMk hy))
  · have hZ := markedProgressivelyMeasurable_time_state_jump (ℱ := S.ℱ) (coeffs := coeffs)
      (Xp := leftLimPathAt X.X) (Y := leftLimPathAt y)
      (fun i => progressivelyMeasurable_leftLimPathAt hℱ0 hy_ad hy_left i) hγpL
    have hg : Continuous fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
        u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1 :=
      (hu.continuous.comp (continuous_fst.prodMk
        (continuous_snd.fst.add continuous_snd.snd))).sub
        (hu.continuous.comp (continuous_fst.prodMk continuous_snd.fst))
    have hg0 : (fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
        u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1) 0 = 0 := by simp
    exact hg.comp_markedProgressivelyMeasurable hg0 hZ
  · exact lintegral_window_mark_sq_le_of_abs_le
      (a := fun i ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i) (c := n * max K₁ 0) hγmL
      (fun ω s e => abs_mixedJumpIncrement_le hu hK₁'' hK₁0' s _ _ e) T'
      (fun i => hγqL i T' hT')

/-- Away from a countable set of times the path and its left limit agree, jointly for a
càdlàg jump diffusion and a càdlàg path with left limits. -/
theorem ae_countable_setOf_leftLim_ne_pair {y : ℝ → Ω → Fin n → ℝ}
    (hy_rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω)))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧
      ((leftLimPathAt y s ω, leftLimPathAt X.X s ω) : (Fin n → ℝ) × (Fin n → ℝ))
        ≠ (y s ω, X.X s ω)}.Countable := by
  filter_upwards [X.cadlag_paths] with ω hcad
  exact countable_setOf_pos_ne_pair (Y₁ := leftLimPathAt y) (Z₁ := y)
    (Y₂ := leftLimPathAt X.X) (Z₂ := X.X)
    (countable_setOf_pos_leftLimPathAt_ne (fun t _ => hy_rc ω t) (fun t _ i => hy_left ω t i))
    (countable_setOf_pos_leftLimPathAt_ne (fun t ht => (hcad t ht).1)
      (fun t ht i => (hcad t ht.le).2 i))

/-- The zero extension to the positive times of the mixed jump increment read at the left
limits is marked predictable. -/
theorem markedPredictable_zeroExtPos_mixedJumpIncrement_leftLim (S : SdeData X)
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγmeasi : ∀ i : Fin n,
      Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i)
    {u : ℝ → (Fin n → ℝ) → ℝ} (hu : ContDiff ℝ 2 (Function.uncurry u))
    {y : ℝ → Ω → Fin n → ℝ} (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L)) :
    MarkedPredictable S.ℱ ν (zeroExtPos fun ω s e =>
      mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω) (leftLimPathAt X.X s ω) e) := by
  have hY := measurable_predictableSigma_leftLimPathAtPos y S.ℱ hy_ad
    (fun ω t _ i => hy_left ω t i)
  have hΓ : MarkedPredictable S.ℱ ν fun (ω : Ω) (s : ℝ) (e : E) =>
      (if 0 < s then coeffs.γ s (leftLimPathAt X.X s ω) e else 0 : Fin n → ℝ) := by
    unfold MarkedPredictable
    letI : MeasurableSpace (Ω × ℝ × E) := markedPredictableSigma S.ℱ ν
    refine measurable_pi_lambda _ fun i => ?_
    have h := markedPredictable_zeroExtPos_jumpCoeff_leftLimPathAt (ν := ν) X.X S.ℱ i hXadapt
      (fun ω t _ j => hXleft ω t j) (hγmeasi i)
    unfold MarkedPredictable at h
    convert h using 2 with p
    by_cases hs : (0 : ℝ) < p.2.1 <;> simp [zeroExtPos, hs]
  have hF : Measurable fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1 :=
    ((hu.continuous.comp (continuous_fst.prodMk
      (continuous_snd.fst.add continuous_snd.snd))).sub
      (hu.continuous.comp (continuous_fst.prodMk continuous_snd.fst))).measurable
  have h := MarkedPredictable.comp_measurable (ℱ := S.ℱ) (ν := ν) hF
    (Y := fun ω s => leftLimPathAtPos y s ω) hY hΓ
  convert h using 1
  funext ω s e
  by_cases hs : (0 : ℝ) < s <;> simp [zeroExtPos, hs, mixedJumpIncrement, leftLimPathAtPos]

omit [IsProbabilityMeasure P] in
/-- A marked integrand of finite mark energy on every bounded window has finite energy on the
window against the reference intensity of the mark measure. -/
theorem lintegral_referenceIntensity_window_ne_top {φ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (B : Set E) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ B,
      ‖φ ω q.1 q.2‖ₑ ^ 2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P ≠ ⊤ := by
  refine ne_top_of_le_ne_top (hφq T hT).ne (lintegral_mono fun ω => ?_)
  rw [LevyStochCalc.Poisson.lintegral_referenceIntensity_window
    (f := fun q : ℝ × E => ‖φ ω q.1 q.2‖ₑ ^ 2) ((hφm.comp
      (by fun_prop :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).enorm.pow_const 2) B T]
  refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans (lintegral_mono fun s => ?_)
  exact lintegral_mono' Measure.restrict_le_self fun e => le_rfl


end Mixed

end LevyStochCalc.Ito.JumpFormula
