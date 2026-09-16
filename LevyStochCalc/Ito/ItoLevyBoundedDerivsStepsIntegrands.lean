/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.BigJumpPathBridge
import LevyStochCalc.Ito.LeftLimIntegrandRegularity
import LevyStochCalc.Ito.TruncatedContinuousPart
import LevyStochCalc.Ito.JumpFormulaMixed
import LevyStochCalc.Ito.JumpFormulaTaylorBounds
import LevyStochCalc.Ito.JumpFormulaContinuity
import LevyStochCalc.Ito.SubsequenceBookkeeping
import LevyStochCalc.Ito.VectorItoProcessDiff
import LevyStochCalc.Ito.ItoLevyMixedBounds
import LevyStochCalc.Probability.MarkedProgressiveSlice

/-!
# Admissibility of the mixed integrands of the Itô–Lévy formula

The mixed integrands of the Itô–Lévy formula along a jump diffusion — the derivatives of a `C²`
state function read at an auxiliary path, the coefficients read at the solution — are jointly
measurable, are progressively measurable for the right-continuous regularisation of the
filtration of the SDE data, and have finite energy on every bounded window; over that
regularisation the Brownian and the compensated jump integral agree almost surely with the ones
over the filtration itself, and the endpoint of a path together with its two stochastic
integrals is measurable componentwise.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Mixed

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}
  {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The mixed diffusion integrand, read at an auxiliary path and at the solution, is jointly
measurable in the sample point and the time. -/
theorem measurable_uncurry_mixedDiffusionIntegrand (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hy : Measurable (Function.uncurry y)) (j : Fin d) :
    Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j) := by
  change Measurable fun p : Ω × ℝ =>
    ∑ i, gradient u p.2 (y p.2 p.1) i * coeffs.σ p.2 (X.X p.2 p.1) i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ (S.σ_meas i j)
  exact (continuous_gradient_uncurry hu i).measurable.comp
    (measurable_snd.prodMk (hy.comp (measurable_snd.prodMk measurable_fst)))

/-- The mixed diffusion integrand, read at a right-continuous adapted auxiliary path and at the
solution, is progressively measurable for the right-continuous filtration of the SDE data. -/
theorem progressivelyMeasurable_mixedDiffusionIntegrand (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hyad : ∀ t : ℝ, Measurable[S.ℱ.rightCont t] (y t))
    (hyrc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω))) (j : Fin d) :
    Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j := by
  change Probability.ProgressivelyMeasurable S.ℱ.rightCont
    fun ω s => ∑ i, gradient u s (y s ω) i * coeffs.σ s (X.X s ω) i j
  refine progressivelyMeasurable_finset_sum _ fun i _ =>
    Probability.ProgressivelyMeasurable.mul ?_
      ((S.σ_prog i j).mono fun t => S.ℱ.le_rightCont t)
  exact progressivelyMeasurable_of_rightContinuous (X := fun s ω => gradient u s (y s ω) i)
    (fun t => (continuous_gradient hu t i).measurable.comp (hyad t))
    (fun ω t => ((continuous_gradient_uncurry hu i).tendsto (t, y t ω)).comp
      ((tendsto_id'.mpr nhdsWithin_le_nhds).prodMk_nhds (hyrc ω t)))

/-- The mixed diffusion integrand has finite energy on every bounded window, under a bound on
the gradient of the state function. -/
theorem lintegral_window_sq_mixedDiffusionIntegrand_lt_top (S : SdeData X) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (y : ℝ → Ω → Fin n → ℝ) (j : Fin d)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ :=
  lintegral_window_sq_le_of_abs_le (a := fun i ω s => coeffs.σ s (X.X s ω) i j) (c := c)
    (fun i => S.σ_meas i j) (fun _ω s => abs_mixedDiffusionIntegrand_le hc s _ _ j) T
    (fun i => S.σ_sq i j T hT)

/-- The mixed jump increment, read at an auxiliary path and at the solution, is jointly
measurable in the sample point, the time and the mark. -/
theorem measurable_mixedJumpIncrement (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hy : Measurable (Function.uncurry y)) :
    Measurable fun p : Ω × ℝ × E =>
      mixedJumpIncrement u coeffs.γ p.2.1 (y p.2.1 p.1) (X.X p.2.1 p.1) p.2.2 := by
  have hyp : Measurable fun p : Ω × ℝ × E => y p.2.1 p.1 :=
    hy.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγ : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 :=
    measurable_pi_lambda _ fun i => S.γ_meas i
  change Measurable fun p : Ω × ℝ × E =>
    u p.2.1 (y p.2.1 p.1 + coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2) - u p.2.1 (y p.2.1 p.1)
  exact (hu.continuous.measurable.comp (measurable_snd.fst.prodMk (hyp.add hγ))).sub
    (hu.continuous.measurable.comp (measurable_snd.fst.prodMk hyp))

/-- The mixed jump increment, read at a progressively measurable auxiliary path and at the
solution, is marked progressively measurable for the right-continuous filtration of the SDE
data. -/
theorem markedProgressivelyMeasurable_mixedJumpIncrement (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (y : ℝ → Ω → Fin n → ℝ)
    (hyp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ.rightCont fun ω s => y s ω i) :
    Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e := by
  have hZ := markedProgressivelyMeasurable_time_state_jump (ℱ := S.ℱ.rightCont)
    (coeffs := coeffs) (Xp := X.X) (Y := y) hyp
    (fun i => (S.γ_prog i).mono fun t => S.ℱ.le_rightCont t)
  have hg : Continuous fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1 :=
    (hu.continuous.comp (continuous_fst.prodMk (continuous_snd.fst.add continuous_snd.snd))).sub
      (hu.continuous.comp (continuous_fst.prodMk continuous_snd.fst))
  have hg0 : (fun q : ℝ × (Fin n → ℝ) × (Fin n → ℝ) =>
      u q.1 (q.2.1 + q.2.2) - u q.1 q.2.1) 0 = 0 := by simp
  exact hg.comp_markedProgressivelyMeasurable hg0 hZ

/-- The mixed jump increment has finite energy on every bounded window, under a bound on the
gradient of the state function. -/
theorem lintegral_window_mark_sq_mixedJumpIncrement_lt_top (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (hc0 : 0 ≤ c) (y : ℝ → Ω → Fin n → ℝ)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ :=
  lintegral_window_mark_sq_le_of_abs_le (a := fun i ω s e => coeffs.γ s (X.X s ω) e i)
    (c := n * c) (fun i => S.γ_meas i)
    (fun _ω s e => abs_mixedJumpIncrement_le hu hc hc0 s _ _ e) T (fun i => S.γ_sq i T hT)

/-- The multidimensional Brownian integral over the right-continuous regularisation of the
filtration of the SDE data agrees almost surely with the one over that filtration. -/
theorem multidimStochasticIntegral_rightCont_ae_eq (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (Z : ℝ → Ω → Fin d → ℝ)
    (hZm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hZp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ fun ω s => Z s ω j)
    (hZp' : ∀ j : Fin d,
      Probability.ProgressivelyMeasurable S.ℱ.rightCont fun ω s => Z s ω j)
    (hZq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (T : ℝ) :
    MultidimBrownianMotion.stochasticIntegral W S.ℱ.rightCont h𝒢W Z hZm hZp' hZq T
      =ᵐ[P] MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian Z hZm hZp hZq T := by
  have hchan : ∀ j : Fin d,
      stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => Z s ω j) (hZm j) (hZp j) (hZq j) T
        =ᵐ[P] stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => Z s ω j) (hZm j) (hZp' j) (hZq j) T :=
    fun j => stochasticIntegralBrownian_congr_filtration (W.W j) S.ℱ S.ℱ.rightCont
      (S.isBrownian j) (h𝒢W j) (fun t => S.ℱ.le_rightCont t) _ (hZm j) (hZp j)
      (hZp' j) (hZq j) T
  filter_upwards [MeasureTheory.ae_all_iff.mpr hchan] with ω hω
  rw [multidimStochasticIntegral_eq_sum, multidimStochasticIntegral_eq_sum]
  exact Finset.sum_congr rfl fun j _ => (hω j).symm

/-- The compensated jump integral over the right-continuous regularisation of the filtration of
the SDE data agrees almost surely with the one over that filtration. -/
theorem compensatedStochasticIntegral_rightCont_ae_eq (S : SdeData X)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont) (Φ : Ω → ℝ → E → ℝ)
    (hΦm : Measurable fun p : Ω × ℝ × E => Φ p.1 p.2.1 p.2.2)
    (hΦp : Probability.MarkedProgressivelyMeasurable S.ℱ Φ)
    (hΦp' : Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont Φ)
    (hΦq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖Φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (T : ℝ) :
    stochasticIntegral N S.ℱ.rightCont h𝒢N Φ hΦm hΦp' hΦq T
      =ᵐ[P] stochasticIntegral N S.ℱ S.isPoisson Φ hΦm hΦp hΦq T :=
  (stochasticIntegral_congr_filtration N S.ℱ S.ℱ.rightCont S.isPoisson h𝒢N
    (fun t => S.ℱ.le_rightCont t) _ hΦm hΦp hΦp' hΦq T).symm

/-- The endpoint of an auxiliary path, the Brownian integrals of the mixed diffusion integrands
along it and the compensated integral of its cut mixed jump increment are measurable
componentwise. -/
theorem measurable_sumElim_mixedTerms (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont)
    (y : ℝ → Ω → Fin n → ℝ) (hy : Measurable (Function.uncurry y)) (A : Set E)
    (hBm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j))
    (hBp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
    (hBq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hCm : Measurable fun p : Ω × ℝ × E => markCut A
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) p.1 p.2.1 p.2.2)
    (hCp : Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont (markCut A
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e))
    (hCq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut A (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) ω s e‖₊ :
        ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (c : Fin n ⊕ Fin d ⊕ Unit) :
    Measurable (Sum.elim (fun i ω => y T ω i) (Sum.elim
      (fun j ω => stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
        (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
        (hBm j) (hBp j) (hBq j) T ω)
      (fun _ ω => stochasticIntegral N S.ℱ.rightCont h𝒢N (markCut A
          fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
        hCm hCp hCq T ω)) c) := by
  rcases c with i | j | _
  · exact (measurable_pi_apply i).comp (hy.comp (measurable_const.prodMk measurable_id))
  · exact ((stochasticIntegralBrownian_stronglyAdapted (W.W j) S.ℱ.rightCont (h𝒢W j)
      (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
      (hBm j) (hBp j) (hBq j) T).mono
        (S.ℱ.rightCont.le T)).measurable
  · exact (stochasticIntegral_adapted N S.ℱ.rightCont h𝒢N _ hCm hCp hCq T).mono
      (S.ℱ.rightCont.rightCont.le T) le_rfl

/-- The endpoint of the solution, the Brownian integrals of the diffusion integrands along it
and the compensated integral of its jump increment are measurable componentwise. -/
theorem measurable_sumElim_solutionTerms (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont)
    (hσm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
    (hσq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hjm : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (hjp : Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont
        (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω')))
    (hjq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (c : Fin n ⊕ Fin d ⊕ Unit) :
    Measurable (Sum.elim (fun i ω => X.X T ω i) (Sum.elim
      (fun j ω => stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
        (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
        (hσm j) (hσp j) (hσq j) T ω)
      (fun _ ω => stochasticIntegral N S.ℱ.rightCont h𝒢N
        (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
        hjm hjp hjq T ω)) c) := by
  rcases c with i | j | _
  · exact (measurable_pi_apply i).comp (X.measurable_path.comp
      (measurable_const.prodMk measurable_id))
  · exact ((stochasticIntegralBrownian_stronglyAdapted (W.W j) S.ℱ.rightCont (h𝒢W j)
      (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
      (hσm j) (hσp j) (hσq j) T).mono
        (S.ℱ.rightCont.le T)).measurable
  · exact (stochasticIntegral_adapted N S.ℱ.rightCont h𝒢N _ hjm hjp hjq T).mono
      (S.ℱ.rightCont.rightCont.le T) le_rfl

end Mixed

end LevyStochCalc.Ito.JumpFormula
