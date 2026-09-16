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
# Steps of the Itô–Lévy formula at bounded derivatives

The admissibility, transport and limit steps for the small-jump truncation of the Itô–Lévy
formula along a jump diffusion. The mixed integrands — derivatives of a `C²` state function
along an auxiliary path, coefficients along the solution — are admissible over the
right-continuous regularisation of the filtration of the SDE data; the Brownian integral over
that regularisation agrees almost surely with the one over the filtration itself; and, along a
family of paths converging to the solution at almost every time of the window, the four term
families of the formula converge to their counterparts along the solution.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated_ae` — dominated convergence
  for a mark integral over a shrinking family of cuts, with the domination and the convergence
  asked at almost every time of the window only.
* `LevyStochCalc.Ito.JumpFormula.tendsto_mixedDriftIntegral_of_tendsto` and
  `LevyStochCalc.Ito.JumpFormula.tendsto_mixedCompensatorDriftIntegral_of_tendsto` — the two
  pathwise integral terms converge along an approximating family of paths.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DominatedAe

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- **Dominated convergence for a mark integral over a shrinking family of cuts, at almost every
time.** The variant of `tendsto_setIntegral_of_dominated` in which the domination and the
pointwise convergence are asked at almost every time of the window only. -/
theorem tendsto_setIntegral_of_dominated_ae
    {T : ℝ} {A : ℕ → Set E} {fs : ℕ → ℝ → E → ℝ} {f g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable (fun p : ℝ × E => fs m p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e, |fs m s e| ≤ g s e)
    (hconv : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ e,
      Tendsto (fun m => fs m s e) atTop (𝓝 (f s e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν)) := by
  classical
  have hwin : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      (∀ m, ∀ e, |fs m p.1 e| ≤ g p.1 e) ∧
        ∀ e, Tendsto (fun m => fs m p.1 e) atTop (𝓝 (f p.1 e)) :=
    Measure.quasiMeasurePreserving_fst.ae ((MeasureTheory.ae_all_iff.mpr hdom).and hconv)
  have hevp : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ∀ᶠ m in atTop, p.2 ∉ A m :=
    Measure.quasiMeasurePreserving_snd.ae hev
  have hSm : ∀ m, MeasurableSet {p : ℝ × E | p.2 ∈ (A m)ᶜ} := fun m =>
    measurable_snd (hA m).compl
  set F : ℕ → ℝ × E → ℝ :=
    fun m => {p : ℝ × E | p.2 ∈ (A m)ᶜ}.indicator (fun q => fs m q.1 q.2) with hF
  have hFmeas : ∀ m, AEStronglyMeasurable (F m)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    fun m => (hmeas m).indicator (hSm m)
  have hbound : ∀ m, ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖F m p‖ ≤ g p.1 p.2 := by
    intro m
    filter_upwards [hwin] with p hp
    have hle : |fs m p.1 p.2| ≤ g p.1 p.2 := hp.1 m p.2
    by_cases hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ}
    · rw [hF]
      simp only [Set.indicator_of_mem hpS, Real.norm_eq_abs]
      exact hle
    · rw [hF]
      simp only [Set.indicator_of_notMem hpS, norm_zero]
      exact le_trans (abs_nonneg _) hle
  have hlim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      Tendsto (fun m => F m p) atTop (𝓝 (f p.1 p.2)) := by
    filter_upwards [hwin, hevp] with p hp hpe
    refine Tendsto.congr' ?_ (hp.2 p.2)
    filter_upwards [hpe] with m hm
    have hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ} := hm
    rw [hF]
    simp only [Set.indicator_of_mem hpS]
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) (F := F)
    (f := fun p : ℝ × E => f p.1 p.2) (fun p : ℝ × E => g p.1 p.2)
    hFmeas hg hbound hlim
  have hLHS : ∀ m, ∫ p, F m p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν := by
    intro m
    have hint : Integrable (F m) ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
      hg.mono' (hFmeas m) (hbound m)
    rw [integral_prod _ hint]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    change ∫ e, F m (s, e) ∂ν = ∫ e in (A m)ᶜ, fs m s e ∂ν
    have hfun : (fun e => F m (s, e)) = ((A m)ᶜ).indicator (fun e => fs m s e) := by
      funext e
      by_cases he : e ∈ (A m)ᶜ
      · rw [hF]
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem (show (s, e) ∈
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
      · rw [hF]
        simp only [Set.indicator_of_notMem he, Set.indicator_of_notMem (show (s, e) ∉
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
    rw [hfun, integral_indicator (hA m).compl]
  have hmlim : AEStronglyMeasurable (fun p : ℝ × E => f p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlim
  have hblim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖f p.1 p.2‖ ≤ g p.1 p.2 := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hbound, hlim] with p hb hl
    exact le_of_tendsto hl.norm (Eventually.of_forall hb)
  have hRHS : ∫ p, f p.1 p.2 ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν :=
    integral_prod _ (hg.mono' hmlim hblim)
  simp_rw [hLHS] at hDCT
  rwa [hRHS] at hDCT

end DominatedAe


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

open LevyStochCalc.Ito.IntegralLimit in
/-- Along a family of paths converging to the solution at almost every time of the window, the
Brownian integrals of the mixed diffusion integrands converge in `L²` to the Brownian integral
of the diffusion integrand along the solution. -/
theorem tendsto_lintegral_sq_mixedDiffusionIntegral_sub (S : SdeData X)
    (h𝒢W : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (hc0 : 0 ≤ c) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (hym : ∀ (k : ℕ) (j : Fin d), Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j))
    (hyp : ∀ (k : ℕ) (j : Fin d), Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
    (hyq : ∀ (k : ℕ) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hσm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (hσp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
    (hσq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T)
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => y k s ω) atTop (𝓝 (X.X s ω))) (j : Fin d) :
    Tendsto (fun k => ∫⁻ ω,
      (‖stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
          (hym k j) (hyp k j) (hyq k j) T ω
        - stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
          (hσm j) (hσp j) (hσq j) T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  refine tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated
    (W.W j) S.ℱ.rightCont (h𝒢W j)
    (fun k ω s => mixedDiffusionIntegrand u coeffs.σ s (y k s ω) (X.X s ω) j)
    (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
    (fun ω s => c * ∑ i, |coeffs.σ s (X.X s ω) i j|)
    (fun k => hym k j) (fun k => hyp k j) (fun k => hyq k j)
    (hσm j) (hσp j) (hσq j) ?_ hT ?_ ?_ ?_
  · change Measurable fun p : Ω × ℝ => c * ∑ i, |coeffs.σ p.2 (X.X p.2 p.1) i j|
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (S.σ_meas i j).abs)
  · filter_upwards [hpath] with ω hω
    filter_upwards [hω] with s hs
    change Tendsto (fun k => ∑ i, gradient u s (y k s ω) i * coeffs.σ s (X.X s ω) i j)
      atTop (𝓝 (∑ i, gradient u s (X.X s ω) i * coeffs.σ s (X.X s ω) i j))
    exact tendsto_sum_gradient_mul_of_tendsto hu s (fun i => coeffs.σ s (X.X s ω) i j) hs
  · intro k
    refine Eventually.of_forall fun ω => Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact abs_mixedDiffusionIntegrand_le hc s _ _ j
  · refine lintegral_window_sq_le_of_abs_le (a := fun i ω s => coeffs.σ s (X.X s ω) i j)
      (c := c) (fun i => S.σ_meas i j) (fun ω s => ?_) T (fun i => S.σ_sq i j T hT)
    rw [abs_of_nonneg (mul_nonneg hc0 (Finset.sum_nonneg fun i _ => abs_nonneg _))]

open LevyStochCalc.Ito.IntegralLimit in
/-- Along a family of paths converging to the solution at almost every time of the window, the
compensated integrals of the cut mixed jump increments converge in `L²` to the compensated
integral of the jump increment along the solution. -/
theorem tendsto_lintegral_sq_mixedCompensatedIntegral_sub (S : SdeData X)
    (h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i, |gradient u s x i| ≤ c) (hc0 : 0 ≤ c) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (ψ : ℕ → ℕ) (hψ : ∀ k, k ≤ ψ k)
    (hym : ∀ k, Measurable fun p : Ω × ℝ × E => markCut (smallMarks ν (ψ k))ᶜ
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e) p.1 p.2.1 p.2.2)
    (hyp : ∀ k, Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont (markCut
      (smallMarks ν (ψ k))ᶜ fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e))
    (hyq : ∀ (k : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut (smallMarks ν (ψ k))ᶜ
        (fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e) ω s e‖₊ :
          ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
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
    (T : ℝ) (hT : 0 < T)
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => y k s ω) atTop (𝓝 (X.X s ω))) :
    Tendsto (fun k => ∫⁻ ω,
      (‖stochasticIntegral N S.ℱ.rightCont h𝒢N (markCut (smallMarks ν (ψ k))ᶜ
            fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e)
          (hym k) (hyp k) (hyq k) T ω
        - stochasticIntegral N S.ℱ.rightCont h𝒢N
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          hjm hjp hjq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by
  refine tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated
    N S.ℱ.rightCont h𝒢N
    (fun k => markCut (smallMarks ν (ψ k))ᶜ
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e)
    (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
    (fun ω s e => (n : ℝ) * c * ∑ i, |coeffs.γ s (X.X s ω) e i|)
    hym hyp hyq hjm hjp hjq ?_ hT ?_ ?_ ?_
  · exact measurable_const.mul (Finset.measurable_sum _ fun i _ => (S.γ_meas i).abs)
  · filter_upwards [hpath] with ω hω
    filter_upwards [hω] with s hs
    filter_upwards [ae_eventually_notMem_comp (antitone_smallMarks ν)
      (measure_iInter_smallMarks ν) hψ] with e he
    have hlim : Tendsto
        (fun k => mixedJumpIncrement u coeffs.γ s (y k s ω) (X.X s ω) e) atTop
        (𝓝 (mixedJumpIncrement u coeffs.γ s (X.X s ω) (X.X s ω) e)) :=
      tendsto_mixedJumpIncrement_of_tendsto hu coeffs.γ s _ e hs
    refine hlim.congr' ?_
    filter_upwards [he] with k hk
    simp [markCut, hk]
  · intro k
    refine Eventually.of_forall fun ω => Eventually.of_forall fun s =>
      Eventually.of_forall fun e => ?_
    rw [Real.norm_eq_abs]
    exact (abs_markCut_le _ _ _ _ _).trans (abs_mixedJumpIncrement_le hu hc hc0 s _ _ e)
  · refine lintegral_window_mark_sq_le_of_abs_le
      (a := fun i ω s e => coeffs.γ s (X.X s ω) e i) (c := n * c)
      (fun i => S.γ_meas i) (fun ω s e => ?_) T (fun i => S.γ_sq i T hT)
    rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Nat.cast_nonneg n) hc0)
      (Finset.sum_nonneg fun i _ => abs_nonneg _))]

/-- Along a family of paths converging to the solution at almost every time of the window, the
mixed drift integrals converge almost surely to the drift integral along the solution. -/
theorem tendsto_mixedDriftIntegral_of_tendsto (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c₀ c₁ c₂ : ℝ}
    (hc₀ : ∀ s x, |timeDeriv u s x| ≤ c₀) (hc₁ : ∀ s x i, |gradient u s x i| ≤ c₁)
    (hc₂ : ∀ s x i j, |hessian u s x i j| ≤ c₂) (hc₂0 : 0 ≤ c₂)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) (y : ℕ → ℝ → Ω → Fin n → ℝ)
    (hym : ∀ i, Measurable (Function.uncurry (y i)))
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun i => y i s ω) atTop (𝓝 (X.X s ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun i => ∫ s in Set.Icc (0 : ℝ) T,
        mixedDriftIntegrand u coeffs s (y i s ω) (X.X s ω)) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))) := by
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
  filter_upwards [hpath, hμint, hσsq] with ω hω hμω hσω
  refine tendsto_integral_of_dominated_convergence
    (fun s => c₀ + c₁ * ∑ p, |coeffs.μ s (X.X s ω) p|
      + (1 / 2) * c₂ * ∑ p, ∑ q, ∑ j,
        (coeffs.σ s (X.X s ω) p j ^ 2 + coeffs.σ s (X.X s ω) q j ^ 2) / 2) ?_ ?_ ?_ ?_
  · intro i
    refine Measurable.aestronglyMeasurable ?_
    have hy : Measurable fun s => y i s ω := (hym i).of_uncurry_right
    change Measurable fun s => timeDeriv u s (y i s ω)
      + ((∑ p, coeffs.μ s (X.X s ω) p * gradient u s (y i s ω) p)
        + (1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s (X.X s ω) p j * coeffs.σ s (X.X s ω) q j
          * hessian u s (y i s ω) p q)
    refine Measurable.add ((continuous_timeDeriv hu).measurable.comp
      (measurable_id.prodMk hy)) (Measurable.add ?_ (measurable_const.mul ?_))
    · exact Finset.measurable_sum _ fun p _ => (Measurable.of_uncurry_left (hμm p)).mul
        ((continuous_gradient_uncurry hu p).measurable.comp (measurable_id.prodMk hy))
    · refine Finset.measurable_sum _ fun p _ => Finset.measurable_sum _ fun q _ =>
        Finset.measurable_sum _ fun j _ => ?_
      exact ((Measurable.of_uncurry_left (S.σ_meas p j)).mul
        (Measurable.of_uncurry_left (S.σ_meas q j))).mul
        ((continuous_hessian hu p q).measurable.comp (measurable_id.prodMk hy))
  · refine Integrable.add (Integrable.add (integrable_const _) ?_) ?_
    · exact (integrable_finsetSum _ fun p _ => (hμω p).abs).const_mul _
    · refine Integrable.const_mul ?_ _
      refine integrable_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ =>
        integrable_finsetSum _ fun j _ => ?_
      exact ((hσω p j).add (hσω q j)).div_const 2
  · intro i
    refine Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    exact abs_mixedDriftIntegrand_le coeffs hc₂0 hc₀ hc₁ hc₂ s _ _
  · filter_upwards [hω] with s hs
    exact tendsto_mixedDriftIntegrand_of_tendsto hu coeffs s _ hs

/-- Along a family of paths converging to the solution at almost every time of the window, the
mixed compensator-drift integrals over a shrinking family of cuts converge almost surely to the
compensator-drift integral along the solution. -/
theorem tendsto_mixedCompensatorDriftIntegral_of_tendsto (S : SdeData X)
    (hu : ContDiff ℝ 2 (Function.uncurry u)) {c : ℝ}
    (hc : ∀ s x i j, |hessian u s x i j| ≤ c) (hc0 : 0 ≤ c) (T : ℝ) (hT : 0 < T)
    (y : ℕ → ℝ → Ω → Fin n → ℝ) (hym : ∀ i, Measurable (Function.uncurry (y i)))
    (ψ : ℕ → ℕ) (hψ : ∀ i, i ≤ ψ i)
    (hpath : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun i => y i s ω) atTop (𝓝 (X.X s ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun i => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (smallMarks ν (ψ i))ᶜ,
        mixedCompensatorDriftIntegrand u coeffs.γ s (y i s ω) (X.X s ω) e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)) := by
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
  filter_upwards [hpath, hγint] with ω hω hγω
  have hγm : Measurable fun p : ℝ × E => coeffs.γ p.1 (X.X p.1 ω) p.2 :=
    measurable_pi_lambda _ fun i =>
      (S.γ_meas i).comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  refine tendsto_setIntegral_of_dominated_ae (ν := ν) (T := T)
    (A := fun i => smallMarks ν (ψ i))
    (fs := fun i s e => mixedCompensatorDriftIntegrand u coeffs.γ s (y i s ω) (X.X s ω) e)
    (f := fun s e => compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e)
    (g := fun s e => (n : ℝ) ^ 2 * c * ((n : ℝ) * ∑ i, coeffs.γ s (X.X s ω) e i ^ 2))
    (fun i => measurableSet_smallMarks ν (ψ i))
    (ae_eventually_notMem_comp (antitone_smallMarks ν) (measure_iInter_smallMarks ν) hψ)
    ?_ ?_ ?_ ?_
  · intro i
    refine Measurable.aestronglyMeasurable ?_
    have hy : Measurable fun p : ℝ × E => y i p.1 ω :=
      ((hym i).of_uncurry_right).comp measurable_fst
    change Measurable fun p : ℝ × E =>
      u p.1 (y i p.1 ω + coeffs.γ p.1 (X.X p.1 ω) p.2) - u p.1 (y i p.1 ω)
        - ∑ l, coeffs.γ p.1 (X.X p.1 ω) p.2 l * gradient u p.1 (y i p.1 ω) l
    refine Measurable.sub (Measurable.sub ?_ ?_) ?_
    · exact hu.continuous.measurable.comp (measurable_fst.prodMk (hy.add hγm))
    · exact hu.continuous.measurable.comp (measurable_fst.prodMk hy)
    · exact Finset.measurable_sum _ fun l _ => ((measurable_pi_apply l).comp hγm).mul
        ((continuous_gradient_uncurry hu l).measurable.comp (measurable_fst.prodMk hy))
  · exact ((integrable_finsetSum _ fun l _ => hγω l).const_mul _).const_mul _
  · intro i
    exact Eventually.of_forall fun s e =>
      abs_mixedCompensatorDriftIntegrand_le hu hc hc0 s _ _ e
  · filter_upwards [hω] with s hs e
    exact tendsto_mixedCompensatorDriftIntegrand_of_tendsto hu coeffs.γ s _ e hs

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
