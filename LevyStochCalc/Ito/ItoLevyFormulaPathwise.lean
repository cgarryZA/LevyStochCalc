/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyFormulaGeneral
import LevyStochCalc.Ito.JumpSplittingAllTimes
import LevyStochCalc.Brownian.CadlagVectorIntegral
import LevyStochCalc.Poisson.CompensatedNonpos
import LevyStochCalc.Ito.PicardOutputModification

/-!
# The Itô–Lévy formula at every time along one path

The Itô–Lévy formula `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general` holds, for each
horizon separately, off a null set depending on that horizon. Both sides of the identity are
right-continuous in the horizon along almost every path, so the union of the null sets over the
rational horizons is again null and the identity holds at every horizon `T ≥ 0` simultaneously
off a single null set.

The compensated-Poisson leg is càdlàg at every sample point by construction. The Brownian leg
`MultidimBrownianMotion.stochasticIntegral` is defined one time at a time, as an equivalence
class for each horizon, and so carries no path regularity; the first statement below therefore
takes a process `M` that is a version of it and is right-continuous along every path, and the
second supplies such a version from
`LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general_pathwise` — the four-term formula at
  every horizon off one null set, for a prescribed right-continuous version of the Brownian leg.
* `LevyStochCalc.Ito.JumpFormula.exists_itoLevyFormula_general_pathwise` — the same, for a
  version of the Brownian leg that is adapted to the right-continuous filtration, jointly
  measurable, càdlàg at every sample point and a martingale.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Probability LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Ito.CutoffPath LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian.Multidim

universe u v

section Pathwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (coeffs : JumpDiffusionCoeffs n d E)

/-- **The Itô–Lévy formula for a jump diffusion, at every horizon along one path.** For a jump
diffusion carrying SDE data at a filtration satisfying the usual conditions, with jointly
measurable coefficients and a drift of finite energy along the path, and a jointly `C²` state
function whose derived integrands `(∇u)ᵀσ` and `u(x + γ) − u(x)` along the path have finite
energy and whose compensator drift is integrable over every window, the four-term identity for
`u(T, X_T) − u(0, X_0)` holds at every horizon `T ≥ 0` simultaneously, off a single null set.

Beyond the hypotheses of `itoLevyFormula_general` — with the integrability of the compensator
drift assumed over every window rather than over one — the drift integrand and the integrated
compensator-drift integrand are assumed integrable over every window along almost every path,
and the Brownian leg is presented as a process `M` that is a version of
`MultidimBrownianMotion.stochasticIntegral` at each time and is right-continuous along every
path; the latter is supplied by `exists_itoLevyFormula_general_pathwise`. -/
theorem itoLevyFormula_general_pathwise (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ T' : ℝ, 0 < T' → ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤)
    (h_drift_loc : ∀ᵐ ω ∂P, ∀ b : ℝ,
      IntegrableOn (fun s => driftIntegrand u coeffs s (X.X s ω)) (Set.Icc (0 : ℝ) b) volume)
    (h_cd_loc : ∀ᵐ ω ∂P, ∀ b : ℝ,
      IntegrableOn (fun s => ∫ e, compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)
        (Set.Icc (0 : ℝ) b) volume)
    (M : ℝ → Ω → ℝ)
    (hMae : ∀ t : ℝ, M t =ᵐ[P]
      MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
        (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
        (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
        (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
        h_sigmaGrad_sq t)
    (hMright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T →
      u T (X.X T ω) - u 0 (X.X 0 ω)
        = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          + M T ω
          + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
              h_jumpInt_sq T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  set J : ℝ → Ω → ℝ := LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
      (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
      (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
      (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
      h_jumpInt_sq with hJ
  have hJcad := LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag N S.ℱ S.isPoisson
      (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
      (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
      (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
      h_jumpInt_sq
  refine ae_forall_eq_of_ae_rat (P := P)
    (Y := fun T ω => u T (X.X T ω) - u 0 (X.X 0 ω))
    (Z := fun T ω => (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
      + M T ω + J T ω
      + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν) ?_ ?_ ?_
  · -- the identity at the rational horizons
    intro q hq
    rcases eq_or_lt_of_le hq with heq | hpos
    · -- the horizon `0`, where both stochastic legs vanish
      have hzeroM : M (q : ℝ) =ᵐ[P] 0 := (hMae _).trans
        (MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos W S.ℱ S.isBrownian _ _ _ _
          (le_of_eq heq.symm))
      have hzeroJ : J (q : ℝ) =ᵐ[P] 0 :=
        (LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N S.ℱ S.isPoisson
            _ _ _ h_jumpInt_sq _).trans
          (LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos N S.ℱ S.isPoisson
            _ _ _ h_jumpInt_sq (le_of_eq heq.symm))
      filter_upwards [hzeroM, hzeroJ] with ω hM0 hJ0
      rw [← heq] at hM0 hJ0
      simp only [← heq, Set.Icc_self]
      simp [hM0, hJ0]
    · filter_upwards [itoLevyFormula_general W N coeffs x₀ X S hℱ0 hnull hμmeas hσmeas hγmeas
        hμq u hu (q : ℝ) hpos h_sigmaGrad_sq h_jumpInt_sq (h_compDrift_int (q : ℝ) hpos),
        hMae (q : ℝ)] with ω hω hMω
      rw [hMω]
      exact hω
  · -- right-continuity of the left side in the horizon
    filter_upwards [X.cadlag_paths] with ω hω t ht
    have hpair : Tendsto (fun s => ((s, X.X s ω) : ℝ × (Fin n → ℝ))) (𝓝[>] t)
        (𝓝 ((t, X.X t ω) : ℝ × (Fin n → ℝ))) :=
      ((continuous_id.tendsto t).mono_left nhdsWithin_le_nhds).prodMk_nhds (hω t ht).1
    exact ((hu.continuous.tendsto _).comp hpair).sub_const _
  · -- right-continuity of the right side in the horizon
    filter_upwards [h_drift_loc, h_cd_loc, hJcad] with ω hd hc hJω t ht
    have h1 : Tendsto (fun s => ∫ r in Set.Icc (0 : ℝ) s, driftIntegrand u coeffs r (X.X r ω))
        (𝓝[>] t) (𝓝 (∫ r in Set.Icc (0 : ℝ) t, driftIntegrand u coeffs r (X.X r ω))) :=
      ((LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn
        hd).tendsto t).mono_left nhdsWithin_le_nhds
    have h4 : Tendsto (fun s => ∫ r in Set.Icc (0 : ℝ) s,
          ∫ e, compensatorDriftIntegrand u coeffs.γ r (X.X r ω) e ∂ν)
        (𝓝[>] t) (𝓝 (∫ r in Set.Icc (0 : ℝ) t,
          ∫ e, compensatorDriftIntegrand u coeffs.γ r (X.X r ω) e ∂ν)) :=
      ((LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn
        hc).tendsto t).mono_left nhdsWithin_le_nhds
    exact ((h1.add (hMright ω t)).add (hJω t).1).add h4

/-- **The Itô–Lévy formula for a jump diffusion, at every horizon along one path, with a
canonical Brownian leg.** Under the hypotheses of `itoLevyFormula_general_pathwise` other than
those on the Brownian leg, the Brownian leg has a version that is adapted to the right-continuous
filtration, jointly measurable in the time and the sample point, càdlàg at every sample point and
a martingale, and for it the four-term identity holds at every horizon `T ≥ 0` simultaneously,
off a single null set. -/
theorem exists_itoLevyFormula_general_pathwise (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ T' : ℝ, 0 < T' → ∀ᵐ ω ∂P,
      ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤)
    (h_drift_loc : ∀ᵐ ω ∂P, ∀ b : ℝ,
      IntegrableOn (fun s => driftIntegrand u coeffs s (X.X s ω)) (Set.Icc (0 : ℝ) b) volume)
    (h_cd_loc : ∀ᵐ ω ∂P, ∀ b : ℝ,
      IntegrableOn (fun s => ∫ e, compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)
        (Set.Icc (0 : ℝ) b) volume) :
    ∃ M : ℝ → Ω → ℝ, Adapted S.ℱ.rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P]
        MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
          (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
          (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
          (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
          h_sigmaGrad_sq t) ∧
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))
        ∧ ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M S.ℱ.rightCont P ∧
      ∀ᵐ ω ∂P, ∀ T : ℝ, 0 ≤ T →
        u T (X.X T ω) - u 0 (X.X 0 ω)
          = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
            + M T ω
            + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
                (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
                (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
                (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
                h_jumpInt_sq T ω
            + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
                compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  have hrc : S.ℱ.rightCont = S.ℱ := Filtration.IsRightContinuous.eq
  have hℱ0' : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t := by
    intro t ht
    rw [hrc]
    exact hℱ0 t ht
  obtain ⟨M, hMadapt, hMmeas, hMae, hMcad, hMmart⟩ :=
    MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral W S.ℱ S.isBrownian
      (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
      (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
      (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
      h_sigmaGrad_sq hℱ0' hnull
  exact ⟨M, hMadapt, hMmeas, hMae, hMcad, hMmart,
    itoLevyFormula_general_pathwise W N coeffs x₀ X S hℱ0 hnull hμmeas hσmeas hγmeas hμq u hu
      h_sigmaGrad_sq h_jumpInt_sq h_compDrift_int h_drift_loc h_cd_loc M hMae
      fun ω t => (hMcad ω t).1⟩

end Pathwise

end LevyStochCalc.Ito.JumpFormula
