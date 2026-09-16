/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionRepresentative
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolutionIntegrands

/-!
# The Itô–Lévy formula at bounded derivatives, from the solution data

For regular Lipschitz coefficients and a filtration satisfying the usual conditions, a `C²` state
function with bounded time derivative, gradient and Hessian satisfies the Itô–Lévy formula along
a jump diffusion that solves the equation on every window, that carries SDE data and has left
limits at every sample point and every time, or that carries SDE data alone: its increment is the
drift integral, the Brownian integral of `(∇u)ᵀσ`, the compensated integral of `u(x + γ) − u(x)`
and the compensator-drift integral. Every admissibility input of the two stochastic integrals is
derived from the solution data and the coefficient regularity; `multidimIntegral_congr_ae`
transports the Brownian integral between vector integrands agreeing almost everywhere on a
window.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section Main

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E)

/-- **The Itô–Lévy formula at bounded derivatives, from the solution data.** For regular
Lipschitz coefficients and a right-continuous filtration containing the null sets at time zero,
there is a jump diffusion solving the equation on every window relative to that filtration, with
progressively measurable coordinates and càdlàg paths at every sample point and every time,
along which a `C²` state function with bounded time derivative, gradient and Hessian satisfies
the Itô–Lévy formula: its increment is the drift integral, the Brownian integral of `(∇u)ᵀσ`,
the compensated integral of `u(x + γ) − u(x)` and the compensator-drift integral. Every
admissibility input of the two stochastic integrals is derived from the solution data. -/
theorem itoLevyFormula_jumpResidual_of_solvesOn [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : coeffs.IsRegular ν) {L : ℝ} (hLip : coeffs.IsLipschitz ν L) (x₀ : Fin n → ℝ)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∃ (X : JumpDiffusion W N coeffs x₀)
      (hsol : ∀ T' : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X.X T')
      (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X.X s ω i),
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X.X s ω) (𝓝[>] t) (𝓝 (X.X t ω))
          ∧ ∀ j : Fin n, ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
      ∧ ∀ᵐ ω ∂P,
        (u T (X.X T ω) - u 0 (X.X 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          - MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
              (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              (fun j => measurable_diffusionIntegrand_path hu hReg.2.1 X.measurable_path j)
              (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hReg.2.1 hXa j)
              (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
                (hsol 0).h_σ_meas (hsol 0).h_σ_sq j hT') T ω)
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path hu hReg.2.2.1 X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path hu hReg.2.2.1 hXa)
              (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ (hsol 0).h_γ_meas
                (hsol 0).h_γ_sq hT') T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  -- the solution of the well-posedness theorem
  obtain ⟨X₀, hXm, hXa₀, hX0, hXcad, hXS, hXsol⟩ :=
    exists_globalSolution W N ℱ hℱW hℱN coeffs hℱ0 hnull hReg hLip x₀
  -- the good set, on which its paths are càdlàg
  obtain ⟨G, hGm, hG0, hGp⟩ := exists_measurable_full_of_ae (P := P) hXcad
  have hG : MeasurableSet[ℱ 0] G := by
    simpa using (hnull Gᶜ hGm.compl hG0).compl
  have hXad : ∀ t : ℝ, Measurable[ℱ t] (X₀ t) := measurable_of_progressivelyMeasurable ℱ hXa₀
  -- the representative and its data
  set Y : ℝ → Ω → Fin n → ℝ := cadlagRep G X₀ with hYdef
  have hYm : Measurable (Function.uncurry Y) := measurable_uncurry_cadlagRep hGm hXm
  have hYa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => Y s ω i :=
    fun i => progressivelyMeasurable_cadlagRep hGp hG hXad i
  have hY0 : ∀ᵐ ω ∂P, Y 0 ω = x₀ := ae_cadlagRep_zero hG0 hX0
  have hYcad : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Y s ω i) (𝓝[<] t) (𝓝 L) :=
    fun ω t => cadlagRep_cadlag hGp ω t
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => by
      rw [hYdef, lintegral_iSup_cadlagRep hG0]
      exact hXS T' hT'
  have hYsol : ∀ T' : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T' := fun T' =>
    solvesOn_cadlagRep W N ℱ hℱW hℱN coeffs hGm hG0 hnull hReg.2.1 hReg.2.2.1 (hXsol 0).h_σ_sq
      (hXsol 0).h_γ_sq hXm hXa₀ hX0 hGp hXsol T'
  let X : JumpDiffusion W N coeffs x₀ :=
    jumpDiffusionOfSolvesOn W N ℱ hℱW hℱN coeffs x₀ hYm hY0
      (Eventually.of_forall fun ω t _ => hYcad ω t) hYS hYsol
  refine ⟨X, hYsol, hYa, hYcad, ?_⟩
  -- the SDE data of the representative at the given filtration
  let S : SdeData X := SdeData.ofSolvesOn X ℱ hℱW hℱN hYa hYsol
  haveI : S.ℱ.IsRightContinuous := ‹ℱ.IsRightContinuous›
  have hrc : ℱ.rightCont = ℱ := Filtration.IsRightContinuous.eq
  have hℱ0' : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t := by
    intro t ht
    change ℱ.rightCont 0 ≤ ℱ.rightCont t
    rw [hrc]
    exact hℱ0 t ht
  have hYsq := fun b => lintegral_lintegral_sq_lt_top_of_supL2 hYS b
  have hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i) :=
    fun i => measurable_mu_comp_state coeffs hReg hYm i
  have hμp : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (Y s ω) i :=
    fun i => progressivelyMeasurable_comp_state hYa (f := fun s x => coeffs.μ s x i)
      ((measurable_pi_apply i).comp hReg.1)
  have hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i T' hT' => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip hYsq i hT'
  exact itoLevyFormula_jumpResidual_of_boundedDerivs W N coeffs x₀ X S hℱ0' hnull
    (fun t => measurable_of_progressivelyMeasurable ℱ hYa t) (fun ω t j => (hYcad ω t).2 j)
    hμm hμp hμq hReg.2.2.1 u hu hK₀ hK₁ hK₂ T hT (ae_integrableOn_drift_path hμm hμq T)
    (fun j => measurable_diffusionIntegrand_path hu hReg.2.1 X.measurable_path j)
    (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hReg.2.1 hYa j)
    (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
      (hYsol 0).h_σ_meas (hYsol 0).h_σ_sq j hT')
    (measurable_jumpIncrement_path hu hReg.2.2.1 X.measurable_path)
    (markedProgressivelyMeasurable_jumpIncrement_path hu hReg.2.2.1 hYa)
    (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ (hYsol 0).h_γ_meas
      (hYsol 0).h_γ_sq hT')
    (ae_lintegral_compensatorDriftIntegrand_lt_top hu hK₂ hReg.2.2.1 X.measurable_path
      (hYsol 0).h_γ_meas (hYsol 0).h_γ_sq hT)


/-- Itô integrals of vector integrands agreeing almost everywhere on `[0, T]` agree almost
surely. -/
theorem multidimIntegral_congr_ae (Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ))
    (hm₁ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₁ s ω i))
    (hp₁ : ∀ i : Fin d, ProgressivelyMeasurable ℱ fun ω s => Z₁ s ω i)
    (hq₁ : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₁ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z₂ s ω i))
    (hp₂ : ∀ i : Fin d, ProgressivelyMeasurable ℱ fun ω s => Z₂ s ω i)
    (hq₂ : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z₂ s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (h : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Z₁ s ω = Z₂ s ω) :
    ∀ᵐ ω ∂P, MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z₁ hm₁ hp₁ hq₁ T ω
      = MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z₂ hm₂ hp₂ hq₂ T ω := by
  have hcomp : ∀ i : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱW i)
          (fun ω' s => Z₁ s ω' i) (hm₁ i) (hp₁ i) (hq₁ i) T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱW i)
          (fun ω' s => Z₂ s ω' i) (hm₂ i) (hp₂ i) (hq₂ i) T ω := by
    intro i
    refine itoIntegral_congr_ae (W.W i) ℱ (hℱW i) _ _ _ _ _ _ _ _ hT ?_
    filter_upwards [h] with ω hω
    filter_upwards [hω] with s hs
    rw [hs]
  filter_upwards [MeasureTheory.ae_all_iff.mpr hcomp] with ω hω
  simp only [MultidimBrownianMotion.stochasticIntegral]
  exact Finset.sum_congr rfl fun i _ => hω i

/-- **The Itô–Lévy formula at bounded derivatives, for a solution with left limits everywhere.**
For a jump diffusion carrying SDE data at a filtration satisfying the usual conditions, with
jointly measurable coefficients, a drift of finite energy along the path and left limits along
every path, a `C²` state function with
bounded time derivative, gradient and Hessian satisfies the Itô–Lévy formula relative to that
filtration.

Every admissibility input of the two stochastic integrals, the adaptedness of the path, the
drift's measurability, progressive measurability and energy, and the integrability of the drift
and of the compensator drift are derived from the SDE data and the measurability of the
coefficients, not assumed. -/
theorem itoLevyFormula_jumpResidual_of_sdeData_of_leftLim (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
              S.σ_meas S.σ_sq j hT') T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT') T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  have hrc : S.ℱ.rightCont = S.ℱ := Filtration.IsRightContinuous.eq
  have hℱ0' : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t := by
    intro t ht
    rw [hrc]
    exact hℱ0 t ht
  have hXm : Measurable (Function.uncurry X.X) := X.measurable_path
  have hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i) :=
    fun i => ((measurable_pi_apply i).comp hμmeas).comp
      (measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst)))
  have hμp : ∀ i : Fin n,
      ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i :=
    fun i => progressivelyMeasurable_comp_state S.X_prog (f := fun s x => coeffs.μ s x i)
      ((measurable_pi_apply i).comp hμmeas)
  exact itoLevyFormula_jumpResidual_of_boundedDerivs W N coeffs x₀ X S hℱ0' hnull
    (fun t => measurable_of_progressivelyMeasurable S.ℱ S.X_prog t) hXleft
    hμm hμp hμq hγmeas u hu hK₀ hK₁ hK₂ T hT (ae_integrableOn_drift_path hμm hμq T)
    (fun j => measurable_diffusionIntegrand_path hu hσmeas hXm j)
    (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
    (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁ S.σ_meas S.σ_sq j hT')
    (measurable_jumpIncrement_path hu hγmeas hXm)
    (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
    (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT')
    (ae_lintegral_compensatorDriftIntegrand_lt_top hu hK₂ hγmeas hXm S.γ_meas S.γ_sq hT)

/-- **The Itô–Lévy formula at bounded derivatives, for a given solution.** For a jump diffusion
carrying SDE data at a filtration satisfying the usual conditions, with jointly measurable
coefficients and a drift of finite energy along the path, a `C²` state function with bounded time
derivative, gradient and Hessian satisfies the Itô–Lévy formula relative to that filtration.

Every admissibility input of the two stochastic integrals, the adaptedness of the path, the
drift's measurability, progressive measurability and energy, the integrability of the drift and
of the compensator drift, and the left limits of the path are derived from the SDE data and the
coefficient regularity, not assumed: the almost-sure càdlàg paths of the jump diffusion give a
representative with left limits at every sample point and every time, which solves the same
equation, and each of the four terms reads the path only up to a null set. -/
theorem itoLevyFormula_jumpResidual_of_sdeData (x₀ : Fin n → ℝ)
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
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
              S.σ_meas S.σ_sq j hT') T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT') T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  -- the good set, on which the paths of the jump diffusion are càdlàg
  obtain ⟨G, hGm, hG0, hGp⟩ := exists_measurable_full_of_ae (P := P) X.cadlag_paths
  have hG : MeasurableSet[S.ℱ 0] G := by
    simpa using (hnull Gᶜ hGm.compl hG0).compl
  have hXm : Measurable (Function.uncurry X.X) := X.measurable_path
  have hXad : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t) :=
    measurable_of_progressivelyMeasurable S.ℱ S.X_prog
  have hXsol : ∀ T' : ℝ,
      SolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ X.X T' := fun T' =>
    solvesOn_of_eqn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ S.σ_meas S.σ_prog S.σ_sq
      S.γ_meas S.γ_prog S.γ_sq S.sde T'
  -- the representative with left limits at every sample point and every time
  set Y : ℝ → Ω → Fin n → ℝ := cadlagRep G X.X with hYdef
  have hYm : Measurable (Function.uncurry Y) := measurable_uncurry_cadlagRep hGm hXm
  have hYa : ∀ i : Fin n, ProgressivelyMeasurable S.ℱ fun ω s => Y s ω i :=
    fun i => progressivelyMeasurable_cadlagRep hGp hG hXad i
  have hY0 : ∀ᵐ ω ∂P, Y 0 ω = x₀ := ae_cadlagRep_zero hG0 X.initial_value
  have hYcad : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))
      ∧ ∀ i : Fin n, ∃ ℓ : ℝ, Tendsto (fun s => Y s ω i) (𝓝[<] t) (𝓝 ℓ) :=
    fun ω t => cadlagRep_cadlag hGp ω t
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => by
      rw [hYdef, lintegral_iSup_cadlagRep hG0]
      exact X.sup_L2 T' hT'
  have hYsol : ∀ T' : ℝ, SolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ Y T' := fun T' =>
    solvesOn_cadlagRep W N S.ℱ S.isBrownian S.isPoisson coeffs hGm hG0 hnull hσmeas hγmeas
      S.σ_sq S.γ_sq hXm S.X_prog X.initial_value hGp hXsol T'
  have hpe : ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → Y s ω = X.X s ω :=
    ae_forall_cadlagRep_eq (P := P) hG0
  have hYX : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Y s ω = X.X s ω := by
    filter_upwards [hpe] with ω hω
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hω s hs.1
  -- the formula along the representative
  let XY : JumpDiffusion W N coeffs x₀ :=
    jumpDiffusionOfSolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ hYm hY0
      (Eventually.of_forall fun ω t _ => hYcad ω t) hYS hYsol
  let SY : LevyStochCalc.Ito.BigJump.SdeData XY :=
    LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn XY S.ℱ S.isBrownian S.isPoisson hYa hYsol
  haveI : SY.ℱ.IsRightContinuous := ‹S.ℱ.IsRightContinuous›
  have hmain := itoLevyFormula_jumpResidual_of_sdeData_of_leftLim W N coeffs x₀ XY SY
    hℱ0 hnull (fun ω t j => (hYcad ω t).2 j) hμmeas hσmeas hγmeas
    (fun i T' hT' => (lintegral_sq_comp_cadlagRep hG0 (fun s x => coeffs.μ s x i) T').trans_lt
      (hμq i T' hT')) u hu hK₀ hK₁ hK₂ T hT
  -- the four terms read the path only up to a null set
  have hBro := multidimIntegral_congr_ae W S.ℱ S.isBrownian
    (fun s ω => diffusionIntegrand u coeffs.σ s (Y s ω))
    (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
    (fun j => measurable_diffusionIntegrand_path hu hσmeas hYm j)
    (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas hYa j)
    (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
      (hYsol 0).h_σ_meas (hYsol 0).h_σ_sq j hT')
    (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
    (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
    (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁ S.σ_meas S.σ_sq j hT')
    hT (by
      filter_upwards [hYX] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (diffusionIntegrand u coeffs.σ s) hs)
  have hCmp := compensatedIntegral_congr_ae N S.ℱ S.isPoisson
    (fun ω' s e => u s (Y s ω' + coeffs.γ s (Y s ω') e) - u s (Y s ω'))
    (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
    (measurable_jumpIncrement_path hu hγmeas hYm)
    (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas hYa)
    (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ (hYsol 0).h_γ_meas
      (hYsol 0).h_γ_sq hT')
    (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
    (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
    (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT')
    hT (by
      filter_upwards [hYX] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (fun x => fun e => u s (x + coeffs.γ s x e) - u s x) hs)
  filter_upwards [hmain, hBro, hCmp, hpe] with ω hω hbro hcmp hag
  have hdr : (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (Y s ω))
      = ∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω) :=
    setIntegral_congr_fun measurableSet_Icc fun s hs =>
      congrArg (driftIntegrand u coeffs s) (hag s hs.1)
  have hcd : (∫ s in Set.Icc (0 : ℝ) T, ∫ e, compensatorDriftIntegrand u coeffs.γ s (Y s ω) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν :=
    setIntegral_congr_fun measurableSet_Icc fun s hs =>
      congrArg (fun x => ∫ e, compensatorDriftIntegrand u coeffs.γ s x e ∂ν) (hag s hs.1)
  rw [← hdr, ← hbro, ← hcmp, ← hcd, ← hag T hT.le, ← hag 0 le_rfl]
  exact hω

/-- The Itô–Lévy formula for a jump diffusion and a jointly `C²` state function with bounded
first and second derivatives, relative to the filtration of the solution's SDE data:
`u(T, X_T) − u(0, X_0)` is the drift integral of `∂ₜu + 𝓛u`, plus the Brownian integral of
`(∇u)ᵀσ`, plus the compensated-Poisson integral of `u(x + γ) − u(x)`, plus the compensator-drift
integral of `u(x + γ) − u(x) − γᵀ∇u`, all along the path. -/
theorem itoLevyFormula_of_boundedDerivs (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hReg : coeffs.IsRegular ν) {L : ℝ} (hLip : coeffs.IsLipschitz ν L)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∀ᵐ ω ∂P,
      u T (X.X T ω) - u 0 (X.X 0 ω)
        = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          + MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
              (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              (fun j => measurable_diffusionIntegrand_path hu hReg.2.1 X.measurable_path j)
              (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hReg.2.1 S.X_prog j)
              (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
                S.σ_meas S.σ_sq j hT') T ω
          + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path hu hReg.2.2.1 X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path hu hReg.2.2.1 S.X_prog)
              (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ S.γ_meas S.γ_sq hT')
              T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  filter_upwards [itoLevyFormula_jumpResidual_of_sdeData W N coeffs x₀ X S hℱ0 hnull hReg.1
    hReg.2.1 hReg.2.2.1 (fun i T' hT' => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip
      (fun b => lintegral_lintegral_sq_lt_top_of_supL2 X.sup_L2 b) i hT')
    u hu hK₀ hK₁ hK₂ T hT] with ω hω
  linarith

end Main

end LevyStochCalc.Ito.JumpFormula
