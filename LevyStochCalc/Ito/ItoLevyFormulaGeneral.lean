/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSolution
import LevyStochCalc.Ito.CutoffJumpTransfer
import LevyStochCalc.Ito.CutoffGlobalBounds
import LevyStochCalc.Ito.JumpSplittingRemainder

/-!
# The Itô–Lévy formula for a jump diffusion

The Itô–Lévy formula for a jointly `C²` state function of a jump diffusion, relative to the
filtration of the solution's SDE data, with no bound on the derivatives of the state function:
the only hypotheses beyond the SDE data are the joint measurability of the coefficients, the
window energy of the drift along the path, and the admissibility of the two derived integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` together with the integrability of the compensator drift.

The proof cuts the state function off outside a ball, applies the bounded-derivative formula to
the cut-off, and transfers every term back on the event that the path stays in the ball over the
window: the continuous side term by term, the jump side as a sum, through the arrival-time jump
relation of the solution. Almost every path stays in some ball.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim` —
  the residual form along a solution with càdlàg paths at every sample point.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_sdeData_general` — the residual
  form along any jump diffusion, through its càdlàg representative.
* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general` — the four-term form.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Probability LevyStochCalc.Ito.Setting LevyStochCalc.Ito.JumpSplitting
open LevyStochCalc.Ito.CutoffPath LevyStochCalc.Poisson.Compensated

universe u v

section Transfers

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {n : ℕ}

/-- A marked integrand read along the left limits of an almost surely càdlàg path has the same
window energy as read along the path. -/
theorem lintegral_sq_marked_leftLimPathAt_eq {X : ℝ → Ω → Fin n → ℝ}
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (F : ℝ → (Fin n → ℝ) → E → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖F s (leftLimPathAt X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖F s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPathAt X hcad] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  rw [hs]

/-- An integrand of the time and the state read along the left limits of an almost surely càdlàg
path has the same window energy as read along the path. -/
theorem lintegral_sq_leftLimPathAt_eq {X : ℝ → Ω → Fin n → ℝ}
    (hcad : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (f : ℝ → (Fin n → ℝ) → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (leftLimPathAt X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPathAt X hcad] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  rw [hs]

variable [SigmaFinite ν]

/-- A measurable marked function of the time whose iterated `L¹` bound on a closed window is
finite is integrable over the left-open window and all marks for the reference intensity. -/
theorem integrableOn_window_univ_of_lintegral_lt_top {g : ℝ × E → ℝ} (hg : Measurable g) {T : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    IntegrableOn g (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
      (LevyStochCalc.Poisson.referenceIntensity ν) := by
  refine ⟨hg.aestronglyMeasurable, ?_⟩
  rw [HasFiniteIntegral]
  have hm : Measurable fun q : ℝ × E => (‖g q‖₊ : ℝ≥0∞) :=
    hg.nnnorm.coe_nnreal_ennreal
  calc ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), ‖g q‖ₑ
          ∂(LevyStochCalc.Poisson.referenceIntensity ν)
        = ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), (‖g q‖₊ : ℝ≥0∞)
          ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
          simp only [enorm_eq_nnnorm]
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e in Set.univ, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume :=
          LevyStochCalc.Poisson.lintegral_referenceIntensity_window hm Set.univ T
      _ = ∫⁻ s in Set.Ioc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume := by
          simp only [Measure.restrict_univ]
      _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g (s, e)‖₊ : ℝ≥0∞) ∂ν ∂volume :=
          lintegral_mono_set Set.Ioc_subset_Icc_self
      _ < ⊤ := hfin

end Transfers

section Main

open LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.Picard (SolvesOn solvesOn_of_eqn jumpDiffusionOfSolvesOn
  compensatedIntegral_congr_ae)

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (coeffs : JumpDiffusionCoeffs n d E)

/-- **The Itô–Lévy formula, residual form, along a solution with càdlàg paths at every sample
point.** For a jump diffusion carrying SDE data at a filtration satisfying the usual conditions,
with jointly measurable coefficients and a drift of finite energy along the path, and a jointly
`C²` state function whose derived integrands `(∇u)ᵀσ` and `u(x + γ) − u(x)` along the path have
finite energy and whose compensator drift is integrable, the increment `u(T, X_T) − u(0, X_0)`
minus the drift integral and the Brownian integral is the compensated integral plus the
compensator-drift integral, almost surely. No bound on the derivatives of `u` is assumed. -/
theorem itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim (x₀ : Fin n → ℝ)
    (X : JumpDiffusion W N coeffs x₀) (S : LevyStochCalc.Ito.BigJump.SdeData X)
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hXright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X.X s ω) (𝓝[>] t) (𝓝 (X.X t ω)))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hμmeas : Measurable (Function.uncurry coeffs.μ))
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (T : ℝ) (hT : 0 < T)
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            h_sigmaGrad_sq T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  have hXm : Measurable (Function.uncurry X.X) := X.measurable_path
  have hXm' : Measurable fun q : ℝ × Ω => X.X q.1 q.2 := hXm
  have hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t) :=
    measurable_of_progressivelyMeasurable S.ℱ S.X_prog
  have hadapt : Adapted S.ℱ X.X := hXadapt
  have hXcad := X.cadlag_paths
  have hcount := ae_countable_setOf_pos_ne_leftLimPathAt X.X hXcad
  -- the left-limit path
  have hΛm : Measurable fun q : ℝ × Ω => leftLimPathAt X.X q.1 q.2 :=
    measurable_uncurry_leftLimPathAt hXm' hXleft
  have hΛp : ∀ i : Fin n, ProgressivelyMeasurable S.ℱ fun ω s => leftLimPathAt X.X s ω i :=
    fun i => progressivelyMeasurable_leftLimPathAt hℱ0 hXadapt hXleft i
  -- the drift along the path
  have hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i) :=
    fun i => ((measurable_pi_apply i).comp hμmeas).comp
      (measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst)))
  have hμp : ∀ i : Fin n, ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i :=
    fun i => LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state S.X_prog
      (f := fun s x => coeffs.μ s x i) ((measurable_pi_apply i).comp hμmeas)
  -- the jump coefficient along the left limits
  have hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i :=
    fun i => ((measurable_pi_apply i).comp hγmeas).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((hΛm.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
          (measurable_snd.comp measurable_snd)))
  have hγpL : ∀ i : Fin n, MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i :=
    fun i => LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_comp_state hΛp
      (F := fun s x e => coeffs.γ s x e i) ((measurable_pi_apply i).comp hγmeas)
  have hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun i T' hT' => (lintegral_sq_marked_leftLimPathAt_eq hXcad
      (fun s x e => coeffs.γ s x e i) T').trans_lt (S.γ_sq i T' hT')
  have hpredL : ∀ i : Fin n, MarkedPredictable S.ℱ ν
      (zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i) :=
    fun i => markedPredictable_zeroExtPos_comp_leftLimPathAt X.X S.ℱ hXadapt
      (fun ω t _ j => hXleft ω t j) (ν := ν) (F := fun s x e => coeffs.γ s x e i)
      ((measurable_pi_apply i).comp hγmeas)
  -- the arrival-time jump relation at every level of the spanning sequence
  have hjump : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ k, θ k ∈ Set.Ioc (0 : ℝ) T ∧ ε k ∈ spanningSets ν j) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, g p ∂(N.N ω)
        = ∑ k : Fin K, g (θ k, ε k)) ∧
      ∀ k : Fin K,
        X.X (θ k) ω
          = leftLimPathAt X.X (θ k) ω
            + coeffs.γ (θ k) (leftLimPathAt X.X (θ k) ω) (ε k) :=
    fun j => ae_exists_atomEnum_jump_eq_gamma_of_sdeData S hℱ0 hnull hμm hμp hμq hγmL hγpL hγqL
      hpredL j hT
  -- the left-limit jump increment of `u`
  have hmu : Measurable fun p : Ω × ℝ × E => jumpIncrLeft u coeffs X.X p.1 p.2.1 p.2.2 :=
    measurable_jumpIncrLeft hu.continuous hγmeas hXm' hXleft
  have hpu : MarkedProgressivelyMeasurable S.ℱ (jumpIncrLeft u coeffs X.X) :=
    markedProgressivelyMeasurable_jumpIncrLeft hu.continuous hγmeas hℱ0 hXadapt hXleft
  have hqu : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖jumpIncrLeft u coeffs X.X ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' => (lintegral_sq_marked_leftLimPathAt_eq hXcad
      (fun s x e => u s (x + coeffs.γ s x e) - u s x) T').trans_lt (h_jumpInt_sq T' hT')
  -- the compensator drift of `u` along the left limits, in the reference-intensity form
  have hCdu : ∀ᵐ ω ∂P, IntegrableOn (fun q : ℝ × E =>
      compensatorDriftIntegrand u coeffs.γ q.1 (leftLimPathAt X.X q.1 ω) q.2)
      (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (LevyStochCalc.Poisson.referenceIntensity ν) := by
    filter_upwards [h_compDrift_int, hcount] with ω hω hcω
    refine integrableOn_window_univ_of_lintegral_lt_top
      ((measurable_compensatorDriftIntegrand_path hu hγmeas hΛm).comp measurable_prodMk_left) ?_
    calc ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (leftLimPathAt X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume
        = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_eq_of_countable_ne hcω T] with s hs
          rw [hs]
      _ < ⊤ := hω
  -- the identity on the event that the path stays in the ball of radius `m`
  have hmain : ∀ m : ℕ, ∀ᵐ ω ∂P, (0 < m ∧ T < 3 * (m : ℝ)) →
      ω ∈ Brownian.Ito.boundedPathSet X.X T m →
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            h_sigmaGrad_sq T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
    intro m
    by_cases hmT : 0 < m ∧ T < 3 * (m : ℝ)
    swap
    · exact Filter.Eventually.of_forall fun ω h => absurd h hmT
    obtain ⟨hm, hTm⟩ := hmT
    have hR : (0 : ℝ) < 2 * (m : ℝ) := by positivity
    have hv : ContDiff ℝ 2 (Function.uncurry (cutoffFun₂ u (2 * (m : ℝ)))) :=
      contDiff_uncurry_cutoffFun₂ hu _
    obtain ⟨K, -, hK₀, hK₁, hK₂⟩ := exists_globalBound_cutoffFun₂ hu hR
    -- the bounded-derivative formula for the cut-off
    have hM16 := itoLevyFormula_jumpResidual_of_sdeData_of_leftLim W N coeffs x₀ X S hℱ0 hnull
      hXleft hμmeas hσmeas hγmeas hμq (cutoffFun₂ u (2 * (m : ℝ))) hv hK₀ hK₁ hK₂ T hT
    -- the continuous side transfers term by term
    have hcont := ae_continuousSide_cutoffFun₂_eq W S.ℱ S.isBrownian u hm hTm hT hadapt hXright
      (fun j => measurable_diffusionIntegrand_path hv hσmeas X.measurable_path j)
      (fun j => progressivelyMeasurable_diffusionIntegrand_path hv hσmeas S.X_prog j)
      (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁ S.σ_meas S.σ_sq j hT')
      (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
      (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
      h_sigmaGrad_sq
    -- the left-limit jump increment of the cut-off
    have hmv : Measurable fun p : Ω × ℝ × E =>
        jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X p.1 p.2.1 p.2.2 :=
      measurable_jumpIncrLeft hv.continuous hγmeas hXm' hXleft
    have hpv : MarkedProgressivelyMeasurable S.ℱ
        (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X) :=
      markedProgressivelyMeasurable_jumpIncrLeft hv.continuous hγmeas hℱ0 hXadapt hXleft
    have hqv : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤ :=
      fun T' hT' => lintegral_sq_jumpIncrement_path_lt_top hv hK₁ hγmL hγqL hT'
    have hCdv : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet X.X T m →
        IntegrableOn (fun q : ℝ × E => compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ)))
            coeffs.γ q.1 (leftLimPathAt X.X q.1 ω) q.2)
          (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E))
          (LevyStochCalc.Poisson.referenceIntensity ν) := by
      filter_upwards [ae_lintegral_compensatorDriftIntegrand_lt_top hv hK₂ hγmeas hΛm hγmL hγqL
        hT] with ω hω _
      exact integrableOn_window_univ_of_lintegral_lt_top
        ((measurable_compensatorDriftIntegrand_path hv hγmeas hΛm).comp measurable_prodMk_left)
        hω
    -- the jump side transfers as a sum
    have hjs := ae_jumpSide_cutoffFun₂_eq N S.ℱ S.isPoisson u hu hγmeas hT hm hTm hXadapt hXleft
      hmv hpv hqv hmu hpu hqu hCdv (by filter_upwards [hCdu] with ω hω _; exact hω) hjump
    -- the compensated integrals in the point-value convention
    have hcmpv : ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs X.X) hmv hpv hqv T ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (fun ω' s e => cutoffFun₂ u (2 * (m : ℝ)) s
                (X.X s ω' + coeffs.γ s (X.X s ω') e) - cutoffFun₂ u (2 * (m : ℝ)) s (X.X s ω'))
            (measurable_jumpIncrement_path hv hγmeas X.measurable_path)
            (markedProgressivelyMeasurable_jumpIncrement_path hv hγmeas S.X_prog)
            (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hv hK₁ S.γ_meas S.γ_sq hT')
            T ω :=
      compensatedIntegral_congr_of_countable_ne N S.isPoisson
        (fun s x e => cutoffFun₂ u (2 * (m : ℝ)) s (x + coeffs.γ s x e)
          - cutoffFun₂ u (2 * (m : ℝ)) s x) hcount hmv
        (measurable_jumpIncrement_path hv hγmeas X.measurable_path) hpv
        (markedProgressivelyMeasurable_jumpIncrement_path hv hγmeas S.X_prog) hqv
        (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hv hK₁ S.γ_meas S.γ_sq hT') hT
    have hcmpu : ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (jumpIncrLeft u coeffs X.X) hmu hpu hqu T ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
            (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
            (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
            h_jumpInt_sq T ω :=
      compensatedIntegral_congr_of_countable_ne N S.isPoisson
        (fun s x e => u s (x + coeffs.γ s x e) - u s x) hcount hmu
        (measurable_jumpIncrement_path hu hγmeas X.measurable_path) hpu
        (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog) hqu
        h_jumpInt_sq hT
    filter_upwards [hM16, hcont, hjs, hcmpv, hcmpu, hCdv, hCdu, hcount]
      with ω h16 hc hj hcv hcu hCv hCu hcω
    intro _ hb
    -- the compensator drifts in the iterated point-value convention
    have hcdv : (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s (X.X s ω) e ∂ν)
        = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
            compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
              (leftLimPathAt X.X q.1 ω) q.2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      rw [← setIntegral_congr_of_countable_ne
        (fun s x e => compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s x e) ν
        hcω T, (integral_window_eq_and_integrableOn
        (fun s e => compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s
          (leftLimPathAt X.X s ω) e) (hCv hb)).1]
      simp only [Measure.restrict_univ]
    have hcdu : (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
          compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)
        = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
            compensatorDriftIntegrand u coeffs.γ q.1 (leftLimPathAt X.X q.1 ω) q.2
              ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      rw [← setIntegral_congr_of_countable_ne
        (fun s x e => compensatorDriftIntegrand u coeffs.γ s x e) ν hcω T,
        (integral_window_eq_and_integrableOn
        (fun s e => compensatorDriftIntegrand u coeffs.γ s (leftLimPathAt X.X s ω) e) hCu).1]
      simp only [Measure.restrict_univ]
    have hc' := hc hb
    have hj' := hj hb
    rw [hcv, hcu, ← hcdv, ← hcdu] at hj'
    rw [← hc', h16, hj']
  -- almost every path stays in some ball of a radius exceeding the horizon
  have hex : ∀ᵐ ω ∂P, ∃ m : ℕ, (0 < m ∧ T < 3 * (m : ℝ)) ∧
      ω ∈ Brownian.Ito.boundedPathSet X.X T m := by
    filter_upwards [ae_exists_mem_boundedPathSet X T] with ω hω
    obtain ⟨m, hm⟩ := hω
    refine ⟨m + ⌈T⌉₊ + 1, ⟨by omega, ?_⟩,
      Brownian.Ito.boundedPathSet_mono X.X T (by omega) hm⟩
    have h1 : T ≤ ⌈T⌉₊ := Nat.le_ceil T
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    push_cast
    linarith
  filter_upwards [MeasureTheory.ae_all_iff.mpr hmain, hex] with ω hω hex
  obtain ⟨m, hmT, hb⟩ := hex
  exact hω m hmT hb

/-- **The Itô–Lévy formula, residual form, along a jump diffusion.** For a jump diffusion
carrying SDE data at a filtration satisfying the usual conditions, with jointly measurable
coefficients and a drift of finite energy along the path, and a jointly `C²` state function
whose derived integrands `(∇u)ᵀσ` and `u(x + γ) − u(x)` along the path have finite energy and
whose compensator drift is integrable, the increment `u(T, X_T) − u(0, X_0)` minus the drift
integral and the Brownian integral is the compensated integral plus the compensator-drift
integral, almost surely. No bound on the derivatives of `u` and no growth or Lipschitz condition
on the coefficients is assumed. -/
theorem itoLevyFormula_jumpResidual_of_sdeData_general (x₀ : Fin n → ℝ)
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
    (T : ℝ) (hT : 0 < T)
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
            (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
            h_sigmaGrad_sq T ω)
      = LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
          (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
          (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
          h_jumpInt_sq T ω
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
  -- the representative with càdlàg paths at every sample point
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
  -- the admissibility inputs transported to the representative
  have hσY : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (Y s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun j T' hT' => (lintegral_sq_comp_cadlagRep hG0
      (fun s x => diffusionIntegrand u coeffs.σ s x j) T').trans_lt (h_sigmaGrad_sq j T' hT')
  have hγY : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (Y s ω + coeffs.γ s (Y s ω) e) - u s (Y s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' => (lintegral_sq_marked_comp_cadlagRep hG0
      (fun s x e => u s (x + coeffs.γ s x e) - u s x) T').trans_lt (h_jumpInt_sq T' hT')
  have hcdY : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (Y s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤ := by
    filter_upwards [h_compDrift_int, hpe] with ω hω hag
    have hrw : (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (Y s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume)
        = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume :=
      setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hag s hs.1]
    rw [hrw]
    exact hω
  -- the formula along the representative
  let XY : JumpDiffusion W N coeffs x₀ :=
    jumpDiffusionOfSolvesOn W N S.ℱ S.isBrownian S.isPoisson coeffs x₀ hYm hY0
      (Eventually.of_forall fun ω t _ => hYcad ω t) hYS hYsol
  let SY : LevyStochCalc.Ito.BigJump.SdeData XY :=
    LevyStochCalc.Ito.BigJump.SdeData.ofSolvesOn XY S.ℱ S.isBrownian S.isPoisson hYa hYsol
  haveI : SY.ℱ.IsRightContinuous := ‹S.ℱ.IsRightContinuous›
  have hmain := itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim W N coeffs x₀ XY SY
    hℱ0 hnull (fun ω t => (hYcad ω t).1) (fun ω t j => (hYcad ω t).2 j) hμmeas hσmeas hγmeas
    (fun i T' hT' => (lintegral_sq_comp_cadlagRep hG0 (fun s x => coeffs.μ s x i) T').trans_lt
      (hμq i T' hT')) u hu T hT hσY hγY hcdY
  -- the four terms read the path only up to a null set
  have hBro := multidimIntegral_congr_ae W S.ℱ S.isBrownian
    (fun s ω => diffusionIntegrand u coeffs.σ s (Y s ω))
    (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
    (fun j => measurable_diffusionIntegrand_path hu hσmeas hYm j)
    (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas hYa j)
    hσY
    (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
    (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
    h_sigmaGrad_sq
    hT (by
      filter_upwards [hYX] with ω hω
      filter_upwards [hω] with s hs
      exact congrArg (diffusionIntegrand u coeffs.σ s) hs)
  have hCmp := compensatedIntegral_congr_ae N S.ℱ S.isPoisson
    (fun ω' s e => u s (Y s ω' + coeffs.γ s (Y s ω') e) - u s (Y s ω'))
    (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
    (measurable_jumpIncrement_path hu hγmeas hYm)
    (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas hYa)
    hγY
    (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
    (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
    h_jumpInt_sq
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

/-- **The Itô–Lévy formula for a jump diffusion.** For a jump diffusion carrying SDE data at a
filtration satisfying the usual conditions, with jointly measurable coefficients and a drift of
finite energy along the path, and a jointly `C²` state function whose derived integrands
`(∇u)ᵀσ` and `u(x + γ) − u(x)` along the path have finite energy and whose compensator drift is
integrable, `u(T, X_T) − u(0, X_0)` is the drift integral of `∂ₜu + 𝓛u`, plus the Brownian
integral of `(∇u)ᵀσ`, plus the compensated-Poisson integral of `u(x + γ) − u(x)`, plus the
compensator-drift integral of `u(x + γ) − u(x) − γᵀ∇u`, all along the path, almost surely. -/
theorem itoLevyFormula_general (x₀ : Fin n → ℝ)
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
    (T : ℝ) (hT : 0 < T)
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e) - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤)
    (h_compDrift_int : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      u T (X.X T ω) - u 0 (X.X 0 ω)
        = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          + MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
              (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              (fun j => measurable_diffusionIntegrand_path hu hσmeas X.measurable_path j)
              (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hσmeas S.X_prog j)
              h_sigmaGrad_sq T ω
          + LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path hu hγmeas X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path hu hγmeas S.X_prog)
              h_jumpInt_sq T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  filter_upwards [itoLevyFormula_jumpResidual_of_sdeData_general W N coeffs x₀ X S hℱ0 hnull
    hμmeas hσmeas hγmeas hμq u hu T hT h_sigmaGrad_sq h_jumpInt_sq h_compDrift_int] with ω hω
  linarith

end Main

end LevyStochCalc.Ito.JumpFormula
