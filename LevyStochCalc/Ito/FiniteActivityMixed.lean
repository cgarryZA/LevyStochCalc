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
# The finite-activity Itô–Lévy identity along a truncated path, in the mixed form

Along a càdlàg path `y` that is a continuous vector Itô process plus the left-limit jump sum of
a jump diffusion `X` over a mark set of finite intensity, the increment of a `C²` state function
with bounded derivatives is the mixed drift integral, the Brownian integral of the mixed
diffusion integrand, the compensated integral of the mixed jump increment over the mark set and
the compensator-drift integral over that set. The derivatives of the state function are read
along `y` and the coefficients along `X`.

The proof telescopes Itô's formula for the time-augmented continuous part between consecutive
arrival times of the mark set, identifies the increments across the arrival times with the
atom sum of the mixed jump increment read at the left limits, and identifies that atom sum with
the pathwise form of the compensated integral.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevy_finiteActivity_mixed`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability
open LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim LevyStochCalc.Ito.BigJump
open LevyStochCalc.Ito.JumpSplitting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section BrownianSum

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)

include hℱ in
/-- The `L²` Itô integral of a finite sum of integrands is the sum of their Itô integrals. -/
theorem stochasticIntegralBrownian_sum_univ {T : ℝ} (hT : 0 < T) : ∀ {m : ℕ}
    (H : Fin m → Ω → ℝ → ℝ)
    (hm : ∀ i, Measurable (Function.uncurry (H i)))
    (hp : ∀ i, Probability.ProgressivelyMeasurable ℱ (H i))
    (hq : ∀ (i : Fin m) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hms : Measurable (Function.uncurry fun ω s => ∑ i, H i ω s))
    (hps : Probability.ProgressivelyMeasurable ℱ fun ω s => ∑ i, H i ω s)
    (hqs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖∑ i, H i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => ∑ i, H i ω s) hms hps hqs T
      =ᵐ[P] fun ω => ∑ i, stochasticIntegralBrownian W ℱ hℱ (H i) (hm i) (hp i) (hq i) T ω := by
  intro m
  induction m with
  | zero =>
    intro H hm hp hq hms hps hqs
    have h0 : (fun ω s => ∑ i : Fin 0, H i ω s) = fun (_ : Ω) (_ : ℝ) => (0 : ℝ) := by
      funext ω s
      simp
    have hm0 : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) := measurable_const
    have hp0 : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => (0 : ℝ) :=
      Probability.progressivelyMeasurable_const ℱ 0
    have hq0 : ∀ T : ℝ, 0 < T → ∫⁻ _ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T _
      simp
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ h0 hms hps hqs hm0 hp0 hq0 T]
    filter_upwards [stochasticIntegralBrownian_ae_zero W ℱ hℱ hm0 hp0 hq0 T] with ω hω
    rw [hω]
    simp
  | succ m ih =>
    intro H hm hp hq hms hps hqs
    have hsucc : (fun ω s => ∑ i : Fin (m + 1), H i ω s)
        = fun ω s => H 0 ω s + ∑ i : Fin m, H i.succ ω s := by
      funext ω s
      exact Fin.sum_univ_succ _
    have hmt : Measurable (Function.uncurry fun ω s => ∑ i : Fin m, H i.succ ω s) :=
      Finset.measurable_sum _ fun i _ => hm i.succ
    have hpt : Probability.ProgressivelyMeasurable ℱ fun ω s => ∑ i : Fin m, H i.succ ω s :=
      progressivelyMeasurable_finset_sum _ fun i _ => hp i.succ
    have hqt : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖∑ i : Fin m, H i.succ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun T hT =>
      lintegral_window_sq_le_of_abs_le (a := fun i => H i.succ) (c := 1)
        (fun i => hm i.succ) (fun ω s => by rw [one_mul]; exact Finset.abs_sum_le_sum_abs _ _) T
        (fun i => hq i.succ T hT)
    have hma : Measurable (Function.uncurry fun ω s => H 0 ω s + ∑ i : Fin m, H i.succ ω s) :=
      (hm 0).add hmt
    have hpa : Probability.ProgressivelyMeasurable ℱ
        fun ω s => H 0 ω s + ∑ i : Fin m, H i.succ ω s := (hp 0).add hpt
    have hqa : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H 0 ω s + ∑ i : Fin m, H i.succ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro T hT
      have := hqs T hT
      simp only [Fin.sum_univ_succ] at this
      exact this
    rw [stochasticIntegralBrownian_congr_fun W ℱ hℱ hsucc hms hps hqs hma hpa hqa T]
    filter_upwards [stochasticIntegralBrownian_add W ℱ hℱ (hm 0) hmt (hp 0) hpt (hq 0) hqt hma
      hpa hqa hT, ih (fun i => H i.succ) (fun i => hm i.succ)
      (fun i => hp i.succ) (fun i => hq i.succ) hmt hpt hqt] with ω h1 h2
    rw [h1, h2, Fin.sum_univ_succ]

end BrownianSum

section Main

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : MultidimBrownianMotion P d} {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- **The finite-activity Itô–Lévy identity in the mixed form.** Along a càdlàg adapted path
`y` that is a continuous vector Itô process `V` plus the left-limit jump sum of the jump
diffusion `X` over a mark set `B` of finite intensity, the increment of `u` along `y` is the
mixed drift integral, the Brownian integral of the mixed diffusion integrand, the compensated
integral of the mixed jump increment cut to `B` and the compensator-drift integral over `B`. -/
theorem itoLevy_finiteActivity_mixed
    (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
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
    {B : Set E} (hB : MeasurableSet B) (hBν : ν B ≠ ⊤)
    (y : ℝ → Ω → Fin n → ℝ)
    (hy_m : Measurable (Function.uncurry y))
    (hy_rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => y s ω) (𝓝[>] t) (𝓝 (y t ω)))
    (hy_ad : ∀ t : ℝ, Measurable[S.ℱ t] (y t))
    (hy_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => y s ω j) (𝓝[<] t) (𝓝 L))
    (V : ℝ → Ω → Fin n → ℝ)
    (hV : IsVectorItoVersion W S.ℱ S.isBrownian
      (fun i j ω s => coeffs.σ s (X.X s ω) i j) S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
      (continuousDriftLeftAt coeffs ν X.X B) V)
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      y t ω i = V t ω i + jumpSumLeftAt (coeffs.markCutγ B) N X.X B t ω i)
    (hBm : ∀ j : Fin d, Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j))
    (hBp : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
    (hBq : ∀ (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hCm : Measurable fun p : Ω × ℝ × E => markCut B
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) p.1 p.2.1 p.2.2)
    (hCp : Probability.MarkedProgressivelyMeasurable S.ℱ (markCut B
      fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e))
    (hCq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut B (fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e) ω s e‖₊ :
        ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P,
      u T (y T ω) - u 0 (y 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω))
        - MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
            (fun s ω => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω)) hBm hBp hBq T ω
        = stochasticIntegral N S.ℱ S.isPoisson
            (markCut B fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
            hCm hCp hCq T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in B,
              mixedCompensatorDriftIntegrand u coeffs.γ s (y s ω) (X.X s ω) e ∂ν := by
  classical
  -- ## The time-augmented representative and its derivatives
  set H : Fin n → Fin d → Ω → ℝ → ℝ := fun i j ω s => coeffs.σ s (X.X s ω) i j with hHdef
  set bdr : Fin n → Ω → ℝ → ℝ := continuousDriftLeftAt coeffs ν X.X B with hbdrdef
  set f : (Fin (n + 1) → ℝ) → ℝ := timeAugFun u with hfdef
  have hfu : ∀ z, f z = timeAugFun u z := fun _ => rfl
  have hfC : ContDiff ℝ 2 f := contDiff_timeAugFun hu
  set f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ := fderiv ℝ f with hf'def
  set f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ :=
    fderiv ℝ f' with hf''def
  have hf : ∀ z, HasFDerivAt f (f' z) z :=
    fun z => (hfC.differentiable (by norm_num) z).hasFDerivAt
  have hf' : ∀ z, HasFDerivAt f' (f'' z) z := fun z =>
    ((hfC.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) z).hasFDerivAt
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hf''c : Continuous f'' :=
    ((hfC.fderiv_right (m := 1) (by norm_num)).fderiv_right (m := 0) (by norm_num)).continuous
  have hK₁' : ∀ (p : Fin (n + 1)) (z : Fin (n + 1) → ℝ), |coordDeriv f' p z| ≤ max K₀ K₁ :=
    abs_coordDeriv_timeAug_le hfu hf hK₀ hK₁
  have hK₁0 : (0 : ℝ) ≤ max K₀ K₁ := le_trans (abs_nonneg _) (hK₁' 0 0)
  have hK₂' := abs_coordDeriv₂_timeAug_mul_le hfu hf hf' hK₂ H
  -- ## The time-augmented processes and their admissibility
  set V' : ℝ → Ω → Fin (n + 1) → ℝ := timeAugProcess V with hV'def
  set Y' : ℝ → Ω → Fin (n + 1) → ℝ := timeAugProcess y with hY'def
  set H' : Fin (n + 1) → Fin d → Ω → ℝ → ℝ := timeAugDiffusion H with hH'def
  set b' : Fin (n + 1) → Ω → ℝ → ℝ := timeAugDrift bdr with hb'def
  have hV' := hV.timeAug
  have hH'm : ∀ p j, Measurable (Function.uncurry (H' p j)) :=
    measurable_timeAugDiffusion H S.σ_meas
  have hH'p : ∀ p j, Probability.ProgressivelyMeasurable S.ℱ (H' p j) :=
    progressivelyMeasurable_timeAugDiffusion H S.ℱ S.σ_prog
  have hH'q : ∀ (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖H' p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    sq_timeAugDiffusion H S.σ_sq
  have hγmeasi : ∀ i : Fin n,
      Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i :=
    fun i => (measurable_pi_apply i).comp hγmeas
  have hXm : Measurable fun q : ℝ × Ω => X.X q.1 q.2 := X.measurable_path
  have hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i :=
    fun i => measurable_jumpCoeff_leftLimPathAt hXm hXleft i (hγmeasi i)
  have hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i :=
    fun i => markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt hℱ0 hXadapt hXleft i
      (hγmeasi i)
  have hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    intro i T' hT'
    rw [lintegral_sq_jumpCoeff_leftLimPathAt_eq X.cadlag_paths i T']
    exact S.γ_sq i T' hT'
  have hbdrm : ∀ i, Measurable (Function.uncurry (bdr i)) :=
    fun i => measurable_uncurry_continuousDriftLeftAt B i (hμm i) (hγmL i)
  have hbdrp : ∀ i, Probability.ProgressivelyMeasurable S.ℱ (bdr i) :=
    fun i => progressivelyMeasurable_continuousDriftLeftAt B i S.ℱ (hμp i) (hγpL i)
  have hbdrq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖bdr i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i T' hT' => lintegral_sq_continuousDriftLeftAt_lt_top hBν i (hμm i) (hμq i) (hγmL i)
      (hγqL i) T' hT'
  have hb'm : ∀ p, Measurable (Function.uncurry (b' p)) := measurable_timeAugDrift bdr hbdrm
  have hb'p : ∀ p, Probability.ProgressivelyMeasurable S.ℱ (b' p) :=
    progressivelyMeasurable_timeAugDrift bdr S.ℱ hbdrp
  have hb'q : ∀ (p : Fin (n + 1)) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖b' p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p
    induction p using Fin.cases with
    | zero =>
      intro T' hT'
      simp [b', timeAugDrift, Real.volume_Icc]
    | succ q => simpa [b', timeAugDrift] using hbdrq q
  have hY'm : Measurable (Function.uncurry fun ω s => Y' s ω) := by
    refine measurable_pi_iff.mpr fun p => ?_
    induction p using Fin.cases with
    | zero =>
      simp only [Function.uncurry, Y', timeAugProcess, Fin.cons_zero]
      exact measurable_snd
    | succ q =>
      simp only [Function.uncurry, Y', timeAugProcess, Fin.cons_succ]
      exact (measurable_pi_apply q).comp (hy_m.comp (measurable_snd.prodMk measurable_fst))
  have hY'ad : ∀ t : ℝ, Measurable[S.ℱ t] (Y' t) := by
    intro t
    letI : MeasurableSpace Ω := S.ℱ t
    refine measurable_pi_iff.mpr fun p => ?_
    induction p using Fin.cases with
    | zero =>
      simp only [Y', timeAugProcess, Fin.cons_zero]
      exact measurable_const
    | succ q =>
      simp only [Y', timeAugProcess, Fin.cons_succ]
      exact (measurable_pi_apply q).comp (hy_ad t)
  have hY'rc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y' s ω) (𝓝[>] t) (𝓝 (Y' t ω)) := by
    intro ω t
    refine tendsto_pi_nhds.mpr fun p => ?_
    induction p using Fin.cases with
    | zero =>
      simp only [Y', timeAugProcess, Fin.cons_zero]
      exact tendsto_id.mono_left nhdsWithin_le_nhds
    | succ q =>
      simp only [Y', timeAugProcess, Fin.cons_succ]
      exact ((continuous_apply q).tendsto _).comp (hy_rc ω t)
  have hY'comp : ∀ {φ : (Fin (n + 1) → ℝ) → ℝ}, Continuous φ →
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => φ (Y' s ω) := fun {φ} hφ =>
    progressivelyMeasurable_of_rightContinuous (X := fun s ω => φ (Y' s ω))
      (fun t => hφ.measurable.comp (hY'ad t)) (fun ω t => (hφ.tendsto _).comp (hY'rc ω t))
  -- ## The chain data
  have hmG : ∀ (p : Fin (n + 1)) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y' s ω) * H' p j ω s) :=
    measurable_timeAugWeight f' y H
      (fun q k => ((continuous_coordDeriv hf'c q.succ).measurable.comp hY'm).mul (S.σ_meas q k))
  have hpG : ∀ (p : Fin (n + 1)) (j : Fin d), Probability.ProgressivelyMeasurable S.ℱ
      fun ω s => coordDeriv f' p (Y' s ω) * H' p j ω s :=
    progressivelyMeasurable_timeAugWeight f' y H S.ℱ
      (fun q k => (hY'comp (continuous_coordDeriv hf'c q.succ)).mul (S.σ_prog q k))
  have hqG : ∀ (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (Y' s ω) * H' p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    sq_timeAugWeight f' y H (fun q k => energy_lt_top_of_abs_le_mul hK₁0
      (fun ω s => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hK₁' _ _) (abs_nonneg _))
      (S.σ_sq q k))
  have hmD : ∀ p : Fin (n + 1), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (Y' s ω) * b' p ω s) := fun p =>
    ((continuous_coordDeriv hf'c p).measurable.comp hY'm).mul (hb'm p)
  have hqD : ∀ (p : Fin (n + 1)) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (Y' s ω) * b' p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun p =>
    energy_lt_top_of_abs_le_mul hK₁0
      (fun ω s => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hK₁' _ _) (abs_nonneg _))
      (hb'q p)
  have hmQ : ∀ p q : Fin (n + 1), Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (Y' s ω) * ∑ j : Fin d, H' p j ω s * H' q j ω s) :=
    fun p q => ((continuous_coordDeriv₂ hf''c p q).measurable.comp hY'm).mul
      (Finset.measurable_sum _ fun j _ => (hH'm p j).mul (hH'm q j))
  have hQint : ∀ᵐ ω ∂P, ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (Y' s ω) * ∑ j : Fin d, H' p j ω s * H' q j ω s)
      (Set.Ioc (0 : ℝ) T) volume := by
    filter_upwards [ae_integrableOn_Ioc_sum_mul hH'm (fun p j => hH'q p j T hT)] with ω hω p q
    refine Integrable.mono' ((hω p q).abs.const_mul |K₂|)
      (Measurable.of_uncurry_left (hmQ p q)).aestronglyMeasurable ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, abs_mul]
    exact (hK₂' p q _ ω s).trans (mul_le_mul_of_nonneg_right (le_abs_self K₂) (abs_nonneg _))
  -- ## The stopping times and the shifts
  set σ : ℕ → Ω → WithTop ℝ := cappedJumpTime N B T with hσdef
  obtain ⟨hσ, hmono, h0⟩ := cappedJumpTime_chain_of_complete N B S.isPoisson hB hBν hnull0 hT.le
  have hσ0 : ∀ (k : ℕ) (ω : Ω), ((0 : ℝ) : WithTop ℝ) ≤ σ k ω := fun k ω =>
    le_min (by
      rw [← LevyStochCalc.Poisson.jumpTime_zero N B ω]
      exact LevyStochCalc.Poisson.jumpTime_mono N B (Nat.zero_le k) ω) (by exact_mod_cast hT.le)
  have hσne : ∀ (k : ℕ) (ω : Ω), σ k ω ≠ ⊤ := fun k ω =>
    ne_top_of_le_ne_top WithTop.coe_ne_top (min_le_right _ _)
  set c : ℕ → Ω → Fin n → ℝ := fun k ω => y (σ k ω).untopA ω - V (σ k ω).untopA ω with hcdef
  set c' : ℕ → Ω → Fin (n + 1) → ℝ := fun k ω => Fin.cons 0 (c k ω) with hc'def
  have hyprog : ∀ i : Fin n, Probability.ProgressivelyMeasurable S.ℱ fun ω s => y s ω i :=
    fun i => progressivelyMeasurable_of_rightContinuous (X := fun s ω => y s ω i)
      (fun t => (measurable_pi_apply i).comp (hy_ad t))
      (fun ω t => ((continuous_apply i).tendsto _).comp (hy_rc ω t))
  have hVprog : ∀ i : Fin n, Probability.ProgressivelyMeasurable S.ℱ fun ω s => V s ω i :=
    fun i => hV.progressivelyMeasurable_comp (continuous_apply i)
  have hc : ∀ k, Measurable[(hσ k).measurableSpace] (c k) := fun k =>
    measurable_stoppingTime_eval_untopA (Y := fun s ω => y s ω - V s ω)
      (fun i => (hyprog i).sub (hVprog i)) (hσ k)
  have hc' : ∀ k, Measurable[(hσ k).measurableSpace] (c' k) := fun k =>
    Measurable.finCons_zero (hc k)
  have hcm : ∀ k, Measurable (c' k) := fun k => (hc' k).mono (hσ k).measurableSpace_le le_rfl
  have hsplit' : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      y t ω i = V t ω i + JumpSplitting.jumpSumLeft X B t ω i := by
    filter_upwards [hsplit] with ω hω t ht i
    rw [hω t ht i, jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath X hB]
    rfl
  have hcap := ae_forall_add_cappedJumpSumLeft_eq_of_path (Z := y) hsplit' hB hBν hT.le
  have hceq : ∀ᵐ ω ∂P, ∀ k : ℕ, c k ω = cappedJumpSumAt X (leftLimPath X) B T k ω := by
    filter_upwards [hsplit] with ω hω k
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (hσne k ω)
    have hr0 : 0 ≤ r := by
      have := hσ0 k ω
      rw [← hr] at this
      exact_mod_cast this
    have hunt : (σ k ω).untopA = r := by rw [← hr]; rfl
    have hclip : clipTime (LevyStochCalc.Poisson.jumpTime N B k) T ω = r := by
      rw [clipTime_jumpTime_eq_untopA]
      exact hunt
    funext i
    simp only [c, hunt, cappedJumpSumAt, hclip, Pi.sub_apply]
    rw [hω r hr0 i, jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath X hB]
    ring
  have hshift : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V' s ω + c' k ω = Y' s ω := by
    filter_upwards [hcap, hceq] with ω hω hcω k s h1 h2
    have hks := hω k s h1 h2
    rw [← hcω k] at hks
    simp only [V', c', Y', timeAugProcess]
    rw [cons_add_cons_zero, hks]
  -- ## The stopped increments and the per-interval formula
  have hV'm : Measurable (Function.uncurry fun ω s => V' s ω) := hV'.measurable_uncurry
  have hV'prog : Probability.ProgressivelyMeasurable S.ℱ fun ω s => V' s ω :=
    Probability.ProgressivelyMeasurable.of_isStronglyProgressive
      (StronglyAdapted.isStronglyProgressive_of_continuous hV'.adapted hV'.continuous_path)
  have hmVun : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) := fun k p j =>
    ((continuous_coordDeriv hf'c p).measurable.comp
      (hV'm.add ((hcm k).comp measurable_fst))).mul (hH'm p j)
  have hqVun : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun k p j => energy_lt_top_of_abs_le_mul hK₁0
      (fun ω s => by rw [abs_mul]; exact mul_le_mul_of_nonneg_right (hK₁' _ _) (abs_nonneg _))
      (hH'q p j)
  have hmV : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (σ (k + 1))
          (fun ω s => coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s
        - Probability.stopped (σ k)
            (fun ω s => coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s) := fun k p j =>
    measurable_uncurry_stopped_sub_shift (hσ k) (hσ (k + 1)) (hcm k) hV'm
      (continuous_coordDeriv hf'c p) (hH'm p j) (fun _ _ => rfl)
  have hpV : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d),
      Probability.ProgressivelyMeasurable S.ℱ fun ω s =>
      Probability.stopped (σ (k + 1))
          (fun ω s => coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s
        - Probability.stopped (σ k)
            (fun ω s => coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s := fun k p j =>
    progressivelyMeasurable_stopped_sub_shift (hσ k) (hσ (k + 1)) (hmono k) (hc' k) hV'prog
      (continuous_coordDeriv hf'c p) (hH'p p j) (fun _ _ => rfl)
  have hqV : ∀ (k : ℕ) (p : Fin (n + 1)) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖Probability.stopped (σ (k + 1))
              (fun ω s => coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s
            - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V' s ω + c' k ω) * H' p j ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ := fun k p j =>
    energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmVun k p j) (hqVun k p j)
  have hX₀ : ∀ p : Fin (n + 1), Measurable[S.ℱ 0] fun ω => timeAugInit (fun _ : Ω => x₀) ω p :=
    fun p => measurable_const
  have hcont := fun k : ℕ => itoFormula_between_measurableShift W S.ℱ S.isBrownian hV' hℱ0
    hnull0 hX₀ hb'm hb'p hb'q (hσ k) (hσ (k + 1)) (hmono k) (hσ0 k) (hσ0 (k + 1)) hfC hf hf'
    hK₁' hK₂' hT (hc' k) (hmV k) (hpV k) (hqV k)
  have hchain := fun m : ℕ => itoFormula_chain W S.ℱ S.isBrownian hσ hmono hmG hpG hqG hmD hqD
    hmQ hmV hpV hqV hT hQint (m := m) h0 hshift (fun k _ => hcont k)
  -- ## The four analytic identifications
  have hBro : ∀ᵐ ω ∂P, (∑ p : Fin (n + 1), ∑ j : Fin d,
        stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => coordDeriv f' p (Y' s ω) * H' p j ω s) (hmG p j) (hpG p j) (hqG p j) T ω)
      = MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
          (fun s ω => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω)) hBm hBp hBq T ω := by
    have hrow : ∀ j : Fin d, (fun ω s => ∑ p : Fin (n + 1), coordDeriv f' p (Y' s ω) * H' p j ω s)
        = fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j := by
      intro j
      funext ω s
      rw [Fin.sum_univ_succ]
      simp only [H', timeAugDiffusion, Fin.cons_zero, Fin.cons_succ, mul_zero, zero_add,
        mixedDiffusionIntegrand, Y', timeAugProcess, H]
      exact Finset.sum_congr rfl fun i _ => by
        rw [coordDeriv_succ_cons_eq_gradient hfu hf]
    have hj : ∀ j : Fin d, (fun ω => ∑ p : Fin (n + 1),
        stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => coordDeriv f' p (Y' s ω) * H' p j ω s) (hmG p j) (hpG p j) (hqG p j) T ω)
        =ᵐ[P] stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
          (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j)
          (hBm j) (hBp j) (hBq j) T := by
      intro j
      have hms : Measurable (Function.uncurry
          fun ω s => ∑ p : Fin (n + 1), coordDeriv f' p (Y' s ω) * H' p j ω s) := by
        rw [hrow j]; exact hBm j
      have hps : Probability.ProgressivelyMeasurable S.ℱ
          fun ω s => ∑ p : Fin (n + 1), coordDeriv f' p (Y' s ω) * H' p j ω s := by
        rw [hrow j]; exact hBp j
      have hqs : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖∑ p : Fin (n + 1), coordDeriv f' p (Y' s ω) * H' p j ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤ := by
        intro T' hT'
        have hrow' : ∀ ω s, (∑ p : Fin (n + 1), coordDeriv f' p (Y' s ω) * H' p j ω s)
            = mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω) j :=
          fun ω s => congrFun (congrFun (hrow j) ω) s
        simp only [hrow']
        exact hBq j T' hT'
      filter_upwards [stochasticIntegralBrownian_sum_univ (W.W j) S.ℱ (S.isBrownian j) hT
        (fun p ω s => coordDeriv f' p (Y' s ω) * H' p j ω s) (fun p => hmG p j)
        (fun p => hpG p j) (fun p => hqG p j) hms hps hqs] with ω hω
      rw [← hω, stochasticIntegralBrownian_congr_fun (W.W j) S.ℱ (S.isBrownian j) (hrow j) hms
        hps hqs (hBm j) (hBp j) (hBq j) T]
    filter_upwards [MeasureTheory.ae_all_iff.mpr hj] with ω hω
    rw [multidimStochasticIntegral_eq_sum, Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hω j
  set φm : Ω → ℝ → E → ℝ := fun ω s e =>
    mixedJumpIncrement u coeffs.γ s (leftLimPathAt y s ω) (leftLimPathAt X.X s ω) e with hφmdef
  have hCmp : ∀ᵐ ω ∂P, stochasticIntegral N S.ℱ S.isPoisson
        (markCut B fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
        hCm hCp hCq T ω
      = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ B, markCut B φm ω q.1 q.2 ∂(N.N ω))
        - ∫ s in Set.Icc (0 : ℝ) T, ∫ e in B,
            mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e ∂ν := by
    have hK₁'' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
      fun s x i => (hK₁ s x i).trans (le_max_left _ _)
    have hK₁0' : (0 : ℝ) ≤ max K₁ 0 := le_max_right _ _
    -- admissibility of the mixed jump increment read at the left limits
    have hyLm : Measurable fun q : ℝ × Ω => leftLimPathAt y q.1 q.2 :=
      measurable_uncurry_leftLimPathAt hy_m hy_left
    have hXLm : Measurable fun q : ℝ × Ω => leftLimPathAt X.X q.1 q.2 :=
      measurable_uncurry_leftLimPathAt hXm hXleft
    have hφmm : Measurable fun p : Ω × ℝ × E => φm p.1 p.2.1 p.2.2 := by
      have hy : Measurable fun p : Ω × ℝ × E => leftLimPathAt y p.2.1 p.1 :=
        hyLm.comp (measurable_snd.fst.prodMk measurable_fst)
      have hγ : Measurable fun p : Ω × ℝ × E =>
          coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 :=
        measurable_pi_lambda _ fun i => hγmL i
      exact (hu.continuous.measurable.comp (measurable_snd.fst.prodMk (hy.add hγ))).sub
        (hu.continuous.measurable.comp (measurable_snd.fst.prodMk hy))
    have hφmp : Probability.MarkedProgressivelyMeasurable S.ℱ φm := by
      have hZ := markedProgressivelyMeasurable_time_state_jump (ℱ := S.ℱ) (coeffs := coeffs)
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
    have hφmq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖φm ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun T' hT' =>
      lintegral_window_mark_sq_le_of_abs_le
        (a := fun i ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i) (c := n * max K₁ 0) hγmL
        (fun ω s e => abs_mixedJumpIncrement_le hu hK₁'' hK₁0' s _ _ e) T'
        (fun i => hγqL i T' hT')
    have hCmm : Measurable fun p : Ω × ℝ × E => markCut B φm p.1 p.2.1 p.2.2 :=
      measurable_markCut hφmm hB
    have hCmp' : Probability.MarkedProgressivelyMeasurable S.ℱ (markCut B φm) :=
      hφmp.indicator_mark hB
    have hCmq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖markCut B φm ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
      fun T' hT' => sq_markCut hφmq B T' hT'
    -- the point-evaluated and the left-limit integrands have the same compensated integral
    have hcount : ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧
        ((leftLimPathAt y s ω, leftLimPathAt X.X s ω) : (Fin n → ℝ) × (Fin n → ℝ))
          ≠ (y s ω, X.X s ω)}.Countable := by
      filter_upwards [X.cadlag_paths] with ω hcad
      exact countable_setOf_pos_ne_pair (Y₁ := leftLimPathAt y) (Z₁ := y)
        (Y₂ := leftLimPathAt X.X) (Z₂ := X.X)
        (countable_setOf_pos_leftLimPathAt_ne (fun t _ => hy_rc ω t) (fun t _ i => hy_left ω t i))
        (countable_setOf_pos_leftLimPathAt_ne (fun t ht => (hcad t ht).1)
          (fun t ht i => (hcad t ht.le).2 i))
    have hcongr : stochasticIntegral N S.ℱ S.isPoisson (markCut B φm) hCmm hCmp' hCmq T
        =ᵐ[P] stochasticIntegral N S.ℱ S.isPoisson
          (markCut B fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
          hCm hCp hCq T :=
      LevyStochCalc.Ito.compensatedIntegral_congr_of_countable_ne N S.isPoisson
        (X := fun s ω => ((y s ω, X.X s ω) : (Fin n → ℝ) × (Fin n → ℝ)))
        (Xm := fun s ω => ((leftLimPathAt y s ω, leftLimPathAt X.X s ω) :
          (Fin n → ℝ) × (Fin n → ℝ)))
        (fun s v e => B.indicator (fun _ => mixedJumpIncrement u coeffs.γ s v.1 v.2 e) e)
        hcount hCmm hCm hCmp' hCp hCmq hCq hT
    -- the zero extension of the left-limit integrand is predictable
    have hpred : MarkedPredictable S.ℱ ν (zeroExtPos φm) := by
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
      by_cases hs : (0 : ℝ) < s <;> simp [zeroExtPos, hs, φm, mixedJumpIncrement, leftLimPathAtPos]
    have hpredM : MarkedPredictable S.ℱ ν (zeroExtPos (markCut B φm)) :=
      markedPredictable_zeroExtPos_markCut hpred hB
    have hpath := stochasticIntegral_ae_eq_pathwise_of_zeroExtPos N S.ℱ S.isPoisson (markCut B φm)
      hCmm hCmp' hCmq hB hpredM hBν (fun ω s e he => Set.indicator_of_notMem he _) hT
    -- the left-limit integrand is integrable on the window against the reference intensity
    have hen : ∫⁻ ω, ∫⁻ q in Set.Ioc (0 : ℝ) T ×ˢ B,
        ‖φm ω q.1 q.2‖ₑ ^ 2 ∂(LevyStochCalc.Poisson.referenceIntensity ν) ∂P ≠ ⊤ := by
      refine ne_top_of_le_ne_top (hφmq T hT).ne (lintegral_mono fun ω => ?_)
      rw [LevyStochCalc.Poisson.lintegral_referenceIntensity_window
        (f := fun q : ℝ × E => ‖φm ω q.1 q.2‖ₑ ^ 2) ((hφmm.comp
          (by fun_prop :
            Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))).enorm.pow_const 2) B T]
      refine (lintegral_mono_set Set.Ioc_subset_Icc_self).trans (lintegral_mono fun s => ?_)
      exact lintegral_mono' Measure.restrict_le_self fun e => le_rfl
    have hwin := ae_integrableOn_window_of_zeroExtPos N S.isPoisson hB hBν T hpred hφmm hen
    filter_upwards [hcongr, hpath, hwin, hcount] with ω h1 h2 h3 h4
    rw [← h1, h2]
    congr 1
    have hmc : Set.EqOn (fun q : ℝ × E => markCut B φm ω q.1 q.2) (fun q => φm ω q.1 q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ B) := fun q hq => Set.indicator_of_mem hq.2 _
    rw [setIntegral_congr_fun (measurableSet_Ioc.prod hB) hmc,
      (integral_window_eq_and_integrableOn (fun s e => φm ω s e) h3.2).1]
    exact LevyStochCalc.Ito.setIntegral_congr_of_countable_ne
      (X := fun s ω => ((y s ω, X.X s ω) : (Fin n → ℝ) × (Fin n → ℝ)))
      (Xm := fun s ω => ((leftLimPathAt y s ω, leftLimPathAt X.X s ω) :
        (Fin n → ℝ) × (Fin n → ℝ)))
      (fun s v e => mixedJumpIncrement u coeffs.γ s v.1 v.2 e) (ν.restrict B) h4 T
  have hdict : ∀ᵐ ω ∂P, (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (Y' s ω) * b' p ω s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (Y' s ω) * (∑ j : Fin d, H' p j ω s * H' q j ω s) ∂volume
      = ∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s ω) (X.X s ω)
          - ∑ i : Fin n, gradient u s (y s ω) i * ∫ e in B, coeffs.γ s (X.X s ω) e i ∂ν) := by
    have hDint : ∀ᵐ ω ∂P, ∀ p : Fin (n + 1), IntegrableOn
        (fun s => coordDeriv f' p (Y' s ω) * b' p ω s) (Set.Ioc (0 : ℝ) T) volume :=
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
        coordDeriv f' p (Y' s ω) * b' p ω s = coordDeriv f' p (Y' s ω) * bpt p s := by
      intro p
      induction p using Fin.cases with
      | zero => exact Filter.Eventually.of_forall fun s => rfl
      | succ q =>
        filter_upwards [hae] with s hs
        simp only [b', bpt, timeAugDrift, Fin.cons_succ, bdr, continuousDriftLeftAt, hs]
    have hD' : ∀ p : Fin (n + 1), IntegrableOn
        (fun s => coordDeriv f' p (Y' s ω) * bpt p s) (Set.Ioc (0 : ℝ) T) volume :=
      fun p => (hDω p).congr_fun_ae (hbeq p)
    have hdrift_eq : ∀ p : Fin (n + 1), (∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (Y' s ω) * b' p ω s ∂volume)
        = ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (Y' s ω) * bpt p s ∂volume :=
      fun p => integral_congr_ae (hbeq p)
    rw [Finset.sum_congr rfl fun p _ => hdrift_eq p, setIntegral_Icc_eq_setIntegral_Ioc]
    exact setIntegral_splitDrift_dictionary_mixed hfu hf hf' coeffs B T (fun s => y s ω)
      (fun s => X.X s ω) bpt (fun p j s => H' p j ω s) (fun s => rfl) (fun q s => rfl)
      (fun j s => rfl) (fun p j s => rfl) hD' hQω
  have hint : ∀ᵐ ω ∂P,
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
  -- ## Assembly
  filter_upwards [MeasureTheory.ae_all_iff.mpr hchain,
    LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N B hB hBν T,
    LevyStochCalc.Poisson.ae_jumpTime_lt_jumpTime_succ N B hB hBν T,
    ae_exists_le_jumpTime N B hB hBν T, hshift, hceq, hBro, hCmp, hdict, hint]
    with ω hchainω hatomω hstrictω hm'ω hshiftω hceqω hBroω hCmpω hdictω hintω
  obtain ⟨m, hm⟩ := hm'ω
  obtain ⟨K, θ, ε, hmonoθ, hrange, hmem, hsum⟩ := hatomω
  have hm' : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N B m ω := hm
  have hchainm := hchainω m ((le_cappedJumpTime_iff N B T m ω).mpr hm')
  -- the endpoints
  have hend1 : f (V' T ω + c' m ω) = u T (y T ω) := by
    have hσm : σ m ω = ((T : ℝ) : WithTop ℝ) := min_eq_right hm'
    have hunt : (σ m ω).untopA = T := by rw [hσm]; rfl
    simp only [V', c', c, hunt, timeAugProcess, hfdef]
    rw [timeAugFun_cons_add_cons_zero, add_sub_cancel]
  have hend0 : f (V' 0 ω + c' 0 ω) = u 0 (y 0 ω) := by
    have hσ00 : σ 0 ω = ((0 : ℝ) : WithTop ℝ) := h0 ω
    have hunt : (σ 0 ω).untopA = 0 := by rw [hσ00]; rfl
    simp only [V', c', c, hunt, timeAugProcess, hfdef]
    rw [timeAugFun_cons_add_cons_zero, add_sub_cancel]
  -- the jump telescope against the atoms
  have hjump : (∑ k ∈ Finset.range m, (f (V' (clipTime (σ (k + 1)) T ω) ω + c' (k + 1) ω)
        - f (V' (clipTime (σ (k + 1)) T ω) ω + c' k ω)))
      = ∑ j : Fin K, markCut B φm ω (θ j) (ε j) := by
    rw [sum_range_jumpTerm_eq_sum_atomEnum_of_shift (A := B) f (V := V') (Y := Y') (c := c')
      (jump := fun j => Fin.cons 0 (coeffs.γ (θ j) (leftLimPath X (θ j) ω) (ε j)))
      hmonoθ (fun j => (hmem j).1) hrange (hV'.continuous_path ω) hstrictω
      (fun k s h1 h2 => hshiftω k s h1 h2) ?_ ?_ hm']
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [leftLim_timeAugProcess_eq_cons y (fun i => hy_left ω (θ j) i)]
      simp only [hfdef, markCut_apply, Set.indicator_of_mem (hmem j).2, φm,
        mixedJumpIncrement]
      rw [timeAugFun_cons_add_cons_zero, timeAugFun_cons]
      rfl
    · intro k hk
      simp only [c']
      rw [hceqω, hceqω,
        cappedJumpSumAt_succ_eq_of_horizon_lt X (leftLimPath X) hB hmem hsum hrange hk]
    · intro k hk
      obtain ⟨j, hj, hinc⟩ := cappedJumpSumAt_succ_eq_add_gamma X (leftLimPath X) hB hmem hsum
        hmonoθ.injective hrange (hstrictω k hk) hk
      refine ⟨j, hj, ?_⟩
      simp only [c']
      rw [hceqω, hceqω, hinc, cons_add_cons_zero]
  have hjump' : (∑ j : Fin K, markCut B φm ω (θ j) (ε j))
      = stochasticIntegral N S.ℱ S.isPoisson
          (markCut B fun ω s e => mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e)
          hCm hCp hCq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in B,
            mixedJumpIncrement u coeffs.γ s (y s ω) (X.X s ω) e ∂ν := by
    rw [hCmpω, ← hsum (fun q => markCut B φm ω q.1 q.2)]
    ring
  rw [hend1, hend0, hjump] at hchainm
  obtain ⟨hγi, hΔi, hΔt, hgt, hdt⟩ := hintω
  have hkey := itoLevy_of_splitDrift_and_jumpSum_mixed_ae (u := u) (coeffs := coeffs) (ν := ν)
    (A := B) (y := fun s => y s ω) (x := fun s => X.X s ω) (T := T)
    (Dm := MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
      (fun s ω => mixedDiffusionIntegrand u coeffs.σ s (y s ω) (X.X s ω)) hBm hBp hBq T ω)
    hγi hΔi hΔt hgt hdt (by linarith [hchainm, hdictω, hBroω]) hjump'
  beta_reduce at hkey
  linarith

end Main

end LevyStochCalc.Ito.JumpFormula
