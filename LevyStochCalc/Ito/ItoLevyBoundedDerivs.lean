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
import LevyStochCalc.Ito.FiniteActivityMixed
import LevyStochCalc.Ito.ItoLevyBoundedDerivsSteps
import LevyStochCalc.Probability.MarkedProgressiveSlice

/-!
# The Itô–Lévy formula for a jump diffusion at bounded derivatives

The Itô–Lévy identity for a `C²` function of time and state whose time derivative, gradient and
Hessian are bounded, along a jump diffusion, with every stochastic integral taken over the one
filtration carried by the SDE data of the solution. The proof is the small-jump truncation: the
big-jump paths at the complements of a spanning family of the intensity are repaired to be
càdlàg at every sample point, the mixed integrands — derivatives of the state function along the
truncated path, coefficients along the solution — are integrated over the right-continuous
filtration, where the truncated paths are adapted, and the four terms are passed to the limit
along one composite subsequence; the two stochastic limits are then transported back to the
filtration of the SDE data.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.truncPath` — the big-jump path at the `m`-th small-mark set,
  restricted to a set of sample points and frozen at zero before time zero.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_of_boundedDerivs` — the canonical
  residual is the compensated jump integral plus the compensator-drift integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section TruncPath

open LevyStochCalc.Ito.BigJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- The big-jump path at the `m`-th small-mark set, restricted to a set of sample points and
frozen at zero before time zero. -/
noncomputable def truncPath (S : SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (G : Set Ω) (m : ℕ) (s : ℝ) (ω : Ω) : Fin n → ℝ :=
  (Set.Ici (0 : ℝ)).indicator
    (fun r => repairOn G (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0) r ω) s

variable (S : SdeData X)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
  (G : Set Ω)

theorem truncPath_of_nonneg (m : ℕ) {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    truncPath S hℱ0 hnull0 G m s ω
      = repairOn G (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0) s ω :=
  Set.indicator_of_mem (Set.mem_Ici.mpr hs) _

theorem truncPath_of_neg (m : ℕ) {s : ℝ} (hs : s < 0) (ω : Ω) :
    truncPath S hℱ0 hnull0 G m s ω = 0 :=
  Set.indicator_of_notMem (fun h => absurd (Set.mem_Ici.mp h) (not_le.mpr hs)) _

/-- On the good set and at nonnegative times the truncated path is the big-jump process. -/
theorem truncPath_eq_of_mem (m : ℕ) {s : ℝ} (hs : 0 ≤ s) {ω : Ω} (hω : ω ∈ G) :
    truncPath S hℱ0 hnull0 G m s ω
      = SmallJump.bigJumpProcess S.toJumpIntegrand (measurableSet_smallMarks ν) hℱ0 hnull0
          m s ω := by
  rw [truncPath_of_nonneg S hℱ0 hnull0 G m hs, repairOn_of_mem hω]
  rfl

/-- The truncated path is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_truncPath (hGm : MeasurableSet G) (m : ℕ) :
    Measurable (Function.uncurry (truncPath S hℱ0 hnull0 G m)) := by
  have hrep := measurable_uncurry_repairOn hGm
    (measurable_uncurry_bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0)
  have heq : Function.uncurry (truncPath S hℱ0 hnull0 G m)
      = {q : ℝ × Ω | 0 ≤ q.1}.indicator (Function.uncurry
          (repairOn G (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0))) := by
    funext q
    by_cases hq : 0 ≤ q.1
    · change truncPath S hℱ0 hnull0 G m q.1 q.2 = _
      rw [truncPath_of_nonneg S hℱ0 hnull0 G m hq,
        Set.indicator_of_mem (show q ∈ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
      rfl
    · change truncPath S hℱ0 hnull0 G m q.1 q.2 = _
      rw [truncPath_of_neg S hℱ0 hnull0 G m (not_le.mp hq),
        Set.indicator_of_notMem (show q ∉ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
  rw [heq]
  exact hrep.indicator (measurableSet_le measurable_const measurable_fst)

/-- Every path of the truncated path is right-continuous, when the big-jump paths are càdlàg on
the good set. -/
theorem truncPath_rightContinuous
    (hGp : ∀ ω ∈ G, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω) (𝓝[>] t)
          (𝓝 (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
          Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω i)
            (𝓝[<] t) (𝓝 L))
    (m : ℕ) (ω : Ω) (t : ℝ) :
    Tendsto (fun s => truncPath S hℱ0 hnull0 G m s ω) (𝓝[>] t)
      (𝓝 (truncPath S hℱ0 hnull0 G m t ω)) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [truncPath_of_neg S hℱ0 hnull0 G m ht]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
    exact (truncPath_of_neg S hℱ0 hnull0 G m (Set.mem_Iio.mp hs) ω).symm
  · rw [truncPath_of_nonneg S hℱ0 hnull0 G m ht]
    have hrep := (repairOn_cadlag (fun ω hω t ht => hGp ω hω m t ht) ω t ht).1
    refine hrep.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (truncPath_of_nonneg S hℱ0 hnull0 G m (ht.trans (le_of_lt (Set.mem_Ioi.mp hs)))
      ω).symm

/-- Every coordinate of every path of the truncated path has a left limit at every time, when
the big-jump paths are càdlàg on the good set. -/
theorem truncPath_leftLim
    (hGp : ∀ ω ∈ G, ∀ m : ℕ, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω) (𝓝[>] t)
          (𝓝 (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ,
          Tendsto (fun s => bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 s ω i)
            (𝓝[<] t) (𝓝 L))
    (m : ℕ) (ω : Ω) (t : ℝ) (i : Fin n) :
    ∃ L : ℝ, Tendsto (fun s => truncPath S hℱ0 hnull0 G m s ω i) (𝓝[<] t) (𝓝 L) := by
  rcases le_or_gt t 0 with ht | ht
  · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [truncPath_of_neg S hℱ0 hnull0 G m (lt_of_lt_of_le (Set.mem_Iio.mp hs) ht)]
    rfl
  · obtain ⟨L, hL⟩ := (repairOn_cadlag (fun ω hω t ht => hGp ω hω m t ht) ω t ht.le).2 i
    refine ⟨L, hL.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    rw [truncPath_of_nonneg S hℱ0 hnull0 G m hs.1.le]

/-- The truncated path is adapted to the right-continuous filtration of the SDE data, when the
good set belongs to it at every nonnegative time. -/
theorem measurable_rightCont_truncPath (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    (hG : ∀ t : ℝ, 0 ≤ t → MeasurableSet[S.ℱ.rightCont t] G) (m : ℕ) (t : ℝ) :
    Measurable[S.ℱ.rightCont t] (truncPath S hℱ0 hnull0 G m t) := by
  classical
  rcases lt_or_ge t 0 with ht | ht
  · have hz : truncPath S hℱ0 hnull0 G m t = fun _ => 0 :=
      funext fun ω => truncPath_of_neg S hℱ0 hnull0 G m ht ω
    rw [hz]
    exact measurable_const
  · have hite : truncPath S hℱ0 hnull0 G m t = fun ω =>
        if ω ∈ G then bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t ω else 0 := by
      funext ω
      rw [truncPath_of_nonneg S hℱ0 hnull0 G m ht]
      by_cases hω : ω ∈ G <;> simp [repairOn, hω]
    rw [hite]
    -- The two ingredients, elaborated against the ambient measurable space before the
    -- filtration at `t` is installed as the ambient one.
    have hXm : Measurable[S.ℱ.rightCont t] (X.X t) :=
      (hXadapt t).mono (S.ℱ.le_rightCont t) le_rfl
    have hcut : ∀ i : Fin n, Measurable[S.ℱ.rightCont t]
        (cutJumpIntegral S (measurableSet_smallMarks ν m) hℱ0 hnull0 i t) := fun i =>
      adapted_cutJumpIntegral S (measurableSet_smallMarks ν m) hℱ0 hnull0 i t
    have hGt : MeasurableSet[S.ℱ.rightCont t] G := hG t ht
    have hbig : Measurable[S.ℱ.rightCont t]
        (bigJumpPath S (measurableSet_smallMarks ν m) hℱ0 hnull0 t) := by
      letI : MeasurableSpace Ω := S.ℱ.rightCont t
      exact measurable_pi_lambda _ fun i => ((measurable_pi_apply i).comp hXm).sub (hcut i)
    exact Measurable.ite hGt hbig measurable_const

end TruncPath

section Main

open LevyStochCalc.Ito.BigJump LevyStochCalc.Brownian.Multidim LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

open LevyStochCalc.Ito.IntegralLimit in
/-- **The Itô–Lévy formula at bounded derivatives.** For a jump diffusion with SDE data `S`
whose right-continuous filtration satisfies the usual conditions at time zero, whose path has
left limits at every time and whose drift along the path is progressively measurable, and a
`C²` state function with bounded time derivative, gradient and Hessian, the canonical residual
of the Itô–Lévy formula is the compensated jump integral plus the compensator-drift integral,
every stochastic integral being taken over the filtration of `S`.

The admissibility of the derived integrands `(∇u)ᵀσ` and `u(x + γ) − u(x)` along the solution
is still taken as a hypothesis; deriving it from the bounded derivatives and the SDE data is a
later lemma. -/
theorem itoLevyFormula_jumpResidual_of_boundedDerivs
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    -- Correction 8 (one filtration): the SDE data of `X`, with the usual-conditions shape at
    -- time zero that the truncated paths need.
    (S : LevyStochCalc.Ito.BigJump.SdeData X)
    -- Correction 8 (usual conditions): the filtration of the SDE data is right continuous, so
    -- its right continuation is itself and the two shapes of `hℱ0` are the same statement.
    [S.ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    -- (3) The structure calls its solution adapted but carries no such field.
    (hXadapt : ∀ t : ℝ, Measurable[S.ℱ t] (X.X t))
    -- (3') Statement change: `cadlag_paths` holds almost surely and only on `[0, ∞)`, while the
    -- left limits along which the jump coefficient is read must exist at every sample point and
    -- every time for that reading to be a process at all.
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    -- (5) The drift along the path.
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    -- (5') Statement change: `SdeData` carries no drift field, and progressive measurability of
    -- the drift along the path does not follow from its joint measurability.
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- (6) Joint measurability of the jump coefficient.
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    -- The bounded derivatives, coordinatewise.
    {K₀ K₁ K₂ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T)
    (_h_μ_int : ∀ᵐ ω ∂P, ∀ i : Fin n,
        IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) T))
    (h_sigmaGrad_meas : ∀ j : Fin d,
        Measurable (Function.uncurry
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)))
    (h_sigmaGrad_progMeas : ∀ j : Fin d,
        Probability.ProgressivelyMeasurable S.ℱ
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤)
    (h_jumpInt_meas : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_progMeas :
        Probability.MarkedProgressivelyMeasurable S.ℱ
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω')))
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (_h_compDrift_int : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W S.ℱ S.isBrownian
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω)
        =
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N S.ℱ S.isPoisson
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω'))
            h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  -- The mark sets of the truncation and the right-continuous filtration of the SDE data.
  have hA : ∀ m : ℕ, MeasurableSet (smallMarks ν m) := measurableSet_smallMarks ν
  have hanti : Antitone (smallMarks ν) := antitone_smallMarks ν
  have hnull : ν (⋂ m, smallMarks ν m) = 0 := measure_iInter_smallMarks ν
  have hle : ∀ t, S.ℱ t ≤ S.ℱ.rightCont t := fun t => S.ℱ.le_rightCont t
  have h𝒢W : ∀ j : Fin d,
      LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) S.ℱ.rightCont :=
    fun j => (S.isBrownian j).rightCont
  have h𝒢N : LevyStochCalc.Poisson.IsPoissonFiltration N S.ℱ.rightCont :=
    S.isPoisson.rightCont
  -- Nonnegative versions of the derivative bounds.
  have hK₀' : ∀ s x, |timeDeriv u s x| ≤ max K₀ 0 :=
    fun s x => (hK₀ s x).trans (le_max_left _ _)
  have hK₁' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  have hK₂' : ∀ s x i j, |hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  have hK₁0 : (0 : ℝ) ≤ max K₁ 0 := le_max_right _ _
  have hK₂0 : (0 : ℝ) ≤ max K₂ 0 := le_max_right _ _
  -- Steps 1–2: the good set, on which every big-jump path is càdlàg, and the truncated paths.
  obtain ⟨G, hGm, hG0, hGp⟩ := exists_measurable_full_of_ae (P := P)
    (MeasureTheory.ae_all_iff.mpr fun m : ℕ => bigJumpPath_ae_cadlag S (hA m) hℱ0 hnull0)
  have hGae : ∀ᵐ ω ∂P, ω ∈ G := mem_ae_iff.mpr hG0
  have hGF : ∀ t : ℝ, 0 ≤ t → MeasurableSet[S.ℱ.rightCont t] G := by
    intro t ht
    have h0 : MeasurableSet[S.ℱ 0] G := by simpa using (hnull0 Gᶜ hGm.compl hG0).compl
    exact S.ℱ.rightCont.mono ht _ (S.ℱ.le_rightCont 0 _ h0)
  set xs : ℕ → ℝ → Ω → (Fin n → ℝ) := fun m => truncPath S hℱ0 hnull0 G m with hxs_def
  have hxs_eq : ∀ m, ∀ ω ∈ G, ∀ s : ℝ, 0 ≤ s →
      xs m s ω = SmallJump.bigJumpProcess S.toJumpIntegrand hA hℱ0 hnull0 m s ω :=
    fun m ω hω s hs => truncPath_eq_of_mem S hℱ0 hnull0 G m hs hω
  have hxs_m : ∀ m, Measurable (Function.uncurry (xs m)) :=
    fun m => measurable_uncurry_truncPath S hℱ0 hnull0 G hGm m
  have hxs_rc : ∀ m ω t, Tendsto (fun s => xs m s ω) (𝓝[>] t) (𝓝 (xs m t ω)) :=
    fun m ω t => truncPath_rightContinuous S hℱ0 hnull0 G
      (fun ω hω m t ht => hGp ω hω m t ht) m ω t
  have hxs_ad : ∀ m t, Measurable[S.ℱ.rightCont t] (xs m t) :=
    fun m t => measurable_rightCont_truncPath S hℱ0 hnull0 G hXadapt hGF m t
  have hxs_prog : ∀ m i,
      Probability.ProgressivelyMeasurable S.ℱ.rightCont fun ω s => xs m s ω i :=
    fun m i => progressivelyMeasurable_of_rightContinuous (X := fun s ω => xs m s ω i)
      (fun t => (measurable_pi_apply i).comp (hxs_ad m t))
      (fun ω t => ((continuous_apply i).tendsto _).comp (hxs_rc m ω t))
  -- Step 3: the mixed integrands along the truncated paths, and their admissibility over the
  -- right-continuous filtration.
  have hBm : ∀ m (j : Fin d), Measurable (Function.uncurry
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω) j) :=
    fun m j => measurable_uncurry_mixedDiffusionIntegrand S hu (xs m) (hxs_m m) j
  have hBp : ∀ m (j : Fin d), Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω) j :=
    fun m j => progressivelyMeasurable_mixedDiffusionIntegrand S hu (xs m) (hxs_ad m)
      (hxs_rc m) j
  have hBq : ∀ m (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ :=
    fun m j T' hT' =>
      lintegral_window_sq_mixedDiffusionIntegrand_lt_top S hK₁' (xs m) j T' hT'
  have hΦm : ∀ m, Measurable fun p : Ω × ℝ × E =>
      mixedJumpIncrement u coeffs.γ p.2.1 (xs m p.2.1 p.1) (X.X p.2.1 p.1) p.2.2 :=
    fun m => measurable_mixedJumpIncrement S hu (xs m) (hxs_m m)
  have hΦp : ∀ m, Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont
      fun ω s e => mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e :=
    fun m => markedProgressivelyMeasurable_mixedJumpIncrement S hu (xs m) (hxs_prog m)
  have hΦq : ∀ m (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ :=
    fun m T' hT' =>
      lintegral_window_mark_sq_mixedJumpIncrement_lt_top S hu hK₁' hK₁0 (xs m) T' hT'
  have hCm : ∀ m, Measurable fun p : Ω × ℝ × E => markCut (smallMarks ν m)ᶜ
      (fun ω s e => mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e) p.1 p.2.1 p.2.2 :=
    fun m => measurable_markCut (hΦm m) (hA m).compl
  have hCp : ∀ m, Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont (markCut
      (smallMarks ν m)ᶜ fun ω s e => mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e) :=
    fun m => (hΦp m).indicator_mark (hA m).compl
  have hCq : ∀ m (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖markCut (smallMarks ν m)ᶜ
        (fun ω s e => mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e) ω s e‖₊ :
          ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun m T' hT' => sq_markCut (hΦq m) (smallMarks ν m)ᶜ T' hT'
  -- The four term families along the truncated paths.
  set Dr : ℕ → Ω → ℝ := fun m ω => ∫ s in Set.Icc (0 : ℝ) T,
    mixedDriftIntegrand u coeffs s (xs m s ω) (X.X s ω) with hDr_def
  set Cd : ℕ → Ω → ℝ := fun m ω => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (smallMarks ν m)ᶜ,
    mixedCompensatorDriftIntegrand u coeffs.γ s (xs m s ω) (X.X s ω) e ∂ν with hCd_def
  set Bro : ℕ → Ω → ℝ := fun m => MultidimBrownianMotion.stochasticIntegral W S.ℱ.rightCont h𝒢W
    (fun s ω => mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω))
    (hBm m) (hBp m) (hBq m) T with hBro_def
  set Cmp : ℕ → Ω → ℝ := fun m => stochasticIntegral N S.ℱ.rightCont h𝒢N (markCut
    (smallMarks ν m)ᶜ fun ω s e => mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e)
    (hCm m) (hCp m) (hCq m) T with hCmp_def
  -- The limit integrands over the right-continuous filtration, and their transport back.
  have hBp𝒢 : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ.rightCont
      fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j :=
    fun j => (h_sigmaGrad_progMeas j).mono hle
  have hCp𝒢 : Probability.MarkedProgressivelyMeasurable S.ℱ.rightCont
      (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω')) :=
    h_jumpInt_progMeas.mono hle
  have hB_eq := multidimStochasticIntegral_rightCont_ae_eq S h𝒢W
    (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω)) h_sigmaGrad_meas
    h_sigmaGrad_progMeas hBp𝒢 h_sigmaGrad_sq T
  have hC_eq := compensatedStochasticIntegral_rightCont_ae_eq S h𝒢N
    (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
    h_jumpInt_meas h_jumpInt_progMeas hCp𝒢 h_jumpInt_sq T
  -- Step 4: the path limit at almost every time along `ms`, the `L²` limits of the endpoint and
  -- of the two stochastic terms along `ms`, and one common subsequence `k`.
  obtain ⟨ms, hms, hpath⟩ := SmallJump.exists_seq_ae_ae_tendsto_bigJumpProcess_pi
    S.toJumpIntegrand hA hℱ0 hnull0 hanti hnull hT
  have hpath' : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => xs (ms k) s ω) atTop (𝓝 (X.X s ω)) := by
    filter_upwards [hpath, hGae] with ω hω hωG
    filter_upwards [hω, ae_restrict_mem measurableSet_Icc] with s hs hsI
    exact hs.congr fun k => (hxs_eq (ms k) ω hωG s hsI.1).symm
  have hendL2 : ∀ i : Fin n, Tendsto
      (fun k => ∫⁻ ω, (‖xs (ms k) T ω i - X.X T ω i‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) := by
    intro i
    have h := (SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub S.toJumpIntegrand hA hℱ0
      hnull0 hanti hnull i hT.le).comp (tendsto_atTop_of_le hms)
    refine h.congr fun k => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hGae] with ω hω
    rw [hxs_eq (ms k) ω hω T hT.le]
  have hbroL2 := tendsto_lintegral_sq_mixedDiffusionIntegral_sub S h𝒢W hu hK₁' hK₁0
    (fun k => xs (ms k)) (fun k => hBm (ms k)) (fun k => hBp (ms k)) (fun k => hBq (ms k))
    h_sigmaGrad_meas hBp𝒢 h_sigmaGrad_sq T hT hpath'
  have hcmpL2 := tendsto_lintegral_sq_mixedCompensatedIntegral_sub S h𝒢N hu hK₁' hK₁0
    (fun k => xs (ms k)) ms hms (fun k => hCm (ms k)) (fun k => hCp (ms k))
    (fun k => hCq (ms k)) h_jumpInt_meas hCp𝒢 h_jumpInt_sq T hT hpath'
  have hUm := fun l => measurable_sumElim_mixedTerms S h𝒢W h𝒢N (xs (ms l)) (hxs_m (ms l))
    ((smallMarks ν (ms l))ᶜ) (hBm (ms l)) (hBp (ms l)) (hBq (ms l)) (hCm (ms l))
    (hCp (ms l)) (hCq (ms l)) T
  have hVm := measurable_sumElim_solutionTerms S h𝒢W h𝒢N h_sigmaGrad_meas hBp𝒢
    h_sigmaGrad_sq h_jumpInt_meas hCp𝒢 h_jumpInt_sq T
  have hL2 : ∀ c : Fin n ⊕ Fin d ⊕ Unit, Tendsto (fun l : ℕ => ∫⁻ ω,
      (‖Sum.elim (fun i ω => xs (ms l) T ω i) (Sum.elim
            (fun j ω => stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
              (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (xs (ms l) s ω) (X.X s ω) j)
              (hBm (ms l) j) (hBp (ms l) j) (hBq (ms l) j) T ω)
            (fun _ ω => Cmp (ms l) ω)) c ω
          - Sum.elim (fun i ω => X.X T ω i) (Sum.elim
            (fun j ω => stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
              (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)
              (h_sigmaGrad_meas j) (hBp𝒢 j) (h_sigmaGrad_sq j) T ω)
            (fun _ ω => stochasticIntegral N S.ℱ.rightCont h𝒢N
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              h_jumpInt_meas hCp𝒢 h_jumpInt_sq T ω)) c ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
    rintro (i | j | _)
    · exact hendL2 i
    · exact hbroL2 j
    · exact hcmpL2
  obtain ⟨k, hk, hlim⟩ := exists_seq_ae_tendsto_of_tendsto_lintegral hUm hVm hL2
  -- The composite index map and the four limits along it.
  set φ : ℕ → ℕ := fun i => ms (k i) with hφ_def
  have hφ : ∀ i, i ≤ φ i := fun i => le_comp_of_le (ms := ms) (k := k) hms hk i
  have hpathφ : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun i => xs (φ i) s ω) atTop (𝓝 (X.X s ω)) := by
    filter_upwards [hpath'] with ω hω
    filter_upwards [hω] with s hs
    exact Tendsto.comp_of_le hs hk
  -- The two shapes of the usual-conditions hypothesis at time zero, under right continuity.
  have hℱ0' : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t := by
    intro t ht
    have hrc : S.ℱ.rightCont = S.ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
    have h := hℱ0 t ht
    rwa [hrc] at h
  -- The admissibility of the jump coefficient read at the left limits of the solution.
  have hγmeasi : ∀ i : Fin n,
      Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i :=
    fun i => (measurable_pi_apply i).comp hγmeas
  have hXm : Measurable fun q : ℝ × Ω => X.X q.1 q.2 := X.measurable_path
  have hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (JumpSplitting.leftLimPathAt X.X p.2.1 p.1) p.2.2 i :=
    fun i => JumpSplitting.measurable_jumpCoeff_leftLimPathAt hXm hXleft i (hγmeasi i)
  have hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (JumpSplitting.leftLimPathAt X.X s ω) e i :=
    fun i => JumpSplitting.markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt hℱ0' hXadapt
      hXleft i (hγmeasi i)
  have hγqL : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (JumpSplitting.leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ := by
    intro i T' hT'
    rw [JumpSplitting.lintegral_sq_jumpCoeff_leftLimPathAt_eq X.cadlag_paths i T']
    exact S.γ_sq i T' hT'
  -- The finite-activity splitting of the truncated path at level `m`, from the hypotheses of
  -- this theorem alone. This is the step `[OB-1]` starts from: the truncated path is a
  -- continuous vector Itô process plus the sum of the jumps carried by the big marks.
  have hsplit : ∀ m : ℕ, ∃ V : ℝ → Ω → Fin n → ℝ,
      LevyStochCalc.Brownian.Ito.IsVectorItoVersion W S.ℱ S.isBrownian
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
        (JumpSplitting.continuousDriftLeftAt coeffs ν X.X (smallMarks ν m)ᶜ) V
      ∧ ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
        xs m t ω i = V t ω i
          + JumpSplitting.jumpSumLeftAt (coeffs.markCutγ (smallMarks ν m)ᶜ) N X.X
              (smallMarks ν m)ᶜ t ω i := by
    intro m
    obtain ⟨V, hV⟩ := JumpSplitting.exists_continuousPart S (A := (smallMarks ν m)ᶜ)
      (measure_compl_smallMarks_ne_top ν m) hℱ0' hnull0 hμm hμp hμq hγmL hγpL hγqL
    have hdrift : JumpSplitting.continuousDriftLeftAt (coeffs.markCutγ (smallMarks ν m)ᶜ) ν X.X
          (smallMarks ν m)ᶜ
        = JumpSplitting.continuousDriftLeftAt coeffs ν X.X (smallMarks ν m)ᶜ :=
      JumpSplitting.continuousDriftLeftAt_congr_of_eqOn coeffs _ X.X (hA m).compl rfl
        fun _ _ e he => Set.indicator_of_mem he _
    have hV' := hV
    rw [← hdrift] at hV'
    refine ⟨V, hV, ?_⟩
    filter_upwards [ae_forall_bigJumpPath_eq_add_jumpSumLeftAt S (hA m) hℱ0 hnull0
      (measure_compl_smallMarks_ne_top ν m) hμm hμq hγmL hγpL hγqL hXadapt
      (fun ω t _ j => hXleft ω t j) hγmeas V hV', hGae] with ω hω hωG
    intro t ht i
    simp only [hxs_def]
    rw [truncPath_of_nonneg S hℱ0 hnull0 G m ht, repairOn_of_mem hωG]
    exact hω t ht i
  -- Obligation 1' (the finite-activity identity at each level, in the mixed form), from the
  -- finite-activity identity along the truncated path, with the two stochastic integrals
  -- transported from the filtration of the SDE data to its right-continuous regularisation.
  have hstep : ∀ m, ∀ᵐ ω ∂P,
      u T (xs m T ω) - u 0 (xs m 0 ω) - Dr m ω - Bro m ω = Cmp m ω + Cd m ω := by
    intro m
    obtain ⟨V, hV, hVsplit⟩ := hsplit m
    have hrc : S.ℱ.rightCont = S.ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
    have hBp' : ∀ j : Fin d, Probability.ProgressivelyMeasurable S.ℱ
        fun ω s => mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω) j :=
      fun j => hrc ▸ hBp m j
    have hCp' : Probability.MarkedProgressivelyMeasurable S.ℱ (markCut (smallMarks ν m)ᶜ
        fun ω s e => mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e) :=
      hrc ▸ hCp m
    have hxs_ad' : ∀ t : ℝ, Measurable[S.ℱ t] (xs m t) := fun t => hrc ▸ hxs_ad m t
    have hxs_left : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
        ∃ L : ℝ, Tendsto (fun s => xs m s ω j) (𝓝[<] t) (𝓝 L) :=
      fun ω t j => truncPath_leftLim S hℱ0 hnull0 G (fun ω hω m t ht => hGp ω hω m t ht) m ω t j
    have hmain := itoLevy_finiteActivity_mixed S hℱ0' hnull0 hXadapt hXleft hμm hμp hμq hγmeas
      u hu hK₀ hK₁ hK₂ T hT (hA m).compl (measure_compl_smallMarks_ne_top ν m) (xs m) (hxs_m m)
      (hxs_rc m) hxs_ad' hxs_left V hV hVsplit (hBm m) hBp' (hBq m) (hCm m) hCp' (hCq m)
    have hchan : ∀ j : Fin d,
        stochasticIntegralBrownian (W.W j) S.ℱ (S.isBrownian j)
            (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω) j)
            (hBm m j) (hBp' j) (hBq m j) T
          =ᵐ[P] stochasticIntegralBrownian (W.W j) S.ℱ.rightCont (h𝒢W j)
            (fun ω s => mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω) j)
            (hBm m j) (hBp m j) (hBq m j) T :=
      fun j => stochasticIntegralBrownian_congr_filtration (W.W j) S.ℱ S.ℱ.rightCont
        (S.isBrownian j) (h𝒢W j) hle _ (hBm m j) (hBp' j) (hBp m j) (hBq m j) T
    have hC : stochasticIntegral N S.ℱ S.isPoisson
          (markCut (smallMarks ν m)ᶜ
            fun ω s e => mixedJumpIncrement u coeffs.γ s (xs m s ω) (X.X s ω) e)
          (hCm m) hCp' (hCq m) T
        =ᵐ[P] Cmp m :=
      stochasticIntegral_congr_filtration N S.ℱ S.ℱ.rightCont S.isPoisson h𝒢N hle _
        (hCm m) hCp' (hCp m) (hCq m) T
    filter_upwards [hmain, MeasureTheory.ae_all_iff.mpr hchan, hC] with ω h1 h2 h3
    have hB : MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
          (fun s ω => mixedDiffusionIntegrand u coeffs.σ s (xs m s ω) (X.X s ω))
          (hBm m) hBp' (hBq m) T ω = Bro m ω := by
      simp only [hBro_def]
      rw [multidimStochasticIntegral_eq_sum, multidimStochasticIntegral_eq_sum]
      exact Finset.sum_congr rfl fun j _ => h2 j
    rw [hB, h3] at h1
    exact h1
  -- The endpoints.
  have hend : ∀ᵐ ω ∂P, Tendsto (fun i => u T (xs (φ i) T ω) - u 0 (xs (φ i) 0 ω)) atTop
      (𝓝 (u T (X.X T ω) - u 0 (X.X 0 ω))) := by
    filter_upwards [hlim, hGae, X.initial_value, MeasureTheory.ae_all_iff.mpr
      fun m : ℕ => bigJumpPath_ae_initial S (hA m) hℱ0 hnull0] with ω hω hωG h0 hm0
    have hT' : Tendsto (fun i => xs (φ i) T ω) atTop (𝓝 (X.X T ω)) :=
      tendsto_pi_nhds.mpr fun i => hω (Sum.inl i)
    have h0' : ∀ i, u 0 (xs (φ i) 0 ω) = u 0 (X.X 0 ω) := by
      intro i
      rw [hxs_eq (φ i) ω hωG 0 le_rfl, h0]
      exact congrArg (u 0) (hm0 (φ i))
    simp_rw [h0']
    exact (SmallJump.tendsto_comp_of_tendsto hu T hT').sub_const _
  -- The drift term: dominated convergence on the window.
  have hdrift : ∀ᵐ ω ∂P, Tendsto (fun i => Dr (φ i) ω) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))) :=
    tendsto_mixedDriftIntegral_of_tendsto S hu hK₀' hK₁' hK₂' hK₂0 hμm hμq T hT
      (fun i => xs (φ i)) (fun i => hxs_m (φ i)) hpathφ
  -- The two stochastic terms, by the choice of `k`, transported back to the filtration of `S`.
  have hbro : ∀ᵐ ω ∂P, Tendsto (fun i => Bro (φ i) ω) atTop
      (𝓝 (MultidimBrownianMotion.stochasticIntegral W S.ℱ S.isBrownian
        (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
        h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω)) := by
    filter_upwards [hlim, hB_eq] with ω hω hB
    rw [← hB]
    exact tendsto_finsetSum _ fun j _ => hω (Sum.inr (Sum.inl j))
  have hcmp : ∀ᵐ ω ∂P, Tendsto (fun i => Cmp (φ i) ω) atTop
      (𝓝 (stochasticIntegral N S.ℱ S.isPoisson
        (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
        h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω)) := by
    filter_upwards [hlim, hC_eq] with ω hω hC
    rw [← hC]
    exact hω (Sum.inr (Sum.inr ()))
  -- The compensator-drift term: dominated convergence on the window and the mark space.
  have hcdrift : ∀ᵐ ω ∂P, Tendsto (fun i => Cd (φ i) ω) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν)) :=
    tendsto_mixedCompensatorDriftIntegral_of_tendsto S hu hK₂' hK₂0 T hT
      (fun i => xs (φ i)) (fun i => hxs_m (φ i)) φ hφ hpathφ
  -- Step 5: the five-term limit identity along `φ`.
  exact ae_itoLevy_of_ae_tendsto_terms coeffs u T (fun i => xs (φ i)) X.X
    (fun i => Dr (φ i)) (fun i => Bro (φ i)) _ (fun i => Cmp (φ i)) _ (fun i => Cd (φ i))
    (fun i => hstep (φ i)) hend hdrift hbro hcmp hcdrift

end Main

end LevyStochCalc.Ito.JumpFormula
