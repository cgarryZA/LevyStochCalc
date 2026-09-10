/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSplittingLeftLim
import LevyStochCalc.Ito.MarkedZeroExtension

/-!
# Finite-activity splitting along the left limits of a prescribed path

A pathwise jump sum is an integral against the random measure of a jump coefficient read along
the left limits of a path, so it is determined by a coefficient bundle, a random measure and a
path; no relation between the bundle and the path enters. Indexing the left-limit jump sum, the
left limits themselves and the drift carrying the left-limit compensator on that triple rather
than on a jump-diffusion solution therefore loses nothing, and lets the coefficient bundle be
changed — to the bundle cut down to a mark set, say — with the path held fixed.

The splitting of a path into a vector Itô process and a left-limit jump sum likewise separates
into what is read along the evaluation path, namely the coefficients and the jump sum, and what
is asked of the split path, namely the integral equation and right continuity on the nonnegative
half-line. The two paths are therefore free of one another.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.leftLimPathAt` — the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt` — the pathwise sum of the jumps carried by a
  mark set, with the jump coefficient of a bundle evaluated at the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt` — the drift of a bundle along a path
  with the compensator of its left-limit jump coefficient subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt_path`,
  `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt_path` — the jump-diffusion-indexed jump
  sum and drift as the instances of these at the path of the jump diffusion.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt_congr_of_eqOn` — two bundles whose jump
  coefficients agree on a mark set have the same jump sum over it.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt_congr_of_eqOn` — two bundles with the
  same drift whose jump coefficients agree on a mark set have the same compensator drift.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt_zeroExtPos`,
  `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt_zeroExtPos` — the jump sum and the
  compensator drift at a positive time are unchanged by the zero extension of the left-limit
  jump integrand.
* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeftAt_of_path` — the splitting
  at a fixed nonnegative time, for a path satisfying the integral equation.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_of_path` — the same identity
  almost surely at all nonnegative times simultaneously, for a right-continuous such path.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft_of_path`,
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion` — the case of
  the coefficients read along the path of a jump diffusion, and of its own path.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_integrableOn_windowLeft`,
  `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeft`,
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft` — the same three statements
  indexed on a jump diffusion rather than on a coefficient bundle and a path.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}

section BarePath

/-- The left limits of a path. -/
noncomputable def leftLimPathAt (Xp : ℝ → Ω → Fin n → ℝ) (s : ℝ) (ω : Ω) : Fin n → ℝ :=
  Function.leftLim (fun r => Xp r ω) s

/-- The pathwise sum of the jumps carried by the mark set `A` over the window `(0, t]`, with the
jump coefficient evaluated at the left limits of the path `Xp`. -/
noncomputable def jumpSumLeftAt (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ) (A : Set E)
    (t : ℝ) (ω : Ω) (i : Fin n) : ℝ :=
  ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i ∂(N.N ω)

/-- The drift of a coefficient bundle along a path with the compensator of the jumps carried by
`A` subtracted, the jump coefficient being evaluated at the left limits of the path. -/
noncomputable def continuousDriftLeftAt (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (ν : Measure E) (Xp : ℝ → Ω → Fin n → ℝ) (A : Set E) (i : Fin n) (ω : Ω) (s : ℝ) : ℝ :=
  coeffs.μ s (Xp s ω) i - ∫ e in A, coeffs.γ s (leftLimPathAt Xp s ω) e i ∂ν

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- Along the path of a jump diffusion the left limits are those of the jump diffusion. -/
theorem leftLimPathAt_path (X : Setting.JumpDiffusion W N coeffs x₀) :
    leftLimPathAt X.X = leftLimPath X := rfl

/-- Along the path of a jump diffusion the jump sum is the jump diffusion's left-limit jump
sum. -/
theorem jumpSumLeftAt_path (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    jumpSumLeftAt coeffs N X.X A = jumpSumLeft X A := rfl

/-- Along the path of a jump diffusion the drift is the jump diffusion's left-limit drift. -/
theorem continuousDriftLeftAt_path (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) :
    continuousDriftLeftAt coeffs ν X.X A = continuousDriftLeft X A := rfl

end BarePath

section BareRegularity

variable (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)

/-- The jump sum over the degenerate window vanishes. -/
theorem jumpSumLeftAt_zero (A : Set E) (ω : Ω) (i : Fin n) :
    jumpSumLeftAt coeffs N Xp A 0 ω i = 0 := by
  simp [jumpSumLeftAt]

/-- The jump sum integrates over a window of positive times, so it is unchanged when the
left-limit jump integrand is replaced by its zero extension. -/
theorem jumpSumLeftAt_zeroExtPos {A : Set E} (hA : MeasurableSet A) (t : ℝ) (ω : Ω)
    (i : Fin n) :
    ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, JumpFormula.zeroExtPos
        (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) ω q.1 q.2 ∂(N.N ω)
      = jumpSumLeftAt coeffs N Xp A t ω i :=
  JumpFormula.setIntegral_window_zeroExtPos _ ω hA t (N.N ω)

omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- At a positive time the drift carrying the left-limit compensator is unchanged when the
left-limit jump integrand is replaced by its zero extension. -/
theorem continuousDriftLeftAt_zeroExtPos (A : Set E) (i : Fin n) (ω : Ω) {s : ℝ} (hs : 0 < s) :
    coeffs.μ s (Xp s ω) i - ∫ e in A, JumpFormula.zeroExtPos
        (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) ω s e ∂ν
      = continuousDriftLeftAt coeffs ν Xp A i ω s := by
  simp only [continuousDriftLeftAt, JumpFormula.zeroExtPos_of_pos _ ω hs]

variable {Xp}

omit [MeasurableSpace Ω] in
/-- A path converging in each coordinate along the filter of times strictly below a given time
has that limit as its left limit there. -/
theorem leftLimPathAt_eq_of_tendsto {ω : Ω} {t : ℝ} {L : Fin n → ℝ}
    (hL : ∀ i : Fin n, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 (L i))) :
    leftLimPathAt Xp t ω = L :=
  leftLim_eq_of_tendsto (tendsto_pi_nhds.mpr hL)

omit [MeasurableSpace Ω] in
/-- A path with left limits in each coordinate at a given time converges there to its left
limits. -/
theorem tendsto_nhdsLT_leftLimPathAt {ω : Ω} {t : ℝ}
    (h : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L)) (i : Fin n) :
    Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 (leftLimPathAt Xp t ω i)) := by
  classical
  choose L hL using h
  rw [leftLimPathAt_eq_of_tendsto hL]
  exact hL i

variable (Xp)

omit [IsProbabilityMeasure P] in
/-- A càdlàg path meets its left limits at all but countably many positive times. -/
theorem ae_countable_setOf_pos_ne_leftLimPathAt
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧ leftLimPathAt Xp s ω ≠ Xp s ω}.Countable := by
  filter_upwards [hcadlag] with ω hω
  refine Set.Countable.mono ?_ (countable_setOf_pos_ne_of_cadlag
    (f := fun s => Xp s ω) (g := fun s => leftLimPathAt Xp s ω)
    (fun t ht => (hω t ht).1) (fun t ht i => tendsto_nhdsLT_leftLimPathAt (hω t ht.le).2 i))
  intro s hs
  exact ⟨hs.1, fun h => hs.2 h.symm⟩

/-- The left-limit jump sum over `(0, ·]` is right-continuous in time along a path whose
left-limit jump coefficient is integrable over every bounded window. -/
theorem tendsto_jumpSumLeftAt_nhdsWithin_Ioi {A : Set E} (hA : MeasurableSet A) {i : Fin n}
    (hγmL : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
    {ω : Ω}
    (hint : ∀ T : ℝ, IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)) (t : ℝ) :
    Tendsto (fun s => jumpSumLeftAt coeffs N Xp A s ω i) (𝓝[>] t)
      (𝓝 (jumpSumLeftAt coeffs N Xp A t ω i)) := by
  have hfm : Measurable fun q : ℝ × E => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i :=
    hγmL.comp measurable_prodMk_left
  exact tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi hA hfm hint t

/-- The left-limit jump coefficient along a path is almost surely integrable against the random
measure over every bounded window of a mark set of finite intensity. -/
theorem ae_forall_integrableOn_windowLeftAt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (i : Fin n),
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω) := by
  have hstep : ∀ (m : ℕ) (i : Fin n), ∀ᵐ ω ∂P,
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) ((m : ℝ) + 1) ×ˢ A) (N.N ω) := by
    intro m i
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    filter_upwards [JumpFormula.ae_integrableOn_window_of_zeroExtPos N hℱN hA hAν ((m : ℝ) + 1)
      (hpredL i) (hγmL i)
      (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
        (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) (hγmL i) (hγqL i)
        (A := A) hpos)] with ω hω
    exact hω.1
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun m : ℕ =>
    MeasureTheory.ae_all_iff.mpr fun i : Fin n => hstep m i] with ω hω
  intro T i
  obtain ⟨m, hm⟩ := exists_nat_ge T
  refine (hω m i).mono_set (Set.prod_mono (Set.Ioc_subset_Ioc_right ?_) (subset_refl A))
  linarith

omit [MeasurableSpace E] in
/-- The Brownian integral of a row of the diffusion coefficient along a path is the martingale
part of the corresponding coordinate of the vector Itô process built from it. -/
theorem multidimIntegral_eq_vectorItoMartingaleAt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hσm : ∀ (i : Fin n) (j : Fin d),
      Measurable (Function.uncurry fun ω s => coeffs.σ s (Xp s ω) i j))
    (hσp : ∀ (i : Fin n) (j : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Xp s ω) i j)
    (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.σ s (Xp s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (i : Fin n) (t : ℝ) (ω : Ω) :
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
        (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
        (fun j => hσq i j) t ω
      = LevyStochCalc.Brownian.Ito.vectorItoMartingale W ℱ hℱW
          (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq i t ω := rfl

end BareRegularity

section Bundles

/-- Two coefficient bundles whose jump coefficients agree on a mark set have the same jump sum
over that mark set. -/
theorem jumpSumLeftAt_congr_of_eqOn (coeffs coeffs' : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ) {A : Set E}
    (hA : MeasurableSet A)
    (hγ : ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∈ A → coeffs'.γ s y e = coeffs.γ s y e)
    (t : ℝ) (ω : Ω) (i : Fin n) :
    jumpSumLeftAt coeffs' N Xp A t ω i = jumpSumLeftAt coeffs N Xp A t ω i :=
  setIntegral_congr_fun (measurableSet_Ioc.prod hA) fun q hq =>
    congrFun (hγ q.1 (leftLimPathAt Xp q.1 ω) q.2 hq.2) i

omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- Two coefficient bundles with the same drift whose jump coefficients agree on a mark set have
the same drift carrying the left-limit compensator over that mark set. -/
theorem continuousDriftLeftAt_congr_of_eqOn (coeffs coeffs' : Setting.JumpDiffusionCoeffs n d E)
    (Xp : ℝ → Ω → Fin n → ℝ) {A : Set E} (hA : MeasurableSet A) (hμ : coeffs'.μ = coeffs.μ)
    (hγ : ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∈ A → coeffs'.γ s y e = coeffs.γ s y e) :
    continuousDriftLeftAt coeffs' ν Xp A = continuousDriftLeftAt coeffs ν Xp A := by
  funext i ω s
  rw [continuousDriftLeftAt, continuousDriftLeftAt, hμ]
  congr 1
  exact setIntegral_congr_fun hA fun e he => congrFun (hγ s (leftLimPathAt Xp s ω) e he) i

end Bundles

section SplittingAt

variable (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
  (x₀ : Fin n → ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Xp s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Xp s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (Xp s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Xp p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (Xp s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
    coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ
    fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation.** If the jump
coefficient is carried by a mark set of finite intensity, the zero extension of its left-limit
integrand along the evaluation path is marked predictable and that path is càdlàg, then at every
nonnegative time a path
satisfying that equation is almost surely the sum of the vector Itô process with diffusion `σ`
and drift `continuousDriftLeftAt`, and the left-limit jump sum over that mark set. -/
theorem eq_vectorItoProcess_add_jumpSumLeftAt_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hXpcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeftAt coeffs ν Xp A) t ω i
          + jumpSumLeftAt coeffs N Xp A t ω i := by
  have hsupp' : ∀ (i : Fin n) (ω : Ω) (s : ℝ) (e : E), e ∉ A →
      coeffs.γ s (leftLimPathAt Xp s ω) e i = 0 := by
    intro i ω s e he
    simp [hsupp s (leftLimPathAt Xp s ω) e he]
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    have hCzero : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) 0 ω = 0 := by
      intro i
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN
          (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) 0,
        LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos N ℱ hℱN
          (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i)
          (le_refl (0 : ℝ))] with ω h1 h2
      rw [h1, h2]
      rfl
    have hz0 : ∀ g : ℝ → ℝ, ∫ s in Set.Icc (0 : ℝ) 0, g s ∂volume = 0 :=
      fun g => setIntegral_measure_zero g (by simp)
    filter_upwards [hSDE 0 le_rfl, MeasureTheory.ae_all_iff.mpr hCzero] with ω hω hz
    intro i
    rw [hω i, hz i,
      multidimIntegral_eq_vectorItoMartingaleAt coeffs Xp ℱ hℱW hσm hσp hσq i 0 ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, hz0, jumpSumLeftAt_zero]
  · have hcong : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) t ω := fun i =>
      compensatedIntegral_congr_of_countable_ne N hℱN (fun s x e => coeffs.γ s x e i)
        (ae_countable_setOf_pos_ne_leftLimPathAt Xp hXpcadlag) (hγmL i) (hγm i) (hγpL i)
        (hγp i) (hγqL i) (hγq i) hpos
    have hpathL : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = jumpSumLeftAt coeffs N Xp A t ω i
            - ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i
                ∂(LevyStochCalc.Poisson.referenceIntensity ν) := fun i =>
      JumpFormula.stochasticIntegral_ae_eq_pathwise_of_zeroExtPos N ℱ hℱN
        (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) (hγmL i) (hγpL i) (hγqL i) hA
        (hpredL i) hAν (hsupp' i) hpos
    have hwinL : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i)
          (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [JumpFormula.ae_integrableOn_window_of_zeroExtPos N hℱN hA hAν t (hpredL i)
        (hγmL i) (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
          (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) (hγmL i) (hγqL i)
          (A := A) hpos)] with ω hω
      exact hω.2
    have hμint : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun s => coeffs.μ s (Xp s ω) i) (Set.Icc (0 : ℝ) t) volume := by
      intro i
      have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        ((ENNReal.continuous_coe.measurable.comp (hμm i).nnnorm).pow_const
          2).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      filter_upwards [ae_lt_top' hmeas.aemeasurable (hμq i t hpos).ne] with ω hω
      exact integrableOn_Icc_of_lintegral_sq_lt_top
        ((hμm i).comp measurable_prodMk_left).aestronglyMeasurable hω
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [hSDE t ht, hcong i, hpathL i, hwinL i, hμint i] with ω hω hc hp hw hm
    obtain ⟨heq, hcint⟩ :=
      integral_window_eq_and_integrableOn
        (fun s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) hw
    have hd : ∫ s in Set.Icc (0 : ℝ) t, continuousDriftLeftAt coeffs ν Xp A i ω s ∂volume
        = (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t,
              (∫ e in A, coeffs.γ s (leftLimPathAt Xp s ω) e i ∂ν) ∂volume :=
      integral_sub hm hcint
    rw [hω i, ← hc, hp,
      multidimIntegral_eq_vectorItoMartingaleAt coeffs Xp ℱ hℱW hσm hσp hσq i t ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    rw [hd, heq]
    ring

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation, at all
nonnegative times.** If the jump coefficient is carried by a mark set of finite intensity, the
zero extension of its left-limit integrand along the càdlàg evaluation path is marked predictable,
`V` is a modification of the vector Itô process with diffusion `σ` and drift
`continuousDriftLeftAt` whose paths are
right-continuous, and `Z` is a right-continuous path satisfying that equation, then almost surely
`Z` is, at every nonnegative time, the sum of `V` and the left-limit jump sum over that mark
set. -/
theorem ae_forall_eq_add_jumpSumLeftAt_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hXpcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeftAt coeffs ν Xp A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i := by
  have hwin := ae_forall_integrableOn_windowLeftAt coeffs N Xp ℱ hℱN hA hAν hpredL hγmL hγqL
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      Z t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine ae_forall_eq_of_ae_rat (P := P) (Y := fun s ω => Z s ω i)
      (Z := fun s ω => V s ω i + jumpSumLeftAt coeffs N Xp A s ω i) ?_ ?_ ?_
    · intro q hq
      filter_upwards [eq_vectorItoProcess_add_jumpSumLeftAt_of_path coeffs N Xp x₀ ℱ hℱW
        hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL hγqL Z hXpcadlag hSDE hA hAν hsupp hpredL
        hμm hμq hq, hVae (q : ℝ) hq] with ω h1 h2
      show Z (q : ℝ) ω i = V (q : ℝ) ω i + jumpSumLeftAt coeffs N Xp A (q : ℝ) ω i
      rw [h1 i, h2 i]
    · filter_upwards [hZright] with ω hω t ht
      exact ((continuous_apply i).tendsto (Z t ω)).comp (hω t ht)
    · filter_upwards [hVright, hwin] with ω hVω hwω t ht
      exact (hVω t ht i).add
        (tendsto_jumpSumLeftAt_nhdsWithin_Ioi coeffs N Xp hA (hγmL i) (fun T => hwω T i) t)
  filter_upwards [key] with ω hω
  intro t ht i
  exact hω i t ht

end SplittingAt

section JumpDiffusionWindow

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The left-limit jump coefficient along the path of a jump diffusion is almost surely
integrable against the random measure over every bounded window of the mark set. -/
theorem ae_forall_integrableOn_windowLeft (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hγmL : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (leftLimPath X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (i : Fin n),
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω) :=
  ae_forall_integrableOn_windowLeftAt coeffs N X.X ℱ hℱN hA hAν hpredL hγmL hγqL

end JumpDiffusionWindow

section Splitting

variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPath X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation, along the path of
a jump diffusion.** -/
theorem eq_vectorItoProcess_add_jumpSumLeft_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeft X A) t ω i
          + jumpSumLeft X A t ω i :=
  eq_vectorItoProcess_add_jumpSumLeftAt_of_path coeffs N X.X x₀ ℱ hℱW hσm hσp hσq hℱN
    hγm hγp hγq hγmL hγpL hγqL Z X.cadlag_paths hSDE hA hAν hsupp hpredL hμm hμq ht

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation, at all
nonnegative times, along the path of a jump diffusion.** -/
theorem ae_forall_eq_add_jumpSumLeft_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumLeft X A t ω i :=
  ae_forall_eq_add_jumpSumLeftAt_of_path coeffs N X.X x₀ ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq
    hγmL hγpL hγqL Z X.cadlag_paths hZright hSDE hA hAν hsupp hpredL hμm hμq V hVae hVright

include hγmL hγpL hγqL in
/-- **The finite-activity splitting along the left limits at all nonnegative times.** The case of
the jump diffusion's own path, whose right continuity is carried by the càdlàg field. -/
theorem ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumLeft X A t ω i :=
  ae_forall_eq_add_jumpSumLeft_of_path X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL hγqL
    X.X (by filter_upwards [X.cadlag_paths] with ω hω t ht using (hω t ht).1)
    hSDE hA hAν hsupp hpredL hμm hμq V hVae hVright

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a jump diffusion along the left limits of its path.** If
the jump coefficient is carried by a mark set of finite intensity and the zero extension of its
left-limit integrand along the path is marked predictable, then at every nonnegative time the
path is almost surely the sum of the vector Itô process with diffusion `σ` and drift
`continuousDriftLeft`, and the left-limit jump sum over that mark set. -/
theorem eq_vectorItoProcess_add_jumpSumLeft
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeft X A) t ω i
          + jumpSumLeft X A t ω i :=
  eq_vectorItoProcess_add_jumpSumLeft_of_path X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL
    hγqL X.X hSDE hA hAν hsupp hpredL hμm hμq ht

include hγmL hγpL hγqL in
/-- **The finite-activity splitting along the left limits at all nonnegative times.** If the jump
coefficient is carried by a mark set of finite intensity, the zero extension of its left-limit
integrand along the path is marked predictable and `V` is a modification of the vector Itô
process with diffusion `σ` and drift `continuousDriftLeft` whose paths are right-continuous, then
almost surely the path is, at every nonnegative time, the sum of `V` and the left-limit jump sum
over that mark set. -/
theorem ae_forall_eq_add_jumpSumLeft
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPath X s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumLeft X A t ω i :=
  ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL
    hγqL hSDE hA hAν hsupp hpredL hμm hμq V hVae hVright

end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting
