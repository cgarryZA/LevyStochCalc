/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSplittingLeftLim
import LevyStochCalc.Ito.MarkedZeroExtension

/-!
# Pathwise left-limit jump sums and compensator drifts

A pathwise jump sum is an integral against the random measure of a jump coefficient read along
the left limits of a path, so it is determined by a coefficient bundle, a random measure and a
path; no relation between the bundle and the path enters. This file indexes the left limits, the
left-limit jump sum over a mark set and the drift carrying the left-limit compensator on such a
triple, identifies them along the path of a jump diffusion with the jump-diffusion-indexed
objects, and records their elementary regularity: the jump sum vanishes over the degenerate
window, the jump sum and the compensator drift are unchanged when the left-limit jump integrand
is replaced by its zero extension, a càdlàg path meets its left limits at all but countably many
positive times, the jump sum is right-continuous in time, its integrand is almost surely
integrable over every bounded window of a mark set of finite intensity, and both the jump sum and
the compensator drift depend on the coefficient bundle only through the values of its jump
coefficient on that mark set.
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

end Setup

end LevyStochCalc.Ito.JumpSplitting
