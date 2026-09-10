/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Setting
import LevyStochCalc.Poisson.SmallJump
import LevyStochCalc.Ito.ItoFormulaUnbounded
import LevyStochCalc.Probability.ProgressiveCadlag

/-!
# Removing the small jumps of a jump diffusion

For a jump diffusion `X` and an antitone family `A : ℕ → Set E` of mark sets whose intersection
is `ν`-null, the *big-jump process* is the path with the compensated integral of the jump
coefficient over `A m` subtracted coordinatewise. The subtracted term is the compensated
integral of a mark cut, so its `L²` size is the energy carried by `A m` and vanishes as
`m → ∞`; the big-jump processes therefore converge to the path at every fixed nonnegative time
in `L²`, almost surely along a subsequence, and — after composing with a `C²` function of time
and state — pathwise along that subsequence.

## Main definitions

* `LevyStochCalc.Ito.SmallJump.JumpIntegrand` — the filtration and admissibility data with
  which the coordinates of the jump coefficient along a path are integrated against `Ñ`.
* `LevyStochCalc.Ito.SmallJump.smallJumpIntegral` — the compensated integral of one coordinate
  of the jump coefficient, restricted to the marks in `A m`.
* `LevyStochCalc.Ito.SmallJump.bigJumpProcess` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` — `L²` convergence of
  the big-jump processes to the path at a fixed nonnegative time.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors along a subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_comp` — the same, transported through a
  `C²` function of time and state.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.SmallJump

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

/-- The `i`-th coordinate of the jump coefficient of a jump diffusion, evaluated along a path
`Xp`, as an integrand in sample point, time and mark. -/
def pathJumpCoeff (coeffs : JumpDiffusionCoeffs n d E) (Xp : ℝ → Ω → (Fin n → ℝ))
    (i : Fin n) : Ω → ℝ → E → ℝ :=
  fun ω s e => coeffs.γ s (Xp s ω) e i

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
variable {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The data with which the jump coefficient along a path `Xp` is integrated against the
compensated Poisson random measure of `N`. -/
structure JumpIntegrand (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E) (Xp : ℝ → Ω → (Fin n → ℝ)) where
  /-- The filtration the integrands are progressively measurable for. -/
  ℱ : Filtration ℝ ‹MeasurableSpace Ω›
  /-- `N` is a Poisson random measure for `ℱ`. -/
  isPoisson : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ
  /-- The path is jointly measurable in time and sample point. -/
  measurable_path : Measurable (Function.uncurry Xp)
  /-- Each coordinate of the jump coefficient along the path is jointly measurable. -/
  meas : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => pathJumpCoeff coeffs Xp i p.1 p.2.1 p.2.2
  /-- Each coordinate of the jump coefficient along the path is progressively measurable. -/
  prog : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ (pathJumpCoeff coeffs Xp i)
  /-- Each coordinate of the jump coefficient along the path has finite energy on every
  bounded window. -/
  sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖pathJumpCoeff coeffs Xp i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤

/-- The integrand data supplied by the SDE that a jump diffusion solves. -/
noncomputable def JumpIntegrand.ofJumpDiffusion (X : JumpDiffusion W N coeffs x₀) :
    JumpIntegrand N coeffs X.X := by
  choose ℱ _hW hN _hσm _hσp _hσq hγm hγp hγq _hsol using X.is_solution
  exact ⟨ℱ, hN, X.measurable_path, hγm, hγp, hγq⟩

variable {Xp : ℝ → Ω → (Fin n → ℝ)} {A : ℕ → Set E}

/-- The compensated integral of the `i`-th coordinate of the jump coefficient along the path,
restricted to the marks in `A m`. -/
noncomputable def smallJumpIntegral (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m)) (m : ℕ) (i : Fin n) : ℝ → Ω → ℝ :=
  stochasticIntegral N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
    (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
    fun T' hT' => sq_markCut (G.sq i) (A m) T' hT'

/-- The path of a jump diffusion with the jumps carried by the marks in `A m` removed. -/
noncomputable def bigJumpProcess (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m)) (m : ℕ) (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => Xp t ω i - smallJumpIntegral G hA m i t ω

section Basic

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))

/-- The big-jump process differs from the path by the compensated integral over the small
marks. -/
theorem bigJumpProcess_sub (m : ℕ) (t : ℝ) (ω : Ω) (i : Fin n) :
    bigJumpProcess G hA m t ω i - Xp t ω i = -smallJumpIntegral G hA m i t ω := by
  show Xp t ω i - smallJumpIntegral G hA m i t ω - Xp t ω i = _
  ring

/-- A coordinate of a jointly measurable path at a fixed time is measurable. -/
theorem measurable_pathCoord (hXm : Measurable (Function.uncurry Xp)) (t : ℝ) (i : Fin n) :
    Measurable fun ω => Xp t ω i :=
  (measurable_pi_apply i).comp (hXm.comp (measurable_const.prodMk measurable_id))

/-- The compensated integral over the small marks is adapted to the right-continuous
filtration. -/
theorem adapted_smallJumpIntegral (m : ℕ) (i : Fin n) :
    Adapted G.ℱ.rightCont (smallJumpIntegral G hA m i) :=
  stochasticIntegral_adapted N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
    (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
    fun T' hT' => sq_markCut (G.sq i) (A m) T' hT'

/-- The compensated integral over the small marks is measurable at each time. -/
theorem measurable_smallJumpIntegral (m : ℕ) (i : Fin n) (t : ℝ) :
    Measurable (smallJumpIntegral G hA m i t) :=
  (adapted_smallJumpIntegral G hA m i t).mono (G.ℱ.rightCont.le t) le_rfl

/-- A coordinate of the big-jump process at a fixed time is measurable. -/
theorem measurable_bigJumpProcess (m : ℕ) (t : ℝ) (i : Fin n) :
    Measurable fun ω => bigJumpProcess G hA m t ω i :=
  (measurable_pathCoord G.measurable_path t i).sub (measurable_smallJumpIntegral G hA m i t)

/-- The paths of the compensated integral over the small marks are almost surely càdlàg. -/
theorem ae_cadlag_smallJumpIntegral (m : ℕ) (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => smallJumpIntegral G hA m i s ω) (𝓝[>] t)
          (𝓝 (smallJumpIntegral G hA m i t ω))
        ∧ ∃ L : ℝ, Tendsto (fun s => smallJumpIntegral G hA m i s ω) (𝓝[<] t) (𝓝 L) :=
  stochasticIntegral_cadlag N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
    (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
    fun T' hT' => sq_markCut (G.sq i) (A m) T' hT'

/-- A coordinate of the big-jump process is jointly measurable as soon as the compensated
integral over the small marks is right-continuous at every sample point. -/
theorem measurable_uncurry_bigJumpProcess (m : ℕ) (i : Fin n)
    (hright : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => smallJumpIntegral G hA m i s ω) (𝓝[>] t)
      (𝓝 (smallJumpIntegral G hA m i t ω))) :
    Measurable (Function.uncurry fun ω s => bigJumpProcess G hA m s ω i) := by
  have hM : Measurable fun p : Ω × ℝ => smallJumpIntegral G hA m i p.2 p.1 :=
    (Probability.measurable_uncurry_of_rightContinuous
      (adapted_smallJumpIntegral G hA m i) hright).comp measurable_swap
  have hX : Measurable fun p : Ω × ℝ => Xp p.2 p.1 i :=
    (measurable_pi_apply i).comp (G.measurable_path.comp measurable_swap)
  exact hX.sub hM

/-- At nonpositive times the compensated integral over the small marks vanishes almost
surely. -/
theorem smallJumpIntegral_ae_zero (m : ℕ) (i : Fin n) {t : ℝ} (ht : t ≤ 0) :
    smallJumpIntegral G hA m i t =ᵐ[P] 0 :=
  (stochasticIntegral_ae_eq_process N G.ℱ G.isPoisson
        (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
        ((G.prog i).indicator_mark (hA m))
        (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') t).trans
    (process_ae_zero_of_nonpos N G.ℱ G.isPoisson _ _ _ _ ht)

end Basic

section Limits

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))

/-- The compensated integrals over a shrinking family of marks tend to `0` in `L²`. -/
theorem tendsto_lintegral_sq_smallJumpIntegral (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) (i : Fin n) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun m => ∫⁻ ω, (‖smallJumpIntegral G hA m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P) atTop (𝓝 0) :=
  tendsto_lintegral_sq_stochasticIntegral_markCut N G.ℱ G.isPoisson
    (pathJumpCoeff coeffs Xp i) (G.meas i) (G.prog i) (G.sq i) A hA hanti hnull ht

/-- **The big-jump processes converge to the path in `L²` at every nonnegative time.** -/
theorem tendsto_lintegral_sq_bigJumpProcess_sub (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => ∫⁻ ω, (‖bigJumpProcess G hA m t ω i - Xp t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hrw : ∀ m : ℕ, ∫⁻ ω, (‖bigJumpProcess G hA m t ω i - Xp t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖smallJumpIntegral G hA m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro m
    refine lintegral_congr fun ω => ?_
    rw [bigJumpProcess_sub, nnnorm_neg]
  simp_rw [hrw]
  rcases eq_or_lt_of_le ht with h0 | h0
  · subst h0
    have hz : ∀ m : ℕ, ∫⁻ ω, (‖smallJumpIntegral G hA m i 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
      intro m
      have hae : (fun ω => (‖smallJumpIntegral G hA m i 0 ω‖₊ : ℝ≥0∞) ^ 2)
          =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
        filter_upwards [smallJumpIntegral_ae_zero G hA m i (le_refl (0 : ℝ))] with ω hω
        simp [hω]
      rw [lintegral_congr_ae hae]
      simp
    simp_rw [hz]
    exact tendsto_const_nhds
  · exact tendsto_lintegral_sq_smallJumpIntegral G hA hanti hnull i h0

/-- **Along a subsequence the big-jump processes converge to the path almost surely, in every
coordinate at once.** -/
theorem exists_seq_ae_tendsto_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ i : Fin n,
        Tendsto (fun k => bigJumpProcess G hA (ms k) t ω i) atTop (𝓝 (Xp t ω i)) :=
  LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral
    (u := fun m i ω => bigJumpProcess G hA m t ω i) (v := fun i ω => Xp t ω i)
    (fun m i => measurable_bigJumpProcess G hA m t i)
    (fun i => measurable_pathCoord G.measurable_path t i)
    fun i => tendsto_lintegral_sq_bigJumpProcess_sub G hA hanti hnull i ht

/-- **Along a subsequence the big-jump vectors converge to the path almost surely.** -/
theorem exists_seq_ae_tendsto_bigJumpProcess_pi (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => bigJumpProcess G hA (ms k) t ω) atTop (𝓝 (Xp t ω)) := by
  obtain ⟨ms, hms, hae⟩ := exists_seq_ae_tendsto_bigJumpProcess G hA hanti hnull ht
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae] with ω hω
  exact tendsto_pi_nhds.mpr hω

end Limits

/-- A twice continuously differentiable function of time and state is continuous in the state,
so it transports convergence of vectors. -/
theorem tendsto_comp_of_tendsto {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (t : ℝ) {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}
    (h : Tendsto z atTop (𝓝 w)) : Tendsto (fun k => u t (z k)) atTop (𝓝 (u t w)) := by
  have hc : Continuous fun y : Fin n → ℝ => u t y := by
    have heq : (fun y : Fin n → ℝ => u t y) = Function.uncurry u ∘ fun y => (t, y) := rfl
    rw [heq]
    exact hu.continuous.comp (continuous_const.prodMk continuous_id)
  exact (hc.tendsto w).comp h

/-- **A `C²` function of time and state, evaluated along the big-jump processes, converges to
its value along the path almost surely, along a subsequence.** -/
theorem exists_seq_ae_tendsto_comp (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m)) (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0)
    {t : ℝ} (ht : 0 ≤ t) {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => bigJumpProcess G hA (ms k) t ω) atTop (𝓝 (Xp t ω))) ∧
      ∀ᵐ ω ∂P,
        Tendsto (fun k => u t (bigJumpProcess G hA (ms k) t ω)) atTop (𝓝 (u t (Xp t ω))) := by
  obtain ⟨ms, hms, hae⟩ := exists_seq_ae_tendsto_bigJumpProcess_pi G hA hanti hnull ht
  refine ⟨ms, hms, hae, ?_⟩
  filter_upwards [hae] with ω hω
  exact tendsto_comp_of_tendsto hu t hω

end LevyStochCalc.Ito.SmallJump
