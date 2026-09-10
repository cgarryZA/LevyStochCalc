/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Setting
import LevyStochCalc.Poisson.SmallJump
import LevyStochCalc.Poisson.CompensatedCadlagMod
import LevyStochCalc.Ito.ItoFormulaUnbounded
import LevyStochCalc.Probability.ProgressiveCadlag

/-!
# Removing the small jumps of a jump diffusion

For a jump diffusion `X` and an antitone family `A : ℕ → Set E` of mark sets whose intersection
is `ν`-null, the *big-jump process* is the path with the compensated integral of the jump
coefficient over `A m` subtracted coordinatewise. The subtracted term is the everywhere-càdlàg
modification of the compensated integral of a mark cut, so its `L²` size is the energy carried
by `A m` and vanishes as `m → ∞`; the big-jump processes therefore converge to the path at every
fixed nonnegative time in `L²`, almost surely along a subsequence, at almost every time of a
bounded window along a subsequence, and — after composing with a `C²` function of time and
state — pathwise along that subsequence.

## Main definitions

* `LevyStochCalc.Ito.SmallJump.JumpIntegrand` — the filtration and admissibility data with
  which the coordinates of the jump coefficient along a path are integrated against `Ñ`.
* `LevyStochCalc.Ito.SmallJump.smallJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of one coordinate of the jump coefficient, restricted to the marks
  in `A m`.
* `LevyStochCalc.Ito.SmallJump.bigJumpProcess` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.SmallJump.measurable_uncurry_bigJumpProcess` — joint measurability of a
  coordinate of the big-jump process in the sample point and the time.
* `LevyStochCalc.Ito.SmallJump.tendsto_lintegral_sq_bigJumpProcess_sub` — `L²` convergence of
  the big-jump processes to the path at a fixed nonnegative time.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors along a subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_ae_tendsto_bigJumpProcess_pi` — almost-sure
  convergence of the big-jump vectors at almost every time of a bounded window, along a
  subsequence.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_comp` — the same, transported through a
  `C²` function of time and state.
* `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_drift_bigJumpProcess`,
  `LevyStochCalc.Ito.SmallJump.exists_seq_ae_tendsto_quadVar_bigJumpProcess` — pathwise
  convergence of the drift and quadratic-variation integrals along the big-jump processes.
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

/-- The everywhere-càdlàg modification of the compensated integral of the `i`-th coordinate of
the jump coefficient along the path, restricted to the marks in `A m`. -/
noncomputable def smallJumpIntegral (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)
    (m : ℕ) (i : Fin n) : ℝ → Ω → ℝ :=
  cadlagIntegralPi N G.ℱ G.isPoisson hℱ0 hnull0
    (fun j => markCut (A m) (pathJumpCoeff coeffs Xp j))
    (fun j => measurable_markCut (G.meas j) (hA m))
    (fun j => (G.prog j).indicator_mark (hA m))
    (fun j T' hT' => sq_markCut (G.sq j) (A m) T' hT') i

/-- The path of a jump diffusion with the jumps carried by the marks in `A m` removed. -/
noncomputable def bigJumpProcess (G : JumpIntegrand N coeffs Xp)
    (hA : ∀ m, MeasurableSet (A m))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)
    (m : ℕ) (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => Xp t ω i - smallJumpIntegral G hA hℱ0 hnull0 m i t ω

section Basic

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

/-- The big-jump process differs from the path by the compensated integral over the small
marks. -/
theorem bigJumpProcess_sub (m : ℕ) (t : ℝ) (ω : Ω) (i : Fin n) :
    bigJumpProcess G hA hℱ0 hnull0 m t ω i - Xp t ω i
      = -smallJumpIntegral G hA hℱ0 hnull0 m i t ω := by
  show Xp t ω i - smallJumpIntegral G hA hℱ0 hnull0 m i t ω - Xp t ω i = _
  ring

/-- A coordinate of a jointly measurable path at a fixed time is measurable. -/
theorem measurable_pathCoord (hXm : Measurable (Function.uncurry Xp)) (t : ℝ) (i : Fin n) :
    Measurable fun ω => Xp t ω i :=
  (measurable_pi_apply i).comp (hXm.comp (measurable_const.prodMk measurable_id))

/-- The compensated integral over the small marks agrees almost surely, at each time, with the
`L²` Itô–Lévy integral of the mark cut. -/
theorem smallJumpIntegral_ae_eq (m : ℕ) (i : Fin n) (t : ℝ) :
    smallJumpIntegral G hA hℱ0 hnull0 m i t
      =ᵐ[P] stochasticIntegral N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
        (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
        (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') t :=
  cadlagIntegral_ae_eq N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
    (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0 t

/-- The compensated integral over the small marks is adapted to the right-continuous
filtration. -/
theorem adapted_smallJumpIntegral (m : ℕ) (i : Fin n) :
    Adapted G.ℱ.rightCont (smallJumpIntegral G hA hℱ0 hnull0 m i) :=
  cadlagIntegral_adapted N G.ℱ G.isPoisson (markCut (A m) (pathJumpCoeff coeffs Xp i))
    (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0

/-- The compensated integral over the small marks is measurable at each time. -/
theorem measurable_smallJumpIntegral (m : ℕ) (i : Fin n) (t : ℝ) :
    Measurable (smallJumpIntegral G hA hℱ0 hnull0 m i t) :=
  (adapted_smallJumpIntegral G hA hℱ0 hnull0 m i t).mono (G.ℱ.rightCont.le t) le_rfl

/-- A coordinate of the big-jump process at a fixed time is measurable. -/
theorem measurable_bigJumpProcess (m : ℕ) (t : ℝ) (i : Fin n) :
    Measurable fun ω => bigJumpProcess G hA hℱ0 hnull0 m t ω i :=
  (measurable_pathCoord G.measurable_path t i).sub
    (measurable_smallJumpIntegral G hA hℱ0 hnull0 m i t)

/-- Every path of the compensated integral over the small marks is right-continuous. -/
theorem rightContinuous_smallJumpIntegral (m : ℕ) (i : Fin n) (ω : Ω) (t : ℝ) :
    Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[>] t)
      (𝓝 (smallJumpIntegral G hA hℱ0 hnull0 m i t ω)) :=
  cadlagIntegral_rightContinuous N G.ℱ G.isPoisson
    (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
    ((G.prog i).indicator_mark (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0 ω t

/-- Every path of the compensated integral over the small marks has a left limit at every
time. -/
theorem exists_leftLim_smallJumpIntegral (m : ℕ) (i : Fin n) (ω : Ω) (t : ℝ) :
    ∃ L : ℝ, Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[<] t) (𝓝 L) :=
  cadlagIntegral_exists_leftLim N G.ℱ G.isPoisson
    (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
    ((G.prog i).indicator_mark (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0 ω t

/-- The paths of the compensated integral over the small marks are almost surely càdlàg. -/
theorem ae_cadlag_smallJumpIntegral (m : ℕ) (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[>] t)
          (𝓝 (smallJumpIntegral G hA hℱ0 hnull0 m i t ω))
        ∧ ∃ L : ℝ,
            Tendsto (fun s => smallJumpIntegral G hA hℱ0 hnull0 m i s ω) (𝓝[<] t) (𝓝 L) :=
  Filter.Eventually.of_forall fun ω t =>
    ⟨rightContinuous_smallJumpIntegral G hA hℱ0 hnull0 m i ω t,
      exists_leftLim_smallJumpIntegral G hA hℱ0 hnull0 m i ω t⟩

/-- The compensated integral over the small marks is jointly measurable in the sample point and
the time. -/
theorem measurable_uncurry_smallJumpIntegral (m : ℕ) (i : Fin n) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      smallJumpIntegral G hA hℱ0 hnull0 m i s ω) :=
  measurable_uncurry_cadlagIntegral N G.ℱ G.isPoisson
    (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
    ((G.prog i).indicator_mark (hA m))
    (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') hℱ0 hnull0

/-- A coordinate of the big-jump process is jointly measurable in the sample point and the
time. -/
theorem measurable_uncurry_bigJumpProcess (m : ℕ) (i : Fin n) :
    Measurable (Function.uncurry fun ω s => bigJumpProcess G hA hℱ0 hnull0 m s ω i) := by
  have hM := measurable_uncurry_smallJumpIntegral G hA hℱ0 hnull0 m i
  have hX : Measurable fun p : Ω × ℝ => Xp p.2 p.1 i :=
    (measurable_pi_apply i).comp (G.measurable_path.comp measurable_swap)
  exact hX.sub hM

/-- The big-jump vectors are jointly measurable in the sample point and the time. -/
theorem measurable_uncurry_bigJumpProcess_pi (m : ℕ) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      bigJumpProcess G hA hℱ0 hnull0 m s ω) :=
  measurable_pi_lambda _ fun i => measurable_uncurry_bigJumpProcess G hA hℱ0 hnull0 m i

/-- The squared compensated integral over the small marks is jointly measurable in the sample
point and the time. -/
theorem measurable_uncurry_sq_smallJumpIntegral (m : ℕ) (i : Fin n) :
    Measurable fun q : Ω × ℝ =>
      (‖smallJumpIntegral G hA hℱ0 hnull0 m i q.2 q.1‖₊ : ℝ≥0∞) ^ 2 :=
  (((measurable_uncurry_smallJumpIntegral G hA hℱ0 hnull0 m
    i).nnnorm).coe_nnreal_ennreal).pow_const 2

/-- The squared error between a coordinate of the big-jump process and the path is jointly
measurable in the sample point and the time. -/
theorem measurable_uncurry_sq_bigJumpProcess_sub (m : ℕ) (i : Fin n) :
    Measurable fun q : Ω × ℝ =>
      (‖bigJumpProcess G hA hℱ0 hnull0 m q.2 q.1 i - Xp q.2 q.1 i‖₊ : ℝ≥0∞) ^ 2 := by
  have hB : Measurable fun q : Ω × ℝ => bigJumpProcess G hA hℱ0 hnull0 m q.2 q.1 i :=
    measurable_uncurry_bigJumpProcess G hA hℱ0 hnull0 m i
  have hX : Measurable fun q : Ω × ℝ => Xp q.2 q.1 i :=
    (measurable_pi_apply i).comp (G.measurable_path.comp measurable_swap)
  exact (((hB.sub hX).nnnorm).coe_nnreal_ennreal).pow_const 2

/-- The squared error between a coordinate of the big-jump process and the path is measurable in
the time, at each sample point. -/
theorem measurable_sq_bigJumpProcess_sub_time (m : ℕ) (i : Fin n) (ω : Ω) :
    Measurable fun s : ℝ =>
      (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 := by
  have hB : Measurable fun s : ℝ => bigJumpProcess G hA hℱ0 hnull0 m s ω i :=
    Measurable.of_uncurry_left (measurable_uncurry_bigJumpProcess G hA hℱ0 hnull0 m i)
  have hX : Measurable fun s : ℝ => Xp s ω i :=
    (measurable_pi_apply i).comp
      (G.measurable_path.comp (measurable_id.prodMk measurable_const))
  exact (((hB.sub hX).nnnorm).coe_nnreal_ennreal).pow_const 2

/-- The energy over a bounded window of the error between a coordinate of the big-jump process
and the path is measurable in the sample point. -/
theorem measurable_lintegral_sq_bigJumpProcess_sub (m : ℕ) (i : Fin n) (T : ℝ) :
    Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
  (measurable_uncurry_sq_bigJumpProcess_sub G hA hℱ0 hnull0 m i).lintegral_prod_right'

/-- At nonpositive times the compensated integral over the small marks vanishes almost
surely. -/
theorem smallJumpIntegral_ae_zero (m : ℕ) (i : Fin n) {t : ℝ} (ht : t ≤ 0) :
    smallJumpIntegral G hA hℱ0 hnull0 m i t =ᵐ[P] 0 :=
  (smallJumpIntegral_ae_eq G hA hℱ0 hnull0 m i t).trans
    ((stochasticIntegral_ae_eq_process N G.ℱ G.isPoisson
          (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
          ((G.prog i).indicator_mark (hA m))
          (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') t).trans
      (process_ae_zero_of_nonpos N G.ℱ G.isPoisson _ _ _ _ ht))

end Basic

section Limits

variable (G : JumpIntegrand N coeffs Xp) (hA : ∀ m, MeasurableSet (A m))
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)

/-- The compensated integrals over a shrinking family of marks tend to `0` in `L²`. -/
theorem tendsto_lintegral_sq_smallJumpIntegral (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) (i : Fin n) {t : ℝ} (ht : 0 < t) :
    Tendsto (fun m => ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hrw : ∀ m : ℕ,
      ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖stochasticIntegral N G.ℱ G.isPoisson
            (markCut (A m) (pathJumpCoeff coeffs Xp i))
            (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
            (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro m
    refine lintegral_congr_ae ?_
    filter_upwards [smallJumpIntegral_ae_eq G hA hℱ0 hnull0 m i t] with ω hω
    rw [hω]
  simp_rw [hrw]
  exact tendsto_lintegral_sq_stochasticIntegral_markCut N G.ℱ G.isPoisson
    (pathJumpCoeff coeffs Xp i) (G.meas i) (G.prog i) (G.sq i) A hA hanti hnull ht

/-- **The big-jump processes converge to the path in `L²` at every nonnegative time.** -/
theorem tendsto_lintegral_sq_bigJumpProcess_sub (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) (i : Fin n) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun m => ∫⁻ ω,
        (‖bigJumpProcess G hA hℱ0 hnull0 m t ω i - Xp t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hrw : ∀ m : ℕ,
      ∫⁻ ω, (‖bigJumpProcess G hA hℱ0 hnull0 m t ω i - Xp t ω i‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro m
    refine lintegral_congr fun ω => ?_
    rw [bigJumpProcess_sub, nnnorm_neg]
  simp_rw [hrw]
  rcases eq_or_lt_of_le ht with h0 | h0
  · subst h0
    have hz : ∀ m : ℕ,
        ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i 0 ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
      intro m
      have hae : (fun ω => (‖smallJumpIntegral G hA hℱ0 hnull0 m i 0 ω‖₊ : ℝ≥0∞) ^ 2)
          =ᵐ[P] fun _ => (0 : ℝ≥0∞) := by
        filter_upwards [smallJumpIntegral_ae_zero G hA hℱ0 hnull0 m i (le_refl (0 : ℝ))]
          with ω hω
        simp [hω]
      rw [lintegral_congr_ae hae]
      simp
    simp_rw [hz]
    exact tendsto_const_nhds
  · exact tendsto_lintegral_sq_smallJumpIntegral G hA hℱ0 hnull0 hanti hnull i h0

/-- **Along a subsequence the big-jump processes converge to the path almost surely, in every
coordinate at once.** -/
theorem exists_seq_ae_tendsto_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ i : Fin n,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω i) atTop
          (𝓝 (Xp t ω i)) :=
  LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral
    (u := fun m i ω => bigJumpProcess G hA hℱ0 hnull0 m t ω i) (v := fun i ω => Xp t ω i)
    (fun m i => measurable_bigJumpProcess G hA hℱ0 hnull0 m t i)
    (fun i => measurable_pathCoord G.measurable_path t i)
    fun i => tendsto_lintegral_sq_bigJumpProcess_sub G hA hℱ0 hnull0 hanti hnull i ht

/-- **Along a subsequence the big-jump vectors converge to the path almost surely.** -/
theorem exists_seq_ae_tendsto_bigJumpProcess_pi (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {t : ℝ} (ht : 0 ≤ t) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω) atTop (𝓝 (Xp t ω)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_tendsto_bigJumpProcess G hA hℱ0 hnull0 hanti hnull ht
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae] with ω hω
  exact tendsto_pi_nhds.mpr hω

/-- The `L²` size of the compensated integral over the small marks at a time of the window is
bounded by the energy carried by those marks over the whole window. -/
theorem lintegral_sq_smallJumpIntegral_le (m : ℕ) (i : Fin n) {s T : ℝ}
    (hs : 0 ≤ s) (hsT : s ≤ T) :
    ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rcases eq_or_lt_of_le hs with h0 | h0
  · have hz : ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 := by
      refine (lintegral_congr_ae ?_).trans lintegral_zero
      filter_upwards [smallJumpIntegral_ae_zero G hA hℱ0 hnull0 m i (le_of_eq h0.symm)]
        with ω hω
      simp [hω]
    rw [hz]
    exact zero_le
  · have hrw : ∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, (‖stochasticIntegral N G.ℱ G.isPoisson
            (markCut (A m) (pathJumpCoeff coeffs Xp i))
            (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
            (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') s ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [smallJumpIntegral_ae_eq G hA hℱ0 hnull0 m i s] with ω hω
      rw [hω]
    rw [hrw, isometry_stochasticIntegral N G.ℱ G.isPoisson
      (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
      ((G.prog i).indicator_mark (hA m))
      (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') s h0]
    exact lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hsT)

include G hA in
/-- The energies carried by a shrinking family of marks over a fixed window vanish. -/
theorem tendsto_markCut_energy (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0) (i : Fin n)
    {T : ℝ} (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      atTop (𝓝 0) := by
  have hiso : ∀ m : ℕ, ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
        = ∫⁻ ω, (‖stochasticIntegral N G.ℱ G.isPoisson
            (markCut (A m) (pathJumpCoeff coeffs Xp i))
            (measurable_markCut (G.meas i) (hA m)) ((G.prog i).indicator_mark (hA m))
            (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    intro m
    exact (isometry_stochasticIntegral N G.ℱ G.isPoisson
      (markCut (A m) (pathJumpCoeff coeffs Xp i)) (measurable_markCut (G.meas i) (hA m))
      ((G.prog i).indicator_mark (hA m))
      (fun T' hT' => sq_markCut (G.sq i) (A m) T' hT') T hT).symm
  simp_rw [hiso]
  exact tendsto_lintegral_sq_stochasticIntegral_markCut N G.ℱ G.isPoisson
    (pathJumpCoeff coeffs Xp i) (G.meas i) (G.prog i) (G.sq i) A hA hanti hnull hT

/-- The energy over a bounded window of the compensated integral over the small marks is bounded
by the length of the window times the energy carried by those marks over it. -/
theorem lintegral_window_sq_smallJumpIntegral_le (m : ℕ) (i : Fin n) (T : ℝ) :
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [MeasureTheory.lintegral_lintegral_swap
    (measurable_uncurry_sq_smallJumpIntegral G hA hℱ0 hnull0 m i).aemeasurable]
  calc ∫⁻ s in Set.Icc (0 : ℝ) T,
        (∫⁻ ω, (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T, (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2
            ∂ν ∂volume ∂P) ∂volume := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_Icc fun s hs => ?_
        exact lintegral_sq_smallJumpIntegral_le G hA hℱ0 hnull0 m i hs.1 hs.2
    _ = ENNReal.ofReal T * ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2
            ∂ν ∂volume ∂P := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Icc, sub_zero, mul_comm]

/-- The energy over a bounded window of the error between a coordinate of the big-jump process
and the path is bounded by the length of the window times the energy carried by the small
marks over it. -/
theorem lintegral_window_sq_bigJumpProcess_sub_le (m : ℕ) (i : Fin n) (T : ℝ) :
    ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P
      ≤ ENNReal.ofReal T * ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hnorm : ∀ (s : ℝ) (ω : Ω),
      (‖bigJumpProcess G hA hℱ0 hnull0 m s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2
        = (‖smallJumpIntegral G hA hℱ0 hnull0 m i s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro s ω
    rw [bigJumpProcess_sub, nnnorm_neg]
  simp_rw [hnorm]
  exact lintegral_window_sq_smallJumpIntegral_le G hA hℱ0 hnull0 m i T

/-- **Along a subsequence the big-jump processes converge to the path at almost every time of a
bounded window, almost surely, in every coordinate at once.** -/
theorem exists_seq_ae_ae_tendsto_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω i) atTop
          (𝓝 (Xp s ω i)) := by
  classical
  have hsumTendsto : Tendsto (fun m => ∑ i : Fin n, ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markCut (A m) (pathJumpCoeff coeffs Xp i) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      atTop (𝓝 0) := by
    have hfin := tendsto_finsetSum (Finset.univ : Finset (Fin n))
      fun i _ => tendsto_markCut_energy G hA hanti hnull i hT
    simpa using hfin
  obtain ⟨ms, hmsge, hmslt⟩ :=
    LevyStochCalc.Brownian.Ito.exists_seq_lt_of_tendsto_zero hsumTendsto
  refine ⟨ms, hmsge, ?_⟩
  have hper : ∀ i : Fin n, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω i) atTop
        (𝓝 (Xp s ω i)) := by
    intro i
    have hsum : ∑' k : ℕ, ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω i - Xp s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P
          ≠ ⊤ := by
      refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun k => ?_)
        (lt_top_iff_ne_top.mpr
          (LevyStochCalc.Brownian.Ito.tsum_geometric_inv_two_mul_ne_top (ENNReal.ofReal T)
            ENNReal.ofReal_ne_top)))
      refine (lintegral_window_sq_bigJumpProcess_sub_le G hA hℱ0 hnull0 (ms k) i T).trans ?_
      refine mul_le_mul' le_rfl (le_of_lt (lt_of_le_of_lt ?_ (hmslt k)))
      exact Finset.single_le_sum
        (f := fun j : Fin n => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut (A (ms k)) (pathJumpCoeff coeffs Xp j) ω u e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    filter_upwards [LevyStochCalc.Brownian.Ito.ae_tsum_ne_top_of_lintegral_summable (μ := P)
      (fun k => measurable_lintegral_sq_bigJumpProcess_sub G hA hℱ0 hnull0 (ms k) i T)
      hsum] with ω hω
    filter_upwards [LevyStochCalc.Brownian.Ito.ae_tendsto_zero_of_lintegral_summable
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (fun k => measurable_sq_bigJumpProcess_sub_time G hA hℱ0 hnull0 (ms k) i ω) hω] with s hs
    exact LevyStochCalc.Brownian.Ito.tendsto_of_tendsto_sq_enorm hs
  filter_upwards [MeasureTheory.ae_all_iff.mpr hper] with ω hω
  exact MeasureTheory.ae_all_iff.mpr hω

/-- **Along a subsequence the big-jump vectors converge to the path at almost every time of a
bounded window, almost surely.** -/
theorem exists_seq_ae_ae_tendsto_bigJumpProcess_pi (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω) atTop (𝓝 (Xp s ω)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_ae_tendsto_bigJumpProcess G hA hℱ0 hnull0 hanti hnull hT
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hae] with ω hω
  filter_upwards [hω] with s hs
  exact tendsto_pi_nhds.mpr hs

/-- **The drift integrals along the big-jump processes, with the drift clamped at the levels of
the subsequence, converge to the drift integral along the path, at almost every sample
point.** -/
theorem exists_seq_ae_tendsto_drift_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T)
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ p : Fin n, Tendsto (fun k => ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω)
            * LevyStochCalc.Brownian.Ito.clampDrift b (ms k) p ω s ∂volume) atTop
        (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (Xp s ω) * b p ω s ∂volume)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_ae_tendsto_bigJumpProcess_pi G hA hℱ0 hnull0 hanti hnull hT
  refine ⟨ms, hms, ?_⟩
  exact LevyStochCalc.Brownian.Ito.ae_tendsto_drift_clamp hf'c hf'bd hbm hbq
    (Y := fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k)) (X := Xp)
    (fun k => measurable_uncurry_bigJumpProcess_pi G hA hℱ0 hnull0 (ms k))
    (G.measurable_path.comp measurable_swap) hms hae

/-- **The quadratic-variation integrals along the big-jump processes, with the diffusion matrix
clamped at the levels of the subsequence, converge to the quadratic-variation integral along the
path, at almost every sample point.** -/
theorem exists_seq_ae_tendsto_quadVar_bigJumpProcess (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T)
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hf''c : Continuous f'')
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p l, Measurable (Function.uncurry (H p l)))
    (hq : ∀ (p : Fin n) (l : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p l ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      ∀ᵐ ω ∂P, ∀ p q : Fin n, Tendsto (fun k => ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv₂ f'' p q (bigJumpProcess G hA hℱ0 hnull0 (ms k) s ω)
            * ∑ l : Fin d, LevyStochCalc.Brownian.Ito.clampCoeff H (ms k) p l ω s
                * LevyStochCalc.Brownian.Ito.clampCoeff H (ms k) q l ω s ∂volume) atTop
        (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv₂ f'' p q (Xp s ω) * ∑ l : Fin d, H p l ω s * H q l ω s ∂volume)) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_ae_tendsto_bigJumpProcess_pi G hA hℱ0 hnull0 hanti hnull hT
  refine ⟨ms, hms, ?_⟩
  exact LevyStochCalc.Brownian.Ito.ae_tendsto_quadVar_clamp hf''c hK₂0 hf''bd hm hq
    (Y := fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k)) (X := Xp)
    (fun k => measurable_uncurry_bigJumpProcess_pi G hA hℱ0 hnull0 (ms k)) hms hae

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
    (hA : ∀ m, MeasurableSet (A m))
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → G.ℱ.rightCont 0 ≤ G.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[G.ℱ 0] s)
    (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0)
    {t : ℝ} (ht : 0 ≤ t) {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    ∃ ms : ℕ → ℕ, (∀ k : ℕ, k ≤ ms k) ∧
      (∀ᵐ ω ∂P,
        Tendsto (fun k => bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω) atTop (𝓝 (Xp t ω))) ∧
      ∀ᵐ ω ∂P, Tendsto (fun k => u t (bigJumpProcess G hA hℱ0 hnull0 (ms k) t ω)) atTop
        (𝓝 (u t (Xp t ω))) := by
  obtain ⟨ms, hms, hae⟩ :=
    exists_seq_ae_tendsto_bigJumpProcess_pi G hA hℱ0 hnull0 hanti hnull ht
  refine ⟨ms, hms, hae, ?_⟩
  filter_upwards [hae] with ω hω
  exact tendsto_comp_of_tendsto hu t hω

end LevyStochCalc.Ito.SmallJump
