/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyProcess
import LevyStochCalc.Ito.SmallJumpProcess
import LevyStochCalc.Poisson.CompensatedLinear
import LevyStochCalc.Probability.DoobContinuous
import LevyStochCalc.Martingale.CadlagModification

/-!
# Truncating the jumps of a jump diffusion at one mark set

Restricting the jump coefficient of a jump diffusion to a measurable set of marks `A` splits it
into two coefficient bundles, and the compensated integral of an admissible integrand splits
accordingly. Subtracting the everywhere-càdlàg modification of the compensated integral over `A`
from the path leaves the *big-jump path*, which carries the drift, the diffusion and the jumps
outside `A`.

## Main definitions

* `LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.markCutγ` — the coefficient bundle with the jump
  coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.SdeData` — the filtration and admissibility data with which a jump
  diffusion satisfies its SDE.
* `LevyStochCalc.Ito.BigJump.cutJumpIntegral` — the everywhere-càdlàg modification of the
  compensated integral of the jump coefficient restricted to a set of marks.
* `LevyStochCalc.Ito.BigJump.bigJumpPath` — the path with that integral subtracted.

## Main statements

* `LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl` — the compensated integral of
  an integrand is the sum of the compensated integrals of its two mark cuts.
* `LevyStochCalc.Ito.BigJump.lintegral_sq_iSup_bigJumpPath_lt_top` — the big-jump path has
  square-integrable supremum over every bounded window.
* `LevyStochCalc.Ito.BigJump.isItoLevyProcess_bigJumpPath` — the big-jump path is an Itô–Lévy
  process whose drift and diffusion are those of the jump diffusion along its own path and whose
  jump integrand is the jump coefficient restricted to the complement of the cut.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Poisson.Compensated

namespace LevyStochCalc.Ito.Setting

universe v

variable {n d : ℕ} {E : Type v}

/-- The coefficient bundle with the jump coefficient restricted to a set of marks: `γ` is left
unchanged on `A` and replaced by `0` off `A`. -/
noncomputable def JumpDiffusionCoeffs.markCutγ (coeffs : JumpDiffusionCoeffs n d E) (A : Set E) :
    JumpDiffusionCoeffs n d E where
  μ := coeffs.μ
  σ := coeffs.σ
  γ := fun s y e => A.indicator (fun _ => coeffs.γ s y e) e

@[simp] theorem JumpDiffusionCoeffs.markCutγ_μ (coeffs : JumpDiffusionCoeffs n d E)
    (A : Set E) : (coeffs.markCutγ A).μ = coeffs.μ := rfl

@[simp] theorem JumpDiffusionCoeffs.markCutγ_σ (coeffs : JumpDiffusionCoeffs n d E)
    (A : Set E) : (coeffs.markCutγ A).σ = coeffs.σ := rfl

@[simp] theorem JumpDiffusionCoeffs.markCutγ_γ (coeffs : JumpDiffusionCoeffs n d E) (A : Set E)
    (s : ℝ) (y : Fin n → ℝ) (e : E) :
    (coeffs.markCutγ A).γ s y e = A.indicator (fun _ => coeffs.γ s y e) e := rfl

/-- A coordinate of the restricted jump coefficient is the restriction of that coordinate. -/
theorem JumpDiffusionCoeffs.markCutγ_γ_apply (coeffs : JumpDiffusionCoeffs n d E) (A : Set E)
    (s : ℝ) (y : Fin n → ℝ) (e : E) (i : Fin n) :
    (coeffs.markCutγ A).γ s y e i = A.indicator (fun _ => coeffs.γ s y e i) e := by
  by_cases he : e ∈ A <;> simp [he]

/-- The jump coefficient is the sum of its restrictions to a set of marks and to its
complement. -/
theorem JumpDiffusionCoeffs.markCutγ_add_markCutγ_compl (coeffs : JumpDiffusionCoeffs n d E)
    (A : Set E) (s : ℝ) (y : Fin n → ℝ) (e : E) :
    coeffs.γ s y e = (coeffs.markCutγ A).γ s y e + (coeffs.markCutγ Aᶜ).γ s y e := by
  by_cases he : e ∈ A <;> simp [he]

/-- The restricted jump coefficient is supported on the cut. -/
theorem JumpDiffusionCoeffs.markCutγ_eq_zero (coeffs : JumpDiffusionCoeffs n d E) (A : Set E) :
    ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∉ A → (coeffs.markCutγ A).γ s y e = 0 :=
  fun _ _ _ he => Set.indicator_of_notMem he _

end LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.BigJump

universe u v

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.SmallJump

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}

section Split

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)

/-- The compensated integral of an integrand determines the compensated integral of any
integrand equal to it. -/
theorem stochasticIntegral_congr_fun {φ ψ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hψp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hψq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h : φ = ψ) (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hφm hφp hφq T
      = stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T := by
  subst h; rfl

omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- An integrand is the sum of its restrictions to a set of marks and to its complement. -/
theorem markCut_add_markCut_compl (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    markCut A φ ω s e + markCut Aᶜ φ ω s e = φ ω s e := by
  by_cases he : e ∈ A <;> simp [markCut, he]

include hℱ in
/-- **The compensated integral splits along a measurable set of marks.** -/
theorem stochasticIntegral_markCut_add_compl (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {A : Set E} (hA : MeasurableSet A) (T : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ (markCut A φ)
            (measurable_markCut hm hA) (hp.indicator_mark hA)
            (fun T' hT' => sq_markCut hq A T' hT') T ω
          + stochasticIntegral N ℱ hℱ (markCut Aᶜ φ)
            (measurable_markCut hm hA.compl) (hp.indicator_mark hA.compl)
            (fun T' hT' => sq_markCut hq Aᶜ T' hT') T ω := by
  rcases le_or_gt T 0 with hT | hT
  · have hzero : ∀ (ψ : Ω → ℝ → E → ℝ)
        (h1 : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
        (h2 : Probability.MarkedProgressivelyMeasurable ℱ ψ)
        (h3 : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
        stochasticIntegral N ℱ hℱ ψ h1 h2 h3 T =ᵐ[P] 0 := fun ψ h1 h2 h3 =>
      (stochasticIntegral_ae_eq_process N ℱ hℱ ψ h1 h2 h3 T).trans
        (process_ae_zero_of_nonpos N ℱ hℱ ψ h1 h2 h3 hT)
    filter_upwards [hzero φ hm hp hq,
      hzero (markCut A φ) (measurable_markCut hm hA) (hp.indicator_mark hA)
        (fun T' hT' => sq_markCut hq A T' hT'),
      hzero (markCut Aᶜ φ) (measurable_markCut hm hA.compl) (hp.indicator_mark hA.compl)
        (fun T' hT' => sq_markCut hq Aᶜ T' hT')] with ω h0 h1 h2
    simp [h0, h1, h2]
  · have hpt := markCut_add_markCut_compl (Ω := Ω) (E := E) A φ
    have hfun : (fun ω s e => markCut A φ ω s e + markCut Aᶜ φ ω s e) = φ := by
      funext ω s e; exact hpt ω s e
    have hma : Measurable fun p : Ω × ℝ × E =>
        markCut A φ p.1 p.2.1 p.2.2 + markCut Aᶜ φ p.1 p.2.1 p.2.2 :=
      (measurable_markCut hm hA).add (measurable_markCut hm hA.compl)
    have hpa : Probability.MarkedProgressivelyMeasurable ℱ
        (fun ω s e => markCut A φ ω s e + markCut Aᶜ φ ω s e) := by
      simp only [hpt]; exact hp
    have hqa : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖markCut A φ ω s e + markCut Aᶜ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
      simp only [hpt]; exact hq
    have hadd := stochasticIntegral_add N ℱ hℱ
      (φ₁ := markCut A φ) (φ₂ := markCut Aᶜ φ)
      (measurable_markCut hm hA) (measurable_markCut hm hA.compl)
      (hp.indicator_mark hA) (hp.indicator_mark hA.compl)
      (fun T' hT' => sq_markCut hq A T' hT') (fun T' hT' => sq_markCut hq Aᶜ T' hT')
      hma hpa hqa hT
    rw [← stochasticIntegral_congr_fun N ℱ hℱ hma hpa hqa hm hp hq hfun T]
    exact hadd

end Split

section Data

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The filtration and admissibility data with which a jump diffusion satisfies its SDE: the
contents of the `is_solution` field, named. -/
structure SdeData (X : JumpDiffusion W N coeffs x₀) where
  /-- The filtration the integrands are progressively measurable for. -/
  ℱ : Filtration ℝ ‹MeasurableSpace Ω›
  /-- Every coordinate of `W` is a Brownian motion for `ℱ`. -/
  isBrownian : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ
  /-- `N` is a Poisson random measure for `ℱ`. -/
  isPoisson : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ
  /-- The diffusion coefficient along the path is jointly measurable, entrywise. -/
  σ_meas : ∀ i : Fin n, ∀ j : Fin d,
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j)
  /-- The diffusion coefficient along the path is progressively measurable, entrywise. -/
  σ_prog : ∀ i : Fin n, ∀ j : Fin d,
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j
  /-- The diffusion coefficient along the path has finite energy on every bounded window. -/
  σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤
  /-- The jump coefficient along the path is jointly measurable, coordinatewise. -/
  γ_meas : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => pathJumpCoeff coeffs X.X i p.1 p.2.1 p.2.2
  /-- The jump coefficient along the path is marked progressively measurable. -/
  γ_prog : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ (pathJumpCoeff coeffs X.X i)
  /-- The jump coefficient along the path has finite energy on every bounded window. -/
  γ_sq : ∀ i : Fin n, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖pathJumpCoeff coeffs X.X i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤
  /-- The SDE integral equation, almost surely at every nonnegative time. -/
  sde : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
    X.X t ω i = x₀ i
      + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
      + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
          W ℱ isBrownian (fun s ω => coeffs.σ s (X.X s ω) i)
          (fun j => σ_meas i j) (fun j => σ_prog i j) (fun j => σ_sq i j) t ω
      + stochasticIntegral N ℱ isPoisson (pathJumpCoeff coeffs X.X i)
          (γ_meas i) (γ_prog i) (γ_sq i) t ω

/-- A jump-diffusion solution carries SDE data. -/
theorem nonempty_sdeData (X : JumpDiffusion W N coeffs x₀) : Nonempty (SdeData X) := by
  obtain ⟨ℱ, hℱW, hℱN, hσm, hσp, hσq, hγm, hγp, hγq, heq⟩ := X.is_solution
  exact ⟨⟨ℱ, hℱW, hℱN, hσm, hσp, hσq, hγm, hγp, hγq, heq⟩⟩

/-- The jump-integrand data underlying the SDE data. -/
def SdeData.toJumpIntegrand {X : JumpDiffusion W N coeffs x₀} (S : SdeData X) :
    JumpIntegrand N coeffs X.X :=
  ⟨S.ℱ, S.isPoisson, X.measurable_path, S.γ_meas, S.γ_prog, S.γ_sq⟩

end Data

section Path

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- The everywhere-càdlàg modification of the compensated integral of the `i`-th coordinate of
the jump coefficient along the path, restricted to the marks in `A`. -/
noncomputable def cutJumpIntegral (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (i : Fin n) : ℝ → Ω → ℝ :=
  cadlagIntegralPi N S.ℱ S.isPoisson hℱ0 hnull0
    (fun j => markCut A (pathJumpCoeff coeffs X.X j))
    (fun j => measurable_markCut (S.γ_meas j) hA)
    (fun j => (S.γ_prog j).indicator_mark hA)
    (fun j T' hT' => sq_markCut (S.γ_sq j) A T' hT') i

/-- The path of a jump diffusion with the jumps carried by the marks in `A` removed. -/
noncomputable def bigJumpPath (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (t : ℝ) (ω : Ω) : Fin n → ℝ :=
  fun i => X.X t ω i - cutJumpIntegral S hA hℱ0 hnull0 i t ω

variable (S : SdeData X) {A : Set E} (hA : MeasurableSet A)
  (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t)
  (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)

/-- The truncated compensated integral agrees almost surely, at each time, with the `L²`
Itô–Lévy integral of the mark cut. -/
theorem cutJumpIntegral_ae_eq (i : Fin n) (t : ℝ) :
    cutJumpIntegral S hA hℱ0 hnull0 i t
      =ᵐ[P] stochasticIntegral N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
        (measurable_markCut (S.γ_meas i) hA) ((S.γ_prog i).indicator_mark hA)
        (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') t :=
  cadlagIntegral_ae_eq N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((S.γ_prog i).indicator_mark hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0 t

/-- The truncated compensated integral is adapted to the right-continuous filtration. -/
theorem adapted_cutJumpIntegral (i : Fin n) :
    Adapted S.ℱ.rightCont (cutJumpIntegral S hA hℱ0 hnull0 i) :=
  cadlagIntegral_adapted N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((S.γ_prog i).indicator_mark hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0

/-- The truncated compensated integral is measurable at each time. -/
theorem measurable_cutJumpIntegral (i : Fin n) (t : ℝ) :
    Measurable (cutJumpIntegral S hA hℱ0 hnull0 i t) :=
  (adapted_cutJumpIntegral S hA hℱ0 hnull0 i t).mono (S.ℱ.rightCont.le t) le_rfl

/-- Every path of the truncated compensated integral is right-continuous. -/
theorem rightContinuous_cutJumpIntegral (i : Fin n) (ω : Ω) (t : ℝ) :
    Tendsto (fun s => cutJumpIntegral S hA hℱ0 hnull0 i s ω) (𝓝[>] t)
      (𝓝 (cutJumpIntegral S hA hℱ0 hnull0 i t ω)) :=
  cadlagIntegral_rightContinuous N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((S.γ_prog i).indicator_mark hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0 ω t

/-- Every path of the truncated compensated integral has a left limit at every time. -/
theorem exists_leftLim_cutJumpIntegral (i : Fin n) (ω : Ω) (t : ℝ) :
    ∃ L : ℝ, Tendsto (fun s => cutJumpIntegral S hA hℱ0 hnull0 i s ω) (𝓝[<] t) (𝓝 L) :=
  cadlagIntegral_exists_leftLim N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((S.γ_prog i).indicator_mark hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0 ω t

/-- The truncated compensated integral is jointly measurable in the sample point and the
time. -/
theorem measurable_uncurry_cutJumpIntegral (i : Fin n) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      cutJumpIntegral S hA hℱ0 hnull0 i s ω) :=
  measurable_uncurry_cadlagIntegral N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((S.γ_prog i).indicator_mark hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') hℱ0 hnull0

/-- The truncated compensated integral is a martingale for the right-continuous filtration. -/
theorem martingale_cutJumpIntegral (i : Fin n) :
    MeasureTheory.Martingale (cutJumpIntegral S hA hℱ0 hnull0 i) S.ℱ.rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_stochasticIntegral_rightCont N S.ℱ S.isPoisson
      (markCut A (pathJumpCoeff coeffs X.X i)) (measurable_markCut (S.γ_meas i) hA)
      ((S.γ_prog i).indicator_mark hA) (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT'))
    (fun t => (adapted_cutJumpIntegral S hA hℱ0 hnull0 i t).stronglyMeasurable)
    (cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i)

/-- At nonpositive times the truncated compensated integral vanishes almost surely. -/
theorem cutJumpIntegral_ae_zero (i : Fin n) {t : ℝ} (ht : t ≤ 0) :
    cutJumpIntegral S hA hℱ0 hnull0 i t =ᵐ[P] 0 :=
  (cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i t).trans
    ((stochasticIntegral_ae_eq_process N S.ℱ S.isPoisson
        (markCut A (pathJumpCoeff coeffs X.X i)) (measurable_markCut (S.γ_meas i) hA)
        ((S.γ_prog i).indicator_mark hA)
        (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') t).trans
      (process_ae_zero_of_nonpos N S.ℱ S.isPoisson _ _ _ _ ht))

/-- A coordinate of the big-jump path is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_bigJumpPath_coord (i : Fin n) :
    Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      bigJumpPath S hA hℱ0 hnull0 t ω i) := by
  have hX : Measurable fun q : ℝ × Ω => X.X q.1 q.2 i :=
    (measurable_pi_apply i).comp X.measurable_path
  have hC : Measurable fun q : ℝ × Ω => cutJumpIntegral S hA hℱ0 hnull0 i q.1 q.2 :=
    (measurable_uncurry_cutJumpIntegral S hA hℱ0 hnull0 i).comp measurable_swap
  exact hX.sub hC

/-- The big-jump path is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_bigJumpPath :
    Measurable (Function.uncurry (bigJumpPath S hA hℱ0 hnull0)) :=
  measurable_pi_lambda _ fun i => measurable_uncurry_bigJumpPath_coord S hA hℱ0 hnull0 i

/-- The big-jump path starts at the initial value of the jump diffusion. -/
theorem bigJumpPath_ae_initial : ∀ᵐ ω ∂P, bigJumpPath S hA hℱ0 hnull0 0 ω = x₀ := by
  filter_upwards [X.initial_value, MeasureTheory.ae_all_iff.mpr
    fun i : Fin n => cutJumpIntegral_ae_zero S hA hℱ0 hnull0 i (le_refl (0 : ℝ))] with ω h0 hc
  funext i
  show X.X 0 ω i - cutJumpIntegral S hA hℱ0 hnull0 i 0 ω = x₀ i
  rw [hc i, h0]
  simp

/-- The big-jump path is almost surely càdlàg on the SDE time domain. -/
theorem bigJumpPath_ae_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    Tendsto (fun s => bigJumpPath S hA hℱ0 hnull0 s ω) (𝓝[>] t)
        (𝓝 (bigJumpPath S hA hℱ0 hnull0 t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Tendsto (fun s => bigJumpPath S hA hℱ0 hnull0 s ω i) (𝓝[<] t) (𝓝 L) := by
  filter_upwards [X.cadlag_paths] with ω hω t ht
  refine ⟨tendsto_pi_nhds.mpr fun i => ?_, fun i => ?_⟩
  · exact (((continuous_apply i).tendsto _).comp (hω t ht).1).sub
      (rightContinuous_cutJumpIntegral S hA hℱ0 hnull0 i ω t)
  · obtain ⟨L, hL⟩ := (hω t ht).2 i
    obtain ⟨M, hM⟩ := exists_leftLim_cutJumpIntegral S hA hℱ0 hnull0 i ω t
    exact ⟨L - M, hL.sub hM⟩

omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A coordinate of the jump coefficient restricted to a set of marks, along a path, is the
restriction of that coordinate along the path. -/
theorem pathJumpCoeff_markCutγ (A' : Set E) (Xp : ℝ → Ω → (Fin n → ℝ)) (i : Fin n) :
    pathJumpCoeff (coeffs.markCutγ A') Xp i = markCut A' (pathJumpCoeff coeffs Xp i) := by
  funext ω s e
  simpa [pathJumpCoeff, markCut] using
    JumpDiffusionCoeffs.markCutγ_γ_apply coeffs A' s (Xp s ω) e i

include S hA in
/-- The jump coefficient outside the cut, along the path, is jointly measurable. -/
theorem measurable_pathJumpCoeff_markCutγ_compl (i : Fin n) :
    Measurable fun p : Ω × ℝ × E =>
      pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i p.1 p.2.1 p.2.2 := by
  rw [pathJumpCoeff_markCutγ]; exact measurable_markCut (S.γ_meas i) hA.compl

include S hA in
/-- The jump coefficient outside the cut, along the path, is marked progressively
measurable. -/
theorem markedProg_pathJumpCoeff_markCutγ_compl (i : Fin n) :
    Probability.MarkedProgressivelyMeasurable S.ℱ
      (pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i) := by
  rw [pathJumpCoeff_markCutγ]; exact (S.γ_prog i).indicator_mark hA.compl

include S in
/-- The jump coefficient outside the cut, along the path, has finite energy on every bounded
window. -/
theorem sq_pathJumpCoeff_markCutγ_compl (i : Fin n) : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  rw [pathJumpCoeff_markCutγ]; exact fun T' hT' => sq_markCut (S.γ_sq i) Aᶜ T' hT'

/-- **The big-jump path is an Itô–Lévy process** whose drift and diffusion are those of the jump
diffusion along its own path and whose jump integrand is the jump coefficient restricted to the
complement of the cut. -/
theorem isItoLevyProcess_bigJumpPath (i : Fin n) :
    IsItoLevyProcess W N S.ℱ S.isBrownian S.isPoisson
      (fun t ω => bigJumpPath S hA hℱ0 hnull0 t ω i) (fun _ => x₀ i)
      (fun s ω => coeffs.μ s (X.X s ω) i) (fun s ω => coeffs.σ s (X.X s ω) i)
      (pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i) := by
  have hbridge : pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i
      = markCut Aᶜ (pathJumpCoeff coeffs X.X i) := pathJumpCoeff_markCutγ Aᶜ X.X i
  have hγm := measurable_pathJumpCoeff_markCutγ_compl S hA i
  have hγp := markedProg_pathJumpCoeff_markCutγ_compl S hA i
  have hγq := sq_pathJumpCoeff_markCutγ_compl (A := A) S i
  refine ⟨measurable_uncurry_bigJumpPath_coord S hA hℱ0 hnull0 i, fun j => S.σ_meas i j,
    fun j => S.σ_prog i j, fun j => S.σ_sq i j, hγm, hγp, hγq, ?_⟩
  have hcg : stochasticIntegral N S.ℱ S.isPoisson
        (pathJumpCoeff (coeffs.markCutγ Aᶜ) X.X i) hγm hγp hγq
      = stochasticIntegral N S.ℱ S.isPoisson (markCut Aᶜ (pathJumpCoeff coeffs X.X i))
        (measurable_markCut (S.γ_meas i) hA.compl) ((S.γ_prog i).indicator_mark hA.compl)
        (fun T' hT' => sq_markCut (S.γ_sq i) Aᶜ T' hT') := by
    funext t
    exact stochasticIntegral_congr_fun N S.ℱ S.isPoisson hγm hγp hγq _ _ _ hbridge t
  intro t ht
  filter_upwards [S.sde t ht, cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i t,
    stochasticIntegral_markCut_add_compl N S.ℱ S.isPoisson (pathJumpCoeff coeffs X.X i)
      (S.γ_meas i) (S.γ_prog i) (S.γ_sq i) hA t] with ω h1 h2 h3
  show X.X t ω i - cutJumpIntegral S hA hℱ0 hnull0 i t ω = _
  rw [h1 i, h2, h3, hcg]
  ring

/-- The energy of the truncated compensated integral at the horizon is the energy carried by the
cut. -/
theorem lintegral_sq_cutJumpIntegral (i : Fin n) {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖cutJumpIntegral S hA hℱ0 hnull0 i T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖markCut A (pathJumpCoeff coeffs X.X i) ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← isometry_stochasticIntegral N S.ℱ S.isPoisson (markCut A (pathJumpCoeff coeffs X.X i))
    (measurable_markCut (S.γ_meas i) hA) ((S.γ_prog i).indicator_mark hA)
    (fun T' hT' => sq_markCut (S.γ_sq i) A T' hT') T hT]
  refine lintegral_congr_ae ?_
  filter_upwards [cutJumpIntegral_ae_eq S hA hℱ0 hnull0 i T] with ω hω
  rw [hω]

/-- The truncated compensated integral has finite second moment of its supremum over every
bounded window. -/
theorem lintegral_sq_iSup_cutJumpIntegral_lt_top (i : Fin n) {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ m, (‖Probability.dyadicRunMax
        (cutJumpIntegral S hA hℱ0 hnull0 i) T m ω‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤ := by
  refine lt_of_le_of_lt (Probability.lintegral_iSup_dyadicRunMax_sq_le
    (martingale_cutJumpIntegral S hA hℱ0 hnull0 i) hT.le) ?_
  rw [lintegral_sq_cutJumpIntegral S hA hℱ0 hnull0 i hT]
  exact ENNReal.mul_lt_top (by norm_num) (sq_markCut (S.γ_sq i) A T hT)

/-- **The big-jump path has square-integrable supremum over every bounded window.** -/
theorem lintegral_sq_iSup_bigJumpPath_lt_top {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T,
      ∑ i, (‖bigJumpPath S hA hℱ0 hnull0 (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  classical
  set B : Ω → ℝ≥0∞ := fun ω => ∑ i : Fin n, (⨆ m, (‖Probability.dyadicRunMax
    (cutJumpIntegral S hA hℱ0 hnull0 i) T m ω‖₊ : ℝ≥0∞)) ^ 2 with hBdef
  have hBmeas : Measurable B :=
    Finset.measurable_sum _ fun i _ =>
      (Measurable.iSup fun m => Probability.measurable_enorm_dyadicRunMax
        (fun t => measurable_cutJumpIntegral S hA hℱ0 hnull0 i t) T m).pow_const 2
  have hcut : ∀ (ω : Ω) (i : Fin n) (t : Set.Icc (0 : ℝ) T),
      (‖cutJumpIntegral S hA hℱ0 hnull0 i (t : ℝ) ω‖₊ : ℝ≥0∞)
        ≤ ⨆ m, (‖Probability.dyadicRunMax
            (cutJumpIntegral S hA hℱ0 hnull0 i) T m ω‖₊ : ℝ≥0∞) := by
    intro ω i t
    rw [← Probability.iSup_enorm_eq_iSup_dyadicRunMax hT.le
      (fun r => rightContinuous_cutJumpIntegral S hA hℱ0 hnull0 i ω r)]
    exact le_iSup (fun u : Set.Icc (0 : ℝ) T =>
      (‖cutJumpIntegral S hA hℱ0 hnull0 i (u : ℝ) ω‖₊ : ℝ≥0∞)) t
  have hstep : ∀ ω : Ω,
      (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖bigJumpPath S hA hℱ0 hnull0 (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2)
        ≤ 2 * (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) + 2 * B ω := by
    intro ω
    refine iSup_le fun t => ?_
    have hterm : ∀ i : Fin n,
        (‖bigJumpPath S hA hℱ0 hnull0 (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2
          ≤ 2 * ((‖X.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2
            + (⨆ m, (‖Probability.dyadicRunMax
                (cutJumpIntegral S hA hℱ0 hnull0 i) T m ω‖₊ : ℝ≥0∞)) ^ 2) := by
      intro i
      refine le_trans (LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) ?_
      exact mul_le_mul' le_rfl (add_le_add le_rfl (pow_le_pow_left' (hcut ω i t) 2))
    calc ∑ i, (‖bigJumpPath S hA hℱ0 hnull0 (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2
        ≤ ∑ i : Fin n, 2 * ((‖X.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2
            + (⨆ m, (‖Probability.dyadicRunMax
                (cutJumpIntegral S hA hℱ0 hnull0 i) T m ω‖₊ : ℝ≥0∞)) ^ 2) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = 2 * (∑ i, (‖X.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) + 2 * B ω := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, mul_add, hBdef]
      _ ≤ 2 * (⨆ u : Set.Icc (0 : ℝ) T, ∑ i, (‖X.X (u : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) + 2 * B ω := by
          gcongr
          exact le_iSup (fun u : Set.Icc (0 : ℝ) T =>
            ∑ i, (‖X.X (u : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) t
  calc ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T,
        ∑ i, (‖bigJumpPath S hA hℱ0 hnull0 (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, (2 * (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2)
          + 2 * B ω) ∂P := lintegral_mono hstep
    _ = 2 * (∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X.X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P)
          + 2 * ∫⁻ ω, B ω ∂P := by
        rw [lintegral_add_right _ (hBmeas.const_mul 2),
          lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤),
          lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
    _ < ⊤ := by
        refine ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (by norm_num) (X.sup_L2 T hT), ?_⟩
        refine ENNReal.mul_lt_top (by norm_num) ?_
        rw [hBdef, lintegral_finsetSum _ fun i _ =>
          (Measurable.iSup fun m => Probability.measurable_enorm_dyadicRunMax
            (fun r => measurable_cutJumpIntegral S hA hℱ0 hnull0 i r) T m).pow_const 2]
        exact ENNReal.sum_lt_top.mpr fun i _ =>
          lintegral_sq_iSup_cutJumpIntegral_lt_top S hA hℱ0 hnull0 i hT

end Path

section Diffusion

variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {X : JumpDiffusion W N coeffs x₀}

/-- The multidimensional Brownian Itô integral depends only on its integrand. -/
theorem brownianIntegral_congr_fun (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    {Z Z' : ℝ → Ω → (Fin d → ℝ)}
    (hm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hp : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω j)
    (hq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm' : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => Z' s ω j))
    (hp' : ∀ j : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => Z' s ω j)
    (hq' : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (h : Z = Z') (T : ℝ) :
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
        W ℱ hℱ Z hm hp hq T
      = LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
        W ℱ hℱ Z' hm' hp' hq' T := by
  subst h; rfl

end Diffusion

end LevyStochCalc.Ito.BigJump

