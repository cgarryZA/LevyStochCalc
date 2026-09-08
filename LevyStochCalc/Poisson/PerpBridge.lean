/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedRange
import LevyStochCalc.Poisson.CompensatedPullOut

/-!
# The perp bridge for the compensated integral

A weight measurable before a horizon does not see the compensated integral beyond it: the
increment is a martingale increment, and conditioning on the horizon kills it. So orthogonality
to every admissible integrand over `[0, T]` extends to every admissible integrand over any
larger horizon. This is the marked counterpart of the Brownian perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Congr

/-- **Two admissible integrands agreeing over the horizon integrate to the same thing there.** -/
theorem stochasticIntegral_ae_congr (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (φ ψ : Ω → ℝ → E → ℝ)
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hψp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hφq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) (h : ∀ ω s e, s ∈ Set.Icc (0 : ℝ) T → φ ω s e = ψ ω s e) :
    stochasticIntegral N ℱ hℱ φ hφm hφp hφq T
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T := by
  have hiso := itoIsometry_diff_compensated N ℱ hℱ φ ψ hφm hψm hφp hψp hφq hψq T hT
  have hzero : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) = 0 := by
    have hin : ∀ ω : Ω, (∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume) = 0 := by
      intro ω
      have heq : ∀ s ∈ Set.Icc (0 : ℝ) T,
          (∫⁻ e, (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) = 0 := by
        intro s hs
        have hpt : ∀ e : E, (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 = 0 := by
          intro e
          rw [h ω s e hs, sub_self]
          simp
        simp [hpt]
      rw [setLIntegral_congr_fun measurableSet_Icc heq]
      simp
    simp [hin]
  rw [hzero] at hiso
  have hφL : MemLp (stochasticIntegral N ℱ hℱ φ hφm hφp hφq T) 2 P :=
    stochasticIntegral_memLp N ℱ hℱ φ hφm hφp hφq T
  have hψL : MemLp (stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T) 2 P :=
    stochasticIntegral_memLp N ℱ hℱ ψ hψm hψp hψq T
  have hae : AEMeasurable (fun ω => (‖stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (((hφL.sub hψL).aestronglyMeasurable.aemeasurable).nnnorm).coe_nnreal_ennreal.pow_const 2
  filter_upwards [(lintegral_eq_zero_iff' hae).mp hiso] with ω hω
  have h2 : (‖stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω‖₊ : ℝ≥0∞) = 0 :=
    (pow_eq_zero_iff (n := 2) (by norm_num)).mp hω
  have h3 : stochasticIntegral N ℱ hℱ φ hφm hφp hφq T ω
      - stochasticIntegral N ℱ hℱ ψ hψm hψp hψq T ω = 0 := by simpa using h2
  linarith

end Congr

section Clip

namespace MarkedHorizonIntegrand

/-- An admissible integrand over a larger horizon, clipped to `[0, T]`. -/
noncomputable def clip {R : ℝ} (G : MarkedHorizonIntegrand P ν ℱ R) {T : ℝ} (hTR : T ≤ R) :
    MarkedHorizonIntegrand P ν ℱ T where
  toFun := fun ω s e => (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun ω s e) s
  measurable_uncurry := by
    have hrw : (fun p : Ω × ℝ × E =>
          (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun p.1 p.2.1 p.2.2) p.2.1)
        = {p : Ω × ℝ × E | p.2.1 ∈ Set.Icc (0 : ℝ) T}.indicator
          (fun p => G.toFun p.1 p.2.1 p.2.2) := by
      funext p
      by_cases hp : p.2.1 ∈ Set.Icc (0 : ℝ) T
      · have hp' : p ∈ {q : Ω × ℝ × E | q.2.1 ∈ Set.Icc (0 : ℝ) T} := hp
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      · have hp' : p ∉ {q : Ω × ℝ × E | q.2.1 ∈ Set.Icc (0 : ℝ) T} := hp
        rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
    rw [hrw]
    exact G.measurable_uncurry.indicator (measurable_snd.fst measurableSet_Icc)
  progressive :=
    Probability.MarkedProgressivelyMeasurable.indicator_time G.progressive measurableSet_Icc
  vanishing := fun _ _ _ hs => Set.indicator_of_notMem hs _
  energy_ne_top := by
    have heq : markedEnergy P ν T (fun ω s e =>
        (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun ω s e) s)
        = markedEnergy P ν T G.toFun := by
      simp only [markedEnergy]
      refine lintegral_congr fun ω => ?_
      refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      refine lintegral_congr fun e => ?_
      rw [Set.indicator_of_mem hs]
    rw [heq]
    refine ne_top_of_le_ne_top G.energy_ne_top ?_
    simp only [markedEnergy]
    refine lintegral_mono fun ω => ?_
    exact lintegral_mono_set (Set.Icc_subset_Icc le_rfl hTR)

/-- The clipped integrand's integral is the integral of the original over the shorter horizon. -/
theorem integral_clip (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {R : ℝ}
    (G : MarkedHorizonIntegrand P ν ℱ R) {T : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    (G.clip hTR).integral N hℱ
      =ᵐ[P] stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
        G.sq_int_global T :=
  stochasticIntegral_ae_congr N hℱ (G.clip hTR).toFun G.toFun (G.clip hTR).measurable_uncurry
    G.measurable_uncurry (G.clip hTR).progressive G.progressive (G.clip hTR).sq_int_global
    G.sq_int_global hT (by
      intro ω s e hs
      show (Set.Icc (0 : ℝ) T).indicator (fun _ => G.toFun ω s e) s = G.toFun ω s e
      exact Set.indicator_of_mem hs _)

end MarkedHorizonIntegrand

end Clip

section Bridge

/-- **A weight measurable before `T` does not see the increment of the compensated integral after
`T`.** -/
theorem integral_mul_increment_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) (φ : Ω → ℝ → E → ℝ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {z : Ω → ℝ} (hz2 : MemLp z 2 P) {T t : ℝ}
    (hzm : AEStronglyMeasurable[ℱ T] z P) (hTt : T ≤ t) :
    ∫ ω, z ω * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
      - stochasticIntegral N ℱ hℱ φ hm hp hq T ω) ∂P = 0 := by
  haveI : SigmaFinite (P.trim (ℱ.rightCont.le T)) := by infer_instance
  set M := stochasticIntegral N ℱ hℱ φ hm hp hq with hMdef
  have hmart : MeasureTheory.Martingale M ℱ.rightCont P :=
    martingale_stochasticIntegral_rightCont N ℱ hℱ φ hm hp hq
  have hMLp : ∀ u : ℝ, MemLp (M u) 2 P := fun u => stochasticIntegral_memLp N ℱ hℱ φ hm hp hq u
  have hMint : ∀ u : ℝ, Integrable (M u) P := fun u => (hMLp u).integrable (by norm_num)
  have hgLp : MemLp (fun ω => M t ω - M T ω) 2 P := (hMLp t).sub (hMLp T)
  have hgint : Integrable (fun ω => M t ω - M T ω) P := (hMint t).sub (hMint T)
  have hzm' : AEStronglyMeasurable[ℱ.rightCont T] z P := hzm.mono (ℱ.le_rightCont T)
  have hprod : Integrable (fun ω => z ω * (M t ω - M T ω)) P :=
    integrable_mul_of_memLp_two hz2 hgLp
  have hpull := condExp_mul_of_aestronglyMeasurable_left (m := ℱ.rightCont T)
    (f := z) (g := fun ω => M t ω - M T ω) hzm' hprod hgint
  have hcond : P[(fun ω => M t ω - M T ω) | ℱ.rightCont T] =ᵐ[P] 0 := by
    have h1 : P[(fun ω => M t ω - M T ω) | ℱ.rightCont T]
        =ᵐ[P] P[M t | ℱ.rightCont T] - P[M T | ℱ.rightCont T] :=
      condExp_sub (hMint t) (hMint T) _
    have h2 : P[M t | ℱ.rightCont T] =ᵐ[P] M T := hmart.2 T t hTt
    have h3 : P[M T | ℱ.rightCont T] = M T :=
      condExp_of_stronglyMeasurable (ℱ.rightCont.le T) (hmart.1 T) (hMint T)
    rw [h3] at h1
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, Pi.sub_apply, e2, sub_self]
    rfl
  have key : ∫ ω, z ω * (M t ω - M T ω) ∂P
      = ∫ ω, (P[(fun ω => z ω * (M t ω - M T ω)) | ℱ.rightCont T]) ω ∂P :=
    (integral_condExp (ℱ.rightCont.le T)).symm
  have hpull' : P[(fun ω => z ω * (M t ω - M T ω)) | ℱ.rightCont T]
      =ᵐ[P] z * P[(fun ω => M t ω - M T ω) | ℱ.rightCont T] := hpull
  rw [key]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hpull', hcond] with ω e1 e2
  rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]

/-- **The marked perp bridge.** A square-integrable weight measurable before `T` and orthogonal
to the compensated integral of every admissible integrand over `[0, T]` is orthogonal to the
compensated integral of every admissible integrand over any larger horizon. -/
theorem integral_mul_integral_eq_zero (N : PoissonRandomMeasure P ν)
    (hℱ : IsPoissonFiltration N ℱ) {T : ℝ} (hT : 0 < T) {z : Ω → ℝ} (hz2 : MemLp z 2 P)
    (hzm : AEStronglyMeasurable[ℱ T] z P)
    (hperp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, z ω * G.integral N hℱ ω ∂P = 0)
    {R : ℝ} (hTR : T ≤ R) (G : MarkedHorizonIntegrand P ν ℱ R) :
    ∫ ω, z ω * G.integral N hℱ ω ∂P = 0 := by
  set M := stochasticIntegral N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global with hMdef
  have hMLp : ∀ u : ℝ, MemLp (M u) 2 P := fun u =>
    stochasticIntegral_memLp N ℱ hℱ G.toFun G.measurable_uncurry G.progressive
      G.sq_int_global u
  have hclipzero : ∫ ω, z ω * M T ω ∂P = 0 := by
    have h := hperp (G.clip hTR)
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [MarkedHorizonIntegrand.integral_clip N hℱ G hT hTR] with ω e
    rw [e]
  have hincr := integral_mul_increment_eq_zero N hℱ G.toFun G.measurable_uncurry G.progressive
    G.sq_int_global hz2 hzm hTR
  have hint1 : Integrable (fun ω => z ω * M T ω) P :=
    integrable_mul_of_memLp_two hz2 (hMLp T)
  have hint2 : Integrable (fun ω => z ω * (M R ω - M T ω)) P :=
    integrable_mul_of_memLp_two hz2 ((hMLp R).sub (hMLp T))
  have hrw : (fun ω => z ω * M R ω)
      = fun ω => z ω * M T ω + z ω * (M R ω - M T ω) := by funext ω; ring
  show ∫ ω, z ω * M R ω ∂P = 0
  rw [show (∫ ω, z ω * M R ω ∂P)
      = ∫ ω, (z ω * M T ω + z ω * (M R ω - M T ω)) ∂P from by rw [hrw],
    integral_add hint1 hint2, hclipzero, hincr, add_zero]

end Bridge

end LevyStochCalc.Poisson.Compensated
