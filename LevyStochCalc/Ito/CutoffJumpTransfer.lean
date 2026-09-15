/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSideCompensator
import LevyStochCalc.Ito.CutoffPathAgreement
import LevyStochCalc.Ito.CompensatedLocality
import LevyStochCalc.Ito.StabilityEstimate
import LevyStochCalc.Ito.LeftLimIntegrandRegularity
import LevyStochCalc.Ito.JumpCoefficientPredictableZeroExt

/-!
# The jump side of the Itô–Lévy formula under the state cut-off

Along a path confined to a ball the state cut-off moves the jump increment and the
compensator-drift integrand by the same quantity, and that quantity vanishes at every atom of the
random measure. An integrand vanishing at the atoms has compensated integral minus its
compensator, so the two moves cancel: the *sum* of the compensated integral of the jump increment
and the compensator-drift integral is the same for a state function and for its cut-off, even
though neither term is.

## Main definitions

* `jumpIncrLeft` — the jump increment of a state function along a path, read at the left limits.

## Main statements

* `measurable_jumpIncrLeft`, `markedProgressivelyMeasurable_jumpIncrLeft`,
  `markedPredictable_zeroExtPos_jumpIncrLeft` — its admissibility and the predictability of its
  zero extension.
* `ae_jumpSide_cutoffFun₂_eq` — the jump side is unchanged by the cut-off on the event that the
  path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Ito.JumpFormula LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.JumpSplitting LevyStochCalc.Ito.JumpSide
open LevyStochCalc.Probability

universe u v

section Integrand

variable {Ω : Type u} {E : Type v} {n d : ℕ}

/-- The jump increment of a state function along a path, read at the left limits of the path. -/
noncomputable def jumpIncrLeft (w : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : Setting.JumpDiffusionCoeffs n d E) (Xp : ℝ → Ω → Fin n → ℝ)
    (ω : Ω) (s : ℝ) (e : E) : ℝ :=
  w s (leftLimPathAt Xp s ω + coeffs.γ s (leftLimPathAt Xp s ω) e)
    - w s (leftLimPathAt Xp s ω)

end Integrand

section Regularity

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n d : ℕ}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
  {w : ℝ → (Fin n → ℝ) → ℝ}

/-- The state increment across a jump is jointly measurable in the time, the state and the
mark. -/
theorem measurable_stateIncr (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2) :
    Measurable fun q : ℝ × (Fin n → ℝ) × E =>
      w q.1 (q.2.1 + coeffs.γ q.1 q.2.1 q.2.2) - w q.1 q.2.1 := by
  have h1 : Measurable fun q : ℝ × (Fin n → ℝ) × E =>
      ((q.1, q.2.1 + coeffs.γ q.1 q.2.1 q.2.2) : ℝ × (Fin n → ℝ)) :=
    measurable_fst.prodMk (measurable_snd.fst.add hγ)
  have h2 : Measurable fun q : ℝ × (Fin n → ℝ) × E => ((q.1, q.2.1) : ℝ × (Fin n → ℝ)) :=
    measurable_fst.prodMk measurable_snd.fst
  exact (hw.measurable.comp h1).sub (hw.measurable.comp h2)

/-- The jump increment along the left limits of a jointly measurable path with left limits is
jointly measurable. -/
theorem measurable_jumpIncrLeft (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    Measurable fun p : Ω × ℝ × E => jumpIncrLeft w coeffs Xp p.1 p.2.1 p.2.2 := by
  have hΛ : Measurable fun p : Ω × ℝ × E => leftLimPathAt Xp p.2.1 p.1 :=
    (measurable_uncurry_leftLimPathAt hXm hleft).comp
      (measurable_snd.fst.prodMk measurable_fst)
  exact (measurable_stateIncr hw hγ).comp
    (measurable_snd.fst.prodMk (hΛ.prodMk measurable_snd.snd))

/-- The jump increment along the left limits of an adapted path with left limits is marked
progressively measurable. -/
theorem markedProgressivelyMeasurable_jumpIncrLeft
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    MarkedProgressivelyMeasurable ℱ (jumpIncrLeft w coeffs Xp) :=
  markedProgressivelyMeasurable_comp_state
    (fun j => progressivelyMeasurable_leftLimPathAt hℱ0 hXadapt hleft j)
    (F := fun s y e => w s (y + coeffs.γ s y e) - w s y) (measurable_stateIncr hw hγ)

variable {ν : Measure E} [SigmaFinite ν]

/-- The zero extension of the jump increment along the left limits of an adapted path with left
limits is marked predictable. -/
theorem markedPredictable_zeroExtPos_jumpIncrLeft
    (Xp : ℝ → Ω → Fin n → ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hw : Continuous (Function.uncurry w))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    MarkedPredictable ℱ ν (zeroExtPos (jumpIncrLeft w coeffs Xp)) :=
  markedPredictable_zeroExtPos_comp_leftLimPathAt Xp ℱ hXadapt
    (fun ω t _ j => hleft ω t j)
    (F := fun s y e => w s (y + coeffs.γ s y e) - w s y) (measurable_stateIncr hw hγ)

end Regularity

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

/-- **The cut-off leaves the jump side of the Itô–Lévy formula unchanged** on the event that the
path stays in the ball. The cut-off moves the jump increment and the compensator-drift integrand
by the same quantity, that quantity vanishes at every atom of the random measure, and an
integrand vanishing at the atoms has compensated integral minus its compensator, so the two moves
cancel. Neither term is unchanged on its own. -/
theorem ae_jumpSide_cutoffFun₂_eq
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : IsPoissonFiltration N ℱ)
    {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ))
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hXleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L))
    (hmv : Measurable fun p : Ω × ℝ × E =>
      jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp p.1 p.2.1 p.2.2)
    (hpv : MarkedProgressivelyMeasurable ℱ
      (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp))
    (hqv : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤)
    (hmu : Measurable fun p : Ω × ℝ × E => jumpIncrLeft u coeffs Xp p.1 p.2.1 p.2.2)
    (hpu : MarkedProgressivelyMeasurable ℱ (jumpIncrLeft u coeffs Xp))
    (hqu : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖jumpIncrLeft u coeffs Xp ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hCdv : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ)))
          coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hCdu : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => compensatorDriftIntegrand u
          coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν))
    (hjump : ∀ j : ℕ, ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ k, θ k ∈ Set.Ioc (0 : ℝ) T ∧ ε k ∈ spanningSets ν j) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, g p ∂(N.N ω)
        = ∑ k : Fin K, g (θ k, ε k)) ∧
      ∀ k : Fin K,
        Xp (θ k) ω
          = leftLimPathAt Xp (θ k) ω + coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k)) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      Compensated.stochasticIntegral N ℱ hℱN
            (jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp) hmv hpv hqv T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
              compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
                (leftLimPathAt Xp q.1 ω) q.2 ∂(referenceIntensity ν)
        = Compensated.stochasticIntegral N ℱ hℱN (jumpIncrLeft u coeffs Xp) hmu hpu hqu T ω
          + ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
              compensatorDriftIntegrand u coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2
                ∂(referenceIntensity ν) := by
  classical
  set Ψ : Ω → ℝ → E → ℝ := fun ω s e =>
    jumpIncrLeft (cutoffFun₂ u (2 * (m : ℝ))) coeffs Xp ω s e - jumpIncrLeft u coeffs Xp ω s e
    with hΨdef
  have hvC : ContDiff ℝ 2 (Function.uncurry (cutoffFun₂ u (2 * (m : ℝ)))) :=
    contDiff_uncurry_cutoffFun₂ hu _
  have hms : Measurable fun p : Ω × ℝ × E => Ψ p.1 p.2.1 p.2.2 := hmv.sub hmu
  have hps : MarkedProgressivelyMeasurable ℱ Ψ := markedProgressivelyMeasurable_sub hpv hpu
  have hqs : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖Ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' => LevyStochCalc.Ito.Stability.lintegral_sq_sub_marked_lt_top hmv hmu
      (hqv T' hT') (hqu T' hT')
  have hpred : MarkedPredictable ℱ ν (zeroExtPos Ψ) :=
    markedPredictable_zeroExtPos_comp_leftLimPathAt Xp ℱ hXadapt
      (fun ω t _ j => hXleft ω t j)
      (F := fun s y e => (cutoffFun₂ u (2 * (m : ℝ)) s (y + coeffs.γ s y e)
          - cutoffFun₂ u (2 * (m : ℝ)) s y) - (u s (y + coeffs.γ s y e) - u s y))
      ((measurable_stateIncr hvC.continuous hγ).sub (measurable_stateIncr hu.continuous hγ))
  -- the difference vanishes at the atoms of every finite-intensity window
  have hatoms : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m → ∀ j : ℕ,
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, zeroExtPos Ψ ω q.1 q.2 ∂(N.N ω) = 0 := by
    have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
        ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j, zeroExtPos Ψ ω q.1 q.2
          ∂(N.N ω) = 0 := by
      refine MeasureTheory.ae_all_iff.mpr fun j => ?_
      filter_upwards [ae_setIntegral_jumpIncrement_sub_eq_zero coeffs N Xp (spanningSets ν j)
        (measurableSet_spanningSets ν j) (measure_spanningSets_lt_top ν j).ne u hm hTm (hjump j)
        (Filter.Eventually.of_forall fun ω t i => hXleft ω t i)]
        with ω hω hG
      refine Eq.trans ?_ (hω hG)
      refine setIntegral_congr_fun (measurableSet_Ioc.prod (measurableSet_spanningSets ν j))
        fun q hq => ?_
      exact zeroExtPos_of_pos Ψ ω hq.1.1 q.2
    filter_upwards [hall] with ω hω hG j
    exact hω j hG
  -- the difference is the difference of the compensator-drift integrands, hence integrable
  have hpt : ∀ (ω : Ω), ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      ∀ q : ℝ × E, q ∈ Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E) →
        zeroExtPos Ψ ω q.1 q.2
          = compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
              (leftLimPathAt Xp q.1 ω) q.2
            - compensatorDriftIntegrand u coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 := by
    intro ω hG q hq
    rw [zeroExtPos_of_pos Ψ ω hq.1.1 q.2]
    exact jumpIncrement_sub_eq_compensatorDrift_sub_of_boundedPath u hm hTm hG hq.1
      (fun i => hXleft ω q.1 i) q.2
  have hint : ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      IntegrableOn (fun q : ℝ × E => zeroExtPos Ψ ω q.1 q.2)
        (Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E)) (referenceIntensity ν) := by
    filter_upwards [hCdv, hCdu] with ω h1 h2 hG
    exact ((h1 hG).sub (h2 hG)).congr_fun (fun q hq => (hpt ω hG q hq).symm)
      (measurableSet_Ioc.prod MeasurableSet.univ)
  -- the three identities
  have hmainΨ := stochasticIntegral_eq_neg_setIntegral_of_atoms_zero_spanning N ℱ hℱN
    (zeroExtPos Ψ) (measurable_zeroExtPos hms) (markedProgressivelyMeasurable_zeroExtPos hps)
    (energy_zeroExtPos_lt_top hqs) hpred (fun ω s e hs => zeroExtPos_of_nonpos Ψ ω hs e) hT
    (Brownian.Ito.boundedPathSet Xp T m) hint hatoms
  have hze := compensated_zeroExtPos_congr N ℱ hℱN Ψ hms hps hqs hT
  have hsub := stochasticIntegral_sub N hℱN hmv hmu hpv hpu hqv hqu hms hps hqs hT
  filter_upwards [hmainΨ, hze, hsub, hCdv, hCdu] with ω h1 h2 h3 h4 h5 hG
  have hI : ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E), zeroExtPos Ψ ω q.1 q.2
        ∂(referenceIntensity ν)
      = (∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
          compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ q.1
            (leftLimPathAt Xp q.1 ω) q.2 ∂(referenceIntensity ν))
        - ∫ q in Set.Ioc (0 : ℝ) T ×ˢ (Set.univ : Set E),
            compensatorDriftIntegrand u coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2
              ∂(referenceIntensity ν) := by
    rw [← integral_sub (h4 hG) (h5 hG)]
    exact setIntegral_congr_fun (measurableSet_Ioc.prod MeasurableSet.univ)
      fun q hq => hpt ω hG q hq
  rw [h1 hG, hI] at h2
  linarith [h2, h3]

end Transfer

end LevyStochCalc.Ito.CutoffPath
