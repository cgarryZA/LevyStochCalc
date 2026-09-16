/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.CutoffGlobalBounds
import LevyStochCalc.Ito.CutoffJumpTransfer
import LevyStochCalc.Ito.JumpFormulaContinuityC12
import LevyStochCalc.Ito.C12Product

/-!
# The time–space cut-off of a `C^{1,2}` state function

The time–space cut-off of radius `R` multiplies a state function by a jointly `C²` factor, so the
cut-off of a `C^{1,2}` function is again of class `C^{1,2}`. Its time derivative, gradient and
Hessian vanish outside the closed ball of radius `2R` and are continuous, hence are bounded
everywhere by one constant. Along a path confined to a ball the cut-off leaves the jump side of
the Itô–Lévy formula — the compensated integral of the jump increment plus the compensator-drift
integral — unchanged, and that transfer needs of the state function only the joint continuity of
the function and of its cut-off.

## Main statements

* `LevyStochCalc.Ito.JumpFormulaCutoff.exists_globalBound_cutoffFun₂_c12` — one constant bounds
  the time derivative, every gradient entry and every Hessian entry of the cut-off of a `C^{1,2}`
  function, at every time and every state.
* `LevyStochCalc.Ito.CutoffPath.ae_jumpSide_cutoffFun₂_eq_c12` — for a `C^{1,2}` state function
  the jump side is unchanged by the cut-off on the event that the path stays in the ball.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormulaCutoff

open LevyStochCalc.Ito.JumpFormula

variable {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- **The cut-off of a `C^{1,2}` state function has globally bounded derivatives.** One constant
bounds its time derivative, every entry of its gradient and every entry of its Hessian, at every
time and every state. -/
theorem exists_globalBound_cutoffFun₂_c12 (hu : IsC12 u) {R : ℝ} (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧ (∀ s x, |timeDeriv (cutoffFun₂ u R) s x| ≤ K) ∧
      (∀ s x i, |gradient (cutoffFun₂ u R) s x i| ≤ K) ∧
      (∀ s x i j, |hessian (cutoffFun₂ u R) s x i j| ≤ K) := by
  obtain ⟨K, hK0, hKt, hKg, hKh⟩ :=
    exists_bound_on_box_c12 (isC12_cutoffFun₂ hu R) (-(2 * R)) (2 * R) (2 * R)
  refine ⟨K, hK0, fun s x => ?_, fun s x i => ?_, fun s x i j => ?_⟩
  · by_cases hz : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖
    · rw [timeDeriv_cutoffFun₂_eq_zero hR hz, abs_zero]
      exact hK0
    · have hz' : ‖((s, x) : ℝ × (Fin n → ℝ))‖ ≤ 2 * R := not_lt.mp hz
      simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hz'
      exact hKt s x (abs_le.mp hz'.1) hz'.2
  · by_cases hz : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖
    · rw [gradient_cutoffFun₂_eq_zero hR hz i, abs_zero]
      exact hK0
    · have hz' : ‖((s, x) : ℝ × (Fin n → ℝ))‖ ≤ 2 * R := not_lt.mp hz
      simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hz'
      exact hKg s x (abs_le.mp hz'.1) hz'.2 i
  · by_cases hz : 2 * R < ‖((s, x) : ℝ × (Fin n → ℝ))‖
    · rw [hessian_cutoffFun₂_eq_zero hR hz i j, abs_zero]
      exact hK0
    · have hz' : ‖((s, x) : ℝ × (Fin n → ℝ))‖ ≤ 2 * R := not_lt.mp hz
      simp only [Prod.norm_def, max_le_iff, Real.norm_eq_abs] at hz'
      exact hKh s x (abs_le.mp hz'.1) hz'.2 i j

end LevyStochCalc.Ito.JumpFormulaCutoff

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Ito.JumpFormula LevyStochCalc.Ito.JumpFormulaCutoff
open LevyStochCalc.Ito.JumpSplitting LevyStochCalc.Ito.JumpSide
open LevyStochCalc.Probability

universe u v

section Transfer

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
/-- **The cut-off leaves the jump side of the Itô–Lévy formula unchanged** on the event that the
path stays in the ball, for a `C^{1,2}` state function. The cut-off moves the jump increment and
the compensator-drift integrand by the same quantity, that quantity vanishes at every atom of the
random measure, and an integrand vanishing at the atoms has compensated integral minus its
compensator, so the two moves cancel. Neither term is unchanged on its own. -/
theorem ae_jumpSide_cutoffFun₂_eq_c12
    (N : PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : IsPoissonFiltration N ℱ)
    {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : IsC12 u)
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
  have hvC : IsC12 (cutoffFun₂ u (2 * (m : ℝ))) := isC12_cutoffFun₂ hu _
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
        u hm hTm (hjump j)
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
