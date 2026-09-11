/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaGeneralShift

/-!
# Itô's formula between two stopping times of unrestricted range

A stopping time is approximated from above by the stopping time that stops at the first point of
a uniform grid strictly beyond it, which takes finitely many values below the horizon. Itô's
formula for the increment of a path between two such discretisations, for a `C²` function
translated by a random vector, passes to the limit: the boundary term converges by continuity of
the function and of the path, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of two
increments is at most twice the sum of the two energies, hence almost surely along a subsequence
common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStop` — the σ-algebra of a stopping time is
  contained in that of its upward grid discretisation.
* `LevyStochCalc.Brownian.Ito.tendsto_stopped_gridStop` — the integrand cut off at the grid
  discretisations converges pointwise at every positive time of the window.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_gridStop` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_sub_gridStop` — the increments cut off at the
  grid discretisations converge in the energy of the window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift` — Itô's formula for the increment of a
  path between two stopping times of unrestricted range.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section GridMeasurableSpace

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The σ-algebra of a stopping time is contained in the σ-algebra of the stopping time that stops
at the first point of a uniform grid strictly beyond it. -/
theorem measurableSpace_le_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) (t : ℝ) (m : ℕ) :
    hσ.measurableSpace ≤ (isStoppingTime_gridStop σ hσ t m).measurableSpace :=
  hσ.measurableSpace_mono _ fun ω => le_gridStop σ t m ω

/-- A mark measurable at a stopping time is measurable at its upward grid discretisation. -/
theorem measurable_gridStop_measurableSpace {α : Type*} [MeasurableSpace α]
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (t : ℝ) (m : ℕ) :
    Measurable[(isStoppingTime_gridStop σ hσ t m).measurableSpace] c :=
  hc.mono (measurableSpace_le_gridStop hσ t m) le_rfl

end GridMeasurableSpace

section PointwiseLimit

variable {Ω : Type u}

/-- The integrand cut off at the upward grid discretisations of a stopping time converges to the
integrand cut off at that stopping time, at every positive time of the window. -/
theorem tendsto_stopped_gridStop (υ : Ω → WithTop ℝ) (A : Ω → ℝ → ℝ) (ω : Ω)
    {t s : ℝ} (ht : 0 < t) (hs : 0 < s) (hst : s ≤ t) :
    Filter.Tendsto (fun m : ℕ => Probability.stopped (gridStop υ t m) A ω s) Filter.atTop
      (𝓝 (Probability.stopped υ A ω s)) := by
  by_cases hυ : ((s : ℝ) : WithTop ℝ) ≤ υ ω
  · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun m _ => ?_
    have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop υ t m ω := le_trans hυ (le_gridStop υ t m ω)
    simp [Probability.stopped, h1, hυ]
  · rw [not_le] at hυ
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (eventually_gridStop_lt υ ht ω hs hst hυ)
    refine tendsto_atTop_of_eventually_const (i₀ := N) fun m hmN => ?_
    have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ gridStop υ t m ω := not_le.mpr (hN m hmN)
    have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ υ ω := not_le.mpr hυ
    simp [Probability.stopped, h1, h2]

end PointwiseLimit

section LebesgueTerm

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The increment between the upward grid discretisations of two stopping times of an integrand
dominated by a multiple of an integrable coefficient converges on a bounded half-open window. -/
theorem tendsto_setIntegral_stopped_sub_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {A : Ω → ℝ → ℝ}
    (hmA : Measurable (Function.uncurry A)) (D : Ω → ℝ → ℝ) (K : ℝ)
    (hAD : ∀ ω s, |A ω s| ≤ K * |D ω s|) {t : ℝ} (ht : 0 < t) {ω : Ω}
    (hint : MeasureTheory.IntegrableOn (fun s => D ω s) (Set.Ioc (0 : ℝ) t) volume) :
    Filter.Tendsto (fun m : ℕ => ∫ s in Set.Ioc (0 : ℝ) t,
        (Probability.stopped (gridStop τ t m) A ω s
          - Probability.stopped (gridStop σ t m) A ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) t,
        (Probability.stopped τ A ω s - Probability.stopped σ A ω s) ∂volume)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => 2 * (K * |D ω s|)) (fun m => ?_) ((hint.abs.const_mul K).const_mul 2)
    (fun m => ?_) ?_
  · exact (Measurable.of_uncurry_left (measurable_uncurry_stopped_sub
      (isStoppingTime_gridStop σ hσ t m) (isStoppingTime_gridStop τ hτ t m)
      hmA)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs]
    refine le_trans (abs_stopped_sub_stopped_le _ _ A ω s) ?_
    exact mul_le_mul_of_nonneg_left (hAD ω s) (by norm_num)
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with s hs
    exact (tendsto_stopped_gridStop τ A ω ht hs.1 hs.2).sub
      (tendsto_stopped_gridStop σ A ω ht hs.1 hs.2)

end LebesgueTerm

section EnergyTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- An integrand whose square is dominated pointwise by twice the sum of the squares of two others
has energy at most twice the sum of their energies. -/
theorem lintegral_energy_le_two_mul (K H₁ H₂ : Ω → ℝ → ℝ)
    (hbound : ∀ ω s, (‖K ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2)
    (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂)) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have e1 := measurable_energyDensity hm₁ T
  have e2 := measurable_energyDensity hm₂ T
  rw [← lintegral_const_mul 2 e1, ← lintegral_const_mul 2 e2,
    ← lintegral_add_left (e1.const_mul 2)]
  refine lintegral_mono fun ω => ?_
  have h1 : Measurable fun s => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp (hm₁.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
  have h2 : Measurable fun s => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 :=
    (((measurable_nnnorm.comp (hm₂.comp measurable_prodMk_left)).coe_nnreal_ennreal).pow_const 2)
  rw [← lintegral_const_mul 2 h1, ← lintegral_const_mul 2 h2,
    ← lintegral_add_left (h1.const_mul 2)]
  exact lintegral_mono fun s => hbound ω s

/-- The increments cut off at the upward grid discretisations of two stopping times converge, in
the energy of the window, to the increment cut off at those stopping times. -/
theorem tendsto_energy_stopped_sub_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {G : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry G)) {t : ℝ} (ht : 0 < t)
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto (fun m : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Probability.stopped (gridStop τ t m) G ω s
              - Probability.stopped (gridStop σ t m) G ω s)
            - (Probability.stopped τ G ω s - Probability.stopped σ G ω s)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by
  have hEτ := tendsto_energy_stopped_gridStop hτ hm ht hq
  have hEσ := tendsto_energy_stopped_gridStop hσ hm ht hq
  have hub : Filter.Tendsto (fun m : ℕ =>
      2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖Probability.stopped (gridStop τ t m) G ω s
            - Probability.stopped τ G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖Probability.stopped (gridStop σ t m) G ω s
              - Probability.stopped σ G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) := by
    have h1 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hEτ (Or.inr (by simp))
    have h2 := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hEσ (Or.inr (by simp))
    rw [mul_zero] at h1 h2
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
    (fun _ => zero_le) fun m => ?_
  refine lintegral_energy_le_two_mul
    (fun ω s => (Probability.stopped (gridStop τ t m) G ω s
        - Probability.stopped (gridStop σ t m) G ω s)
      - (Probability.stopped τ G ω s - Probability.stopped σ G ω s))
    (fun ω s => Probability.stopped (gridStop τ t m) G ω s - Probability.stopped τ G ω s)
    (fun ω s => Probability.stopped (gridStop σ t m) G ω s - Probability.stopped σ G ω s)
    (fun ω s => ?_) ?_ ?_ t
  · rw [show (Probability.stopped (gridStop τ t m) G ω s
          - Probability.stopped (gridStop σ t m) G ω s)
        - (Probability.stopped τ G ω s - Probability.stopped σ G ω s)
      = (Probability.stopped (gridStop τ t m) G ω s - Probability.stopped τ G ω s)
        - (Probability.stopped (gridStop σ t m) G ω s
            - Probability.stopped σ G ω s) from by ring]
    exact le_trans (sq_nnnorm_sub_le_two_mul _ _) (le_of_eq (by ring))
  · exact (Probability.measurable_uncurry_stopped (isStoppingTime_gridStop τ hτ t m) hm).sub
      (Probability.measurable_uncurry_stopped hτ hm)
  · exact (Probability.measurable_uncurry_stopped (isStoppingTime_gridStop σ hσ t m) hm).sub
      (Probability.measurable_uncurry_stopped hσ hm)

end EnergyTerm

section GridShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **Itô's formula for the increment of a path between two stopping times of unrestricted range,
for a function translated by a random vector, from the identities along the upward grid
discretisations of the two times.** -/
theorem itoFormula_between_gridShift
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXc : ∀ ω, Continuous fun s : ℝ => X s ω)
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ K₂ : ℝ} (hK₁ : ∀ (p : Fin n) (z : Fin n → ℝ), |coordDeriv f' p z| ≤ K₁)
    (hK₂ : ∀ (p q : Fin n) (z : Fin n → ℝ) (ω : Ω) (s : ℝ),
      |coordDeriv₂ f'' p q z| * |∑ k : Fin d, H p k ω s * H q k ω s|
        ≤ K₂ * |∑ k : Fin d, H p k ω s * H q k ω s|)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable c)
    (hbint : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (fun s => bdrift p ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped (gridStop τ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped (gridStop σ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hbase : ∀ m : ℕ,
      (fun ω : Ω => f (X (clipTime (gridStop τ T m) T ω) ω + c ω)
          - f (X (clipTime (gridStop σ T m) T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (gridStop τ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped (gridStop σ T m)
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped (gridStop τ T m)
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped (gridStop σ T m)
                        (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSm m p k) (hpSm m p k) (hqSm m p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (gridStop τ T m)
                  (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped (gridStop σ T m)
                    (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                      * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hfc : Continuous f := Differentiable.continuous fun z => (hf z).differentiableAt
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hf''c : Continuous f'' := by
    have h1 : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
    have h2 : f'' = fderiv ℝ f' := funext fun z => (hf' z).fderiv.symm
    rw [h2, h1]
    exact ((hfC.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous
  have hXcm : Measurable (Function.uncurry fun ω s => X s ω + c ω) :=
    hXm.add (hc.comp measurable_fst)
  have hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) :=
    fun p k => ((continuous_coordDeriv hf'c p).measurable.comp hXcm).mul (hHm p k)
  have hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) :=
    fun p => ((continuous_coordDeriv hf'c p).measurable.comp hXcm).mul (hbm p)
  have hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) := by
    intro p q
    refine ((continuous_coordDeriv₂ hf''c p q).measurable.comp hXcm).mul ?_
    exact Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hqG : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coordDeriv f' p (X s ω + c ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    refine energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hHs p k) T hT
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hdrift : ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun m : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (gridStop τ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - Probability.stopped (gridStop σ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)) := by
    filter_upwards [hbint] with ω hω p
    refine tendsto_setIntegral_stopped_sub_gridStop hσ hτ (hmD p) (bdrift p) K₁
      (fun ω s => ?_) hT (hω p)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hquad : ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun m : ℕ =>
      ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (gridStop τ T m)
            (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped (gridStop σ T m)
              (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)) := by
    filter_upwards [hQint] with ω hω p q
    refine tendsto_setIntegral_stopped_sub_gridStop hσ hτ (hmQ p q)
      (fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) K₂ (fun ω s => ?_) hT (hω p q)
    rw [abs_mul]
    exact hK₂ p q _ ω s
  obtain ⟨ms, hmsge, hSI⟩ := exists_seq_ae_tendsto_stochInt_of_tendsto_energy
    (fun i : Fin n × Fin d => W.W i.2) ℱ' (fun i => hcoord i.2)
    (fun m i ω s => Probability.stopped (gridStop τ T m)
        (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
      - Probability.stopped (gridStop σ T m)
          (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)
    (fun i ω s => Probability.stopped τ
        (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
      - Probability.stopped σ
          (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)
    (fun m i => hmSm m i.1 i.2) (fun m i => hpSm m i.1 i.2) (fun m i => hqSm m i.1 i.2)
    (fun i => hmSc i.1 i.2) (fun i => hpSc i.1 i.2) (fun i => hqSc i.1 i.2) hT
    (fun i => tendsto_energy_stopped_sub_gridStop hσ hτ (hmG i.1 i.2) hT (hqG i.1 i.2))
  have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
  refine ae_eq_of_tendsto_comp_of_forall_ae_eq ms hbase ?_ ?_
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hXτ : Filter.Tendsto (fun m : ℕ => X (clipTime (gridStop τ T m) T ω) ω + c ω)
        Filter.atTop (𝓝 (X (clipTime τ T ω) ω + c ω)) :=
      (((hXc ω).tendsto _).comp (tendsto_clipTime_gridStop τ hτ0 hT ω)).add tendsto_const_nhds
    have hXσ : Filter.Tendsto (fun m : ℕ => X (clipTime (gridStop σ T m) T ω) ω + c ω)
        Filter.atTop (𝓝 (X (clipTime σ T ω) ω + c ω)) :=
      (((hXc ω).tendsto _).comp (tendsto_clipTime_gridStop σ hσ0 hT ω)).add tendsto_const_nhds
    exact ((hfc.continuousAt.tendsto.comp hXτ).sub
      (hfc.continuousAt.tendsto.comp hXσ)).comp hmsTop
  · filter_upwards [hdrift, hquad, hSI] with ω h1 h2 h3
    refine ((tendsto_finsetSum _ fun p _ => (h1 p).comp hmsTop).add
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun k _ => h3 (p, k))).add ?_
    exact (tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun q _ => (h2 p q).comp hmsTop).const_mul _

end GridShift

end LevyStochCalc.Brownian.Ito
