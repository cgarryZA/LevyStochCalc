/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaRandomShift
import LevyStochCalc.Ito.ItoFormulaSimpleShift

/-!
# Itô's formula for an increment translated by a general random vector

A random vector approached pointwise by random vectors for which Itô's formula between two
stopping times already holds carries the formula itself: the boundary term converges by
continuity of the function, the two Lebesgue terms converge along almost every path by
domination, and the stochastic term converges in `L²` because the energy of the difference of
two increments is at most four times the energy of the difference of the integrands, hence
almost surely along a subsequence common to the finitely many Brownian channels.

## Main statements

* `LevyStochCalc.Brownian.Ito.lintegral_sq_stopped_sub_diff_le` — the energy of the difference of
  the increments of two integrands is at most four times the energy of their difference.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_of_energy` — a path of finite energy is almost
  surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_Ioc_sum_mul` — the pointwise inner product of two
  families of paths of finite energy is almost surely integrable on a bounded half-open window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift` — Itô's formula for the increment
  of a path between two stopping times, for a function translated by a general random vector.
* `LevyStochCalc.Brownian.Ito.dyadicShift` — the dyadic lattice point of a given resolution below
  a vector, coordinate by coordinate.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx` — a bounded random vector known at a
  stopping time is a pointwise limit of finitely valued random vectors known at that time.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- The energy of the difference between the increments of two integrands between two stopping
times is at most four times the energy of the difference of the integrands. -/
theorem lintegral_sq_stopped_sub_diff_le (σ τ : Ω → WithTop ℝ) (A B : Ω → ℝ → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
            - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P
      ≤ 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h4 : ENNReal.ofReal ((2 : ℝ) ^ 2) = 4 := by
    rw [show ((2 : ℝ) ^ 2) = (4 : ℝ) by norm_num]
    simp
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
          - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)‖₊ : ℝ≥0∞) ^ 2
        ≤ 4 * (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s
    have habs : |(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
        - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)|
          ≤ 2 * |A ω s - B ω s| := by
      rw [stopped_sub_stopped_sub]
      exact abs_stopped_sub_stopped_le σ τ (fun ω s => A ω s - B ω s) ω s
    have hsq := sq_enorm_le_of_abs_le (by norm_num : (0 : ℝ) ≤ 2) habs
    rwa [h4] at hsq
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(Probability.stopped τ A ω s - Probability.stopped σ A ω s)
              - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          4 * (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hpt ω s
    _ = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖A ω s - B ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤)]
        exact MeasureTheory.lintegral_congr fun ω =>
          MeasureTheory.lintegral_const_mul' _ _ (by simp : (4 : ℝ≥0∞) ≠ ⊤)

end IncrementEnergy

section WindowIntegrability

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A path of finite energy on a bounded window is almost surely integrable on the corresponding
half-open window. -/
theorem ae_integrableOn_Ioc_of_energy {b : Ω → ℝ → ℝ}
    (hbm : Measurable (Function.uncurry b)) {T : ℝ}
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn (b ω) (Set.Ioc (0 : ℝ) T) volume := by
  filter_upwards [ae_integrableOn_of_energy_lt_top hbm hbq] with ω hω
  exact hω.mono_set Set.Ioc_subset_Icc_self

omit [IsProbabilityMeasure P] in
/-- The pointwise inner product of two families of paths of finite energy on a bounded window is
almost surely integrable on the corresponding half-open window. -/
theorem ae_integrableOn_Ioc_sum_mul {n d : ℕ} {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k))) {T : ℝ}
    (hHs : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume := by
  have hprod : ∀ {μ : Measure ℝ} (u v : ℝ → ℝ), MeasureTheory.MemLp u 2 μ →
      MeasureTheory.MemLp v 2 μ → MeasureTheory.Integrable (fun s => u s * v s) μ := by
    intro μ u v hu hv
    refine MeasureTheory.Integrable.mono'
      ((hu.integrable_sq.const_mul (1 / 2 : ℝ)).add (hv.integrable_sq.const_mul (1 / 2 : ℝ)))
      (hu.1.mul hv.1) ?_
    filter_upwards with s
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (u s), sq_abs (v s), sq_nonneg (|u s| - |v s|)]
  have hfin : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
    MeasureTheory.ae_all_iff.mpr fun p => MeasureTheory.ae_all_iff.mpr fun k =>
      MeasureTheory.ae_lt_top (measurable_energyDensity (hHm p k) T) (hHs p k).ne
  filter_upwards [hfin] with ω hω p q
  have hmem : ∀ (r : Fin n) (k : Fin d), MeasureTheory.MemLp (H r k ω) 2
      (volume.restrict (Set.Icc (0 : ℝ) T)) := fun r k =>
    LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
      (Measurable.of_uncurry_left (hHm r k)) (hω r k)
  have hIcc : MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Icc (0 : ℝ) T) volume :=
    MeasureTheory.integrable_finsetSum _ fun k _ => hprod _ _ (hmem p k) (hmem q k)
  exact hIcc.mono_set Set.Ioc_subset_Icc_self

end WindowIntegrability

section GeneralShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **Itô's formula for the increment of a path between two stopping times, for a function
translated by a random vector that is a pointwise limit of random vectors carrying the
formula.** -/
theorem itoFormula_between_generalShift
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
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
    {cm : ℕ → Ω → Fin n → ℝ} (hcm : ∀ m, Measurable (cm m))
    (hlim : ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (𝓝 (c ω)))
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
    (hmScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s))
    (hpScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s)
    (hqScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hbase : ∀ m : ℕ,
      (fun ω : Ω => f (X (clipTime τ T ω) ω + cm m ω) - f (X (clipTime σ T ω) ω + cm m ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ
                (fun ω s => coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped τ
                      (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
                    - Probability.stopped σ
                        (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s)
                (hmScm m p k) (hpScm m p k) (hqScm m p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + cm m ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + cm m ω)
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
  have hmDm : ∀ (m : ℕ) (p : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) := fun m p =>
    ((continuous_coordDeriv hf'c p).measurable.comp
      (hXm.add ((hcm m).comp measurable_fst))).mul (hbm p)
  have hmQm : ∀ (m : ℕ) (p q : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω + cm m ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) := by
    intro m p q
    refine ((continuous_coordDeriv₂ hf''c p q).measurable.comp
      (hXm.add ((hcm m).comp measurable_fst))).mul ?_
    exact Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hEnergy : ∀ i : Fin n × Fin d, Filter.Tendsto (fun m => ∫⁻ ω,
      ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(Probability.stopped τ
                (fun ω s => coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s)
            - (Probability.stopped τ
                  (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)‖₊
          : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
    rintro ⟨p, k⟩
    have hraw := tendsto_lintegral_sq_comp_shift (X := X) (continuous_coordDeriv hf'c p)
      (hK₁ p) (hHm p k) hXm hcm hc hlim (hHs p k T hT).ne
    have hub : Filter.Tendsto (fun m => (4 : ℝ≥0∞) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coordDeriv f' p (X s ω + cm m ω) * H p k ω s
          - coordDeriv f' p (X s ω + c ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        Filter.atTop (𝓝 (4 * 0)) :=
      ENNReal.Tendsto.const_mul hraw (Or.inr (by simp))
    rw [mul_zero] at hub
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hub
      (fun _ => zero_le) fun m => ?_
    exact lintegral_sq_stopped_sub_diff_le σ τ
      (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s)
      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) T
  obtain ⟨ms, hmsge, hSI⟩ := exists_seq_ae_tendsto_stochInt_of_tendsto_energy
    (fun i : Fin n × Fin d => W.W i.2) ℱ' (fun i => hcoord i.2)
    (fun m i ω s => Probability.stopped τ
        (fun ω s => coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s
      - Probability.stopped σ
          (fun ω s => coordDeriv f' i.1 (X s ω + cm m ω) * H i.1 i.2 ω s) ω s)
    (fun i ω s => Probability.stopped τ
        (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s
      - Probability.stopped σ
          (fun ω s => coordDeriv f' i.1 (X s ω + c ω) * H i.1 i.2 ω s) ω s)
    (fun m i => hmScm m i.1 i.2) (fun m i => hpScm m i.1 i.2) (fun m i => hqScm m i.1 i.2)
    (fun i => hmSc i.1 i.2) (fun i => hpSc i.1 i.2) (fun i => hqSc i.1 i.2) hT hEnergy
  have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
  have hdrift : ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
      (Probability.stopped τ
          (fun ω s => coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + cm m ω) * bdrift p ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)) := by
    filter_upwards [hbint] with ω hω p
    refine tendsto_setIntegral_stopped_sub_shift (continuous_coordDeriv hf'c p) (hK₁ p)
      (hlim ω) (hω p) fun m => ?_
    exact (Measurable.of_uncurry_left
      (measurable_uncurry_stopped_sub hσ hτ (hmDm m p))).aestronglyMeasurable
  have hquad : ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
      (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + cm m ω)
          * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
        - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + cm m ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      Filter.atTop (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)) := by
    filter_upwards [hQint] with ω hω p q
    refine tendsto_setIntegral_stopped_sub_shift_of_mul (continuous_coordDeriv₂ hf''c p q)
      (fun z s => hK₂ p q z ω s) (hlim ω) (hω p q) fun m => ?_
    exact (Measurable.of_uncurry_left
      (measurable_uncurry_stopped_sub hσ hτ (hmQm m p q))).aestronglyMeasurable
  refine ae_eq_of_tendsto_comp_of_forall_ae_eq ms hbase ?_ ?_
  · refine Filter.Eventually.of_forall fun ω => ?_
    have hshift : ∀ z : Fin n → ℝ, Filter.Tendsto (fun m => z + cm m ω) Filter.atTop
        (𝓝 (z + c ω)) := fun z => Filter.Tendsto.const_add z (hlim ω)
    exact ((hfc.continuousAt.tendsto.comp (hshift (X (clipTime τ T ω) ω))).sub
      (hfc.continuousAt.tendsto.comp (hshift (X (clipTime σ T ω) ω)))).comp hmsTop
  · filter_upwards [hdrift, hquad, hSI] with ω h1 h2 h3
    refine ((tendsto_finsetSum _ fun p _ => (h1 p).comp hmsTop).add
      (tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun k _ => h3 (p, k))).add ?_
    exact (tendsto_finsetSum _ fun p _ =>
      tendsto_finsetSum _ fun q _ => (h2 p q).comp hmsTop).const_mul _

end GeneralShift

section DyadicApproximation

/-- The vector of dyadic lattice points of resolution `2 ^ m` below the coordinates of a vector. -/
noncomputable def dyadicShift {n : ℕ} (m : ℕ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun i => (⌊(2 : ℝ) ^ m * z i⌋ : ℝ) / (2 : ℝ) ^ m

theorem dyadicShift_sub_eq {n : ℕ} (m : ℕ) (z : Fin n → ℝ) (i : Fin n) :
    dyadicShift m z i - z i
      = (((⌊(2 : ℝ) ^ m * z i⌋ : ℤ) : ℝ) - (2 : ℝ) ^ m * z i) / (2 : ℝ) ^ m := by
  have h2 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
  simp only [dyadicShift]
  field_simp

theorem measurable_dyadicShift {n m : ℕ} : Measurable (dyadicShift (n := n) m) := by
  refine measurable_pi_lambda _ fun i => ?_
  have hfr : ∀ z : Fin n → ℝ, dyadicShift m z i
      = z i - Int.fract ((2 : ℝ) ^ m * z i) / (2 : ℝ) ^ m := by
    intro z
    have h2 : ((2 : ℝ) ^ m) ≠ 0 := by positivity
    simp only [dyadicShift, Int.fract]
    field_simp
    ring
  simp only [hfr]
  exact (measurable_pi_apply i).sub
    ((measurable_fract.comp ((measurable_pi_apply i).const_mul _)).div_const _)

theorem abs_dyadicShift_sub_le {n : ℕ} (m : ℕ) (z : Fin n → ℝ) (i : Fin n) :
    |dyadicShift m z i - z i| ≤ 1 / 2 ^ m := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  have hfl : ((⌊(2 : ℝ) ^ m * z i⌋ : ℤ) : ℝ) ≤ (2 : ℝ) ^ m * z i := Int.floor_le _
  have hlt : (2 : ℝ) ^ m * z i < ((⌊(2 : ℝ) ^ m * z i⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [dyadicShift_sub_eq, abs_div, abs_of_pos h2, div_le_div_iff_of_pos_right h2, abs_le]
  constructor <;> linarith

theorem floor_mul_mem_Icc {M x : ℝ} (m : ℕ) (hx : |x| ≤ M) :
    ⌊(2 : ℝ) ^ m * x⌋
      ∈ Finset.Icc (-(⌈(2 : ℝ) ^ m * M⌉ + 1)) (⌈(2 : ℝ) ^ m * M⌉ + 1) := by
  have h2 : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  obtain ⟨hl, hu⟩ := abs_le.mp hx
  have hceil : (2 : ℝ) ^ m * M ≤ ((⌈(2 : ℝ) ^ m * M⌉ : ℤ) : ℝ) := Int.le_ceil _
  have hfl : ((⌊(2 : ℝ) ^ m * x⌋ : ℤ) : ℝ) ≤ (2 : ℝ) ^ m * x := Int.floor_le _
  have hxu : (2 : ℝ) ^ m * x ≤ (2 : ℝ) ^ m * M := mul_le_mul_of_nonneg_left hu h2.le
  have hxl : -((2 : ℝ) ^ m * M) ≤ (2 : ℝ) ^ m * x := by
    have hml := mul_le_mul_of_nonneg_left hl h2.le
    linarith
  refine Finset.mem_Icc.mpr ⟨Int.le_floor.mpr ?_, ?_⟩
  · push_cast
    linarith
  · have hcast : ((⌊(2 : ℝ) ^ m * x⌋ : ℤ) : ℝ) ≤ (((⌈(2 : ℝ) ^ m * M⌉ + 1 : ℤ)) : ℝ) := by
      push_cast
      linarith
    exact_mod_cast hcast

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A bounded random vector known at a stopping time in the sense that every Borel condition on
it, intersected with a level set of the time, is known there, is the pointwise limit of random
vectors taking finitely many values and known at that time in the same sense. -/
theorem exists_simpleShift_approx {n : ℕ} {ℱ' : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} {c : Ω → Fin n → ℝ} (hc : Measurable c) {M : ℝ}
    (hcb : ∀ ω i, |c ω i| ≤ M)
    (hcell : ∀ (a : ℝ) (B : Set (Fin n → ℝ)), MeasurableSet B →
      MeasurableSet[ℱ' a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω ∈ B}) :
    ∃ (cm : ℕ → Ω → Fin n → ℝ) (Vs : ℕ → Finset (Fin n → ℝ)),
      (∀ m, Measurable (cm m)) ∧ (∀ m ω, cm m ω ∈ Vs m) ∧
      (∀ (m : ℕ) (a : ℝ) (v : Fin n → ℝ),
        MeasurableSet[ℱ' a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ cm m ω = v}) ∧
      (∀ (m : ℕ) (ω : Ω) (i : Fin n), |cm m ω i - c ω i| ≤ 1 / 2 ^ m) ∧
      ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (𝓝 (c ω)) := by
  classical
  refine ⟨fun m ω => dyadicShift m (c ω), fun m =>
    (Fintype.piFinset fun _ : Fin n =>
        Finset.Icc (-(⌈(2 : ℝ) ^ m * M⌉ + 1)) (⌈(2 : ℝ) ^ m * M⌉ + 1)).image
      fun g : Fin n → ℤ => fun i => (g i : ℝ) / (2 : ℝ) ^ m,
    fun m => measurable_dyadicShift.comp hc, ?_, ?_,
    fun m ω i => abs_dyadicShift_sub_le m (c ω) i, ?_⟩
  · intro m ω
    refine Finset.mem_image.mpr ⟨fun i => ⌊(2 : ℝ) ^ m * c ω i⌋, ?_, rfl⟩
    exact Fintype.mem_piFinset.mpr fun i => floor_mul_mem_Icc m (hcb ω i)
  · intro m a v
    exact hcell a _ (measurable_dyadicShift (measurableSet_singleton v))
  · intro ω
    have hhalf : Filter.Tendsto (fun m : ℕ => ((1 : ℝ) / 2) ^ m) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hg : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / 2 ^ m) Filter.atTop (𝓝 0) := by
      simpa [div_pow] using hhalf
    refine tendsto_pi_nhds.2 fun i => ?_
    rw [← tendsto_sub_nhds_zero_iff]
    have hb : ∀ m : ℕ, ‖dyadicShift m (c ω) i - c ω i‖ ≤ 1 / 2 ^ m := by
      intro m
      rw [Real.norm_eq_abs]
      exact abs_dyadicShift_sub_le m (c ω) i
    exact squeeze_zero_norm hb hg

end DyadicApproximation

end LevyStochCalc.Brownian.Ito
