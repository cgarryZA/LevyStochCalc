/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaStoppedLimit
import LevyStochCalc.Ito.ItoFormulaShift
import LevyStochCalc.Ito.VectorItoProcessDiff
import LevyStochCalc.Brownian.ItoFinsetSum

/-!
# Itô's formula for the increment of a path between two stopping times

Subtracting Itô's formula along the path stopped at one stopping time from Itô's formula along
the path stopped at another recombines into a single formula for the increment between the two
clipped horizons: each Lebesgue integral becomes the integral of the increment of the cut-off
integrand, and the two Itô integrals become the single Itô integral of that increment.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub` — the Itô integral of the
  increment between two cut-offs of an integrand is the difference of the two Itô integrals.
* `LevyStochCalc.Brownian.Ito.ae_integrableOn_stopped_Ioc` — a cut-off integrand of finite energy
  is almost surely integrable on a bounded window.
* `LevyStochCalc.Brownian.Ito.itoFormula_between` — Itô's formula for the increment of a path
  between two stopping times.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general_shift` — Itô's formula along a path
  stopped at an arbitrary stopping time, for a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_shift` — the increment formula for a function
  translated by a fixed vector.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section IncrementAdmissible

variable {Ω : Type u} {mΩ : MeasurableSpace Ω}

/-- The increment between the cut-offs of an integrand at two stopping times has measurable
uncurrying. -/
theorem measurable_uncurry_stopped_sub {ℱ : Filtration ℝ mΩ} {σ τ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s) :=
  (Probability.measurable_uncurry_stopped hτ hmK).sub
    (Probability.measurable_uncurry_stopped hσ hmK)

/-- The increment between the cut-offs of an integrand at two stopping times is progressively
measurable. -/
theorem progressivelyMeasurable_stopped_sub {ℱ : Filtration ℝ mΩ} {σ τ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hpK : Probability.ProgressivelyMeasurable ℱ K) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s :=
  (Probability.ProgressivelyMeasurable.stopped hτ hpK).sub
    (Probability.ProgressivelyMeasurable.stopped hσ hpK)

end IncrementAdmissible

section IncrementEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The increment between the cut-offs of an integrand at two stopping times has finite energy on
every window carrying finite energy of the integrand. -/
theorem energy_stopped_sub_lt_top {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ K ω s - Probability.stopped σ K ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ :=
  lintegral_energy_lt_top_of_bound (fun _ _ => sq_nnnorm_sub_le_two_mul _ _)
    (Probability.measurable_uncurry_stopped hτ hmK)
    (Probability.measurable_uncurry_stopped hσ hmK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK)

/-- A cut-off integrand of finite energy is almost surely integrable on a bounded window. -/
theorem ae_integrableOn_stopped_Ioc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, MeasureTheory.IntegrableOn
      (Probability.stopped τ K ω) (Set.Ioc (0 : ℝ) T) volume := by
  have hq := energy_lt_top_of_abs_le
    (fun ω s => Probability.abs_stopped_le τ K ω s) hqK T hT
  filter_upwards [ae_integrableOn_of_energy_lt_top
    (Probability.measurable_uncurry_stopped hτ hmK) hq] with ω hω
  exact hω.mono_set Set.Ioc_subset_Icc_self

end IncrementEnergy

section IncrementItoIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral of the increment of an integrand between two stopping times.** It is the
difference of the Itô integrals of the integrand cut off at each of the two times. -/
theorem stochasticIntegralBrownian_stopped_sub
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ K ω s - Probability.stopped σ K ω s)
        (measurable_uncurry_stopped_sub hσ hτ hmK)
        (progressivelyMeasurable_stopped_sub hσ hτ hpK)
        (energy_stopped_sub_lt_top hσ hτ hmK hqK) T
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ K)
          (Probability.measurable_uncurry_stopped hτ hmK)
          (Probability.ProgressivelyMeasurable.stopped hτ hpK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK) T ω
        - stochasticIntegralBrownian W ℱ hℱ (Probability.stopped σ K)
          (Probability.measurable_uncurry_stopped hσ hmK)
          (Probability.ProgressivelyMeasurable.stopped hσ hpK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK) T ω :=
  stochasticIntegralBrownian_sub W ℱ hℱ
    (Probability.measurable_uncurry_stopped hτ hmK)
    (Probability.measurable_uncurry_stopped hσ hmK)
    (Probability.ProgressivelyMeasurable.stopped hτ hpK)
    (Probability.ProgressivelyMeasurable.stopped hσ hpK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK)
    (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK)
    (measurable_uncurry_stopped_sub hσ hτ hmK)
    (progressivelyMeasurable_stopped_sub hσ hτ hpK)
    (energy_stopped_sub_lt_top hσ hτ hmK hqK) hT

end IncrementItoIntegral

section Between

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in
/-- **Itô's formula for the increment of a path between two stopping times.** -/
theorem itoFormula_between
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, Multidim.MultidimBrownianMotion.CrossWitness W ℱ' j)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpG : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqG : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s))
    (hqD : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s))
    (hqQ : ∀ (p q : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω) - f (X (clipTime σ T ω) ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s)
            (measurable_uncurry_stopped_sub hσ hτ (hmG p k))
            (progressivelyMeasurable_stopped_sub hσ hτ (hpG p k))
            (energy_stopped_sub_lt_top hσ hτ (hmG p k) (hqG p k)) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hmSτ : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)) :=
    fun p k => Probability.measurable_uncurry_stopped hτ (hmG p k)
  have hpSτ : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s) :=
    fun p k => Probability.ProgressivelyMeasurable.stopped hτ (hpG p k)
  have hqSτ : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun p k => energy_lt_top_of_abs_le
      (fun ω s => Probability.abs_stopped_le τ _ ω s) (hqG p k)
  have hmSσ : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped σ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)) :=
    fun p k => Probability.measurable_uncurry_stopped hσ (hmG p k)
  have hpSσ : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped σ fun ω s => coordDeriv f' p (X s ω) * H p k ω s) :=
    fun p k => Probability.ProgressivelyMeasurable.stopped hσ (hpG p k)
  have hqSσ : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped σ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun p k => energy_lt_top_of_abs_le
      (fun ω s => Probability.abs_stopped_le σ _ ω s) (hqG p k)
  have hτres := itoFormula_stopped_general W ℱ' hcoord h 𝒲 hℱ0 hnull hX₀ hbm hbp hbq hτ hτ0
    hfC hf hf' hmSτ hpSτ hqSτ hT
  have hσres := itoFormula_stopped_general W ℱ' hcoord h 𝒲 hℱ0 hnull hX₀ hbm hbp hbq hσ hσ0
    hfC hf hf' hmSσ hpSσ hqSσ hT
  have hsub : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s)
          (measurable_uncurry_stopped_sub hσ hτ (hmG p k))
          (progressivelyMeasurable_stopped_sub hσ hτ (hpG p k))
          (energy_stopped_sub_lt_top hσ hτ (hmG p k) (hqG p k)) T ω
        = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmSτ p k) (hpSτ p k) (hqSτ p k) T ω
          - stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped σ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmSσ p k) (hpSσ p k) (hqSσ p k) T ω := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact stochasticIntegralBrownian_stopped_sub (W.W k) ℱ' (hcoord k) hσ hτ
      (hmG p k) (hpG p k) (hqG p k) hT
  have hDτ : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω)
      (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    exact fun p => ae_integrableOn_stopped_Ioc hτ (hmD p) (hqD p) hT
  have hDσ : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (Probability.stopped σ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω)
      (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    exact fun p => ae_integrableOn_stopped_Ioc hσ (hmD p) (hqD p) hT
  have hQτ : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) ω) (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    exact fun q => ae_integrableOn_stopped_Ioc hτ (hmQ p q) (hqQ p q) hT
  have hQσ : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω)
        * ∑ k : Fin d, H p k ω s * H q k ω s) ω) (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    exact fun q => ae_integrableOn_stopped_Ioc hσ (hmQ p q) (hqQ p q) hT
  filter_upwards [hτres, hσres, hsub, hDτ, hDσ, hQτ, hQσ] with ω e1 e2 e3 e4 e5 e6 e7
  have hA : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s) ∂volume)
      = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s ∂volume)
        - ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s ∂volume := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun p _ => MeasureTheory.integral_sub (e4 p) (e5 p)
  have hB : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s)
        (measurable_uncurry_stopped_sub hσ hτ (hmG p k))
        (progressivelyMeasurable_stopped_sub hσ hτ (hpG p k))
        (energy_stopped_sub_lt_top hσ hτ (hmG p k) (hqG p k)) T ω)
      = (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
          (hmSτ p k) (hpSτ p k) (hqSτ p k) T ω)
        - ∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped σ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmSσ p k) (hpSσ p k) (hqSσ p k) T ω := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => e3 p k
  have hC : (∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      = (∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume)
        - ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun q _ => MeasureTheory.integral_sub (e6 p q) (e7 p q)
  rw [hA, hB, hC]
  linarith [e1, e2]

include hcoord in
/-- **Itô's formula along a path stopped at a stopping time, for a function translated by a fixed
vector.** -/
theorem itoFormula_stopped_general_shift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, Multidim.MultidimBrownianMotion.CrossWitness W ℱ' j)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (c : Fin n → ℝ)
    (hmg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s)))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s))
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c) - f (X 0 ω + c)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω + c) * bdrift p ω s) ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume :=
  itoFormula_stopped_general W ℱ' hcoord h 𝒲 hℱ0 hnull hX₀ hbm hbp hbq hτ hτ0
    (f := fun z => f (z + c)) (f' := fun z => f' (z + c)) (f'' := fun z => f'' (z + c))
    (contDiff_shiftArg hfC c) (fun z => hasFDerivAt_shiftArg hf c z)
    (fun z => hasFDerivAt_shiftArg hf' c z) hmg hpg hqg hT

include hcoord in
/-- **Itô's formula for the increment of a path between two stopping times, for a function
translated by a fixed vector.** -/
theorem itoFormula_between_shift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, Multidim.MultidimBrownianMotion.CrossWitness W ℱ' j)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (c : Fin n → ℝ)
    (hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s))
    (hpG : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s)
    (hqG : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω + c) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + c) * bdrift p ω s))
    (hqD : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω + c) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω + c) * ∑ k : Fin d, H p k ω s * H q k ω s))
    (hqQ : ∀ (p q : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv₂ f'' p q (X s ω + c) * ∑ k : Fin d, H p k ω s * H q k ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c) - f (X (clipTime σ T ω) ω + c))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s) ω s)
            (measurable_uncurry_stopped_sub hσ hτ (hmG p k))
            (progressivelyMeasurable_stopped_sub hσ hτ (hpG p k))
            (energy_stopped_sub_lt_top hσ hτ (hmG p k) (hqG p k)) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume :=
  itoFormula_between W ℱ' hcoord h 𝒲 hℱ0 hnull hX₀ hbm hbp hbq hσ hτ hσ0 hτ0
    (f := fun z => f (z + c)) (f' := fun z => f' (z + c)) (f'' := fun z => f'' (z + c))
    (contDiff_shiftArg hfC c) (fun z => hasFDerivAt_shiftArg hf c z)
    (fun z => hasFDerivAt_shiftArg hf' c z) hmG hpG hqG hmD hqD hmQ hqQ hT

end Between

end LevyStochCalc.Brownian.Ito
