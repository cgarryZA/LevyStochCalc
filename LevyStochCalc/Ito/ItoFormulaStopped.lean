/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaUnbounded
import LevyStochCalc.Brownian.VectorItoStopped

/-!
# Itô's formula along a stopped path

Stopping a vector Itô process at a stopping time of finite range stops each of the three
integrands of Itô's formula at the same time, so the formula for the stopped process reads as the
formula for the original one with every integrand cut off at the stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_stopped` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section StoppedFormula

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

omit [IsProbabilityMeasure P] in
/-- A function of the stopped path against a stopped integrand is the stopped product. -/
theorem stopped_comp_eq {X : ℝ → Ω → Fin n → ℝ} (τ : Ω → WithTop ℝ)
    (g : (Fin n → ℝ) → ℝ) (K : Ω → ℝ → ℝ) :
    (fun ω s => g (X (clipTime τ s ω) ω) * Probability.stopped τ K ω s)
      = Probability.stopped τ (fun ω s => g (X s ω) * K ω s) := by
  funext ω s
  simp only [Probability.stopped]
  by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
  · rw [if_pos hle, if_pos hle, clipTime_of_le hle]
  · rw [if_neg hle, if_neg hle, mul_zero]

omit [IsProbabilityMeasure P] in
/-- A function of the stopped path against a sum of products of stopped integrands is the
stopped product. -/
theorem stopped_comp₂_eq {X : ℝ → Ω → Fin n → ℝ} (τ : Ω → WithTop ℝ)
    (g : (Fin n → ℝ) → ℝ) (K L : Fin d → Ω → ℝ → ℝ) :
    (fun ω s => g (X (clipTime τ s ω) ω)
        * ∑ k : Fin d, Probability.stopped τ (K k) ω s * Probability.stopped τ (L k) ω s)
      = Probability.stopped τ (fun ω s => g (X s ω) * ∑ k : Fin d, K k ω s * L k ω s) := by
  funext ω s
  simp only [Probability.stopped]
  by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
  · simp only [if_pos hle, clipTime_of_le hle]
  · simp [hle]

include hcoord in
/-- **Itô's formula along a path stopped at a stopping time of finite range.** -/
theorem itoFormula_stopped
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
    (J : Finset ℝ) (hJ0 : ∀ c ∈ J, 0 ≤ c)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
  classical
  have hstop := h.stopped W ℱ' hcoord hτ hτ0 J hJ0 hτJ
  have hG : ∀ (p : Fin n) (k : Fin d),
      (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (H p k) ω s)
        = Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) :=
    fun p k => stopped_comp_eq τ (coordDeriv f' p) (H p k)
  have hGb : ∀ p : Fin n,
      (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (bdrift p) ω s)
        = Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) :=
    fun p => stopped_comp_eq τ (coordDeriv f' p) (bdrift p)
  have hGq : ∀ p q : Fin n,
      (fun ω s => coordDeriv₂ f'' p q (X (clipTime τ s ω) ω)
          * ∑ k : Fin d, Probability.stopped τ (H p k) ω s
              * Probability.stopped τ (H q k) ω s)
        = Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) :=
    fun p q => stopped_comp₂_eq τ (coordDeriv₂ f'' p q) (fun k => H p k) (fun k => H q k)
  have hmgτ : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
        * Probability.stopped τ (H p k) ω s) := by
    intro p k
    rw [hG p k]
    exact hmg p k
  have hpgτ : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
        * Probability.stopped τ (H p k) ω s := by
    intro p k
    rw [hG p k]
    exact hpg p k
  have hqgτ : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (H p k) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    have := hqg p k
    rw [← hG p k] at this
    exact this
  have hres := itoFormula_of_unbounded W ℱ' hcoord hstop 𝒲 hℱ0 hnull hX₀
    (fun p => Probability.measurable_uncurry_stopped hτ (hbm p))
    (fun p => Probability.ProgressivelyMeasurable.stopped hτ (hbp p))
    (fun p T' hT' => energy_lt_top_of_abs_le
      (fun ω s => Probability.abs_stopped_le τ (bdrift p) ω s) (hbq p) T' hT')
    hfC hf hf' hmgτ hpgτ hqgτ hT
  have hSI : ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
            * Probability.stopped τ (H p k) ω s)
          (hmgτ p k) (hpgτ p k) (hqgτ p k) T
        = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
          (hmg p k) (hpg p k) (hqg p k) T :=
    fun p k => stochasticIntegralBrownian_congr_fun (W.W k) ℱ' (hcoord k) (hG p k)
      (hmgτ p k) (hpgτ p k) (hqgτ p k) (hmg p k) (hpg p k) (hqg p k) T
  filter_upwards [hres] with ω hω
  rw [clipTime_of_le (hτ0 ω)] at hω
  have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (X (clipTime τ s ω) ω) * Probability.stopped τ (bdrift p) ω s ∂volume)
      = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s
          ∂volume := by
    refine Finset.sum_congr rfl fun p _ => ?_
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun s _ => congrFun (congrFun (hGb p) ω) s
  have e2 : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (H p k) ω s) (hmgτ p k) (hpgτ p k) (hqgτ p k) T ω)
      = ∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
        (hmg p k) (hpg p k) (hqg p k) T ω :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => congrFun (hSI p k) ω
  have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (X (clipTime τ s ω) ω)
          * ∑ k : Fin d, Probability.stopped τ (H p k) ω s
              * Probability.stopped τ (H q k) ω s ∂volume)
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
          * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
    refine congrArg (fun x => 1 / 2 * x) ?_
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun s _ => congrFun (congrFun (hGq p q) ω) s
  rw [hω, e1, e2, e3]

end StoppedFormula

end LevyStochCalc.Brownian.Ito
