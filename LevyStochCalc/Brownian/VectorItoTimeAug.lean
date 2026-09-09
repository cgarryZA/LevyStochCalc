/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoZero
import LevyStochCalc.Brownian.VectorItoProcessVersion

/-!
# Time as a state coordinate

Prepending a coordinate that drifts at unit rate and carries no diffusion turns a vector Itô
process `X` on `Fin n → ℝ` into one on `Fin (n + 1) → ℝ` whose path is `t ↦ (t, X_t)`. Itô's
formula for a time-dependent function of the state is then the state-only formula for the
augmented process.

## Main statements

* `LevyStochCalc.Brownian.Ito.timeAugDiffusion`, `timeAugDrift`, `timeAugInit`,
  `timeAugProcess` — the augmented data.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.timeAug` — the augmented path is a version of
  the augmented Itô process.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Data

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

/-- The diffusion matrix with a time coordinate prepended: the time row is zero. -/
def timeAugDiffusion (H : Fin n → Fin d → Ω → ℝ → ℝ) : Fin (n + 1) → Fin d → Ω → ℝ → ℝ :=
  Fin.cons (fun _ _ _ => 0) H

/-- The drift with a time coordinate prepended: the time coordinate drifts at unit rate. -/
def timeAugDrift (bdrift : Fin n → Ω → ℝ → ℝ) : Fin (n + 1) → Ω → ℝ → ℝ :=
  Fin.cons (fun _ _ => 1) bdrift

/-- The initial value with a time coordinate prepended, starting at the origin. -/
def timeAugInit (X₀ : Ω → Fin n → ℝ) : Ω → Fin (n + 1) → ℝ := fun ω => Fin.cons 0 (X₀ ω)

/-- A process with its own time prepended as a coordinate. -/
def timeAugProcess (X : ℝ → Ω → Fin n → ℝ) : ℝ → Ω → Fin (n + 1) → ℝ :=
  fun t ω => Fin.cons t (X t ω)

variable (H : Fin n → Fin d → Ω → ℝ → ℝ)

theorem measurable_timeAugDiffusion (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (p : Fin (n + 1)) (k : Fin d) :
    Measurable (Function.uncurry (timeAugDiffusion H p k)) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDiffusion, Fin.cons_zero]
    exact measurable_const
  | succ q => simpa [timeAugDiffusion] using hHm q k

theorem progressivelyMeasurable_timeAugDiffusion (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)) (p : Fin (n + 1)) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (timeAugDiffusion H p k) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDiffusion, Fin.cons_zero]
    exact Probability.progressivelyMeasurable_const (Ω := Ω) ℱ (0 : ℝ)
  | succ q => simpa [timeAugDiffusion] using hHp q k

theorem sq_timeAugDiffusion
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p : Fin (n + 1)) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖timeAugDiffusion H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  induction p using Fin.cases with
  | zero => simp [timeAugDiffusion]
  | succ q => simpa [timeAugDiffusion] using hHs q k T hT

theorem measurable_timeAugDiffusion_add (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (p q : Fin (n + 1)) (k : Fin d) :
    Measurable (Function.uncurry fun ω s =>
      timeAugDiffusion H p k ω s + timeAugDiffusion H q k ω s) :=
  (measurable_timeAugDiffusion H hHm p k).add (measurable_timeAugDiffusion H hHm q k)

theorem progressivelyMeasurable_timeAugDiffusion_add (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)) (p q : Fin (n + 1))
    (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      timeAugDiffusion H p k ω s + timeAugDiffusion H q k ω s :=
  (progressivelyMeasurable_timeAugDiffusion H ℱ hHp p k).add
    (progressivelyMeasurable_timeAugDiffusion H ℱ hHp q k)

theorem sq_timeAugDiffusion_add
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (p q : Fin (n + 1)) (k : Fin d) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖timeAugDiffusion H p k ω s + timeAugDiffusion H q k ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ := by
  induction p using Fin.cases with
  | zero =>
    induction q using Fin.cases with
    | zero => simp [timeAugDiffusion]
    | succ q' => simpa [timeAugDiffusion] using hHs q' k T hT
  | succ p' =>
    induction q using Fin.cases with
    | zero => simpa [timeAugDiffusion] using hHs p' k T hT
    | succ q' => simpa [timeAugDiffusion] using hqa p' q' k T hT

omit [MeasurableSpace Ω] in
theorem abs_timeAugDiffusion_le {C : ℝ} (hC0 : 0 ≤ C)
    (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)
    (p : Fin (n + 1)) (k : Fin d) (ω : Ω) (s : ℝ) : |timeAugDiffusion H p k ω s| ≤ C := by
  induction p using Fin.cases with
  | zero => simpa [timeAugDiffusion] using hC0
  | succ q => simpa [timeAugDiffusion] using hCH q k ω s

variable (bdrift : Fin n → Ω → ℝ → ℝ)

theorem measurable_timeAugDrift (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (p : Fin (n + 1)) : Measurable (Function.uncurry (timeAugDrift bdrift p)) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDrift, Fin.cons_zero]
    exact measurable_const
  | succ q => simpa [timeAugDrift] using hbm q

theorem progressivelyMeasurable_timeAugDrift (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ (bdrift p)) (p : Fin (n + 1)) :
    Probability.ProgressivelyMeasurable ℱ (timeAugDrift bdrift p) := by
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugDrift, Fin.cons_zero]
    exact Probability.progressivelyMeasurable_const (Ω := Ω) ℱ (1 : ℝ)
  | succ q => simpa [timeAugDrift] using hbp q

omit [MeasurableSpace Ω] in
theorem abs_timeAugDrift_le {B : ℝ} (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (p : Fin (n + 1)) (ω : Ω) (s : ℝ) : |timeAugDrift bdrift p ω s| ≤ max B 1 := by
  induction p using Fin.cases with
  | zero => simp [timeAugDrift]
  | succ q => exact le_trans (by simpa [timeAugDrift] using hB q ω s) (le_max_left B 1)

end Data

section Version

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}

/-- **The augmented path is a version of the augmented Itô process.** Prepending the time
coordinate to a version of `X` gives a version of the vector Itô process whose extra coordinate
drifts at unit rate and carries no diffusion. -/
theorem IsVectorItoVersion.timeAug
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) :
    IsVectorItoVersion W ℱ hcoord (timeAugDiffusion H)
      (measurable_timeAugDiffusion H hHm) (progressivelyMeasurable_timeAugDiffusion H ℱ hHp)
      (sq_timeAugDiffusion H hHs) (timeAugInit X₀) (timeAugDrift bdrift)
      (timeAugProcess X) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω
    refine continuous_pi fun p => ?_
    induction p using Fin.cases with
    | zero =>
      simp only [timeAugProcess, Fin.cons_zero]
      exact continuous_id
    | succ q =>
      simp only [timeAugProcess, Fin.cons_succ]
      exact (continuous_apply q).comp (h.continuous_path ω)
  · intro t
    have hco : ∀ p : Fin (n + 1), Measurable[ℱ t] fun ω => timeAugProcess X t ω p := by
      intro p
      induction p using Fin.cases with
      | zero =>
        simp only [timeAugProcess, Fin.cons_zero]
        exact measurable_const
      | succ q =>
        simp only [timeAugProcess, Fin.cons_succ]
        exact (continuous_apply q).measurable.comp (h.adapted t).measurable
    refine Measurable.stronglyMeasurable ?_
    letI : MeasurableSpace Ω := ℱ t
    exact measurable_pi_lambda _ hco
  · intro t ht
    have hzero : ∀ᵐ ω ∂P, ∀ k : Fin d,
        coordItoIntegral W ℱ hcoord (timeAugDiffusion H) (measurable_timeAugDiffusion H hHm)
            (progressivelyMeasurable_timeAugDiffusion H ℱ hHp) (sq_timeAugDiffusion H hHs)
            0 k t ω = 0 := by
      refine MeasureTheory.ae_all_iff.mpr fun k => ?_
      have hz0 : stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (timeAugDiffusion H 0 k)
          (measurable_timeAugDiffusion H hHm 0 k)
          (progressivelyMeasurable_timeAugDiffusion H ℱ hHp 0 k)
          (sq_timeAugDiffusion H hHs 0 k) t =ᵐ[P] 0 :=
        stochasticIntegralBrownian_ae_zero (W.W k) ℱ (hcoord k) _ _ _ t
      filter_upwards [hz0] with ω hω
      simpa [coordItoIntegral] using hω
    have hone : ∫ _s in Set.Icc (0 : ℝ) t, (1 : ℝ) ∂volume = t := by
      rw [MeasureTheory.setIntegral_const]
      simp [MeasureTheory.measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal ht]
    filter_upwards [h.ae_eq t ht, hzero] with ω hX hz
    funext p
    induction p using Fin.cases with
    | zero =>
      simp only [timeAugProcess, Fin.cons_zero, vectorItoProcess, vectorItoMartingale,
        timeAugInit, timeAugDrift]
      rw [Finset.sum_congr rfl fun k (_ : k ∈ Finset.univ) => hz k, hone]
      simp
    | succ q =>
      simp only [timeAugProcess, Fin.cons_succ, vectorItoProcess, timeAugInit, timeAugDrift]
      exact congrFun hX q

end Version

end LevyStochCalc.Brownian.Ito
