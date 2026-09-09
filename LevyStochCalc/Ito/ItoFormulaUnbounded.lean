/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.VectorItoProcessDiff
import LevyStochCalc.Brownian.ItoCutoff

/-!
# Itô's formula without a pointwise bound on the coefficients

Clamping the coefficients of a vector Itô process at level `j` leaves bounded coefficients driving
a process that converges to the original one in `L²`, uniformly on a bounded window.

## Main statements

* `LevyStochCalc.Brownian.Ito.clampCoeff`, `clampDrift` — the clamped coefficients.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_window_clamp` — the mesh of the approximation.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Clamped

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- The diffusion matrix clamped at level `j`. -/
noncomputable def clampCoeff (H : Fin n → Fin d → Ω → ℝ → ℝ) (j : ℕ) :
    Fin n → Fin d → Ω → ℝ → ℝ := fun p k ω s => clampAt (j : ℝ) (H p k ω s)

/-- The drift clamped at level `j`. -/
noncomputable def clampDrift (b : Fin n → Ω → ℝ → ℝ) (j : ℕ) : Fin n → Ω → ℝ → ℝ :=
  fun p ω s => clampAt (j : ℝ) (b p ω s)

theorem measurable_clampCoeff {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k))) (j : ℕ) (p : Fin n) (k : Fin d) :
    Measurable (Function.uncurry (clampCoeff H j p k)) :=
  (continuous_clampAt (j : ℝ)).measurable.comp (hm p k)

theorem measurable_clampDrift {b : Fin n → Ω → ℝ → ℝ}
    (hm : ∀ p, Measurable (Function.uncurry (b p))) (j : ℕ) (p : Fin n) :
    Measurable (Function.uncurry (clampDrift b j p)) :=
  (continuous_clampAt (j : ℝ)).measurable.comp (hm p)

theorem progressivelyMeasurable_clampCoeff {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)) (j : ℕ) (p : Fin n) (k : Fin d) :
    Probability.ProgressivelyMeasurable ℱ (clampCoeff H j p k) :=
  Probability.ProgressivelyMeasurable.comp_continuous (continuous_clampAt (j : ℝ))
    (clampAt_zero (Nat.cast_nonneg j)) (hp p k)

theorem progressivelyMeasurable_clampDrift {b : Fin n → Ω → ℝ → ℝ}
    (hp : ∀ p, Probability.ProgressivelyMeasurable ℱ (b p)) (j : ℕ) (p : Fin n) :
    Probability.ProgressivelyMeasurable ℱ (clampDrift b j p) :=
  Probability.ProgressivelyMeasurable.comp_continuous (continuous_clampAt (j : ℝ))
    (clampAt_zero (Nat.cast_nonneg j)) (hp p)

theorem abs_clampCoeff_le (H : Fin n → Fin d → Ω → ℝ → ℝ) (j : ℕ)
    (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ) : |clampCoeff H j p k ω s| ≤ (j : ℝ) :=
  abs_clampAt_le (Nat.cast_nonneg j) _

theorem abs_clampDrift_le (b : Fin n → Ω → ℝ → ℝ) (j : ℕ) (p : Fin n) (ω : Ω) (s : ℝ) :
    |clampDrift b j p ω s| ≤ (j : ℝ) :=
  abs_clampAt_le (Nat.cast_nonneg j) _

theorem energy_clampCoeff_lt_top {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k))) (j : ℕ) (p : Fin n) (k : Fin d)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampCoeff H j p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  energy_lt_top_of_bounded (fun ω s => abs_clampCoeff_le H j p k ω s) T hT

theorem energy_clampDrift_lt_top {b : Fin n → Ω → ℝ → ℝ}
    (hm : ∀ p, Measurable (Function.uncurry (b p))) (j : ℕ) (p : Fin n) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampDrift b j p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  energy_lt_top_of_bounded (fun ω s => abs_clampDrift_le b j p ω s) T hT

/-- The combination of energies that bounds the `L²` distance on `[0, T]` between a vector Itô
process and the one driven by its coefficients clamped at level `j`. -/
noncomputable def clampMesh (P : Measure Ω) (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (b : Fin n → Ω → ℝ → ℝ) (T : ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ p : Fin n, (2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))

/-- **The clamped coefficients approximate the coefficients in energy**, in the combination that
bounds the `L²` distance between the processes they drive. -/
theorem tendsto_energy_window_clamp {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k))) {b : Fin n → Ω → ℝ → ℝ}
    (hbm : ∀ p, Measurable (Function.uncurry (b p))) {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (clampMesh P H b T) Filter.atTop (𝓝 0) := by
  unfold clampMesh
  have hdrift : ∀ p : Fin n, Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) :=
    fun p => tendsto_energy_clampAt_sub (hbm p) (hbq p)
  have hdiff : ∀ (p : Fin n) (k : Fin d),
      Filter.Tendsto (fun j : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) :=
    fun p k => tendsto_energy_clampAt_sub (hm p k) (hq p k)
  have hterm : ∀ p : Fin n, Filter.Tendsto (fun j : ℕ =>
      (2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)))
      Filter.atTop (𝓝 0) := by
    intro p
    have h1 : Filter.Tendsto (fun j : ℕ =>
        2 * (ENNReal.ofReal T * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := 2 * ENNReal.ofReal T) (hdrift p)
        (Or.inr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
      rw [mul_zero] at hc
      exact hc.congr fun j => by rw [mul_assoc]
    have h2 : Filter.Tendsto (fun j : ℕ =>
        2 * ((d : ℝ≥0∞) * ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        Filter.atTop (𝓝 0) := by
      have hsum : Filter.Tendsto (fun j : ℕ => ∑ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          Filter.atTop (𝓝 0) := by
        have := tendsto_finset_sum (Finset.univ : Finset (Fin d))
          (fun k _ => hdiff p k)
        simpa using this
      have hc := ENNReal.Tendsto.const_mul (a := 2 * (d : ℝ≥0∞)) hsum
        (Or.inr (ENNReal.mul_ne_top (by simp) (by simp)))
      rw [mul_zero] at hc
      exact hc.congr fun j => by rw [mul_assoc]
    simpa using h1.add h2
  have := tendsto_finset_sum (Finset.univ : Finset (Fin n)) (fun p _ => hterm p)
  simpa using this

section ClampProcess

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **The process driven by the clamped coefficients approximates the original one in `L²`,
uniformly on `[0, T]`.** -/
theorem lintegral_sq_norm_clampProcess_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (j : ℕ) {T t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫⁻ ω, (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
            X₀ (clampDrift b j) t ω
        - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ clampMesh P H b T j := by
  have hbound := lintegral_sq_norm_vectorItoProcess_sub_le W ℱ' hcoord
    hm hpg hq (fun p k => measurable_clampCoeff hm j p k)
    (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
    (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
    hX₀ hbm (fun p => measurable_clampDrift hbm j p) ht hbq
    (fun p T' hT' => energy_clampDrift_lt_top hbm j p T' hT')
  refine hbound.trans ?_
  unfold clampMesh
  refine Finset.sum_le_sum fun p _ => ?_
  have hmonoD : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampDrift b j p ω s - b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    MeasureTheory.lintegral_mono fun ω =>
      MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc_right htT)
  have hmonoH : ∀ k : Fin d, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖clampCoeff H j p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun k => MeasureTheory.lintegral_mono fun ω =>
      MeasureTheory.lintegral_mono_set (Set.Icc_subset_Icc_right htT)
  have hT : ENNReal.ofReal t ≤ ENNReal.ofReal T := ENNReal.ofReal_le_ofReal htT
  gcongr

/-- **The energy of the approximation error over the whole window.** -/
theorem lintegral_window_sq_norm_clampProcess_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k))
    (hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (j : ℕ) {T : ℝ} (hT : 0 < T) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ENNReal.ofReal T * clampMesh P H b T j := by
  have hset : ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      = ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume := by
    exact (MeasureTheory.setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc)).symm
  rw [hset]
  calc ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω,
        (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) T, clampMesh P H b T j ∂volume := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        exact lintegral_sq_norm_clampProcess_sub_le W ℱ' hcoord hm hpg hq hX₀ hbm hbq j
          hs.1 hs.2
    _ = ENNReal.ofReal T * clampMesh P H b T j := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]

end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito
