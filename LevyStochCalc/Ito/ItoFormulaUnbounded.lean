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

/-- **The `L²` distance between a version and the version of the clamped process**, at a single
time of the window. -/
theorem lintegral_sq_norm_version_clamp_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {j : ℕ} {X Xj : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
      X₀ (clampDrift b j) Xj)
    {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    ∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ clampMesh P H b T j := by
  have hcongr : ∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖vectorItoProcess W ℱ' hcoord (clampCoeff H j)
            (fun p k => measurable_clampCoeff hm j p k)
            (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
            (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
            X₀ (clampDrift b j) s ω
          - vectorItoProcess W ℱ' hcoord H hm hpg hq X₀ b s ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine MeasureTheory.lintegral_congr_ae ?_
    filter_upwards [hX.ae_eq s hs.le, hXj.ae_eq s hs.le] with ω h1 h2
    rw [h1, h2]
  rw [hcongr]
  exact lintegral_sq_norm_clampProcess_sub_le W ℱ' hcoord hm hpg hq hX₀ hbm hbq j hs hsT

/-- **The energy of the approximation error of the versions over the whole window.** -/
theorem lintegral_window_sq_norm_version_clamp_sub_le
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {j : ℕ} {X Xj : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
      X₀ (clampDrift b j) Xj)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal T * clampMesh P H b T j := by
  have hjoint : Measurable fun q : Ω × ℝ => (‖Xj q.2 q.1 - X q.2 q.1‖₊ : ℝ≥0∞) ^ 2 :=
    (((hXj.measurable_uncurry.sub hX.measurable_uncurry).nnnorm).coe_nnreal_ennreal).pow_const 2
  rw [MeasureTheory.lintegral_lintegral_swap hjoint.aemeasurable]
  have hIoc : ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      = ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume :=
    (MeasureTheory.setLIntegral_congr (MeasureTheory.Ioc_ae_eq_Icc)).symm
  rw [hIoc]
  calc ∫⁻ s in Set.Ioc (0 : ℝ) T, (∫⁻ ω, (‖Xj s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) ∂volume
      ≤ ∫⁻ _s in Set.Ioc (0 : ℝ) T, clampMesh P H b T j ∂volume := by
        refine MeasureTheory.setLIntegral_mono' measurableSet_Ioc fun s hs => ?_
        exact lintegral_sq_norm_version_clamp_sub_le W ℱ' hcoord hX₀ hbm hbq hX hXj hs.1 hs.2
    _ = ENNReal.ofReal T * clampMesh P H b T j := by
        rw [MeasureTheory.setLIntegral_const, Real.volume_Ioc, sub_zero, mul_comm]

/-- If the integrals of a sequence of nonnegative functions are summable, their sum is finite
almost everywhere. -/
theorem ae_tsum_ne_top_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) : ∀ᵐ a ∂μ, ∑' i : ℕ, g i a ≠ ⊤ := by
  have h1 : ∫⁻ a, ∑' i : ℕ, g i a ∂μ ≠ ⊤ := by
    rw [MeasureTheory.lintegral_tsum fun i => (hg i).aemeasurable]
    exact hsum
  filter_upwards [MeasureTheory.ae_lt_top (Measurable.ennreal_tsum hg) h1] with a ha
  exact ha.ne

/-- If the integrals of a sequence of nonnegative functions are summable, the functions tend to
zero almost everywhere. -/
theorem ae_tendsto_zero_of_lintegral_summable {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) :
    ∀ᵐ a ∂μ, Filter.Tendsto (fun i => g i a) Filter.atTop (𝓝 0) := by
  filter_upwards [ae_tsum_ne_top_of_lintegral_summable hg hsum] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha

/-- Convergence of the squared extended norms of the differences is convergence. -/
theorem tendsto_of_tendsto_sq_enorm {E : Type*} [NormedAddCommGroup E] {u : ℕ → E} {w : E}
    (h : Filter.Tendsto (fun i => (‖u i - w‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0)) :
    Filter.Tendsto u Filter.atTop (𝓝 w) := by
  have hnn : Filter.Tendsto (fun i : ℕ => ‖u i - w‖₊ ^ 2) Filter.atTop (𝓝 0) := by
    rw [← ENNReal.tendsto_coe]
    push_cast
    simpa using h
  have hreal : Filter.Tendsto (fun i : ℕ => ‖u i - w‖ ^ 2) Filter.atTop (𝓝 0) := by
    have hco := NNReal.tendsto_coe.mpr hnn
    push_cast at hco
    simpa using hco
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hreal
  simp only [Function.comp_def, Real.sqrt_zero] at hsqrt
  refine hsqrt.congr fun i => ?_
  exact Real.sqrt_sq (norm_nonneg _)

/-- **A clamping level along which the approximation error is summable.** -/
theorem exists_seq_clampMesh_lt
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤)
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    ∃ ns : ℕ → ℕ, ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
  have hmesh : Filter.Tendsto (clampMesh P H b T) Filter.atTop (𝓝 0) :=
    tendsto_energy_window_clamp hm hbm hq hbq
  have hchoice : ∀ i : ℕ, ∃ j : ℕ, clampMesh P H b T j < ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro i
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
      refine pos_iff_ne_zero.mpr (pow_ne_zero i ?_)
      simp
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hmesh.eventually (gt_mem_nhds hpos))
    exact ⟨N, hN N le_rfl⟩
  choose ns hns using hchoice
  exact ⟨ns, hns⟩

/-- The geometric bound the summability argument uses. -/
theorem tsum_geometric_inv_two_mul_ne_top (c : ℝ≥0∞) (hc : c ≠ ⊤) :
    ∑' i : ℕ, c * ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := by
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ne_of_lt (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) ?_)
  have hne : (1 : ℝ≥0∞) - 2⁻¹ ≠ 0 := by
    rw [Ne, tsub_eq_zero_iff_le]
    exact not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num))
  exact lt_top_iff_ne_top.mpr (ENNReal.inv_ne_top.mpr hne)

/-- **Along the chosen levels the clamped versions converge to the original process almost
everywhere on the window.** -/
theorem ae_ae_tendsto_version_clamp
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Xj : ℕ → ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : ∀ j : ℕ, IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
      X₀ (clampDrift b j) (Xj j))
    {T : ℝ} (hT : 0 < T) {ns : ℕ → ℕ}
    (hns : ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) := by
  have hmeasi : ∀ i : ℕ, Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro i
    have hjoint : Measurable fun q : Ω × ℝ => (‖Xj (ns i) q.2 q.1 - X q.2 q.1‖₊ : ℝ≥0∞) ^ 2 :=
      ((((hXj (ns i)).measurable_uncurry.sub
        hX.measurable_uncurry).nnnorm).coe_nnreal_ennreal).pow_const 2
    exact hjoint.lintegral_prod_right'
  have hsum : ∑' i : ℕ, ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr (tsum_geometric_inv_two_mul_ne_top (ENNReal.ofReal T)
        ENNReal.ofReal_ne_top)))
    refine (lintegral_window_sq_norm_version_clamp_sub_le W ℱ' hcoord hX₀ hbm hbq hX
      (hXj (ns i)) hT).trans ?_
    exact mul_le_mul' le_rfl (hns i).le
  filter_upwards [ae_tsum_ne_top_of_lintegral_summable (μ := P) hmeasi hsum] with ω hω
  have hmeasω : ∀ i : ℕ, Measurable fun s : ℝ => (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    have h1 : Measurable fun s : ℝ => Xj (ns i) s ω :=
      ((hXj (ns i)).measurable_uncurry.comp (measurable_const.prodMk measurable_id))
    have h2 : Measurable fun s : ℝ => X s ω :=
      (hX.measurable_uncurry.comp (measurable_const.prodMk measurable_id))
    exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hinner := ae_tendsto_zero_of_lintegral_summable
    (μ := volume.restrict (Set.Icc (0 : ℝ) T)) hmeasω hω
  filter_upwards [hinner] with s hs
  exact tendsto_of_tendsto_sq_enorm hs

/-- **Along the chosen levels the clamped versions converge to the original process almost surely
at each positive time of the window.** -/
theorem ae_tendsto_version_clamp_at
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Xj : ℕ → ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X)
    (hXj : ∀ j : ℕ, IsVectorItoVersion W ℱ' hcoord (clampCoeff H j)
      (fun p k => measurable_clampCoeff hm j p k)
      (fun p k => progressivelyMeasurable_clampCoeff hpg j p k)
      (fun p k T' hT' => energy_clampCoeff_lt_top hm j p k T' hT')
      X₀ (clampDrift b j) (Xj j))
    {T : ℝ} {ns : ℕ → ℕ}
    (hns : ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i)
    {s : ℝ} (hs : 0 < s) (hsT : s ≤ T) :
    ∀ᵐ ω ∂P, Filter.Tendsto (fun i => Xj (ns i) s ω) Filter.atTop (𝓝 (X s ω)) := by
  have hmeasi : ∀ i : ℕ, Measurable fun ω : Ω =>
      (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    have h1 : Measurable fun ω : Ω => Xj (ns i) s ω := (hXj (ns i)).measurable s
    have h2 : Measurable fun ω : Ω => X s ω := hX.measurable s
    exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hsum : ∑' i : ℕ, ∫⁻ ω, (‖Xj (ns i) s ω - X s ω‖₊ : ℝ≥0∞) ^ 2 ∂P ≠ ⊤ := by
    have hgeom := tsum_geometric_inv_two_mul_ne_top (1 : ℝ≥0∞) (by simp)
    refine ne_of_lt (lt_of_le_of_lt (ENNReal.tsum_le_tsum fun i => ?_)
      (lt_top_iff_ne_top.mpr hgeom))
    refine (lintegral_sq_norm_version_clamp_sub_le W ℱ' hcoord hX₀ hbm hbq hX
      (hXj (ns i)) hs hsT).trans ?_
    rw [one_mul]
    exact (hns i).le
  filter_upwards [ae_tendsto_zero_of_lintegral_summable (μ := P) hmeasi hsum] with ω hω
  exact tendsto_of_tendsto_sq_enorm hω

/-- A version starts at its initial value. -/
theorem version_ae_eq_zero
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hpg : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hq : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {b : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (hX : IsVectorItoVersion W ℱ' hcoord H hm hpg hq X₀ b X) :
    X 0 =ᵐ[P] X₀ := by
  have hzero : ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k) (H p k) (hm p k) (hpg p k) (hq p k) 0
        =ᵐ[P] 0 :=
    fun p k => stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ' (hcoord k) (H p k)
      (hm p k) (hpg p k) (hq p k) le_rfl
  have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k) (H p k) (hm p k) (hpg p k) (hq p k) 0 ω
        = 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact hzero p k
  filter_upwards [hX.ae_eq 0 le_rfl, hall] with ω hω hz
  rw [hω]
  funext p
  have hdrift : ∫ s in Set.Icc (0 : ℝ) 0, b p ω s ∂volume = 0 := by
    rw [show Set.Icc (0 : ℝ) 0 = {(0 : ℝ)} from Set.Icc_self 0,
      MeasureTheory.setIntegral_measure_zero _ Real.volume_singleton]
  simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, hdrift]
  have : ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k) (H p k)
      (hm p k) (hpg p k) (hq p k) 0 ω = 0 :=
    Finset.sum_eq_zero fun k _ => hz p k
  rw [this]
  ring

end ClampProcess

end Clamped

end LevyStochCalc.Brownian.Ito
