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
    ∃ ns : ℕ → ℕ, (∀ i : ℕ, i ≤ ns i) ∧
      ∀ i : ℕ, clampMesh P H b T (ns i) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
  have hmesh : Filter.Tendsto (clampMesh P H b T) Filter.atTop (𝓝 0) :=
    tendsto_energy_window_clamp hm hbm hq hbq
  have hchoice : ∀ i : ℕ, ∃ j : ℕ, i ≤ j ∧ clampMesh P H b T j < ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro i
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
      refine pos_iff_ne_zero.mpr (pow_ne_zero i ?_)
      simp
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hmesh.eventually (gt_mem_nhds hpos))
    exact ⟨max N i, le_max_right N i, hN (max N i) (le_max_left N i)⟩
  choose ns hge hns using hchoice
  exact ⟨ns, hge, hns⟩

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

section Limits

variable (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)

omit [IsProbabilityMeasure P] in
/-- Clamping at a level that grows to infinity converges to the identity. -/
theorem tendsto_clampAt_comp {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i) (x : ℝ) :
    Filter.Tendsto (fun i => clampAt ((ns i : ℕ) : ℝ) x) Filter.atTop (𝓝 x) := by
  obtain ⟨N, hN⟩ := exists_nat_gt |x|
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [Filter.eventually_ge_atTop N] with i hi
  refine (clampAt_eq_self ?_).symm
  have hle : (N : ℝ) ≤ ((ns i : ℕ) : ℝ) := by exact_mod_cast le_trans hi (hge i)
  linarith [hN]

/-- For almost every path, an integrand with finite energy is square integrable on the window. -/
theorem ae_memLp_two_window {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, MeasureTheory.MemLp (G ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
  filter_upwards [MeasureTheory.ae_lt_top (measurable_energyDensity hmG T) hqG.ne] with ω hω
  exact LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
    (Measurable.of_uncurry_left hmG) hω

/-- **The drift integrals of the clamped approximation converge, pathwise.** -/
theorem ae_tendsto_drift_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {b : Fin n → Ω → ℝ → ℝ} (hbm : ∀ p, Measurable (Function.uncurry (b p)))
    {T : ℝ}
    (hbq : ∀ p : Fin n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (Y i s ω) * clampDrift b (ns i) p ω s ∂volume) Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * b p ω s ∂volume)) := by
  have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hf'bd 0)
  have hint : ∀ p : Fin n, ∀ᵐ ω ∂P,
      IntegrableOn (b p ω) (Set.Icc (0 : ℝ) T) volume :=
    fun p => ae_integrableOn_of_energy_lt_top (hbm p) (hbq p)
  have hintall : ∀ᵐ ω ∂P, ∀ p : Fin n, IntegrableOn (b p ω) (Set.Icc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    exact hint
  filter_upwards [hae, hintall] with ω hω hbint
  intro p
  have haeIoc : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hω
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => K₁ * |b p ω s|) (fun i => ?_) ?_ (fun i => ?_) ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    exact (((continuous_coordDeriv hf'c p).measurable.comp
      (Measurable.of_uncurry_left (hYm i))).mul
      ((continuous_clampAt (((ns i : ℕ) : ℝ))).measurable.comp
        (Measurable.of_uncurry_left (hbm p))))
  · exact ((hbint p).mono_set Set.Ioc_subset_Icc_self).abs.const_mul K₁
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (abs_coordDeriv_le hf'bd p _)
      (abs_clampAt_le_abs (Nat.cast_nonneg _) _) (abs_nonneg _) hK₁0
  · filter_upwards [haeIoc] with s hs
    exact ((continuous_coordDeriv hf'c p).continuousAt.tendsto.comp hs).mul
      (tendsto_clampAt_comp hge (b p ω s))

/-- **The quadratic-variation integrals of the clamped approximation converge, pathwise.** -/
theorem ae_tendsto_quadVar_clamp
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} (hf''c : Continuous f'')
    {K₂ : ℝ} (hK₂0 : 0 ≤ K₂) (hf''bd : ∀ z, ‖f'' z‖ ≤ K₂)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω))) :
    ∀ᵐ ω ∂P, ∀ p q : Fin n, Filter.Tendsto (fun i => ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (Y i s ω)
          * ∑ k : Fin d, clampCoeff H (ns i) p k ω s * clampCoeff H (ns i) q k ω s ∂volume)
      Filter.atTop
      (𝓝 (∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)) := by
  have hmemall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      MeasureTheory.MemLp (H p k ω) 2 (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact ae_memLp_two_window (hm p k) (hq p k)
  filter_upwards [hae, hmemall] with ω hω hmem
  intro p q
  have haeIoc : ∀ᵐ s ∂(volume.restrict (Set.Ioc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)) :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset Set.Ioc_subset_Icc_self hω
  have hprodint : ∀ k : Fin d,
      IntegrableOn (fun s => |H p k ω s * H q k ω s|) (Set.Ioc (0 : ℝ) T) volume := by
    intro k
    have h0 : IntegrableOn (fun s => |H p k ω s * H q k ω s|) (Set.Icc (0 : ℝ) T) volume :=
      (MeasureTheory.MemLp.integrable_mul (p := 2) (q := 2) (hmem p k) (hmem q k)).abs
    exact h0.mono_set Set.Ioc_subset_Icc_self
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => K₂ * ∑ k : Fin d, |H p k ω s * H q k ω s|) (fun i => ?_) ?_ (fun i => ?_) ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    refine ((continuous_coordDeriv₂ hf''c p q).measurable.comp
      (Measurable.of_uncurry_left (hYm i))).mul ?_
    refine Finset.measurable_sum _ fun k _ => ?_
    exact ((continuous_clampAt (((ns i : ℕ) : ℝ))).measurable.comp
      (Measurable.of_uncurry_left (hm p k))).mul
      ((continuous_clampAt (((ns i : ℕ) : ℝ))).measurable.comp
        (Measurable.of_uncurry_left (hm q k)))
  · exact (MeasureTheory.integrable_finsetSum _ fun k _ => hprodint k).const_mul K₂
  · refine Filter.Eventually.of_forall fun s => ?_
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul (abs_coordDeriv₂_le hf''bd p q _) ?_ (abs_nonneg _) hK₂0
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [abs_mul, abs_mul]
    exact mul_le_mul (abs_clampAt_le_abs (Nat.cast_nonneg _) _)
      (abs_clampAt_le_abs (Nat.cast_nonneg _) _) (abs_nonneg _) (abs_nonneg _)
  · filter_upwards [haeIoc] with s hs
    refine ((continuous_coordDeriv₂ hf''c p q).continuousAt.tendsto.comp hs).mul ?_
    exact tendsto_finsetSum _ fun k _ =>
      (tendsto_clampAt_comp hge (H p k ω s)).mul (tendsto_clampAt_comp hge (H q k ω s))

omit [IsProbabilityMeasure P] in
/-- A pointwise bound `|u| ≤ c|v|` squares into a bound on the extended norms. -/
theorem sq_enorm_le_of_abs_le {c : ℝ} (hc : 0 ≤ c) {u v : ℝ} (h : |u| ≤ c * |v|) :
    (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : ‖u‖₊ ≤ Real.toNNReal c * ‖v‖₊ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal c hc]
    simpa [Real.norm_eq_abs] using h
  calc (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal c * ‖v‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 := by
        exact pow_le_pow_left' (by exact_mod_cast h1) 2
    _ = ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, ← Real.toNNReal_pow hc]
        rfl

/-- **The energies of the perturbed diffusion integrands vanish.** -/
theorem tendsto_energy_coordDeriv_diff
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {G : Ω → ℝ → ℝ} (hmG : Measurable (Function.uncurry G)) {T : ℝ}
    (hqG : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P) Filter.atTop (𝓝 0) := by
  set c : ℝ := 2 * K₁ with hc
  have hc0 : (0 : ℝ) ≤ c := by positivity
  have hbnd : ∀ (i : ℕ) (ω : Ω) (s : ℝ),
      (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro i ω s
    refine sq_enorm_le_of_abs_le hc0 ?_
    rw [abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    calc |coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)|
        ≤ |coordDeriv f' p (Y i s ω)| + |coordDeriv f' p (X s ω)| :=
          abs_sub_le_abs_add_abs _ _
      _ ≤ K₁ + K₁ := add_le_add (abs_coordDeriv_le hf'bd p _) (abs_coordDeriv_le hf'bd p _)
      _ = c := by rw [hc]; ring
  have hjoint : ∀ i : ℕ, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s) := by
    intro i
    exact (((continuous_coordDeriv hf'c p).measurable.comp (hYm i)).sub
      ((continuous_coordDeriv hf'c p).measurable.comp hXm)).mul hmG
  have hFmeas : ∀ i : ℕ, Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun i => measurable_energyDensity (hjoint i) T
  have hGmeas : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := measurable_energyDensity hmG T
  -- inner limit, for almost every path
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun i : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (𝓝 0) := by
    filter_upwards [hae, MeasureTheory.ae_lt_top hGmeas hqG.ne] with ω hω hfin
    have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) T))
      (F := fun (i : ℕ) (s : ℝ) =>
        (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _s : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun i => (((Measurable.of_uncurry_left (hjoint i)).nnnorm).coe_nnreal_ennreal).pow_const 2)
      (fun i => Filter.Eventually.of_forall fun s => hbnd i ω s) ?_ ?_
    · simpa using hlim
    · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
      exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin).ne
    · filter_upwards [hω] with s hs
      have hcd : Filter.Tendsto (fun i : ℕ => coordDeriv f' p (Y i s ω)) Filter.atTop
          (𝓝 (coordDeriv f' p (X s ω))) :=
        (continuous_coordDeriv hf'c p).continuousAt.tendsto.comp hs
      have hconstX : Filter.Tendsto (fun _ : ℕ => coordDeriv f' p (X s ω)) Filter.atTop
          (𝓝 (coordDeriv f' p (X s ω))) := tendsto_const_nhds
      have hconstG : Filter.Tendsto (fun _ : ℕ => G ω s) Filter.atTop (𝓝 (G ω s)) :=
        tendsto_const_nhds
      have hzero : Filter.Tendsto (fun i : ℕ =>
          (coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s) Filter.atTop (𝓝 0) := by
        have hs2 := (hcd.sub hconstX).mul hconstG
        simpa using hs2
      have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2 := by
        have h1 : Continuous fun x : ℝ => (‖x‖₊ ^ 2 : ℝ≥0) := continuous_nnnorm.pow 2
        have h2 := ENNReal.continuous_coe.comp h1
        simp only [Function.comp_def, ENNReal.coe_pow] at h2
        exact h2
      have hres := (hcont.tendsto (0 : ℝ)).comp hzero
      simp only [Function.comp_def] at hres
      have hz0 : ((‖(0 : ℝ)‖₊ : ℝ≥0∞)) ^ 2 = 0 := by simp
      rw [hz0] at hres
      exact hres
  have hdom : ∀ (i : ℕ) (ω : Ω), (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      ≤ ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro i ω
    rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact MeasureTheory.lintegral_mono fun s => hbnd i ω s
  -- outer limit
  have hlim := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (μ := P)
    (F := fun (i : ℕ) (ω : Ω) => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ω : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ENNReal.ofReal (c ^ 2) * ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun i => Filter.Eventually.of_forall fun ω => hdom i ω) ?_ hinner
  · simpa using hlim
  · rw [MeasureTheory.lintegral_const_mul' _ _ (by simp : ENNReal.ofReal (c ^ 2) ≠ ⊤)]
    exact (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hqG).ne

omit [IsProbabilityMeasure P] in
/-- Additivity of the window energy. -/
theorem lintegral_window_add {f g : Ω → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) (hg : Measurable (Function.uncurry g)) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (f ω s + g ω s) ∂volume ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume ∂P := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (f ω s + g ω s) ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, g ω s ∂volume :=
    fun ω => MeasureTheory.lintegral_add_left (Measurable.of_uncurry_left hf) _
  simp_rw [hinner]
  exact MeasureTheory.lintegral_add_left hf.lintegral_prod_right' _

omit [IsProbabilityMeasure P] in
/-- Constants come out of the window energy. -/
theorem lintegral_window_const_mul {f : Ω → ℝ → ℝ≥0∞}
    (hf : Measurable (Function.uncurry f)) {c : ℝ≥0∞} (hc : c ≠ ⊤) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, c * f ω s ∂volume ∂P
      = c * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume ∂P := by
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, c * f ω s ∂volume
      = c * ∫⁻ s in Set.Icc (0 : ℝ) T, f ω s ∂volume :=
    fun ω => MeasureTheory.lintegral_const_mul' _ _ hc
  simp_rw [hinner]
  exact MeasureTheory.lintegral_const_mul' _ _ hc

/-- **The energies of the differences of the diffusion integrands vanish.** -/
theorem tendsto_energy_diffusionIntegrand_clamp
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ} (hf'c : Continuous f')
    {K₁ : ℝ} (hK₁0 : 0 ≤ K₁) (hf'bd : ∀ z, ‖f' z‖ ≤ K₁)
    {H : Fin n → Fin d → Ω → ℝ → ℝ} (hm : ∀ p k, Measurable (Function.uncurry (H p k)))
    {T : ℝ}
    (hq : ∀ (p : Fin n) (k : Fin d), ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {X : ℝ → Ω → Fin n → ℝ} {Y : ℕ → ℝ → Ω → Fin n → ℝ}
    (hYm : ∀ i, Measurable (Function.uncurry fun ω s => Y i s ω))
    (hXm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω))
    {ns : ℕ → ℕ} (hge : ∀ i, i ≤ ns i)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Filter.Tendsto (fun i => Y i s ω) Filter.atTop (𝓝 (X s ω)))
    (p : Fin n) (k : Fin d) :
    Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s
          - coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) := by
  have hnsTop : Filter.Tendsto ns Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono hge Filter.tendsto_id
  have hclamp : Filter.Tendsto (fun i : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (𝓝 0) :=
    (tendsto_energy_clampAt_sub (hm p k) (hq p k).ne).comp hnsTop
  have hderiv := tendsto_energy_coordDeriv_diff hf'c hK₁0 hf'bd (hm p k) (hq p k)
    hYm hXm hae p
  have hbound : ∀ (i : ℕ) (ω : Ω) (s : ℝ),
      (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s
        - coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (ENNReal.ofReal (K₁ ^ 2)
          * (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
        + 2 * (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
      := by
    intro i ω s
    have hsplit : coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s
        - coordDeriv f' p (X s ω) * H p k ω s
        = coordDeriv f' p (Y i s ω) * (clampCoeff H (ns i) p k ω s - H p k ω s)
          + (coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * H p k ω s := by ring
    rw [hsplit]
    set A : ℝ := coordDeriv f' p (Y i s ω) * (clampCoeff H (ns i) p k ω s - H p k ω s) with hA
    set B : ℝ := (coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * H p k ω s with hB
    have hAle : (‖A‖₊ : ℝ≥0∞) ^ 2
        ≤ ENNReal.ofReal (K₁ ^ 2)
          * (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 := by
      rw [hA]
      refine sq_enorm_le_of_abs_le hK₁0 ?_
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_coordDeriv_le hf'bd p _) (abs_nonneg _)
    calc (‖A + B‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖A‖₊ : ℝ≥0∞) ^ 2 + (‖B‖₊ : ℝ≥0∞) ^ 2) := sq_nnnorm_add_le_two_mul A B
      _ = 2 * (‖A‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖B‖₊ : ℝ≥0∞) ^ 2 := by rw [mul_add]
      _ ≤ 2 * (ENNReal.ofReal (K₁ ^ 2)
            * (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
          + 2 * (‖B‖₊ : ℝ≥0∞) ^ 2 := by
          exact add_le_add (mul_le_mul' le_rfl hAle) le_rfl
  have hlimbound : Filter.Tendsto (fun i : ℕ =>
      2 * (ENNReal.ofReal (K₁ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun i : ℕ =>
        2 * (ENNReal.ofReal (K₁ ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))
        Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := 2 * ENNReal.ofReal (K₁ ^ 2)) hclamp
        (Or.inr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top))
      rw [mul_zero] at hc
      exact hc.congr fun i => by rw [mul_assoc]
    have h2 : Filter.Tendsto (fun i : ℕ =>
        2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P) Filter.atTop (𝓝 0) := by
      have hc := ENNReal.Tendsto.const_mul (a := (2 : ℝ≥0∞)) hderiv (Or.inr (by simp))
      rw [mul_zero] at hc
      exact hc
    simpa using h1.add h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlimbound
    (fun i => zero_le) (fun i => ?_)
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coordDeriv f' p (Y i s ω) * clampCoeff H (ns i) p k ω s
          - coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (2 * (ENNReal.ofReal (K₁ ^ 2)
              * (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2)
            + 2 * (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω))
                * H p k ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω =>
          MeasureTheory.lintegral_mono fun s => hbound i ω s
    _ = _ := by
        have hAm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
            ENNReal.ofReal (K₁ ^ 2)
              * (‖clampCoeff H (ns i) p k ω s - H p k ω s‖₊ : ℝ≥0∞) ^ 2) :=
          ((((measurable_clampCoeff hm (ns i) p k).sub
            (hm p k)).nnnorm).coe_nnreal_ennreal).pow_const 2 |>.const_mul _
        have hBm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
            (‖(coordDeriv f' p (Y i s ω) - coordDeriv f' p (X s ω)) * H p k ω s‖₊ : ℝ≥0∞) ^ 2) :=
          (((((continuous_coordDeriv hf'c p).measurable.comp (hYm i)).sub
            ((continuous_coordDeriv hf'c p).measurable.comp hXm)).mul
              (hm p k)).nnnorm).coe_nnreal_ennreal.pow_const 2
        rw [lintegral_window_add (hAm.const_mul _) (hBm.const_mul _) T,
          lintegral_window_const_mul hAm (by simp) T,
          lintegral_window_const_mul hBm (by simp) T,
          lintegral_window_const_mul
            (((((measurable_clampCoeff hm (ns i) p k).sub
              (hm p k)).nnnorm).coe_nnreal_ennreal).pow_const 2)
            (by simp : ENNReal.ofReal (K₁ ^ 2) ≠ ⊤) T]

end Limits

end Clamped

end LevyStochCalc.Brownian.Ito
