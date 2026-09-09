/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.VectorItoTimeRiemann
import LevyStochCalc.Brownian.CrossVariationSum
import LevyStochCalc.Brownian.PolarisedQuadVar
import LevyStochCalc.Probability.AbsMoment

/-!
# The quadratic-variation Riemann sum for a vector Itô process

Multiplying the increments of two coordinates of a continuous vector Itô process across a uniform
grid and weighting them by a bounded function of the process gives a Riemann sum for
`∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`. Expanding the product of increments leaves five
pieces: the drift–drift term, the two drift–martingale terms, the compensated products on the
diagonal in the Brownian index, the cross terms off that diagonal, and a frozen-weight Riemann
sum for the density `∑ₖ H^{p,k} H^{q,k}`.

## Main statements

* `LevyStochCalc.Brownian.Ito.integral_abs_weighted_cellSum_le` — the `L¹` bound for a weighted
  sum of cell terms with a common first-absolute-moment bound.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_drift_sq_le` — the
  drift–drift term.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.integral_abs_sum_driftCross_le` — a
  drift–martingale term.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section CellSums

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`L¹` bound for a weighted sum of cell terms.** With weights bounded by `Kw` and cell terms
whose first absolute moments are all at most `ρ`, the weighted sum has first absolute moment at
most `N·Kw·ρ`. -/
theorem integral_abs_weighted_cellSum_le (N : ℕ) (w R : ℕ → Ω → ℝ)
    (hwm : ∀ i, Measurable (w i)) (hRm : ∀ i, Measurable (R i))
    {Kw : ℝ} (hKw0 : 0 ≤ Kw) (hwb : ∀ (i : ℕ) (ω : Ω), |w i ω| ≤ Kw)
    (hRint : ∀ i, Integrable (fun ω => |R i ω|) P)
    {ρ : ℝ} (hRle : ∀ i, ∫ ω, |R i ω| ∂P ≤ ρ) :
    Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P ≤ (N : ℝ) * (Kw * ρ) := by
  have hdom : Integrable (fun ω => ∑ i ∈ Finset.range N, Kw * |R i ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun i _ => (hRint i).const_mul _
  have hmeas : Measurable fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω :=
    Finset.measurable_sum _ fun i _ => (hwm i).mul (hRm i)
  have hpt : ∀ ω, |∑ i ∈ Finset.range N, w i ω * R i ω|
      ≤ ∑ i ∈ Finset.range N, Kw * |R i ω| := by
    intro ω
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hwb i ω) (abs_nonneg _)
  have hint : Integrable (fun ω => ∑ i ∈ Finset.range N, w i ω * R i ω) P := by
    refine hdom.mono hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hpt ω).trans (le_abs_self _)
  refine ⟨hint, ?_⟩
  calc ∫ ω, |∑ i ∈ Finset.range N, w i ω * R i ω| ∂P
      ≤ ∫ ω, ∑ i ∈ Finset.range N, Kw * |R i ω| ∂P :=
        MeasureTheory.integral_mono hint.abs hdom hpt
    _ = ∑ i ∈ Finset.range N, Kw * ∫ ω, |R i ω| ∂P := by
        rw [MeasureTheory.integral_finsetSum _ fun i _ => (hRint i).const_mul _]
        exact Finset.sum_congr rfl fun i _ => MeasureTheory.integral_const_mul _ _
    _ ≤ ∑ _i ∈ Finset.range N, Kw * ρ :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hRle i) hKw0
    _ = (N : ℝ) * (Kw * ρ) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The squared cell lengths of the uniform grid sum to `T²/m`. -/
theorem sum_unifGrid_sq_diff {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m, (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = T ^ 2 / (m : ℝ) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hterm : ∀ i ∈ Finset.range m,
      (unifGrid T m (i + 1) - unifGrid T m i) ^ 2 = (T / (m : ℝ)) ^ 2 :=
    fun i _ => by rw [unifGrid_succ_sub hm0 i]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp

/-- The first absolute moment of a sum is at most the sum of the bounds. -/
theorem integral_abs_add_le {f g : Ω → ℝ} (hf : Integrable f P) (hg : Integrable g P)
    {a b : ℝ} (ha : ∫ ω, |f ω| ∂P ≤ a) (hb : ∫ ω, |g ω| ∂P ≤ b) :
    ∫ ω, |f ω + g ω| ∂P ≤ a + b := by
  calc ∫ ω, |f ω + g ω| ∂P ≤ ∫ ω, (|f ω| + |g ω|) ∂P :=
        MeasureTheory.integral_mono (hf.add hg).abs (hf.abs.add hg.abs)
          (fun ω => abs_add_le _ _)
    _ = (∫ ω, |f ω| ∂P) + ∫ ω, |g ω| ∂P := MeasureTheory.integral_add hf.abs hg.abs
    _ ≤ a + b := add_le_add ha hb

/-- The first absolute moment of a finite sum is at most the sum of the bounds. -/
theorem integral_abs_finsetSum_le {ι : Type*} (s : Finset ι) (F : ι → Ω → ℝ)
    (hF : ∀ j ∈ s, Integrable (F j) P) (c : ι → ℝ) (hc : ∀ j ∈ s, ∫ ω, |F j ω| ∂P ≤ c j) :
    ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∑ j ∈ s, c j := by
  have hsum : Integrable (fun ω => ∑ j ∈ s, F j ω) P :=
    MeasureTheory.integrable_finsetSum _ hF
  have habs : Integrable (fun ω => ∑ j ∈ s, |F j ω|) P :=
    MeasureTheory.integrable_finsetSum _ fun j hj => (hF j hj).abs
  calc ∫ ω, |∑ j ∈ s, F j ω| ∂P ≤ ∫ ω, ∑ j ∈ s, |F j ω| ∂P :=
        MeasureTheory.integral_mono hsum.abs habs fun ω => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j ∈ s, ∫ ω, |F j ω| ∂P :=
        MeasureTheory.integral_finsetSum _ fun j hj => (hF j hj).abs
    _ ≤ ∑ j ∈ s, c j := Finset.sum_le_sum hc

end CellSums

section VectorQuadVar

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

/-- **The drift–drift term is `O(1/m)`.** -/
theorem IsVectorItoVersion.integral_abs_sum_drift_sq_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift q ω s ∂volume)) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift q ω s ∂volume)| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hDbd : ∀ (r : Fin n) (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift r ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro r ω i
    have hle := abs_setIntegral_Ioc_le (Measurable.of_uncurry_left (hbm r)) (hB r ω)
      (unifGrid_lt_succ hT hm0 i).le
    rwa [unifGrid_succ_sub hm0 i] at hle
  have hRm : ∀ i : ℕ, Measurable fun ω : Ω =>
      (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume :=
    fun i => (measurable_setIntegral_Ioc (hbm p) _ _).mul
      (measurable_setIntegral_Ioc (hbm q) _ _)
  have hRb : ∀ (i : ℕ) (ω : Ω),
      |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume|
      ≤ (B * (T / (m : ℝ))) ^ 2 := by
    intro i ω
    rw [abs_mul, pow_two]
    exact mul_le_mul (hDbd p ω i) (hDbd q ω i) (abs_nonneg _) (by positivity)
  have hRdata : ∀ i : ℕ, Integrable (fun ω : Ω =>
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume|) P
      ∧ ∫ ω, |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                bdrift q ω s ∂volume| ∂P
        ≤ (B * (T / (m : ℝ))) ^ 2 := by
    intro i
    obtain ⟨hi, hle⟩ := integral_abs_le_of_bounded (P := P) (hRm i) (by positivity) (hRb i ·)
    exact ⟨hi.abs, hle⟩
  exact integral_abs_weighted_cellSum_le m (fun i ω => φ (X (unifGrid T m i) ω)) _
    (fun i => hφc.measurable.comp (h.measurable (unifGrid T m i))) hRm hKφ0
    (fun i ω => hφbd _) (fun i => (hRdata i).1) (fun i => (hRdata i).2)

include hC0 hCH in
/-- **A drift–martingale term is `O(m^{-1/2})`.** -/
theorem IsVectorItoVersion.integral_abs_sum_driftCross_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))| ∂P
        ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hTm0 : (0 : ℝ) ≤ T / (m : ℝ) := (div_pos hT hm').le
  have hDbd : ∀ (ω : Ω) (i : ℕ),
      |∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume|
        ≤ B * (T / (m : ℝ)) := by
    intro ω i
    have hle := abs_setIntegral_Ioc_le (Measurable.of_uncurry_left (hbm p)) (hB p ω)
      (unifGrid_lt_succ hT hm0 i).le
    rwa [unifGrid_succ_sub hm0 i] at hle
  have hMdata : ∀ i : ℕ,
      Integrable (fun ω : Ω =>
          |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω|) P
        ∧ ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| ∂P
            ≤ (d : ℝ) * (C * Real.sqrt (T / (m : ℝ))) := by
    intro i
    obtain ⟨hint, hle⟩ := integral_abs_vectorItoMartingale_sub_le W ℱ hcoord H hHm hHp hHs
      hC0 hCH q (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
    rw [unifGrid_succ_sub hm0 i] at hle
    exact ⟨hint, hle⟩
  have hRm : ∀ i : ℕ, Measurable fun ω : Ω =>
      (∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
        * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω) :=
    fun i => (measurable_setIntegral_Ioc (hbm p) _ _).mul
      ((measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1))).sub
        (measurable_vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i)))
  have hRdata : ∀ i : ℕ, Integrable (fun ω : Ω =>
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)|) P
      ∧ ∫ ω, |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)| ∂P
        ≤ B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))) := by
    intro i
    have hpt : ∀ ω : Ω,
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)|
        ≤ B * (T / (m : ℝ))
          * |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| := by
      intro ω
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hDbd ω i) (abs_nonneg _)
    have hdom : Integrable (fun ω : Ω => B * (T / (m : ℝ))
        * |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω|) P :=
      (hMdata i).1.const_mul _
    have hint : Integrable (fun ω : Ω =>
        |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)|) P := by
      refine hdom.mono (hRm i).abs.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
      exact (hpt ω).trans (le_abs_self _)
    refine ⟨hint, ?_⟩
    calc ∫ ω, |(∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)| ∂P
        ≤ ∫ ω, B * (T / (m : ℝ))
            * |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| ∂P :=
          MeasureTheory.integral_mono hint hdom hpt
      _ = B * (T / (m : ℝ))
            * ∫ ω, |vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω| ∂P :=
          MeasureTheory.integral_const_mul _ _
      _ ≤ B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))) :=
          mul_le_mul_of_nonneg_left (hMdata i).2 (by positivity)
  exact integral_abs_weighted_cellSum_le m (fun i ω => φ (X (unifGrid T m i) ω)) _
    (fun i => hφc.measurable.comp (h.measurable (unifGrid T m i))) hRm hKφ0
    (fun i ω => hφbd _) (fun i => (hRdata i).1) (fun i => (hRdata i).2)

include hC0 hCH in
/-- **The compensated products on the diagonal in the Brownian index sum to `O(m^{-1/2})`.** -/
theorem IsVectorItoVersion.integral_abs_sum_polarQuadVar_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X) (p q : Fin n) (k : Fin d)
    (hma : Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := by
  have h0 : (0 : ℝ) ≤ unifGrid T m 0 := le_of_eq (unifGrid_zero T m).symm
  have hgrid : ∀ i : ℕ, unifGrid T m i < unifGrid T m (i + 1) := unifGrid_lt_succ hT hm0
  have hg : ∀ i : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont (unifGrid T m i))
      (fun ω => φ (X (unifGrid T m i) ω)) := fun i =>
    (hφc.comp_stronglyMeasurable (h.adapted (unifGrid T m i))).mono (ℱ.le_rightCont _)
  have hζmem : ∀ i : ℕ, MemLp (polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k)
      (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k)
      (unifGrid T m i) (unifGrid T m (i + 1))) 2 P := fun i =>
    memLp_two_polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
      (hHp p k) (hHp q k) (hHs p k) (hHs q k) hma hpa hqa hC0 (hCH p k) (hCH q k)
      (unifGrid_nonneg hT.le m i) (hgrid i)
  have hζmeas : ∀ i : ℕ, Measurable (polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k)
      (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k)
      (unifGrid T m i) (unifGrid T m (i + 1))) := fun i =>
    ((stronglyMeasurable_polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
      (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) (hgrid i).le).mono
        (ℱ.rightCont.le _)).measurable
  have hYmem : ∀ i : ℕ, MemLp (fun ω => φ (X (unifGrid T m i) ω)
      * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
          (hHp p k) (hHp q k) (hHs p k) (hHs q k)
          (unifGrid T m i) (unifGrid T m (i + 1)) ω) 2 P := by
    intro i
    refine MeasureTheory.MemLp.mono ((hζmem i).const_mul Kφ)
      (((hφc.measurable.comp (h.measurable (unifGrid T m i))).mul
        (hζmeas i)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hSmem := memLp_finsetSum (Finset.range m) fun i _ => hYmem i
  have hbound := integral_sq_weighted_polarQuadVarSum_le (W.W k) ℱ (hcoord k) (H p k) (H q k)
    (hHm p k) (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) hma hpa hqa hC0
    (hCH p k) (hCH q k) (unifGrid T m) h0 hgrid (fun i ω => φ (X (unifGrid T m i) ω)) hg
    hKφ0 (fun i ω => hφbd _) m
  rw [sum_unifGrid_sq_diff hT hm0] at hbound
  exact ⟨hSmem.integrable (by norm_num),
    integral_abs_le_sqrt_of_integral_sq_le ((hSmem.integrable (by norm_num)).abs)
      hSmem.integrable_sq hbound⟩

include hC0 hCH in
/-- **The cross terms off the diagonal in the Brownian index sum to `O(m^{-1/2})`.** -/
theorem IsVectorItoVersion.integral_abs_sum_offDiagCross_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, MultidimBrownianMotion.CrossWitness W ℱ j) (p q : Fin n)
    {k l : Fin d} (hkl : k ≠ l)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
            k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
              k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
          * (T ^ 2 / (m : ℝ))) := by
  have h0 : (0 : ℝ) ≤ unifGrid T m 0 := le_of_eq (unifGrid_zero T m).symm
  have hgrid : ∀ i : ℕ, unifGrid T m i < unifGrid T m (i + 1) := unifGrid_lt_succ hT hm0
  have hg : ∀ i : ℕ, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ (unifGrid T m i))
      (fun ω => φ (X (unifGrid T m i) ω)) := fun i =>
    hφc.comp_stronglyMeasurable (h.adapted (unifGrid T m i))
  have hζmem : ∀ i : ℕ, MemLp (crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k)
      (hHm q l) (hHp q l) (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1))) 2 P := fun i =>
    memLp_two_crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
      (hHs q l) hC0 (hCH p k) hC0 (hCH q l) k l (unifGrid_nonneg hT.le m i) (hgrid i)
  have hζmeas : ∀ i : ℕ, Measurable (crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k)
      (hHm q l) (hHp q l) (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1))) := fun i =>
    measurable_crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
      (hHs q l) k l _ _
  have hYmem : ∀ i : ℕ, MemLp (fun ω => φ (X (unifGrid T m i) ω)
      * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l) (hHs q l)
          k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) 2 P := by
    intro i
    refine MeasureTheory.MemLp.mono ((hζmem i).const_mul Kφ)
      (((hφc.measurable.comp (h.measurable (unifGrid T m i))).mul
        (hζmeas i)).aestronglyMeasurable) (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hKφ0]
    exact mul_le_mul_of_nonneg_right (hφbd _) (abs_nonneg _)
  have hSmem := memLp_finsetSum (Finset.range m) fun i _ => hYmem i
  have hbound := integral_sq_weighted_crossSum_le W hcoord 𝒲 (hHm p k) (hHp p k) (hHs p k)
    (hHm q l) (hHp q l) (hHs q l) hC0 (hCH p k) hC0 (hCH q l) hkl (unifGrid T m) h0 hgrid
    (fun i ω => φ (X (unifGrid T m i) ω)) hg hKφ0 (fun i ω => hφbd _) m
  rw [sum_unifGrid_sq_diff hT hm0] at hbound
  exact ⟨hSmem.integrable (by norm_num),
    integral_abs_le_sqrt_of_integral_sq_le ((hSmem.integrable (by norm_num)).abs)
      hSmem.integrable_sq hbound⟩

/-- The product of the increments of two coordinates splits into a drift–drift term, two
drift–martingale terms and the product of the martingale parts. -/
theorem IsVectorItoVersion.prod_sub_ae
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) :
    ∀ᵐ ω ∂P, (X v ω p - X u ω p) * (X v ω q - X u ω q)
      = (∫ s in Set.Ioc u v, bdrift p ω s ∂volume)
          * (∫ s in Set.Ioc u v, bdrift q ω s ∂volume)
        + (∫ s in Set.Ioc u v, bdrift p ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
        + (∫ s in Set.Ioc u v, bdrift q ω s ∂volume)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
        + (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
          * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
            - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω) := by
  filter_upwards [h.sub_ae hbm hB hu huv p, h.sub_ae hbm hB hu huv q] with ω e1 e2
  rw [e1, e2]
  ring

include hC0 hCH in
/-- The product of the martingale parts' increments splits into the compensated products on the
diagonal in the Brownian index, their compensators, and the cross terms off that diagonal. -/
theorem vectorItoMartingale_prod_eq (p q : Fin n) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (ω : Ω) :
    (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
      * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
        - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
        + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
            crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
  have hcomp : ∀ k : Fin d,
      (∫ s in Set.Icc (0 : ℝ) v, H p k ω s * H q k ω s ∂volume)
        - ∫ s in Set.Icc (0 : ℝ) u, H p k ω s * H q k ω s ∂volume
      = ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
    intro k
    refine setIntegral_Icc_sub_Icc (B := C ^ 2)
      ((Measurable.of_uncurry_left (hHm p k)).mul (Measurable.of_uncurry_left (hHm q k)))
      (fun s => ?_) hu huv
    show |H p k ω s * H q k ω s| ≤ C ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
  have key : ∀ k : Fin d,
      (∑ l : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω))
      = polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
          (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
        + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
        + ∑ l ∈ Finset.univ.erase k,
            crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l u v ω := by
    intro k
    have hcross : ∀ l : Fin d,
        (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
          * (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω)
        = crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l u v ω := fun l => rfl
    simp only [hcross]
    rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ k)]
    have hdiag : crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q k) (hHp q k)
          (hHs q k) k k u v ω
        = polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume := by
      simp only [crossIncrement, polarQuadVarIncrement]
      rw [← hcomp k]
      ring
    rw [hdiag]
  calc (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p u ω)
        * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q v ω
          - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q u ω)
      = (∑ k : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω))
          * ∑ l : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
            - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := by
        rw [vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs p u v,
          vectorItoMartingale_sub W ℱ hcoord H hHm hHp hHs q u v]
    _ = ∑ k : Fin d, ∑ l : Fin d, (coordItoIntegral W ℱ hcoord H hHm hHp hHs p k v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs p k u ω)
        * (coordItoIntegral W ℱ hcoord H hHm hHp hHs q l v ω
          - coordItoIntegral W ℱ hcoord H hHm hHp hHs q l u ω) := Finset.sum_mul_sum _ _ _ _
    _ = ∑ k : Fin d, (polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω
          + (∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ l ∈ Finset.univ.erase k,
              crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω) := Finset.sum_congr rfl fun k _ => key k
    _ = (∑ k : Fin d, polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k)
            (hHm q k) (hHp p k) (hHp q k) (hHs p k) (hHs q k) u v ω)
          + (∑ k : Fin d, ∫ s in Set.Ioc u v, H p k ω s * H q k ω s ∂volume)
          + ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
              crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l u v ω := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

include hC0 hCH in
/-- **The weighted product sum decomposes into six groups.** -/
theorem IsVectorItoVersion.quadVarRiemann_decomp_ae
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ}
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (φ : (Fin n → ℝ) → ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∀ᵐ ω ∂P, (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
      = (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω)))
        + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
              * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
                - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω)))
        + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
            φ (X (unifGrid T m i) ω)
              * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : ℕ =>
    h.prod_sub_ae hbm hB p q (unifGrid_nonneg hT.le m i)
      (unifGrid_lt_succ hT hm0 i).le] with ω hω
  have hswap : ∀ i : ℕ, (∑ k : Fin d, ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
        H p k ω s * H q k ω s ∂volume)
      = ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
          ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
    intro i
    refine (MeasureTheory.integral_finsetSum _ fun k _ => ?_).symm
    refine integrableOn_of_bounded_of_measurable (B := C ^ 2)
      ((Measurable.of_uncurry_left (hHm p k)).mul (Measurable.of_uncurry_left (hHm q k)))
      (fun s => ?_) (measure_Ioc_lt_top).ne
    show |H p k ω s * H q k ω s| ≤ C ^ 2
    rw [abs_mul, pow_two]
    exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
  have hterm : ∀ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
      * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
        * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q))
      = φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
        + φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift p ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))
        + φ (X (unifGrid T m i) ω)
          * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)), bdrift q ω s ∂volume)
            * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
              - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω))
        + (∑ k : Fin d, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, φ (X (unifGrid T m i) ω)
            * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
        + φ (X (unifGrid T m i) ω)
          * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
              ∑ k : Fin d, H p k ω s * H q k ω s ∂volume := by
    intro i _
    rw [hω i, vectorItoMartingale_prod_eq hC0 hCH p q (unifGrid_nonneg hT.le m i)
      (unifGrid_lt_succ hT hm0 i).le ω, ← hswap i]
    simp only [mul_add, Finset.mul_sum]
    ring
  have hcomm1 : (∑ i ∈ Finset.range m, ∑ k : Fin d, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω)
      = ∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω := Finset.sum_comm
  have hcomm2 : (∑ i ∈ Finset.range m, ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
        φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
      = ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
          φ (X (unifGrid T m i) ω)
            * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, hcomm1, hcomm2]

include hC0 hCH in
/-- **The weighted quadratic-variation Riemann sum converges in `L¹` at rate `√(T/m)`.** The
product of the increments of two coordinates, weighted by a bounded Lipschitz `φ(X)`, approximates
`∫_0^T φ(X_s)·(∑ₖ H^{p,k}_s H^{q,k}_s) ds`; the six groups of the decomposition contribute the six
summands of the bound. -/
theorem IsVectorItoVersion.integral_abs_quadVarRiemann_sub_le
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, MultidimBrownianMotion.CrossWitness W ℱ j)
    (hbm : ∀ m, Measurable (Function.uncurry (bdrift m))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (m : Fin n) (ω : Ω) (s : ℝ), |bdrift m ω s| ≤ B) (p q : Fin n)
    (hma : ∀ k : Fin d, Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ k : Fin d, Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {φ : (Fin n → ℝ) → ℝ} (hφc : Continuous φ) {Kφ : ℝ} (hKφ0 : 0 ≤ Kφ)
    (hφbd : ∀ x, |φ x| ≤ Kφ) {L : ℝ} (hL0 : 0 ≤ L)
    (hφlip : ∀ x y : Fin n → ℝ, |φ x - φ y| ≤ L * ‖x - y‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) P
      ∧ ∫ ω, |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
            * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
        - ∫ s in Set.Ioc (0 : ℝ) T,
            φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume| ∂P
      ≤ (m : ℝ) * (Kφ * (B * (T / (m : ℝ))) ^ 2)
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (m : ℝ) * (Kφ * (B * (T / (m : ℝ)) * ((d : ℝ) * (C * Real.sqrt (T / (m : ℝ))))))
        + (d : ℝ) * Real.sqrt (Kφ ^ 2
            * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ)))
        + (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
            * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        + L * ((d : ℝ) * C ^ 2)
          * (T * ((n : ℝ) * (B * (T / (m : ℝ))
            + (d : ℝ) * (C * Real.sqrt (T / (m : ℝ)))))) := by
  classical
  -- the weight of the frozen Riemann sum
  have hwm : Measurable (Function.uncurry fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) :=
    Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  have hA0 : (0 : ℝ) ≤ (d : ℝ) * C ^ 2 := by positivity
  have hA : ∀ (ω : Ω) (s : ℝ), |∑ k : Fin d, H p k ω s * H q k ω s| ≤ (d : ℝ) * C ^ 2 := by
    intro ω s
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ (Finset.univ : Finset (Fin d)), |H p k ω s * H q k ω s| ≤ C ^ 2 := by
      intro k _
      rw [abs_mul, pow_two]
      exact mul_le_mul (hCH p k ω s) (hCH q k ω s) (abs_nonneg _) hC0
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  -- the six groups
  obtain ⟨i1, b1⟩ := h.integral_abs_sum_drift_sq_le hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i2, b2⟩ := h.integral_abs_sum_driftCross_le hC0 hCH hbm hB0 hB p q hφc hKφ0 hφbd hT hm0
  obtain ⟨i3, b3⟩ := h.integral_abs_sum_driftCross_le hC0 hCH hbm hB0 hB q p hφc hKφ0 hφbd hT hm0
  have hpol : ∀ k : Fin d, Integrable (fun ω : Ω => ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
              (hHp p k) (hHp q k) (hHs p k) (hHs q k)
              (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
      ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
            * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
        ≤ Real.sqrt (Kφ ^ 2 * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4))
          * (T ^ 2 / (m : ℝ))) := fun k =>
    h.integral_abs_sum_polarQuadVar_le hC0 hCH p q k (hma k) (hpa k) (hqa k) hφc hKφ0 hφbd hT hm0
  have hcr : ∀ (k : Fin d), ∀ l ∈ Finset.univ.erase k,
      Integrable (fun ω : Ω => ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P
        ∧ ∫ ω, |∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                  (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
          ≤ Real.sqrt (Kφ ^ 2 * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2)
            * (T ^ 2 / (m : ℝ))) := fun k l hl =>
    h.integral_abs_sum_offDiagCross_le hC0 hCH 𝒲 p q ((Finset.mem_erase.mp hl).1.symm)
      hφc hKφ0 hφbd hT hm0
  obtain ⟨i6, b6⟩ := h.integral_abs_frozenRiemann_sub_le hC0 hCH hbm hB0 hB
    (fun ω s => ∑ k : Fin d, H p k ω s * H q k ω s) hwm hA0 hA hφc hφbd hL0 hφlip hT hm0
  -- integrability of the grouped sums
  have i4 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ i ∈ Finset.range m,
      φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ => (hpol k).1
  have i5 : Integrable (fun ω : Ω => ∑ k : Fin d, ∑ l ∈ Finset.univ.erase k,
      ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
            (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω) P :=
    MeasureTheory.integrable_finsetSum _ fun k _ =>
      MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1
  -- the bounds on the two grouped sums
  have b4 : ∫ ω, |∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
            (hHp p k) (hHp q k) (hHs p k) (hHs q k)
            (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
        * (3 * ((2 * (6 + gaussianFourthMoment) + 2) * (2 * C) ^ 4)) * (T ^ 2 / (m : ℝ))) := by
    refine (integral_abs_finsetSum_le _ _ (fun k _ => (hpol k).1) _
      (fun k _ => (hpol k).2)).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have b5 : ∫ ω, |∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
        φ (X (unifGrid T m i) ω)
          * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
              (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω| ∂P
      ≤ (d : ℝ) ^ 2 * Real.sqrt (Kφ ^ 2
        * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
    have hsqrt0 : (0 : ℝ) ≤ Real.sqrt (Kφ ^ 2
        * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) :=
      Real.sqrt_nonneg _
    refine (integral_abs_finsetSum_le _ _
      (fun k _ => MeasureTheory.integrable_finsetSum _ fun l hl => (hcr k l hl).1)
      (fun k => ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
        * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))))
      (fun k _ => integral_abs_finsetSum_le _ _ (fun l hl => (hcr k l hl).1) _
        (fun l hl => (hcr k l hl).2))).trans ?_
    have hk : ∀ k : Fin d, ∑ _l ∈ Finset.univ.erase k, Real.sqrt (Kφ ^ 2
          * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ)))
        ≤ (d : ℝ) * Real.sqrt (Kφ ^ 2
          * ((6 + gaussianFourthMoment) * (C ^ 4 + C ^ 4) / 2) * (T ^ 2 / (m : ℝ))) := by
      intro k
      refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun l _ _ => hsqrt0)).trans ?_
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    refine (Finset.sum_le_sum fun k _ => hk k).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring_nf
    exact le_rfl
  -- assemble
  have hae : (fun ω : Ω => |(∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
        * ((X (unifGrid T m (i + 1)) ω p - X (unifGrid T m i) ω p)
          * (X (unifGrid T m (i + 1)) ω q - X (unifGrid T m i) ω q)))
      - ∫ s in Set.Ioc (0 : ℝ) T,
          φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume|)
      =ᵐ[P] fun ω => |((((∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume))
            + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift p ω s ∂volume)
                * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m (i + 1)) ω
                  - vectorItoMartingale W ℱ hcoord H hHm hHp hHs q (unifGrid T m i) ω))))
            + (∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ((∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                    bdrift q ω s ∂volume)
                * (vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m (i + 1)) ω
                  - vectorItoMartingale W ℱ hcoord H hHm hHp hHs p (unifGrid T m i) ω))))
            + (∑ k : Fin d, ∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * polarQuadVarIncrement (W.W k) ℱ (hcoord k) (H p k) (H q k) (hHm p k) (hHm q k)
                  (hHp p k) (hHp q k) (hHs p k) (hHs q k)
                  (unifGrid T m i) (unifGrid T m (i + 1)) ω))
            + (∑ k : Fin d, ∑ l ∈ Finset.univ.erase k, ∑ i ∈ Finset.range m,
              φ (X (unifGrid T m i) ω)
                * crossIncrement W hcoord (hHm p k) (hHp p k) (hHs p k) (hHm q l) (hHp q l)
                    (hHs q l) k l (unifGrid T m i) (unifGrid T m (i + 1)) ω)
          + ((∑ i ∈ Finset.range m, φ (X (unifGrid T m i) ω)
              * ∫ s in Set.Ioc (unifGrid T m i) (unifGrid T m (i + 1)),
                  ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)
            - ∫ s in Set.Ioc (0 : ℝ) T,
                φ (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume)| := by
    filter_upwards [h.quadVarRiemann_decomp_ae hC0 hCH hbm hB p q φ hT hm0] with ω hω
    rw [hω]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · refine (((((i1.add i2).add i3).add i4).add i5).add i6).congr ?_
    filter_upwards [h.quadVarRiemann_decomp_ae hC0 hCH hbm hB p q φ hT hm0] with ω hω
    simp only [Pi.add_apply]
    rw [hω]
    ring
  rw [MeasureTheory.integral_congr_ae hae]
  exact integral_abs_add_le ((((i1.add i2).add i3).add i4).add i5) i6
    (integral_abs_add_le (((i1.add i2).add i3).add i4) i5
      (integral_abs_add_le ((i1.add i2).add i3) i4
        (integral_abs_add_le (i1.add i2) i3 (integral_abs_add_le i1 i2 b1 b2) b3) b4) b5) b6

end VectorQuadVar

end LevyStochCalc.Brownian.Ito
