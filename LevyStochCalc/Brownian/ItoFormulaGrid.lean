/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoIncrementMoment

/-!
# The uniform grid and the third-moment remainder

The uniform partition of `[0, T]` into `m` cells, and the bound it gives for the sum of third
absolute moments of the increments of an Itô process — the size of the Taylor remainder in
Itô's formula.

## Main statements

* `LevyStochCalc.Brownian.Ito.unifGrid` — the uniform grid on `[0, T]`.
* `LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid` — the simple integrand carried by
  the uniform grid.
* `LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le` — the sum of third absolute
  moments of the Itô-integral increments across the grid, of order `m^{-1/2}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- `(a + b)³ ≤ 4(a³ + b³)` for nonnegative reals. -/
theorem add_pow_three_le_four {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [sq_nonneg (a - b), mul_nonneg ha hb, sq_nonneg (a + b)]

/-- The uniform grid on `[0, T]` with `m` cells. -/
noncomputable def unifGrid (T : ℝ) (m : ℕ) (i : ℕ) : ℝ := (i : ℝ) * T / (m : ℝ)

@[simp] theorem unifGrid_zero (T : ℝ) (m : ℕ) : unifGrid T m 0 = 0 := by simp [unifGrid]

theorem unifGrid_self {T : ℝ} {m : ℕ} (hm : m ≠ 0) : unifGrid T m m = T := by
  rw [unifGrid]
  field_simp

theorem unifGrid_succ_sub {T : ℝ} {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) := by
  have hm' : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hm
  rw [unifGrid, unifGrid]
  push_cast
  field_simp
  ring

theorem unifGrid_nonneg {T : ℝ} (hT : 0 ≤ T) (m i : ℕ) : 0 ≤ unifGrid T m i := by
  rw [unifGrid]
  positivity

theorem unifGrid_lt_succ {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0) (i : ℕ) :
    unifGrid T m i < unifGrid T m (i + 1) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  have h := unifGrid_succ_sub (T := T) hm i
  have : 0 < T / (m : ℝ) := div_pos hT hm'
  linarith

theorem unifGrid_le {T : ℝ} (hT : 0 ≤ T) {m i : ℕ} (hi : i ≤ m) (hm : m ≠ 0) :
    unifGrid T m i ≤ T := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm)
  rw [unifGrid, div_le_iff₀ hm']
  have : (i : ℝ) ≤ (m : ℝ) := Nat.cast_le.mpr hi
  nlinarith


/-- The simple integrand on the uniform grid of `[0, T]` with the given cell coefficients. -/
noncomputable def SimplePredictable.ofUnifGrid {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) : SimplePredictable Ω T where
  N := m
  partition := fun i => unifGrid T m (i : ℕ)
  partition_zero := by simp
  partition_le_T := le_of_eq (by simpa using unifGrid_self (T := T) hm)
  partition_strictMono := by
    refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
    simpa using unifGrid_lt_succ hT hm (i : ℕ)
  ξ := ξ
  ξ_bounded := hbdd
  ξ_measurable := hmeas

@[simp] theorem SimplePredictable.ofUnifGrid_partition {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin (m + 1)) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i = unifGrid T m (i : ℕ) := rfl

@[simp] theorem SimplePredictable.ofUnifGrid_xi {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i = ξ i := rfl

theorem SimplePredictable.ofUnifGrid_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i))
    (hadapt : ∀ i : Fin m, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (unifGrid T m (i : ℕ))) (ξ i)) :
    ∀ i : Fin (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).partition i.castSucc))
        ((SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).ξ i) := hadapt

/-- The grid integrand evaluates to the cell coefficient on each cell. -/
theorem SimplePredictable.ofUnifGrid_eval {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ξ : Fin m → Ω → ℝ) (hbdd : ∀ i : Fin m, ∃ M : ℝ, ∀ ω : Ω, |ξ i ω| ≤ M)
    (hmeas : ∀ i : Fin m, Measurable (ξ i)) (i : Fin m) {s : ℝ}
    (hs : unifGrid T m (i : ℕ) < s ∧ s ≤ unifGrid T m ((i : ℕ) + 1)) (ω : Ω) :
    (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval s ω = ξ i ω :=
  (SimplePredictable.ofUnifGrid hT hm ξ hbdd hmeas).eval_of_mem_Ioc i hs ω

section ThirdMomentSum

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
  (hp : Probability.ProgressivelyMeasurable ℱ H)
  (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)

include hℱ hC0 hCH in
/-- **The third absolute moments of the Itô-integral increments across a uniform grid sum to
`O(m^{-1/2})`.** -/
theorem sum_integral_abs_sub_pow_three_le {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    ∑ i ∈ Finset.range m,
        ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ^ 3 ∂P
      ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) := by
  have hm' : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  have hstep : ∀ i : ℕ, unifGrid T m (i + 1) - unifGrid T m i = T / (m : ℝ) :=
    unifGrid_succ_sub hm0
  have hK0 : (0 : ℝ) ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 := by
    have := gaussianFourthMoment_nonneg
    have h1 : (0 : ℝ) ≤ (6 + gaussianFourthMoment) * C ^ 4 :=
      mul_nonneg (by linarith) (by positivity)
    have h2 : (0 : ℝ) ≤ C ^ 2 := sq_nonneg C
    linarith
  have hterm : ∀ i ∈ Finset.range m,
      ∫ ω, |stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m (i + 1)) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (unifGrid T m i) ω| ^ 3 ∂P
        ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ))) := by
    intro i _
    have h := integral_abs_sub_pow_three_le W ℱ hℱ H hm hp hq hC0 hCH
      (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
    rwa [hstep i] at h
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hTm : (m : ℝ) * (T / (m : ℝ)) = T := by field_simp
  calc (m : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * (T / (m : ℝ) * Real.sqrt (T / (m : ℝ))))
      = (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
        * (((m : ℝ) * (T / (m : ℝ))) * Real.sqrt (T / (m : ℝ))) := by ring
    _ = (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) := by
        rw [hTm]
    _ ≤ (C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2 * (T * Real.sqrt (T / (m : ℝ))) :=
        le_rfl

end ThirdMomentSum

end LevyStochCalc.Brownian.Ito
