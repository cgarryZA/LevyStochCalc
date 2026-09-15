/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.Existence

/-!
# Young and Lipschitz pointwise rate bounds for a BSDEJ generator

Pure real-variable inequalities behind the BSDEJ contraction estimate: a weighted Young
inequality (`two_mul_mul_le_young`), a three-term square bound (`sq_add_add_le_three`), a bound
of the `Fin d → ℝ` sup norm by the sum of squared coordinates (`sq_norm_pi_le_sum_sq`), their
combination into a pointwise bound on the squared increment of a Lipschitz generator
(`sq_generator_sub_le`) and on `2 * (a * Δf)` for that increment (`two_mul_mul_generator_sub_le`
and its negated-argument form `two_mul_mul_generator_sub_le'`), and the contraction threshold on
the Young weight `β = max 2 (24 * L ^ 2)` (`contraction_factor_le`).
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Contraction

/-- Weighted Young's inequality: twice a product is at most `β / 2` times the square of the
first factor plus `2 / β` times the square of the second, for any positive weight `β`. -/
theorem two_mul_mul_le_young {β : ℝ} (hβ : 0 < β) (a b : ℝ) :
    2 * (a * b) ≤ β / 2 * a ^ 2 + 2 / β * b ^ 2 := by
  have hβ' : β ≠ 0 := hβ.ne'
  have h2β : (0 : ℝ) < 2 * β := by linarith
  have key : β / 2 * a ^ 2 + 2 / β * b ^ 2 - 2 * (a * b)
      = (β * a - 2 * b) ^ 2 / (2 * β) := by
    field_simp
    ring
  have hnn : (0 : ℝ) ≤ (β * a - 2 * b) ^ 2 / (2 * β) := div_nonneg (sq_nonneg _) h2β.le
  linarith [key, hnn]

/-- The square of a sum of three reals is at most three times the sum of their squares. -/
theorem sq_add_add_le_three (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (a - c)]

/-- The (sup-norm) norm on `Fin d → ℝ`, squared, is at most the sum of the squared
coordinates. -/
theorem sq_norm_pi_le_sum_sq {d : ℕ} (z : Fin d → ℝ) : ‖z‖ ^ 2 ≤ ∑ j, z j ^ 2 := by
  have hnn : (0 : ℝ) ≤ Real.sqrt (∑ j, z j ^ 2) := Real.sqrt_nonneg _
  have hbound : ‖z‖ ≤ Real.sqrt (∑ j, z j ^ 2) := by
    rw [pi_norm_le_iff_of_nonneg hnn]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun j _ => sq_nonneg (z j)) (Finset.mem_univ i))
  calc ‖z‖ ^ 2 ≤ (Real.sqrt (∑ j, z j ^ 2)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hbound 2
    _ = ∑ j, z j ^ 2 := Real.sq_sqrt (by positivity)

variable {d : ℕ} {E : Type*} [MeasurableSpace E] {ν : Measure E}
variable {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-- Squared pointwise bound on the increment of a generator `f(s, y, z, u)` (with no
forward-process argument) that is Lipschitz, in the `ℝ≥0∞`-valued clause `hlip`, in `(y, z, u)`
for the `L²(ν)` distance of the jump variable, at a pair `(u₁, u₂)` whose `L²(ν)` distance is
finite. -/
theorem sq_generator_sub_le (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) :
    (f s y₁ z₁ u₁ - f s y₂ z₂ u₂) ^ 2
      ≤ 3 * L ^ 2 * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  set A : ℝ≥0∞ := ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν with hA
  -- Real-valued form of the `ℝ≥0∞` Lipschitz clause, by the technique of
  -- `Existence.abs_sub_le_of_lipschitz` (which is stated for a generator carrying an extra
  -- forward-process argument `x` that this clause has none of; the conversion itself never
  -- uses `x`, so it is reproduced here directly rather than routed through `BSDEJData`).
  have hroot : A ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt A.toReal) := by
    rw [Real.sqrt_eq_rpow, ← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by norm_num),
      ENNReal.ofReal_toReal hu]
  have key := hlip s y₁ y₂ z₁ z₂ u₁ u₂
  rw [hroot] at key
  have hne : ENNReal.ofReal L * ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
      + ENNReal.ofReal (Real.sqrt A.toReal)) ≠ ⊤ := by finiteness
  have hmono := ENNReal.toReal_mono hne key
  rw [ENNReal.toReal_mul, ENNReal.toReal_add
      (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ENNReal.coe_ne_top⟩) ENNReal.ofReal_ne_top,
    ENNReal.toReal_add ENNReal.coe_ne_top ENNReal.coe_ne_top, ENNReal.coe_toReal,
    ENNReal.coe_toReal, ENNReal.coe_toReal, ENNReal.toReal_ofReal hL,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _), coe_nnnorm, coe_nnnorm, coe_nnnorm,
    Real.norm_eq_abs, Real.norm_eq_abs] at hmono
  -- hmono : |f s y₁ z₁ u₁ - f s y₂ z₂ u₂| ≤ L * (|y₁ - y₂| + ‖z₁ - z₂‖ + √A.toReal)
  set Δf := f s y₁ z₁ u₁ - f s y₂ z₂ u₂
  set dy := |y₁ - y₂|
  set dz := ‖z₁ - z₂‖
  set r := Real.sqrt A.toReal
  have hΔf_sq : Δf ^ 2 ≤ (L * (dy + dz + r)) ^ 2 := by
    have h0 : 0 ≤ |Δf| := abs_nonneg _
    have hp := pow_le_pow_left₀ h0 hmono 2
    rwa [sq_abs] at hp
  have hthree : (dy + dz + r) ^ 2 ≤ 3 * (dy ^ 2 + dz ^ 2 + r ^ 2) := sq_add_add_le_three dy dz r
  have hLsq : (0 : ℝ) ≤ L ^ 2 := sq_nonneg L
  have hstep : (L * (dy + dz + r)) ^ 2 ≤ L ^ 2 * (3 * (dy ^ 2 + dz ^ 2 + r ^ 2)) := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hthree hLsq
  have hdy_sq : dy ^ 2 = (y₁ - y₂) ^ 2 := sq_abs _
  have hdz_sq : dz ^ 2 ≤ ∑ j, (z₁ j - z₂ j) ^ 2 := by
    have h := sq_norm_pi_le_sum_sq (z₁ - z₂)
    simpa [Pi.sub_apply] using h
  have hr_sq : r ^ 2 = A.toReal := Real.sq_sqrt ENNReal.toReal_nonneg
  have hmono2 : dy ^ 2 + dz ^ 2 + r ^ 2
      ≤ (y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2) + A.toReal := by
    rw [hdy_sq, hr_sq]; linarith [hdz_sq]
  have hfinal : L ^ 2 * (3 * (dy ^ 2 + dz ^ 2 + r ^ 2))
      ≤ 3 * L ^ 2 * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2) + A.toReal) := by
    nlinarith [mul_le_mul_of_nonneg_left hmono2 hLsq]
  calc Δf ^ 2 ≤ (L * (dy + dz + r)) ^ 2 := hΔf_sq
    _ ≤ L ^ 2 * (3 * (dy ^ 2 + dz ^ 2 + r ^ 2)) := hstep
    _ ≤ 3 * L ^ 2 * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2) + A.toReal) := hfinal

/-- Weighted-Young combination of `two_mul_mul_le_young` and `sq_generator_sub_le`: twice the
product of a real `a` with the increment of a Lipschitz generator `f`, bounded by `β / 2 * a ^ 2`
plus `6 * L ^ 2 / β` times the same three-term sum as in `sq_generator_sub_le`. -/
theorem two_mul_mul_generator_sub_le {β : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) (a : ℝ) :
    2 * (a * (f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      ≤ β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  have hyoung := two_mul_mul_le_young hβ a (f s y₁ z₁ u₁ - f s y₂ z₂ u₂)
  have hsq := sq_generator_sub_le hL hlip s y₁ y₂ z₁ z₂ u₁ u₂ hu
  have hβnn : (0 : ℝ) ≤ 2 / β := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hβnn
  have heq : 2 / β * (3 * L ^ 2 *
        ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal))
      = 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
    ring
  linarith [hyoung, hmul, heq]

/-- The negated-argument form of `two_mul_mul_generator_sub_le`, as used by the drift pairing
`∫ ω, X s ω * (-Δf) ∂P` in the weighted energy identity. -/
theorem two_mul_mul_generator_sub_le' {β : ℝ} (hβ : 0 < β) (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) (a : ℝ) :
    2 * (a * -(f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      ≤ β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by
  have h := two_mul_mul_generator_sub_le hβ hL hlip s y₁ y₂ z₁ z₂ u₁ u₂ hu (-a)
  calc 2 * (a * -(f s y₁ z₁ u₁ - f s y₂ z₂ u₂))
      = 2 * (-a * (f s y₁ z₁ u₁ - f s y₂ z₂ u₂)) := by ring
    _ ≤ β / 2 * (-a) ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := h
    _ = β / 2 * a ^ 2 + 6 * L ^ 2 / β * ((y₁ - y₂) ^ 2 + (∑ j, (z₁ j - z₂ j) ^ 2)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal) := by ring

/-- At the Young weight `β = max 2 (24 * L ^ 2)`, the contraction coefficient `6 * L ^ 2 / β` is
at most `1 / 4` and `β` is itself at least `2`. -/
theorem contraction_factor_le (L : ℝ) :
    6 * L ^ 2 / max 2 (24 * L ^ 2) ≤ 1 / 4 ∧ (2 : ℝ) ≤ max 2 (24 * L ^ 2) := by
  refine ⟨?_, le_max_left _ _⟩
  rcases le_total (24 * L ^ 2) 2 with h | h
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right h]
    have hL2pos : (0 : ℝ) < L ^ 2 := by linarith
    have h24 : (0 : ℝ) < 24 * L ^ 2 := by linarith
    rw [div_le_div_iff₀ h24 (by norm_num : (0 : ℝ) < 4)]
    nlinarith

end LevyStochCalc.BSDEJ.Contraction
