/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoAlgebra

/-!
# Moments of a Brownian increment

The moments of a Brownian increment, and the independence of a random variable measurable
before the increment from every power of it. These are the inputs to the fourth-moment bound
on the elementary integral.

## Main statements

* `integral_pow_gaussianReal_zero` — the moments of a centred real Gaussian scale with the
  standard deviation.
* `integral_pow_gaussianReal_odd` — the odd moments of the standard real Gaussian vanish.
* `integral_increment_sq`, `integral_increment_pow_four` — the second and fourth moments of a
  Brownian increment.
* `integral_mul_increment_pow` — a random variable measurable before `a` factors out of the
  integral against a power of the increment over `(a, b]`.
* `memLp_increment`, `memLp_mul_increment` — a Brownian increment, and a bounded random
  variable times one, have moments of every order.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- The fourth moment of the standard real Gaussian distribution. -/
noncomputable def gaussianFourthMoment : ℝ :=
  ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)

theorem gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun x => by positivity

/-- Every power of the identity is integrable for a real Gaussian distribution. -/
theorem integrable_pow_gaussianReal (m : ℕ) (hm : m ≠ 0) (μ' : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ m) (gaussianReal μ' v) := by
  have h : MemLp (id : ℝ → ℝ) (m : ℝ≥0∞) (gaussianReal μ' v) :=
    memLp_id_gaussianReal' _ (by simp)
  refine (h.integrable_norm_pow hm).mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Powers of a centred real Gaussian scale with the standard deviation. -/
theorem integral_pow_gaussianReal_zero (v : ℝ≥0) (m : ℕ) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 v)
      = Real.sqrt v ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hsq : NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) * 1 = v := by
    rw [mul_one]
    exact NNReal.eq (by simp [Real.sq_sqrt v.coe_nonneg])
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := 1) (Real.sqrt v)
    rw [mul_zero, hsq] at h
    exact h
  conv_lhs => rw [← hmap]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]

/-- The odd moments of the standard real Gaussian vanish. -/
theorem integral_pow_gaussianReal_odd (m : ℕ) (hm : Odd m) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have h1 : ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
      = ∫ x : ℝ, (-x) ^ m ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hm.neg_pow] at h1
  rw [integral_neg] at h1
  linarith

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

/-- The moments of a Brownian increment scale with the square root of its length. -/
theorem integral_increment_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (m : ℕ) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
      = Real.sqrt (b - a) ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [← integral_map hmeas.aemeasurable
      (f := fun x : ℝ => x ^ m) (by fun_prop),
    W.increment_gaussian ha hab, integral_pow_gaussianReal_zero]
  rfl

/-- Odd moments of a Brownian increment vanish. -/
theorem integral_increment_pow_odd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ} (hm : Odd m) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P = 0 := by
  rw [integral_increment_pow W ha hab m, integral_pow_gaussianReal_odd m hm, mul_zero]

/-- The second moment of a Brownian increment is its length. -/
theorem integral_increment_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  rw [integral_increment_pow W ha hab 2,
    LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment 1]
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]
  norm_num

/-- The fourth moment of a Brownian increment is the square of its length, up to the fourth
moment of the standard Gaussian. -/
theorem integral_increment_pow_four {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 4 ∂P = (b - a) ^ 2 * gaussianFourthMoment := by
  rw [integral_increment_pow W ha hab 4]
  congr 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]

/-- A random variable measurable before `a` is independent of every power of the increment
over `(a, b]`. -/
theorem integral_mul_increment_pow (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
    (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
    ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
      = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P := by
  have hΔ : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hindepσ := hℱ.indep ha hab
  have hYcomap : MeasurableSpace.comap Y inferInstance ≤ ℱ a := hY.measurable.comap_le
  have hIF : ProbabilityTheory.IndepFun Y (fun ω => W.W b ω - W.W a ω) P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at hindepσ
    exact hindepσ u v (hYcomap u hu) hv
  have hIF' : ProbabilityTheory.IndepFun Y (fun ω => (W.W b ω - W.W a ω) ^ m) P :=
    hIF.comp measurable_id (measurable_id.pow_const m)
  exact hIF'.integral_mul_eq_mul_integral hYm.aestronglyMeasurable
    (hΔ.pow_const m).aestronglyMeasurable

/-- A Brownian increment has moments of every order. -/
theorem memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)

/-- A bounded random variable times a Brownian increment has moments of every order. -/
theorem memLp_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤)
    {Y : Ω → ℝ} (hYm : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    MemLp (fun ω => Y ω * (W.W b ω - W.W a ω)) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  refine MemLp.mono ((memLp_increment W ha hab p hp).const_mul C)
    (hYm.mul hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (Y ω)).trans (hC ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)

end Increments

end LevyStochCalc.Brownian.Ito
