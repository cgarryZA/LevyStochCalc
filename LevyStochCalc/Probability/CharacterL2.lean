/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Characters of real variables in `L²`

For a real frequency `u` the character `x ↦ e^{iux}` has modulus one and is `|u|`-Lipschitz, and
`e^{iux} − 1` is bounded by `|u| |x|` and by two. So along `L²` convergence of real variables
`Y_n → Y` the characters `e^{iuY_n}` converge in `L²`, and a square-integrable `Y` gives a
square-integrable `e^{iuY} − 1` on any measure and a square-integrable `e^{iuY}` on a finite one.
The complex pairing `∫ F G` is the `L²` inner product of `F̄` and `G`, so it is continuous along
`L²` convergence in each argument.

## Main statements

* `LevyStochCalc.Probability.norm_exp_I_mul_sub_one_le_two` — `‖e^{it} − 1‖ ≤ 2`.
* `LevyStochCalc.Probability.integrable_exp_I_mul_mul` — a character times an integrable
  variable is integrable.
* `LevyStochCalc.Probability.memLp_exp_I_mul`, `LevyStochCalc.Probability.memLp_exp_I_mul_sub_one`
  — square integrability of `e^{iuY}` and of `e^{iuY} − 1`.
* `LevyStochCalc.Probability.memLp_mul_of_norm_le` — a bounded multiple of a square-integrable
  variable is square integrable.
* `LevyStochCalc.Probability.tendsto_integral_mul_of_tendsto_eLpNorm` — continuity of the complex
  pairing along `L²` convergence.
* `LevyStochCalc.Probability.tendsto_eLpNorm_ofReal_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_exp_I_mul_sub`,
  `LevyStochCalc.Probability.tendsto_eLpNorm_mul_sub_mul` — `L²` convergence passes to the complex
  embedding, to the characters and to bounded multiples.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Probability

/-- For real `t`, `‖e^{it} − 1‖ ≤ 2`. -/
theorem norm_exp_I_mul_sub_one_le_two (t : ℝ) :
    ‖Complex.exp (Complex.I * (t : ℂ)) - 1‖ ≤ 2 := by
  refine (norm_sub_le _ _).trans (le_of_eq ?_)
  rw [Complex.norm_exp_I_mul_ofReal, norm_one]
  norm_num

/-- The product of an integrable complex function with the character `e^{iuY}` of a real
function `Y` is integrable. -/
theorem integrable_exp_I_mul_mul {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : α → ℝ} (hY : AEStronglyMeasurable Y m) {X : α → ℂ} (hX : Integrable X m) :
    Integrable (fun x => Complex.exp (Complex.I * ((u * Y x : ℝ) : ℂ)) * X x) m := by
  refine hX.norm.mono' (((by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (Complex.I * ((u * t : ℝ) : ℂ))).comp_aestronglyMeasurable hY).mul hX.1)
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]

/-- On a finite measure the character `e^{iuY}` of a real function `Y` is square integrable. -/
theorem memLp_exp_I_mul {α : Type*} [MeasurableSpace α] {m : Measure α} [IsFiniteMeasure m]
    (u : ℝ) {Y : α → ℝ} (hY : AEStronglyMeasurable Y m) :
    MemLp (fun x => Complex.exp (Complex.I * ((u * Y x : ℝ) : ℂ))) 2 m :=
  MemLp.of_bound ((by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (Complex.I * ((u * t : ℝ) : ℂ))).comp_aestronglyMeasurable hY) 1
    (Eventually.of_forall fun x => le_of_eq (Complex.norm_exp_I_mul_ofReal _))

/-- For a square-integrable real function `Y`, `e^{iuY} − 1` is square integrable. -/
theorem memLp_exp_I_mul_sub_one {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : α → ℝ} (hY : MemLp Y 2 m) :
    MemLp (fun x => Complex.exp (Complex.I * ((u * Y x : ℝ) : ℂ)) - 1) 2 m :=
  hY.of_le_mul (c := |u|) (((by fun_prop : Continuous fun t : ℝ =>
    Complex.exp (Complex.I * ((u * t : ℝ) : ℂ)) - 1).comp_aestronglyMeasurable hY.1))
    (Eventually.of_forall fun x => by
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul])

/-- The product of a bounded complex function with a square-integrable one is square
integrable. -/
theorem memLp_mul_of_norm_le {α : Type*} [MeasurableSpace α] {m : Measure α}
    {Z X : α → ℂ} (hZ : AEStronglyMeasurable Z m) {C : ℝ} (hZC : ∀ x, ‖Z x‖ ≤ C)
    (hX : MemLp X 2 m) : MemLp (fun x => Z x * X x) 2 m :=
  hX.of_le_mul (c := C) (hZ.mul hX.1) (Eventually.of_forall fun x => by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hZC x) (norm_nonneg _))

/-- **The complex pairing `∫ F G` is continuous along `L²` convergence in each argument.** -/
theorem tendsto_integral_mul_of_tendsto_eLpNorm {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F G : ℕ → α → ℂ} {F' G' : α → ℂ} (hF : ∀ n, MemLp (F n) 2 m) (hG : ∀ n, MemLp (G n) 2 m)
    (hF' : MemLp F' 2 m) (hG' : MemLp G' 2 m)
    (hFc : Tendsto (fun n => eLpNorm (fun x => F n x - F' x) 2 m) atTop (𝓝 0))
    (hGc : Tendsto (fun n => eLpNorm (fun x => G n x - G' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, F n x * G n x ∂m) atTop (𝓝 (∫ x, F' x * G' x ∂m)) := by
  have hconj : ∀ {H : α → ℂ}, MemLp H 2 m → MemLp (fun x => starRingEnd ℂ (H x)) 2 m :=
    fun hH => hH.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hH.1)
      (Eventually.of_forall fun x => (Complex.norm_conj _).symm)
  have key : ∀ (H K : α → ℂ) (hH : MemLp H 2 m) (hK : MemLp K 2 m),
      ∫ x, H x * K x ∂m = inner ℂ ((hconj hH).toLp _) (hK.toLp K) := by
    intro H K hH hK
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [(hconj hH).coeFn_toLp, hK.coeFn_toLp] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  have hFc' : Tendsto (fun n => eLpNorm ((fun x => starRingEnd ℂ (F n x))
      - fun x => starRingEnd ℂ (F' x)) 2 m) atTop (𝓝 0) := by
    refine hFc.congr fun n => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => ?_)
    rw [Pi.sub_apply, ← map_sub, Complex.norm_conj]
  have hu := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hconj (hF n)) _ (hconj hF')).2
    hFc'
  have hv := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' G hG G' hG').2 hGc
  rw [key F' G' hF' hG']
  exact (hu.inner hv).congr fun n => (key _ _ (hF n) (hG n)).symm

/-- Real functions converging in `L²` converge in `L²` as complex functions. -/
theorem tendsto_eLpNorm_ofReal_sub {α : Type*} [MeasurableSpace α] {m : Measure α}
    {Y : ℕ → α → ℝ} {Y' : α → ℝ}
    (hc : Tendsto (fun n => eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => (Y n x : ℂ) - (Y' x : ℂ)) 2 m) atTop (𝓝 0) :=
  hc.congr fun n => eLpNorm_congr_norm_ae (Eventually.of_forall fun x => by
    rw [← Complex.ofReal_sub, Complex.norm_real])

/-- For real functions `Y_n → Y` in `L²`, the characters `e^{iuY_n} → e^{iuY}` in `L²`. -/
theorem tendsto_eLpNorm_exp_I_mul_sub {α : Type*} [MeasurableSpace α] {m : Measure α} (u : ℝ)
    {Y : ℕ → α → ℝ} {Y' : α → ℝ}
    (hc : Tendsto (fun n => eLpNorm (fun x => Y n x - Y' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))) 2 m) atTop (𝓝 0) := by
  have hbound : ∀ n, eLpNorm (fun x => Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))) 2 m
      ≤ ENNReal.ofReal |u| * eLpNorm (fun x => Y n x - Y' x) 2 m := by
    intro n
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => ?_) 2
    have h1 : Complex.exp (Complex.I * ((u * Y n x : ℝ) : ℂ))
        - Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((u * Y' x : ℝ) : ℂ))
          * (Complex.exp (Complex.I * ((u * (Y n x - Y' x) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      push_cast
      ring_nf
    rw [h1, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul, Real.norm_eq_abs, ← abs_mul]
    exact Real.norm_exp_I_mul_ofReal_sub_one_le.trans (le_of_eq (Real.norm_eq_abs _))
  have h := ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal |u|)
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hbound

/-- Multiplication by a bounded complex function preserves `L²` convergence. -/
theorem tendsto_eLpNorm_mul_sub_mul {α : Type*} [MeasurableSpace α] {m : Measure α}
    {Z : α → ℂ} {C : ℝ} (hZC : ∀ x, ‖Z x‖ ≤ C) {X : ℕ → α → ℂ} {X' : α → ℂ}
    (hc : Tendsto (fun n => eLpNorm (fun x => X n x - X' x) 2 m) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun x => Z x * X n x - Z x * X' x) 2 m) atTop (𝓝 0) := by
  have hbound : ∀ n, eLpNorm (fun x => Z x * X n x - Z x * X' x) 2 m
      ≤ ENNReal.ofReal C * eLpNorm (fun x => X n x - X' x) 2 m := fun n =>
    eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Eventually.of_forall fun x => by
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_right (hZC x) (norm_nonneg _)) 2
  have h := ENNReal.Tendsto.const_mul hc (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal C)
  rw [mul_zero] at h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h (fun _ => zero_le) hbound

end LevyStochCalc.Probability
