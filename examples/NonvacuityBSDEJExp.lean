/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc
import NonvacuityDrivers
import NonvacuityBSDEJ

/-!
# The explicit solution of a backward equation with the identity generator

The scalar backward equation

  `Y_t = W_1 + ∫_t^1 Y_s ds − ∫_t^1 Z_s dW_s − ∫_t^1 ∫_ℝ U_s(e) Ñ(ds, de)`

driven by a Lévy driver with one Brownian coordinate and a Poisson random measure of intensity
`dt ⊗ δ_1` on `[0, ∞) × ℝ`. The generator is `f(s, y, z, u) = y`, the horizon is `T = 1` and the
terminal datum is the Brownian value `W_1`. Since `d(e^{1-t} W_t) = −e^{1-t} W_t dt + e^{1-t} dW_t`,
the value process is `Y_t = e^{1-t} W_t`, the Brownian integrand is the windowed weight
`e^{1-s} 1_{(0, 1]}(s)` and the jump integrand vanishes.

## Main statements

* `exists_solvesBSDEJ_expZ` — the equation is solved by `e^{1-t}` times a continuous modification
  of the Brownian motion, together with the integrand pair `(e^{1-s} 1_{(0, 1]}, 0)`.
* `energy_expZ` — the energy of `e^{1-s} 1_{(0, 1]}` on `[0, 1]` is `(e² − 1)/2`.
* `energy_eq_of_solvesBSDEJ` — every solution triple of the equation has Brownian integrand of
  energy `(e² − 1)/2` on `[0, 1]`.
* `exists_solvesBSDEJ_generator_id_energy_ne_zero` — on a probability space carrying such a
  driver the equation has this solution triple and every solution triple has Brownian integrand
  of nonzero energy.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer 2013,
  §4.1.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Examples.Nonvacuity

open LevyStochCalc.BSDEJ.Solves
open LevyStochCalc.Driver (LevyDriver)
open LevyStochCalc.Brownian.Ito (IsVectorItoVersion)

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### The test function `(t, x) ↦ e^{1-t} x` -/

/-- The `i`-th coordinate functional on `ℝ²`. -/
noncomputable def coordFun (i : Fin 2) : (Fin 2 → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj i

/-- The value of the `i`-th coordinate functional on `ℝ²`. -/
theorem coordFun_apply (i : Fin 2) (z : Fin 2 → ℝ) : coordFun i z = z i := rfl

/-- The function `(t, x) ↦ e^{1-t} x` on `ℝ²`, with the time in coordinate `0`. -/
noncomputable def expTest (z : Fin 2 → ℝ) : ℝ := Real.exp (1 - z 0) * z 1

/-- The Fréchet derivative of `expTest`. -/
noncomputable def expTestD (z : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] ℝ :=
  (-(Real.exp (1 - z 0) * z 1)) • coordFun 0 + Real.exp (1 - z 0) • coordFun 1

/-- The second Fréchet derivative of `expTest`. -/
noncomputable def expTestD2 (z : Fin 2 → ℝ) : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) →L[ℝ] ℝ :=
  ((Real.exp (1 - z 0) * z 1) • coordFun 0
        - Real.exp (1 - z 0) • coordFun 1).smulRight (coordFun 0)
    + ((-Real.exp (1 - z 0)) • coordFun 0).smulRight (coordFun 1)

/-- A coordinate functional is its own Fréchet derivative. -/
theorem hasFDerivAt_coordFun (i : Fin 2) (z : Fin 2 → ℝ) :
    HasFDerivAt (fun w : Fin 2 → ℝ => w i) (coordFun i) z := (coordFun i).hasFDerivAt

/-- The Fréchet derivative of the time factor `(t, x) ↦ e^{1-t}` of `expTest`. -/
theorem hasFDerivAt_expFactor (z : Fin 2 → ℝ) :
    HasFDerivAt (fun w : Fin 2 → ℝ => Real.exp (1 - w 0))
      ((-Real.exp (1 - z 0)) • coordFun 0) z := by
  refine (((hasFDerivAt_const (1 : ℝ) z).sub (hasFDerivAt_coordFun 0 z)).exp).congr_fderiv ?_
  ext v
  simp

/-- `expTestD` is the Fréchet derivative of `expTest`. -/
theorem hasFDerivAt_expTest (z : Fin 2 → ℝ) : HasFDerivAt expTest (expTestD z) z := by
  refine ((hasFDerivAt_expFactor z).mul (hasFDerivAt_coordFun 1 z)).congr_fderiv ?_
  ext v
  simp [expTestD, coordFun_apply]
  ring

/-- `expTestD2` is the Fréchet derivative of `expTestD`. -/
theorem hasFDerivAt_expTestD (z : Fin 2 → ℝ) : HasFDerivAt expTestD (expTestD2 z) z := by
  have hα : HasFDerivAt (fun w : Fin 2 → ℝ => -(Real.exp (1 - w 0) * w 1))
      ((Real.exp (1 - z 0) * z 1) • coordFun 0 - Real.exp (1 - z 0) • coordFun 1) z := by
    refine ((hasFDerivAt_expTest z).neg).congr_fderiv ?_
    ext v
    simp [expTestD, coordFun_apply]
    ring
  exact (hα.smul_const (coordFun 0)).add ((hasFDerivAt_expFactor z).smul_const (coordFun 1))

/-- `expTest` is twice continuously differentiable. -/
theorem contDiff_expTest : ContDiff ℝ 2 expTest := by
  have h0 : ContDiff ℝ 2 fun z : Fin 2 → ℝ => z 0 := (coordFun 0).contDiff
  have h1 : ContDiff ℝ 2 fun z : Fin 2 → ℝ => z 1 := (coordFun 1).contDiff
  exact (Real.contDiff_exp.comp (contDiff_const.sub h0)).mul h1

/-! ### The exponential weight -/

/-- A process that does not depend on the sample point and is continuous in time is
progressively measurable. -/
theorem progressivelyMeasurable_of_time (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {φ : ℝ → ℝ}
    (hφ : Continuous φ) : Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) s => φ s :=
  Probability.ProgressivelyMeasurable.of_isStronglyProgressive
    (MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
      (fun _ => stronglyMeasurable_const) fun _ => hφ)

/-- A constant integrand has finite energy on every bounded window. -/
theorem lintegral_sq_const_lt_top (P : Measure Ω) [IsProbabilityMeasure P] (c T : ℝ) :
    ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
    measure_univ, mul_one]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top

/-- The extended norm of a nonnegative real is its image under `ENNReal.ofReal`. -/
theorem ennnorm_of_nonneg {x : ℝ} (hx : 0 ≤ x) : (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal x := by
  simp [Real.nnnorm_of_nonneg hx, ENNReal.ofReal, Real.toNNReal_of_nonneg hx]

/-- The weight `e^{1-s}` is bounded by `e` at nonnegative times. -/
theorem nnnorm_expWeight_le {s : ℝ} (hs : 0 ≤ s) :
    (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ≤ (‖Real.exp 1‖₊ : ℝ≥0∞) := by
  refine ENNReal.coe_le_coe.mpr ?_
  rw [← NNReal.coe_le_coe]
  simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  exact Real.exp_le_exp.mpr (by linarith)

/-- The weight `e^{1-s}` has finite energy on every bounded window. -/
theorem expWeight_sq (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (_hT : 0 < T) :
    ∫⁻ _ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hinner : ∀ _ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal T := by
    intro _
    calc ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Real.exp (1 - s)‖₊ : ℝ≥0∞) ^ 2 ∂volume
        ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem (measurableSet_Icc (a := (0 : ℝ)) (b := T))] with s hs
          exact pow_le_pow_left' (nnnorm_expWeight_le hs.1) 2
      _ = (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 * ENNReal.ofReal T := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  refine lt_of_le_of_lt (lintegral_mono hinner) ?_
  rw [lintegral_const, measure_univ, mul_one]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top

/-! ### The integrands of the equation -/

/-- The windowed exponential weight `e^{1-s} 1_{(0, 1]}(s)`, read as a one-dimensional Brownian
integrand. -/
noncomputable def expZ (Ω) [MeasurableSpace Ω] : ℝ → Ω → (Fin 1 → ℝ) :=
  fun s _ _ => Set.indicator (Set.Ioc (0 : ℝ) 1) (fun r => Real.exp (1 - r)) s

/-- The value of `expZ` at a time is the windowed exponential weight at that time. -/
theorem expZ_apply (s : ℝ) (ω : Ω) (i : Fin 1) :
    expZ Ω s ω i = Set.indicator (Set.Ioc (0 : ℝ) 1) (fun r => Real.exp (1 - r)) s := rfl

/-- `expZ` is the exponential weight times the indicator of the window `(0, 1]`. -/
theorem expZ_eq_mul (s : ℝ) (ω : Ω) (i : Fin 1) :
    expZ Ω s ω i = Real.exp (1 - s) * Brownian.Ito.indIoc Ω 0 1 ω s := by
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1 <;> simp [expZ, Brownian.Ito.indIoc, hs]

/-- `expZ` is dominated by the exponential weight. -/
theorem abs_expZ_le (s : ℝ) (ω : Ω) (i : Fin 1) :
    |expZ Ω s ω i| ≤ |Real.exp (1 - s)| := by
  rw [expZ_apply]
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs, abs_zero]
    exact abs_nonneg _

/-- Each coordinate of `expZ` is jointly measurable. -/
theorem expZ_meas (i : Fin 1) :
    Measurable (Function.uncurry fun (ω : Ω) s => expZ Ω s ω i) := by
  have h : Measurable fun r : ℝ => Real.exp (1 - r) :=
    Real.continuous_exp.measurable.comp (measurable_const.sub measurable_id)
  exact (h.indicator measurableSet_Ioc).comp measurable_snd

/-- Each coordinate of `expZ` is progressively measurable for every filtration. -/
theorem expZ_prog (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (i : Fin 1) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => expZ Ω s ω i := by
  have hfun : (fun (ω : Ω) s => expZ Ω s ω i)
      = fun (ω : Ω) s => Real.exp (1 - s) * Brownian.Ito.indIoc Ω 0 1 ω s := by
    funext ω s
    exact expZ_eq_mul s ω i
  rw [hfun]
  exact (progressivelyMeasurable_of_time ℱ
      (Real.continuous_exp.comp (continuous_const.sub continuous_id))).mul
    (Brownian.Ito.progressivelyMeasurable_indIoc₀ ℱ zero_lt_one)

/-- `expZ` vanishes off the horizon `[0, 1]`. -/
theorem expZ_vanish (ω : Ω) (s : ℝ) (hs : s ∉ Set.Icc (0 : ℝ) 1) : expZ Ω s ω = 0 := by
  have hs' : s ∉ Set.Ioc (0 : ℝ) 1 := fun h => hs ⟨h.1.le, h.2⟩
  funext i
  simp [expZ, Set.indicator_of_notMem hs']

/-- Each coordinate of `expZ` is square integrable on every bounded window. -/
theorem expZ_sq_global (P : Measure Ω) [IsProbabilityMeasure P] (i : Fin 1) (T : ℝ)
    (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖expZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  Brownian.Ito.energy_lt_top_of_abs_le (fun ω s => abs_expZ_le s ω i) (expWeight_sq P) T hT

/-- Each coordinate of `expZ` has finite energy on the horizon `[0, 1]`. -/
theorem expZ_sq (i : Fin 1) : Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω i) ≠ ⊤ :=
  (expZ_sq_global P i 1 zero_lt_one).ne

/-- The zero jump integrand is jointly measurable in the sample point, the time and the mark. -/
theorem zeroJump_meas : Measurable fun _p : Ω × ℝ × ℝ => (0 : ℝ) := measurable_const

/-- The zero jump integrand is marked progressively measurable for the augmented joint
filtration. -/
theorem zeroJump_prog (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    Probability.MarkedProgressivelyMeasurable (augJoint D)
      fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ) :=
  Poisson.Compensated.markedProgressivelyMeasurable_zero (augJoint D)

/-- The zero jump integrand has finite marked energy on the horizon `[0, 1]`. -/
theorem zeroJump_sq : Poisson.Compensated.markedEnergy P (Measure.dirac (1 : ℝ)) 1
    (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) ≠ ⊤ := by
  simp [Poisson.Compensated.markedEnergy]

/-! ### Itô's formula for `e^{1-t} W_t` -/

section Version

variable (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))

/-- A continuous adapted modification of the first Brownian coordinate is a version of the
one-dimensional vector Itô process with zero initial value, zero drift and unit diffusion. -/
theorem isVectorItoVersion_modification {V : ℝ → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t => V t ω)
    (hadapt : ∀ t, Measurable[augJoint D t] (V t))
    (hae : ∀ t : ℝ, 0 ≤ t → V t =ᵐ[P] (D.W.W 0).W t) :
    IsVectorItoVersion D.W (augJoint D) D.isBrownianFiltration_aug
      (fun _ _ (_ : Ω) (_ : ℝ) => (1 : ℝ)) (fun _ _ => measurable_const)
      (fun _ _ => Probability.progressivelyMeasurable_const (augJoint D) (1 : ℝ))
      (fun _ _ => lintegral_sq_one_lt_top P) (fun (_ : Ω) (_ : Fin 1) => (0 : ℝ))
      (fun (_ : Fin 1) (_ : Ω) (_ : ℝ) => (0 : ℝ)) (fun t ω (_ : Fin 1) => V t ω) where
  continuous_path := fun ω => continuous_pi fun _ => hcont ω
  adapted := by
    intro t
    letI : MeasurableSpace Ω := augJoint D t
    exact (measurable_pi_lambda _ fun _ => hadapt t).stronglyMeasurable
  ae_eq := by
    intro t ht
    filter_upwards [hae t ht, Brownian.Ito.stochasticIntegralBrownian_one (D.W.W 0)
      (augJoint D) (D.isBrownianFiltration_aug 0) measurable_const
      (Probability.progressivelyMeasurable_const (augJoint D) (1 : ℝ))
      (lintegral_sq_one_lt_top P) ht] with ω h1 h2
    funext m
    simp only [Brownian.Ito.vectorItoProcess, Brownian.Ito.vectorItoMartingale,
      Brownian.Ito.coordItoIntegral, Fin.sum_univ_one, integral_zero, zero_add, add_zero]
    rw [h1, ← h2]

/-- The multidimensional Itô integral of `expZ` is the one-dimensional Itô integral of its
single coordinate. -/
theorem multidim_expZ_eq (t : ℝ) (ω : Ω) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
        D.isBrownianFiltration_aug (expZ Ω) expZ_meas (expZ_prog (augJoint D))
        (sq_int_global_of_vanishing expZ_vanish expZ_sq) t ω
      = Brownian.Ito.stochasticIntegralBrownian (D.W.W 0) (augJoint D)
        (D.isBrownianFiltration_aug 0) (fun ω' s => expZ Ω s ω' 0) (expZ_meas 0)
        (expZ_prog (augJoint D) 0) (sq_int_global_of_vanishing expZ_vanish expZ_sq 0) t ω := by
  simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral, Fin.sum_univ_one]
  rfl

/-- Itô's formula for `e^{1-t} V_t` at a positive time of the horizon `[0, 1]`, with `V` a
continuous adapted modification of the first Brownian coordinate. -/
theorem expIto_identity {V : ℝ → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t => V t ω)
    (hadapt : ∀ t, Measurable[augJoint D t] (V t))
    (hae : ∀ t : ℝ, 0 ≤ t → V t =ᵐ[P] (D.W.W 0).W t)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    ∀ᵐ ω ∂P, Real.exp (1 - t) * V t ω
      = -(∫ s in Set.Ioc (0 : ℝ) t, Real.exp (1 - s) * V s ω)
        + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
            D.isBrownianFiltration_aug (expZ Ω) expZ_meas (expZ_prog (augJoint D))
            (sq_int_global_of_vanishing expZ_vanish expZ_sq) t ω := by
  classical
  have hver := isVectorItoVersion_modification D hcont hadapt hae
  have hcoordD : ∀ (q : Fin 1) (ω : Ω) (s : ℝ),
      coordDeriv expTestD q.succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω)
        = Real.exp (1 - s) := by
    intro q ω s
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    simp [coordDeriv, expTestD, coordFun_apply, Brownian.Ito.timeAugProcess]
  have hfun : ∀ (q : Fin 1) (k : Fin 1),
      (fun (ω : Ω) (s : ℝ) => coordDeriv expTestD q.succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ))
        = fun (_ : Ω) (s : ℝ) => Real.exp (1 - s) := by
    intro q k
    funext ω s
    rw [hcoordD q ω s, mul_one]
  have hmg : ∀ (q : Fin 1) (k : Fin 1), Measurable (Function.uncurry
      fun (ω : Ω) (s : ℝ) => coordDeriv expTestD q.succ
        (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ)) := by
    intro q k
    rw [hfun q k]
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.sub measurable_id)).comp measurable_snd
  have hpg : ∀ (q : Fin 1) (k : Fin 1), Probability.ProgressivelyMeasurable (augJoint D)
      fun (ω : Ω) (s : ℝ) => coordDeriv expTestD q.succ
        (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ) := by
    intro q k
    rw [hfun q k]
    exact progressivelyMeasurable_of_time (augJoint D)
      (Real.continuous_exp.comp (continuous_const.sub continuous_id))
  have hqg : ∀ (q : Fin 1) (k : Fin 1) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv expTestD q.succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω)
        * (1 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro q k T' hT'
    simp only [hcoordD, mul_one]
    exact expWeight_sq P T' hT'
  have hform := hver.itoFormulaTime (C := 1) zero_le_one (fun _ _ _ _ => by norm_num)
    (fun _ => measurable_const) (fun _ => measurable_const) (B := 0) le_rfl
    (fun _ _ _ => by norm_num)
    (fun _ _ _ T' _ => lintegral_sq_const_lt_top P ((1 : ℝ) + 1) T')
    hasFDerivAt_expTest hasFDerivAt_expTestD contDiff_expTest hmg hpg hqg ht0
  have hexpTest : ∀ (r : ℝ) (ω : Ω),
      expTest (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) r ω)
        = Real.exp (1 - r) * V r ω := by
    intro r ω
    simp [expTest, Brownian.Ito.timeAugProcess]
  have hcoord0 : ∀ (r : ℝ) (ω : Ω), coordDeriv expTestD 0
      (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) r ω)
        = -(Real.exp (1 - r) * V r ω) := by
    intro r ω
    simp [coordDeriv, expTestD, coordFun_apply, Brownian.Ito.timeAugProcess]
  have hcoord2 : ∀ (q q' : Fin 1) (r : ℝ) (ω : Ω), coordDeriv₂ expTestD2
      q.succ q'.succ (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) r ω) = 0 := by
    intro q q' r ω
    have hq : q = 0 := Subsingleton.elim _ _
    have hq' : q' = 0 := Subsingleton.elim _ _
    subst hq
    subst hq'
    simp [coordDeriv₂, expTestD2, coordFun_apply]
  have hagree : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
      coordDeriv expTestD (0 : Fin 1).succ
          (Brownian.Ito.timeAugProcess (fun t ω (_ : Fin 1) => V t ω) s ω) * (1 : ℝ)
        = expZ Ω s ω 0 := by
    refine Filter.Eventually.of_forall fun ω => ?_
    have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
    filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with s hs0 hs
    have hsne : s ≠ 0 := by simpa using hs0
    have hs' : s ∈ Set.Ioc (0 : ℝ) 1 :=
      ⟨lt_of_le_of_ne hs.1 (Ne.symm hsne), hs.2.trans ht1⟩
    rw [hcoordD 0 ω s, mul_one, expZ_apply, Set.indicator_of_mem hs']
  have hSI := Brownian.Ito.stochasticIntegralBrownian_congr_ae (D.W.W 0) (augJoint D)
    (D.isBrownianFiltration_aug 0) (hmg 0 0) (hpg 0 0) (hqg 0 0) (expZ_meas 0)
    (expZ_prog (augJoint D) 0) (sq_int_global_of_vanishing expZ_vanish expZ_sq 0) ht0 hagree
  filter_upwards [hform, hSI, hae 0 le_rfl, (D.W.W 0).initial_zero] with ω h1 h2 h3 h4
  have hV0 : V 0 ω = 0 := h3.trans h4
  simp only [Fin.sum_univ_one] at h1
  rw [h2] at h1
  simp only [hexpTest, hcoord0, hcoord2, mul_zero, zero_mul, integral_zero, integral_neg,
    add_zero, hV0, sub_zero] at h1
  rw [multidim_expZ_eq D t ω]
  linarith [h1]

/-- Itô's formula for `e^{1-t} V_t` at a time of the horizon `[0, 1]`, with `V` a continuous
adapted modification of the first Brownian coordinate. -/
theorem expIto_identity_of_mem {V : ℝ → Ω → ℝ}
    (hcont : ∀ ω, Continuous fun t => V t ω)
    (hadapt : ∀ t, Measurable[augJoint D t] (V t))
    (hae : ∀ t : ℝ, 0 ≤ t → V t =ᵐ[P] (D.W.W 0).W t)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ∀ᵐ ω ∂P, Real.exp (1 - t) * V t ω
      = -(∫ s in Set.Ioc (0 : ℝ) t, Real.exp (1 - s) * V s ω)
        + Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W (augJoint D)
            D.isBrownianFiltration_aug (expZ Ω) expZ_meas (expZ_prog (augJoint D))
            (sq_int_global_of_vanishing expZ_vanish expZ_sq) t ω := by
  rcases eq_or_lt_of_le ht.1 with h0 | h0
  · have hzero := Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (D.W.W 0)
      (augJoint D) (D.isBrownianFiltration_aug 0) (fun ω' s => expZ Ω s ω' 0) (expZ_meas 0)
      (expZ_prog (augJoint D) 0) (sq_int_global_of_vanishing expZ_vanish expZ_sq 0)
      (le_refl (0 : ℝ))
    filter_upwards [hae 0 le_rfl, (D.W.W 0).initial_zero, hzero] with ω e1 e2 e3
    rw [← h0, multidim_expZ_eq D 0 ω]
    simp only [Pi.zero_apply] at e3
    rw [e1, e2, e3]
    simp
  · exact expIto_identity D hcont hadapt hae h0 ht.2

end Version

/-! ### The solution triple -/

/-- The backward equation with generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon
`1` is solved by `e^{1-t}` times a continuous modification of the Brownian motion, the integrand
`e^{1-s} 1_{(0, 1]}` in the Brownian coordinate and the zero jump integrand. -/
theorem exists_solvesBSDEJ_expZ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))) :
    ∃ Y : ℝ → Ω → ℝ,
      SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y (expZ Ω)
          (fun _ _ _ => (0 : ℝ)) ∧
        ∀ t, Y t =ᵐ[P] fun ω => Real.exp (1 - t) * (D.W.W 0).W t ω := by
  obtain ⟨N, hsub, hNmeas, hNnull⟩ :=
    exists_measurable_superset_of_null (MeasureTheory.ae_iff.1 (D.W.W 0).continuous_paths)
  have hnotN : ∀ᵐ ω ∂P, ω ∈ Nᶜ := by
    rw [MeasureTheory.ae_iff]
    simpa using hNnull
  have hVcont : ∀ ω : Ω, Continuous fun t => Set.indicator Nᶜ ((D.W.W 0).W t) ω := by
    intro ω
    by_cases hω : ω ∈ N
    · have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = 0 :=
        fun s => Set.indicator_of_notMem (by simpa using hω) _
      simp only [hpt]
      exact continuous_const
    · have hc : Continuous fun s => (D.W.W 0).W s ω := by
        by_contra hcc
        exact hω (hsub hcc)
      have hpt : ∀ s : ℝ, Set.indicator Nᶜ ((D.W.W 0).W s) ω = (D.W.W 0).W s ω :=
        fun s => Set.indicator_of_mem hω _
      simp only [hpt]
      exact hc
  have hVadapt : ∀ t : ℝ, Measurable[augJoint D t] (Set.indicator Nᶜ ((D.W.W 0).W t)) := by
    intro t
    have hle0 : augJoint D 0 ≤ augJoint D t := by
      rcases le_total (0 : ℝ) t with h | h
      · exact (augJoint D).mono h
      · exact D.augFiltration_le_of_nonpos h
    have hNt : MeasurableSet[augJoint D t] Nᶜ :=
      (hle0 _ (D.measurableSet_augFiltration_of_null hNmeas hNnull)).compl
    have hW : Measurable[augJoint D t] ((D.W.W 0).W t) :=
      (D.isBrownianFiltration_aug 0).measurable t
    exact hW.indicator hNt
  have hVae : ∀ t : ℝ, 0 ≤ t →
      (Set.indicator Nᶜ ((D.W.W 0).W t)) =ᵐ[P] (D.W.W 0).W t := by
    intro t _
    filter_upwards [hnotN] with ω hω
    exact Set.indicator_of_mem hω _
  have hVjoint : Measurable (Function.uncurry fun t => Set.indicator Nᶜ ((D.W.W 0).W t)) := by
    have hfun : (Function.uncurry fun t => Set.indicator Nᶜ ((D.W.W 0).W t))
        = Set.indicator (Prod.snd ⁻¹' Nᶜ) (Function.uncurry (D.W.W 0).W) := by
      funext p
      by_cases hp : p.2 ∈ Nᶜ
      · rw [Set.indicator_of_mem (show p ∈ Prod.snd ⁻¹' Nᶜ from hp)]
        exact Set.indicator_of_mem hp _
      · rw [Set.indicator_of_notMem (show p ∉ Prod.snd ⁻¹' Nᶜ from hp)]
        exact Set.indicator_of_notMem hp _
    rw [hfun]
    exact (D.W.W 0).joint_measurable.indicator (measurable_snd hNmeas.compl)
  have hYcont : ∀ ω : Ω,
      Continuous fun t => Real.exp (1 - t) * Set.indicator Nᶜ ((D.W.W 0).W t) ω :=
    fun ω => (Real.continuous_exp.comp (continuous_const.sub continuous_id)).mul (hVcont ω)
  refine ⟨fun t ω => Real.exp (1 - t) * Set.indicator Nᶜ ((D.W.W 0).W t) ω, ?_, ?_⟩
  · refine
      { Z_meas := expZ_meas
        Z_prog := expZ_prog (augJoint D)
        Z_vanish := expZ_vanish
        Z_sq := expZ_sq
        U_meas := zeroJump_meas
        U_prog := zeroJump_prog D
        U_vanish := fun _ _ _ _ => rfl
        U_sq := zeroJump_sq
        Y_meas := ?_
        Y_adapted := ?_
        Y_cadlag := ?_
        Y_sup := ?_
        eqn := ?_ }
    · exact ((Real.continuous_exp.measurable.comp
        (measurable_const.sub measurable_id)).comp measurable_fst).mul hVjoint
    · intro t
      exact ((hVadapt t).const_mul (Real.exp (1 - t))).mono
        ((augJoint D).le_rightCont t) le_rfl
    · intro ω t
      exact ⟨((hYcont ω).tendsto t).mono_left nhdsWithin_le_nhds,
        Real.exp (1 - t) * Set.indicator Nᶜ ((D.W.W 0).W t) ω,
        ((hYcont ω).tendsto t).mono_left nhdsWithin_le_nhds⟩
    · have hbound : ∀ ω : Ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
          (‖Real.exp (1 - r) * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2)
          ≤ ⨆ r ∈ Set.Icc (0 : ℝ) 1,
            (‖Real.exp 1 * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2 := by
        intro ω
        refine iSup₂_le fun r hr => ?_
        refine le_trans (pow_le_pow_left' ?_ 2)
          (le_iSup₂ (f := fun r (_ : r ∈ Set.Icc (0 : ℝ) 1) =>
            (‖Real.exp 1 * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) r hr)
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simp only [coe_nnnorm, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith [hr.1]))
          (abs_nonneg _)
      have hcongr : ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
          (‖Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P
          = ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1, (‖(D.W.W 0).W r ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hnotN] with ω hω
        exact iSup_congr fun r => iSup_congr fun _ => by rw [Set.indicator_of_mem hω]
      have hcad : ∀ᵐ ω ∂P, ∀ r : ℝ, Filter.Tendsto (fun s => (D.W.W 0).W s ω)
          (nhdsWithin r (Set.Ioi r)) (nhds ((D.W.W 0).W r ω)) := by
        filter_upwards [(D.W.W 0).continuous_paths] with ω hω r
        exact (hω.tendsto r).mono_left nhdsWithin_le_nhds
      have hdoob := BSDEJ.SupBound.lintegral_biSup_sq_le_of_martingale (μ := P)
        (Brownian.Martingale.brownian_martingale_natural (D.W.W 0)) zero_le_one hcad
      have hfin : ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
          (‖Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
        rw [hcongr]
        refine lt_of_le_of_lt hdoob ?_
        rw [lintegral_nnnorm_sq_brownian (D.W.W 0) zero_lt_one]
        exact lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) ENNReal.ofReal_ne_top)
      calc ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
            (‖Real.exp (1 - r) * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P
          ≤ ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
              (‖Real.exp 1 * Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
            lintegral_mono hbound
        _ = (‖Real.exp 1‖₊ : ℝ≥0∞) ^ 2 * ∫⁻ ω, (⨆ r ∈ Set.Icc (0 : ℝ) 1,
              (‖Set.indicator Nᶜ ((D.W.W 0).W r) ω‖₊ : ℝ≥0∞) ^ 2) ∂P :=
            BSDEJ.SupBound.lintegral_biSup_sq_const_mul (Real.exp 1)
              (fun r => Set.indicator Nᶜ ((D.W.W 0).W r)) 1
        _ < ⊤ := ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) hfin
    · intro t ht
      have hJ : ∀ t' : ℝ, 0 ≤ t' → ∀ᵐ ω ∂P,
          Poisson.Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
              (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) zeroJump_meas (zeroJump_prog D)
              (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) zeroJump_sq) t' ω
            = 0 := by
        intro t' ht'
        filter_upwards [Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing D.N
          D.isPoissonFiltration_aug (fun (_ : Ω) (_ : ℝ) (_ : ℝ) => (0 : ℝ)) zeroJump_meas
          (zeroJump_prog D) (marked_sq_int_global_of_vanishing (fun _ _ _ _ => rfl) zeroJump_sq)
          ht' (fun _ _ _ _ => rfl)] with ω hω
        simpa using hω
      have hsplit : ∀ ω : Ω,
          (∫ s in Set.Icc t 1, Real.exp (1 - s) * Set.indicator Nᶜ ((D.W.W 0).W s) ω)
            = (∫ s in Set.Ioc (0 : ℝ) 1,
                Real.exp (1 - s) * Set.indicator Nᶜ ((D.W.W 0).W s) ω)
              - ∫ s in Set.Ioc (0 : ℝ) t,
                  Real.exp (1 - s) * Set.indicator Nᶜ ((D.W.W 0).W s) ω := by
        intro ω
        have hdisj : Disjoint (Set.Ioc (0 : ℝ) t) (Set.Ioc t 1) :=
          Set.disjoint_left.mpr fun x hx hx' => absurd hx.2 (not_le.mpr hx'.1)
        have hun := setIntegral_union (μ := volume) hdisj measurableSet_Ioc
          ((hYcont ω).integrableOn_Ioc) ((hYcont ω).integrableOn_Ioc)
        rw [Set.Ioc_union_Ioc_eq_Ioc ht.1 ht.2] at hun
        rw [integral_Icc_eq_integral_Ioc, hun]
        ring
      filter_upwards [expIto_identity_of_mem D hVcont hVadapt hVae ht,
        expIto_identity_of_mem D hVcont hVadapt hVae (Set.right_mem_Icc.mpr zero_le_one),
        hJ 1 zero_le_one, hJ t ht.1, hVae 1 zero_le_one] with ω e1 e2 e3 e4 e5
      rw [e3, e4, hsplit ω, ← e5]
      norm_num at e2
      linarith [e1, e2]
  · intro t
    filter_upwards [hnotN] with ω hω
    rw [Set.indicator_of_mem hω]

/-! ### The energy of the Brownian integrand -/

/-- The integral of `e^{2-2s}` over the window `(0, 1]`. -/
theorem integral_expWeight_sq :
    ∫ s in Set.Ioc (0 : ℝ) 1, Real.exp (2 - 2 * s) = (Real.exp 2 - 1) / 2 := by
  have hfun : Continuous fun s : ℝ => Real.exp (2 - 2 * s) :=
    Real.continuous_exp.comp (continuous_const.sub (continuous_const.mul continuous_id))
  have hd : ∀ s : ℝ, HasDerivAt (fun r : ℝ => -(1 / 2 : ℝ) * Real.exp (2 - 2 * r))
      (Real.exp (2 - 2 * s)) s := by
    intro s
    have h1 : HasDerivAt (fun r : ℝ => 2 - 2 * r) (-2 : ℝ) s := by
      simpa using ((hasDerivAt_id s).const_mul (2 : ℝ)).const_sub (2 : ℝ)
    refine (h1.exp.const_mul (-(1 / 2 : ℝ))).congr_deriv ?_
    ring
  have hsub := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
    (fun x _ => hd x) (hfun.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le zero_le_one] at hsub
  rw [hsub]
  norm_num
  ring

/-- The energy of a path of `expZ` on the horizon `[0, 1]`. -/
theorem lintegral_expZ_sq (ω : Ω) (i : Fin 1) :
    ∫⁻ s in Set.Icc (0 : ℝ) 1, (‖expZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ENNReal.ofReal ((Real.exp 2 - 1) / 2) := by
  have hsq : ∀ r : ℝ, Real.exp (1 - r) ^ 2 = Real.exp (2 - 2 * r) := by
    intro r
    rw [sq, ← Real.exp_add]
    ring_nf
  have hpt : ∀ s : ℝ, (‖expZ Ω s ω i‖₊ : ℝ≥0∞) ^ 2
      = Set.indicator (Set.Ioc (0 : ℝ) 1)
        (fun r => ENNReal.ofReal (Real.exp (2 - 2 * r))) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc (0 : ℝ) 1
    · rw [expZ_apply, Set.indicator_of_mem hs, Set.indicator_of_mem hs,
        ennnorm_of_nonneg (Real.exp_nonneg _), ← ENNReal.ofReal_pow (Real.exp_nonneg _), hsq]
    · rw [expZ_apply, Set.indicator_of_notMem hs, Set.indicator_of_notMem hs]
      simp
  simp only [hpt]
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc,
    Set.inter_eq_left.mpr Set.Ioc_subset_Icc_self]
  have hio : IntegrableOn (fun s : ℝ => Real.exp (2 - 2 * s)) (Set.Ioc (0 : ℝ) 1) volume :=
    Continuous.integrableOn_Ioc
      (Real.continuous_exp.comp (continuous_const.sub (continuous_const.mul continuous_id)))
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)] fun s : ℝ => Real.exp (2 - 2 * s) :=
    Filter.Eventually.of_forall fun s => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hio hnn, integral_expWeight_sq]

/-- The energy of `expZ` on the horizon `[0, 1]` is `(e² − 1)/2`. -/
theorem energy_expZ (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω i)
      = ENNReal.ofReal ((Real.exp 2 - 1) / 2) := by
  rw [Brownian.Ito.energy]
  simp [lintegral_expZ_sq]

/-- The real number `(e² − 1)/2` is positive. -/
theorem ofReal_expWeight_ne_zero : ENNReal.ofReal ((Real.exp 2 - 1) / 2) ≠ 0 := by
  have h2 : (3 : ℝ) < Real.exp 2 := by
    have := Real.add_one_lt_exp (x := (2 : ℝ)) (by norm_num)
    linarith
  simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]
  linarith

/-- The energy of `expZ` on the horizon `[0, 1]` is nonzero. -/
theorem energy_expZ_ne_zero (i : Fin 1) :
    Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω i) ≠ 0 := by
  rw [energy_expZ]
  exact ofReal_expWeight_ne_zero

/-- The Brownian integrand of a solution of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` has energy `(e² − 1)/2` on `[0, 1]`. -/
theorem energy_eq_of_solvesBSDEJ (D : LevyDriver P 1 (Measure.dirac (1 : ℝ)))
    {Y' : ℝ → Ω → ℝ} {Z' : ℝ → Ω → (Fin 1 → ℝ)} {U' : ℝ → Ω → ℝ → ℝ}
    (h : SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U') :
    Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0)
      = ENNReal.ofReal ((Real.exp 2 - 1) / 2) := by
  obtain ⟨Y, hY, -⟩ := exists_solvesBSDEJ_expZ D
  have hf0 : ∫⁻ _s in Set.Icc (0 : ℝ) 1, (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 < ⊤ := by
    rw [lintegral_generator_id_zero]
    exact ENNReal.zero_lt_top
  obtain ⟨-, huniq⟩ := exists_unique_solvesBSDEJ D (fun _ y _ _ => y) (L := 1) zero_le_one
    measurable_generator_id lipschitz_generator_id one_pos hf0 (memLp_brownian_one D.W)
    (aestronglyMeasurable_brownian_one_augJoint D)
  have hzero := (huniq Y' Y Z' (expZ Ω) U' (fun _ _ _ => (0 : ℝ)) h hY).2.1 0
  have hmZ : Measurable (Function.uncurry fun ω s => Z' s ω 0) := h.Z_meas 0
  have hmE : Measurable (Function.uncurry fun (ω : Ω) s => expZ Ω s ω 0) := expZ_meas 0
  have hmd : Measurable (Function.uncurry fun ω s => Z' s ω 0 - expZ Ω s ω 0) := hmZ.sub hmE
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmd 1] at hzero
  have h0 : eLpNorm (fun p : Ω × ℝ => Z' p.2 p.1 0 - expZ Ω p.2 p.1 0) 2
      (Brownian.Ito.energyMeasure P 1) = 0 := (pow_eq_zero_iff two_ne_zero).mp hzero
  have hae := (eLpNorm_eq_zero_iff hmd.aestronglyMeasurable (by norm_num)).mp h0
  have hae2 : (fun p : Ω × ℝ => Z' p.2 p.1 0)
      =ᵐ[Brownian.Ito.energyMeasure P 1] fun p : Ω × ℝ => expZ Ω p.2 p.1 0 := by
    filter_upwards [hae] with p hp
    have hp' : Z' p.2 p.1 0 - expZ Ω p.2 p.1 0 = 0 := hp
    linarith
  rw [Brownian.Ito.energy_eq_eLpNorm_sq hmZ 1, eLpNorm_congr_ae hae2,
    ← Brownian.Ito.energy_eq_eLpNorm_sq hmE 1]
  exact energy_expZ 0

/-! ### The witness -/

/-- On some probability space there are a Lévy driver with one Brownian coordinate and jump
intensity `δ_1`, and a solution triple of the backward equation with generator
`f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` whose value process is `e^{1-t} W_t`,
whose Brownian integrand is `e^{1-s} 1_{(0, 1]}`, of energy `(e² − 1)/2` on the horizon, and
whose jump integrand vanishes; the Brownian integrand of every solution triple of that equation
has nonzero energy on the horizon. -/
theorem exists_solvesBSDEJ_generator_id_energy_ne_zero :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (D : LevyDriver P 1 (Measure.dirac (1 : ℝ))),
      (∃ Y : ℝ → Ω → ℝ,
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y (expZ Ω)
              (fun _ _ _ => (0 : ℝ)) ∧
            ∀ t, Y t =ᵐ[P] fun ω => Real.exp (1 - t) * (D.W.W 0).W t ω) ∧
        Brownian.Ito.energy P 1 (fun ω s => expZ Ω s ω 0)
            = ENNReal.ofReal ((Real.exp 2 - 1) / 2) ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin 1 → ℝ)) (U' : ℝ → Ω → ℝ → ℝ),
          SolvesBSDEJ D (fun _ y _ _ => y) (fun ω => (D.W.W 0).W 1 ω) 1 Y' Z' U' →
            Brownian.Ito.energy P 1 (fun ω s => Z' s ω 0) ≠ 0 := by
  obtain ⟨Ω, _, P, _, ⟨D⟩⟩ :=
    LevyStochCalc.Driver.LevyDriver.exists 1 ℝ (Measure.dirac (1 : ℝ))
  refine ⟨Ω, inferInstance, P, inferInstance, D, exists_solvesBSDEJ_expZ D, energy_expZ 0,
    fun _ _ _ h => ?_⟩
  rw [energy_eq_of_solvesBSDEJ D h]
  exact ofReal_expWeight_ne_zero

end LevyStochCalc.Examples.Nonvacuity
