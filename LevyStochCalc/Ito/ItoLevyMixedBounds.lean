/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.BigJumpPathBridge
import LevyStochCalc.Ito.LeftLimIntegrandRegularity
import LevyStochCalc.Ito.TruncatedContinuousPart
import LevyStochCalc.Ito.JumpFormulaMixed
import LevyStochCalc.Ito.JumpFormulaTaylorBounds
import LevyStochCalc.Ito.JumpFormulaContinuity
import LevyStochCalc.Ito.SubsequenceBookkeeping
import LevyStochCalc.Ito.VectorItoProcessDiff

/-!
# Bounds and admissibility of the mixed integrands

Energy bounds on a bounded window for integrands dominated by finitely many square-integrable
ones, the bounds on the four mixed integrands through the bounded derivatives of the state
function, their continuity in the state, and the progressive measurability of a marked integrand
read at a progressively measurable state.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.lintegral_window_sq_le_of_abs_le`,
  `LevyStochCalc.Ito.JumpFormula.lintegral_window_mark_sq_le_of_abs_le` — energy bounds for
  dominated integrands.
* `LevyStochCalc.Ito.JumpFormula.abs_mixedDriftIntegrand_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_mixedJumpIncrement_le` — bounds on the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_time_state_jump` — the triple of
  the time, a progressively measurable state and the jump coefficient along a path is marked
  progressively measurable.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Poisson.Compensated LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section Norms

/-- The supremum norm on `Fin n → ℝ` is at most the sum of the absolute coordinates. -/
theorem norm_le_sum_abs {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ≤ ∑ i, |v i| := by
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => abs_nonneg _)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  exact Finset.single_le_sum (fun j _ => abs_nonneg (v j)) (Finset.mem_univ i)

/-- The square of the sum of `n` absolute values is at most `n` times the sum of the squares. -/
theorem sq_sum_abs_le {n : ℕ} (v : Fin n → ℝ) : (∑ i, |v i|) ^ 2 ≤ (n : ℝ) * ∑ i, v i ^ 2 := by
  have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |v i|)
  simpa [sq_abs] using h

/-- The squared supremum norm is at most `n` times the sum of the squared coordinates. -/
theorem norm_sq_le_card_mul_sum_sq {n : ℕ} (v : Fin n → ℝ) :
    ‖v‖ ^ 2 ≤ (n : ℝ) * ∑ i, v i ^ 2 :=
  (pow_le_pow_left₀ (norm_nonneg v) (norm_le_sum_abs v) 2).trans (sq_sum_abs_le v)

/-- A real dominated by `c` times a sum of `n` absolute values has squared extended norm at most
`c² n` times the sum of the squared extended norms. -/
theorem enorm_sq_le_of_abs_le_mul_sum {n : ℕ} {x c : ℝ} {a : Fin n → ℝ}
    (h : |x| ≤ c * ∑ i, |a i|) :
    (‖x‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2 * n) * ∑ i, (‖a i‖₊ : ℝ≥0∞) ^ 2 := by
  have hreal : x ^ 2 ≤ c ^ 2 * n * ∑ i, a i ^ 2 := by
    calc x ^ 2 = |x| ^ 2 := (sq_abs x).symm
      _ ≤ (c * ∑ i, |a i|) ^ 2 := pow_le_pow_left₀ (abs_nonneg x) h 2
      _ = c ^ 2 * (∑ i, |a i|) ^ 2 := by ring
      _ ≤ c ^ 2 * ((n : ℝ) * ∑ i, a i ^ 2) :=
          mul_le_mul_of_nonneg_left (sq_sum_abs_le a) (sq_nonneg c)
      _ = c ^ 2 * n * ∑ i, a i ^ 2 := by ring
  have hconv : ∀ y : ℝ, (‖y‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (y ^ 2) := by
    intro y
    rw [show ((‖y‖₊ : ℝ≥0∞)) = ‖y‖ₑ from rfl, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg y), sq_abs]
  simp_rw [hconv]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (a i)),
    ← ENNReal.ofReal_mul (by positivity)]
  exact ENNReal.ofReal_le_ofReal hreal

end Norms

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The energy of a finite sum of jointly measurable kernels over a window is the sum of the
energies. -/
theorem lintegral_window_sum {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ → ℝ≥0∞}
    (hf : ∀ i, Measurable (Function.uncurry (f i))) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, f i ω s ∂volume ∂P
      = ∑ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, f i ω s ∂volume ∂P := by
  have h1 : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, f i ω s ∂volume
      = ∑ i, ∫⁻ s in Set.Icc (0 : ℝ) T, f i ω s ∂volume := fun ω =>
    lintegral_finsetSum _ fun i _ => Measurable.of_uncurry_left (hf i)
  simp_rw [h1]
  exact lintegral_finsetSum _ fun i _ => (hf i).lintegral_prod_right'

/-- The marked energy of a finite sum of jointly measurable kernels over a window is the sum of
the marked energies. -/
theorem lintegral_window_mark_sum {ι : Type*} [Fintype ι] {f : ι → Ω → ℝ → E → ℝ≥0∞}
    (hf : ∀ i, Measurable fun p : Ω × ℝ × E => f i p.1 p.2.1 p.2.2) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, ∑ i, f i ω s e ∂ν ∂volume ∂P
      = ∑ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f i ω s e ∂ν ∂volume ∂P := by
  have h1 : ∀ ω s, ∫⁻ e, ∑ i, f i ω s e ∂ν = ∑ i, ∫⁻ e, f i ω s e ∂ν := fun ω s =>
    lintegral_finsetSum _ fun i _ =>
      (hf i).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have h2 : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, ∫⁻ e, f i ω s e ∂ν ∂volume
      = ∑ i, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f i ω s e ∂ν ∂volume := fun ω =>
    lintegral_finsetSum _ fun i _ =>
      LevyStochCalc.Ito.IntegralLimit.measurable_section_markLIntegral (hf i) ω
  simp_rw [h1, h2]
  exact lintegral_finsetSum _ fun i _ => measurable_markEnergy (hf i) T

/-- A process dominated by `c` times a sum of `n` processes of finite energy on a window has
finite energy on that window. -/
theorem lintegral_window_sq_le_of_abs_le {n : ℕ} {H : Ω → ℝ → ℝ} {a : Fin n → Ω → ℝ → ℝ}
    {c : ℝ} (ha : ∀ i, Measurable (Function.uncurry (a i)))
    (h : ∀ ω s, |H ω s| ≤ c * ∑ i, |a i ω s|) (T : ℝ)
    (hq : ∀ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖a i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω s, (‖H ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (c ^ 2 * n) * ∑ i, (‖a i ω s‖₊ : ℝ≥0∞) ^ 2 :=
    fun ω s => enorm_sq_le_of_abs_le_mul_sum (h ω s)
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => hpt ω s) ?_
  have hm : ∀ i, Measurable (Function.uncurry fun ω s => (‖a i ω s‖₊ : ℝ≥0∞) ^ 2) :=
    fun i => ((ha i).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hC : ENNReal.ofReal (c ^ 2 * n) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [lintegral_const_mul' _ _ hC]
  rw [lintegral_window_sum (f := fun i ω s => (‖a i ω s‖₊ : ℝ≥0∞) ^ 2) hm T]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun i _ => hq i)

/-- A marked integrand dominated by `c` times a sum of `n` marked integrands of finite energy on
a window has finite energy on that window. -/
theorem lintegral_window_mark_sq_le_of_abs_le {n : ℕ} {φ : Ω → ℝ → E → ℝ}
    {a : Fin n → Ω → ℝ → E → ℝ} {c : ℝ}
    (ha : ∀ i, Measurable fun p : Ω × ℝ × E => a i p.1 p.2.1 p.2.2)
    (h : ∀ ω s e, |φ ω s e| ≤ c * ∑ i, |a i ω s e|) (T : ℝ)
    (hq : ∀ i, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖a i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hpt : ∀ ω s e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2
      ≤ ENNReal.ofReal (c ^ 2 * n) * ∑ i, (‖a i ω s e‖₊ : ℝ≥0∞) ^ 2 :=
    fun ω s e => enorm_sq_le_of_abs_le_mul_sum (h ω s e)
  refine lt_of_le_of_lt
    (lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e) ?_
  have hm : ∀ i, Measurable fun p : Ω × ℝ × E => (‖a i p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => ((ha i).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hC : ENNReal.ofReal (c ^ 2 * n) ≠ ⊤ := ENNReal.ofReal_ne_top
  simp_rw [lintegral_const_mul' _ _ hC]
  rw [lintegral_window_mark_sum (f := fun i ω s e => (‖a i ω s e‖₊ : ℝ≥0∞) ^ 2) hm T]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.sum_lt_top.mpr fun i _ => hq i)

end Energies

section MixedBounds

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The mixed drift integrand is bounded, through the derivative bounds, by an affine function
of the drift and the squared diffusion coefficients. -/
theorem abs_mixedDriftIntegrand_le (coeffs : JumpDiffusionCoeffs n d E) {K₀ K₁ K₂ : ℝ}
    (hK₂0 : 0 ≤ K₂) (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (s : ℝ) (y x : Fin n → ℝ) :
    |mixedDriftIntegrand u coeffs s y x|
      ≤ K₀ + K₁ * ∑ p, |coeffs.μ s x p|
        + (1 / 2) * K₂ * ∑ p, ∑ q, ∑ j, (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 := by
  unfold mixedDriftIntegrand
  have h1 : |∑ p, coeffs.μ s x p * gradient u s y p| ≤ K₁ * ∑ p, |coeffs.μ s x p| := by
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hK₁ s y p) (abs_nonneg _)
  have h2 : |(1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s x p j * coeffs.σ s x q j * hessian u s y p q|
      ≤ (1 / 2) * K₂ * ∑ p, ∑ q, ∑ j, (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 := by
    rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    have hsq : |coeffs.σ s x p j * coeffs.σ s x q j|
        ≤ (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 := by
      rw [abs_mul]
      have := two_mul_le_add_sq |coeffs.σ s x p j| |coeffs.σ s x q j|
      rw [sq_abs, sq_abs] at this
      linarith
    calc |coeffs.σ s x p j * coeffs.σ s x q j| * |hessian u s y p q|
        ≤ |coeffs.σ s x p j * coeffs.σ s x q j| * K₂ :=
          mul_le_mul_of_nonneg_left (hK₂ s y p q) (abs_nonneg _)
      _ ≤ (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2 * K₂ :=
          mul_le_mul_of_nonneg_right hsq hK₂0
      _ = K₂ * ((coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2) := mul_comm _ _
  calc |timeDeriv u s y + (∑ p, coeffs.μ s x p * gradient u s y p
          + (1 / 2) * ∑ p, ∑ q, ∑ j, coeffs.σ s x p j * coeffs.σ s x q j * hessian u s y p q)|
      ≤ |timeDeriv u s y| + (|∑ p, coeffs.μ s x p * gradient u s y p|
          + |(1 / 2) * ∑ p, ∑ q, ∑ j,
              coeffs.σ s x p j * coeffs.σ s x q j * hessian u s y p q|) :=
        (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ K₀ + (K₁ * ∑ p, |coeffs.μ s x p|
          + (1 / 2) * K₂ * ∑ p, ∑ q, ∑ j, (coeffs.σ s x p j ^ 2 + coeffs.σ s x q j ^ 2) / 2) :=
        add_le_add (hK₀ s y) (add_le_add h1 h2)
    _ = _ := by ring

/-- A component of the mixed diffusion integrand is bounded, through the gradient bound, by the
sum of the absolute entries of the corresponding column of the diffusion matrix. -/
theorem abs_mixedDiffusionIntegrand_le {σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)} {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (s : ℝ) (y x : Fin n → ℝ) (j : Fin d) :
    |mixedDiffusionIntegrand u σ s y x j| ≤ K₁ * ∑ i, |σ s x i j| := by
  unfold mixedDiffusionIntegrand
  rw [Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hK₁ s y i) (abs_nonneg _)

/-- The mixed jump increment is bounded, through the gradient bound, by `n K₁` times the sum of
the absolute coordinates of the jump size. -/
theorem abs_mixedJumpIncrement_le (hu : ContDiff ℝ 2 (Function.uncurry u))
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₁0 : 0 ≤ K₁) (s : ℝ) (y x : Fin n → ℝ)
    (e : E) : |mixedJumpIncrement u γ s y x e| ≤ (n : ℝ) * K₁ * ∑ i, |γ s x e i| := by
  unfold mixedJumpIncrement
  refine (abs_sub_le_of_gradient_le hu s (hK₁ s) y (γ s x e)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_le_sum_abs _) (mul_nonneg (Nat.cast_nonneg n) hK₁0)

/-- The mixed compensator-drift integrand is bounded, through the Hessian bound, by `n³ K₂`
times the sum of the squared coordinates of the jump size. -/
theorem abs_mixedCompensatorDriftIntegrand_le (hu : ContDiff ℝ 2 (Function.uncurry u))
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (hK₂0 : 0 ≤ K₂) (s : ℝ) (y x : Fin n → ℝ)
    (e : E) :
    |mixedCompensatorDriftIntegrand u γ s y x e|
      ≤ (n : ℝ) ^ 2 * K₂ * ((n : ℝ) * ∑ i, γ s x e i ^ 2) := by
  unfold mixedCompensatorDriftIntegrand
  refine (abs_sub_sub_le_of_hessian_le hu s (hK₂ s) y (γ s x e)).trans ?_
  exact mul_le_mul_of_nonneg_left (norm_sq_le_card_mul_sum_sq _)
    (mul_nonneg (sq_nonneg _) hK₂0)

/-- The mark cut of an integrand is bounded by the integrand. -/
theorem abs_markCut_le {Ω : Type u} (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    |markCut A φ ω s e| ≤ |φ ω s e| := by
  by_cases h : e ∈ A
  · simp [markCut, h]
  · simp [markCut, h]

end MixedBounds

section MixedContinuity

variable {n d : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ} {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ}

/-- At a fixed time and coefficient state, the mixed drift integrand transports convergence of
the derivative state. -/
theorem tendsto_mixedDriftIntegrand_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u))
    (coeffs : JumpDiffusionCoeffs n d E) (s : ℝ) (x : Fin n → ℝ)
    (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => mixedDriftIntegrand u coeffs s (z m) x) atTop
      (𝓝 (mixedDriftIntegrand u coeffs s w x)) := by
  unfold mixedDriftIntegrand
  refine (tendsto_timeDeriv_of_tendsto hu s h).add (Tendsto.add ?_ (tendsto_const_nhds.mul ?_))
  · exact tendsto_finsetSum _ fun p _ =>
      tendsto_const_nhds.mul (tendsto_gradient_apply_of_tendsto hu s p h)
  · exact tendsto_finsetSum _ fun p _ => tendsto_finsetSum _ fun q _ =>
      tendsto_finsetSum _ fun j _ => tendsto_const_nhds.mul (tendsto_hessian_of_tendsto hu s p q h)

/-- At a fixed time, coefficient state and mark, the mixed jump increment transports convergence
of the derivative state. -/
theorem tendsto_mixedJumpIncrement_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u))
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E)
    (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => mixedJumpIncrement u γ s (z m) x e) atTop
      (𝓝 (mixedJumpIncrement u γ s w x e)) := by
  unfold mixedJumpIncrement
  exact (SmallJump.tendsto_comp_of_tendsto hu s (h.add_const _)).sub
    (SmallJump.tendsto_comp_of_tendsto hu s h)

/-- At a fixed time, coefficient state and mark, the mixed compensator-drift integrand
transports convergence of the derivative state. -/
theorem tendsto_mixedCompensatorDriftIntegrand_of_tendsto
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ)
    (x : Fin n → ℝ) (e : E) (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => mixedCompensatorDriftIntegrand u γ s (z m) x e) atTop
      (𝓝 (mixedCompensatorDriftIntegrand u γ s w x e)) := by
  unfold mixedCompensatorDriftIntegrand
  refine ((SmallJump.tendsto_comp_of_tendsto hu s (h.add_const _)).sub
    (SmallJump.tendsto_comp_of_tendsto hu s h)).sub ?_
  exact tendsto_finsetSum _ fun i _ =>
    tendsto_const_nhds.mul (tendsto_gradient_apply_of_tendsto hu s i h)

end MixedContinuity

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

/-- A finite sum of progressively measurable real processes is progressively measurable. -/
theorem progressivelyMeasurable_finset_sum {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {ι : Type*}
    (s : Finset ι) {H : ι → Ω → ℝ → ℝ} (h : ∀ i ∈ s, ProgressivelyMeasurable ℱ (H i)) :
    ProgressivelyMeasurable ℱ fun ω t => ∑ i ∈ s, H i ω t := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun r => ∑ i ∈ s, H i p.1 r) p.2)
      = fun p : Ω × ℝ => ∑ i ∈ s, (Set.Iic t).indicator (H i p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, Finset.sum_const_zero]
  rw [key]
  exact Finset.stronglyMeasurable_fun_sum
    (f := fun i (p : Ω × ℝ) => (Set.Iic t).indicator (H i p.1) p.2) s fun i hi => h i hi t

/-- The triple of the time, a progressively measurable state and the jump coefficient along a
path is a marked progressively measurable process. -/
theorem markedProgressivelyMeasurable_time_state_jump {n d : ℕ}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {coeffs : JumpDiffusionCoeffs n d E}
    {Xp Y : ℝ → Ω → (Fin n → ℝ)}
    (hY : ∀ i, ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    (hγ : ∀ i, MarkedProgressivelyMeasurable ℱ (SmallJump.pathJumpCoeff coeffs Xp i)) :
    MarkedProgressivelyMeasurable ℱ fun ω s e =>
      ((s, Y s ω, coeffs.γ s (Xp s ω) e) : ℝ × (Fin n → ℝ) × (Fin n → ℝ)) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have heq : (fun p : Ω × ℝ × E => (Set.Iic t).indicator
        (fun s => ((s, Y s p.1, coeffs.γ s (Xp s p.1) p.2.2) :
          ℝ × (Fin n → ℝ) × (Fin n → ℝ))) p.2.1)
      = fun p : Ω × ℝ × E => ((Set.Iic t).indicator (fun s => s) p.2.1,
          fun i => (Set.Iic t).indicator (fun s => Y s p.1 i) p.2.1,
          fun i => (Set.Iic t).indicator (fun s => coeffs.γ s (Xp s p.1) p.2.2 i) p.2.1) := by
    funext p
    by_cases hp : p.2.1 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp]
      rfl
  rw [heq]
  refine Measurable.stronglyMeasurable ?_
  refine Measurable.prodMk ?_ (Measurable.prodMk ?_ ?_)
  · exact (measurable_id.indicator measurableSet_Iic).comp measurable_snd.fst
  · refine measurable_pi_lambda _ fun i => ?_
    exact ((hY i t).measurable).comp (measurable_fst.prodMk measurable_snd.fst)
  · refine measurable_pi_lambda _ fun i => ?_
    exact (hγ i t).measurable

end Progressive

end LevyStochCalc.Ito.JumpFormula
