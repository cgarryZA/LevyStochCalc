/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.ProfileExpVector
import LevyStochCalc.Poisson.CompensatedProductMoments
import LevyStochCalc.Probability.CharacterL2
import LevyStochCalc.Probability.L2Series

/-!
# Continuity of the exponential vector of a step in the mark profile

For a Poisson random measure with intensity `ν`, a step `(a, b]` and a real frequency `u`, the
exponential vector `𝓔_u(f) = exp (i u J(f)) · exp (−(b − a) ∫ ψ_u(f) dν)` of the step at a
square-integrable mark profile `f` depends continuously on `f`: if `f_n → f` in `L²(ν)` then
`𝓔_u(f_n) → 𝓔_u(f)` in `L²(P; ℂ)`. The compensated integrals converge in `L²(P)` by the isometry,
so their characters converge in `L²(P)` because `x ↦ e^{iux}` is `|u|`-Lipschitz, and the
deterministic factors converge because the Lévy characteristic exponent is continuous along
`L²(ν)` convergence.

The same Lipschitz bound `|e^{iux} − e^{iuy}| ≤ |u| |x − y|` makes `e^{iu f_n} − 1 → e^{iu f} − 1`
in `L²(ν; ℂ)`, whence the two constants
`∫ ‖e^{iu f} − 1‖ ^ 2 dν` and `∫ (e^{iu f} − 1) ^ 2 dν` are continuous along `L²(ν)` convergence.

## Main statements

* `LevyStochCalc.Poisson.tendsto_eLpNorm_profileExpVector_sub` — `𝓔_u(f_n) → 𝓔_u(f)` in
  `L²(P; ℂ)`.
* `LevyStochCalc.Poisson.tendsto_eLpNorm_exp_I_mul_sub_one_sub` — `e^{iu f_n} − 1 → e^{iu f} − 1`
  in `L²(ν; ℂ)`.
* `LevyStochCalc.Poisson.tendsto_integral_norm_sq_exp_I_mul_sub_one` —
  `∫ ‖e^{iu f_n} − 1‖ ^ 2 dν → ∫ ‖e^{iu f} − 1‖ ^ 2 dν`.
* `LevyStochCalc.Poisson.tendsto_integral_sq_exp_I_mul_sub_one` —
  `∫ (e^{iu f_n} − 1) ^ 2 dν → ∫ (e^{iu f} − 1) ^ 2 dν`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal Topology

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **Continuity of the exponential vector in the profile.** If square-integrable mark profiles
`f_n` converge to `f` in `L²(ν)`, the exponential vectors of a step at `f_n` converge to the
exponential vector at `f` in `L²(P; ℂ)`. -/
theorem tendsto_eLpNorm_profileExpVector_sub (N : PoissonRandomMeasure P ν) {h : ℕ → E → ℝ}
    {f : E → ℝ} (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω => profileExpVector N (h n) a b u ω
      - profileExpVector N f a b u ω) 2 P) atTop (𝓝 0) := by
  set X : (E → ℝ) → Ω → ℂ :=
    fun g ω => Complex.exp (Complex.I * ((u * compensatedProfile N g a b ω : ℝ) : ℂ)) with hX
  set K : (E → ℝ) → ℂ :=
    fun g => Complex.exp (-(((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (g e) ∂ν)) with hK
  have hXm : ∀ g, MemLp (X g) 2 P := fun g =>
    Probability.memLp_exp_I_mul u (measurable_compensatedProfile N g a b).aestronglyMeasurable
  have hXc : Tendsto (fun n => (hXm (h n)).toLp (X (h n))) atTop (𝓝 ((hXm f).toLp (X f))) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hXm (h n)) _ (hXm f)).2
      (Probability.tendsto_eLpNorm_exp_I_mul_sub u
        (tendsto_compensatedProfile_of_tendsto N hh hf ha hab hc))
  have hKc : Tendsto (fun n => K (h n)) atTop (𝓝 (K f)) :=
    (Complex.continuous_exp.comp (continuous_const.mul continuous_id).neg).continuousAt.tendsto.comp
      (tendsto_integral_levyCharIntegrand u hh hf hc)
  have hV : ∀ g, MemLp (profileExpVector N g a b u) 2 P := fun g =>
    memLp_profileExpVector N g a b u 2
  have hsmul : ∀ g, (hV g).toLp (profileExpVector N g a b u) = K g • (hXm g).toLp (X g) := by
    intro g
    refine Lp.ext ?_
    filter_upwards [(hV g).coeFn_toLp, Lp.coeFn_smul (K g) ((hXm g).toLp (X g)),
      (hXm g).coeFn_toLp] with ω h1 h2 h3
    rw [h1, h2, Pi.smul_apply, h3, smul_eq_mul, profileExpVector, mul_comm]
  have hlim := hKc.smul hXc
  simp_rw [← hsmul] at hlim
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ (fun n => hV (h n)) _ (hV f)).1 hlim

omit [SigmaFinite ν] in
/-- If mark profiles `f_n` converge to `f` in `L²(ν)`, then `e^{iu f_n} − 1 → e^{iu f} − 1` in
`L²(ν; ℂ)`. -/
theorem tendsto_eLpNorm_exp_I_mul_sub_one_sub {h : ℕ → E → ℝ} {f : E → ℝ} (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun e => (Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1)
      - (Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1)) 2 ν) atTop (𝓝 0) := by
  refine (Probability.tendsto_eLpNorm_exp_I_mul_sub u hc).congr fun n => ?_
  congr 1
  funext e
  ring

omit [SigmaFinite ν] in
/-- The constant `∫ ‖e^{iu f} − 1‖ ^ 2 dν` is continuous along `L²(ν)` convergence of the
square-integrable mark profile `f`. -/
theorem tendsto_integral_norm_sq_exp_I_mul_sub_one {h : ℕ → E → ℝ} {f : E → ℝ}
    (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, ‖Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1‖ ^ 2 ∂ν) atTop
      (𝓝 (∫ e, ‖Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1‖ ^ 2 ∂ν)) := by
  have hm : ∀ n, MemLp (fun e => Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1) 2 ν :=
    fun n => Probability.memLp_exp_I_mul_sub_one u (hh n)
  have hm' : MemLp (fun e => Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1) 2 ν :=
    Probability.memLp_exp_I_mul_sub_one u hf
  have hL := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hm _ hm').2
    (tendsto_eLpNorm_exp_I_mul_sub_one_sub u hc)
  have hn := hL.norm.pow 2
  rw [Probability.norm_toLp_sq _ hm'] at hn
  exact hn.congr fun n => Probability.norm_toLp_sq _ (hm n)

omit [SigmaFinite ν] in
/-- The constant `∫ (e^{iu f} − 1) ^ 2 dν` is continuous along `L²(ν)` convergence of the
square-integrable mark profile `f`. -/
theorem tendsto_integral_sq_exp_I_mul_sub_one {h : ℕ → E → ℝ} {f : E → ℝ}
    (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) (u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ e, (Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1) ^ 2 ∂ν) atTop
      (𝓝 (∫ e, (Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1) ^ 2 ∂ν)) := by
  have hm : ∀ n, MemLp (fun e => Complex.exp (Complex.I * ((u * h n e : ℝ) : ℂ)) - 1) 2 ν :=
    fun n => Probability.memLp_exp_I_mul_sub_one u (hh n)
  have hm' : MemLp (fun e => Complex.exp (Complex.I * ((u * f e : ℝ) : ℂ)) - 1) 2 ν :=
    Probability.memLp_exp_I_mul_sub_one u hf
  have h2 := Probability.tendsto_integral_mul_of_tendsto_eLpNorm hm hm hm' hm'
    (tendsto_eLpNorm_exp_I_mul_sub_one_sub u hc) (tendsto_eLpNorm_exp_I_mul_sub_one_sub u hc)
  simpa only [sq] using h2

end LevyStochCalc.Poisson
