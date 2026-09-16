/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.SecondMomentBilinear

/-!
# The exponentially weighted second moment of an Itô–Lévy process

The map `t ↦ 𝔼[X_t²]` is the initial value plus the time integral of the rate
`2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`, so integration by parts against the
weight `e^{βs}` gives

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic formula. The
weighting of an absolutely continuous function by an exponential is isolated first, as a real
identity. The vector form follows coordinatewise, and the cross witness carried by the driver
gives the bilinear and the weighted forms over its augmented joint natural filtration.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Weight

/-! ### The exponential weight: integration by parts against `e^{βs}` -/

/-- A finite window energy is the time integral of the sample energies at each time. -/
theorem toReal_lintegral_lintegral_eq {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) {T : ℝ}
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P).toReal
      = ∫ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, F ω s ∂P).toReal := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, F ω s ∂P ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hF.aemeasurable
  have hm : Measurable fun s => ∫⁻ ω, F ω s ∂P := hF.lintegral_prod_left
  rw [hswap, integral_toReal hm.aemeasurable]
  exact ae_lt_top hm (by rw [← hswap]; exact hfin.ne)

/-- The sample energies of a finite window energy are integrable in time. -/
theorem integrableOn_toReal_lintegral {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F)) {T : ℝ}
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P < ⊤) :
    IntegrableOn (fun s => (∫⁻ ω, F ω s ∂P).toReal) (Set.Icc (0 : ℝ) T) := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, F ω s ∂P ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hF.aemeasurable
  exact integrable_toReal_of_lintegral_ne_top hF.lintegral_prod_left.aemeasurable
    (by rw [← hswap]; exact hfin.ne)

/-- The integral of `β e^{βs}` over `[r, T]`. -/
theorem setIntegral_mul_exp_mul (β : ℝ) {r T : ℝ} (hrT : r ≤ T) :
    ∫ s in Set.Icc r T, β * Real.exp (β * s) = Real.exp (β * T) - Real.exp (β * r) := by
  have hder : ∀ x : ℝ, HasDerivAt (fun s => Real.exp (β * s)) (β * Real.exp (β * x)) x := by
    intro x
    have := ((hasDerivAt_id' (x := x)).const_mul β).exp
    convert this using 1
    ring
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrT]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    ((by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s)).intervalIntegrable _ _)

/-- **Integration by parts against an exponential weight.** For an integrable function `g` on
`[0, T]`, `∫_0^T β e^{βs} (∫_0^s g) ds = e^{βT} ∫_0^T g − ∫_0^T e^{βr} g(r) dr`. -/
theorem setIntegral_exp_mul_setIntegral {g : ℝ → ℝ} {T : ℝ}
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) T)) (β : ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T, β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r
      = Real.exp (β * T) * (∫ r in Set.Icc (0 : ℝ) T, g r)
        - ∫ r in Set.Icc (0 : ℝ) T, Real.exp (β * r) * g r := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have hwi : IntegrableOn (fun s : ℝ => β * Real.exp (β * s)) (Set.Icc (0 : ℝ) T) :=
    (by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s)).integrableOn_Icc
  have hprod : Integrable (fun p : ℝ × ℝ => g p.1 * (β * Real.exp (β * p.2))) (μ.prod μ) :=
    hg.mul_prod hwi
  set F : ℝ × ℝ → ℝ :=
    {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => g p.1 * (β * Real.exp (β * p.2)) with hF
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hFint : Integrable F (μ.prod μ) := hprod.indicator hle
  -- sliced at the second coordinate: the running integral against the weight
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ r, F (r, s) ∂μ = (∫ r in Set.Icc (0 : ℝ) s, g r) * (β * Real.exp (β * s)) := by
    intro s hs
    have h1 : (fun r => F (r, s))
        = fun r => (Set.Iic s).indicator (fun r => g r * (β * Real.exp (β * s))) r := by
      funext r
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
    have hset : Set.Iic s ∩ Set.Icc (0 : ℝ) T = Set.Icc (0 : ℝ) s := by
      ext r
      simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h2, h1⟩
        exact ⟨h1, h2, h1.trans hs.2⟩
    rw [h1, integral_indicator measurableSet_Iic, integral_mul_const, hμ,
      Measure.restrict_restrict measurableSet_Iic, hset]
  have hFeq : ∫ p, F p ∂(μ.prod μ)
      = ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, g r) * (β * Real.exp (β * s)) := by
    rw [integral_prod_symm F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => hinner s hs
  -- sliced at the first coordinate: the weight integrated from `r` to `T`
  have hinner' : ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫ s, F (r, s) ∂μ = g r * (Real.exp (β * T) - Real.exp (β * r)) := by
    intro r hr
    have h1 : (fun s => F (r, s))
        = fun s => (Set.Ici r).indicator (fun s => g r * (β * Real.exp (β * s))) s := by
      funext s
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Ici]
    have hset : Set.Ici r ∩ Set.Icc (0 : ℝ) T = Set.Icc r T := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h3⟩
        exact ⟨h1, hr.1.trans h1, h3⟩
    rw [h1, integral_indicator measurableSet_Ici, integral_const_mul, hμ,
      Measure.restrict_restrict measurableSet_Ici, hset, setIntegral_mul_exp_mul β hr.2]
  have hFeq' : ∫ p, F p ∂(μ.prod μ)
      = ∫ r in Set.Icc (0 : ℝ) T, g r * (Real.exp (β * T) - Real.exp (β * r)) := by
    rw [integral_prod F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hinner' r hr
  have hge : IntegrableOn (fun r => g r * Real.exp (β * r)) (Set.Icc (0 : ℝ) T) :=
    hg.mul_continuousOn (by fun_prop : Continuous fun r : ℝ => Real.exp (β * r)).continuousOn
      isCompact_Icc
  calc ∫ s in Set.Icc (0 : ℝ) T, β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r
      = ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, g r) * (β * Real.exp (β * s)) :=
        setIntegral_congr_fun measurableSet_Icc fun s _ => mul_comm _ _
    _ = ∫ r in Set.Icc (0 : ℝ) T, g r * (Real.exp (β * T) - Real.exp (β * r)) := by
        rw [← hFeq, hFeq']
    _ = Real.exp (β * T) * (∫ r in Set.Icc (0 : ℝ) T, g r)
        - ∫ r in Set.Icc (0 : ℝ) T, Real.exp (β * r) * g r := by
        have e : (fun r => g r * (Real.exp (β * T) - Real.exp (β * r)))
            = fun r => Real.exp (β * T) * g r - g r * Real.exp (β * r) := by
          funext r
          ring
        rw [e, integral_sub (hg.const_mul _) hge, integral_const_mul]
        congr 1
        exact setIntegral_congr_fun measurableSet_Icc fun r _ => mul_comm _ _

/-- **The exponential weighting of an absolutely continuous function.** If
`m(s) = m₀ + ∫_0^s g` on `(0, T]` with `g` integrable on `[0, T]`, then
`e^{βT} m(T) = m₀ + ∫_0^T e^{βs} (β m(s) + g(s)) ds`. -/
theorem exp_mul_eq_add_setIntegral {m g : ℝ → ℝ} {m₀ T : ℝ} (hT : 0 < T)
    (hg : IntegrableOn g (Set.Icc (0 : ℝ) T))
    (hm : ∀ s ∈ Set.Ioc (0 : ℝ) T, m s = m₀ + ∫ r in Set.Icc (0 : ℝ) s, g r) (β : ℝ) :
    Real.exp (β * T) * m T
      = m₀ + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β * m s + g s) := by
  have hG : ContinuousOn (fun s => ∫ r in Set.Icc (0 : ℝ) s, g r) (Set.Icc (0 : ℝ) T) :=
    intervalIntegral.continuousOn_primitive_Icc hg
  have h1 : Integrable (fun s => β * Real.exp (β * s) * m₀)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    (by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s) * m₀).integrableOn_Icc
  have h2 : Integrable (fun s => β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ((by fun_prop : Continuous fun s : ℝ => β * Real.exp (β * s)).continuousOn.mul
      hG).integrableOn_Icc
  have h12 : Integrable (fun s => β * Real.exp (β * s) * m₀
      + β * Real.exp (β * s) * ∫ r in Set.Icc (0 : ℝ) s, g r)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := h1.add h2
  have h3 : Integrable (fun s => Real.exp (β * s) * g s)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    IntegrableOn.continuousOn_mul
      (by fun_prop : Continuous fun s : ℝ => Real.exp (β * s)).continuousOn hg isCompact_Icc
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Real.exp (β * s) * (β * m s + g s)
        = β * Real.exp (β * s) * m₀
          + β * Real.exp (β * s) * (∫ r in Set.Icc (0 : ℝ) s, g r)
          + Real.exp (β * s) * g s := by
    filter_upwards [ae_restrict_mem measurableSet_Icc,
      ae_restrict_of_ae (Measure.ae_ne volume (0 : ℝ))] with s hs hs0
    rw [hm s ⟨lt_of_le_of_ne hs.1 (Ne.symm hs0), hs.2⟩]
    ring
  have h0 : ∫ s in Set.Icc (0 : ℝ) T, β * Real.exp (β * s) * m₀
      = (Real.exp (β * T) - 1) * m₀ := by
    rw [integral_mul_const, setIntegral_mul_exp_mul β hT.le, mul_zero, Real.exp_zero]
  rw [integral_congr_ae hae, integral_add h12 h3, integral_add h1 h2,
    setIntegral_exp_mul_setIntegral hg β, hm T ⟨hT, le_rfl⟩, h0]
  ring

end Weight

section Weighted

/-! ### The exponentially weighted second moment -/

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- The squared norm of a diffusion coordinate is jointly measurable. -/
theorem measurable_uncurry_sq_diffusion
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ) (j : Fin d) :
    Measurable (Function.uncurry fun ω s => (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2) :=
  (h.σ_meas j).nnnorm.coe_nnreal_ennreal.pow_const 2

/-- The jump energy density `(ω, s) ↦ ∫_E γ(ω, s, e)² ν(de)` is jointly measurable. -/
theorem measurable_uncurry_lintegral_sq_jump
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ) :
    Measurable (Function.uncurry fun ω s => ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
  ((h.γ_meas.nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
    Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
      (ν := ν)

/-- The pairing of an Itô–Lévy process with its drift is integrable in time on every window. -/
theorem integrableOn_integral_mul_drift
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (hX₀2 : MemLp X₀ 2 P) (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    IntegrableOn (fun s => ∫ ω, X s ω * b s ω ∂P) (Set.Icc (0 : ℝ) T) := by
  classical
  set S : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) with hSdef
  set C : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq
    with hCdef
  have hS2 : ∀ j, MemLp (S j T) 2 P := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) T
  have hC2 : MemLp (C T) 2 P :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq T
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hXb : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * (∫ r in Set.Icc (0 : ℝ) s, b r ω) ∂P
        + (∑ j, ∫ ω, b s ω * S j T ω ∂P) + ∫ ω, b s ω * C T ω ∂P := by
    filter_upwards [ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT), hsw] with s hs2 hs
    exact integral_mul_eq_expand h hX₀2 hbm hbq hs.1 hs.2 (hbp.stronglyMeasurable_eval s) hs2
  have hint_s : ∀ (g : Ω → ℝ), MemLp g 2 P →
      Integrable (fun s => ∫ ω, b s ω * g ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun g hg => ((memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
      (memLp_two_prod_fst hg)).integral_prod_right
  have hint_Dr : Integrable (fun s => ∫ ω, b s ω * (∫ r in Set.Icc (0 : ℝ) s, b r ω) ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : Integrable (fun s => ∫ ω, b s ω * running b T (ω, s) ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      ((memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
        (memLp_two_running (P := P) hbm (hbq T hT))).integral_prod_right
    refine h1.congr ?_
    filter_upwards [hsw] with s hs
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact congrArg (fun x => b s ω * x) (running_eq hs)
  have i3 : Integrable (fun s => ∑ j, ∫ ω, b s ω * S j T ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := integrable_finsetSum _ fun j _ => hint_s _ (hS2 j)
  refine ((((hint_s X₀ hX₀2).add hint_Dr).add i3).add (hint_s _ hC2)).congr ?_
  filter_upwards [hXb] with s hs
  exact hs.symm

/-- The second moment of an Itô–Lévy process is its initial second moment plus the time
integral of the rate `2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)`. -/
theorem integral_mul_self_eq_add_setIntegral
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ) (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, X t ω * X t ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) t, (2 * ∫ ω, X s ω * b s ω ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
  have i1 : Integrable (fun s => 2 * ∫ ω, X s ω * b s ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    (integrableOn_integral_mul_drift h hX₀2 hbm hbp hbq ht).const_mul 2
  have iσ : ∀ j : Fin d, Integrable (fun s => (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := fun j =>
    integrableOn_toReal_lintegral (measurable_uncurry_sq_diffusion h j) (h.σ_sq j t ht)
  have i2 : Integrable (fun s => ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := integrable_finsetSum _ fun j _ => iσ j
  have i12 : Integrable (fun s => 2 * ∫ ω, X s ω * b s ω ∂P
      + ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) := i1.add i2
  have i3 : Integrable (fun s => (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)
      (volume.restrict (Set.Icc (0 : ℝ) t)) :=
    integrableOn_toReal_lintegral (measurable_uncurry_lintegral_sq_jump h) (h.γ_sq t ht)
  rw [integral_mul_self_eq_of_isItoLevyProcess h 𝒲 hX₀ hX₀2 hbm hbp hbq ht,
    integral_add i12 i3, integral_add i1 i2, integral_const_mul,
    integral_finsetSum _ fun j _ => iσ j,
    toReal_lintegral_lintegral_eq (measurable_uncurry_lintegral_sq_jump h) (h.γ_sq t ht),
    Finset.sum_congr rfl fun j _ =>
      toReal_lintegral_lintegral_eq (measurable_uncurry_sq_diffusion h j) (h.σ_sq j t ht)]
  ring

/-- **The exponentially weighted second moment of an Itô–Lévy process.** For every `β` and
`T > 0`,

`e^{βT} 𝔼[X_T²] = 𝔼[X₀²] + ∫_0^T e^{βs} (β 𝔼[X_s²] + 2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²]
  + 𝔼 ∫_E γ(s, e)² ν(de)) ds`,

the form in which the a-priori estimates for BSDEs with jumps read the quadratic Itô formula. -/
theorem integral_exp_mul_self_eq_of_isItoLevyProcess
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ) (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Real.exp (β * T) * ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
            * (β * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b s ω ∂P
              + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
              + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
  have hg : IntegrableOn (fun s => 2 * ∫ ω, X s ω * b s ω ∂P
      + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) (Set.Icc (0 : ℝ) T) :=
    (((integrableOn_integral_mul_drift h hX₀2 hbm hbp hbq hT).const_mul 2).add
      (integrable_finsetSum _ fun j _ =>
        integrableOn_toReal_lintegral (measurable_uncurry_sq_diffusion h j) (h.σ_sq j T hT))).add
      (integrableOn_toReal_lintegral (measurable_uncurry_lintegral_sq_jump h) (h.γ_sq T hT))
  have key := exp_mul_eq_add_setIntegral (m := fun t => ∫ ω, X t ω * X t ω ∂P) hT hg
    (fun s hs => integral_mul_self_eq_add_setIntegral h 𝒲 hX₀ hX₀2 hbm hbp hbq hs.1) β
  refine key.trans ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  ring

end Weighted

section WeightedVector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

/-- **The exponentially weighted second moment of a vector Itô–Lévy process**, coordinate by
coordinate: the weighted expected squared norm at the horizon is the sum of the weighted scalar
identities of the coordinates. -/
theorem integral_exp_mul_sum_mul_self_eq_of_isItoLevyProcess
    (h : ∀ i, LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (X i) (X₀ i) (b i)
      (σ i) (γ i))
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : ∀ i, StronglyMeasurable[ℱ 0] (X₀ i)) (hX₀2 : ∀ i, MemLp (X₀ i) 2 P)
    (hbm : ∀ i, Measurable (Function.uncurry fun ω s => b i s ω))
    (hbp : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b i s ω)
    (hbq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Real.exp (β * T) * ∫ ω, ∑ i, X i T ω * X i T ω ∂P
      = ∑ i, (∫ ω, X₀ i ω * X₀ i ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
            * (β * ∫ ω, X i s ω * X i s ω ∂P + 2 * ∫ ω, X i s ω * b i s ω ∂P
              + (∑ j : Fin d, (∫⁻ ω, (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
              + (∫⁻ ω, ∫⁻ e, (‖γ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal)) := by
  have hX2 : ∀ i, MemLp (X i T) 2 P := fun i =>
    memLp_two_of_isItoLevyProcess (h i) (hX₀2 i) (hbm i) (hbq i) hT.le
  have hint : ∀ i, Integrable (fun ω => X i T ω * X i T ω) P := fun i =>
    (hX2 i).integrable_mul (hX2 i)
  rw [integral_finsetSum _ fun i _ => hint i, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    integral_exp_mul_self_eq_of_isItoLevyProcess (h i) 𝒲 (hX₀ i) (hX₀2 i) (hbm i) (hbp i)
      (hbq i) β hT

end WeightedVector

section AugmentedMore

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- The bilinear second moment of two Itô–Lévy processes over the augmented joint natural
filtration of the driver, where the driver itself supplies the cross witness. -/
theorem integral_mul_eq_of_isItoLevyProcess_aug
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug X X₀ b σ γ)
    {Y : ℝ → Ω → ℝ} {Y₀ : Ω → ℝ} {b' : ℝ → Ω → ℝ} {σ' : ℝ → Ω → Fin d → ℝ}
    {γ' : Ω → ℝ → E → ℝ}
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug Y Y₀ b' σ' γ')
    (hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] X₀)
    (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] Y₀)
    (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * Y T ω ∂P
      = ∫ ω, X₀ ω * Y₀ ω ∂P
        + (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b' s ω + Y s ω * b s ω ∂P)
        + (∑ j : Fin d, ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, σ s ω j * σ' s ω j ∂volume ∂P)
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, ∫ e, γ ω s e * γ' ω s e ∂ν ∂volume ∂P :=
  integral_mul_eq_of_isItoLevyProcess h h' D.crossWitness.aug hX₀ hX₀2 hbm hbp hbq hY₀ hY₀2
    hb'm hb'p hb'q hT

/-- The exponentially weighted second moment of an Itô–Lévy process over the augmented joint
natural filtration of the driver, where the driver itself supplies the cross witness. -/
theorem integral_exp_mul_self_eq_of_isItoLevyProcess_aug
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N
      (LevyStochCalc.Brownian.augFiltration D.filtration P) D.isBrownianFiltration_aug
      D.isPoissonFiltration_aug X X₀ b σ γ)
    (hX₀ : StronglyMeasurable[LevyStochCalc.Brownian.augFiltration D.filtration P 0] X₀)
    (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable
      (LevyStochCalc.Brownian.augFiltration D.filtration P) fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (β : ℝ) {T : ℝ} (hT : 0 < T) :
    Real.exp (β * T) * ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
            * (β * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b s ω ∂P
              + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
              + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) :=
  integral_exp_mul_self_eq_of_isItoLevyProcess h D.crossWitness.aug hX₀ hX₀2 hbm hbp hbq β hT

end AugmentedMore

end LevyStochCalc.Ito.SecondMoment
