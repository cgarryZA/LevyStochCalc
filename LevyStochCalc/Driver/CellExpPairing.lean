/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellBrownianStep
import LevyStochCalc.Poisson.ProfileExpProduct
import Mathlib.Probability.Moments.ComplexMGF

/-!
# The character of a cell increment against the cell elements of order one and two

Over the cell `(s, t]` of a Lévy driver write `ΔWᵃ` for the increment of the Brownian coordinate
`a` and `J(f)` for the jump coordinate of the cell increment `levyCellProfileStep` along a mark
profile `f`. For a Brownian coordinate `j`, a square-integrable jump profile `h`, a volatility
`σ₀` and a frequency `u`, let `ξ = σ₀ ΔWʲ + J(h)`, `γ_u = e^{iuh} − 1` and
`β_a = i u σ₀ (t − s)` if `a = j`, `β_a = 0` otherwise. Then

* `E[e^{iuξ}] = e^{−u² σ₀² (t − s) / 2} E[e^{iuJ(h)}]`;
* `E[e^{iuξ} ΔWᵃ] = β_a E[e^{iuξ}]`;
* `E[e^{iuξ} (ΔWᵃ ΔWᵇ − δ_ab (t − s))] = β_a β_b E[e^{iuξ}]`;
* `E[e^{iuξ} J(f)] = (t − s) ∫ γ_u f dν · E[e^{iuξ}]`;
* `E[e^{iuξ} ΔWᵃ J(f)] = β_a (t − s) ∫ γ_u f dν · E[e^{iuξ}]`;
* `E[e^{iuξ} Q(f, g)] = (t − s)² ∫ γ_u f dν ∫ γ_u g dν · E[e^{iuξ}]` for the compensated product
  `Q(f, g) = J(f) J(g) − J(f g) − (t − s) ∫ f g dν` of profiles with `f g` square integrable.

The character factors as `e^{iuσ₀ΔWʲ} e^{iuJ(h)}`, a function of the Brownian coordinates times a
function of the Poisson random measure up to a null set, and so does each element paired with
it; the two σ-algebras are independent, so every expectation splits into a Gaussian factor and a
jump factor. The Gaussian factors are the derivatives of the complex moment generating function
`z ↦ e^{(t − s) z² / 2}` at `z = i u σ₀`, or vanish by the independence of distinct Brownian
coordinates; the jump factors are the pairings of `Poisson/ProfileExpPairing.lean` and
`Poisson/ProfileExpProduct.lean`.

## Main statements

* `LevyStochCalc.Driver.integral_exp_I_mul_levyCellProfileStep` — the character of `ξ`.
* `LevyStochCalc.Driver.integral_exp_I_mul_levyCellProfileStep_mul_castAdd` — the pairing with
  a Brownian coordinate of the cell increment.
* `LevyStochCalc.Driver.integral_exp_I_mul_levyCellProfileStep_mul_levyCellBrownian` — with the
  Brownian elements of degree two.
* `LevyStochCalc.Driver.integral_exp_I_mul_levyCellProfileStep_mul_natAdd` — with a jump
  coordinate of the cell increment.
* `LevyStochCalc.Driver.integral_exp_I_mul_levyCellProfileStep_mul_levyCellMixed` — with the
  mixed elements.
* `LevyStochCalc.Driver.integral_exp_I_mul_levyCellProfileStep_mul_levyCellProduct`,
  `LevyStochCalc.Driver.integral_exp_I_mul_levyCellProfileStep_mul_levyCellProduct_of_bound` —
  with the compensated products.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d q : ℕ}

/-! ### A centred Gaussian against its character -/

/-- The character of the law `𝒩(0, v)` and its pairings with `x` and with `x² − v`. -/
private theorem gaussian_exp_moments (v : ℝ≥0) (α : ℝ) :
    (∫ x, Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) ∂gaussianReal 0 v
      = Complex.exp (-((α ^ 2 * v / 2 : ℝ) : ℂ)))
    ∧ (∫ x, Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) * (x : ℂ) ∂gaussianReal 0 v
      = Complex.I * α * v * Complex.exp (-((α ^ 2 * v / 2 : ℝ) : ℂ)))
    ∧ (∫ x, Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) * ((x ^ 2 - v : ℝ) : ℂ)
        ∂gaussianReal 0 v
      = (Complex.I * α * v) ^ 2 * Complex.exp (-((α ^ 2 * v / 2 : ℝ) : ℂ))) := by
  set g : ℂ → ℂ := fun z => Complex.exp ((v : ℂ) * z ^ 2 / 2) with hg
  have hmgf : complexMGF id (gaussianReal 0 v) = g := funext fun z => by
    rw [complexMGF_id_gaussianReal]; simp [hg]
  have hd1 : ∀ z, HasDerivAt g (g z * ((v : ℂ) * z)) z := fun z => by
    refine (((hasDerivAt_pow 2 z).const_mul (v : ℂ)).div_const 2).cexp.congr_deriv ?_
    simp only [hg]
    ring
  have hd1' : deriv g = fun z => g z * ((v : ℂ) * z) := funext fun z => (hd1 z).deriv
  have hd2 : ∀ z, HasDerivAt (fun z => g z * ((v : ℂ) * z))
      (g z * ((v : ℂ) * z) * ((v : ℂ) * z) + g z * v) z := fun z => by
    refine ((hd1 z).mul ((hasDerivAt_id z).const_mul (v : ℂ))).congr_deriv ?_
    simp
  have hz : ∀ z : ℂ, z.re ∈ interior (integrableExpSet id (gaussianReal 0 v)) := by
    simp [integrableExpSet_id_gaussianReal]
  set z₀ : ℂ := Complex.I * α with hz₀
  have hexp : ∀ x : ℝ, Complex.exp (z₀ * (x : ℂ))
      = Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) := fun x => by
    rw [hz₀]; push_cast; ring_nf
  have e0 := iteratedDeriv_complexMGF (hz z₀) 0
  have e1 := iteratedDeriv_complexMGF (hz z₀) 1
  have e2 := iteratedDeriv_complexMGF (hz z₀) 2
  have i0 := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (hz z₀) 0
  have i2 := integrable_pow_mul_cexp_of_re_mem_interior_integrableExpSet (hz z₀) 2
  rw [hmgf] at e0 e1 e2
  simp only [iteratedDeriv_zero, iteratedDeriv_succ, hd1', (hd2 _).deriv, id, pow_zero,
    one_mul, pow_one, hexp] at e0 e1 e2 i0 i2
  have hgz : g z₀ = Complex.exp (-((α ^ 2 * v / 2 : ℝ) : ℂ)) := by
    rw [hg, hz₀]; push_cast; ring_nf; rw [Complex.I_sq]; ring_nf
  refine ⟨by rw [← e0, hgz], ?_, ?_⟩
  · rw [show (fun x : ℝ => Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) * (x : ℂ))
        = fun x : ℝ => (x : ℂ) * Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) from
        funext fun x => mul_comm _ _, ← e1, hgz, hz₀]
    ring
  · have hsplit : (fun x : ℝ => Complex.exp (Complex.I * ((α * x : ℝ) : ℂ))
        * ((x ^ 2 - v : ℝ) : ℂ))
        = fun x : ℝ => (x : ℂ) ^ 2 * Complex.exp (Complex.I * ((α * x : ℝ) : ℂ))
          - (v : ℂ) * Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) := funext fun x => by
      push_cast; ring
    rw [hsplit, integral_sub i2 (i0.const_mul _), integral_const_mul, ← e2, ← e0, hgz, hz₀]
    ring

/-! ### Factorisation over the Brownian and the Poisson σ-algebras -/

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

/-- A complex function of the Brownian coordinates and a complex function of the Poisson random
measure, up to a null set, factor in expectation. -/
private theorem integral_mul_of_sigmaPoisson_complex {Z Y : Ω → ℂ}
    (hZ : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)] Z)
    (hY : AEStronglyMeasurable[sigmaPoisson D.N] Y P) :
    ∫ ω, Z ω * Y ω ∂P = (∫ ω, Z ω ∂P) * ∫ ω, Y ω ∂P := by
  have hYm : StronglyMeasurable[sigmaPoisson D.N] (hY.mk Y) := hY.stronglyMeasurable_mk
  have hind : IndepFun Z (hY.mk Y) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left D.indep hZ.comap_le)
      hYm.measurable.comap_le
  have hcongr : ∫ ω, Z ω * Y ω ∂P = ∫ ω, Z ω * hY.mk Y ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hY.ae_eq_mk] with ω hω
    rw [hω]
  rw [hcongr, hind.integral_fun_mul_eq_mul_integral
      (hZ.mono (iSup_le fun i => Brownian.sigmaBrownian_le _) le_rfl).aestronglyMeasurable
      (hYm.mono (sigmaPoisson_le D.N)).aestronglyMeasurable,
    integral_congr_ae hY.ae_eq_mk.symm]

/-- A complex function of one Brownian coordinate and a complex function of everything else the
driver generates factor in expectation. -/
private theorem integral_mul_of_restSigma_complex (k : Fin d) {Z Y : Ω → ℂ}
    (hZ : Measurable[Brownian.sigmaBrownian (D.W.W k)] Z) (hY : Measurable[D.restSigma k] Y) :
    ∫ ω, Z ω * Y ω ∂P = (∫ ω, Z ω ∂P) * ∫ ω, Y ω ∂P := by
  have hind : IndepFun Z Y P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right
      (indep_of_indep_of_le_left (D.indep_restSigma k).symm hZ.comap_le) hY.comap_le
  exact hind.integral_fun_mul_eq_mul_integral
    (hZ.mono (Brownian.sigmaBrownian_le _) le_rfl).aestronglyMeasurable
    (hY.mono (D.restSigma_le k) le_rfl).aestronglyMeasurable

/-! ### The Brownian factor -/

/-- The character of a real multiple of a Brownian increment. -/
private theorem continuous_exp_mul (α : ℝ) :
    Continuous fun x : ℝ => Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) := by fun_prop

/-- The character of a Brownian increment over `(s, t]`. -/
private theorem integral_exp_increment (j : Fin d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (α : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ)) ∂P
      = Complex.exp (-((α ^ 2 * (t - s) / 2 : ℝ) : ℂ)) := by
  have h := (D.hasLaw_increment j hs hst).integral_comp
    (continuous_exp_mul α).aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h, (gaussian_exp_moments _ α).1]
  rfl

/-- The pairing of the character of the Brownian increment of the coordinate `j` with the
Brownian increment of a coordinate `a`. -/
private theorem integral_exp_increment_mul_increment (j a : Fin d) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (α : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ))
        * (((D.W.W a).W t ω - (D.W.W a).W s ω : ℝ) : ℂ) ∂P
      = (if a = j then Complex.I * α * ((t - s : ℝ) : ℂ) else 0)
        * ∫ ω, Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ))
          ∂P := by
  by_cases haj : a = j
  · subst haj
    rw [if_pos rfl, integral_exp_increment D a hs hst]
    have h := (D.hasLaw_increment a hs hst).integral_comp (by fun_prop : Continuous fun x : ℝ =>
      Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) * (x : ℂ)).aestronglyMeasurable
    simp only [Function.comp_def] at h
    rw [h, (gaussian_exp_moments _ α).2.1]
    rfl
  · rw [if_neg haj, zero_mul]
    have hZ : Measurable[Brownian.sigmaBrownian (D.W.W a)]
        fun ω => (((D.W.W a).W t ω - (D.W.W a).W s ω : ℝ) : ℂ) :=
      Complex.measurable_ofReal.comp (Measurable.of_comap_le
        (Brownian.comap_increment_le_sigmaBrownian (D.W.W a) s t))
    have hY : Measurable[D.restSigma a] fun ω =>
        Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ)) :=
      (continuous_exp_mul α).measurable.comp (D.measurable_increment_restSigma (Ne.symm haj) s t)
    simp_rw [mul_comm (Complex.exp _)]
    rw [D.integral_mul_of_restSigma_complex a hZ hY, integral_complex_ofReal,
      D.integral_increment a hs hst]
    simp

/-- The pairing of the character of the Brownian increment of the coordinate `j` with the
Brownian element of the coordinates `a` and `b`. -/
private theorem integral_exp_increment_mul_levyCellBrownian (j a b : Fin d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (α : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ))
        * (levyCellBrownian D s t a b ω : ℂ) ∂P
      = (if a = j then Complex.I * α * ((t - s : ℝ) : ℂ) else 0)
        * (if b = j then Complex.I * α * ((t - s : ℝ) : ℂ) else 0)
        * ∫ ω, Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ))
          ∂P := by
  have hX : ∀ k : Fin d, Measurable[Brownian.sigmaBrownian (D.W.W k)]
      fun ω => (D.W.W k).W t ω - (D.W.W k).W s ω := fun k =>
    Measurable.of_comap_le (Brownian.comap_increment_le_sigmaBrownian (D.W.W k) s t)
  have hY : ∀ k : Fin d, j ≠ k → Measurable[D.restSigma k] fun ω =>
      Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ)) :=
    fun k hjk => (continuous_exp_mul α).measurable.comp (D.measurable_increment_restSigma hjk s t)
  by_cases hab : a = j ∧ b = j
  · obtain ⟨ha, hb⟩ := hab
    rw [ha, hb, if_pos rfl, integral_exp_increment D j hs hst]
    have hc : Continuous fun x : ℝ =>
        Complex.exp (Complex.I * ((α * x : ℝ) : ℂ)) * ((x ^ 2 - (t - s) : ℝ) : ℂ) := by fun_prop
    have h := (D.hasLaw_increment j hs hst).integral_comp hc.aestronglyMeasurable
    simp only [Function.comp_def] at h
    have hpt : ∀ ω, levyCellBrownian D s t j j ω
        = ((D.W.W j).W t ω - (D.W.W j).W s ω) ^ 2 - (t - s) := fun ω => by
      simp [levyCellBrownian, sq]
    simp_rw [hpt]
    rw [h]
    refine (gaussian_exp_moments ⟨t - s, sub_nonneg.2 hst⟩ α).2.2.trans ?_
    change (Complex.I * α * ((t - s : ℝ) : ℂ)) ^ 2
      * Complex.exp (-((α ^ 2 * (t - s) / 2 : ℝ) : ℂ)) = _
    ring
  · have hR : (if a = j then Complex.I * α * ((t - s : ℝ) : ℂ) else 0)
        * (if b = j then Complex.I * α * ((t - s : ℝ) : ℂ) else 0) = 0 := by
      by_cases ha : a = j
      · simp [show b ≠ j from fun hb => hab ⟨ha, hb⟩]
      · simp [ha]
    rw [hR, zero_mul]
    simp_rw [mul_comm (Complex.exp _)]
    by_cases hab' : a = b
    · subst hab'
      have hZ : Measurable[Brownian.sigmaBrownian (D.W.W a)]
          fun ω => (levyCellBrownian D s t a a ω : ℂ) :=
        Complex.measurable_ofReal.comp (((hX a).mul (hX a)).sub measurable_const)
      rw [D.integral_mul_of_restSigma_complex a hZ (hY a fun h => hab ⟨h.symm, h.symm⟩),
        integral_complex_ofReal, integral_levyCellBrownian D a a hs hst]
      simp
    · obtain ⟨k, k', hjk, hkk', hpt⟩ : ∃ k k' : Fin d, j ≠ k ∧ k' ≠ k ∧ ∀ ω,
          levyCellBrownian D s t a b ω = ((D.W.W k).W t ω - (D.W.W k).W s ω)
            * ((D.W.W k').W t ω - (D.W.W k').W s ω) := by
        by_cases ha : a = j
        · refine ⟨b, a, fun h => hab ⟨ha, h.symm⟩, hab', fun ω => ?_⟩
          simp [levyCellBrownian, hab', mul_comm]
        · exact ⟨a, b, Ne.symm ha, Ne.symm hab', fun ω => by simp [levyCellBrownian, hab']⟩
      have hZ : Measurable[Brownian.sigmaBrownian (D.W.W k)]
          fun ω => (((D.W.W k).W t ω - (D.W.W k).W s ω : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp (hX k)
      have hY' : Measurable[D.restSigma k] fun ω =>
          (((D.W.W k').W t ω - (D.W.W k').W s ω : ℝ) : ℂ)
            * Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ)) :=
        (Complex.measurable_ofReal.comp (D.measurable_increment_restSigma hkk' s t)).mul
          (hY k hjk)
      have hpt' : ∀ ω, (levyCellBrownian D s t a b ω : ℂ)
          * Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ))
          = (((D.W.W k).W t ω - (D.W.W k).W s ω : ℝ) : ℂ)
            * ((((D.W.W k').W t ω - (D.W.W k').W s ω : ℝ) : ℂ)
              * Complex.exp (Complex.I * ((α * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ))) :=
        fun ω => by rw [hpt]; push_cast; ring
      simp_rw [hpt']
      rw [D.integral_mul_of_restSigma_complex k hZ hY', integral_complex_ofReal,
        D.integral_increment k hs hst]
      simp

/-! ### The jump factor -/

/-- The first-order pairing of the character of a jump coordinate of the cell increment. -/
private theorem integral_exp_repr_mul_repr {h f : E → ℝ} (hh : MemLp h 2 ν) (hf : MemLp f 2 ν)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I
        * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N h s t ω : ℝ) : ℂ))
        * (Poisson.compensatedProfileRepr (D.filtration t) D.N f s t ω : ℂ) ∂P
      = ((t - s : ℝ) : ℂ)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I
          * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N h s t ω : ℝ) : ℂ)) ∂P := by
  have hJh := Poisson.compensatedProfileRepr_ae_eq (D.filtration t) D.N h s t
  have hJf := Poisson.compensatedProfileRepr_ae_eq (D.filtration t) D.N f s t
  have h0 : ∫ ω, Complex.exp (Complex.I
      * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N h s t ω : ℝ) : ℂ)) ∂P
      = ∫ ω, Complex.exp (Complex.I
        * ((u * Poisson.compensatedProfile D.N h s t ω : ℝ) : ℂ)) ∂P :=
    integral_congr_ae (by filter_upwards [hJh] with ω e1; rw [e1])
  rw [h0, integral_congr_ae (by filter_upwards [hJh, hJf] with ω e1 e2; rw [e1, e2])]
  exact Poisson.integral_exp_I_mul_compensatedProfile_mul D.N hh hf hs hst u

/-- The pairing of the character of a jump coordinate of the cell increment with a compensated
product over the cell. -/
private theorem integral_exp_repr_mul_levyCellProduct {h f g : E → ℝ} (hh : MemLp h 2 ν)
    (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) (hfg : MemLp (fun e => f e * g e) 2 ν) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I
        * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N h s t ω : ℝ) : ℂ))
        * (levyCellProduct D s t f g ω : ℂ) ∂P
      = ((t - s : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * h e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I
          * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N h s t ω : ℝ) : ℂ)) ∂P := by
  have hJh := Poisson.compensatedProfileRepr_ae_eq (D.filtration t) D.N h s t
  have hQ := levyCellProduct_ae_eq D s t f g
  have h0 : ∫ ω, Complex.exp (Complex.I
      * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N h s t ω : ℝ) : ℂ)) ∂P
      = ∫ ω, Complex.exp (Complex.I
        * ((u * Poisson.compensatedProfile D.N h s t ω : ℝ) : ℂ)) ∂P :=
    integral_congr_ae (by filter_upwards [hJh] with ω e1; rw [e1])
  rw [h0, integral_congr_ae (by filter_upwards [hJh, hQ] with ω e1 e2; rw [e1, e2])]
  exact Poisson.integral_exp_I_mul_compensatedProfile_mul_compensatedProduct D.N hh hf hg hfg
    hs hst u

/-! ### The character of the cell increment -/

/-- **Factorisation.** The character of `σ₀ ΔWʲ + J(η_r)` times a function of the Brownian
coordinates times a function of the Poisson random measure splits into a Gaussian and a jump
factor. -/
private theorem integral_cellExp_mul (j : Fin d) {η : Fin q → E → ℝ} (r : Fin q)
    (hη : MemLp (η r) 2 ν) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (σ₀ u : ℝ) {B Y : Ω → ℂ}
    (hB : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)] B)
    (hY : AEStronglyMeasurable[sigmaPoisson D.N] Y P) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) * (B ω * Y ω) ∂P
      = (∫ ω, Complex.exp (Complex.I
          * (((u * σ₀) * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ)) * B ω ∂P)
        * ∫ ω, Complex.exp (Complex.I
          * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N (η r) s t ω : ℝ) : ℂ))
          * Y ω ∂P := by
  have hpt : ∀ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω
      (Fin.castAdd q j) + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ))
      * (B ω * Y ω)
      = (Complex.exp (Complex.I * (((u * σ₀) * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ))
          * B ω)
        * (Complex.exp (Complex.I
          * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N (η r) s t ω : ℝ) : ℂ))
          * Y ω) := fun ω => by
    rw [levyCellProfileStep_castAdd, levyCellProfileStep_natAdd, mul_mul_mul_comm,
      ← Complex.exp_add]
    congr 2
    push_cast
    ring
  simp_rw [hpt]
  exact D.integral_mul_of_sigmaPoisson_complex
    (((continuous_exp_mul (u * σ₀)).measurable.comp
      (D.measurable_increment_iSup_sigmaBrownian j s t)).mul hB)
    (((continuous_exp_mul u).comp_aestronglyMeasurable
      (aestronglyMeasurable_sigmaPoisson_compensatedProfileRepr D hη hs hst)).mul hY)

/-- The character of `σ₀ ΔWʲ + J(η_r)` as the product of its Gaussian and jump factors. -/
private theorem integral_cellExp (j : Fin d) {η : Fin q → E → ℝ} (r : Fin q)
    (hη : MemLp (η r) 2 ν) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P
      = (∫ ω, Complex.exp (Complex.I
          * (((u * σ₀) * ((D.W.W j).W t ω - (D.W.W j).W s ω) : ℝ) : ℂ)) ∂P)
        * ∫ ω, Complex.exp (Complex.I
          * ((u * Poisson.compensatedProfileRepr (D.filtration t) D.N (η r) s t ω : ℝ) : ℂ))
          ∂P := by
  have h := D.integral_cellExp_mul j r hη hs hst σ₀ u (B := fun _ => 1) (Y := fun _ => 1)
    measurable_const aestronglyMeasurable_const
  simpa only [mul_one] using h

end LevyDriver

/-! ### The pairings -/

/-- **The character of the cell increment.** For the Brownian coordinate `j` and the jump
coordinate `r` of the cell increment over `(s, t]`, with square-integrable profile `η r`,
`E[e^{iu(σ₀ ΔWʲ + J(η_r))}] = e^{−u² σ₀² (t − s) / 2} E[e^{iuJ(η_r)}]`. -/
theorem integral_exp_I_mul_levyCellProfileStep (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {η : Fin q → E → ℝ} (r : Fin q) (hη : MemLp (η r) 2 ν) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P
      = Complex.exp (-((u ^ 2 * σ₀ ^ 2 * (t - s) / 2 : ℝ) : ℂ))
        * ∫ ω, Complex.exp (Complex.I
          * ((u * levyCellProfileStep D s t η ω (Fin.natAdd d r) : ℝ) : ℂ)) ∂P := by
  rw [D.integral_cellExp j r hη hs hst σ₀ u, D.integral_exp_increment j hs hst,
    show (u * σ₀) ^ 2 * (t - s) / 2 = u ^ 2 * σ₀ ^ 2 * (t - s) / 2 by ring]
  simp only [levyCellProfileStep_natAdd]

/-- **The pairing with a Brownian coordinate.** For the Brownian coordinates `j, a` and the jump
coordinate `r` of the cell increment over `(s, t]`, with `ξ = σ₀ ΔWʲ + J(η_r)`,
`E[e^{iuξ} ΔWᵃ] = β_a E[e^{iuξ}]` with `β_a = i u σ₀ (t − s)` if `a = j` and `β_a = 0`
otherwise. -/
theorem integral_exp_I_mul_levyCellProfileStep_mul_castAdd (D : LevyDriver.{u, v, w} P d ν)
    (j a : Fin d) {η : Fin q → E → ℝ} (r : Fin q) (hη : MemLp (η r) 2 ν) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ))
        * (levyCellProfileStep D s t η ω (Fin.castAdd q a) : ℂ) ∂P
      = (if a = j then Complex.I * u * σ₀ * ((t - s : ℝ) : ℂ) else 0)
        * ∫ ω, Complex.exp (Complex.I * ((u * (σ₀
          * levyCellProfileStep D s t η ω (Fin.castAdd q j)
          + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P := by
  have h := D.integral_cellExp_mul j r hη hs hst σ₀ u (Y := fun _ => 1)
    (B := fun ω => (((D.W.W a).W t ω - (D.W.W a).W s ω : ℝ) : ℂ))
    (Complex.measurable_ofReal.comp (D.measurable_increment_iSup_sigmaBrownian a s t))
    aestronglyMeasurable_const
  simp only [mul_one, ← levyCellProfileStep_castAdd D s t η _ a] at h
  rw [h, D.integral_cellExp j r hη hs hst σ₀ u]
  simp only [levyCellProfileStep_castAdd]
  rw [D.integral_exp_increment_mul_increment j a hs hst (u * σ₀)]
  split_ifs <;> push_cast <;> ring

/-- **The pairing with a Brownian element of degree two.** For the Brownian coordinates
`j, a, b` and the jump coordinate `r` of the cell increment over `(s, t]`, with
`ξ = σ₀ ΔWʲ + J(η_r)`, `E[e^{iuξ} (ΔWᵃ ΔWᵇ − δ_ab (t − s))] = β_a β_b E[e^{iuξ}]` with
`β_a = i u σ₀ (t − s)` if `a = j` and `β_a = 0` otherwise. -/
theorem integral_exp_I_mul_levyCellProfileStep_mul_levyCellBrownian
    (D : LevyDriver.{u, v, w} P d ν) (j a b : Fin d) {η : Fin q → E → ℝ} (r : Fin q)
    (hη : MemLp (η r) 2 ν) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ))
        * (levyCellBrownian D s t a b ω : ℂ) ∂P
      = (if a = j then Complex.I * u * σ₀ * ((t - s : ℝ) : ℂ) else 0)
        * (if b = j then Complex.I * u * σ₀ * ((t - s : ℝ) : ℂ) else 0)
        * ∫ ω, Complex.exp (Complex.I * ((u * (σ₀
          * levyCellProfileStep D s t η ω (Fin.castAdd q j)
          + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P := by
  have h := D.integral_cellExp_mul j r hη hs hst σ₀ u (Y := fun _ => 1)
    (B := fun ω => (levyCellBrownian D s t a b ω : ℂ))
    (Complex.measurable_ofReal.comp (((D.measurable_increment_iSup_sigmaBrownian a s t).mul
      (D.measurable_increment_iSup_sigmaBrownian b s t)).sub measurable_const))
    aestronglyMeasurable_const
  simp only [mul_one] at h
  rw [h, D.integral_cellExp j r hη hs hst σ₀ u,
    D.integral_exp_increment_mul_levyCellBrownian j a b hs hst (u * σ₀)]
  split_ifs <;> push_cast <;> ring

/-- **The pairing with a jump coordinate.** For the Brownian coordinate `j` and the jump
coordinates `r, r'` of the cell increment over `(s, t]`, with square-integrable profiles and
`ξ = σ₀ ΔWʲ + J(η_r)`, `E[e^{iuξ} J(η_{r'})] = (t − s) ∫ γ_u η_{r'} dν · E[e^{iuξ}]` with
`γ_u = e^{iuη_r} − 1`. -/
theorem integral_exp_I_mul_levyCellProfileStep_mul_natAdd (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {η : Fin q → E → ℝ} (r r' : Fin q) (hη : MemLp (η r) 2 ν)
    (hη' : MemLp (η r') 2 ν) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ))
        * (levyCellProfileStep D s t η ω (Fin.natAdd d r') : ℂ) ∂P
      = ((t - s : ℝ) : ℂ)
          * (∫ e, (Complex.exp (Complex.I * ((u * η r e : ℝ) : ℂ)) - 1) * (η r' e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * (σ₀
          * levyCellProfileStep D s t η ω (Fin.castAdd q j)
          + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P := by
  have h := D.integral_cellExp_mul j r hη hs hst σ₀ u (B := fun _ => 1)
    (Y := fun ω => (Poisson.compensatedProfileRepr (D.filtration t) D.N (η r') s t ω : ℂ))
    measurable_const (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_sigmaPoisson_compensatedProfileRepr D hη' hs hst))
  simp only [one_mul, mul_one, ← levyCellProfileStep_natAdd D s t η _ r'] at h
  rw [h, D.integral_cellExp j r hη hs hst σ₀ u]
  simp only [levyCellProfileStep_natAdd]
  rw [D.integral_exp_repr_mul_repr hη hη' hs hst u]
  ring

/-- **The pairing with a mixed element.** For the Brownian coordinates `j, a` and the jump
coordinate `r` of the cell increment over `(s, t]`, a square-integrable profile `f` and
`ξ = σ₀ ΔWʲ + J(η_r)`, `E[e^{iuξ} ΔWᵃ J(f)] = β_a (t − s) ∫ γ_u f dν · E[e^{iuξ}]` with
`γ_u = e^{iuη_r} − 1`, `β_a = i u σ₀ (t − s)` if `a = j` and `β_a = 0` otherwise. -/
theorem integral_exp_I_mul_levyCellProfileStep_mul_levyCellMixed
    (D : LevyDriver.{u, v, w} P d ν) (j a : Fin d) {η : Fin q → E → ℝ} (r : Fin q)
    (hη : MemLp (η r) 2 ν) {f : E → ℝ} (hf : MemLp f 2 ν) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ))
        * (levyCellMixed D s t a f ω : ℂ) ∂P
      = (if a = j then Complex.I * u * σ₀ * ((t - s : ℝ) : ℂ) else 0)
        * (((t - s : ℝ) : ℂ)
          * ∫ e, (Complex.exp (Complex.I * ((u * η r e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * (σ₀
          * levyCellProfileStep D s t η ω (Fin.castAdd q j)
          + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P := by
  have h := D.integral_cellExp_mul j r hη hs hst σ₀ u
    (B := fun ω => (((D.W.W a).W t ω - (D.W.W a).W s ω : ℝ) : ℂ))
    (Y := fun ω => (Poisson.compensatedProfileRepr (D.filtration t) D.N f s t ω : ℂ))
    (Complex.measurable_ofReal.comp (D.measurable_increment_iSup_sigmaBrownian a s t))
    (Complex.continuous_ofReal.comp_aestronglyMeasurable
      (aestronglyMeasurable_sigmaPoisson_compensatedProfileRepr D hf hs hst))
  have hpt : ∀ ω, (levyCellMixed D s t a f ω : ℂ)
      = (((D.W.W a).W t ω - (D.W.W a).W s ω : ℝ) : ℂ)
        * (Poisson.compensatedProfileRepr (D.filtration t) D.N f s t ω : ℂ) := fun ω => by
    simp [levyCellMixed]
  simp_rw [hpt]
  rw [h, D.integral_cellExp j r hη hs hst σ₀ u,
    D.integral_exp_increment_mul_increment j a hs hst (u * σ₀),
    D.integral_exp_repr_mul_repr hη hf hs hst u]
  split_ifs <;> push_cast <;> ring

/-- **The pairing with a compensated product.** For the Brownian coordinate `j` and the jump
coordinate `r` of the cell increment over `(s, t]`, square-integrable profiles `f, g` with
square-integrable product and `ξ = σ₀ ΔWʲ + J(η_r)`,
`E[e^{iuξ} Q(f, g)] = (t − s)² ∫ γ_u f dν ∫ γ_u g dν · E[e^{iuξ}]` with `γ_u = e^{iuη_r} − 1`
and `Q(f, g) = J(f) J(g) − J(f g) − (t − s) ∫ f g dν`. -/
theorem integral_exp_I_mul_levyCellProfileStep_mul_levyCellProduct
    (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {η : Fin q → E → ℝ} (r : Fin q)
    (hη : MemLp (η r) 2 ν) {f g : E → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν)
    (hfg : MemLp (fun e => f e * g e) 2 ν) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ))
        * (levyCellProduct D s t f g ω : ℂ) ∂P
      = ((t - s : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * η r e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * η r e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * (σ₀
          * levyCellProfileStep D s t η ω (Fin.castAdd q j)
          + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P := by
  have hQ : AEStronglyMeasurable[sigmaPoisson D.N] (levyCellProduct D s t f g) P :=
    (((aestronglyMeasurable_sigmaPoisson_compensatedProfileRepr D hf hs hst).mul
      (aestronglyMeasurable_sigmaPoisson_compensatedProfileRepr D hg hs hst)).sub
      (aestronglyMeasurable_sigmaPoisson_compensatedProfileRepr D hfg hs hst)).sub
      aestronglyMeasurable_const
  have h := D.integral_cellExp_mul j r hη hs hst σ₀ u (B := fun _ => 1)
    (Y := fun ω => (levyCellProduct D s t f g ω : ℂ)) measurable_const
    (Complex.continuous_ofReal.comp_aestronglyMeasurable hQ)
  simp only [one_mul, mul_one] at h
  rw [h, D.integral_cellExp j r hη hs hst σ₀ u,
    D.integral_exp_repr_mul_levyCellProduct hη hf hg hfg hs hst u]
  ring

/-- The pairing with the compensated product of a square-integrable profile and a bounded
square-integrable one. -/
theorem integral_exp_I_mul_levyCellProfileStep_mul_levyCellProduct_of_bound
    (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {η : Fin q → E → ℝ} (r : Fin q)
    (hη : MemLp (η r) 2 ν) {f g : E → ℝ} (hf : MemLp f 2 ν) (hg : MemLp g 2 ν) {Cg : ℝ}
    (hbg : ∀ e, |g e| ≤ Cg) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (σ₀ u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (σ₀ * levyCellProfileStep D s t η ω (Fin.castAdd q j)
        + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ))
        * (levyCellProduct D s t f g ω : ℂ) ∂P
      = ((t - s : ℝ) : ℂ) ^ 2
          * (∫ e, (Complex.exp (Complex.I * ((u * η r e : ℝ) : ℂ)) - 1) * (f e : ℂ) ∂ν)
          * (∫ e, (Complex.exp (Complex.I * ((u * η r e : ℝ) : ℂ)) - 1) * (g e : ℂ) ∂ν)
        * ∫ ω, Complex.exp (Complex.I * ((u * (σ₀
          * levyCellProfileStep D s t η ω (Fin.castAdd q j)
          + levyCellProfileStep D s t η ω (Fin.natAdd d r)) : ℝ) : ℂ)) ∂P :=
  integral_exp_I_mul_levyCellProfileStep_mul_levyCellProduct D j r hη hf hg
    (hf.of_le_mul (c := Cg) (hf.1.mul hg.1) (Eventually.of_forall fun e => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, mul_comm Cg]
      exact mul_le_mul_of_nonneg_left (hbg e) (abs_nonneg _))) hs hst σ₀ u

end LevyStochCalc.Driver
