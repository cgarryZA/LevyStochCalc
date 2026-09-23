/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedProfileMoments

/-!
# Linearity of the compensated integral of a mark profile

For the compensated integral `J(f)` over the step `(a, b]` of a mark profile `f : E → ℝ` against a
Poisson random measure with intensity `ν`, and square-integrable profiles `f₁, …, fₙ`,

  `J(∑ᵢ cᵢ fᵢ) = ∑ᵢ cᵢ J(fᵢ)`   almost surely.

The defect `X = J(∑ᵢ cᵢ fᵢ) − ∑ᵢ cᵢ J(fᵢ)` is orthogonal in `L²(P)` to the compensated integral
of every square-integrable profile, because the `L²(P)` pairing
`E[J(f) J(g)] = (b − a) ∫ f g dν` is linear in `f`. The defect is itself a combination of such
integrals, so its second moment vanishes.

The compensated integral depends on the profile only through its class modulo `ν`-null sets:
the approximating sequences of simple profiles, and hence the defining limit, are the same for
two profiles equal `ν`-almost everywhere.

## Main statements

* `LevyStochCalc.Poisson.compensatedProfile_congr_ae` — profiles equal `ν`-almost everywhere
  have the same compensated integral over every step.
* `LevyStochCalc.Poisson.compensatedProfile_ae_eq_of_ae_eq` — the same, almost surely.
* `LevyStochCalc.Poisson.compensatedProfile_finsetSum_smul` — the compensated integral of a
  finite linear combination of square-integrable profiles.
* `LevyStochCalc.Poisson.compensatedProfile_finsetSum` — of a finite sum.
* `LevyStochCalc.Poisson.compensatedProfile_add`, `LevyStochCalc.Poisson.compensatedProfile_smul`,
  `LevyStochCalc.Poisson.compensatedProfile_neg`, `LevyStochCalc.Poisson.compensatedProfile_sub`
  — of a sum, a scalar multiple, a negative and a difference.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Congruence -/

/-- **Congruence.** Two mark profiles equal `ν`-almost everywhere have the same compensated
integral over every step. -/
theorem compensatedProfile_congr_ae (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hfg : f =ᵐ[ν] g) (a b : ℝ) :
    compensatedProfile N f a b = compensatedProfile N g a b := by
  have hn : ∀ G : SimpleProfile E ν, eLpNorm (fun e => G.toFun e - f e) 2 ν
      = eLpNorm (fun e => G.toFun e - g e) 2 ν := fun G =>
    eLpNorm_congr_ae (hfg.mono fun e he => by simp only [he])
  have hpred : IsCompensatedProfile N f a b = IsCompensatedProfile N g a b := by
    funext J
    simp only [IsCompensatedProfile, hn]
  unfold compensatedProfile
  rw [hpred]

/-- Two mark profiles equal `ν`-almost everywhere have almost surely equal compensated integrals
over every step. -/
theorem compensatedProfile_ae_eq_of_ae_eq (N : PoissonRandomMeasure P ν) {f g : E → ℝ}
    (hfg : f =ᵐ[ν] g) (a b : ℝ) :
    compensatedProfile N f a b =ᵐ[P] compensatedProfile N g a b := by
  rw [compensatedProfile_congr_ae N hfg a b]

/-! ### Linear combinations -/

/-- **Linearity.** The compensated integral over the step `(a, b]` of a finite linear
combination of square-integrable mark profiles is almost surely the same linear combination of
their compensated integrals. -/
theorem compensatedProfile_finsetSum_smul (N : PoissonRandomMeasure P ν) {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) {f : ι → E → ℝ} (hf : ∀ i ∈ s, MemLp (f i) 2 ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (∑ i ∈ s, c i • f i) a b
      =ᵐ[P] ∑ i ∈ s, c i • compensatedProfile N (f i) a b := by
  set F : E → ℝ := ∑ i ∈ s, c i • f i with hFdef
  have hFe : ∀ e, F e = ∑ i ∈ s, c i * f i e := fun e => by
    simp [hFdef, Finset.sum_apply]
  have hF : MemLp F 2 ν := memLp_finsetSum' s fun i hi => (hf i hi).const_smul (c i)
  have hJ : ∀ g : E → ℝ, MemLp (compensatedProfile N g a b) 2 P :=
    fun g => memLp_compensatedProfile N g a b
  set X : Ω → ℝ := fun ω => compensatedProfile N F a b ω
    - ∑ i ∈ s, c i * compensatedProfile N (f i) a b ω with hXdef
  have hX : MemLp X 2 P :=
    (hJ F).sub (memLp_finsetSum s fun i _ => (hJ (f i)).const_mul (c i))
  have horth : ∀ g : E → ℝ, MemLp g 2 ν →
      ∫ ω, X ω * compensatedProfile N g a b ω ∂P = 0 := by
    intro g hg
    have hint : ∀ i ∈ s, Integrable (fun ω => c i * compensatedProfile N (f i) a b ω
        * compensatedProfile N g a b ω) P :=
      fun i _ => ((hJ (f i)).const_mul (c i)).integrable_mul (hJ g)
    have hνint : ∀ i ∈ s, Integrable (fun e => c i * f i e * g e) ν :=
      fun i hi => ((hf i hi).const_mul (c i)).integrable_mul hg
    have hνF : ∫ e, F e * g e ∂ν = ∑ i ∈ s, c i * ∫ e, f i e * g e ∂ν := by
      simp_rw [hFe, Finset.sum_mul]
      rw [integral_finsetSum s hνint]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← integral_const_mul]
      simp_rw [mul_assoc]
    calc ∫ ω, X ω * compensatedProfile N g a b ω ∂P
        = ∫ ω, compensatedProfile N F a b ω * compensatedProfile N g a b ω ∂P
          - ∑ i ∈ s, c i * ∫ ω, compensatedProfile N (f i) a b ω
            * compensatedProfile N g a b ω ∂P := by
          have h1 : Integrable (fun ω => compensatedProfile N F a b ω
              * compensatedProfile N g a b ω) P := (hJ F).integrable_mul (hJ g)
          simp only [hXdef, sub_mul, Finset.sum_mul]
          rw [integral_sub h1 (integrable_finsetSum s hint), integral_finsetSum s hint]
          refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
          rw [← integral_const_mul]
          simp_rw [mul_assoc]
      _ = (b - a) * (∫ e, F e * g e ∂ν - ∑ i ∈ s, c i * ∫ e, f i e * g e ∂ν) := by
          rw [integral_compensatedProfile_mul N hF hg ha hab, mul_sub, Finset.mul_sum]
          refine congrArg _ (Finset.sum_congr rfl fun i hi => ?_)
          rw [integral_compensatedProfile_mul N (hf i hi) hg ha hab]
          ring
      _ = 0 := by rw [hνF, sub_self, mul_zero]
  have hsq : ∫ ω, X ω ^ 2 ∂P = 0 := by
    have hint : ∀ i ∈ s, Integrable (fun ω => X ω * (c i * compensatedProfile N (f i) a b ω))
        P := fun i _ => hX.integrable_mul ((hJ (f i)).const_mul (c i))
    calc ∫ ω, X ω ^ 2 ∂P
        = ∫ ω, X ω * compensatedProfile N F a b ω ∂P
          - ∑ i ∈ s, c i * ∫ ω, X ω * compensatedProfile N (f i) a b ω ∂P := by
          have hpt : (fun ω => X ω ^ 2) = fun ω => X ω * compensatedProfile N F a b ω
              - ∑ i ∈ s, X ω * (c i * compensatedProfile N (f i) a b ω) := by
            funext ω
            rw [← Finset.mul_sum, ← mul_sub, sq]
          have h1 : Integrable (fun ω => X ω * compensatedProfile N F a b ω) P :=
            hX.integrable_mul (hJ F)
          rw [hpt, integral_sub h1 (integrable_finsetSum s hint), integral_finsetSum s hint]
          refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
          rw [← integral_const_mul]
          congr 1
          funext ω
          ring
      _ = 0 := by
          rw [horth F hF, Finset.sum_eq_zero fun i hi => by rw [horth (f i) (hf i hi), mul_zero],
            sub_zero]
  have hX0 : (fun ω => X ω ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (X ω)) hX.integrable_sq).1 hsq
  filter_upwards [hX0] with ω hω
  have h0 : X ω = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hω
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  simpa [hXdef, sub_eq_zero] using h0

/-- The compensated integral over the step `(a, b]` of a finite sum of square-integrable mark
profiles is almost surely the sum of their compensated integrals. -/
theorem compensatedProfile_finsetSum (N : PoissonRandomMeasure P ν) {ι : Type*}
    (s : Finset ι) {f : ι → E → ℝ} (hf : ∀ i ∈ s, MemLp (f i) 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    compensatedProfile N (∑ i ∈ s, f i) a b =ᵐ[P] ∑ i ∈ s, compensatedProfile N (f i) a b := by
  simpa using compensatedProfile_finsetSum_smul N s (fun _ => 1) hf ha hab

/-- The compensated integral over the step `(a, b]` of a sum of two square-integrable mark
profiles is almost surely the sum of their compensated integrals. -/
theorem compensatedProfile_add (N : PoissonRandomMeasure P ν) {f g : E → ℝ} (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (f + g) a b
      =ᵐ[P] compensatedProfile N f a b + compensatedProfile N g a b := by
  have h := compensatedProfile_finsetSum N (Finset.univ : Finset (Fin 2)) (f := ![f, g])
    (fun i _ => by fin_cases i <;> assumption) ha hab
  simpa [Fin.sum_univ_two] using h

/-- The compensated integral over the step `(a, b]` of a scalar multiple of a square-integrable
mark profile is almost surely the same multiple of its compensated integral. -/
theorem compensatedProfile_smul (N : PoissonRandomMeasure P ν) (c : ℝ) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (c • f) a b =ᵐ[P] c • compensatedProfile N f a b := by
  have h := compensatedProfile_finsetSum_smul N (Finset.univ : Finset (Fin 1)) (fun _ => c)
    (f := fun _ => f) (fun _ _ => hf) ha hab
  simpa using h

/-- The compensated integral over the step `(a, b]` of the negative of a square-integrable mark
profile is almost surely the negative of its compensated integral. -/
theorem compensatedProfile_neg (N : PoissonRandomMeasure P ν) {f : E → ℝ} (hf : MemLp f 2 ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (-f) a b =ᵐ[P] -compensatedProfile N f a b := by
  simpa using compensatedProfile_smul N (-1) hf ha hab

/-- The compensated integral over the step `(a, b]` of a difference of two square-integrable
mark profiles is almost surely the difference of their compensated integrals. -/
theorem compensatedProfile_sub (N : PoissonRandomMeasure P ν) {f g : E → ℝ} (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N (f - g) a b
      =ᵐ[P] compensatedProfile N f a b - compensatedProfile N g a b := by
  filter_upwards [compensatedProfile_add N hf hg.neg ha hab, compensatedProfile_neg N hg ha hab]
    with ω h1 h2
  simp only [sub_eq_add_neg, Pi.add_apply, Pi.neg_apply] at h1 h2 ⊢
  rw [h1, h2]

end LevyStochCalc.Poisson
