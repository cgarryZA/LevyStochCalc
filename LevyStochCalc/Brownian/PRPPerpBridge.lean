/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.PRPMultidimRange
import LevyStochCalc.Brownian.ItoIncrementMoment

/-!
# From horizon orthogonality to orthogonality against every Itô integral

A weight orthogonal to the Itô integrals of integrands supported in `[0, T]` is orthogonal to
`∫_0^t K dW` for every admissible `K` and every `t > 0`. For `t ≤ T` this is because `K` clipped
to `(0, t]` is such an integrand and its integral over the horizon is `∫_0^t K dW`; for `t > T`
the remaining increment is a martingale increment after `T`, which a weight measurable before `T`
does not see.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- An admissible integrand clipped to `(0, t]`, as an integrand over the horizon `[0, T]`. -/
noncomputable def clipHorizonIntegrand (K : Ω → ℝ → ℝ)
    (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) : HorizonIntegrand P ℱ T where
  toFun := fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * K ω s
  measurable_uncurry := measurable_uncurry_indicator_Ioc_mul K hm 0 t
  progressive := progressivelyMeasurable_indicator_Ioc_mul ℱ K hp 0 t
  vanishing := by
    intro ω s hs
    have hns : s ∉ Set.Ioc (0 : ℝ) t := fun h => hs ⟨h.1.le, h.2.trans htT⟩
    rw [Set.indicator_of_notMem hns, zero_mul]
  energy_ne_top := by
    exact (lintegral_sq_indicator_Ioc_mul_lt_top K hq 0 t T (ht.trans_le htT)).ne

/-- The clipped integrand's integral over the horizon is the integral up to the clipping time. -/
theorem integral_clipHorizonIntegrand (V : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration V ℱ) (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t T : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    (clipHorizonIntegrand K hm hp hq ht htT).integral V hℱ
      =ᵐ[P] stochasticIntegralBrownian V ℱ hℱ K hm hp hq t := by
  have hT : (0 : ℝ) < T := ht.trans_le htT
  have hcoe : (clipHorizonIntegrand K hm hp hq ht htT).integral V hℱ
      = stochasticIntegralBrownian V ℱ hℱ
        (fun ω s => (Set.Ioc (0 : ℝ) t).indicator (fun _ => (1 : ℝ)) s * K ω s)
        (measurable_uncurry_indicator_Ioc_mul K hm 0 t)
        (progressivelyMeasurable_indicator_Ioc_mul ℱ K hp 0 t)
        (lintegral_sq_indicator_Ioc_mul_lt_top K hq 0 t) T := rfl
  have hind := stochasticIntegralBrownian_indicator_Ioc V ℱ hℱ K hm hp hq (le_refl (0 : ℝ)) ht
    (measurable_uncurry_indicator_Ioc_mul K hm 0 t)
    (progressivelyMeasurable_indicator_Ioc_mul ℱ K hp 0 t)
    (lintegral_sq_indicator_Ioc_mul_lt_top K hq 0 t) hT
  have hz := stochasticIntegralBrownian_ae_zero_of_nonpos V ℱ hℱ K hm hp hq (le_refl (0 : ℝ))
  rw [hcoe]
  filter_upwards [hind, hz] with ω e1 e2
  rw [e1, min_eq_left htT, min_eq_left hT.le, e2, Pi.zero_apply, sub_zero]

omit [IsProbabilityMeasure P] in
/-- A product of two square-integrable functions is integrable. -/
lemma integrable_mul_of_memLp_two {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := by
  have hdom : Integrable (fun ω => 1 / 2 * f ω ^ 2 + 1 / 2 * g ω ^ 2) P :=
    (hf.integrable_sq.const_mul (1 / 2 : ℝ)).add (hg.integrable_sq.const_mul (1 / 2 : ℝ))
  refine Integrable.mono' hdom (hf.1.mul hg.1) ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  nlinarith [sq_abs (f ω), sq_abs (g ω), sq_nonneg (|f ω| - |g ω|)]

/-- **A weight measurable before `T` does not see the increment of the integral after `T`.** -/
theorem integral_mul_increment_eq_zero (V : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration V ℱ) (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {z : Ω → ℝ} (hz2 : MemLp z 2 P) {T t : ℝ}
    (hzm : AEStronglyMeasurable[ℱ T] z P) (hTt : T ≤ t) :
    ∫ ω, z ω * (stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
      - stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω) ∂P = 0 := by
  haveI : SigmaFinite (P.trim (ℱ.rightCont.le T)) := by infer_instance
  set M := stochasticIntegralBrownian V ℱ hℱ K hm hp hq with hMdef
  have hmart : MeasureTheory.Martingale M ℱ.rightCont P :=
    martingale_rightCont_stochasticIntegralBrownian V ℱ hℱ K hm hp hq
  have hMLp : ∀ u : ℝ, MemLp (M u) 2 P := fun u =>
    stochasticIntegralBrownian_memLp V ℱ hℱ K hm hp hq u
  have hMint : ∀ u : ℝ, Integrable (M u) P := fun u => (hMLp u).integrable (by norm_num)
  have hgLp : MemLp (fun ω => M t ω - M T ω) 2 P := (hMLp t).sub (hMLp T)
  have hgint : Integrable (fun ω => M t ω - M T ω) P := (hMint t).sub (hMint T)
  have hzm' : AEStronglyMeasurable[ℱ.rightCont T] z P := hzm.mono (ℱ.le_rightCont T)
  have hprod : Integrable (fun ω => z ω * (M t ω - M T ω)) P :=
    integrable_mul_of_memLp_two hz2 hgLp
  have hpull := condExp_mul_of_aestronglyMeasurable_left (m := ℱ.rightCont T)
    (f := z) (g := fun ω => M t ω - M T ω) hzm' hprod hgint
  have hcond : P[(fun ω => M t ω - M T ω) | ℱ.rightCont T] =ᵐ[P] 0 := by
    have h1 : P[(fun ω => M t ω - M T ω) | ℱ.rightCont T]
        =ᵐ[P] P[M t | ℱ.rightCont T] - P[M T | ℱ.rightCont T] :=
      condExp_sub (hMint t) (hMint T) _
    have h2 : P[M t | ℱ.rightCont T] =ᵐ[P] M T := hmart.2 T t hTt
    have h3 : P[M T | ℱ.rightCont T] = M T :=
      condExp_of_stronglyMeasurable (ℱ.rightCont.le T) (hmart.1 T) (hMint T)
    rw [h3] at h1
    filter_upwards [h1, h2] with ω e1 e2
    rw [e1, Pi.sub_apply, e2, sub_self]
    rfl
  have key : ∫ ω, z ω * (M t ω - M T ω) ∂P
      = ∫ ω, (P[(fun ω => z ω * (M t ω - M T ω)) | ℱ.rightCont T]) ω ∂P :=
    (integral_condExp (ℱ.rightCont.le T)).symm
  have hpull' : P[(fun ω => z ω * (M t ω - M T ω)) | ℱ.rightCont T]
      =ᵐ[P] z * P[(fun ω => M t ω - M T ω) | ℱ.rightCont T] := hpull
  rw [key]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [hpull', hcond] with ω e1 e2
  rw [e1, Pi.mul_apply, e2, Pi.zero_apply, mul_zero]

/-- **The perp bridge.** A square-integrable weight measurable before `T` and orthogonal to the
Itô integrals of every integrand supported in `[0, T]` is orthogonal to `∫_0^t K dW` for every
admissible `K` and every positive `t`. -/
theorem integral_mul_stochasticIntegral_eq_zero (V : LevyStochCalc.Brownian.BrownianMotion P)
    (hℱ : IsBrownianFiltration V ℱ) {T : ℝ} (hT : 0 < T) {z : Ω → ℝ} (hz2 : MemLp z 2 P)
    (hzm : AEStronglyMeasurable[ℱ T] z P)
    (hperp : ∀ G : HorizonIntegrand P ℱ T, ∫ ω, z ω * G.integral V hℱ ω ∂P = 0)
    (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω ∂P = 0 := by
  have hclip : ∀ {u : ℝ}, 0 < u → u ≤ T →
      ∫ ω, z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq u ω ∂P = 0 := by
    intro u hu huT
    have h := hperp (clipHorizonIntegrand K hm hp hq hu huT)
    rw [← h]
    refine integral_congr_ae ?_
    filter_upwards [integral_clipHorizonIntegrand V hℱ K hm hp hq hu huT] with ω e
    rw [e]
  rcases le_or_gt t T with htT | hTt
  · exact hclip ht htT
  · have hMLp : ∀ u : ℝ, MemLp (stochasticIntegralBrownian V ℱ hℱ K hm hp hq u) 2 P := fun u =>
      stochasticIntegralBrownian_memLp V ℱ hℱ K hm hp hq u
    have h2 := integral_mul_increment_eq_zero V hℱ K hm hp hq hz2 hzm hTt.le (t := t)
    have hint1 : Integrable
        (fun ω => z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω) P :=
      integrable_mul_of_memLp_two hz2 (hMLp T)
    have hint2 : Integrable (fun ω => z ω * (stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
        - stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω)) P :=
      integrable_mul_of_memLp_two hz2 ((hMLp t).sub (hMLp T))
    have hrw : (fun ω => z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω)
        = fun ω => z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω
          + z ω * (stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
            - stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω) := by
      funext ω; ring
    rw [show (∫ ω, z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω ∂P)
        = ∫ ω, (z ω * stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω
          + z ω * (stochasticIntegralBrownian V ℱ hℱ K hm hp hq t ω
            - stochasticIntegralBrownian V ℱ hℱ K hm hp hq T ω)) ∂P from by rw [hrw],
      integral_add hint1 hint2, hclip hT (le_refl T), h2, add_zero]

end LevyStochCalc.Brownian.Ito
