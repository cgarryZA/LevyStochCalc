/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.LinearCombination
import LevyStochCalc.Brownian.ItoL2Completion

/-!
# Linearity of the Itô integral in the driver

The elementary integral of a simple integrand against a linear combination of Brownian motions is
the corresponding combination of the elementary integrals, and both sides of the resulting
identity are `L²`-limits along the same approximating sequence, so the identity passes to the
`L²` Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- The elementary integral against a linear combination is the combination of the elementary
integrals. -/
theorem simpleIntegral_combineBM (W : Multidim.MultidimBrownianMotion P d) {c : Fin d → ℝ}
    (hc : ∑ i, c i ^ 2 = 1) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) (ω : Ω) :
    simpleIntegral (Multidim.MultidimBrownianMotion.combineBM W hc) G t ω
      = ∑ i, c i * simpleIntegral (W.W i) G t ω := by
  simp only [simpleIntegral]
  have hstep : ∀ k : Fin G.N,
      G.ξ k ω * ((Multidim.MultidimBrownianMotion.combineBM W hc).W
            (min (G.partition k.succ) t) ω
          - (Multidim.MultidimBrownianMotion.combineBM W hc).W
            (min (G.partition k.castSucc) t) ω)
        = ∑ i, c i * (G.ξ k ω * ((W.W i).W (min (G.partition k.succ) t) ω
            - (W.W i).W (min (G.partition k.castSucc) t) ω)) := by
    intro k
    show G.ξ k ω * (Multidim.MultidimBrownianMotion.combine W c _ ω
      - Multidim.MultidimBrownianMotion.combine W c _ ω) = _
    rw [Multidim.MultidimBrownianMotion.combine_sub, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [Finset.sum_congr rfl fun k _ => hstep k, Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _).symm

/-- Two `L²` limits of one sequence agree almost everywhere. -/
theorem ae_eq_of_tendsto_eLpNorm {f g : Ω → ℝ} {F : ℕ → Ω → ℝ}
    (hFm : ∀ n, AEStronglyMeasurable (F n) P)
    (hfm : AEStronglyMeasurable f P) (hgm : AEStronglyMeasurable g P)
    (hFf : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - f ω) 2 P) Filter.atTop (nhds 0))
    (hFg : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - g ω) 2 P) Filter.atTop (nhds 0)) :
    f =ᵐ[P] g := by
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hle : ∀ n : ℕ, eLpNorm (fun ω => f ω - g ω) 2 P
      ≤ eLpNorm (fun ω => F n ω - f ω) 2 P + eLpNorm (fun ω => F n ω - g ω) 2 P := by
    intro n
    have hcomm : eLpNorm (fun ω => f ω - F n ω) 2 P = eLpNorm (fun ω => F n ω - f ω) 2 P :=
      eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm])
    have hsplit : (fun ω => f ω - g ω)
        = (fun ω => f ω - F n ω) + fun ω => F n ω - g ω := by
      funext ω; simp only [Pi.add_apply]; ring
    rw [hsplit, ← hcomm]
    exact eLpNorm_add_le (hfm.sub (hFm n)) ((hFm n).sub hgm) hp1
  have hzero : eLpNorm (fun ω => f ω - g ω) 2 P = 0 := by
    refine le_antisymm ?_ (zero_le)
    have hlim : Filter.Tendsto (fun n => eLpNorm (fun ω => F n ω - f ω) 2 P
        + eLpNorm (fun ω => F n ω - g ω) 2 P) Filter.atTop (nhds 0) := by
      simpa using hFf.add hFg
    exact ge_of_tendsto hlim (Filter.Eventually.of_forall hle)
  have hae := (eLpNorm_eq_zero_iff (hfm.sub hgm) (by norm_num)).mp hzero
  filter_upwards [hae] with ω hω
  have hv : f ω - g ω = 0 := hω
  linarith

/-- **Linearity of the Itô integral in the driver.** -/
theorem stochasticIntegralBrownian_combineBM (W : Multidim.MultidimBrownianMotion P d)
    {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱB : IsBrownianFiltration (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian (Multidim.MultidimBrownianMotion.combineBM W hc) ℱ hℱB H hm hp hq t
      =ᵐ[P] fun ω => ∑ i, c i
        * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω := by
  have hp1 : (1 : ℝ≥0∞) ≤ 2 := by norm_num
  have hSm : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (n : ℕ),
      AEStronglyMeasurable (simpleIntegral V (masterApprox ℱ H hm hp hq n) t) P := by
    intro V n
    refine (Finset.measurable_sum _ fun k _ => ?_).aestronglyMeasurable
    exact ((masterApprox ℱ H hm hp hq n).ξ_measurable k).mul
      ((V.measurable_eval _).sub (V.measurable_eval _))
  have hIm : ∀ (V : LevyStochCalc.Brownian.BrownianMotion P) (hV : IsBrownianFiltration V ℱ),
      AEStronglyMeasurable (stochasticIntegralBrownian V ℱ hV H hm hp hq t) P := by
    intro V hV
    exact ((stochasticIntegralBrownian_stronglyAdapted V ℱ hV H hm hp hq t).mono
      (ℱ.le t)).aestronglyMeasurable
  have hgm : AEStronglyMeasurable
      (fun ω => ∑ i, c i * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) P := by
    have hpi : (fun ω => ∑ i, c i
          * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω)
        = ∑ i, fun ω => c i * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω := by
      funext ω; rw [Finset.sum_apply]
    rw [hpi]
    exact Finset.aestronglyMeasurable_sum _ fun i _ => (hIm (W.W i) (hℱi i)).const_mul _
  have hFf := masterApprox_tendsto_L2 (Multidim.MultidimBrownianMotion.combineBM W hc)
    ℱ hℱB H hm hp hq ht
  have hFg : Filter.Tendsto (fun n => eLpNorm (fun ω =>
      simpleIntegral (Multidim.MultidimBrownianMotion.combineBM W hc)
          (masterApprox ℱ H hm hp hq n) t ω
        - ∑ i, c i * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P)
      Filter.atTop (nhds 0) := by
    have hbound : ∀ n : ℕ, eLpNorm (fun ω =>
        simpleIntegral (Multidim.MultidimBrownianMotion.combineBM W hc)
            (masterApprox ℱ H hm hp hq n) t ω
          - ∑ i, c i * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P
        ≤ ∑ i, ‖c i‖ₑ * eLpNorm (fun ω =>
            simpleIntegral (W.W i) (masterApprox ℱ H hm hp hq n) t ω
              - stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P := by
      intro n
      have hpi : (fun ω => simpleIntegral (Multidim.MultidimBrownianMotion.combineBM W hc)
            (masterApprox ℱ H hm hp hq n) t ω
          - ∑ i, c i * stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω)
          = ∑ i, (c i) • fun ω => simpleIntegral (W.W i) (masterApprox ℱ H hm hp hq n) t ω
              - stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω := by
        funext ω
        rw [Finset.sum_apply, simpleIntegral_combineBM W hc, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
      rw [hpi]
      refine le_trans (eLpNorm_sum_le (fun i _ => ?_) hp1) (le_of_eq ?_)
      · exact ((hSm (W.W i) n).sub (hIm (W.W i) (hℱi i))).const_smul _
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [eLpNorm_const_smul]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_
      (fun n => zero_le) hbound
    have hzero : ∀ i : Fin d, Filter.Tendsto (fun n => ‖c i‖ₑ
        * eLpNorm (fun ω => simpleIntegral (W.W i) (masterApprox ℱ H hm hp hq n) t ω
          - stochasticIntegralBrownian (W.W i) ℱ (hℱi i) H hm hp hq t ω) 2 P)
        Filter.atTop (nhds 0) := by
      intro i
      have hlim := masterApprox_tendsto_L2 (W.W i) ℱ (hℱi i) H hm hp hq ht
      have := ENNReal.Tendsto.const_mul (a := ‖c i‖ₑ) hlim (Or.inr (by simp))
      simpa using this
    simpa using tendsto_finsetSum Finset.univ fun i _ => hzero i
  exact ae_eq_of_tendsto_eLpNorm (fun n => hSm _ n) (hIm _ hℱB) hgm hFf hFg

end LevyStochCalc.Brownian.Ito
