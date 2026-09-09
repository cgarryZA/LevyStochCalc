/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.VectorItoThirdMoment
import LevyStochCalc.Brownian.TaylorTwoVector

/-!
# The Taylor remainder of a vector Itô process along a uniform grid

Expanding a twice-differentiable function of a vector Itô process cell by cell leaves a
second-order Taylor remainder. For a Lipschitz second derivative that remainder is cubic in the
increment, so the third moments of the increments bound it in `L¹`; across a uniform grid of `m`
cells the bound is of order `m^{-1/2}`.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_taylorRemainderNormed` — the remainder along a
  measurable sequence is measurable.
* `LevyStochCalc.Brownian.Ito.integral_abs_vectorTaylorRemainder_le` — the `L¹` bound of order
  `m^{-1/2}`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section RemainderMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- The second-order Taylor remainder along a measurable sequence of a function with continuous
first and second derivatives is measurable. -/
theorem measurable_taylorRemainderNormed {f : E → ℝ} {f' : E → E →L[ℝ] ℝ}
    {f'' : E → E →L[ℝ] E →L[ℝ] ℝ} (hfc : Continuous f) (hf'c : Continuous f')
    (hf''c : Continuous f'') {x : ℕ → Ω → E} (hx : ∀ i, Measurable (x i)) (m : ℕ) :
    Measurable fun ω => taylorRemainderNormed f f' f'' (fun i => x i ω) m := by
  have hfirst : ∀ i : ℕ, Measurable fun ω => f' (x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f' p.1 (p.2 - p.1) :=
      (hf'c.comp continuous_fst).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  have hsecond : ∀ i : ℕ,
      Measurable fun ω => f'' (x i ω) (x (i + 1) ω - x i ω) (x (i + 1) ω - x i ω) := by
    intro i
    have hcont : Continuous fun p : E × E => f'' p.1 (p.2 - p.1) (p.2 - p.1) :=
      ((hf''c.comp continuous_fst).clm_apply
        (continuous_snd.sub continuous_fst)).clm_apply (continuous_snd.sub continuous_fst)
    exact hcont.measurable.comp ((hx i).prodMk (hx (i + 1)))
  unfold taylorRemainderNormed
  exact ((hfc.measurable.comp (hx m)).sub (hfc.measurable.comp (hx 0))).sub
    ((Finset.measurable_sum _ fun i _ => hfirst i).add
      (Finset.measurable_sum _ fun i _ => (hsecond i).div_const 2))

end RemainderMeasurable

section VectorTaylor

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
  (H : Fin n → Fin d → Ω → ℝ → ℝ)
  (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
  (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
  (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (m : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H m k ω s| ≤ C)

include hC0 hCH in
/-- **The second-order Taylor remainder of a vector Itô process along a uniform grid is
`O(m^{-1/2})` in `L¹`.** -/
theorem integral_abs_vectorTaylorRemainder_le (X₀ : Ω → Fin n → ℝ)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (bdrift : Fin n → Ω → ℝ → ℝ) (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    {B : ℝ} (hB0 : 0 ≤ B) (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ} {K : ℝ} (hK0 : 0 ≤ K)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hf'' : ∀ z w, ‖f'' z - f'' w‖ ≤ K * ‖z - w‖)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) :
    Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P
      ∧ ∫ ω, |taylorRemainderNormed f f' f''
          (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
        ≤ K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
          + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
            * (T * Real.sqrt (T / (m : ℝ))))))))) := by
  have hX : ∀ i : ℕ,
      Measurable (vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i)) :=
    fun i => measurable_vectorItoProcess W ℱ hcoord H hHm hHp hHs hX₀ hbm _
  have hfd : Differentiable ℝ f := fun z => (hf z).differentiableAt
  have hf'd : Differentiable ℝ f' := fun z => (hf' z).differentiableAt
  have hf''c : Continuous f'' := by
    have hlip : LipschitzWith (Real.toNNReal K) f'' := by
      refine LipschitzWith.of_dist_le_mul fun u v => ?_
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal K hK0]
      exact hf'' u v
    exact hlip.continuous
  have hR := measurable_taylorRemainderNormed hfd.continuous hf'd.continuous hf''c hX m
  have hptw : ∀ ω : Ω, |taylorRemainderNormed f f' f''
      (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m|
      ≤ K * ∑ i ∈ Finset.range m,
        ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
          - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3 :=
    fun ω => abs_taylorRemainderNormed_le hK0 hf hf' hf'' _ m
  have hterm : ∀ i ∈ Finset.range m, Integrable (fun ω : Ω =>
      ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3) P :=
    fun i _ => integrable_norm_vectorItoProcess_sub_pow_three W ℱ hcoord H hHm hHp hHs hC0 hCH
      X₀ bdrift hbm hB0 hB (unifGrid_nonneg hT.le m i) (unifGrid_lt_succ hT hm0 i)
  have hsumint : Integrable (fun ω : Ω => K * ∑ i ∈ Finset.range m,
      ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
        - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3) P :=
    (MeasureTheory.integrable_finsetSum _ hterm).const_mul K
  have hRint : Integrable (fun ω : Ω => |taylorRemainderNormed f f' f''
      (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m|) P := by
    refine hsumint.mono hR.abs.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_abs]
    exact (hptw ω).trans (le_abs_self _)
  have hRint0 : Integrable (fun ω : Ω => taylorRemainderNormed f f' f''
      (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m) P := by
    refine hsumint.mono hR.aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact (hptw ω).trans (le_abs_self _)
  refine ⟨hRint0, ?_⟩
  calc ∫ ω, |taylorRemainderNormed f f' f''
        (fun i => vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω) m| ∂P
      ≤ ∫ ω, K * ∑ i ∈ Finset.range m,
          ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
            - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3 ∂P :=
        MeasureTheory.integral_mono hRint hsumint hptw
    _ = K * ∑ i ∈ Finset.range m, ∫ ω,
          ‖vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m (i + 1)) ω
            - vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift (unifGrid T m i) ω‖ ^ 3 ∂P := by
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ hterm]
    _ ≤ K * ((n : ℝ) ^ 2 * ((n : ℝ) * (4 * ((m : ℝ) * (B * (T / (m : ℝ))) ^ 3
        + (d : ℝ) ^ 2 * ((d : ℝ) * ((C ^ 2 + (6 + gaussianFourthMoment) * C ^ 4) / 2
          * (T * Real.sqrt (T / (m : ℝ))))))))) :=
        mul_le_mul_of_nonneg_left (sum_integral_norm_vectorItoIncrement_pow_three_le W ℱ hcoord
          H hHm hHp hHs hC0 hCH X₀ bdrift hbm hB0 hB hT hm0) hK0

end VectorTaylor

end LevyStochCalc.Brownian.Ito
