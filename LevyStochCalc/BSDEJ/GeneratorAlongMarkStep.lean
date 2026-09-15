/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.BSDEJ.Existence
import LevyStochCalc.Poisson.MarkStep
import LevyStochCalc.Probability.Progressive

/-!
# The generator of a BSDEJ along a mark-step jump integrand

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable
depends on a finite combination `∑ₖ cₖ 1_{Bₖ}` of mark sets of finite measure only through the
coefficient vector `c`, continuously, so `(p, c) ↦ f p.1 p.2.1 p.2.2 (∑ₖ cₖ 1_{Bₖ})` is jointly
measurable.

A mark-step integrand `G` is such a combination at every `(ω, s)`, with coefficient vector
`markStepCoeff G ω s`; consequently the composite process
`(ω, s) ↦ f s (Y s ω) (Z s ω) (fun e => G.eval s e ω)` is jointly measurable, and progressively
measurable for a filtration to which `Y`, `Z` and the coefficients of `G` are adapted.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {d : ℕ}

/-! ### Finite combinations of mark sets -/

/-- The `L²(ν)` norm of a finite combination `∑ₖ cₖ 1_{Bₖ}` of mark sets is at most
`∑ₖ ‖cₖ‖ ν(Bₖ)^{1/2}`. -/
theorem lintegral_sq_finsetCombination_le {K : ℕ} {B : Fin K → Set E}
    (hB : ∀ k, MeasurableSet (B k)) (c : Fin K → ℝ) :
    (∫⁻ e, (‖∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)
      ≤ ∑ k, (‖c k‖₊ : ℝ≥0∞) * ν (B k) ^ (1 / 2 : ℝ) := by
  have hfun : (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
      = ∑ k, ((B k).indicator (fun _ => c k)) := by
    funext e
    rw [Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : e ∈ B k <;> simp [h]
  have hsq : (∫⁻ e, (‖∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      = eLpNorm (∑ k, ((B k).indicator (fun _ => c k))) 2 ν ^ 2 := by
    rw [LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral ν
      (∑ k, ((B k).indicator (fun _ => c k)))]
    exact congrArg (fun F : E → ℝ => ∫⁻ e, (‖F e‖₊ : ℝ≥0∞) ^ 2 ∂ν) hfun
  rw [hsq, ← ENNReal.rpow_natCast (eLpNorm (∑ k, ((B k).indicator (fun _ => c k))) 2 ν) 2,
    ← ENNReal.rpow_mul]
  norm_num
  refine (eLpNorm_sum_le (fun k _ =>
    ((measurable_const.indicator (hB k)).aestronglyMeasurable)) (by norm_num)).trans ?_
  refine Finset.sum_le_sum fun k _ => ?_
  rw [eLpNorm_indicator_const (hB k) (by norm_num) (by norm_num)]
  norm_num [enorm_eq_nnnorm]

/-- A Lipschitz generator is continuous in the coefficient vector of a finite combination of
mark sets of finite measure. -/
theorem continuous_generator_finsetCombination {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {K : ℕ} {B : Fin K → Set E} (hB : ∀ k, MeasurableSet (B k)) (hBν : ∀ k, ν (B k) ≠ ⊤)
    (s y : ℝ) (z : Fin d → ℝ) :
    Continuous fun c : Fin K → ℝ =>
      f s y z (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e) := by
  have hCν : (∑ k, ν (B k) ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun k _ => ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hBν k)
  have hfin : ENNReal.ofReal L * (∑ k, ν (B k) ^ (1 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hCν
  refine LipschitzWith.continuous
    (K := (ENNReal.ofReal L * (∑ k, ν (B k) ^ (1 / 2 : ℝ))).toNNReal) ?_
  intro c c'
  rw [ENNReal.coe_toNNReal hfin, edist_eq_enorm_sub, enorm_eq_nnnorm]
  have hsub : ∀ e : E, (∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
      - (∑ k, c' k * (B k).indicator (fun _ => (1 : ℝ)) e)
      = ∑ k, (c k - c' k) * (B k).indicator (fun _ => (1 : ℝ)) e := by
    intro e
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => (sub_mul _ _ _).symm
  have key := hlip s y y z z (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
    (fun e => ∑ k, c' k * (B k).indicator (fun _ => (1 : ℝ)) e)
  simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, zero_add] at key
  refine key.trans ?_
  have hrw : (∫⁻ e, (‖(∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)
        - (∑ k, c' k * (B k).indicator (fun _ => (1 : ℝ)) e)‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      = ∫⁻ e, (‖∑ k, (c k - c' k) * (B k).indicator (fun _ => (1 : ℝ)) e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    lintegral_congr fun e => by rw [hsub e]
  rw [hrw]
  refine (mul_le_mul_right (lintegral_sq_finsetCombination_le hB fun k => c k - c' k) _).trans ?_
  have hb : ∀ k : Fin K, (‖c k - c' k‖₊ : ℝ≥0∞) * ν (B k) ^ (1 / 2 : ℝ)
      ≤ edist c c' * ν (B k) ^ (1 / 2 : ℝ) := by
    intro k
    refine mul_le_mul_left ?_ _
    calc (‖c k - c' k‖₊ : ℝ≥0∞) = edist (c k) (c' k) := by
          rw [edist_eq_enorm_sub, enorm_eq_nnnorm]
      _ ≤ edist c c' := edist_le_pi_edist c c' k
  refine (mul_le_mul_right (Finset.sum_le_sum fun k _ => hb k) _).trans ?_
  rw [← Finset.mul_sum]
  exact le_of_eq (by ring)

/-- A generator measurable in `(s, y, z)` for each jump variable and Lipschitz in `(y, z, u)` is
jointly measurable in `(s, y, z)` and in the coefficient vector of a finite combination of mark
sets of finite measure. -/
theorem measurable_generator_finsetCombination {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {K : ℕ} {B : Fin K → Set E} (hB : ∀ k, MeasurableSet (B k)) (hBν : ∀ k, ν (B k) ≠ ⊤) :
    Measurable fun q : (ℝ × ℝ × (Fin d → ℝ)) × (Fin K → ℝ) =>
      f q.1.1 q.1.2.1 q.1.2.2 (fun e => ∑ k, q.2 k * (B k).indicator (fun _ => (1 : ℝ)) e) := by
  have hu : Measurable (Function.uncurry fun (c : Fin K → ℝ) (p : ℝ × ℝ × (Fin d → ℝ)) =>
      f p.1 p.2.1 p.2.2 (fun e => ∑ k, c k * (B k).indicator (fun _ => (1 : ℝ)) e)) :=
    measurable_uncurry_of_continuous_of_measurable
      (fun p => continuous_generator_finsetCombination hlip hB hBν p.1 p.2.1 p.2.2)
      (fun c => hf _)
  exact hu.comp measurable_swap

/-! ### The generator along a mark-step integrand -/

section MarkStep

variable [SigmaFinite ν] {g : TimeGrid}

/-- The coefficient vector of a mark-step integrand at a sample point and a time: the mark set
`Bₖ` carries the weight `∑ᵢ 1_{(pᵢ, pᵢ₊₁]}(s) ξᵢₖ(ω)`. -/
noncomputable def markStepCoeff (G : MarkStep Ω E ν g) (ω : Ω) (s : ℝ) : Fin G.K → ℝ :=
  fun k => ∑ i ∈ Finset.range g.N₀,
    (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s * G.ξ i k ω

/-- The coefficient vector of a mark-step integrand is jointly measurable in sample point and
time. -/
lemma measurable_markStepCoeff (G : MarkStep Ω E ν g) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => markStepCoeff G ω s) := by
  have hrw : (Function.uncurry fun (ω : Ω) (s : ℝ) => markStepCoeff G ω s)
      = fun p : Ω × ℝ => fun k => ∑ i ∈ Finset.range g.N₀,
        (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) p.2 * G.ξ i k p.1 := rfl
  rw [hrw]
  refine measurable_pi_iff.2 fun k => Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_const.indicator measurableSet_Ioc).comp measurable_snd).mul
    ((G.ξ_measurable i k).comp measurable_fst)

/-- A mark-step integrand is, at each sample point and time, the finite combination of its mark
sets with coefficient vector `markStepCoeff`. -/
lemma eval_eq_finsetCombination (G : MarkStep Ω E ν g) (s : ℝ) (e : E) (ω : Ω) :
    G.eval s e ω = ∑ k, markStepCoeff G ω s k * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
  simp only [MarkStep.eval, markStepCoeff, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => by ring

/-- The generator evaluated along a mark-step integrand is jointly measurable in sample point
and time. -/
theorem measurable_generator_along_markStep {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (G : MarkStep Ω E ν g) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    (hYm : Measurable (Function.uncurry Y))
    (hZm : ∀ i, Measurable (Function.uncurry fun ω s => Z s ω i)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      f s (Y s ω) (Z s ω) (fun e => G.eval s e ω)) := by
  have hrw : (Function.uncurry fun (ω : Ω) (s : ℝ) =>
        f s (Y s ω) (Z s ω) (fun e => G.eval s e ω))
      = fun p : Ω × ℝ => f p.2 (Y p.2 p.1) (Z p.2 p.1) (fun e =>
        ∑ k, markStepCoeff G p.1 p.2 k * (G.B k).indicator (fun _ => (1 : ℝ)) e) := by
    funext p
    exact congrArg (f p.2 (Y p.2 p.1) (Z p.2 p.1))
      (funext fun e => eval_eq_finsetCombination G p.2 e p.1)
  rw [hrw]
  have hmap : Measurable fun p : Ω × ℝ =>
      (((p.2, Y p.2 p.1, Z p.2 p.1) : ℝ × ℝ × (Fin d → ℝ)), markStepCoeff G p.1 p.2) :=
    (measurable_snd.prodMk ((hYm.comp (measurable_snd.prodMk measurable_fst)).prodMk
      (measurable_pi_iff.2 fun i => hZm i))).prodMk (measurable_markStepCoeff G)
  exact (measurable_generator_finsetCombination hf hlip G.B_measurable G.B_finite).comp hmap

/-- The generator evaluated along an adapted mark-step integrand and progressively measurable
processes `Y`, `Z` is progressively measurable. -/
theorem progressive_generator_along_markStep {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ}
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {ℱ : Filtration ℝ mΩ} (G : MarkStep Ω E ν g) (hG : G.Adapted ℱ) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)}
    (hYp : Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω)
    (hZp : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i) :
    Probability.ProgressivelyMeasurable ℱ
      fun ω s => f s (Y s ω) (Z s ω) (fun e => G.eval s e ω) := by
  intro t
  obtain ⟨K, B, ξ, c, hBm, hBf, hξ, hcform, hev⟩ :
      ∃ (K : ℕ) (B : Fin K → Set E) (ξ : ℕ → Fin K → Ω → ℝ) (c : Ω → ℝ → Fin K → ℝ),
        (∀ k, MeasurableSet (B k)) ∧ (∀ k, ν (B k) ≠ ⊤) ∧
          (∀ i, i < g.N₀ → ∀ k, StronglyMeasurable[ℱ (g.p i)] (ξ i k)) ∧
          (∀ ω s k, c ω s k = ∑ i ∈ Finset.range g.N₀,
            (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s * ξ i k ω) ∧
          ∀ s e ω, G.eval s e ω = ∑ k, c ω s k * (B k).indicator (fun _ => (1 : ℝ)) e :=
    ⟨G.K, G.B, G.ξ, markStepCoeff G, G.B_measurable, G.B_finite, hG, fun _ _ _ => rfl,
      eval_eq_finsetCombination G⟩
  simp only [hev]
  letI : MeasurableSpace Ω := ℱ t
  have hY : Measurable fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => Y s p.1) p.2 :=
    (hYp t).measurable
  have hZ : ∀ i, Measurable fun p : Ω × ℝ =>
      (Set.Iic t).indicator (fun s => Z s p.1 i) p.2 := fun i => (hZp i t).measurable
  have hc : ∀ k, Measurable fun p : Ω × ℝ =>
      (Set.Iic t).indicator (fun s => c p.1 s k) p.2 := by
    intro k
    have hEq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => c p.1 s k) p.2)
        = fun p : Ω × ℝ => ∑ i ∈ Finset.range g.N₀,
          (Set.Iic t ∩ Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) p.2
            * ξ i k p.1 := by
      funext p
      by_cases hp : p.2 ∈ Set.Iic t
      · rw [Set.indicator_of_mem hp, hcform]
        refine Finset.sum_congr rfl fun i _ => ?_
        by_cases hi : p.2 ∈ Set.Ioc (g.p i) (g.p (i + 1))
        · rw [Set.indicator_of_mem hi, Set.indicator_of_mem (Set.mem_inter hp hi)]
        · rw [Set.indicator_of_notMem hi,
            Set.indicator_of_notMem (fun h => hi (Set.mem_of_mem_inter_right h))]
      · rw [Set.indicator_of_notMem hp]
        exact (Finset.sum_eq_zero fun i _ => by
          rw [Set.indicator_of_notMem (fun h => hp (Set.mem_of_mem_inter_left h)), zero_mul]).symm
    rw [hEq]
    refine Finset.measurable_sum _ fun i hi => ?_
    by_cases hti : g.p i ≤ t
    · have hm : Measurable[ℱ t] (ξ i k) :=
        ((hξ i (Finset.mem_range.1 hi) k).mono (ℱ.mono hti)).measurable
      exact ((measurable_const.indicator
        (measurableSet_Iic.inter measurableSet_Ioc)).comp measurable_snd).mul
        (hm.comp measurable_fst)
    · have hzero : (fun p : Ω × ℝ =>
          (Set.Iic t ∩ Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) p.2
            * ξ i k p.1) = fun _ => 0 := by
        funext p
        rw [Set.indicator_of_notMem, zero_mul]
        rintro ⟨h1, h2⟩
        exact hti (h2.1.le.trans h1)
      rw [hzero]
      exact measurable_const
  have hmain : Measurable fun p : Ω × ℝ =>
      f p.2 ((Set.Iic t).indicator (fun s => Y s p.1) p.2)
        (fun i => (Set.Iic t).indicator (fun s => Z s p.1 i) p.2)
        (fun e => ∑ k, (Set.Iic t).indicator (fun s => c p.1 s k) p.2
          * (B k).indicator (fun _ => (1 : ℝ)) e) :=
    (measurable_generator_finsetCombination hf hlip hBm hBf).comp
      ((measurable_snd.prodMk (hY.prodMk (measurable_pi_iff.2 hZ))).prodMk
        (measurable_pi_iff.2 hc))
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => f s (Y s p.1) (Z s p.1)
          (fun e => ∑ k, c p.1 s k * (B k).indicator (fun _ => (1 : ℝ)) e)) p.2)
      = {p : Ω × ℝ | p.2 ∈ Set.Iic t}.indicator (fun p : Ω × ℝ =>
        f p.2 ((Set.Iic t).indicator (fun s => Y s p.1) p.2)
          (fun i => (Set.Iic t).indicator (fun s => Z s p.1 i) p.2)
          (fun e => ∑ k, (Set.Iic t).indicator (fun s => c p.1 s k) p.2
            * (B k).indicator (fun _ => (1 : ℝ)) e)) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp,
        Set.indicator_of_mem (show p ∈ {q : Ω × ℝ | q.2 ∈ Set.Iic t} from hp)]
      simp only [Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem
        (show p ∉ {q : Ω × ℝ | q.2 ∈ Set.Iic t} from hp)]
  have final : StronglyMeasurable fun p : Ω × ℝ => (Set.Iic t).indicator
      (fun s => f s (Y s p.1) (Z s p.1)
        (fun e => ∑ k, c p.1 s k * (B k).indicator (fun _ => (1 : ℝ)) e)) p.2 := by
    rw [heq]
    exact (stronglyMeasurable_iff_measurable.2 hmain).indicator (measurable_snd measurableSet_Iic)
  exact final

end MarkStep

end LevyStochCalc.BSDEJ.Generator
