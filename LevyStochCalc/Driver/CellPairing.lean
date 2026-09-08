/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CellIntegrand
import LevyStochCalc.Poisson.CompensatedPullOut
import LevyStochCalc.Brownian.PRPPairing

/-!
# Pairing the jump term of the product rule

A weight orthogonal to every compensated integral over the horizon does not see the compensated
half of a window integral against the random measure: pairing it, times a bounded weight
measurable before the window, with the integral of a continuous adapted factor against the
random measure leaves only the integral against the reference intensity.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section JumpTerm

omit [IsProbabilityMeasure P] in
/-- The product of an `L²` function with a bounded one is integrable. -/
theorem integrable_mul_bdd_mul {Z V F : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hF2 : MemLp F 2 P)
    (hVm : Measurable V) {M : ℝ} (hVb : ∀ ω, |V ω| ≤ M) :
    Integrable (fun ω => Z ω * V ω * F ω) P := by
  have hZF : Integrable (fun ω => Z ω * F ω) P := integrable_mul_of_memLp_two hZ2 hF2
  have hVnorm : ∀ᵐ ω ∂P, ‖V ω‖ ≤ M :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hVb ω
  exact (hZF.bdd_mul hVm.aestronglyMeasurable hVnorm).congr
    (Filter.Eventually.of_forall fun ω => by ring)

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ) {T : ℝ}

/-- **The compensated half of the jump term pairs to zero.** For a weight orthogonal to every
compensated integral over the horizon, a bounded weight measurable before the window, and a
predictable admissible integrand vanishing up to `a`, the pairing with the window integral of a
bounded continuous adapted factor against the random measure is the pairing with its integral
against the reference intensity. -/
theorem integral_mul_setIntegral_count (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hperp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G.integral N hℱ ω ∂P = 0)
    {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V)
    {Mv : ℝ} (hVb : ∀ ω, |V ω| ≤ Mv)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {X : ℝ → Ω → ℝ} (hXc : ∀ ω, Continuous fun t => X t ω)
    (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t)) {C : ℝ} (hC0 : 0 ≤ C)
    (hXb : ∀ s ω, |X s ω| ≤ C) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {τ : ℝ} (hτT : τ ≤ T) :
    ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
        X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) ∂P
      = ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
          X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  classical
  have hVm : Measurable V := hVa.measurable.mono (ℱ.le a) le_rfl
  set F := G.cutMul hXc hXa hC0 hXb hA hAν hGpred τ with hFdef
  have hFa : ∀ ω s e, s ≤ a → F.toFun ω s e = 0 := by
    intro ω s e hs
    change cutWindow X A τ ω s e * G.toFun ω s e = 0
    rw [hGa ω s e hs, mul_zero]
  -- the compensated half pairs to zero
  have hzero : ∫ ω, Z ω * V ω * F.integral N hℱ ω ∂P = 0 := by
    have hpull := MarkedHorizonIntegrand.integral_mulLeft N hℱ hT F ha haT hFa hVa hVb
    have hcongr : ∫ ω, Z ω * ((F.mulLeft hFa hVa hVb).integral N hℱ ω) ∂P
        = ∫ ω, Z ω * V ω * F.integral N hℱ ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hpull] with ω hω
      rw [hω, mul_assoc]
    rw [← hcongr]
    exact hperp _
  -- the pathwise split of the window integral
  have hsplit := MarkedHorizonIntegrand.setIntegral_count_eq_integral_add N hℱ G hXc hXa hC0
    hXb hA hAν hGpred hT hτT
  have hFint : MemLp (F.integral N hℱ) 2 P := MarkedHorizonIntegrand.memLp N hℱ F
  have hIint : Integrable (fun ω => Z ω * V ω * F.integral N hℱ ω) P :=
    integrable_mul_bdd_mul hZ2 hFint hVm hVb
  -- the compensator half is a bounded measurable function of the sample point
  have hXjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => X s ω) := by
    have h : Measurable (Function.uncurry fun (t : ℝ) (ω : Ω) => X t ω) :=
      measurable_uncurry_of_continuous_of_measurable (fun ω => hXc ω)
        (fun t => ((hXa t).mono (ℱ.le t)).measurable)
    exact h.comp measurable_swap
  have hjoint : Measurable fun p : Ω × (ℝ × E) => X p.2.1 p.1 * G.toFun p.1 p.2.1 p.2.2 :=
    (hXjoint.comp (measurable_fst.prodMk measurable_snd.fst)).mul G.measurable_uncurry
  have hWfin : referenceIntensity ν (Set.Ioc (0 : ℝ) τ ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAν τ
  haveI : IsFiniteMeasure ((referenceIntensity ν).restrict (Set.Ioc (0 : ℝ) τ ×ˢ A)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hWfin⟩
  have hDm : StronglyMeasurable fun ω => ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
      X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν) :=
    hjoint.stronglyMeasurable.integral_prod_right'
  have hDb : ∀ ω, ‖∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
      X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)‖
      ≤ (C * Cg) * ((referenceIntensity ν) (Set.Ioc (0 : ℝ) τ ×ˢ A)).toReal := by
    intro ω
    refine norm_setIntegral_le_of_norm_le_const ?_ fun q _ => ?_
    · exact lt_top_iff_ne_top.mpr hWfin
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hXb q.1 ω) (hGb ω q.1 q.2) (abs_nonneg _) hC0
  have hDint : Integrable (fun ω => Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
      X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) P := by
    refine integrable_mul_bdd_mul hZ2 ?_ hVm hVb
    exact MemLp.of_bound hDm.aestronglyMeasurable _
      (Filter.Eventually.of_forall hDb)
  -- assemble
  have hLHS : ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
        X q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) ∂P
      = ∫ ω, (Z ω * V ω * F.integral N hℱ ω
          + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) τ ×ˢ A,
              X q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hsplit] with ω hω
    rw [hω]
    ring
  rw [hLHS, integral_add hIint hDint, hzero, zero_add]

end JumpTerm

section BrownianTerm

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

include hℱW in
/-- **The `dW` term pairs to zero.** A real weight orthogonal to every Itô integral, times a
bounded weight measurable before the window, is orthogonal to the Itô integral of any bounded
progressive integrand supported in the window. -/
theorem integral_mul_stochasticIntegralBrownian_eq_zero {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZp : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    {V : Ω → ℝ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, |V ω| ≤ Mv)
    (hVa : StronglyMeasurable[ℱ a] V)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, Z ω * V ω * stochasticIntegralBrownian W ℱ hℱW
      (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω ∂P = 0 := by
  have hZc : MemLp (fun ω => ((Z ω : ℝ) : ℂ)) 2 P := memLp_ofReal hZ2
  have hVc : Measurable fun ω => ((V ω : ℝ) : ℂ) := Complex.measurable_ofReal.comp hVm
  have hVcb : ∀ ω, ‖((V ω : ℝ) : ℂ)‖ ≤ Mv := fun ω => by
    rw [Complex.norm_real, Real.norm_eq_abs]; exact hVb ω
  have hVca : StronglyMeasurable[ℱ a] fun ω => ((V ω : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp_stronglyMeasurable hVa
  have hc := pairing_ito_eq_zero ha hab hZc hZp hVc hMv0 hVcb hVca hKm hKp hKb0 hKbd hmg hpg
    hqg ht
  set f : Ω → ℝ := fun ω => Z ω * V ω * stochasticIntegralBrownian W ℱ hℱW
    (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω with hf
  have hcast : ∀ ω : Ω, ((Z ω : ℝ) : ℂ) * ((V ω : ℝ) : ℂ) * ((stochasticIntegralBrownian W ℱ hℱW
        (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
      = ((f ω : ℝ) : ℂ) := by
    intro ω
    rw [hf]
    push_cast
    ring
  simp_rw [hcast] at hc
  have hre : ∫ ω, ((f ω : ℝ) : ℂ) ∂P = ((∫ ω, f ω ∂P : ℝ) : ℂ) := integral_ofReal
  rw [hre] at hc
  exact_mod_cast hc

end BrownianTerm


section Assembly

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)

include hℱN hℱW in
/-- **The pairing of the product rule.** Pairing the product rule of a bounded continuous
adapted factor with a bounded pure-jump process against a weight orthogonal to every Itô
integral and every compensated integral, times a bounded weight measurable before the window,
leaves the drift term and the compensator of the jump term. -/
theorem pairing_of_product_rule {T : ℝ} (hT : 0 < T) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (haT : a ≤ T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {Xg : ℝ → Ω → ℝ} (hXc : ∀ ω, Continuous fun t => Xg t ω)
    (hXa : ∀ t : ℝ, StronglyMeasurable[ℱ t] (Xg t)) {C : ℝ} (hC0 : 0 ≤ C)
    (hXb : ∀ s ω, |Xg s ω| ≤ C)
    {Y Yminus : ℝ → Ω → ℝ} (hYm : ∀ s, Measurable (Y s)) (hYb : ∀ s ω, |Y s ω| ≤ 1)
    (hYmm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Yminus s ω))
    (hYmb : ∀ s ω, |Yminus s ω| ≤ 1)
    {bdrift : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry bdrift)) {B : ℝ}
    (hBb : ∀ ω s, |bdrift ω s| ≤ B)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T)
    (hid : ∀ᵐ ω ∂P, Xg t ω * Y t ω - Xg 0 ω * Y 0 ω
      = stochasticIntegralBrownian W ℱ hℱW
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω
        + (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) :
    ∫ ω, Z ω * V ω * (Xg t ω * Y t ω) ∂P
      = ∫ ω, Z ω * V ω * (Xg 0 ω * Y 0 ω) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            Yminus s ω * bdrift ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            Xg q.1 ω * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  classical
  have hVm : Measurable V := hVa.measurable.mono (ℱ.le a) le_rfl
  -- the four bounded or square-integrable pieces
  have hSIBint : Integrable (fun ω => Z ω * V ω * stochasticIntegralBrownian W ℱ hℱW
      (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω) P :=
    integrable_mul_bdd_mul hZ2 (stochasticIntegralBrownian_memLp W ℱ hℱW _ hmg hpg hqg t) hVm hVb
  have hDm : StronglyMeasurable fun ω => ∫ s in Set.Ioc (0 : ℝ) t,
      Yminus s ω * bdrift ω s ∂volume :=
    (hYmm.mul hbm).stronglyMeasurable.integral_prod_right'
  have hDb : ∀ ω, ‖∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume‖
      ≤ B * (volume (Set.Ioc (0 : ℝ) t)).toReal := by
    intro ω
    refine norm_setIntegral_le_of_norm_le_const ?_ fun s _ => ?_
    · rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top
    · rw [Real.norm_eq_abs, abs_mul]
      calc |Yminus s ω| * |bdrift ω s| ≤ 1 * B :=
            mul_le_mul (hYmb s ω) (hBb ω s) (abs_nonneg _) zero_le_one
        _ = B := one_mul B
  have hDint : Integrable (fun ω => Z ω * V ω * ∫ s in Set.Ioc (0 : ℝ) t,
      Yminus s ω * bdrift ω s ∂volume) P :=
    integrable_mul_bdd_mul hZ2 (MemLp.of_bound hDm.aestronglyMeasurable _
      (Filter.Eventually.of_forall hDb)) hVm hVb
  have hprod : ∀ r : ℝ, Integrable (fun ω => Z ω * V ω * (Xg r ω * Y r ω)) P := by
    intro r
    refine integrable_mul_bdd_mul hZ2 (MemLp.of_bound ?_ C ?_) hVm hVb
    · exact ((((hXa r).mono (ℱ.le r)).measurable.mul (hYm r))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      rw [Real.norm_eq_abs, abs_mul]
      calc |Xg r ω| * |Y r ω| ≤ C * 1 := mul_le_mul (hXb r ω) (hYb r ω) (abs_nonneg _) hC0
        _ = C := mul_one C
  have hjumpint : Integrable (fun ω => Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
      Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) P := by
    refine Integrable.congr (((hprod t).sub (hprod 0)).sub (hSIBint.add hDint)) ?_
    filter_upwards [hid] with ω hω
    simp only [Pi.sub_apply, Pi.add_apply]
    linear_combination (Z ω * V ω) * hω
  -- the two pairings that vanish or convert
  have hSIBzero := integral_mul_stochasticIntegralBrownian_eq_zero W hℱW ha hab hZ2 hZito hVm
    hMv0 hVb hVa hKm hKp hKb0 hKbd hmg hpg hqg ht
  have hjumpeq := integral_mul_setIntegral_count N hℱN hT hZ2 hZcomp ha haT hVa hVb G hGpred
    hGa hGb hXc hXa hC0 hXb hA hAν htT
  -- assemble
  have hstep : ∫ ω, Z ω * V ω * (Xg t ω * Y t ω) ∂P
      = ∫ ω, (Z ω * V ω * (Xg 0 ω * Y 0 ω)
          + (Z ω * V ω * stochasticIntegralBrownian W ℱ hℱW
              (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω
            + (Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
              + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
                  Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)))) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hid] with ω hω
    linear_combination (Z ω * V ω) * hω
  have h34 : Integrable (fun ω => Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
        Yminus s ω * bdrift ω s ∂volume)
      + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω)) P := hDint.add hjumpint
  have h234 : Integrable (fun ω => Z ω * V ω * stochasticIntegralBrownian W ℱ hℱW
        (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω
      + (Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t, Yminus s ω * bdrift ω s ∂volume)
        + Z ω * V ω * ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            Xg q.1 ω * G.toFun ω q.1 q.2 ∂(N.N ω))) P := hSIBint.add h34
  rw [hstep, integral_add (hprod 0) h234, integral_add hSIBint h34,
    integral_add hDint hjumpint, hSIBzero, hjumpeq]
  ring

end Assembly

end LevyStochCalc.Driver
