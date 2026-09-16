/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Driver.CrossOrthogonality
import LevyStochCalc.Ito.ItoLevyProcess
import LevyStochCalc.Brownian.CrossOrthogonality
import LevyStochCalc.Ito.PicardOutput
import LevyStochCalc.Brownian.ItoQuadVarSum

/-!
# Auxiliary lemmas for the second moment of an Itô–Lévy process

The `L²` lemmas behind the expectation form of the quadratic Itô formula: the second moment of a
square-integrable variable as the real part of its energy, the expansion of the square of a sum,
the evaluation of a square-integrable martingale paired against a variable measurable at an
earlier time, and the exchange of a time integral with a pairing. The running integral
`∫_0^s b_r dr` of a drift over a window `[0, T]` is introduced as a jointly measurable function of
the sample point and the time, together with the pathwise identities
`(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds` and, for two integrable functions,
`(∫_0^T b)(∫_0^T b') = ∫_0^T ((∫_0^s b) b'_s + b_s (∫_0^s b')) ds`; and the polarised isometry for
the Brownian integral, the expected product of two Brownian integrals at a time being the expected
time integral of the product of their integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Toolkit

omit [IsProbabilityMeasure P] in
/-- The integral of the square of a square-integrable function is the real part of its
energy. -/
theorem integral_mul_self_eq_toReal {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫ ω, f ω * f ω ∂P = (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => mul_self_nonneg _)
    (hf.aestronglyMeasurable.mul hf.aestronglyMeasurable)]
  congr 1
  refine lintegral_congr fun ω => ?_
  rw [← sq, show ((‖f ω‖₊ : ℝ≥0∞)) = ‖f ω‖ₑ from rfl, Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

omit [IsProbabilityMeasure P] in
/-- The energy of a square-integrable function is finite. -/
theorem lintegral_sq_lt_top_of_memLp_two {f : Ω → ℝ} (hf : MemLp f 2 P) :
    ∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  have h := (hf.integrable_mul hf).hasFiniteIntegral
  rw [hasFiniteIntegral_iff_enorm] at h
  refine lt_of_eq_of_lt ?_ h
  refine lintegral_congr fun ω => ?_
  rw [Pi.mul_apply, enorm_mul, sq]
  rfl

omit [IsProbabilityMeasure P] in
/-- The square of a sum of two square-integrable functions, under the integral. -/
theorem integral_mul_self_add {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    ∫ ω, (f ω + g ω) * (f ω + g ω) ∂P
      = ∫ ω, f ω * f ω ∂P + 2 * ∫ ω, f ω * g ω ∂P + ∫ ω, g ω * g ω ∂P := by
  have hff : Integrable (fun ω => f ω * f ω) P := hf.integrable_mul hf
  have hfg : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have hgg : Integrable (fun ω => g ω * g ω) P := hg.integrable_mul hg
  have hexp : (fun ω => (f ω + g ω) * (f ω + g ω))
      = fun ω => f ω * f ω + (2 : ℝ) * (f ω * g ω) + g ω * g ω := by
    funext ω
    ring
  have h2 : Integrable (fun ω => (2 : ℝ) * (f ω * g ω)) P := hfg.const_mul 2
  have h12 : Integrable (fun ω => f ω * f ω + (2 : ℝ) * (f ω * g ω)) P := hff.add h2
  rw [hexp, integral_add h12 hgg, integral_add hff h2, integral_const_mul]

omit [IsProbabilityMeasure P] in
/-- The product of two sums of square-integrable functions, under the integral. -/
theorem integral_add_mul_add {a b c d : Ω → ℝ} (ha : MemLp a 2 P) (hb : MemLp b 2 P)
    (hc : MemLp c 2 P) (hd : MemLp d 2 P) :
    ∫ ω, (a ω + b ω) * (c ω + d ω) ∂P
      = ∫ ω, a ω * c ω ∂P + ∫ ω, a ω * d ω ∂P + ∫ ω, b ω * c ω ∂P + ∫ ω, b ω * d ω ∂P := by
  have hac : Integrable (fun ω => a ω * c ω) P := ha.integrable_mul hc
  have had : Integrable (fun ω => a ω * d ω) P := ha.integrable_mul hd
  have hbc : Integrable (fun ω => b ω * c ω) P := hb.integrable_mul hc
  have hbd : Integrable (fun ω => b ω * d ω) P := hb.integrable_mul hd
  have hexp : (fun ω => (a ω + b ω) * (c ω + d ω))
      = fun ω => a ω * c ω + a ω * d ω + b ω * c ω + b ω * d ω := by
    funext ω
    ring
  have h12 : Integrable (fun ω => a ω * c ω + a ω * d ω) P := hac.add had
  have h123 : Integrable (fun ω => a ω * c ω + a ω * d ω + b ω * c ω) P := h12.add hbc
  rw [hexp, integral_add h123 hbd, integral_add h12 hbc, integral_add hac had]

/-- Pairing a square-integrable martingale at a later time against a square-integrable variable
measurable at an earlier time reads the martingale at the earlier time. -/
theorem integral_mul_martingale_eq {𝒢 : Filtration ℝ ‹MeasurableSpace Ω›} {M : ℝ → Ω → ℝ}
    (hM : Martingale M 𝒢 P) {a t : ℝ} (hat : a ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝒢 a] Z) (hZ2 : MemLp Z 2 P) (hMt : MemLp (M t) 2 P) :
    ∫ ω, Z ω * M t ω ∂P = ∫ ω, Z ω * M a ω ∂P := by
  haveI : SigmaFinite (P.trim (𝒢.le a)) := (isFiniteMeasure_trim (𝒢.le a)).toSigmaFinite
  have hZt : Integrable (fun ω => Z ω * M t ω) P := hZ2.integrable_mul hMt
  have hMtInt : Integrable (M t) P := hMt.integrable one_le_two
  have hce : P[(fun ω => Z ω * M t ω) | 𝒢 a] =ᵐ[P] fun ω => Z ω * (P[M t | 𝒢 a]) ω :=
    condExp_mul_of_stronglyMeasurable_left hZ hZt hMtInt
  have hma : P[M t | 𝒢 a] =ᵐ[P] M a := hM.condExp_ae_eq hat
  rw [← integral_condExp (𝒢.le a)]
  refine integral_congr_ae (hce.trans ?_)
  filter_upwards [hma] with ω hω
  rw [hω]

/-- A square-integrable martingale vanishing at an earlier time is orthogonal to every
square-integrable variable measurable at that time. -/
theorem integral_mul_martingale_eq_zero {𝒢 : Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ} (hM : Martingale M 𝒢 P) {a t : ℝ} (hat : a ≤ t) {Z : Ω → ℝ}
    (hZ : StronglyMeasurable[𝒢 a] Z) (hZ2 : MemLp Z 2 P) (hMt : MemLp (M t) 2 P)
    (hMa : M a =ᵐ[P] 0) : ∫ ω, Z ω * M t ω ∂P = 0 := by
  rw [integral_mul_martingale_eq hM hat hZ hZ2 hMt]
  have h0 : (fun ω => Z ω * M a ω) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [hMa] with ω hω
    rw [hω, Pi.zero_apply, mul_zero]
  rw [integral_congr_ae h0, integral_zero]

omit [IsProbabilityMeasure P] in
/-- A square-integrable integrand on a window is square integrable for the product measure. -/
theorem memLp_two_prod {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (fun p : Ω × ℝ => f p.1 p.2) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hf.aestronglyMeasurable ?_
  exact lt_of_eq_of_lt (lintegral_prod _ (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable)
    hfq

omit [IsProbabilityMeasure P] in
/-- A square-integrable variable, read at the sample point, is square integrable for the product
measure with a bounded window. -/
theorem memLp_two_prod_fst {g : Ω → ℝ} (hg : MemLp g 2 P) {T : ℝ} :
    MemLp (fun p : Ω × ℝ => g p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
    hg.aestronglyMeasurable.aemeasurable.comp_fst.aestronglyMeasurable ?_
  have hgm : AEMeasurable (fun ω => (‖g ω‖₊ : ℝ≥0∞) ^ 2) P :=
    hg.aestronglyMeasurable.aemeasurable.nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [lintegral_prod _ hgm.comp_fst]
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  exact ENNReal.mul_lt_top (lintegral_sq_lt_top_of_memLp_two hg) ENNReal.ofReal_lt_top

/-- **The pairing of a time integral against a square-integrable variable is the time integral
of the pairings.** -/
theorem integral_setIntegral_mul {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {g : Ω → ℝ} (hg : MemLp g 2 P) :
    ∫ ω, (∫ s in Set.Icc (0 : ℝ) T, f ω s) * g ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, f ω s * g ω ∂P := by
  have hint : Integrable (fun p : Ω × ℝ => f p.1 p.2 * g p.1)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (memLp_two_prod hf hfq).integrable_mul (memLp_two_prod_fst hg)
  calc ∫ ω, (∫ s in Set.Icc (0 : ℝ) T, f ω s) * g ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, f ω s * g ω ∂volume ∂P := by
        refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
        exact (integral_mul_const (g ω) fun s => f ω s).symm
    _ = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, f ω s * g ω ∂P :=
        integral_integral_swap (f := fun ω s => f ω s * g ω) hint

omit [IsProbabilityMeasure P] in
/-- The time integral of a square-integrable integrand is square integrable. -/
theorem memLp_two_setIntegral {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hT : 0 ≤ T)
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) T, f ω s) 2 P := by
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top ?_ ?_
  · exact (hf.stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T))).aestronglyMeasurable
  · exact lt_of_le_of_lt (LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le hf hT hfq)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfq)

/-- **The square of the integral of an integrable function over `[0, T]` is twice the integral
of its running integral against the function.** -/
theorem mul_self_setIntegral_eq {b : ℝ → ℝ} {T : ℝ}
    (hb : IntegrableOn b (Set.Icc (0 : ℝ) T)) :
    (∫ s in Set.Icc (0 : ℝ) T, b s) * (∫ s in Set.Icc (0 : ℝ) T, b s)
      = 2 * ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, b r) * b s := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have hprod : Integrable (fun p : ℝ × ℝ => b p.1 * b p.2) (μ.prod μ) := hb.mul_prod hb
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => b p.1 * b p.2 with hF
  set G : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun p => b p.1 * b p.2 with hG
  set Dg : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 = p.2}.indicator fun p => b p.1 * b p.2 with hDg
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hge : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hFint : Integrable F (μ.prod μ) := hprod.indicator hle
  have hGint : Integrable G (μ.prod μ) := hprod.indicator hge
  have hDint : Integrable Dg (μ.prod μ) := hprod.indicator hdiag
  -- the pointwise decomposition of the product along the two triangles and the diagonal
  have hsplit : ∀ p : ℝ × ℝ, b p.1 * b p.2 + Dg p = F p + G p := by
    intro p
    simp only [hF, hG, hDg, Set.indicator, Set.mem_setOf_eq]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h.le, h.ne, not_le.mpr h]
    · simp [h]
    · simp [h.le, h.ne', not_le.mpr h]
  -- the diagonal is null
  have hDzero : ∫ p, Dg p ∂(μ.prod μ) = 0 := by
    rw [hDg, integral_indicator hdiag]
    refine setIntegral_measure_zero _ ?_
    rw [Measure.prod_apply hdiag]
    simp
  -- the two triangles carry the same integral
  have hGF : G = fun p => F p.swap := by
    funext p
    simp only [hF, hG, Set.indicator, Set.mem_setOf_eq, Prod.fst_swap, Prod.snd_swap]
    split_ifs <;> ring
  have hswap : ∫ p, G p ∂(μ.prod μ) = ∫ p, F p ∂(μ.prod μ) := by
    rw [hGF]
    exact integral_prod_swap F
  -- the lower triangle, sliced at the second coordinate
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ r, F (r, s) ∂μ = (∫ r in Set.Icc (0 : ℝ) s, b r) * b s := by
    intro s hs
    have h1 : (fun r => F (r, s)) = fun r => (Set.Iic s).indicator (fun r => b r * b s) r := by
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
      = ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, b r) * b s := by
    rw [integral_prod_symm F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => hinner s hs
  have hsum : ∫ p, b p.1 * b p.2 ∂(μ.prod μ) = ∫ p, F p ∂(μ.prod μ) + ∫ p, G p ∂(μ.prod μ) := by
    have h1 : ∫ p, (b p.1 * b p.2 + Dg p) ∂(μ.prod μ) = ∫ p, (F p + G p) ∂(μ.prod μ) :=
      integral_congr_ae (Eventually.of_forall hsplit)
    rw [integral_add hprod hDint, integral_add hFint hGint, hDzero, add_zero] at h1
    exact h1
  calc (∫ s in Set.Icc (0 : ℝ) T, b s) * (∫ s in Set.Icc (0 : ℝ) T, b s)
      = ∫ p, b p.1 * b p.2 ∂(μ.prod μ) := (integral_prod_mul b b).symm
    _ = ∫ p, F p ∂(μ.prod μ) + ∫ p, G p ∂(μ.prod μ) := hsum
    _ = 2 * ∫ p, F p ∂(μ.prod μ) := by rw [hswap]; ring
    _ = 2 * ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, b r) * b s := by rw [hFeq]

omit [IsProbabilityMeasure P] in
/-- A window energy finite at every positive horizon is finite at every nonnegative one. -/
theorem energy_lt_top_of_nonneg {f : Ω → ℝ → ℝ}
    (hfq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun _ => lintegral_mono_set
    (Set.Icc_subset_Icc le_rfl (by linarith))) (hfq (t + 1) (by linarith))

/-- At almost every time of a window, a square-integrable integrand is square integrable in the
sample point. -/
theorem ae_memLp_two_eval {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (fun ω => f ω s) 2 P := by
  have hm : Measurable fun p : Ω × ℝ => (‖f p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    hf.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hswap : ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P ∂volume < ⊤ := by
    rw [lintegral_lintegral_swap (f := fun ω s => (‖f ω s‖₊ : ℝ≥0∞) ^ 2) hm.aemeasurable] at hfq
    exact hfq
  have hmeas : Measurable fun s => ∫⁻ ω, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    Measurable.lintegral_prod_left' hm
  filter_upwards [ae_lt_top hmeas hswap.ne] with s hs
  exact LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
    (hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable hs

end Toolkit

section Running

variable (b : ℝ → Ω → ℝ) (T : ℝ)

/-- The running integral `∫_0^s b_r dr`, written as an integral over the fixed window `[0, T]`
so that it is jointly measurable in the sample point and the time. -/
noncomputable def running (p : Ω × ℝ) : ℝ :=
  ∫ r in Set.Icc (0 : ℝ) T, (Set.Iic p.2).indicator (fun r => b r p.1) r

variable {b T}

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem running_eq {ω : Ω} {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    running b T (ω, s) = ∫ r in Set.Icc (0 : ℝ) s, b r ω := by
  have hset : Set.Iic s ∩ Set.Icc (0 : ℝ) T = Set.Icc (0 : ℝ) s := by
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨h1, h2, h1.trans hs.2⟩
  rw [running, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
    hset]

omit [IsProbabilityMeasure P] in
theorem stronglyMeasurable_running (hbm : Measurable (Function.uncurry fun ω s => b s ω)) :
    StronglyMeasurable (running b T) := by
  have hfun : (fun q : (Ω × ℝ) × ℝ => (Set.Iic q.1.2).indicator (fun r => b r q.1.1) q.2)
      = {q : (Ω × ℝ) × ℝ | q.2 ≤ q.1.2}.indicator fun q => b q.2 q.1.1 := by
    funext q
    by_cases hq : q.2 ≤ q.1.2 <;> simp [Set.indicator, hq]
  have hm : Measurable fun q : (Ω × ℝ) × ℝ =>
      (Set.Iic q.1.2).indicator (fun r => b r q.1.1) q.2 := by
    rw [hfun]
    exact (hbm.comp (measurable_fst.fst.prodMk measurable_snd)).indicator
      (measurableSet_le measurable_snd measurable_fst.snd)
  exact hm.stronglyMeasurable.integral_prod_right'

/-- The running integral is square integrable for the product measure on the window. -/
theorem memLp_two_running (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (running b T) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hR := stronglyMeasurable_running (T := T) hbm
  refine LevyStochCalc.Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hR.aestronglyMeasurable ?_
  rw [lintegral_prod_symm _ (hR.measurable.nnnorm.coe_nnreal_ennreal.pow_const 2).aemeasurable]
  set K : ℝ≥0∞ := ENNReal.ofReal T
    * ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P with hK
  have hKlt : K < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbq
  have hbound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ω, (‖running b T (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ K := by
    intro s hs
    have h1 : ∀ ω, running b T (ω, s) = ∫ r in Set.Icc (0 : ℝ) s, b r ω :=
      fun ω => running_eq hs
    simp_rw [h1]
    have hwin : ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) s, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) T, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
      lintegral_mono fun _ => lintegral_mono_set (Set.Icc_subset_Icc le_rfl hs.2)
    calc ∫⁻ ω, (‖∫ r in Set.Icc (0 : ℝ) s, b r ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal s
          * ∫⁻ ω, ∫⁻ r in Set.Icc (0 : ℝ) s, (‖b r ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
          LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le (f := fun ω r => b r ω) hbm hs.1
            (lt_of_le_of_lt hwin hbq)
      _ ≤ K := by
          rw [hK]
          exact mul_le_mul' (ENNReal.ofReal_le_ofReal hs.2) hwin
  calc ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ ω, (‖running b T (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂P ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T, K ∂volume :=
        setLIntegral_mono' measurableSet_Icc fun s hs => hbound s hs
    _ = K * ENNReal.ofReal T := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
    _ < ⊤ := ENNReal.mul_lt_top hKlt ENNReal.ofReal_lt_top

end Running

section Polarised

omit [IsProbabilityMeasure P] in
/-- The energy of a square-integrable integrand on a window is the integral of its square for the
product measure. -/
theorem toReal_lintegral_sq_eq {f : Ω → ℝ → ℝ} (hf : Measurable (Function.uncurry f)) {T : ℝ}
    (hfq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
      = ∫ p, f p.1 p.2 * f p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have hmeas : Measurable fun p : Ω × ℝ => (‖f p.1 p.2‖₊ : ℝ≥0∞) ^ 2 :=
    hf.nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [integral_mul_self_eq_toReal (memLp_two_prod hf hfq)]
  congr 1
  exact (lintegral_prod _ hmeas.aemeasurable).symm

/-- **The polarised Itô isometry.** The pairing of two Itô integrals at a positive time is the
integral of the pairing of their integrands over the window. -/
theorem integral_mul_stochasticIntegralBrownian (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω ∂P
      = ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, H ω s * K ω s ∂volume ∂P := by
  have hU2 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ H hHm hHp hHs T
  have hV2 := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp W ℱ hℱ K hKm hKp hKs T
  have hUV2 : MemLp (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) 2 P :=
    hU2.sub hV2
  have hdiff := LevyStochCalc.Brownian.Ito.isometry_diff_stochasticIntegralBrownian W ℱ hℱ H K
    hHm hKm hHp hKp hHs hKs hT
  have hdq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s - K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    rw [← hdiff]
    exact lintegral_sq_lt_top_of_memLp_two hUV2
  have hHm2 := memLp_two_prod hHm (hHs T hT)
  have hKm2 := memLp_two_prod hKm (hKs T hT)
  -- the three energies, on the product measure
  have hUU : ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω ∂P
      = ∫ p, H p.1 p.2 * H p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    rw [integral_mul_self_eq_toReal hU2,
      LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs hT]
    exact toReal_lintegral_sq_eq hHm (hHs T hT)
  have hVV : ∫ ω, LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω ∂P
      = ∫ p, K p.1 p.2 * K p.1 p.2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    rw [integral_mul_self_eq_toReal hV2,
      LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs hT]
    exact toReal_lintegral_sq_eq hKm (hKs T hT)
  have hDD : ∫ ω, (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) ∂P
      = ∫ p, (H p.1 p.2 - K p.1 p.2) * (H p.1 p.2 - K p.1 p.2)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
    rw [integral_mul_self_eq_toReal hUV2, hdiff]
    exact toReal_lintegral_sq_eq (f := fun ω s => H ω s - K ω s) (hHm.sub hKm) hdq
  -- the algebra of the polarisation identity
  have iUU : Integrable (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω) P :=
    hU2.integrable_mul hU2
  have iVV : Integrable (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) P :=
    hV2.integrable_mul hV2
  have iDD : Integrable (fun ω =>
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
      * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)) P :=
    hUV2.integrable_mul hUV2
  have iS : Integrable (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
      + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω) P :=
    iUU.add iVV
  have hexp : (fun ω =>
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
      = fun ω =>
        (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
        + LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
          * LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω
        - (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω)
        * (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H hHm hHp hHs T ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ K hKm hKp hKs T ω))
        / 2 := by
    funext ω
    ring
  have iHH : Integrable (fun p : Ω × ℝ => H p.1 p.2 * H p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hHm2.integrable_mul hHm2
  have iKK : Integrable (fun p : Ω × ℝ => K p.1 p.2 * K p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hKm2.integrable_mul hKm2
  have iHK : Integrable (fun p : Ω × ℝ => H p.1 p.2 * K p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hHm2.integrable_mul hKm2
  have iDD' : Integrable (fun p : Ω × ℝ => (H p.1 p.2 - K p.1 p.2) * (H p.1 p.2 - K p.1 p.2))
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    (hHm2.sub hKm2).integrable_mul (hHm2.sub hKm2)
  have iS' : Integrable (fun p : Ω × ℝ => H p.1 p.2 * H p.1 p.2 + K p.1 p.2 * K p.1 p.2)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := iHH.add iKK
  rw [hexp, integral_div, integral_sub iS iDD, integral_add iUU iVV, hUU, hVV, hDD,
    ← integral_add iHH iKK, ← integral_sub iS' iDD', ← integral_div, ← integral_prod _ iHK]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  ring

end Polarised

section PolarisedDrift

omit [IsProbabilityMeasure P] in
/-- **The product of the integrals of two integrable functions over `[0, T]`** is the integral of
the pairing of their running integrals against each other. -/
theorem mul_setIntegral_eq {b b' : ℝ → ℝ} {T : ℝ}
    (hb : IntegrableOn b (Set.Icc (0 : ℝ) T)) (hb' : IntegrableOn b' (Set.Icc (0 : ℝ) T)) :
    (∫ s in Set.Icc (0 : ℝ) T, b s) * (∫ s in Set.Icc (0 : ℝ) T, b' s)
      = ∫ s in Set.Icc (0 : ℝ) T,
          ((∫ r in Set.Icc (0 : ℝ) s, b r) * b' s + b s * ∫ r in Set.Icc (0 : ℝ) s, b' r) := by
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hμ
  have hprod : Integrable (fun p : ℝ × ℝ => b p.1 * b' p.2) (μ.prod μ) := hb.mul_prod hb'
  set F : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 ≤ p.2}.indicator fun p => b p.1 * b' p.2 with hF
  set G : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.2 ≤ p.1}.indicator fun p => b p.1 * b' p.2 with hG
  set Dg : ℝ × ℝ → ℝ := {p : ℝ × ℝ | p.1 = p.2}.indicator fun p => b p.1 * b' p.2 with hDg
  have hle : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
    measurableSet_le measurable_fst measurable_snd
  have hge : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  have hdiag : MeasurableSet {p : ℝ × ℝ | p.1 = p.2} :=
    measurableSet_eq_fun measurable_fst measurable_snd
  have hFint : Integrable F (μ.prod μ) := hprod.indicator hle
  have hGint : Integrable G (μ.prod μ) := hprod.indicator hge
  have hDint : Integrable Dg (μ.prod μ) := hprod.indicator hdiag
  have hsplit : ∀ p : ℝ × ℝ, b p.1 * b' p.2 + Dg p = F p + G p := by
    intro p
    simp only [hF, hG, hDg, Set.indicator, Set.mem_setOf_eq]
    rcases lt_trichotomy p.1 p.2 with h | h | h
    · simp [h.le, h.ne, not_le.mpr h]
    · simp [h]
    · simp [h.le, h.ne', not_le.mpr h]
  have hDzero : ∫ p, Dg p ∂(μ.prod μ) = 0 := by
    rw [hDg, integral_indicator hdiag]
    refine setIntegral_measure_zero _ ?_
    rw [Measure.prod_apply hdiag]
    simp
  have hset : ∀ s ∈ Set.Icc (0 : ℝ) T, Set.Iic s ∩ Set.Icc (0 : ℝ) T = Set.Icc (0 : ℝ) s := by
    intro s hs
    ext r
    simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]
    constructor
    · rintro ⟨h1, h2, _⟩
      exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩
      exact ⟨h1, h2, h1.trans hs.2⟩
  -- the lower triangle, sliced at the second coordinate
  have hinnerF : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ r, F (r, s) ∂μ = (∫ r in Set.Icc (0 : ℝ) s, b r) * b' s := by
    intro s hs
    have h1 : (fun r => F (r, s)) = fun r => (Set.Iic s).indicator (fun r => b r * b' s) r := by
      funext r
      simp only [hF, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
    rw [h1, integral_indicator measurableSet_Iic, integral_mul_const, hμ,
      Measure.restrict_restrict measurableSet_Iic, hset s hs]
  -- the upper triangle, sliced at the first coordinate
  have hinnerG : ∀ r ∈ Set.Icc (0 : ℝ) T,
      ∫ s, G (r, s) ∂μ = b r * ∫ s in Set.Icc (0 : ℝ) r, b' s := by
    intro r hr
    have h1 : (fun s => G (r, s)) = fun s => (Set.Iic r).indicator (fun s => b r * b' s) s := by
      funext s
      simp only [hG, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic]
    rw [h1, integral_indicator measurableSet_Iic, integral_const_mul, hμ,
      Measure.restrict_restrict measurableSet_Iic, hset r hr]
  have hFeq : ∫ p, F p ∂(μ.prod μ)
      = ∫ s in Set.Icc (0 : ℝ) T, (∫ r in Set.Icc (0 : ℝ) s, b r) * b' s := by
    rw [integral_prod_symm F hFint]
    exact setIntegral_congr_fun measurableSet_Icc fun s hs => hinnerF s hs
  have hGeq : ∫ p, G p ∂(μ.prod μ)
      = ∫ r in Set.Icc (0 : ℝ) T, b r * ∫ s in Set.Icc (0 : ℝ) r, b' s := by
    rw [integral_prod G hGint]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hinnerG r hr
  have hFi : Integrable (fun s => (∫ r in Set.Icc (0 : ℝ) s, b r) * b' s)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : Integrable (fun s => ∫ r, F (r, s) ∂μ) μ := hFint.integral_prod_right
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact hinnerF s hs
  have hGi : Integrable (fun r => b r * ∫ s in Set.Icc (0 : ℝ) r, b' s)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : Integrable (fun r => ∫ s, G (r, s) ∂μ) μ := hGint.integral_prod_left
    refine h1.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact hinnerG r hr
  have hsum : ∫ p, b p.1 * b' p.2 ∂(μ.prod μ) = ∫ p, F p ∂(μ.prod μ) + ∫ p, G p ∂(μ.prod μ) := by
    have h1 : ∫ p, (b p.1 * b' p.2 + Dg p) ∂(μ.prod μ) = ∫ p, (F p + G p) ∂(μ.prod μ) :=
      integral_congr_ae (Eventually.of_forall hsplit)
    rw [integral_add hprod hDint, integral_add hFint hGint, hDzero, add_zero] at h1
    exact h1
  calc (∫ s in Set.Icc (0 : ℝ) T, b s) * (∫ s in Set.Icc (0 : ℝ) T, b' s)
      = ∫ p, b p.1 * b' p.2 ∂(μ.prod μ) := (integral_prod_mul b b').symm
    _ = ∫ p, F p ∂(μ.prod μ) + ∫ p, G p ∂(μ.prod μ) := hsum
    _ = ∫ s in Set.Icc (0 : ℝ) T,
          ((∫ r in Set.Icc (0 : ℝ) s, b r) * b' s + b s * ∫ r in Set.Icc (0 : ℝ) s, b' r) := by
        rw [hFeq, hGeq, ← integral_add hFi hGi]

end PolarisedDrift

end LevyStochCalc.Ito.SecondMoment
