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
# The second moment of an Itô–Lévy process

For an Itô–Lévy process `X_t = X₀ + ∫_0^t b ds + ∑_j ∫_0^t σ_j dW^j + ∫_0^t ∫_E γ dÑ` over a Lévy
driver, with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift, the second moment at a time `T > 0` is

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`,

the expectation form of the quadratic Itô formula, under the `L²` hypotheses alone: no fourth
moment and no pathwise formula is used. It follows from the isometries of the two stochastic
integrals, the orthogonality of the Brownian coordinates and of the Brownian and compensated
integrals, the martingale property of both integrals against the initial value and the drift,
and the pathwise identity `(∫_0^T b)² = 2 ∫_0^T (∫_0^s b) b_s ds`. The drift term is the time
integral of the expected pairing; at every time the pairing is expanded along the decomposition,
and the two martingale pieces are read at the horizon by the martingale property.

## Main statements

* `integral_mul_self_eq_of_isItoLevyProcess` — the second moment of a scalar Itô–Lévy process
  over a Lévy driver whose Brownian and compensated integrals are orthogonal
  (`LevyDriver.CrossWitness`, supplied by `LevyDriver.crossWitness` for the joint natural
  filtration and by `CrossWitness.aug` for its augmentation).
* `integral_sum_mul_self_eq_of_isItoLevyProcess` — the vector form, coordinate by coordinate.
* `integral_mul_self_eq_of_isItoLevyProcess_aug` — the scalar form over the augmented joint
  natural filtration of the driver, with the witness supplied by the driver.
* `memLp_two_of_isItoLevyProcess` — such a process is square integrable at every nonnegative
  time.
* `integral_mul_martingale_eq` — pairing a square-integrable martingale at a later time against
  a square-integrable variable measurable at an earlier time reads the martingale at the earlier
  time.
* `integral_setIntegral_mul` — the pairing of a time integral against a square-integrable
  variable is the time integral of the pairings.
* `mul_self_setIntegral_eq` — the square of the integral of an integrable function over `[0, T]`
  is twice the integral of its running integral against the function.
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

section Scalar

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- An Itô–Lévy process with a square-integrable initial value and a square-integrable drift is
square integrable at every nonnegative time. -/
theorem memLp_two_of_isItoLevyProcess
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (hX₀2 : MemLp X₀ 2 P) (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) : MemLp (X t) 2 P := by
  have hS2 : ∀ j : Fin d, MemLp (LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ
      (hℱW j) (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t) 2 P := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hSsum2 : MemLp (fun ω => ∑ j, LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ
      (hℱW j) (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t ω) 2 P :=
    memLp_finsetSum Finset.univ fun j _ => hS2 j
  have hC2 : MemLp (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq t) 2 P :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hDr2 : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω) 2 P :=
    memLp_two_setIntegral (f := fun ω s => b s ω) hbm ht
      (energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq ht)
  refine (((hX₀2.add hDr2).add hSsum2).add hC2).ae_eq ?_
  exact Filter.EventuallyEq.symm (h.decomposition t ht)

/-- **The second moment of an Itô–Lévy process.** For an Itô–Lévy process over a Lévy driver
with a square-integrable initial value measurable at time zero and a square-integrable
progressive drift,

`𝔼[X_T²] = 𝔼[X₀²] + 2 ∫_0^T 𝔼[X_s b_s] ds + ∑_j 𝔼 ∫_0^T σ_j² ds + 𝔼 ∫_0^T ∫_E γ² dν ds`. -/
theorem integral_mul_self_eq_of_isItoLevyProcess
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + 2 * (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P)
        + (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
  classical
  -- the three pieces of the decomposition
  set S : Fin d → ℝ → Ω → ℝ := fun j =>
    LevyStochCalc.Brownian.Ito.stochasticIntegral (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j)
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) with hSdef
  set C : ℝ → Ω → ℝ :=
    LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq
    with hCdef
  set Dr : ℝ → Ω → ℝ := fun t ω => ∫ s in Set.Icc (0 : ℝ) t, b s ω with hDrdef
  have hdec : ∀ t, 0 ≤ t → ∀ᵐ ω ∂P,
      X t ω = X₀ ω + Dr t ω + (∑ j, S j t ω) + C t ω := fun t ht => h.decomposition t ht
  -- square integrability of every piece
  have hS2 : ∀ (j : Fin d) (t : ℝ), MemLp (S j t) 2 P := fun j t =>
    LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t
  have hSsum2 : ∀ t, MemLp (fun ω => ∑ j, S j t ω) 2 P := fun t =>
    memLp_finsetSum Finset.univ fun j _ => hS2 j t
  have hC2 : ∀ t, MemLp (C t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog
      h.γ_sq t
  have hbq' : ∀ t, 0 ≤ t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun t ht => energy_lt_top_of_nonneg (f := fun ω s => b s ω) hbq ht
  have hDr2 : ∀ t, 0 ≤ t → MemLp (Dr t) 2 P := fun t ht =>
    memLp_two_setIntegral (f := fun ω s => b s ω) hbm ht (hbq' t ht)
  -- the isometries
  have hSiso : ∀ j, ∫ ω, S j T ω * S j T ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    intro j
    rw [integral_mul_self_eq_toReal (hS2 j T)]
    congr 1
    exact LevyStochCalc.Brownian.Ito.isometry_stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j) _
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) hT
  have hCiso : ∫ ω, C T ω * C T ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
    rw [integral_mul_self_eq_toReal (hC2 T)]
    congr 1
    exact LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq T hT
  -- the orthogonalities
  have hSS : ∀ j k, j ≠ k → ∫ ω, S j T ω * S k T ω ∂P = 0 := fun j k hjk =>
    LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero
      D.W hjk hℱW (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) (h.σ_meas k) (h.σ_prog k) (h.σ_sq k) hT.le
  have hSC : ∀ j, ∫ ω, S j T ω * C T ω ∂P = 0 := fun j =>
    LevyStochCalc.Driver.LevyDriver.integral_stochasticIntegral_mul_compensated_eq_zero 𝒲 hℱW hℱN
      (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) h.γ_meas h.γ_prog h.γ_sq hT.le
  have hSsum_sq : ∫ ω, (∑ j, S j T ω) * (∑ j, S j T ω) ∂P
      = ∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
    have hexp : (fun ω => (∑ j, S j T ω) * (∑ j, S j T ω))
        = fun ω => ∑ j, ∑ k, S j T ω * S k T ω := by
      funext ω
      exact Finset.sum_mul_sum _ _ _ _
    have hint : ∀ j k, Integrable (fun ω => S j T ω * S k T ω) P := fun j k =>
      (hS2 j T).integrable_mul (hS2 k T)
    have hint' : ∀ j, Integrable (fun ω => ∑ k, S j T ω * S k T ω) P := fun j =>
      integrable_finsetSum _ fun k _ => hint j k
    rw [hexp, integral_finsetSum _ fun j _ => hint' j]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => hint j k,
      Finset.sum_eq_single j (fun k _ hkj => hSS j k (Ne.symm hkj))
        (fun hj => absurd (Finset.mem_univ j) hj)]
    exact hSiso j
  have hSsum_C : ∫ ω, (∑ j, S j T ω) * C T ω ∂P = 0 := by
    have hexp : (fun ω => (∑ j, S j T ω) * C T ω) = fun ω => ∑ j, S j T ω * C T ω := by
      funext ω
      exact Finset.sum_mul _ _ _
    have hint : ∀ j, Integrable (fun ω => S j T ω * C T ω) P := fun j =>
      (hS2 j T).integrable_mul (hC2 T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hSC j
  -- the martingale pieces are orthogonal to the initial value
  have hX₀S : ∀ j, ∫ ω, X₀ ω * S j T ω ∂P = 0 := fun j =>
    integral_mul_martingale_eq_zero
      (LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j))
      hT.le (hX₀.mono (ℱ.le_rightCont 0)) hX₀2 (hS2 j T)
      (LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos (D.W.W j) ℱ
        (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) le_rfl)
  have hX₀Ssum : ∫ ω, X₀ ω * (∑ j, S j T ω) ∂P = 0 := by
    have hexp : (fun ω => X₀ ω * (∑ j, S j T ω)) = fun ω => ∑ j, X₀ ω * S j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => X₀ ω * S j T ω) P := fun j =>
      hX₀2.integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
    exact Finset.sum_eq_zero fun j _ => hX₀S j
  have hCproc : ∀ t, C t =ᵐ[P]
      LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t :=
    fun t => LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process D.N ℱ hℱN γ
      h.γ_meas h.γ_prog h.γ_sq t
  have hproc2 : ∀ t, MemLp (LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas
      h.γ_prog h.γ_sq t) 2 P := fun t =>
    LevyStochCalc.Poisson.Compensated.process_memLp D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq t
  have hmartC := LevyStochCalc.Poisson.Compensated.martingale_process D.N ℱ hℱN γ h.γ_meas
    h.γ_prog h.γ_sq
  have hproc0 := LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos D.N ℱ hℱN γ
    h.γ_meas h.γ_prog h.γ_sq (le_refl (0 : ℝ))
  have hX₀C : ∫ ω, X₀ ω * C T ω ∂P = 0 := by
    have h1 : (fun ω => X₀ ω * C T ω) =ᵐ[P] fun ω => X₀ ω
        * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
      filter_upwards [hCproc T] with ω hω
      rw [hω]
    rw [integral_congr_ae h1]
    exact integral_mul_martingale_eq_zero hmartC hT.le hX₀ hX₀2 (hproc2 T) hproc0
  -- the drift pairings at the horizon, as time integrals
  have hDrS : ∀ j, ∫ ω, Dr T ω * S j T ω ∂P
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * S j T ω ∂P :=
    fun j => integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hS2 j T)
  have hDrC : ∫ ω, Dr T ω * C T ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * C T ω ∂P :=
    integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) (hC2 T)
  have hDrX₀ : ∫ ω, Dr T ω * X₀ ω ∂P = ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * X₀ ω ∂P :=
    integral_setIntegral_mul (f := fun ω s => b s ω) hbm (hbq T hT) hX₀2
  have hDrDr : ∫ ω, Dr T ω * Dr T ω ∂P
      = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr s ω ∂P := by
    have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s => b s ω) (Set.Icc (0 : ℝ) T) volume := by
      filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b s ω) hbm hbq] with ω hω
      exact hω T
    have hR := memLp_two_running (P := P) hbm (hbq T hT)
    have hint : Integrable (fun p : Ω × ℝ => b p.2 p.1 * running b T p)
        (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
      (memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul hR
    have hpath : ∀ᵐ ω ∂P, Dr T ω * Dr T ω
        = 2 * ∫ s in Set.Icc (0 : ℝ) T, b s ω * running b T (ω, s) := by
      filter_upwards [hbint] with ω hω
      simp only [hDrdef]
      rw [mul_self_setIntegral_eq hω]
      congr 1
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      rw [running_eq hs, mul_comm]
    calc ∫ ω, Dr T ω * Dr T ω ∂P
        = ∫ ω, (2 * ∫ s in Set.Icc (0 : ℝ) T, b s ω * running b T (ω, s)) ∂P :=
          integral_congr_ae hpath
      _ = 2 * ∫ ω, ∫ s in Set.Icc (0 : ℝ) T, b s ω * running b T (ω, s) ∂volume ∂P :=
          integral_const_mul _ _
      _ = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * running b T (ω, s) ∂P := by
          rw [integral_integral_swap (f := fun ω s => b s ω * running b T (ω, s)) hint]
      _ = 2 * ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, b s ω * Dr s ω ∂P := by
          congr 1
          refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
          refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
          exact congrArg (fun x => b s ω * x) (running_eq hs)
  -- at almost every time of the window, the pairing of the path with the drift expands
  have hbs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (fun ω => b s ω) 2 P :=
    ae_memLp_two_eval (f := fun ω s => b s ω) hbm (hbq T hT)
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hXb : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P
        + (∑ j, ∫ ω, b s ω * S j T ω ∂P) + ∫ ω, b s ω * C T ω ∂P := by
    filter_upwards [hbs, hsw] with s hs2 hs
    have hs0 : 0 ≤ s := hs.1
    have hbsm : StronglyMeasurable[ℱ.rightCont s] fun ω => b s ω :=
      (hbp.stronglyMeasurable_eval s).mono (ℱ.le_rightCont s)
    have hbsm' : StronglyMeasurable[ℱ s] fun ω => b s ω := hbp.stronglyMeasurable_eval s
    have h1 : ∫ ω, X s ω * b s ω ∂P
        = ∫ ω, (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * b s ω ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hdec s hs0] with ω hω
      rw [hω]
    have hexp : (fun ω => (X₀ ω + Dr s ω + (∑ j, S j s ω) + C s ω) * b s ω)
        = fun ω => b s ω * X₀ ω + b s ω * Dr s ω + (∑ j, b s ω * S j s ω) + b s ω * C s ω := by
      funext ω
      rw [← Finset.mul_sum]
      ring
    have i1 : Integrable (fun ω => b s ω * X₀ ω) P := hs2.integrable_mul hX₀2
    have i2 : Integrable (fun ω => b s ω * Dr s ω) P := hs2.integrable_mul (hDr2 s hs0)
    have i3 : ∀ j, Integrable (fun ω => b s ω * S j s ω) P := fun j =>
      hs2.integrable_mul (hS2 j s)
    have i3' : Integrable (fun ω => ∑ j, b s ω * S j s ω) P :=
      integrable_finsetSum _ fun j _ => i3 j
    have i4 : Integrable (fun ω => b s ω * C s ω) P := hs2.integrable_mul (hC2 s)
    have i12 : Integrable (fun ω => b s ω * X₀ ω + b s ω * Dr s ω) P := i1.add i2
    have i123 : Integrable
        (fun ω => b s ω * X₀ ω + b s ω * Dr s ω + ∑ j, b s ω * S j s ω) P := i12.add i3'
    have hSj : ∀ j, ∫ ω, b s ω * S j s ω ∂P = ∫ ω, b s ω * S j T ω ∂P := fun j =>
      (integral_mul_martingale_eq
        (LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian (D.W.W j) ℱ
          (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j)) hs.2 hbsm hs2 (hS2 j T)).symm
    have hCs : ∫ ω, b s ω * C s ω ∂P = ∫ ω, b s ω * C T ω ∂P := by
      have e1 : (fun ω => b s ω * C s ω) =ᵐ[P] fun ω => b s ω
          * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq s ω := by
        filter_upwards [hCproc s] with ω hω
        rw [hω]
      have e2 : (fun ω => b s ω * C T ω) =ᵐ[P] fun ω => b s ω
          * LevyStochCalc.Poisson.Compensated.process D.N ℱ hℱN γ h.γ_meas h.γ_prog h.γ_sq T ω := by
        filter_upwards [hCproc T] with ω hω
        rw [hω]
      rw [integral_congr_ae e1, integral_congr_ae e2]
      exact (integral_mul_martingale_eq hmartC hs.2 hbsm' hs2 (hproc2 T)).symm
    rw [h1, hexp, integral_add i123 i4, integral_add i12 i3', integral_add i1 i2,
      integral_finsetSum _ fun j _ => i3 j, hCs]
    congr 1
    congr 1
    exact Finset.sum_congr rfl fun j _ => hSj j
  -- integrability in time of the pieces
  have hint_s : ∀ (g : Ω → ℝ), MemLp g 2 P →
      Integrable (fun s => ∫ ω, b s ω * g ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun g hg => ((memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
      (memLp_two_prod_fst hg)).integral_prod_right
  have hint_Dr : Integrable (fun s => ∫ ω, b s ω * Dr s ω ∂P)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    have h1 : Integrable (fun s => ∫ ω, b s ω * running b T (ω, s) ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) :=
      ((memLp_two_prod (f := fun ω s => b s ω) hbm (hbq T hT)).integrable_mul
        (memLp_two_running (P := P) hbm (hbq T hT))).integral_prod_right
    refine h1.congr ?_
    filter_upwards [hsw] with s hs
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    exact congrArg (fun x => b s ω * x) (running_eq hs)
  have hXs_int : ∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P
      = ∫ ω, Dr T ω * X₀ ω ∂P + (1 / 2) * ∫ ω, Dr T ω * Dr T ω ∂P
        + (∑ j, ∫ ω, Dr T ω * S j T ω ∂P) + ∫ ω, Dr T ω * C T ω ∂P := by
    have i1 := hint_s X₀ hX₀2
    have i3 : ∀ j, Integrable (fun s => ∫ ω, b s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := fun j => hint_s _ (hS2 j T)
    have i3' : Integrable (fun s => ∑ j, ∫ ω, b s ω * S j T ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := integrable_finsetSum _ fun j _ => i3 j
    have i4 := hint_s _ (hC2 T)
    have i12 : Integrable (fun s => ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P)
        (volume.restrict (Set.Icc (0 : ℝ) T)) := i1.add hint_Dr
    have i123 : Integrable (fun s => ∫ ω, b s ω * X₀ ω ∂P + ∫ ω, b s ω * Dr s ω ∂P
        + ∑ j, ∫ ω, b s ω * S j T ω ∂P) (volume.restrict (Set.Icc (0 : ℝ) T)) := i12.add i3'
    rw [integral_congr_ae hXb, integral_add i123 i4, integral_add i12 i3', integral_add i1 hint_Dr,
      integral_finsetSum _ fun j _ => i3 j, hDrX₀, hDrDr, hDrC,
      Finset.sum_congr rfl fun j _ => hDrS j]
    ring
  -- the pairing of the initial value with the drift, and the drift with the Brownian sum
  have hcomm : ∫ ω, X₀ ω * Dr T ω ∂P = ∫ ω, Dr T ω * X₀ ω ∂P :=
    integral_congr_ae (Eventually.of_forall fun ω => mul_comm _ _)
  have hDrSsum : ∫ ω, Dr T ω * (∑ j, S j T ω) ∂P = ∑ j, ∫ ω, Dr T ω * S j T ω ∂P := by
    have hexp : (fun ω => Dr T ω * (∑ j, S j T ω)) = fun ω => ∑ j, Dr T ω * S j T ω := by
      funext ω
      exact Finset.mul_sum _ _ _
    have hint : ∀ j, Integrable (fun ω => Dr T ω * S j T ω) P := fun j =>
      (hDr2 T hT.le).integrable_mul (hS2 j T)
    rw [hexp, integral_finsetSum _ fun j _ => hint j]
  -- expand the square of the decomposition at the horizon
  have hL : ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, (X₀ ω + Dr T ω + ((∑ j, S j T ω) + C T ω))
          * (X₀ ω + Dr T ω + ((∑ j, S j T ω) + C T ω)) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hdec T hT.le] with ω hω
    rw [hω]
    ring
  have hf1 : MemLp (fun ω => X₀ ω + Dr T ω) 2 P := hX₀2.add (hDr2 T hT.le)
  have hg1 : MemLp (fun ω => (∑ j, S j T ω) + C T ω) 2 P := (hSsum2 T).add (hC2 T)
  rw [hL, integral_mul_self_add hf1 hg1, integral_mul_self_add hX₀2 (hDr2 T hT.le),
    integral_mul_self_add (hSsum2 T) (hC2 T),
    integral_add_mul_add hX₀2 (hDr2 T hT.le) (hSsum2 T) (hC2 T),
    hSsum_sq, hCiso, hSsum_C, hX₀Ssum, hX₀C, hXs_int, hcomm, hDrSsum]
  ring

end Scalar

section Vector

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : Fin n → ℝ → Ω → ℝ} {X₀ : Fin n → Ω → ℝ} {b : Fin n → ℝ → Ω → ℝ}
  {σ : Fin n → ℝ → Ω → Fin d → ℝ} {γ : Fin n → Ω → ℝ → E → ℝ}

/-- **The second moment of a vector Itô–Lévy process**, coordinate by coordinate: the expected
squared norm at the horizon is the sum of the scalar identities of the coordinates. -/
theorem integral_sum_mul_self_eq_of_isItoLevyProcess
    (h : ∀ i, LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN (X i) (X₀ i) (b i)
      (σ i) (γ i))
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : ∀ i, StronglyMeasurable[ℱ 0] (X₀ i)) (hX₀2 : ∀ i, MemLp (X₀ i) 2 P)
    (hbm : ∀ i, Measurable (Function.uncurry fun ω s => b i s ω))
    (hbp : ∀ i, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b i s ω)
    (hbq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b i s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, ∑ i, X i T ω * X i T ω ∂P
      = ∑ i, (∫ ω, X₀ i ω * X₀ i ω ∂P
        + 2 * (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X i s ω * b i s ω ∂P)
        + (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖σ i s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖γ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal) := by
  have hX2 : ∀ i, MemLp (X i T) 2 P := fun i =>
    memLp_two_of_isItoLevyProcess (h i) (hX₀2 i) (hbm i) (hbq i) hT.le
  have hint : ∀ i, Integrable (fun ω => X i T ω * X i T ω) P := fun i =>
    (hX2 i).integrable_mul (hX2 i)
  rw [integral_finsetSum _ fun i _ => hint i]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_self_eq_of_isItoLevyProcess (h i) 𝒲 (hX₀ i) (hX₀2 i) (hbm i) (hbp i) (hbq i) hT

end Vector

section Augmented

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- The second moment of an Itô–Lévy process over the augmented joint natural filtration of the
driver, where the driver itself supplies the cross witness. -/
theorem integral_mul_self_eq_of_isItoLevyProcess_aug
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
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, X T ω * X T ω ∂P
      = ∫ ω, X₀ ω * X₀ ω ∂P
        + 2 * (∫ s in Set.Icc (0 : ℝ) T, ∫ ω, X s ω * b s ω ∂P)
        + (∑ j : Fin d, (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
        + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal :=
  integral_mul_self_eq_of_isItoLevyProcess h D.crossWitness.aug hX₀ hX₀2 hbm hbp hbq hT

end Augmented

end LevyStochCalc.Ito.SecondMoment
