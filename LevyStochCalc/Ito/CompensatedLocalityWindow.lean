/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.CompensatedLocalityCutoff

/-!
# The compensated integral over a time window

Restricting a marked integrand to a window `(c, t]` preserves admissibility and yields the
increment of the compensated integral across that window; an integrand vanishing after a
positive time `c` has an integral that no longer moves after `c`, the hit indicator of a
stopping time at `c` factors out of the integral over `(c, t]`, and the integral is additive in
the integrand, over differences and over finite sums.

## Main statements

* `stochasticIntegral_ae_eq_of_vanishing_gt` — the integral of an integrand vanishing after a
  time `c` does not move after `c`.
* `stochasticIntegral_indicator_Ioc` — restricting the integrand to `(c, t]` gives the increment
  of the integral over `(c, t]`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one measurable_uncurry_indIoc hitInd
  abs_hitInd_le_one stronglyMeasurable_hitInd sq_nnnorm_add_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {φ : Ω → ℝ → E → ℝ}
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- **Integrands agreeing at positive times have the same integral at positive times.** -/
theorem stochasticIntegral_congr_of_pos {ψ : Ω → ℝ → E → ℝ}
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ∀ e, φ ω s e = ψ ω s e) {t : ℝ}
    (ht : 0 < t) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t := by
  refine stochasticIntegral_congr_ae N hℱ φ ψ hm hmψ hp hpψ hq hqψ ht
    (LevyStochCalc.Ito.markedEnergyMeasure_ae_eq_of_ae_ae hm hmψ t ?_)
  refine Eventually.of_forall fun ω => ?_
  have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with s hs0 hs
  exact hagree ω s (lt_of_le_of_ne hs.1 (Ne.symm (by simpa using hs0)))

include hℱ in
/-- **The integral of an integrand vanishing after a positive time does not move after it.** -/
theorem stochasticIntegral_ae_eq_of_vanishing_gt {c t : ℝ} (hc : 0 < c) (hct : c ≤ t)
    (hφ : ∀ ω s e, c < s → φ ω s e = 0) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t
      =ᵐ[P] stochasticIntegral N ℱ hℱ φ hm hp hq c := by
  set M := process N ℱ hℱ φ hm hp hq with hMdef
  have hmart : Martingale M ℱ P := martingale_process N ℱ hℱ φ hm hp hq
  have hMt : MemLp (M t) 2 P := process_memLp N ℱ hℱ φ hm hp hq t
  have hMc : MemLp (M c) 2 P := process_memLp N ℱ hℱ φ hm hp hq c
  have hMtInt : Integrable (M t) P := hMt.integrable one_le_two
  have hMcInt : Integrable (M c) P := hMc.integrable one_le_two
  have hct_int : Integrable (fun ω => M c ω * M t ω) P := hMc.integrable_mul hMt
  have hcc_int : Integrable (fun ω => M c ω * M c ω) P := hMc.integrable_mul hMc
  have htt_int : Integrable (fun ω => M t ω * M t ω) P := hMt.integrable_mul hMt
  -- the cross moment is the second moment at the earlier time
  have hcross : ∫ ω, M c ω * M t ω ∂P = ∫ ω, M c ω * M c ω ∂P := by
    have hce : P[(fun ω => M c ω * M t ω) | ℱ c]
        =ᵐ[P] fun ω => M c ω * (P[M t | ℱ c]) ω :=
      condExp_mul_of_stronglyMeasurable_left (hmart.stronglyMeasurable c) hct_int hMtInt
    have hmc : P[M t | ℱ c] =ᵐ[P] M c := hmart.condExp_ae_eq hct
    rw [← integral_condExp (ℱ.le c)]
    refine integral_congr_ae (hce.trans ?_)
    filter_upwards [hmc] with ω hω
    rw [hω]
  -- the second moments agree, by the isometry and the vanishing after `c`
  have hwin : ∀ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ s in Set.Icc (0 : ℝ) c, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
    intro ω
    have hdisj : Disjoint (Set.Icc (0 : ℝ) c) (Set.Ioc c t) :=
      Set.disjoint_left.2 fun s hs hs' => absurd hs'.1 (not_lt.2 hs.2)
    rw [← Set.Icc_union_Ioc_eq_Icc hc.le hct, lintegral_union measurableSet_Ioc hdisj,
      setLIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ≥0∞))
        (fun s hs => by simp [hφ ω s _ hs.1]), lintegral_zero, add_zero]
  have hsq : ∀ {r : ℝ}, 0 ≤ r → ∫ ω, M r ω * M r ω ∂P
      = (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) r, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P).toReal := by
    intro r hr
    rw [← process_lintegral_sq' N ℱ hℱ φ hm hp hq hr,
      integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => mul_self_nonneg _)
        ((process_memLp N ℱ hℱ φ hm hp hq r).aestronglyMeasurable.mul
          (process_memLp N ℱ hℱ φ hm hp hq r).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun ω => ?_
    rw [← sq, show ((‖M r ω‖₊ : ℝ≥0∞)) = ‖M r ω‖ₑ from rfl,
      Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hsame : ∫ ω, M t ω * M t ω ∂P = ∫ ω, M c ω * M c ω ∂P := by
    rw [hsq (hc.le.trans hct), hsq hc.le]
    congr 1
    exact lintegral_congr hwin
  -- hence the increment has zero second moment
  have hzero : ∫ ω, (M t ω - M c ω) * (M t ω - M c ω) ∂P = 0 := by
    have hexp : (fun ω => (M t ω - M c ω) * (M t ω - M c ω))
        = fun ω => M t ω * M t ω - (2 : ℝ) * (M c ω * M t ω) + M c ω * M c ω := by
      funext ω; ring
    have h1 : Integrable (fun ω => M t ω * M t ω - (2 : ℝ) * (M c ω * M t ω)) P :=
      htt_int.sub (hct_int.const_mul 2)
    rw [hexp, integral_add h1 hcc_int, integral_sub htt_int (hct_int.const_mul 2),
      integral_const_mul, hcross, hsame]
    ring
  have hdiff : Integrable (fun ω => (M t ω - M c ω) * (M t ω - M c ω)) P :=
    (hMt.sub hMc).integrable_mul (hMt.sub hMc)
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => mul_self_nonneg _) hdiff).mp hzero
  filter_upwards [hae, stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq t,
    stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq c] with ω hω ht' hc'
  have h0 : M t ω - M c ω = 0 := mul_self_eq_zero.mp hω
  rw [ht', hc']
  linarith

include hℱ in
/-- The compensated integral depends only on the integrand. -/
theorem stochasticIntegral_congr_fun {ψ : Ω → ℝ → E → ℝ} (h : φ = ψ)
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (t : ℝ) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t
      = stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t := by
  subst h
  rfl

include hℱ in
/-- **Integrands agreeing at the positive times of a window have the same integral at its
end.** -/
theorem stochasticIntegral_congr_of_eqOn_Ioc {ψ : Ω → ℝ → E → ℝ}
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t)
    (hagree : ∀ (ω : Ω) (s : ℝ), s ∈ Set.Ioc 0 t → ∀ e, φ ω s e = ψ ω s e) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t
      =ᵐ[P] stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t := by
  refine stochasticIntegral_congr_ae N hℱ φ ψ hm hmψ hp hpψ hq hqψ ht
    (LevyStochCalc.Ito.markedEnergyMeasure_ae_eq_of_ae_ae hm hmψ t ?_)
  refine Eventually.of_forall fun ω => ?_
  have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
  filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc] with s hs0 hs
  exact hagree ω s ⟨lt_of_le_of_ne hs.1 (Ne.symm (by simpa using hs0)), hs.2⟩

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include hm in
/-- Restricting a marked integrand to a time window preserves joint measurability. -/
theorem measurable_indIoc_mul (c t : ℝ) :
    Measurable fun p : Ω × ℝ × E => indIoc Ω c t p.1 p.2.1 * φ p.1 p.2.1 p.2.2 :=
  ((measurable_uncurry_indIoc (Ω := Ω) c t).comp (measurable_fst.prodMk measurable_snd.fst)).mul
    hm

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include hp in
/-- Restricting a marked integrand to a time window preserves progressive measurability. -/
theorem markedProgressivelyMeasurable_indIoc_mul (c t : ℝ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => indIoc Ω c t ω s * φ ω s e := by
  have hfun : (fun ω s e => indIoc Ω c t ω s * φ ω s e)
      = fun ω s e => (Set.Ioc c t).indicator (fun _ => φ ω s e) s := by
    funext ω s e
    by_cases hs : s ∈ Set.Ioc c t <;> simp [indIoc, hs]
  rw [hfun]
  exact hp.indicator_time measurableSet_Ioc

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
include hq in
/-- Restricting a marked integrand to a time window preserves finite energy. -/
theorem sq_int_global_indIoc_mul (c t : ℝ) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖indIoc Ω c t ω s * φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  sq_int_global_of_abs_le (fun ω s e => by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (indIoc_le_one c t ω s)) hq

include hℱ in
/-- The compensated integral at `t` of the integrand restricted to `(0, t]` is the integral at
`t`. -/
theorem stochasticIntegral_indIoc_zero {t : ℝ} (ht : 0 < t) :
    stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω 0 t ω s * φ ω s e)
        (measurable_indIoc_mul hm 0 t) (markedProgressivelyMeasurable_indIoc_mul hp 0 t)
        (sq_int_global_indIoc_mul hq 0 t) t
      =ᵐ[P] stochasticIntegral N ℱ hℱ φ hm hp hq t :=
  stochasticIntegral_congr_of_eqOn_Ioc N hℱ (measurable_indIoc_mul hm 0 t)
    (markedProgressivelyMeasurable_indIoc_mul hp 0 t) (sq_int_global_indIoc_mul hq 0 t) hm hp hq
    ht (fun ω s hs e => by simp [indIoc, hs])

include hℱ in
/-- The compensated integral at a nonpositive time vanishes. -/
theorem stochasticIntegral_ae_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    stochasticIntegral N ℱ hℱ φ hm hp hq t =ᵐ[P] 0 :=
  (stochasticIntegral_ae_eq_process N ℱ hℱ φ hm hp hq t).trans
    (process_ae_zero_of_nonpos N ℱ hℱ φ hm hp hq ht)

include hℱ in
/-- **Locality of the compensated integral.** Restricting the integrand to `(c, t]` gives the
increment of the integral across `(c, t]`. -/
theorem stochasticIntegral_indicator_Ioc {c t : ℝ} (hc : 0 ≤ c) (hct : c < t) :
    stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω c t ω s * φ ω s e)
        (measurable_indIoc_mul hm c t) (markedProgressivelyMeasurable_indIoc_mul hp c t)
        (sq_int_global_indIoc_mul hq c t) t
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        - stochasticIntegral N ℱ hℱ φ hm hp hq c ω := by
  have ht : 0 < t := hc.trans_lt hct
  -- the window `(0, t]` splits at `c`
  have hsplit : (fun ω s e => indIoc Ω 0 t ω s * φ ω s e)
      = fun ω s e => indIoc Ω 0 c ω s * φ ω s e + indIoc Ω c t ω s * φ ω s e := by
    funext ω s e
    simp only [indIoc]
    by_cases h1 : s ∈ Set.Ioc (0 : ℝ) c
    · have h2 : s ∈ Set.Ioc (0 : ℝ) t := ⟨h1.1, h1.2.trans hct.le⟩
      have h3 : s ∉ Set.Ioc c t := fun h => absurd h.1 (not_lt.mpr h1.2)
      simp [h1, h2, h3]
    · by_cases h3 : s ∈ Set.Ioc c t
      · have h2 : s ∈ Set.Ioc (0 : ℝ) t := ⟨hc.trans_lt h3.1, h3.2⟩
        simp [h1, h2, h3]
      · have h2 : s ∉ Set.Ioc (0 : ℝ) t := fun h => by
          rcases le_or_gt s c with hsc | hsc
          · exact h1 ⟨h.1, hsc⟩
          · exact h3 ⟨hsc, h.2⟩
        simp [h1, h2, h3]
  have hm0 := measurable_indIoc_mul hm 0 c
  have hp0 := markedProgressivelyMeasurable_indIoc_mul hp 0 c
  have hq0 := sq_int_global_indIoc_mul hq 0 c
  have hma := measurable_uncurry_congr hsplit (measurable_indIoc_mul hm 0 t)
  have hpa := markedProgressivelyMeasurable_congr hsplit
    (markedProgressivelyMeasurable_indIoc_mul hp 0 t)
  have hqa := sq_int_global_congr hsplit (sq_int_global_indIoc_mul hq 0 t)
  have hadd := stochasticIntegral_add N ℱ hℱ hm0 (measurable_indIoc_mul hm c t) hp0
    (markedProgressivelyMeasurable_indIoc_mul hp c t) hq0 (sq_int_global_indIoc_mul hq c t)
    hma hpa hqa ht
  have hzero := stochasticIntegral_indIoc_zero N hℱ hm hp hq ht
  rw [stochasticIntegral_congr_fun N hℱ (measurable_indIoc_mul hm 0 t)
    (markedProgressivelyMeasurable_indIoc_mul hp 0 t) (sq_int_global_indIoc_mul hq 0 t) hsplit
    hma hpa hqa t] at hzero
  -- the first piece is the integral at `c`
  have hfirst : stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω 0 c ω s * φ ω s e)
        hm0 hp0 hq0 t
      =ᵐ[P] stochasticIntegral N ℱ hℱ φ hm hp hq c := by
    rcases hc.lt_or_eq with hc' | hc'
    · have h1 := stochasticIntegral_ae_eq_of_vanishing_gt N hℱ hm0 hp0 hq0 hc' hct.le
        (fun ω s e hs => by
          have : s ∉ Set.Ioc (0 : ℝ) c := fun h => absurd h.2 (not_le.mpr hs)
          simp [indIoc, this])
      exact h1.trans (stochasticIntegral_indIoc_zero N hℱ hm hp hq hc')
    · subst hc'
      have h1 : stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω 0 0 ω s * φ ω s e)
            hm0 hp0 hq0 t
          =ᵐ[P] 0 :=
        stochasticIntegral_ae_zero_of_vanishing N hℱ _ hm0 hp0 hq0 ht.le
          (fun ω s e _ => by simp [indIoc])
      exact h1.trans (stochasticIntegral_ae_zero_of_nonpos N hℱ hm hp hq le_rfl).symm
  filter_upwards [hadd, hzero, hfirst] with ω h1 h2 h3
  rw [← h2, h1, h3]
  ring

include hℱ in
/-- **Pulling the hit indicator of a stopping time inside the integral over `(c, t]`.** -/
theorem hitInd_mul_stochasticIntegral_indIoc {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    {c t : ℝ} (hc : 0 ≤ c) (hct : c < t)
    (hmV : Measurable fun p : Ω × ℝ × E =>
      hitInd τ c p.1 * (indIoc Ω c t p.1 p.2.1 * φ p.1 p.2.1 p.2.2))
    (hpV : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e))
    (hqV : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e)‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤) :
    stochasticIntegral N ℱ hℱ (fun ω s e => hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e))
        hmV hpV hqV t
      =ᵐ[P] fun ω => hitInd τ c ω
        * stochasticIntegral N ℱ hℱ (fun ω s e => indIoc Ω c t ω s * φ ω s e)
          (measurable_indIoc_mul hm c t) (markedProgressivelyMeasurable_indIoc_mul hp c t)
          (sq_int_global_indIoc_mul hq c t) t ω := by
  have ht : 0 < t := hc.trans_lt hct
  let G : MarkedHorizonIntegrand P ν ℱ t :=
    { toFun := fun ω s e => indIoc Ω c t ω s * φ ω s e
      measurable_uncurry := measurable_indIoc_mul hm c t
      progressive := markedProgressivelyMeasurable_indIoc_mul hp c t
      vanishing := fun ω s e hs => by
        have : s ∉ Set.Ioc c t := fun h => hs ⟨hc.trans h.1.le, h.2⟩
        simp [indIoc, this]
      energy_ne_top := (sq_int_global_indIoc_mul hq c t t ht).ne }
  have hGa : ∀ ω s e, s ≤ c → G.toFun ω s e = 0 := fun ω s e hs => by
    have : s ∉ Set.Ioc c t := fun h => absurd h.1 (not_lt.mpr hs)
    simp [G, indIoc, this]
  exact MarkedHorizonIntegrand.integral_mulLeft N hℱ ht G hc hct.le hGa
    (stronglyMeasurable_hitInd τ hτ c) (abs_hitInd_le_one τ c)

end Window

section Linear

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)

include hℱ in
/-- **The compensated integral of a difference is the difference of the integrals.** -/
theorem stochasticIntegral_sub {φ₁ φ₂ : Ω → ℝ → E → ℝ}
    (hm₁ : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
    (hm₂ : Measurable fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)
    (hp₁ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (hp₂ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (hq₁ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hq₂ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hms : Measurable fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2)
    (hps : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => φ₁ ω s e - φ₂ ω s e)
    (hqs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegral N ℱ hℱ (fun ω s e => φ₁ ω s e - φ₂ ω s e) hms hps hqs T
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ₁ hm₁ hp₁ hq₁ T ω
        - stochasticIntegral N ℱ hℱ φ₂ hm₂ hp₂ hq₂ T ω := by
  have hsubfun : (fun ω s e => φ₁ ω s e - φ₂ ω s e)
      = fun ω s e => φ₁ ω s e + (-1 : ℝ) * φ₂ ω s e := by
    funext ω s e
    ring
  have hmn : Measurable fun p : Ω × ℝ × E => (-1 : ℝ) * φ₂ p.1 p.2.1 p.2.2 :=
    measurable_const.mul hm₂
  have hpn := markedProgressivelyMeasurable_const_mul hp₂ (-1 : ℝ)
  have hqn : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖(-1 : ℝ) * φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun T' hT' =>
    lt_top_iff_ne_top.mpr (markedEnergy_const_mul_ne_top hm₂ (hq₂ T' hT').ne (-1 : ℝ))
  have hma := measurable_uncurry_congr hsubfun hms
  have hpa := markedProgressivelyMeasurable_congr hsubfun hps
  have hqa := sq_int_global_congr hsubfun hqs
  rw [stochasticIntegral_congr_fun N hℱ (φ := fun ω s e => φ₁ ω s e - φ₂ ω s e)
    hms hps hqs hsubfun hma hpa hqa T]
  filter_upwards [stochasticIntegral_add N ℱ hℱ hm₁ hmn hp₁ hpn hq₁ hqn hma hpa hqa hT,
    stochasticIntegral_const_mul N ℱ hℱ hm₂ hp₂ hq₂ (-1 : ℝ) hmn hpn hqn hT]
    with ω hadd hneg
  rw [hadd, hneg]
  ring

include hℱ in
/-- **The compensated integral of a finite sum of integrands is the sum of their integrals.** -/
theorem exists_stochasticIntegral_finsetSum {ι : Type*}
    (H : ι → Ω → ℝ → E → ℝ)
    (hmH : ∀ i, Measurable fun p : Ω × ℝ × E => H i p.1 p.2.1 p.2.2)
    (hpH : ∀ i, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (H i))
    (hqH : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (J : Finset ι) {T : ℝ} (hT : 0 < T) :
    ∃ (hms : Measurable fun p : Ω × ℝ × E => ∑ i ∈ J, H i p.1 p.2.1 p.2.2)
      (hps : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        fun ω s e => ∑ i ∈ J, H i ω s e)
      (hqs : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖∑ i ∈ J, H i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      stochasticIntegral N ℱ hℱ (fun ω s e => ∑ i ∈ J, H i ω s e) hms hps hqs T
        =ᵐ[P] fun ω => ∑ i ∈ J,
          stochasticIntegral N ℱ hℱ (H i) (hmH i) (hpH i) (hqH i) T ω := by
  classical
  induction J using Finset.induction with
  | empty =>
    have hfun : (fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ (∅ : Finset ι), H i ω s e)
        = fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := by
      funext ω s e
      simp
    have hmz : Measurable fun (_ : Ω × ℝ × E) => (0 : ℝ) := measurable_const
    have hpz : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := markedProgressivelyMeasurable_zero ℱ
    have hqz : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ _s in Set.Icc (0 : ℝ) T', ∫⁻ _e,
        (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
      intro T' _
      simp
    refine ⟨measurable_uncurry_congr hfun.symm hmz,
      markedProgressivelyMeasurable_congr hfun.symm hpz, sq_int_global_congr hfun.symm hqz, ?_⟩
    rw [stochasticIntegral_congr_fun N hℱ
      (φ := fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ (∅ : Finset ι), H i ω s e) _ _ _ hfun
      hmz hpz hqz T]
    filter_upwards [stochasticIntegral_ae_zero_of_vanishing N hℱ
      (fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ)) hmz hpz hqz hT.le (fun _ _ _ _ => rfl)]
      with ω hω
    simpa using hω
  | insert a J ha ih =>
    obtain ⟨hms, hps, hqs, hae⟩ := ih
    have hfun : (fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ insert a J, H i ω s e)
        = fun ω s e => H a ω s e + ∑ i ∈ J, H i ω s e := by
      funext ω s e
      exact Finset.sum_insert ha
    have hma : Measurable fun p : Ω × ℝ × E =>
        H a p.1 p.2.1 p.2.2 + ∑ i ∈ J, H i p.1 p.2.1 p.2.2 := (hmH a).add hms
    have hpa : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
        fun ω s e => H a ω s e + ∑ i ∈ J, H i ω s e :=
      markedProgressivelyMeasurable_add (hpH a) hps
    have hqa : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖H a ω s e + ∑ i ∈ J, H i ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P < ⊤ :=
      markedEnergy_lt_top_of_bound (fun _ _ _ => sq_nnnorm_add_le_two_mul _ _) (hmH a) hms
        (hqH a) hqs
    refine ⟨measurable_uncurry_congr hfun.symm hma,
      markedProgressivelyMeasurable_congr hfun.symm hpa, sq_int_global_congr hfun.symm hqa, ?_⟩
    rw [stochasticIntegral_congr_fun N hℱ
      (φ := fun (ω : Ω) (s : ℝ) (e : E) => ∑ i ∈ insert a J, H i ω s e) _ _ _ hfun
      hma hpa hqa T]
    filter_upwards [stochasticIntegral_add N ℱ hℱ (hmH a) hms (hpH a) hps (hqH a) hqs hma hpa
      hqa hT, hae] with ω hadd hsum
    rw [hadd, hsum, Finset.sum_insert ha]

end Linear

end LevyStochCalc.Poisson.Compensated
