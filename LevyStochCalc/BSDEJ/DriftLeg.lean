/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.Progressive
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.BSDEJ.SupBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.SetToL1

/-!
# The drift leg of a Picard iterate

For a drift `b : Ω → ℝ → ℝ` of finite energy on the horizon `[0, T]` and vanishing off it, the
drift leg is the primitive `t ↦ ∫_{[0, t]} b ω s ds`, restricted to the sample points on which
`b ω` is integrable over `[0, T]` and set to `0` elsewhere. That restriction is a `P`-conull set,
so the drift leg is a version of the raw primitive, and on it every path is the primitive of a
globally integrable function, hence continuous.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.integrablePaths` — the sample points whose drift path is integrable
  over the horizon.
* `LevyStochCalc.BSDEJ.Solves.driftLeg` — the primitive of the drift, cut to those sample points.

## Main statements

* `driftLeg_ae_eq` — the drift leg is a version of the raw primitive.
* `setIntegral_Icc_eq_intervalIntegral` — the integral over `[0, t]` is the interval integral
  from `0` to `t`, for every real `t`.
* `continuous_driftLeg` — every path of the drift leg is continuous.
* `stronglyAdapted_driftLeg`, `adapted_driftLeg` — the drift leg is adapted to the filtration of
  the drift.
* `adapted_driftLeg_of_rightCont` — the drift leg is adapted to the filtration already when the
  drift is progressive for the right-continuous filtration.
* `measurable_uncurry_driftLeg` — the drift leg is jointly measurable in time and sample point.
* `driftLeg_sub_ae` — the drift leg at the horizon splits at an intermediate time.
* `lintegral_biSup_sq_driftLeg_lt_top` — the drift leg has finite `S²` seminorm.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### The paths on which the drift is integrable -/

/-- The set of sample points whose drift path is integrable over the horizon `[0, T]`. -/
def integrablePaths (b : Ω → ℝ → ℝ) (T : ℝ) : Set Ω :=
  {ω | IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume}

/-- The set of sample points with an integrable drift path is measurable. -/
theorem measurableSet_integrablePaths (hbm : Measurable (Function.uncurry b)) :
    MeasurableSet (integrablePaths b T) :=
  measurableSet_integrable (μ := volume.restrict (Set.Icc (0 : ℝ) T)) hbm.stronglyMeasurable

/-- The extended norm of a square is the square of the extended norm. -/
private theorem enorm_sq_eq (x : ℝ) : ‖x ^ 2‖ₑ = (‖x‖₊ : ℝ≥0∞) ^ 2 := by
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl

/-- A function with finite energy on a bounded window is square integrable there. -/
private theorem memLp_two_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {c : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) c, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    MemLp f 2 (volume.restrict (Set.Icc (0 : ℝ) c)) := by
  refine (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr ?_
  refine ⟨(hf.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  exact lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => enorm_sq_eq (f s))) hfin

/-- A function with finite energy on a bounded window is integrable there. -/
private theorem integrableOn_of_lintegral_sq_lt_top {f : ℝ → ℝ} (hf : Measurable f) {c : ℝ}
    (hfin : ∫⁻ s in Set.Icc (0 : ℝ) c, (‖f s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) :
    IntegrableOn f (Set.Icc (0 : ℝ) c) volume := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) c)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  exact (memLp_two_of_lintegral_sq_lt_top hf hfin).integrable (by norm_num)

/-- A drift of finite energy on the horizon has an integrable path at almost every sample
point. -/
theorem ae_mem_integrablePaths (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) : ∀ᵐ ω ∂P, ω ∈ integrablePaths b T := by
  have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hbm.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  have hae : ∀ᵐ ω ∂P, (∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) < ⊤ :=
    ae_lt_top hmeas hbq
  filter_upwards [hae] with ω hω
  exact integrableOn_of_lintegral_sq_lt_top (hbm.comp (measurable_const.prodMk measurable_id)) hω

/-! ### The drift leg -/

/-- The primitive `t ↦ ∫_{[0, t]} b ω s ds` of the drift, cut to the sample points on which the
drift is integrable over the horizon. -/
noncomputable def driftLeg (b : Ω → ℝ → ℝ) (T : ℝ) : ℝ → Ω → ℝ := fun t =>
  (integrablePaths b T).indicator fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s

/-- On a sample point with an integrable drift path the drift leg is the primitive. -/
theorem driftLeg_of_mem {ω : Ω} (hω : ω ∈ integrablePaths b T) (t : ℝ) :
    driftLeg b T t ω = ∫ s in Set.Icc (0 : ℝ) t, b ω s :=
  Set.indicator_of_mem hω _

/-- Off the sample points with an integrable drift path the drift leg vanishes. -/
theorem driftLeg_of_notMem {ω : Ω} (hω : ω ∉ integrablePaths b T) (t : ℝ) :
    driftLeg b T t ω = 0 :=
  Set.indicator_of_notMem hω _

/-- The drift leg is a version of the primitive of the drift. -/
theorem driftLeg_ae_eq (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (t : ℝ) :
    driftLeg b T t =ᵐ[P] fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s := by
  filter_upwards [ae_mem_integrablePaths hbm hbq] with ω hω
  exact driftLeg_of_mem hω t

/-- For a drift vanishing off the horizon the integral over `[0, t]` is the interval integral
from `0` to `t`, at every real time. -/
theorem setIntegral_Icc_eq_intervalIntegral (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (ω : Ω) (t : ℝ) : ∫ s in Set.Icc (0 : ℝ) t, b ω s = ∫ s in (0 : ℝ)..t, b ω s := by
  rcases le_or_gt 0 t with ht | ht
  · rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
  · have h0 : Set.EqOn (b ω) (fun _ => (0 : ℝ)) (Set.Ioo t (0 : ℝ)) := fun s hs =>
      hbz ω s fun hc => absurd hc.1 (not_le.mpr hs.2)
    have hIoo : ∫ s in Set.Ioo t (0 : ℝ), b ω s = 0 := by
      rw [setIntegral_congr_fun measurableSet_Ioo h0]
      simp
    rw [Set.Icc_eq_empty (not_le.mpr ht), setIntegral_empty,
      intervalIntegral.integral_of_ge ht.le, integral_Ioc_eq_integral_Ioo, hIoo, neg_zero]

/-- Every path of the drift leg of a drift vanishing off the horizon is continuous. -/
theorem continuous_driftLeg (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0) (ω : Ω) :
    Continuous fun t => driftLeg b T t ω := by
  by_cases hω : ω ∈ integrablePaths b T
  · have hind : Integrable ((Set.Icc (0 : ℝ) T).indicator (b ω)) volume :=
      (integrable_indicator_iff measurableSet_Icc).mpr hω
    have hint : Integrable (b ω) volume := by
      refine hind.congr (Filter.Eventually.of_forall fun s => ?_)
      by_cases hs : s ∈ Set.Icc (0 : ℝ) T
      · rw [Set.indicator_of_mem hs]
      · rw [Set.indicator_of_notMem hs, hbz ω s hs]
    have heq : (fun t => driftLeg b T t ω) = fun t => ∫ s in (0 : ℝ)..t, b ω s := by
      funext t
      rw [driftLeg_of_mem hω t, setIntegral_Icc_eq_intervalIntegral hbz ω t]
    rw [heq]
    exact hint.continuous_primitive 0
  · have heq : (fun t => driftLeg b T t ω) = fun _ => (0 : ℝ) := by
      funext t
      exact driftLeg_of_notMem hω t
    rw [heq]
    exact continuous_const

/-- The drift leg of a progressively measurable drift of finite energy is strongly adapted,
provided the filtration contains the `P`-null sets at time `0`. -/
theorem stronglyAdapted_driftLeg (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ b) (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    StronglyAdapted ℱ (driftLeg b T) := by
  intro t
  rcases le_or_gt 0 t with ht | ht
  · have hnullc : P (integrablePaths b T)ᶜ = 0 :=
      ae_iff.mp (ae_mem_integrablePaths hbm hbq)
    have h0 : MeasurableSet[ℱ 0] (integrablePaths b T)ᶜ :=
      hnull _ (measurableSet_integrablePaths hbm).compl hnullc
    have h1 : MeasurableSet[ℱ 0] (integrablePaths b T) := by
      simpa using h0.compl
    have hgood : MeasurableSet[ℱ t] (integrablePaths b T) := ℱ.mono ht _ h1
    have hsm : StronglyMeasurable[ℱ t] fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s :=
      hbp.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self volume
    exact hsm.indicator hgood
  · have heq : driftLeg b T t = fun _ => (0 : ℝ) := by
      funext ω
      by_cases hω : ω ∈ integrablePaths b T
      · rw [driftLeg_of_mem hω t, Set.Icc_eq_empty (not_le.mpr ht), setIntegral_empty]
      · exact driftLeg_of_notMem hω t
    rw [heq]
    exact stronglyMeasurable_const

/-- The drift leg of a progressively measurable drift of finite energy is adapted, provided the
filtration contains the `P`-null sets at time `0`. -/
theorem adapted_driftLeg (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ b) (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ (driftLeg b T) := fun t =>
  (stronglyAdapted_driftLeg hbm hbp hbq hnull t).measurable

/-- The drift leg is adapted to the right-continuous filtration. -/
theorem adapted_driftLeg_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ b) (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ.rightCont (driftLeg b T) := fun t =>
  (adapted_driftLeg hbm hbp hbq hnull t).mono (ℱ.le_rightCont t) le_rfl

/-- The primitive of a drift over `[0, t]`, cut to the sample points with an integrable drift
path, is measurable before `t` already when the drift is progressively measurable for the
right-continuous filtration. -/
theorem stronglyMeasurable_setIntegral_of_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) {t : ℝ}
    (ht : 0 ≤ t) :
    StronglyMeasurable[ℱ t] fun ω =>
      (integrablePaths b T).indicator (fun ω => ∫ s in Set.Icc (0 : ℝ) t, b ω s) ω := by
  have hnullc : P (integrablePaths b T)ᶜ = 0 := ae_iff.mp (ae_mem_integrablePaths hbm hbq)
  have h0 : MeasurableSet[ℱ 0] (integrablePaths b T)ᶜ :=
    hnull _ (measurableSet_integrablePaths hbm).compl hnullc
  have h1 : MeasurableSet[ℱ 0] (integrablePaths b T) := by simpa using h0.compl
  have hgood : MeasurableSet[ℱ t] (integrablePaths b T) := ℱ.mono ht _ h1
  have hstep : ∀ n : ℕ, StronglyMeasurable[ℱ t] (driftLeg b T (t - 1 / ((n : ℝ) + 1))) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hle : ℱ.rightCont (t - 1 / ((n : ℝ) + 1)) ≤ ℱ t := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le t (by linarith)
    exact ((hbp.stronglyMeasurable_setIntegral measurableSet_Icc Set.Icc_subset_Iic_self
      volume).mono hle).indicator hgood
  have hc : Filter.Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds t) := by
    have h : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (nhds 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Filter.Tendsto (fun n : ℕ => t - 1 / ((n : ℝ) + 1)) Filter.atTop (nhds (t - 0)) :=
      tendsto_const_nhds.sub h
    simpa using h2
  have hlim : Filter.Tendsto (fun n : ℕ => driftLeg b T (t - 1 / ((n : ℝ) + 1)))
      Filter.atTop (nhds (driftLeg b T t)) := by
    rw [tendsto_pi_nhds]
    intro ω
    exact ((continuous_driftLeg hbz ω).tendsto t).comp hc
  exact stronglyMeasurable_of_tendsto (m := ℱ t) Filter.atTop hstep hlim

/-- The drift leg of a drift of finite energy that vanishes off the horizon and is
progressively measurable for the right-continuous filtration is adapted to the filtration
itself, provided the filtration contains the `P`-null sets at time `0`. -/
theorem adapted_driftLeg_of_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ (driftLeg b T) := by
  intro t
  rcases le_or_gt 0 t with ht | ht
  · exact (stronglyMeasurable_setIntegral_of_rightCont hbm hbp hbz hbq hnull ht).measurable
  · have heq : driftLeg b T t = fun _ => (0 : ℝ) := by
      funext ω
      by_cases hω : ω ∈ integrablePaths b T
      · rw [driftLeg_of_mem hω t, Set.Icc_eq_empty (not_le.mpr ht), setIntegral_empty]
      · exact driftLeg_of_notMem hω t
    rw [heq]
    exact measurable_const

/-- The drift leg of a drift progressively measurable for the right-continuous filtration is
adapted to that filtration. -/
theorem adapted_driftLeg_rightCont_of_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    Adapted ℱ.rightCont (driftLeg b T) := fun t =>
  (adapted_driftLeg_of_rightCont hbm hbp hbz hbq hnull t).mono (ℱ.le_rightCont t) le_rfl

/-- The drift leg is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_driftLeg (hbm : Measurable (Function.uncurry b)) :
    Measurable (Function.uncurry (driftLeg b T)) := by
  have hset : MeasurableSet {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1} := by
    have heq : {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1}
        = {q : (ℝ × Ω) × ℝ | (0 : ℝ) ≤ q.2} ∩ {q : (ℝ × Ω) × ℝ | q.2 ≤ q.1.1} := by
      ext q
      exact Set.mem_Icc
    rw [heq]
    exact (measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst.fst)
  have hb : Measurable fun q : (ℝ × Ω) × ℝ => b q.1.2 q.2 :=
    hbm.comp (measurable_fst.snd.prodMk measurable_snd)
  have hF : StronglyMeasurable fun q : (ℝ × Ω) × ℝ =>
      (Set.Icc (0 : ℝ) q.1.1).indicator (b q.1.2) q.2 := by
    have heq : (fun q : (ℝ × Ω) × ℝ => (Set.Icc (0 : ℝ) q.1.1).indicator (b q.1.2) q.2)
        = {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1}.indicator
          fun q => b q.1.2 q.2 := by
      funext q
      by_cases hq : q.2 ∈ Set.Icc (0 : ℝ) q.1.1
      · have hq' : q ∈ {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1} := hq
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq']
      · have hq' : q ∉ {q : (ℝ × Ω) × ℝ | q.2 ∈ Set.Icc (0 : ℝ) q.1.1} := hq
        rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq']
    rw [heq]
    exact (hb.indicator hset).stronglyMeasurable
  have hint : StronglyMeasurable fun p : ℝ × Ω => ∫ s in Set.Icc (0 : ℝ) p.1, b p.2 s := by
    have heq : (fun p : ℝ × Ω => ∫ s in Set.Icc (0 : ℝ) p.1, b p.2 s)
        = fun p : ℝ × Ω => ∫ s, (Set.Icc (0 : ℝ) p.1).indicator (b p.2) s := by
      funext p
      rw [integral_indicator measurableSet_Icc]
    rw [heq]
    exact hF.integral_prod_right'
  have hsnd : MeasurableSet {p : ℝ × Ω | p.2 ∈ integrablePaths b T} :=
    measurable_snd (measurableSet_integrablePaths hbm)
  have heq : Function.uncurry (driftLeg b T)
      = {p : ℝ × Ω | p.2 ∈ integrablePaths b T}.indicator
        fun p => ∫ s in Set.Icc (0 : ℝ) p.1, b p.2 s := by
    funext p
    by_cases hp : p.2 ∈ integrablePaths b T
    · have hp' : p ∈ {p : ℝ × Ω | p.2 ∈ integrablePaths b T} := hp
      rw [Set.indicator_of_mem hp']
      exact driftLeg_of_mem hp p.1
    · have hp' : p ∉ {p : ℝ × Ω | p.2 ∈ integrablePaths b T} := hp
      rw [Set.indicator_of_notMem hp']
      exact driftLeg_of_notMem hp p.1
  rw [heq]
  exact hint.measurable.indicator hsnd

/-- The drift leg at the horizon is almost surely the drift leg at an intermediate time plus the
integral of the drift over the remaining window. -/
theorem driftLeg_sub_ae (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) {t : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    driftLeg b T T =ᵐ[P] fun ω => driftLeg b T t ω + ∫ s in Set.Icc t T, b ω s := by
  filter_upwards [ae_mem_integrablePaths hbm hbq] with ω hω
  have hI : IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume := hω
  have h1 : IntegrableOn (b ω) (Set.Icc (0 : ℝ) t) volume :=
    hI.mono_set (Set.Icc_subset_Icc le_rfl htT)
  have h2 : IntegrableOn (b ω) (Set.Ioc t T) volume :=
    hI.mono_set fun s hs => ⟨ht.trans hs.1.le, hs.2⟩
  have hdisj : Disjoint (Set.Icc (0 : ℝ) t) (Set.Ioc t T) :=
    (Set.Iic_disjoint_Ioi le_rfl).mono Set.Icc_subset_Iic_self Set.Ioc_subset_Ioi_self
  have hsplit : ∫ s in Set.Icc t T, b ω s = ∫ s in Set.Ioc t T, b ω s :=
    integral_Icc_eq_integral_Ioc
  rw [driftLeg_of_mem hω T, driftLeg_of_mem hω t, hsplit,
    ← Set.Icc_union_Ioc_eq_Icc ht htT, setIntegral_union hdisj measurableSet_Ioc h1 h2]

/-- The drift leg of a drift of finite energy has finite `S²` seminorm on the horizon. -/
theorem lintegral_biSup_sq_driftLeg_lt_top (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
  have key : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    by_cases hω : ω ∈ integrablePaths b T
    · have hslice : Measurable (b ω) := hbm.comp (measurable_const.prodMk measurable_id)
      calc (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2)
          = ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖∫ s in Set.Icc (0 : ℝ) t, b ω s‖₊ : ℝ≥0∞) ^ 2 := by
            simp_rw [driftLeg_of_mem hω]
        _ ≤ (∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ∂volume) ^ 2 :=
            SupBound.biSup_sq_setIntegral_le b T ω
        _ ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
            SupBound.sq_lintegral_le_ofReal_mul_lintegral_sq T
              hslice.aestronglyMeasurable.enorm
    · simp [driftLeg_of_notMem hω]
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal T
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ∂P := lintegral_mono key
    _ = ENNReal.ofReal T * Brownian.Ito.energy P T b :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hbq.lt_top

end LevyStochCalc.BSDEJ.Solves
