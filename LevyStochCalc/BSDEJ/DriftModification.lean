/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.Progressive
import LevyStochCalc.Brownian.ItoIntegrandComplete
import Mathlib.MeasureTheory.Covering.DensityTheorem
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# A progressive modification of a drift progressive for the right-continuous filtration

A real process that is progressively measurable for the right-continuous filtration `ℱ₊` has a
modification, equal to it almost everywhere on `Ω × [0, T]`, that is progressively measurable for
`ℱ` itself. The modification is the pointwise `limsup` of the moving averages of the process over
the windows `[s - 2c, s - c]` lying strictly to the left of `s`: each such average is
`ℱ`-progressive because it reads the process only before `s`, and Lebesgue's differentiation
theorem identifies the limit with the process at almost every time.
-/

open MeasureTheory Filter Metric
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
  {b : Ω → ℝ → ℝ} {T : ℝ}

/-! ### Moving averages over a window strictly to the left -/

/-- The mean of `b ω` over the window `[s - 2c, s - c]` of length `c` ending at distance `c` to
the left of `s`. -/
noncomputable def leftAverage (b : Ω → ℝ → ℝ) (c : ℝ) (ω : Ω) (s : ℝ) : ℝ :=
  c⁻¹ * ∫ r in Set.Icc (s - 2 * c) (s - c), b ω r

/-- The integral of a jointly measurable process over the window `[s - 2c, s - c]` is jointly
measurable in the sample point and in `s`. -/
private theorem measurable_windowIntegral {α : Type*} [MeasurableSpace α] {g : α → ℝ → ℝ}
    (hg : Measurable fun q : α × ℝ => g q.1 q.2) (c : ℝ) :
    Measurable fun p : α × ℝ => ∫ r in Set.Icc (p.2 - 2 * c) (p.2 - c), g p.1 r := by
  have hfst : Measurable fun q : (α × ℝ) × ℝ => q.1.2 := measurable_snd.comp measurable_fst
  have hSm : MeasurableSet {q : (α × ℝ) × ℝ | q.1.2 - 2 * c ≤ q.2 ∧ q.2 ≤ q.1.2 - c} :=
    (measurableSet_le (hfst.sub measurable_const) measurable_snd).inter
      (measurableSet_le measurable_snd (hfst.sub measurable_const))
  have hgm : Measurable fun q : (α × ℝ) × ℝ => g q.1.1 q.2 :=
    hg.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have hF : StronglyMeasurable fun q : (α × ℝ) × ℝ =>
      Set.indicator (Set.Icc (q.1.2 - 2 * c) (q.1.2 - c)) (fun r => g q.1.1 r) q.2 := by
    have hrw : (fun q : (α × ℝ) × ℝ =>
          Set.indicator (Set.Icc (q.1.2 - 2 * c) (q.1.2 - c)) (fun r => g q.1.1 r) q.2)
        = Set.indicator {q : (α × ℝ) × ℝ | q.1.2 - 2 * c ≤ q.2 ∧ q.2 ≤ q.1.2 - c}
          fun q : (α × ℝ) × ℝ => g q.1.1 q.2 := by
      funext q
      simp only [Set.indicator_apply, Set.mem_Icc, Set.mem_setOf_eq]
    rw [hrw]
    exact (hgm.indicator hSm).stronglyMeasurable
  have hint := hF.integral_prod_right' (ν := (volume : Measure ℝ))
  have heq : (fun p : α × ℝ => ∫ r in Set.Icc (p.2 - 2 * c) (p.2 - c), g p.1 r)
      = fun p : α × ℝ =>
        ∫ r, Set.indicator (Set.Icc (p.2 - 2 * c) (p.2 - c)) (fun r => g p.1 r) r := by
    funext p
    rw [integral_indicator measurableSet_Icc]
  rw [heq]
  exact hint.measurable

/-- The moving average of a jointly measurable process is jointly measurable. -/
theorem measurable_uncurry_leftAverage (hbm : Measurable (Function.uncurry b)) (c : ℝ) :
    Measurable (Function.uncurry (leftAverage b c)) :=
  measurable_const.mul (measurable_windowIntegral hbm c)

/-- The moving average over a window strictly to the left of the current time of a process
progressively measurable for the right-continuous filtration is progressively measurable for the
filtration itself. -/
theorem progressivelyMeasurable_leftAverage
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b) {c : ℝ} (hc : 0 < c) :
    Probability.ProgressivelyMeasurable ℱ (leftAverage b c) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hle : ℱ.rightCont (t - c) ≤ ℱ t := by
    rw [Filtration.rightCont_eq]
    exact iInf₂_le t (by linarith)
  have hB : Measurable fun q : Ω × ℝ => (Set.Iic (t - c)).indicator (b q.1) q.2 :=
    ((hbp (t - c)).mono (sup_le_sup (MeasurableSpace.comap_mono hle) le_rfl)).measurable
  have hmeas := measurable_windowIntegral
    (g := fun ω r => (Set.Iic (t - c)).indicator (b ω) r) hB c
  have hkey : (fun p : Ω × ℝ => (Set.Iic t).indicator (leftAverage b c p.1) p.2)
      = Set.indicator (Set.univ ×ˢ Set.Iic t)
        (fun p : Ω × ℝ => c⁻¹ * ∫ r in Set.Icc (p.2 - 2 * c) (p.2 - c),
          (Set.Iic (t - c)).indicator (b p.1) r) := by
    funext p
    simp only [Set.indicator_apply, Set.mem_Iic, Set.mem_prod, Set.mem_univ, true_and]
    split_ifs with hp
    · unfold leftAverage
      congr 1
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      exact (Set.indicator_of_mem (s := Set.Iic (t - c))
        (Set.mem_Iic.mpr (by linarith [hr.2])) (b p.1)).symm
    · rfl
  rw [hkey]
  exact ((measurable_const.mul hmeas).stronglyMeasurable).indicator
    (MeasurableSet.univ.prod measurableSet_Iic)

/-! ### Lebesgue differentiation along the left windows -/

/-- At almost every time the moving averages over the windows `[s - 2c n, s - c n]` of a locally
integrable function converge to its value, for any sequence of positive scales `c n` tending to
zero. -/
theorem ae_tendsto_leftAverage_of_locallyIntegrable {f : ℝ → ℝ}
    (hf : LocallyIntegrable f volume) {c : ℕ → ℝ} (hcpos : ∀ n, 0 < c n)
    (hc0 : Tendsto c atTop (𝓝 0)) :
    ∀ᵐ s : ℝ, Tendsto (fun n => (c n)⁻¹ * ∫ r in Set.Icc (s - 2 * c n) (s - c n), f r)
      atTop (𝓝 (f s)) := by
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure ℝ) hf 3]
    with s hs
  have hδ : Tendsto (fun n => c n / 2) atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨by simpa using hc0.div_const 2, Eventually.of_forall fun n => ?_⟩
    exact Set.mem_Ioi.mpr (by linarith [hcpos n])
  have hmem : ∀ᶠ n in atTop, s ∈ closedBall (s - 3 * c n / 2) (3 * (c n / 2)) := by
    refine Eventually.of_forall fun n => ?_
    rw [mem_closedBall, Real.dist_eq, show s - (s - 3 * c n / 2) = 3 * c n / 2 by ring,
      abs_of_nonneg (by linarith [hcpos n])]
    linarith
  refine Tendsto.congr (fun n => ?_) (hs (fun n => s - 3 * c n / 2) (fun n => c n / 2) hδ hmem)
  have hball : closedBall (s - 3 * c n / 2) (c n / 2) = Set.Icc (s - 2 * c n) (s - c n) := by
    rw [Real.closedBall_eq_Icc, show s - 3 * c n / 2 - c n / 2 = s - 2 * c n by ring,
      show s - 3 * c n / 2 + c n / 2 = s - c n by ring]
  rw [setAverage_eq, hball, Real.volume_real_Icc_of_le (by linarith [hcpos n]),
    show s - c n - (s - 2 * c n) = c n by ring, smul_eq_mul]

/-! ### The modification -/

/-- The `limsup` of the moving averages of `b` over the windows
`[s - 2 / (n + 1), s - 1 / (n + 1)]`, truncated to the horizon `[0, T]`. -/
noncomputable def leftAverageLimit (b : Ω → ℝ → ℝ) (T : ℝ) : Ω → ℝ → ℝ := fun ω s =>
  (Set.Icc (0 : ℝ) T).indicator
    (fun s => limsup (fun n : ℕ => leftAverage b (1 / ((n : ℝ) + 1)) ω s) atTop) s

/-- The scales `1 / (n + 1)` are positive. -/
private theorem one_div_succ_pos (n : ℕ) : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity

/-- The limit of the moving averages of a jointly measurable process is jointly measurable. -/
theorem measurable_uncurry_leftAverageLimit (hbm : Measurable (Function.uncurry b)) (T : ℝ) :
    Measurable (Function.uncurry (leftAverageLimit b T)) := by
  have hM : Measurable fun p : Ω × ℝ =>
      limsup (fun n : ℕ => leftAverage b (1 / ((n : ℝ) + 1)) p.1 p.2) atTop :=
    Measurable.limsup fun n => measurable_uncurry_leftAverage hbm (1 / ((n : ℝ) + 1))
  have hrw : (fun p : Ω × ℝ => leftAverageLimit b T p.1 p.2)
      = Set.indicator ((fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T)
        fun p : Ω × ℝ => limsup (fun n : ℕ => leftAverage b (1 / ((n : ℝ) + 1)) p.1 p.2) atTop := by
    funext p
    by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem (s := (fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T) hp]
      exact Set.indicator_of_mem (s := Set.Icc (0 : ℝ) T) hp _
    · rw [Set.indicator_of_notMem (s := (fun p : Ω × ℝ => p.2) ⁻¹' Set.Icc (0 : ℝ) T) hp]
      exact Set.indicator_of_notMem (s := Set.Icc (0 : ℝ) T) hp _
  change Measurable fun p : Ω × ℝ => leftAverageLimit b T p.1 p.2
  rw [hrw]
  exact hM.indicator (measurable_snd measurableSet_Icc)

/-- The limit of the moving averages of a process progressively measurable for the
right-continuous filtration is progressively measurable for the filtration itself. -/
theorem progressivelyMeasurable_leftAverageLimit
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ (leftAverageLimit b T) :=
  Brownian.Ito.progressivelyMeasurable_indicator_Icc
    (Probability.ProgressivelyMeasurable.limsup fun n =>
      progressivelyMeasurable_leftAverage hbp (one_div_succ_pos n)) T

/-- The limit of the moving averages vanishes off the horizon. -/
theorem leftAverageLimit_of_notMem (b : Ω → ℝ → ℝ) (T : ℝ) {ω : Ω} {s : ℝ}
    (hs : s ∉ Set.Icc (0 : ℝ) T) : leftAverageLimit b T ω s = 0 :=
  Set.indicator_of_notMem hs _

/-- A process of finite energy on the horizon that vanishes off it is integrable at almost every
sample point. -/
private theorem ae_integrable (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0) :
    ∀ᵐ ω ∂P, Integrable (b ω) volume := by
  have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hbm.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  filter_upwards [ae_lt_top hmeas hbq] with ω hω
  have hfm : Measurable (b ω) := hbm.comp (measurable_const.prodMk measurable_id)
  have hsq : HasFiniteIntegral (fun s => b ω s ^ 2) (volume.restrict (Set.Icc (0 : ℝ) T)) := by
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => ?_)) hω
    rw [← ENNReal.coe_pow, ← nnnorm_pow]
    rfl
  have hIO : IntegrableOn (b ω) (Set.Icc (0 : ℝ) T) volume :=
    ((memLp_two_iff_integrable_sq hfm.aestronglyMeasurable).mpr
      ⟨(hfm.pow_const 2).aestronglyMeasurable, hsq⟩).integrable (by norm_num)
  have hrw : b ω = (Set.Icc (0 : ℝ) T).indicator (b ω) := by
    funext s
    by_cases hs : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs, hbz ω s hs]
  rw [hrw]
  exact (integrable_indicator_iff measurableSet_Icc).mpr hIO

/-- The limit of the moving averages agrees with the process at almost every time on the
horizon, at almost every sample point. -/
theorem ae_ae_leftAverageLimit_eq (hbm : Measurable (Function.uncurry b))
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), leftAverageLimit b T ω s = b ω s := by
  filter_upwards [ae_integrable hbm hbq hbz] with ω hω
  have hae := ae_tendsto_leftAverage_of_locallyIntegrable hω.locallyIntegrable
    (c := fun n : ℕ => 1 / ((n : ℝ) + 1)) one_div_succ_pos
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ae_restrict_of_ae (hae.mono fun s hs => ?_)
  by_cases hsT : s ∈ Set.Icc (0 : ℝ) T
  · rw [leftAverageLimit, Set.indicator_of_mem hsT]
    exact hs.limsup_eq
  · rw [leftAverageLimit_of_notMem b T hsT, hbz ω s hsT]

/-- A drift of finite energy that vanishes off the horizon and is progressively measurable for
the right-continuous filtration has a modification, equal to it almost everywhere on
`Ω × [0, T]`, that is progressively measurable for the filtration itself. -/
theorem exists_progressive_modification_of_rightCont (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable ℱ.rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) :
    ∃ b' : Ω → ℝ → ℝ, Measurable (Function.uncurry b') ∧
      Probability.ProgressivelyMeasurable ℱ b' ∧
      (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b' ω s = 0) ∧ Brownian.Ito.energy P T b' ≠ ⊤ ∧
      ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), b' p.1 p.2 = b p.1 p.2 := by
  have hae := ae_ae_leftAverageLimit_eq hbm hbz hbq
  have hbm' := measurable_uncurry_leftAverageLimit hbm T
  have henergy : Brownian.Ito.energy P T (leftAverageLimit b T) = Brownian.Ito.energy P T b := by
    refine lintegral_congr_ae ?_
    filter_upwards [hae] with ω hω
    exact lintegral_congr_ae (hω.mono fun s hs => by simp only [hs])
  refine ⟨leftAverageLimit b T, hbm', progressivelyMeasurable_leftAverageLimit hbp T,
    fun ω s hs => leftAverageLimit_of_notMem b T hs, by rw [henergy]; exact hbq, ?_⟩
  have hset : MeasurableSet {p : Ω × ℝ | leftAverageLimit b T p.1 p.2 = b p.1 p.2} :=
    measurableSet_eq_fun hbm' hbm
  exact (Measure.ae_prod_iff_ae_ae hset).mpr hae

end LevyStochCalc.BSDEJ.Generator
