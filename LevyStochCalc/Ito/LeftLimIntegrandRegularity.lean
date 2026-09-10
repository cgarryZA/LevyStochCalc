/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSplittingPath

/-!
# Regularity of a jump coefficient read at the left limits of a path

A path having left limits everywhere meets, at each time, the limit along the dyadic grid points
below that time. The left limits are therefore a countable limit of evaluations of the path, so
they are jointly measurable when the path is, and predictable — hence progressively measurable —
when the path is adapted. Composing with a jointly measurable jump coefficient carries these to
the left-limit jump integrand. Its energy on a horizon is that of the integrand along the path
itself, because a càdlàg path meets its left limits at all but countably many positive times.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.measurable_uncurry_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.progressivelyMeasurable_leftLimPathAt` — joint measurability
  and progressive measurability of the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_comp_state` — a jointly
  measurable function of the time, a progressively measurable state and the mark is marked
  progressively measurable.
* `LevyStochCalc.Ito.JumpSplitting.measurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt`,
  `LevyStochCalc.Ito.JumpSplitting.lintegral_sq_jumpCoeff_leftLimPathAt_eq` — the three
  admissibility data of the left-limit jump integrand.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Probability

/-- The dyadic grid point below a time depends measurably on the time. -/
theorem measurable_leftGridPoint (k : ℕ) : Measurable (leftGridPoint k) := by
  unfold leftGridPoint
  fun_prop

end LevyStochCalc.Probability

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {n : ℕ}

section Measurability

variable {Xp : ℝ → Ω → Fin n → ℝ}

/-- **The left limits of a jointly measurable path having left limits everywhere are jointly
measurable.** -/
theorem measurable_uncurry_leftLimPathAt (hXm : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) :
    Measurable fun q : ℝ × Ω => leftLimPathAt Xp q.1 q.2 := by
  refine measurable_pi_iff.mpr fun i => ?_
  have hrw : (fun q : ℝ × Ω => leftLimPathAt Xp q.1 q.2 i)
      = fun q : ℝ × Ω => limsup (fun k : ℕ => Xp (leftGridPoint k q.1) q.2 i) atTop := by
    funext q
    exact (((tendsto_nhdsLT_leftLimPathAt (fun j => hleft q.2 q.1 j) i).comp
      (tendsto_leftGridPoint q.1)).limsup_eq).symm
  rw [hrw]
  refine Measurable.limsup fun k => ?_
  exact ((measurable_pi_apply i).comp hXm).comp
    (((measurable_leftGridPoint k).comp measurable_fst).prodMk measurable_snd)

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The left limits of an adapted path having left limits everywhere are progressively
measurable.** -/
theorem progressivelyMeasurable_leftLimPathAt (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) (i : Fin n) :
    ProgressivelyMeasurable ℱ fun ω s => leftLimPathAt Xp s ω i := by
  refine Predictable.progressivelyMeasurable hℱ0 ?_
  letI : MeasurableSpace (ℝ × Ω) := predictableSigma ℱ
  refine Measurable.stronglyMeasurable ?_
  exact measurable_predictableSigma_of_tendsto_leftGridPoint
    (Z := fun t ω => Xp t ω i) (Y := fun s ω => leftLimPathAt Xp s ω i)
    (fun t => (measurable_pi_apply i).comp (hXadapt t))
    (fun s ω => (tendsto_nhdsLT_leftLimPathAt (fun j => hleft ω s j) i).comp
      (tendsto_leftGridPoint s))

/-- **A jointly measurable function of the time, a progressively measurable state and the mark is
marked progressively measurable.** -/
theorem markedProgressivelyMeasurable_comp_state {Λ : ℝ → Ω → Fin n → ℝ}
    (hΛ : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => Λ s ω i)
    {F : ℝ → (Fin n → ℝ) → E → ℝ}
    (hF : Measurable fun q : ℝ × (Fin n → ℝ) × E => F q.1 q.2.1 q.2.2) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => F s (Λ s ω) e := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  refine Measurable.stronglyMeasurable ?_
  set G : Ω × ℝ → Fin n → ℝ :=
    fun p i => (Set.Iic t).indicator (fun s => Λ s p.1 i) p.2 with hG_def
  have hGm : Measurable G :=
    measurable_pi_lambda _ fun i => ((hΛ i) t).measurable
  have hSt : MeasurableSet {p : Ω × ℝ × E | p.2.1 ≤ t} :=
    measurable_snd.fst measurableSet_Iic
  have hrw : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => F s (Λ s p.1) p.2.2) p.2.1)
      = {p : Ω × ℝ × E | p.2.1 ≤ t}.indicator
        fun p => F p.2.1 (G (p.1, p.2.1)) p.2.2 := by
    funext p
    by_cases hp : p.2.1 ≤ t
    · have hΛp : G (p.1, p.2.1) = Λ p.2.1 p.1 := by
        funext i
        simp only [hG_def, Set.indicator_of_mem (Set.mem_Iic.mpr hp)]
      rw [Set.indicator_of_mem (Set.mem_Iic.mpr hp),
        Set.indicator_of_mem (show p ∈ {p : Ω × ℝ × E | p.2.1 ≤ t} from hp), hΛp]
    · rw [Set.indicator_of_notMem (fun hmem => hp (Set.mem_Iic.mp hmem)),
        Set.indicator_of_notMem (show p ∉ {p : Ω × ℝ × E | p.2.1 ≤ t} from hp)]
  rw [hrw]
  refine Measurable.indicator ?_ hSt
  exact hF.comp (measurable_snd.fst.prodMk
    ((hGm.comp (measurable_fst.prodMk measurable_snd.fst)).prodMk measurable_snd.snd))

end Measurability

section Coefficient

variable {d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E} {Xp : ℝ → Ω → Fin n → ℝ}

/-- **The jump coefficient read at the left limits of a jointly measurable path having left
limits everywhere is jointly measurable.** -/
theorem measurable_jumpCoeff_leftLimPathAt (hXm : Measurable fun q : ℝ × Ω => Xp q.1 q.2)
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) (i : Fin n)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i) :
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i := by
  have hΛ : Measurable fun p : Ω × ℝ × E => leftLimPathAt Xp p.2.1 p.1 :=
    (measurable_uncurry_leftLimPathAt hXm hleft).comp
      (measurable_snd.fst.prodMk measurable_fst)
  exact hγ.comp (measurable_snd.fst.prodMk (hΛ.prodMk measurable_snd.snd))

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- **The jump coefficient read at the left limits of an adapted path having left limits
everywhere is marked progressively measurable.** -/
theorem markedProgressivelyMeasurable_jumpCoeff_leftLimPathAt
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t) (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (Xp t))
    (hleft : ∀ (ω : Ω) (t : ℝ) (j : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω j) (𝓝[<] t) (𝓝 L)) (i : Fin n)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i :=
  markedProgressivelyMeasurable_comp_state
    (fun j => progressivelyMeasurable_leftLimPathAt hℱ0 hXadapt hleft j)
    (F := fun s y e => coeffs.γ s y e i) hγ

end Coefficient

section Energy

variable {P : Measure Ω} {ν : Measure E} {d : ℕ} {coeffs : Setting.JumpDiffusionCoeffs n d E}
  {Xp : ℝ → Ω → Fin n → ℝ}

/-- The energy of a marked integrand on a horizon is unchanged when the process it is evaluated
along is replaced by one meeting it at all but countably many positive times. -/
theorem lintegral_sq_congr_of_countable_ne {V : Type*} {X Xm : ℝ → Ω → V}
    (F : ℝ → V → E → ℝ)
    (hXm : ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧ Xm s ω ≠ X s ω}.Countable) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖F s (Xm s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖F s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_ae_forall_eq_of_countable_ne (P := P) (E := E) F hXm T] with ω hω
  refine lintegral_congr_ae ?_
  filter_upwards [hω] with s hs
  exact lintegral_congr fun e => by rw [hs e]

/-- **The left-limit jump integrand of a càdlàg path has the energy of the integrand along the
path itself.** -/
theorem lintegral_sq_jumpCoeff_leftLimPathAt_eq
    (hcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (i : Fin n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖coeffs.γ s (Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P :=
  lintegral_sq_congr_of_countable_ne (ν := ν) (fun s y e => coeffs.γ s y e i)
    (ae_countable_setOf_pos_ne_leftLimPathAt (P := P) Xp hcadlag) T

end Energy

end LevyStochCalc.Ito.JumpSplitting
