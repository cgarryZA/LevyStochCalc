/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaIncrement
import LevyStochCalc.Ito.CappedJumpSumMeasurable

/-!
# Increments read along a random vector known at the earlier stopping time

The increment between two ordered stopping times of an integrand built from a path translated by
a random vector known at the earlier time is supported on the region strictly after that time,
where the translation is already known: there the translated path is the path plus the cut-off
vector, which is measurable for the σ-algebra at the running time because the region is a
countable union of rectangles `{σ ≤ q} × (q, t]`. The increment is therefore progressively
measurable without any restriction on the range of the vector or on that of the stopping times.

## Main statements

* `LevyStochCalc.Brownian.Ito.measurable_indicator_shiftRegion` — a random vector known at a
  stopping time, cut to the times strictly after it and up to a horizon, is measurable for the
  σ-algebra at that horizon on the product with the time axis.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift` — the increment between
  two ordered stopping times of an integrand read along a random vector known at the earlier one
  is progressively measurable.
* `LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub_shift` — that increment has
  measurable uncurrying.
* `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_stopped_sub_cappedJumpSumAt` — the
  increment between consecutive capped arrival times of an integrand read along the capped
  left-limit jump sum is progressively measurable.
* `LevyStochCalc.Ito.JumpFormula.measurable_uncurry_stopped_sub_cappedJumpSumAt` — that
  increment has measurable uncurrying.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory

universe u v

section ShiftRegion

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {E : Type*} [MeasurableSpace E] [Zero E]
  {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}

/-- A random vector known at a stopping time, read as zero up to that time and after a horizon,
is measurable for the σ-algebra at that horizon on the product with the time axis. -/
theorem measurable_indicator_shiftRegion (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    {c : Ω → E} (hc : Measurable[hσ.measurableSpace] c) (t : ℝ) :
    Measurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
      (Set.indicator {p : Ω × ℝ | σ p.1 < ((p.2 : ℝ) : WithTop ℝ) ∧ p.2 ≤ t}
        fun p => c p.1) := by
  letI : MeasurableSpace Ω := ℱ t
  set U : Set (Ω × ℝ) := {p : Ω × ℝ | σ p.1 < ((p.2 : ℝ) : WithTop ℝ) ∧ p.2 ≤ t} with hUdef
  have hU : MeasurableSet U := by
    have heq : U = (Set.univ ×ˢ Set.Iic t) \ Probability.stoppedRegion σ t := by
      ext p
      simp only [hUdef, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_prod, Set.mem_univ, Set.mem_Iic,
        true_and, Probability.mem_stoppedRegion, not_and, not_le]
      exact ⟨fun h => ⟨h.2, fun _ => h.1⟩, fun h => ⟨h.2 h.1, h.1⟩⟩
    rw [heq]
    exact (MeasurableSet.univ.prod measurableSet_Iic).diff
      (Probability.measurableSet_stoppedRegion hσ t)
  intro B hB
  have hUB : MeasurableSet (U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B) := by
    have hcov : U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B
        = ⋃ q : ℚ, (c ⁻¹' B ∩ {ω : Ω | σ ω ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)})
            ×ˢ (Set.Ioi (q : ℝ) ∩ Set.Iic t) := by
      ext p
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        have hne : σ p.1 ≠ ⊤ := by
          intro htop
          rw [htop] at h1
          exact absurd h1 (by simp)
        obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
        rw [← hr] at h1
        have hrlt : r < p.2 := by exact_mod_cast h1
        obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hrlt
        refine Set.mem_iUnion.mpr ⟨q, ⟨h3, ?_⟩, hq2, h2⟩
        change σ p.1 ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ)
        rw [← hr]
        have hmin : r ≤ min (q : ℝ) t := le_min hq1.le (hq1.le.trans (hq2.le.trans h2))
        exact_mod_cast hmin
      · intro hmem
        obtain ⟨q, ⟨h3, h4⟩, h5, h6⟩ := Set.mem_iUnion.mp hmem
        refine ⟨⟨?_, h6⟩, h3⟩
        calc σ p.1 ≤ ((min (q : ℝ) t : ℝ) : WithTop ℝ) := h4
          _ ≤ ((q : ℝ) : WithTop ℝ) := by exact_mod_cast min_le_left (q : ℝ) t
          _ < ((p.2 : ℝ) : WithTop ℝ) := by exact_mod_cast h5
    rw [hcov]
    refine MeasurableSet.iUnion fun q => MeasurableSet.prod ?_ ?_
    · exact (ℱ.mono (min_le_right (q : ℝ) t)) _ ((hc hB).2 (min (q : ℝ) t))
    · exact measurableSet_Ioi.inter measurableSet_Iic
  by_cases h0 : (0 : E) ∈ B
  · have hpre : (Set.indicator U fun p : Ω × ℝ => c p.1) ⁻¹' B
        = (U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B) ∪ Uᶜ := by
      ext p
      by_cases hp : p ∈ U <;> simp [hp, h0]
    rw [hpre]
    exact hUB.union hU.compl
  · have hpre : (Set.indicator U fun p : Ω × ℝ => c p.1) ⁻¹' B
        = U ∩ (fun p : Ω × ℝ => c p.1) ⁻¹' B := by
      ext p
      by_cases hp : p ∈ U <;> simp [hp, h0]
    rw [hpre]
    exact hUB

end ShiftRegion

section StoppedShift

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}
  {σ τ : Ω → WithTop ℝ}

/-- The increment between two ordered stopping times of an integrand read along a random vector
known at the earlier one is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_shift (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Probability.ProgressivelyMeasurable ℱ fun ω s => V s ω)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Probability.ProgressivelyMeasurable ℱ H) {K : Ω → ℝ → ℝ}
    (hK : ∀ ω s, K ω s = φ (V s ω + c ω) * H ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s := by
  intro t
  set mt : MeasurableSpace (Ω × ℝ) := @Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance with hmt
  set U : Set (Ω × ℝ) := {p : Ω × ℝ | σ p.1 < ((p.2 : ℝ) : WithTop ℝ) ∧ p.2 ≤ t} with hUdef
  have hind : Measurable[mt] (Set.indicator U fun p : Ω × ℝ => c p.1) :=
    measurable_indicator_shiftRegion hσ hc t
  have hVm : Measurable[mt] fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => V s p.1) p.2 :=
    (hV t).measurable
  have hHm : Measurable[mt] fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2 :=
    (hH t).measurable
  have hw : Measurable[mt] fun p : Ω × ℝ =>
      (Probability.stoppedRegion τ t).indicator (fun _ => (1 : ℝ)) p
        - (Probability.stoppedRegion σ t).indicator (fun _ => (1 : ℝ)) p :=
    (measurable_const.indicator (Probability.measurableSet_stoppedRegion hτ t)).sub
      (measurable_const.indicator (Probability.measurableSet_stoppedRegion hσ t))
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator
        (fun s => Probability.stopped τ K p.1 s - Probability.stopped σ K p.1 s) p.2)
      = fun p : Ω × ℝ =>
        ((Probability.stoppedRegion τ t).indicator (fun _ => (1 : ℝ)) p
            - (Probability.stoppedRegion σ t).indicator (fun _ => (1 : ℝ)) p)
          * φ ((Set.Iic t).indicator (fun s => V s p.1) p.2
              + Set.indicator U (fun p : Ω × ℝ => c p.1) p)
          * (Set.Iic t).indicator (H p.1) p.2 := by
    funext p
    by_cases hp : p.2 ≤ t
    · have hpI : p.2 ∈ Set.Iic t := Set.mem_Iic.mpr hp
      rw [Set.indicator_of_mem hpI (fun s => Probability.stopped τ K p.1 s
          - Probability.stopped σ K p.1 s), Set.indicator_of_mem hpI (H p.1),
        Set.indicator_of_mem hpI (fun s => V s p.1)]
      by_cases hσp : ((p.2 : ℝ) : WithTop ℝ) ≤ σ p.1
      · have hτp : ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1 := hσp.trans (hστ p.1)
        rw [Set.indicator_of_mem (show p ∈ Probability.stoppedRegion τ t from ⟨hp, hτp⟩),
          Set.indicator_of_mem (show p ∈ Probability.stoppedRegion σ t from ⟨hp, hσp⟩),
          Probability.stopped, Probability.stopped, if_pos hτp, if_pos hσp]
        ring
      · have hσlt : σ p.1 < ((p.2 : ℝ) : WithTop ℝ) := not_le.mp hσp
        rw [Set.indicator_of_notMem (show p ∉ Probability.stoppedRegion σ t from
          fun h => hσp h.2)]
        by_cases hτp : ((p.2 : ℝ) : WithTop ℝ) ≤ τ p.1
        · rw [Set.indicator_of_mem (show p ∈ Probability.stoppedRegion τ t from ⟨hp, hτp⟩),
            Set.indicator_of_mem (show p ∈ U from ⟨hσlt, hp⟩),
            Probability.stopped, Probability.stopped, if_pos hτp,
            if_neg (not_le.mpr hσlt), hK p.1 p.2]
          ring
        · rw [Set.indicator_of_notMem (show p ∉ Probability.stoppedRegion τ t from
            fun h => hτp h.2), Probability.stopped, Probability.stopped, if_neg hτp,
            if_neg (not_le.mpr hσlt)]
          ring
    · have hpI : p.2 ∉ Set.Iic t := fun h => hp (Set.mem_Iic.mp h)
      rw [Set.indicator_of_notMem hpI (fun s => Probability.stopped τ K p.1 s
          - Probability.stopped σ K p.1 s), Set.indicator_of_notMem hpI (H p.1)]
      ring
  rw [key]
  exact ((hw.mul (hφ.measurable.comp (hVm.add hind))).mul hHm).stronglyMeasurable

/-- The increment between two stopping times of an integrand read along a random vector has
measurable uncurrying. -/
theorem measurable_uncurry_stopped_sub_shift (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {c : Ω → Fin n → ℝ} (hc : Measurable c)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Measurable (Function.uncurry fun ω s => V s ω))
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) {K : Ω → ℝ → ℝ}
    (hK : ∀ ω s, K ω s = φ (V s ω + c ω) * H ω s) :
    Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ K ω s - Probability.stopped σ K ω s) := by
  refine measurable_uncurry_stopped_sub hσ hτ ?_
  have hfun : Function.uncurry K
      = fun p : Ω × ℝ => φ (V p.2 p.1 + c p.1) * Function.uncurry H p := by
    funext p
    exact hK p.1 p.2
  rw [hfun]
  exact (hφ.measurable.comp (hV.add (hc.comp measurable_fst))).mul hH

end StoppedShift

section FromUnstopped

open scoped NNReal ENNReal

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n d : ℕ} {ℱ : Filtration ℝ mΩ}
  {P : Measure Ω} [IsProbabilityMeasure P] {chain : ℕ → Ω → WithTop ℝ}
  {V : ℝ → Ω → Fin n → ℝ} {c : ℕ → Ω → Fin n → ℝ} {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}

/-- An integrand jointly measurable in the sample point and the time has jointly measurable
increments between the members of a chain of stopping times. -/
theorem measurable_uncurry_stopped_sub_chain_of_measurable
    (hchain : ∀ k, MeasureTheory.IsStoppingTime ℱ (chain k))
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s)) :
    ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (chain (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (chain k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s) :=
  fun k p j => measurable_uncurry_stopped_sub (hchain k) (hchain (k + 1)) (hmV k p j)

/-- A progressively measurable integrand has progressively measurable increments between the
members of a chain of stopping times. -/
theorem progressivelyMeasurable_stopped_sub_chain_of_progressivelyMeasurable
    (hchain : ∀ k, MeasureTheory.IsStoppingTime ℱ (chain k))
    (hpV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) :
    ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (chain (k + 1))
          (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
        - Probability.stopped (chain k)
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s :=
  fun k p j => progressivelyMeasurable_stopped_sub (hchain k) (hchain (k + 1)) (hpV k p j)

/-- An integrand of finite energy on every bounded window has increments of finite energy
between the members of a chain of stopping times. -/
theorem energy_stopped_sub_chain_lt_top
    (hchain : ∀ k, MeasureTheory.IsStoppingTime ℱ (chain k))
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s))
    (hqV : ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (V s ω + c k ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖Probability.stopped (chain (k + 1))
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - Probability.stopped (chain k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
  fun k p j => energy_stopped_sub_lt_top (hchain k) (hchain (k + 1)) (hmV k p j) (hqV k p j)

end FromUnstopped

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpFormula

open MeasureTheory ProbabilityTheory Filter Topology

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ} {A : Set E}

/-- The increment between consecutive capped arrival times of an integrand read along the capped
left-limit jump sum is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_cappedJumpSumAt
    (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Probability.ProgressivelyMeasurable ℱ fun ω s => V s ω)
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Probability.ProgressivelyMeasurable ℱ H) (T : ℝ) (k : ℕ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (cappedJumpTime N A T (k + 1))
          (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
            * H ω s) ω s
        - Probability.stopped (cappedJumpTime N A T k)
            (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
              * H ω s) ω s :=
  LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_shift
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T k)
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T (k + 1))
    (cappedJumpTime_le_succ N A T k)
    (measurable_cappedJumpSumAt_leftLimPath_of_isStoppingTime X ℱ hℱ hA hfin hXadapt hleft hγ
      (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T k))
    hV hφ hH fun _ _ => rfl

/-- The increment between consecutive capped arrival times of an integrand read along the capped
left-limit jump sum has measurable uncurrying. -/
theorem measurable_uncurry_stopped_sub_cappedJumpSumAt
    (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A)
    (hfin : ∀ (ω : Ω) (t : ℝ), LevyStochCalc.Poisson.arrivalCount N A t ω ≠ ⊤)
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    {V : ℝ → Ω → Fin n → ℝ} (hV : Measurable (Function.uncurry fun ω s => V s ω))
    {φ : (Fin n → ℝ) → ℝ} (hφ : Continuous φ) {H : Ω → ℝ → ℝ}
    (hH : Measurable (Function.uncurry H)) (T : ℝ) (k : ℕ) :
    Measurable (Function.uncurry fun ω s =>
      Probability.stopped (cappedJumpTime N A T (k + 1))
          (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
            * H ω s) ω s
        - Probability.stopped (cappedJumpTime N A T k)
            (fun ω s => φ (V s ω + cappedJumpSumAt X (JumpSplitting.leftLimPath X) A T k ω)
              * H ω s) ω s) :=
  LevyStochCalc.Brownian.Ito.measurable_uncurry_stopped_sub_shift
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T k)
    (isStoppingTime_cappedJumpTime_of_forall_ne_top hℱ hA hfin T (k + 1))
    (measurable_cappedJumpSumAt_leftLimPath X hA hfin hleft hγ T k) hV hφ hH fun _ _ => rfl

end LevyStochCalc.Ito.JumpFormula
