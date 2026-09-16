/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.CompensatedLocalityWindow

/-!
# Optional stopping and locality of the compensated integral

On the window `(0, t]` the integrand cut off at a stopping time of finite range is the integrand
minus, for each value the stopping time takes before `t`, the piece it carries after that value,
so its integral is the integral minus the corresponding increments; a general stopping time is
the decreasing limit of its grid approximations, whose cut-off integrands converge in energy, and
the difference isometry squeezes the integrals, so two marked integrands agreeing up to — or
strictly before — a stopping time have the same compensated integral at every time the stopping
time has not reached.

## Main definitions

* `markedCutTerm τ φ c t` — the piece of `φ` on `(c, t]` that the cut at `τ = c` removes.

## Main statements

* `stochasticIntegral_markedStopped_finiteRange` — optional stopping at a stopping time of
  finite range.
* `stochasticIntegral_markedStopped_eq_of_le` — at a time the stopping time has not reached,
  cutting the integrand off at it changes nothing.
* `stochasticIntegral_congr_of_le`, `stochasticIntegral_congr_of_lt` — integrands agreeing up
  to (respectively, strictly before) a stopping time have the same integral at every time the
  stopping time has not reached.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

open LevyStochCalc.Brownian.Ito (indIoc indIoc_le_one hitInd abs_hitInd_le_one measurable_hitInd
  stronglyMeasurable_hitInd gridStop gridPt isStoppingTime_gridStop le_gridStop gridPt_nonneg
  gridPt_lt_of_lt gridStop_finiteRange eventually_gridStop_lt sq_nnnorm_sub_le_two_mul)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section FiniteRange

variable (τ : Ω → WithTop ℝ) (φ : Ω → ℝ → E → ℝ)

/-- The piece of a marked integrand on `(c, t]` that the cut at `τ = c` removes. -/
noncomputable def markedCutTerm (c t : ℝ) : Ω → ℝ → E → ℝ :=
  fun ω s e => hitInd τ c ω * (indIoc Ω c t ω s * φ ω s e)

omit [MeasurableSpace E] in
theorem abs_markedCutTerm_le (c t : ℝ) (ω : Ω) (s : ℝ) (e : E) :
    |markedCutTerm τ φ c t ω s e| ≤ |φ ω s e| := by
  have h1 : |hitInd τ c ω| ≤ 1 := abs_hitInd_le_one τ c ω
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |markedCutTerm τ φ c t ω s e|
      = |hitInd τ c ω| * (|indIoc Ω c t ω s| * |φ ω s e|) := by
        rw [markedCutTerm, abs_mul, abs_mul]
    _ ≤ 1 * (1 * |φ ω s e|) := by gcongr
    _ = |φ ω s e| := by ring

omit [MeasurableSpace E] in
/-- **The pathwise decomposition of the cut marked integrand.** On the window `(0, t]` the
integrand cut off at `τ` is the integrand minus, for each value `c` the stopping time can take
below `t`, the piece it carries on `(c, t]`. -/
theorem markedStopped_eq_sub_sum {t : ℝ} (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ))
      ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    (fun ω s e => indIoc Ω 0 t ω s * markedStopped τ φ ω s e)
      = fun ω s e => indIoc Ω 0 t ω s * φ ω s e
        - ∑ c ∈ J, markedCutTerm τ φ c t ω s e := by
  classical
  funext ω s e
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
  · have hind0 : indIoc Ω 0 t ω s = 1 := by simp [indIoc, hs]
    have hzero : ∀ c ∈ J, τ ω ≠ ((c : ℝ) : WithTop ℝ) →
        markedCutTerm τ φ c t ω s e = 0 := by
      intro c _ hne
      simp [markedCutTerm, hitInd, Set.indicator_of_notMem (show ω ∉ {ω | τ ω = ((c : ℝ) :
        WithTop ℝ)} from hne)]
    rcases hτJ ω with ⟨c₀, hc₀J, hc₀⟩ | hge
    · have hsum : ∑ c ∈ J, markedCutTerm τ φ c t ω s e
          = markedCutTerm τ φ c₀ t ω s e := by
        refine Finset.sum_eq_single_of_mem c₀ hc₀J fun c hc hne => ?_
        refine hzero c hc ?_
        rw [hc₀]
        exact fun hcc => hne (by exact_mod_cast hcc.symm)
      have hhit : hitInd τ c₀ ω = 1 := by
        simp [hitInd, Set.indicator_of_mem (show ω ∈ {ω | τ ω = ((c₀ : ℝ) : WithTop ℝ)}
          from hc₀)]
      rw [hsum, hind0, markedCutTerm, hhit]
      by_cases hsc : s ≤ c₀
      · have h1 : markedStopped τ φ ω s e = φ ω s e := by
          rw [markedStopped, if_pos]
          rw [hc₀]
          exact_mod_cast hsc
        have h2 : indIoc Ω c₀ t ω s = 0 := by
          simp only [indIoc]
          rw [Set.indicator_of_notMem]
          exact fun hmem => absurd hmem.1 (not_lt.mpr hsc)
        rw [h1, h2]
        ring
      · rw [not_le] at hsc
        have h1 : markedStopped τ φ ω s e = 0 := by
          rw [markedStopped, if_neg]
          rw [hc₀]
          exact fun hcon => absurd (by exact_mod_cast hcon : s ≤ c₀) (not_le.mpr hsc)
        have h2 : indIoc Ω c₀ t ω s = 1 := by
          simp [indIoc, Set.indicator_of_mem (show s ∈ Set.Ioc c₀ t from ⟨hsc, hs.2⟩)]
        rw [h1, h2]
        ring
    · have hsum : ∑ c ∈ J, markedCutTerm τ φ c t ω s e = 0 := by
        refine Finset.sum_eq_zero fun c hc => hzero c hc ?_
        intro hcon
        rw [hcon] at hge
        exact absurd (by exact_mod_cast hge : t ≤ c) (not_le.mpr (hJt c hc))
      have h1 : markedStopped τ φ ω s e = φ ω s e := by
        rw [markedStopped, if_pos]
        exact le_trans (by exact_mod_cast hs.2) hge
      rw [hsum, hind0, h1]
      ring
  · have hind0 : indIoc Ω 0 t ω s = 0 := by
      simp only [indIoc]
      exact Set.indicator_of_notMem hs _
    have hsum : ∑ c ∈ J, markedCutTerm τ φ c t ω s e = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hnot : s ∉ Set.Ioc c t := fun hmem =>
        hs ⟨lt_of_le_of_lt (hJ0 c hc) hmem.1, hmem.2⟩
      have hz : indIoc Ω c t ω s = 0 := by
        simp only [indIoc]
        exact Set.indicator_of_notMem hnot _
      simp [markedCutTerm, hz]
    rw [hsum, hind0]
    ring

variable {τ φ}

/-- The removed piece is jointly measurable. -/
theorem measurable_markedCutTerm (hτ : IsStoppingTime ℱ τ)
    (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (c t : ℝ) :
    Measurable fun p : Ω × ℝ × E => markedCutTerm τ φ c t p.1 p.2.1 p.2.2 :=
  ((measurable_hitInd τ hτ c).comp measurable_fst).mul (measurable_indIoc_mul hm c t)

/-- The removed piece is progressively measurable. -/
theorem markedProgressivelyMeasurable_markedCutTerm (hτ : IsStoppingTime ℱ τ)
    (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ) (c t : ℝ) :
    LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ (markedCutTerm τ φ c t) :=
  markedProgressivelyMeasurable_mul_of_vanishing
    (markedProgressivelyMeasurable_indIoc_mul hp c t)
    (fun ω s e hs => by
      have : s ∉ Set.Ioc c t := fun h => absurd h.1 (not_lt.mpr hs)
      simp [indIoc, this])
    (stronglyMeasurable_hitInd τ hτ c)

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The removed piece has finite energy. -/
theorem sq_int_global_markedCutTerm
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (c t : ℝ) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markedCutTerm τ φ c t ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
  sq_int_global_of_abs_le (fun ω s e => abs_markedCutTerm_le τ φ c t ω s e) hq

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- **Optional stopping for the compensated integral, for a stopping time of finite range.** -/
theorem stochasticIntegral_markedStopped_finiteRange (hτ : IsStoppingTime ℱ τ)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ) (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ))
      ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    stochasticIntegral N ℱ hℱ (markedStopped τ φ) (measurable_markedStopped hτ hm)
        (markedProgressivelyMeasurable_markedStopped hτ hp) (sq_int_global_markedStopped hq) t
      =ᵐ[P] fun ω => stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        - ∑ c ∈ J, hitInd τ c ω * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
            - stochasticIntegral N ℱ hℱ φ hm hp hq c ω) := by
  classical
  have hmS := measurable_markedStopped hτ hm
  have hpS := markedProgressivelyMeasurable_markedStopped hτ hp
  have hqS := sq_int_global_markedStopped (τ := τ) hq
  have hmI0 := measurable_indIoc_mul hm 0 t
  have hpI0 := markedProgressivelyMeasurable_indIoc_mul hp 0 t
  have hqI0 := sq_int_global_indIoc_mul hq 0 t
  have hmW := measurable_indIoc_mul hmS 0 t
  have hpW := markedProgressivelyMeasurable_indIoc_mul hpS 0 t
  have hqW := sq_int_global_indIoc_mul hqS 0 t
  have hmF : ∀ c : ℝ,
      Measurable fun p : Ω × ℝ × E => markedCutTerm τ φ c t p.1 p.2.1 p.2.2 :=
    fun c => measurable_markedCutTerm hτ hm c t
  have hpF : ∀ c : ℝ, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      (markedCutTerm τ φ c t) :=
    fun c => markedProgressivelyMeasurable_markedCutTerm hτ hp c t
  have hqF : ∀ (c T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markedCutTerm τ φ c t ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun c => sq_int_global_markedCutTerm hq c t
  obtain ⟨hmSum, hpSum, hqSum, hSum⟩ := exists_stochasticIntegral_finsetSum N hℱ
    (fun c : ℝ => markedCutTerm τ φ c t) hmF hpF hqF J ht
  have hmD : Measurable fun p : Ω × ℝ × E => indIoc Ω 0 t p.1 p.2.1 * φ p.1 p.2.1 p.2.2
      - ∑ c ∈ J, markedCutTerm τ φ c t p.1 p.2.1 p.2.2 := hmI0.sub hmSum
  have hpD : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => indIoc Ω 0 t ω s * φ ω s e - ∑ c ∈ J, markedCutTerm τ φ c t ω s e :=
    markedProgressivelyMeasurable_sub hpI0 hpSum
  have hqD : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖indIoc Ω 0 t ω s * φ ω s e
        - ∑ c ∈ J, markedCutTerm τ φ c t ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P < ⊤ :=
    markedEnergy_lt_top_of_bound (fun _ _ _ => sq_nnnorm_sub_le_two_mul _ _) hmI0 hmSum hqI0
      hqSum
  have hpath : (fun ω s e => indIoc Ω 0 t ω s * markedStopped τ φ ω s e)
      = fun ω s e => indIoc Ω 0 t ω s * φ ω s e
        - ∑ c ∈ J, markedCutTerm τ φ c t ω s e :=
    markedStopped_eq_sub_sum τ φ J hJ0 hJt hτJ
  have hterm : ∀ c ∈ J,
      stochasticIntegral N ℱ hℱ (markedCutTerm τ φ c t) (hmF c) (hpF c) (hqF c) t
        =ᵐ[P] fun ω => hitInd τ c ω * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
          - stochasticIntegral N ℱ hℱ φ hm hp hq c ω) := by
    intro c hc
    have hc0 : 0 ≤ c := hJ0 c hc
    have hct : c < t := hJt c hc
    have hpull := hitInd_mul_stochasticIntegral_indIoc N hℱ hm hp hq hτ hc0 hct (hmF c) (hpF c)
      (hqF c)
    have hloc := stochasticIntegral_indicator_Ioc N hℱ hm hp hq hc0 hct
    filter_upwards [hpull, hloc] with ω hpullω hlocω
    have hpull' : stochasticIntegral N ℱ hℱ (markedCutTerm τ φ c t) (hmF c) (hpF c) (hqF c)
          t ω
        = hitInd τ c ω * stochasticIntegral N ℱ hℱ
          (fun ω s e => indIoc Ω c t ω s * φ ω s e) (measurable_indIoc_mul hm c t)
          (markedProgressivelyMeasurable_indIoc_mul hp c t) (sq_int_global_indIoc_mul hq c t)
          t ω := hpullω
    rw [hpull', hlocω]
  have hstep := stochasticIntegral_indIoc_zero N hℱ hmS hpS hqS ht
  have hcongr := stochasticIntegral_congr_fun N hℱ hmW hpW hqW hpath hmD hpD hqD t
  have hsub := stochasticIntegral_sub N hℱ hmI0 hmSum hpI0 hpSum hqI0 hqSum hmD hpD hqD ht
  have hI0 := stochasticIntegral_indIoc_zero N hℱ hm hp hq ht
  have hall : ∀ᵐ ω ∂P, ∀ c ∈ (↑J : Set ℝ),
      stochasticIntegral N ℱ hℱ (markedCutTerm τ φ c t) (hmF c) (hpF c) (hqF c) t ω
        = hitInd τ c ω * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
          - stochasticIntegral N ℱ hℱ φ hm hp hq c ω) :=
    (MeasureTheory.ae_ball_iff J.countable_toSet).mpr fun c hc => hterm c (Finset.mem_coe.mp hc)
  filter_upwards [hstep, hsub, hI0, hSum, hall] with ω h1 h3 h4 h5 h6
  have h2 := congrFun hcongr ω
  rw [← h1, h2, h3, h4, h5, Finset.sum_congr rfl fun c hc => h6 c (Finset.mem_coe.mpr hc)]

end FiniteRange

section Local

variable (N : PoissonRandomMeasure P ν) (hℱ : IsPoissonFiltration N ℱ)
  {τ : Ω → WithTop ℝ}
  {φ : Ω → ℝ → E → ℝ} (hm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (hp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ φ)
  (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- **The local property of the compensated integral.** At a time the stopping time has not
reached, cutting the integrand off at it changes nothing. -/
theorem stochasticIntegral_markedStopped_eq_of_le (hτ : IsStoppingTime ℱ τ) {t : ℝ}
    (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegral N ℱ hℱ (markedStopped τ φ) (measurable_markedStopped hτ hm)
          (markedProgressivelyMeasurable_markedStopped hτ hp) (sq_int_global_markedStopped hq)
          t ω
        = stochasticIntegral N ℱ hℱ φ hm hp hq t ω := by
  classical
  -- the cut integrand and its approximations
  have hmS := measurable_markedStopped hτ hm
  have hpS := markedProgressivelyMeasurable_markedStopped hτ hp
  have hqS := sq_int_global_markedStopped (τ := τ) hq
  have hmG : ∀ n : ℕ, Measurable fun p : Ω × ℝ × E =>
      markedStopped (gridStop τ t n) φ p.1 p.2.1 p.2.2 :=
    fun n => measurable_markedStopped (isStoppingTime_gridStop τ hτ t n) hm
  have hpG : ∀ n : ℕ, LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      (markedStopped (gridStop τ t n) φ) :=
    fun n => markedProgressivelyMeasurable_markedStopped (isStoppingTime_gridStop τ hτ t n) hp
  have hqG : ∀ (n : ℕ) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖markedStopped (gridStop τ t n) φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun n => sq_int_global_markedStopped (τ := gridStop τ t n) hq
  -- the event on which the stopping time has not been reached
  set A : Set Ω := {ω | ((t : ℝ) : WithTop ℝ) ≤ τ ω} with hAdef
  have hAmeas : MeasurableSet A := by
    have hcompl : A = {ω | τ ω < ((t : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      simp only [hAdef, Set.mem_setOf_eq, Set.mem_compl_iff, not_lt]
    rw [hcompl]
    exact (ℱ.le t _ (hτ.measurableSet_lt t)).compl
  -- on that event the approximations already agree with the uncut integral
  have hagree : ∀ n : ℕ, n ≠ 0 → ∀ᵐ ω ∂P, ω ∈ A →
      stochasticIntegral N ℱ hℱ (markedStopped (gridStop τ t n) φ) (hmG n) (hpG n) (hqG n)
          t ω
        = stochasticIntegral N ℱ hℱ φ hm hp hq t ω := by
    intro n hn
    have hid := stochasticIntegral_markedStopped_finiteRange N hℱ hm hp hq
      (isStoppingTime_gridStop τ hτ t n) ht ((Finset.range n).image (gridPt t n))
      (by
        intro c hc
        obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hc
        exact gridPt_nonneg ht.le n k)
      (by
        intro c hc
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
        exact gridPt_lt_of_lt ht (Finset.mem_range.mp hk))
      (gridStop_finiteRange τ hn)
    filter_upwards [hid] with ω hω hωA
    rw [hω]
    have hzero : ∀ c ∈ (Finset.range n).image (gridPt t n),
        hitInd (gridStop τ t n) c ω = 0 := by
      intro c hc
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hc
      have hlt : gridPt t n k < t := gridPt_lt_of_lt ht (Finset.mem_range.mp hk)
      have hne : gridStop τ t n ω ≠ ((gridPt t n k : ℝ) : WithTop ℝ) := by
        intro hcon
        have h1 : ((t : ℝ) : WithTop ℝ) ≤ ((gridPt t n k : ℝ) : WithTop ℝ) :=
          le_trans hωA (le_trans (le_gridStop τ t n ω) (le_of_eq hcon))
        exact absurd (by exact_mod_cast h1 : t ≤ gridPt t n k) (not_le.mpr hlt)
      simp [hitInd, Set.indicator_of_notMem (show ω ∉ {ω | gridStop τ t n ω
        = ((gridPt t n k : ℝ) : WithTop ℝ)} from hne)]
    have hsum : ∑ c ∈ (Finset.range n).image (gridPt t n),
        hitInd (gridStop τ t n) c ω
          * (stochasticIntegral N ℱ hℱ φ hm hp hq t ω
            - stochasticIntegral N ℱ hℱ φ hm hp hq c ω) = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      rw [hzero c hc, zero_mul]
    rw [hsum, sub_zero]
  -- the approximations converge to the cut integrand in energy
  have hEtend : Filter.Tendsto (fun n : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
      (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
        ∂ν ∂volume ∂P) Filter.atTop (𝓝 0) := by
    have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume :=
      measurable_markedDensity (ν := ν) (φ := φ) hm t
    have hFmeas : ∀ n : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume :=
      fun n => measurable_markedDensity (ν := ν)
        (φ := fun ω s e => markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e)
        ((hmG n).sub hmS) t
    have hptw : ∀ (n : ℕ) (ω : Ω) (s : ℝ) (e : E),
        (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ≤ (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 := by
      intro n ω s e
      have habs : |markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e|
          ≤ |φ ω s e| := by
        rw [markedStopped, markedStopped]
        by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω
        · by_cases h2 : ((s : ℝ) : WithTop ℝ) ≤ τ ω
          · simp [h1, h2]
          · simp [h1, h2]
        · have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := fun hcon =>
            h1 (le_trans hcon (le_gridStop τ t n ω))
          simp [h1, h2]
      have hle : (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞)
          ≤ (‖φ ω s e‖₊ : ℝ≥0∞) := by
        refine ENNReal.coe_le_coe.mpr ?_
        rw [← NNReal.coe_le_coe]
        simpa [Real.norm_eq_abs] using habs
      gcongr
    have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun n : ℕ =>
        ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume) Filter.atTop (𝓝 0) := by
      filter_upwards [MeasureTheory.ae_lt_top hbmeas (hq t ht).ne] with ω hfin
      have hlims : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
          Filter.Tendsto (fun n : ℕ => ∫⁻ e,
            (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
              ∂ν) Filter.atTop (𝓝 0) := by
        have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by
          simp
        filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
          MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
        have hsne : s ≠ 0 := by simpa using hs0
        have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
        by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
        · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => ?_
          have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω :=
            le_trans hτs (le_gridStop τ t n ω)
          simp [markedStopped, h1, hτs]
        · rw [not_le] at hτs
          obtain ⟨N', hN'⟩ := Filter.eventually_atTop.mp
            (eventually_gridStop_lt τ ht ω hs hsmem.2 hτs)
          refine tendsto_atTop_of_eventually_const (i₀ := N') fun n hn => ?_
          have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t n ω := not_le.mpr (hN' n hn)
          have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
          simp [markedStopped, h1, h2]
      have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
        (μ := volume.restrict (Set.Icc (0 : ℝ) t))
        (F := fun n s => ∫⁻ e,
          (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        (f := fun _ : ℝ => (0 : ℝ≥0∞))
        (bound := fun s => ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        (fun n => measurable_markSlice (ν := ν)
          (φ := fun ω s e =>
            markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e)
          ((hmG n).sub hmS) ω)
        (fun n => Filter.Eventually.of_forall fun s => lintegral_mono fun e => hptw n ω s e)
        hfin.ne hlims
      simpa using hconv
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun n ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume)
      (f := fun _ : Ω => (0 : ℝ≥0∞))
      (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume)
      hFmeas
      (fun n => Filter.Eventually.of_forall fun ω =>
        lintegral_mono fun s => lintegral_mono fun e => hptw n ω s e)
      (hq t ht).ne hinner
    simpa using hconv
  -- the squeeze
  set D : Ω → ℝ≥0∞ := fun ω => A.indicator (fun ω =>
    (‖stochasticIntegral N ℱ hℱ (markedStopped τ φ) hmS hpS hqS t ω
      - stochasticIntegral N ℱ hℱ φ hm hp hq t ω‖₊ : ℝ≥0∞) ^ 2) ω with hDdef
  have hDmeas : AEMeasurable D P := by
    refine AEMeasurable.indicator ?_ hAmeas
    have h1 := (stochasticIntegral_memLp N ℱ hℱ (markedStopped τ φ) hmS hpS hqS t
      ).aestronglyMeasurable.aemeasurable
    have h2 := (stochasticIntegral_memLp N ℱ hℱ φ hm hp hq t).aestronglyMeasurable.aemeasurable
    exact (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hDle : ∀ n : ℕ, n ≠ 0 → ∫⁻ ω, D ω ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
        (‖markedStopped (gridStop τ t n) φ ω s e - markedStopped τ φ ω s e‖₊ : ℝ≥0∞) ^ 2
          ∂ν ∂volume ∂P := by
    intro n hn
    rw [← itoIsometry_diff_compensated N ℱ hℱ (markedStopped (gridStop τ t n) φ)
      (markedStopped τ φ) (hmG n) hmS (hpG n) hpS (hqG n) hqS t ht]
    refine lintegral_mono_ae ?_
    filter_upwards [hagree n hn] with ω hω
    by_cases hωA : ω ∈ A
    · simp only [hDdef]
      have hrev : ∀ x y : ℝ, ‖x - y‖₊ = ‖y - x‖₊ := by
        intro x y
        rw [← NNReal.coe_inj]
        simpa using norm_sub_rev x y
      rw [Set.indicator_of_mem hωA, hω hωA, hrev]
    · simp only [hDdef]
      rw [Set.indicator_of_notMem hωA]
      exact zero_le
  have hDzero : ∫⁻ ω, D ω ∂P = 0 := by
    refine le_antisymm ?_ zero_le
    refine ge_of_tendsto hEtend ?_
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    exact hDle n hn.ne'
  have hDae := (MeasureTheory.lintegral_eq_zero_iff' hDmeas).mp hDzero
  filter_upwards [hDae] with ω hω hωA
  have h0 : D ω = 0 := hω
  simp only [hDdef] at h0
  rw [Set.indicator_of_mem (show ω ∈ A from hωA)] at h0
  have hnn : (‖stochasticIntegral N ℱ hℱ (markedStopped τ φ) hmS hpS hqS t ω
      - stochasticIntegral N ℱ hℱ φ hm hp hq t ω‖₊ : ℝ≥0∞) = 0 := by
    simpa [pow_eq_zero_iff] using h0
  have : ‖stochasticIntegral N ℱ hℱ (markedStopped τ φ) hmS hpS hqS t ω
      - stochasticIntegral N ℱ hℱ φ hm hp hq t ω‖₊ = 0 := by
    exact_mod_cast hnn
  have hsub : stochasticIntegral N ℱ hℱ (markedStopped τ φ) hmS hpS hqS t ω
      - stochasticIntegral N ℱ hℱ φ hm hp hq t ω = 0 := by
    simpa using this
  linarith [hsub]

include hℱ in
/-- **Two marked integrands agreeing up to a stopping time have the same compensated integral
at a time that stopping time has not reached.** -/
theorem stochasticIntegral_congr_of_le (hτ : IsStoppingTime ℱ τ) {ψ : Ω → ℝ → E → ℝ}
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ τ ω →
      ∀ e, φ ω s e = ψ ω s e)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        = stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t ω := by
  have e1 := stochasticIntegral_markedStopped_eq_of_le N hℱ hm hp hq hτ ht
  have e2 := stochasticIntegral_markedStopped_eq_of_le N hℱ (φ := ψ) hmψ hpψ hqψ hτ ht
  have hstop : ∀ (ω : Ω) (s : ℝ), 0 < s → ∀ e,
      markedStopped τ φ ω s e = markedStopped τ ψ ω s e := by
    intro ω s hs e
    unfold markedStopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hs hle e]
    · rw [if_neg hle, if_neg hle]
  have e3 := stochasticIntegral_congr_of_pos N hℱ (measurable_markedStopped hτ hm)
    (markedProgressivelyMeasurable_markedStopped hτ hp) (sq_int_global_markedStopped hq)
    (measurable_markedStopped hτ hmψ) (markedProgressivelyMeasurable_markedStopped hτ hpψ)
    (sq_int_global_markedStopped hqψ) hstop ht
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]

include hℱ in
/-- **Two marked integrands agreeing strictly before a stopping time have the same compensated
integral at a time that stopping time has not reached.** -/
theorem stochasticIntegral_congr_of_lt (hτ : IsStoppingTime ℱ τ) {ψ : Ω → ℝ → E → ℝ}
    (hmψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
    (hpψ : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ ψ)
    (hqψ : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) < τ ω →
      ∀ e, φ ω s e = ψ ω s e)
    {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂P, ((t : ℝ) : WithTop ℝ) ≤ τ ω →
      stochasticIntegral N ℱ hℱ φ hm hp hq t ω
        = stochasticIntegral N ℱ hℱ ψ hmψ hpψ hqψ t ω := by
  have e1 := stochasticIntegral_markedStopped_eq_of_le N hℱ hm hp hq hτ ht
  have e2 := stochasticIntegral_markedStopped_eq_of_le N hℱ (φ := ψ) hmψ hpψ hqψ hτ ht
  -- the cut integrands agree off the time `0` and the value of the stopping time
  have hstop : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)), ∀ e,
      markedStopped τ φ ω s e = markedStopped τ ψ ω s e := by
    refine Eventually.of_forall fun ω => ?_
    have hnull : (volume.restrict (Set.Icc (0 : ℝ) t))
        ({(0 : ℝ)} ∪ {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω}) = 0 := by
      refine measure_union_null (by simp) ?_
      rcases eq_or_ne (τ ω) ⊤ with hτω | hτω
      · have hempty : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = ∅ := by
          ext s
          simp [hτω]
        rw [hempty]
        exact measure_empty
      · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hτω
        have hsing : {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ ω} = {r} := by
          ext s
          rw [Set.mem_setOf_eq, Set.mem_singleton_iff, ← hr]
          exact ⟨fun h => by exact_mod_cast h, fun h => by exact_mod_cast h⟩
        rw [hsing]
        simp
    filter_upwards [compl_mem_ae_iff.mpr hnull, ae_restrict_mem measurableSet_Icc]
      with s hs0 hs e
    have hsn : ¬ s = 0 ∧ ¬ ((s : ℝ) : WithTop ℝ) = τ ω := by
      simpa [not_or] using hs0
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hsn.1)
    unfold markedStopped
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · rw [if_pos hle, if_pos hle, hagree ω s hspos (lt_of_le_of_ne hle hsn.2) e]
    · rw [if_neg hle, if_neg hle]
  have e3 := stochasticIntegral_congr_ae N hℱ (markedStopped τ φ) (markedStopped τ ψ)
    (measurable_markedStopped hτ hm) (measurable_markedStopped hτ hmψ)
    (markedProgressivelyMeasurable_markedStopped hτ hp)
    (markedProgressivelyMeasurable_markedStopped hτ hpψ)
    (sq_int_global_markedStopped hq) (sq_int_global_markedStopped hqψ) ht
    (LevyStochCalc.Ito.markedEnergyMeasure_ae_eq_of_ae_ae (measurable_markedStopped hτ hm)
      (measurable_markedStopped hτ hmψ) t hstop)
  filter_upwards [e1, e2, e3] with ω h1 h2 h3 hle
  rw [← h1 hle, ← h2 hle, h3]

end Local

end LevyStochCalc.Poisson.Compensated
