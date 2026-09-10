/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaShift

/-!
# The upward grid discretisation truncated at the horizon

The stopping time that stops at the first point of a uniform grid strictly beyond a stopping time
attains the horizon, so its values are not all grid points strictly below the horizon. Sending it
to `⊤` where it attains the horizon leaves a stopping time whose values are grid points strictly
below the horizon or `⊤`, and changes neither the horizon clipped at it nor an integrand cut off
at it on the closed window, hence neither the Itô integral at the horizon.

## Main statements

* `LevyStochCalc.Brownian.Ito.gridStopTrunc` — the upward grid discretisation of a stopping time,
  sent to `⊤` where it attains the horizon.
* `LevyStochCalc.Brownian.Ito.isStoppingTime_gridStopTrunc` — it is a stopping time.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_mono` — it is monotone in the stopping time.
* `LevyStochCalc.Brownian.Ito.measurableSpace_le_gridStopTrunc` — the σ-algebra of a stopping
  time is contained in that of its truncated grid discretisation.
* `LevyStochCalc.Brownian.Ito.gridStopTrunc_finiteRange` — its values are grid points strictly
  below the horizon, or `⊤`.
* `LevyStochCalc.Brownian.Ito.clipTime_gridStopTrunc` — the horizon clipped at it is the horizon
  clipped at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stopped_gridStopTrunc` — an integrand cut off at it agrees on the
  closed window with the integrand cut off at the grid discretisation.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_le_horizon` — the Itô integral
  at a horizon depends on the integrand only on the window up to that horizon.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridStop_of_gridStopTrunc` — Itô's formula
  between the grid discretisations of two stopping times, from the identity between their
  truncations.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Truncate

variable {Ω : Type u}

/-- The stopping time that stops at the first point of the uniform grid on `[0, T]` with `m`
steps strictly beyond `σ`, sent to `⊤` where that point attains the horizon. -/
noncomputable def gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) : Ω → WithTop ℝ :=
  fun ω => if ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω then ⊤ else gridStop σ T m ω

theorem gridStopTrunc_of_le (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) {ω : Ω}
    (h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω) : gridStopTrunc σ T m ω = ⊤ := by
  simp only [gridStopTrunc]
  rw [if_pos h]

theorem gridStopTrunc_of_lt (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) {ω : Ω}
    (h : gridStop σ T m ω < ((T : ℝ) : WithTop ℝ)) :
    gridStopTrunc σ T m ω = gridStop σ T m ω := by
  simp only [gridStopTrunc]
  rw [if_neg (not_le.mpr h)]

theorem gridStop_le_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    gridStop σ T m ω ≤ gridStopTrunc σ T m ω := by
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · rw [gridStopTrunc_of_le σ T m h]
    exact le_top
  · rw [gridStopTrunc_of_lt σ T m (not_le.mp h)]

theorem le_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    σ ω ≤ gridStopTrunc σ T m ω :=
  le_trans (le_gridStop σ T m ω) (gridStop_le_gridStopTrunc σ T m ω)

theorem zero_le_gridStopTrunc {σ : Ω → WithTop ℝ} (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (T : ℝ) (m : ℕ) (ω : Ω) : ((0 : ℝ) : WithTop ℝ) ≤ gridStopTrunc σ T m ω :=
  le_trans (hσ0 ω) (le_gridStopTrunc σ T m ω)

theorem stepStop_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (c : ℝ) (ω : Ω) :
    stepStop σ c ω ≤ stepStop τ c ω := by
  simp only [stepStop]
  split_ifs with h1 h2 h2
  · exact le_rfl
  · exact absurd (le_trans h1 (hστ ω)) h2
  · exact le_top
  · exact le_rfl

theorem gridStopAux_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (t : ℝ) (n k : ℕ)
    (ω : Ω) : gridStopAux σ t n k ω ≤ gridStopAux τ t n k ω := by
  induction k with
  | zero => exact stepStop_mono hστ (gridPt t n 0) ω
  | succ k ih =>
    have h1 : gridStopAux σ t n (k + 1) ω
        = min (stepStop σ (gridPt t n (k + 1)) ω) (gridStopAux σ t n k ω) := rfl
    have h2 : gridStopAux τ t n (k + 1) ω
        = min (stepStop τ (gridPt t n (k + 1)) ω) (gridStopAux τ t n k ω) := rfl
    rw [h1, h2]
    exact min_le_min (stepStop_mono hστ (gridPt t n (k + 1)) ω) ih

theorem gridStop_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (t : ℝ) (n : ℕ) (ω : Ω) :
    gridStop σ t n ω ≤ gridStop τ t n ω :=
  gridStopAux_mono hστ t n n ω

/-- The truncated grid discretisation is monotone in the stopping time. -/
theorem gridStopTrunc_mono {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω) (T : ℝ) (m : ℕ)
    (ω : Ω) : gridStopTrunc σ T m ω ≤ gridStopTrunc τ T m ω := by
  have hle := gridStop_mono hστ T m ω
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · rw [gridStopTrunc_of_le σ T m h, gridStopTrunc_of_le τ T m (le_trans h hle)]
  · rw [gridStopTrunc_of_lt σ T m (not_le.mp h)]
    by_cases h2 : ((T : ℝ) : WithTop ℝ) ≤ gridStop τ T m ω
    · rw [gridStopTrunc_of_le τ T m h2]
      exact le_top
    · rw [gridStopTrunc_of_lt τ T m (not_le.mp h2)]
      exact hle

end Truncate

section FiniteRange

variable {Ω : Type u}

theorem gridPt_image_nonneg {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ (Finset.range m).image (gridPt T m), 0 ≤ a := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
  exact gridPt_nonneg hT.le m k

theorem gridPt_image_lt {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ (Finset.range m).image (gridPt T m), a < T := by
  intro a ha
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
  exact gridPt_lt_of_lt hT (Finset.mem_range.mp hk)

/-- The truncated grid discretisation takes one of the grid values strictly below the horizon, or
the value `⊤`. -/
theorem gridStopTrunc_finiteRange (σ : Ω → WithTop ℝ) {T : ℝ} (hT : 0 < T) {m : ℕ} (hm : m ≠ 0)
    (ω : Ω) :
    (∃ a ∈ (Finset.range m).image (gridPt T m),
        gridStopTrunc σ T m ω = ((a : ℝ) : WithTop ℝ))
      ∨ gridStopTrunc σ T m ω = ⊤ := by
  rcases gridStop_finiteRange σ hT hm ω with ⟨a, ha, hae⟩ | hge
  · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    have hlt : gridStop σ T m ω < ((T : ℝ) : WithTop ℝ) := by
      rw [hae]
      exact_mod_cast gridPt_lt_of_lt hT (Finset.mem_range.mp hk)
    exact Or.inl ⟨gridPt T m k, ha, by rw [gridStopTrunc_of_lt σ T m hlt, hae]⟩
  · exact Or.inr (gridStopTrunc_of_le σ T m hge)

end FiniteRange

section StoppingTime

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The truncated grid discretisation of a stopping time is a stopping time. -/
theorem isStoppingTime_gridStopTrunc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) (T : ℝ) (m : ℕ) :
    MeasureTheory.IsStoppingTime ℱ (gridStopTrunc σ T m) := by
  have hG : MeasureTheory.IsStoppingTime ℱ (gridStop σ T m) := isStoppingTime_gridStop σ hσ T m
  intro i
  by_cases hiT : i < T
  · have hset : {ω | gridStopTrunc σ T m ω ≤ ((i : ℝ) : WithTop ℝ)}
        = {ω | gridStop σ T m ω ≤ ((i : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [Set.mem_setOf_eq]
      constructor
      · intro hle
        by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
        · rw [gridStopTrunc_of_le σ T m h, top_le_iff] at hle
          exact absurd hle (by simp)
        · rwa [gridStopTrunc_of_lt σ T m (not_le.mp h)] at hle
      · intro hle
        have h : ¬ ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω := by
          intro hcon
          have h1 : ((T : ℝ) : WithTop ℝ) ≤ ((i : ℝ) : WithTop ℝ) := le_trans hcon hle
          exact absurd (by exact_mod_cast h1 : T ≤ i) (not_le.mpr hiT)
        rwa [gridStopTrunc_of_lt σ T m (not_le.mp h)]
    rw [hset]
    exact hG i
  · rw [not_lt] at hiT
    have hset : {ω | gridStopTrunc σ T m ω ≤ ((i : ℝ) : WithTop ℝ)}
        = {ω | gridStop σ T m ω ≤ ((i : ℝ) : WithTop ℝ)}
          ∩ {ω | gridStop σ T m ω < ((T : ℝ) : WithTop ℝ)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
      constructor
      · intro hle
        by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
        · rw [gridStopTrunc_of_le σ T m h, top_le_iff] at hle
          exact absurd hle (by simp)
        · rw [gridStopTrunc_of_lt σ T m (not_le.mp h)] at hle
          exact ⟨hle, not_le.mp h⟩
      · rintro ⟨hle, hlt⟩
        rwa [gridStopTrunc_of_lt σ T m hlt]
    rw [hset]
    exact (hG i).inter (ℱ.mono hiT _ (hG.measurableSet_lt T))

/-- The σ-algebra of a stopping time is contained in the σ-algebra of its truncated grid
discretisation. -/
theorem measurableSpace_le_gridStopTrunc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) (T : ℝ) (m : ℕ) :
    hσ.measurableSpace ≤ (isStoppingTime_gridStopTrunc hσ T m).measurableSpace :=
  hσ.measurableSpace_mono _ fun ω => le_gridStopTrunc σ T m ω

end StoppingTime

section Window

variable {Ω : Type u}

/-- The horizon clipped at the truncated grid discretisation is the horizon clipped at the grid
discretisation. -/
theorem clipTime_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    clipTime (gridStopTrunc σ T m) T ω = clipTime (gridStop σ T m) T ω := by
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · rw [clipTime_eq_self_of_top (gridStopTrunc_of_le σ T m h), clipTime_of_le h]
  · have he : gridStopTrunc σ T m ω = gridStop σ T m ω :=
      gridStopTrunc_of_lt σ T m (not_le.mp h)
    simp only [clipTime, he]

/-- On the closed window an integrand cut off at the truncated grid discretisation is the
integrand cut off at the grid discretisation. -/
theorem stopped_gridStopTrunc (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (K : Ω → ℝ → ℝ) (ω : Ω)
    {s : ℝ} (hs : s ≤ T) :
    Probability.stopped (gridStopTrunc σ T m) K ω s
      = Probability.stopped (gridStop σ T m) K ω s := by
  by_cases h : ((T : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω
  · have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStopTrunc σ T m ω := by
      rw [gridStopTrunc_of_le σ T m h]
      exact le_top
    have h2 : ((s : ℝ) : WithTop ℝ) ≤ gridStop σ T m ω :=
      le_trans (by exact_mod_cast hs) h
    simp only [Probability.stopped]
    rw [if_pos h1, if_pos h2]
  · have he : gridStopTrunc σ T m ω = gridStop σ T m ω :=
      gridStopTrunc_of_lt σ T m (not_le.mp h)
    simp only [Probability.stopped, he]

end Window

section Horizon

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **The Itô integral at a horizon depends on the integrand only on the window up to that
horizon.** -/
theorem stochasticIntegralBrownian_congr_of_le_horizon
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ)
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → s ≤ T → H₁ ω s = H₂ ω s) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by
  have hconst : MeasureTheory.IsStoppingTime ℱ (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) :=
    MeasureTheory.isStoppingTime_const ℱ T
  have hag : ∀ (ω : Ω) (s : ℝ), 0 < s →
      ((s : ℝ) : WithTop ℝ) ≤ (fun _ : Ω => ((T : ℝ) : WithTop ℝ)) ω → H₁ ω s = H₂ ω s := by
    intro ω s hs hle
    have hle' : ((s : ℝ) : WithTop ℝ) ≤ ((T : ℝ) : WithTop ℝ) := hle
    exact hagree ω s hs (by exact_mod_cast hle')
  have h := stochasticIntegralBrownian_congr_of_le (fun _ : Ω => ((T : ℝ) : WithTop ℝ))
    W ℱ hℱ hconst hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hag hT
  filter_upwards [h] with ω hω
  exact hω le_rfl

/-- The Itô integral at the horizon of the increment of an integrand between the truncated grid
discretisations of two stopping times is the one between the grid discretisations. -/
theorem stochasticIntegralBrownian_stopped_sub_gridStopTrunc
    (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) (σ τ : Ω → WithTop ℝ) (K : Ω → ℝ → ℝ)
    {T : ℝ} (hT : 0 < T) (m : ℕ)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStopTrunc τ T m) K ω s
        - Probability.stopped (gridStopTrunc σ T m) K ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStopTrunc τ T m) K ω s
        - Probability.stopped (gridStopTrunc σ T m) K ω s)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStopTrunc τ T m) K ω s
        - Probability.stopped (gridStopTrunc σ T m) K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m) K ω s
        - Probability.stopped (gridStop σ T m) K ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStop τ T m) K ω s
        - Probability.stopped (gridStop σ T m) K ω s)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStop τ T m) K ω s
        - Probability.stopped (gridStop σ T m) K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped (gridStopTrunc τ T m) K ω s
          - Probability.stopped (gridStopTrunc σ T m) K ω s) hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped (gridStop τ T m) K ω s
          - Probability.stopped (gridStop σ T m) K ω s) hm₂ hp₂ hq₂ T := by
  refine stochasticIntegralBrownian_congr_of_le_horizon W ℱ hℱ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hT ?_
  intro ω s _ hsT
  rw [stopped_gridStopTrunc τ T m K ω hsT, stopped_gridStopTrunc σ T m K ω hsT]

end Horizon

section GridShiftTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **Itô's formula for the increment of a path between the upward grid discretisations of two
stopping times, for a function translated by a random vector, from the identity between the
truncations of those discretisations at the horizon.** -/
theorem itoFormula_between_gridStop_of_gridStopTrunc
    {X : ℝ → Ω → Fin n → ℝ} {H : Fin n → Fin d → Ω → ℝ → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
    {σ τ : Ω → WithTop ℝ} {f : (Fin n → ℝ) → ℝ}
    {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    {c : Ω → Fin n → ℝ} {T : ℝ} (hT : 0 < T) (m : ℕ)
    (hmSt : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStopTrunc τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStopTrunc σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSt : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped (gridStopTrunc τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStopTrunc σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSt : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStopTrunc τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStopTrunc σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hmSm : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSm : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSm : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hbase :
      (fun ω : Ω => f (X (clipTime (gridStopTrunc τ T m) T ω) ω + c ω)
          - f (X (clipTime (gridStopTrunc σ T m) T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (gridStopTrunc τ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped (gridStopTrunc σ T m)
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped (gridStopTrunc τ T m)
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped (gridStopTrunc σ T m)
                        (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSt p k) (hpSt p k) (hqSt p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (gridStopTrunc τ T m)
                  (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped (gridStopTrunc σ T m)
                    (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                      * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume) :
    (fun ω : Ω => f (X (clipTime (gridStop τ T m) T ω) ω + c ω)
        - f (X (clipTime (gridStop σ T m) T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped (gridStop τ T m)
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped (gridStop σ T m)
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSm p k) (hpSm p k) (hqSm p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (gridStop τ T m)
                (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped (gridStop σ T m)
                  (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hSI : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            Probability.stopped (gridStopTrunc τ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
              - Probability.stopped (gridStopTrunc σ T m)
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
          (hmSt p k) (hpSt p k) (hqSt p k) T ω
        = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            Probability.stopped (gridStop τ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
              - Probability.stopped (gridStop σ T m)
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
          (hmSm p k) (hpSm p k) (hqSm p k) T ω := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact stochasticIntegralBrownian_stopped_sub_gridStopTrunc (W.W k) ℱ' (hcoord k) σ τ
      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) hT m
      (hmSt p k) (hpSt p k) (hqSt p k) (hmSm p k) (hpSm p k) (hqSm p k)
  filter_upwards [hbase, hSI] with ω hb hs
  have hwin : ∀ K : Ω → ℝ → ℝ,
      ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped (gridStopTrunc τ T m) K ω s
            - Probability.stopped (gridStopTrunc σ T m) K ω s) ∂volume
        = ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped (gridStop τ T m) K ω s
            - Probability.stopped (gridStop σ T m) K ω s) ∂volume := by
    intro K
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hsm => ?_
    rw [stopped_gridStopTrunc τ T m K ω hsm.2, stopped_gridStopTrunc σ T m K ω hsm.2]
  rw [← clipTime_gridStopTrunc τ T m ω, ← clipTime_gridStopTrunc σ T m ω, hb]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) (congrArg₂ (· * ·) rfl ?_)
  · exact Finset.sum_congr rfl fun p _ => hwin _
  · exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => hs p k
  · exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => hwin _

end GridShiftTransfer

end LevyStochCalc.Brownian.Ito

