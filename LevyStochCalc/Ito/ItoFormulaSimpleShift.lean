/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaIncrement
import LevyStochCalc.Ito.JumpTelescope

/-!
# Itô's formula for an increment translated by a simple random vector

A random vector taking finitely many values and known at a stopping time `σ` that itself takes
finitely many values below a horizon decomposes the sample space into the finitely many cells on
which both the value of `σ` and the value of the vector are constant. On such a cell the
translation is by a fixed vector, so Itô's formula for the increment between `σ` and a later
stopping time applies with a constant shift, and the cell indicator — bounded and known at the
deterministic time carried by the cell — passes inside the Itô integral of the increment.

## Main statements

* `LevyStochCalc.Brownian.Ito.cellWeight` — the indicator of a cell of the decomposition.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_weight_mul_stopped_sub` — a bounded weight
  known at a deterministic time, times an increment vanishing up to that time, is progressively
  measurable.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellWeight

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}

/-- The indicator of the event that a stopping time takes the value `a` and a random mark takes
the value `v`. -/
noncomputable def cellWeight (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α) : Ω → ℝ :=
  Set.indicator {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} fun _ => (1 : ℝ)

variable (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

omit [MeasurableSpace Ω] in
theorem cellWeight_of_mem {ω : Ω} (hω : σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v) :
    cellWeight σ c a v ω = 1 :=
  Set.indicator_of_mem hω fun _ => (1 : ℝ)

omit [MeasurableSpace Ω] in
theorem cellWeight_of_notMem {ω : Ω} (hω : ¬ (σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v)) :
    cellWeight σ c a v ω = 0 :=
  Set.indicator_of_notMem hω fun _ => (1 : ℝ)

theorem abs_cellWeight_le_one (ω : Ω) : |cellWeight σ c a v ω| ≤ 1 := by
  by_cases hω : σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v
  · rw [cellWeight_of_mem σ c a v hω]; norm_num
  · rw [cellWeight_of_notMem σ c a v hω]; norm_num

theorem eq_of_cellWeight_ne_zero {ω : Ω} (hω : cellWeight σ c a v ω ≠ 0) :
    σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v := by
  by_contra hcon
  exact hω (cellWeight_of_notMem σ c a v hcon)

theorem le_of_cellWeight_ne_zero {ω : Ω} (hω : cellWeight σ c a v ω ≠ 0) :
    ((a : ℝ) : WithTop ℝ) ≤ σ ω :=
  le_of_eq (eq_of_cellWeight_ne_zero σ c a v hω).1.symm

theorem hitInd_mul_cellWeight (ω : Ω) :
    hitInd σ a ω * cellWeight σ c a v ω = cellWeight σ c a v ω := by
  by_cases hω : σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v
  · have h1 : hitInd σ a ω = 1 := by
      simp only [hitInd]
      exact Set.indicator_of_mem hω.1 fun _ => (1 : ℝ)
    rw [h1, one_mul]
  · rw [cellWeight_of_notMem σ c a v hω, mul_zero]

theorem measurable_cellWeight {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hset : MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v}) :
    Measurable (cellWeight σ c a v) := by
  simp only [cellWeight]
  exact measurable_const.indicator (ℱ.le a _ hset)

theorem stronglyMeasurable_cellWeight {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hset : MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v}) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (cellWeight σ c a v) := by
  letI : MeasurableSpace Ω := ℱ a
  simp only [cellWeight]
  exact (measurable_const.indicator hset).stronglyMeasurable

theorem cellWeight_eq_zero_of_notMem_left {J : Finset ℝ}
    (hσJ : ∀ ω, (∃ b ∈ J, σ ω = ((b : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤) (haJ : a ∉ J) (ω : Ω) :
    cellWeight σ c a v ω = 0 := by
  refine cellWeight_of_notMem σ c a v ?_
  rintro ⟨h1, -⟩
  rcases hσJ ω with ⟨b, hbJ, hb⟩ | htop
  · rw [h1] at hb
    have hab : a = b := by exact_mod_cast hb
    exact haJ (hab ▸ hbJ)
  · rw [htop] at h1
    simp at h1

theorem cellWeight_eq_zero_of_notMem_right {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs)
    (hv : v ∉ Vs) (ω : Ω) : cellWeight σ c a v ω = 0 := by
  refine cellWeight_of_notMem σ c a v ?_
  rintro ⟨-, h2⟩
  exact hv (h2 ▸ hcVs ω)

theorem sum_cellWeight_mul (J : Finset ℝ) (Vs : Finset α) (F : α → ℝ) {ω : Ω}
    (hcω : c ω ∈ Vs) {a₀ : ℝ} (ha₀ : a₀ ∈ J) (hσω : σ ω = ((a₀ : ℝ) : WithTop ℝ)) :
    ∑ x ∈ J ×ˢ Vs, cellWeight σ c x.1 x.2 ω * F x.2 = F (c ω) := by
  refine (Finset.sum_eq_single_of_mem (a₀, c ω) (Finset.mem_product.mpr ⟨ha₀, hcω⟩) ?_).trans ?_
  · rintro ⟨x₁, x₂⟩ - hne
    have hz : cellWeight σ c x₁ x₂ ω = 0 := by
      refine cellWeight_of_notMem σ c x₁ x₂ ?_
      rintro ⟨h1, h2⟩
      have hcoe : ((x₁ : ℝ) : WithTop ℝ) = ((a₀ : ℝ) : WithTop ℝ) := by rw [← h1, hσω]
      have hx1 : x₁ = a₀ := by exact_mod_cast hcoe
      exact hne (by rw [hx1, ← h2])
    rw [hz, zero_mul]
  · rw [cellWeight_of_mem σ c a₀ (c ω) ⟨hσω, rfl⟩, one_mul]

theorem sum_cellWeight_mul_of_top (J : Finset ℝ) (Vs : Finset α) (F : α → ℝ) {ω : Ω}
    (hσω : σ ω = ⊤) : ∑ x ∈ J ×ˢ Vs, cellWeight σ c x.1 x.2 ω * F x.2 = 0 := by
  refine Finset.sum_eq_zero fun x _ => ?_
  have hz : cellWeight σ c x.1 x.2 ω = 0 := by
    refine cellWeight_of_notMem σ c x.1 x.2 ?_
    rintro ⟨h1, -⟩
    rw [hσω] at h1
    simp at h1
  rw [hz, zero_mul]

end CellWeight

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Progressive measurability is local in time: it suffices to match, on each window `s ≤ t`, a
progressively measurable process. -/
theorem progressivelyMeasurable_of_agree {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {H : Ω → ℝ → ℝ}
    (h : ∀ t : ℝ, ∃ G : Ω → ℝ → ℝ, Probability.ProgressivelyMeasurable ℱ G ∧
      ∀ ω s, s ≤ t → H ω s = G ω s) :
    Probability.ProgressivelyMeasurable ℱ H := by
  intro t
  obtain ⟨G, hG, hHG⟩ := h t
  have hfun : (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2)
      = fun p : Ω × ℝ => (Set.Iic t).indicator (G p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      exact hHG p.1 p.2 (Set.mem_Iic.mp hp)
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp]
  rw [hfun]
  exact hG t

variable {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

/-- A bounded weight known at a deterministic time, times the increment of an integrand between
two stopping times the earlier of which is at or beyond that time where the weight is nonzero, is
progressively measurable. -/
theorem progressivelyMeasurable_weight_mul_stopped_sub
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) {a : ℝ} (ha : 0 ≤ a) {V : Ω → ℝ}
    (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    (hV0 : ∀ ω, V ω ≠ 0 → ((a : ℝ) : WithTop ℝ) ≤ σ ω)
    {K : Ω → ℝ → ℝ} (hpK : Probability.ProgressivelyMeasurable ℱ K) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      V ω * (Probability.stopped τ K ω s - Probability.stopped σ K ω s) := by
  have hpD : Probability.ProgressivelyMeasurable ℱ
      (fun ω s => Probability.stopped τ K ω s - Probability.stopped σ K ω s) :=
    (Probability.ProgressivelyMeasurable.stopped hτ hpK).sub
      (Probability.ProgressivelyMeasurable.stopped hσ hpK)
  have hzero : ∀ (ω : Ω) (s : ℝ), s ≤ a →
      V ω * (Probability.stopped τ K ω s - Probability.stopped σ K ω s) = 0 := by
    intro ω s hs
    by_cases hV : V ω = 0
    · rw [hV, zero_mul]
    · have hsσ : ((s : ℝ) : WithTop ℝ) ≤ σ ω :=
        le_trans (by exact_mod_cast hs) (hV0 ω hV)
      rw [stopped_sub_stopped_eq_zero hστ K ω hsσ, mul_zero]
  refine progressivelyMeasurable_of_agree fun t => ?_
  rcases le_or_gt t a with hta | hat
  · refine ⟨fun _ _ => (0 : ℝ), Probability.progressivelyMeasurable_zero ℱ, ?_⟩
    intro ω s hs
    exact hzero ω s (le_trans hs hta)
  · refine ⟨fun ω s => V ω * indIoc Ω a t ω s
      * (Probability.stopped τ K ω s - Probability.stopped σ K ω s),
      (progressivelyMeasurable_mul_indIoc ℱ ha hat hVb hVm hVa).mul hpD, ?_⟩
    intro ω s hs
    show V ω * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)
      = V ω * indIoc Ω a t ω s
        * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)
    rcases le_or_gt s a with h1 | h1
    · rw [hzero ω s h1]
      have hi : indIoc Ω a t ω s = 0 := by
        simp only [indIoc]
        exact Set.indicator_of_notMem
          (fun hm => absurd (Set.mem_Ioc.mp hm).1 (not_lt.mpr h1)) fun _ => (1 : ℝ)
      rw [hi]; ring
    · have hi : indIoc Ω a t ω s = 1 := by
        simp only [indIoc]
        exact Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨h1, hs⟩) fun _ => (1 : ℝ)
      rw [hi]; ring

/-- A bounded weight times the increment of an integrand between two stopping times has
measurable uncurrying. -/
theorem measurable_weight_mul_stopped_sub
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {V : Ω → ℝ} (hVm : Measurable V) {K : Ω → ℝ → ℝ}
    (hmK : Measurable (Function.uncurry K)) :
    Measurable (Function.uncurry fun ω s =>
      V ω * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)) :=
  (hVm.comp measurable_fst).mul (measurable_uncurry_stopped_sub hσ hτ hmK)

end Weight

section WeightEnergy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

/-- A weight bounded by one times the increment of an integrand between two stopping times has
finite energy on every bounded window. -/
theorem energy_weight_mul_stopped_sub_lt_top
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {V : Ω → ℝ} (hV1 : ∀ ω, |V ω| ≤ 1) {K : Ω → ℝ → ℝ}
    (hmK : Measurable (Function.uncurry K))
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖V ω * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ := by
  refine energy_lt_top_of_abs_le (P := P) (fun ω s => ?_)
    (energy_stopped_sub_lt_top hσ hτ hmK hqK)
  rw [abs_mul]
  calc |V ω| * |Probability.stopped τ K ω s - Probability.stopped σ K ω s|
      ≤ 1 * |Probability.stopped τ K ω s - Probability.stopped σ K ω s| := by
        gcongr; exact hV1 ω
    _ = |Probability.stopped τ K ω s - Probability.stopped σ K ω s| := one_mul _

end WeightEnergy

end LevyStochCalc.Brownian.Ito
