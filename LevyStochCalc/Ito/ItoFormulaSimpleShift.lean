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
* `LevyStochCalc.Brownian.Ito.stopped_sub_eq_sum_cells` — the increment of an integrand read
  along a simple random mark is the sum of its cell integrands.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_simple` — that increment is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_cells` — the Itô integral of
  that increment splits over the cells.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_simpleShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a simple random vector.
* `LevyStochCalc.Brownian.Ito.measurableSet_cell_of_measurable` — a mark measurable at a stopping
  time has cells measurable at the deterministic times that stopping time takes.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section CellWeight

variable {Ω : Type u} {α : Type*}

/-- The indicator of the event that a stopping time takes the value `a` and a random mark takes
the value `v`. -/
noncomputable def cellWeight (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α) : Ω → ℝ :=
  Set.indicator {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} fun _ => (1 : ℝ)

variable (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

theorem cellWeight_of_mem {ω : Ω} (hω : σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v) :
    cellWeight σ c a v ω = 1 :=
  Set.indicator_of_mem hω fun _ => (1 : ℝ)

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

end CellWeight

section CellWeightMeasurable

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

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

end CellWeightMeasurable

section CellWeightSum

variable {Ω : Type u} {α : Type*} (σ : Ω → WithTop ℝ) (c : Ω → α) (a : ℝ) (v : α)

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

end CellWeightSum

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

section CellFamily

variable {Ω : Type u} {α : Type*} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

/-- Outside the product of the two value sets the cell integrand vanishes. -/
theorem cell_stopped_sub_eq_zero (hcVs : ∀ ω, c ω ∈ Vs)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (K : α → Ω → ℝ → ℝ) {x : ℝ × α} (hx : ¬ (x.1 ∈ J ∧ x.2 ∈ Vs)) :
    (fun (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s))
      = fun _ _ => (0 : ℝ) := by
  have hc0 : ∀ ω, cellWeight σ c x.1 x.2 ω = 0 := by
    by_cases h1 : x.1 ∈ J
    · exact cellWeight_eq_zero_of_notMem_right σ c x.1 x.2 hcVs fun hv => hx ⟨h1, hv⟩
    · exact cellWeight_eq_zero_of_notMem_left σ c x.1 x.2 hσJ h1
  funext ω s
  rw [hc0 ω, mul_zero, zero_mul]

/-- The increment of an integrand read along a simple random mark is the sum of the cell
integrands over the cells on which the earlier stopping time and the mark are constant. -/
theorem stopped_sub_eq_sum_cells (hστ : ∀ ω, σ ω ≤ τ ω) (hcVs : ∀ ω, c ω ∈ Vs)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (K : α → Ω → ℝ → ℝ) {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    (fun (ω : Ω) (s : ℝ) => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
      = fun (ω : Ω) (u : ℝ) => ∑ x ∈ J ×ˢ Vs, hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω u - Probability.stopped σ (K x.2) ω u) := by
  have hst : ∀ (ρ : Ω → WithTop ℝ) (ω : Ω) (s : ℝ),
      Probability.stopped ρ Kc ω s = Probability.stopped ρ (K (c ω)) ω s := by
    intro ρ ω s
    simp only [Probability.stopped, hKc]
  funext ω u
  have hrw : ∀ x ∈ J ×ˢ Vs, hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
      * (Probability.stopped τ (K x.2) ω u - Probability.stopped σ (K x.2) ω u)
      = cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω u - Probability.stopped σ (K x.2) ω u) :=
    fun x _ => by rw [hitInd_mul_cellWeight]
  rw [Finset.sum_congr rfl hrw]
  rcases hσJ ω with ⟨a₀, ha₀, hσω⟩ | htop
  · rw [sum_cellWeight_mul σ c J Vs
      (fun v => Probability.stopped τ (K v) ω u - Probability.stopped σ (K v) ω u)
      (hcVs ω) ha₀ hσω, hst τ ω u, hst σ ω u]
  · rw [sum_cellWeight_mul_of_top σ c J Vs
      (fun v => Probability.stopped τ (K v) ω u - Probability.stopped σ (K v) ω u) htop]
    have hτω : τ ω = ⊤ := top_le_iff.mp (htop ▸ hστ ω)
    have h1 : Probability.stopped τ Kc ω u = Kc ω u := by
      simp [Probability.stopped, hτω]
    have h2 : Probability.stopped σ Kc ω u = Kc ω u := by
      simp [Probability.stopped, htop]
    rw [h1, h2, sub_self]

end CellFamily

section CellFamilyProgressive

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
  {J : Finset ℝ}

/-- A finite sum of progressively measurable processes is progressively measurable. -/
theorem progressivelyMeasurable_finsetSum {ι : Type*}
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (A : ι → Ω → ℝ → ℝ)
    (hA : ∀ i, Probability.ProgressivelyMeasurable ℱ (A i)) (s : Finset ι) :
    Probability.ProgressivelyMeasurable ℱ fun ω u => ∑ i ∈ s, A i ω u := by
  classical
  induction s using Finset.induction with
  | empty =>
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ (∅ : Finset ι), A i ω u)
        = fun _ _ => (0 : ℝ) := by
      funext ω u
      simp
    rw [hfun]
    exact Probability.progressivelyMeasurable_zero ℱ
  | insert a s ha ih =>
    have hfun : (fun (ω : Ω) (u : ℝ) => ∑ i ∈ insert a s, A i ω u)
        = fun ω u => A a ω u + ∑ i ∈ s, A i ω u := by
      funext ω u
      exact Finset.sum_insert ha
    rw [hfun]
    exact (hA a).add ih

/-- The cell integrands attached to a simple random mark are progressively measurable. -/
theorem progressivelyMeasurable_cell_stopped_sub
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) (hcVs : ∀ ω, c ω ∈ Vs) (hJ0 : ∀ a ∈ J, 0 ≤ a)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    (x : ℝ × α) :
    Probability.ProgressivelyMeasurable ℱ
      (fun (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s)) := by
  have hVeq : (fun ω => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω)
      = cellWeight σ c x.1 x.2 := funext fun ω => hitInd_mul_cellWeight σ c x.1 x.2 ω
  by_cases hx : x.1 ∈ J ∧ x.2 ∈ Vs
  · refine progressivelyMeasurable_weight_mul_stopped_sub hσ hτ hστ (hJ0 x.1 hx.1)
      (V := fun ω => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω)
      ⟨1, fun ω => ?_⟩ ?_ ?_ ?_ (hpK x.2)
    · rw [hitInd_mul_cellWeight]
      exact abs_cellWeight_le_one σ c x.1 x.2 ω
    · rw [hVeq]
      exact measurable_cellWeight σ c x.1 x.2 (hcell x.1 hx.1 x.2 hx.2)
    · rw [hVeq]
      exact stronglyMeasurable_cellWeight σ c x.1 x.2 (hcell x.1 hx.1 x.2 hx.2)
    · intro ω hne
      rw [hitInd_mul_cellWeight] at hne
      exact le_of_cellWeight_ne_zero σ c x.1 x.2 hne
  · rw [cell_stopped_sub_eq_zero hcVs hσJ K hx]
    exact Probability.progressivelyMeasurable_zero ℱ

/-- The increment between two stopping times of an integrand read along a simple random mark
known at the earlier stopping time is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_simple
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) (hcVs : ∀ ω, c ω ∈ Vs) (hJ0 : ∀ a ∈ J, 0 ≤ a)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ
      (fun ω s => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s) := by
  rw [stopped_sub_eq_sum_cells (J := J) hστ hcVs hσJ K hKc]
  exact progressivelyMeasurable_finsetSum ℱ
    (fun (x : ℝ × α) (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
      * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s))
    (progressivelyMeasurable_cell_stopped_sub hσ hτ hστ hcVs hJ0 hσJ hcell K hpK) (J ×ˢ Vs)

end CellFamilyProgressive

section CellIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {α : Type*}
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integral of the increment of an integrand read along a simple random mark is the
sum, over the cells on which the earlier stopping time and the mark are constant, of the cell
indicator times the Itô integral of the increment of the integrand at the cell's mark.** -/
theorem stochasticIntegralBrownian_stopped_sub_cells
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {c : Ω → α} {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs)
    {J : Finset ℝ} {T : ℝ} (hJ0 : ∀ a ∈ J, 0 ≤ a) (hJT : ∀ a ∈ J, a < T)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (K : α → Ω → ℝ → ℝ) (hmK : ∀ v, Measurable (Function.uncurry (K v)))
    (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    (hqK : ∀ (v : α) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K v ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s)
    (hmc : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s))
    (hpc : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
    (hqc : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hT : 0 < T) :
    ∀ᵐ ω ∂P, stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
        hmc hpc hqc T ω
      = ∑ x ∈ J ×ˢ Vs, cellWeight σ c x.1 x.2 ω * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s)
          (measurable_uncurry_stopped_sub hσ hτ (hmK x.2))
          (progressivelyMeasurable_stopped_sub hσ hτ (hpK x.2))
          (energy_stopped_sub_lt_top hσ hτ (hmK x.2) (hqK x.2)) T ω := by
  classical
  have hVeq : ∀ x : ℝ × α, (fun ω => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω)
      = cellWeight σ c x.1 x.2 :=
    fun x => funext fun ω => hitInd_mul_cellWeight σ c x.1 x.2 ω
  have hgz : ∀ x : ℝ × α, ¬ (x.1 ∈ J ∧ x.2 ∈ Vs) →
      (fun (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s))
        = fun _ _ => (0 : ℝ) :=
    fun _ hx => cell_stopped_sub_eq_zero hcVs hσJ K hx
  have hgm : ∀ x : ℝ × α, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s)) := by
    intro x
    by_cases hx : x.1 ∈ J ∧ x.2 ∈ Vs
    · have hV : Measurable fun ω => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω := by
        rw [hVeq x]
        exact measurable_cellWeight σ c x.1 x.2 (hcell x.1 hx.1 x.2 hx.2)
      exact measurable_weight_mul_stopped_sub hσ hτ hV (hmK x.2)
    · rw [hgz x hx]
      exact measurable_const
  have hgp := progressivelyMeasurable_cell_stopped_sub hσ hτ hστ hcVs hJ0 hσJ hcell K hpK
  have hgq : ∀ (x : ℝ × α) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
        * (Probability.stopped τ (K x.2) ω s
          - Probability.stopped σ (K x.2) ω s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro x
    refine energy_weight_mul_stopped_sub_lt_top hσ hτ
      (V := fun ω => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω) (fun ω => ?_)
      (hmK x.2) (hqK x.2)
    rw [hitInd_mul_cellWeight]
    exact abs_cellWeight_le_one σ c x.1 x.2 ω
  have hsumEq := stopped_sub_eq_sum_cells (J := J) hστ hcVs hσJ K hKc
  obtain ⟨hms, hps, hqs, hae⟩ := exists_stochasticIntegralBrownian_finsetSum W ℱ hℱ
    (fun (x : ℝ × α) (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
      * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s))
    hgm hgp hgq (J ×ˢ Vs) hT
  have hcongr := stochasticIntegralBrownian_congr_fun W ℱ hℱ hsumEq hmc hpc hqc hms hps hqs T
  have hcells : ∀ᵐ ω ∂P, ∀ x ∈ J ×ˢ Vs,
      stochasticIntegralBrownian W ℱ hℱ
        (fun (ω : Ω) (s : ℝ) => hitInd σ x.1 ω * cellWeight σ c x.1 x.2 ω
          * (Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s))
        (hgm x) (hgp x) (hgq x) T ω
      = cellWeight σ c x.1 x.2 ω * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Probability.stopped τ (K x.2) ω s - Probability.stopped σ (K x.2) ω s)
          (measurable_uncurry_stopped_sub hσ hτ (hmK x.2))
          (progressivelyMeasurable_stopped_sub hσ hτ (hpK x.2))
          (energy_stopped_sub_lt_top hσ hτ (hmK x.2) (hqK x.2)) T ω := by
    rw [Filter.eventually_all_finset]
    intro x hx
    obtain ⟨haJ, hvVs⟩ := Finset.mem_product.mp hx
    have hpull := mul_stochasticIntegralBrownian_hitInd_stopped_sub W ℱ hℱ hσ hτ hστ
      (hJ0 x.1 haJ) (hJT x.1 haJ) ⟨1, abs_cellWeight_le_one σ c x.1 x.2⟩
      (measurable_cellWeight σ c x.1 x.2 (hcell x.1 haJ x.2 hvVs))
      (stronglyMeasurable_cellWeight σ c x.1 x.2 (hcell x.1 haJ x.2 hvVs))
      (hmK x.2) (hpK x.2) (hqK x.2) (hgm x) (hgp x) (hgq x)
    filter_upwards [hpull] with ω hω
    rw [← hω, hitInd_mul_cellWeight]
  filter_upwards [hae, hcells] with ω h1 h2
  refine (congrFun hcongr ω).trans (h1.trans ?_)
  exact Finset.sum_congr rfl h2

end CellIntegral

section SimpleShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in
/-- **Itô's formula for the increment of a path between two stopping times, for a function
translated by a random vector taking finitely many values and known at the earlier stopping
time.** -/
theorem itoFormula_between_simpleShift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s))
    (hpG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s)
    (hqG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω + v) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ (v : Fin n → ℝ) (p : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + v) * bdrift p ω s))
    (hqD : ∀ (v : Fin n → ℝ) (p : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X s ω + v) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ (v : Fin n → ℝ) (p q : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω + v) * ∑ k : Fin d, H p k ω s * H q k ω s))
    {T : ℝ} (hT : 0 < T)
    (hQint : ∀ v : Fin n → ℝ, ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => coordDeriv₂ f'' p q (X s ω + v) * ∑ k : Fin d, H p k ω s * H q k ω s)
      (Set.Ioc (0 : ℝ) T) volume)
    {c : Ω → Fin n → ℝ} {Vs : Finset (Fin n → ℝ)} (hcVs : ∀ ω, c ω ∈ Vs)
    {J : Finset ℝ} (hJ0 : ∀ a ∈ J, 0 ≤ a) (hJT : ∀ a ∈ J, a < T)
    (hσJ : ∀ ω, (∃ a ∈ J, σ ω = ((a : ℝ) : WithTop ℝ)) ∨ σ ω = ⊤)
    (hcell : ∀ a ∈ J, ∀ v ∈ Vs,
      MeasurableSet[ℱ' a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v})
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hconst : ∀ᵐ ω ∂P, ∀ v ∈ Vs,
      f (X (clipTime τ T ω) ω + v) - f (X (clipTime σ T ω) ω + v)
        = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ
                (fun ω s => coordDeriv f' p (X s ω + v) * bdrift p ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' p (X s ω + v) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped τ
                      (fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s) ω s
                    - Probability.stopped σ
                        (fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s) ω s)
                (measurable_uncurry_stopped_sub hσ hτ (hmG v p k))
                (progressivelyMeasurable_stopped_sub hσ hτ (hpG v p k))
                (energy_stopped_sub_lt_top hσ hτ (hmG v p k) (hqG v p k)) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + v)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + v)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
    rw [Filter.eventually_all_finset]
    intro v _
    exact itoFormula_between_shift W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq hσ hτ hσ0 hτ0
      hfC hf hf' v (hmG v) (hpG v) (hqG v) (hmD v) (hqD v) (hmQ v) hT (hQint v)
  have hitocells : ∀ (p : Fin n) (k : Fin d), ∀ᵐ ω ∂P,
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
        (hmSc p k) (hpSc p k) (hqSc p k) T ω
        = ∑ x ∈ J ×ˢ Vs, cellWeight σ c x.1 x.2 ω * stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + x.2) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + x.2) * H p k ω s) ω s)
            (measurable_uncurry_stopped_sub hσ hτ (hmG x.2 p k))
            (progressivelyMeasurable_stopped_sub hσ hτ (hpG x.2 p k))
            (energy_stopped_sub_lt_top hσ hτ (hmG x.2 p k) (hqG x.2 p k)) T ω := by
    intro p k
    exact stochasticIntegralBrownian_stopped_sub_cells (W.W k) ℱ' (hcoord k) hσ hτ hστ
      hcVs hJ0 hJT hσJ hcell (fun v ω s => coordDeriv f' p (X s ω + v) * H p k ω s)
      (fun v => hmG v p k) (fun v => hpG v p k) (fun v => hqG v p k)
      (Kc := fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) (fun _ _ => rfl)
      (hmSc p k) (hpSc p k) (hqSc p k) hT
  have hito := (MeasureTheory.ae_all_iff (μ := P)).2
    fun p : Fin n => (MeasureTheory.ae_all_iff (μ := P)).2 fun k : Fin d => hitocells p k
  filter_upwards [hconst, hito] with ω hcv hik
  rcases hσJ ω with ⟨a₀, ha₀, hσω⟩ | htop
  · have e2 : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω' s =>
              Probability.stopped τ
                  (fun ω' s => coordDeriv f' p (X s ω' + c ω) * H p k ω' s) ω' s
                - Probability.stopped σ
                    (fun ω' s => coordDeriv f' p (X s ω' + c ω) * H p k ω' s) ω' s)
            (measurable_uncurry_stopped_sub hσ hτ (hmG (c ω) p k))
            (progressivelyMeasurable_stopped_sub hσ hτ (hpG (c ω) p k))
            (energy_stopped_sub_lt_top hσ hτ (hmG (c ω) p k) (hqG (c ω) p k)) T ω)
        = ∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
            (hmSc p k) (hpSc p k) (hqSc p k) T ω := by
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => ?_
      refine ((hik p k).trans ?_).symm
      exact sum_cellWeight_mul σ c J Vs
        (fun v => stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
           (fun ω s =>
             Probability.stopped τ
                 (fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s) ω s
               - Probability.stopped σ
                   (fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s) ω s)
           (measurable_uncurry_stopped_sub hσ hτ (hmG v p k))
           (progressivelyMeasurable_stopped_sub hσ hτ (hpG v p k))
           (energy_stopped_sub_lt_top hσ hτ (hmG v p k) (hqG v p k)) T ω) (hcVs ω) ha₀ hσω
    refine (hcv (c ω) (hcVs ω)).trans ?_
    rw [e2]
    rfl
  · have hτω : τ ω = ⊤ := top_le_iff.mp (htop ▸ hστ ω)
    have hz : ∀ (F : Ω → ℝ → ℝ) (s : ℝ),
        Probability.stopped τ F ω s - Probability.stopped σ F ω s = 0 := by
      intro F s
      simp [Probability.stopped, htop, hτω]
    have hI : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            Probability.stopped τ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
          (hmSc p k) (hpSc p k) (hqSc p k) T ω) = 0 := by
      refine Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun k _ => ?_
      refine (hik p k).trans ?_
      exact sum_cellWeight_mul_of_top σ c J Vs
        (fun v => stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
           (fun ω s =>
             Probability.stopped τ
                 (fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s) ω s
               - Probability.stopped σ
                   (fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s) ω s)
           (measurable_uncurry_stopped_sub hσ hτ (hmG v p k))
           (progressivelyMeasurable_stopped_sub hσ hτ (hpG v p k))
           (energy_stopped_sub_lt_top hσ hτ (hmG v p k) (hqG v p k)) T ω) htop
    rw [clipTime_eq_self_of_top htop, clipTime_eq_self_of_top hτω, sub_self, hI]
    simp [hz]

end SimpleShift

section CellFromStoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {α : Type*}

/-- A cell on which a stopping time takes a deterministic value and a random mark known at that
stopping time takes a given value is measurable at that deterministic time. -/
theorem measurableSet_cell_of_measurableSpace {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α} {v : α} (a : ℝ)
    (hc : MeasurableSet[hσ.measurableSpace] {ω | c ω = v}) :
    MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} := by
  have hset : {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v}
      = {ω | c ω = v} ∩ {ω | σ ω = ((a : ℝ) : WithTop ℝ)} :=
    Set.ext fun _ => ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  rw [hset]
  exact (hσ.measurableSet_inter_eq_iff _ a).1
    (MeasurableSet.inter hc (hσ.measurableSet_eq' a))

/-- The cells of a random mark measurable at a stopping time are measurable at the deterministic
times the stopping time takes. -/
theorem measurableSet_cell_of_measurable [MeasurableSpace α] [MeasurableSingletonClass α]
    {ℱ : Filtration ℝ mΩ} {σ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (a : ℝ) (v : α) :
    MeasurableSet[ℱ a] {ω | σ ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} :=
  measurableSet_cell_of_measurableSpace hσ a (hc (measurableSet_singleton v))

end CellFromStoppingTime

end LevyStochCalc.Brownian.Ito
