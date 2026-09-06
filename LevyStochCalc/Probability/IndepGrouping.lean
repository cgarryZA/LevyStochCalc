/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Independence.Basic

/-!
# Grouping an independent family along the fibres of a product index

An independent family of σ-algebras (or random variables) indexed by pairs `(i, j)` stays
independent after grouping along the second coordinate: the σ-algebras `⨆ i, m (i, j)` are
independent in `j`, and the random vectors `(Y (i, j))ᵢ` are independent in `j`.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω ι κ : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- An independent family of σ-algebras indexed by pairs, grouped along the second
coordinate. -/
theorem iIndep_iSup_fiber {m : ι × κ → MeasurableSpace Ω} (h_le : ∀ q, m q ≤ mΩ)
    (h : iIndep m μ) : iIndep (fun j => ⨆ i, m (i, j)) μ := by
  classical
  rw [iIndep_iff]
  intro s
  induction s using Finset.induction_on with
  | empty => intro f _; simp
  | @insert j₀ s hj₀ ih =>
    intro f hf
    have hind := indep_iSup_of_disjoint h_le h (S := {q : ι × κ | q.2 = j₀})
      (T := {q : ι × κ | q.2 ∈ s}) (by
        rw [Set.disjoint_left]
        rintro ⟨i, j⟩ (hj : j = j₀) (hj' : j ∈ s)
        exact hj₀ (hj ▸ hj'))
    rw [Indep_iff] at hind
    have h1 : MeasurableSet[⨆ q ∈ {q : ι × κ | q.2 = j₀}, m q] (f j₀) := by
      refine MeasurableSpace.le_def.mp (iSup_le fun i => ?_) _ (hf j₀ (Finset.mem_insert_self _ _))
      exact le_iSup₂_of_le (i, j₀) rfl le_rfl
    have h2 : MeasurableSet[⨆ q ∈ {q : ι × κ | q.2 ∈ s}, m q] (⋂ j ∈ s, f j) := by
      refine MeasurableSet.biInter s.countable_toSet fun j hj => ?_
      refine MeasurableSpace.le_def.mp (iSup_le fun i => ?_) _ (hf j (Finset.mem_insert_of_mem hj))
      exact le_iSup₂_of_le (i, j) hj le_rfl
    rw [Finset.set_biInter_insert, hind _ _ h1 h2, Finset.prod_insert hj₀,
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

/-- Independent random variables indexed by pairs, grouped into random vectors along the
second coordinate. -/
theorem iIndepFun_fiber {𝓧 : ι × κ → Type*} [∀ q, MeasurableSpace (𝓧 q)] {Y : ∀ q, Ω → 𝓧 q}
    (mY : ∀ q, Measurable (Y q)) (h : iIndepFun Y μ) :
    iIndepFun (fun j ω (i : ι) => Y (i, j) ω) μ := by
  rw [iIndepFun_iff_iIndep] at h ⊢
  convert iIndep_iSup_fiber (fun q => (mY q).comap_le) h using 1
  funext j
  rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup]
  congr
  funext i
  rw [MeasurableSpace.comap_comp]
  rfl

end LevyStochCalc.Probability
