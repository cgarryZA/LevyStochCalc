/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.VectorIncrement
import LevyStochCalc.Probability.IndepJoin

/-!
# The increment field of a Lévy driver along a grid

Over one interval the mixed increment tuple is independent of the joint filtration at the left
endpoint (`Driver/VectorIncrement.lean`). Along a grid `u 0 < u 1 < ⋯` the tuples of successive
intervals are jointly independent of `ℱ₊ (u 0)`, because each is measurable at the right endpoint
and independent of the filtration at the left one — that is `indep_iSup_lt_of_indep`. Increments
measured from `u 0` are sums of successive increments, so they generate a smaller σ-algebra and
inherit the independence.

## Main statements

* `LevyDriver.indep_iSup_stepSigma` — the successive tuples against `ℱ₊ (u 0)`.
* `LevyDriver.indep_iSup_stepSigma_start` — the tuples measured from `u 0`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

theorem incrementSigma_le_filtration (j : Fin d) {a b : ℝ} (hab : a ≤ b) :
    D.incrementSigma j a b ≤ D.filtration b :=
  ((((D.isBrownianFiltration j).measurable b).sub
    (((D.isBrownianFiltration j).measurable a).mono (D.filtration.mono hab) le_rfl))).comap_le

theorem countSigma_le_filtration (A : Set E) (hA : MeasurableSet A) {a b : ℝ} :
    D.countSigma A a b ≤ D.filtration b :=
  (D.isPoissonFiltration.measurable
    (Set.prod_mono Set.Ioc_subset_Iic_self (Set.subset_univ _))
    (measurableSet_Ioc.prod hA)).comap_le

theorem stepSigma_le_filtration {m : ℕ} (A : Fin m → Set E) (hA : ∀ k, MeasurableSet (A k))
    {a b : ℝ} (hab : a ≤ b) : D.stepSigma A a b ≤ D.filtration b :=
  sup_le (iSup_le fun j => D.incrementSigma_le_filtration j hab)
    (iSup_le fun k => D.countSigma_le_filtration (A k) (hA k))

theorem stepSigma_le {m : ℕ} (A : Fin m → Set E) (hA : ∀ k, MeasurableSet (A k)) (a b : ℝ) :
    D.stepSigma A a b ≤ ‹MeasurableSpace Ω› :=
  sup_le (iSup_le fun _ => (Brownian.comap_increment_le_sigmaBrownian _ a b).trans
      (Brownian.sigmaBrownian_le _))
    (iSup_le fun k => (D.countSigma_le (A k) (hA k) a b).trans (sigmaPoisson_le _))

/-- **The mixed increment tuples of the successive intervals of a grid are jointly independent of
the right-continuous filtration at its left endpoint.** -/
theorem indep_iSup_stepSigma {m : ℕ} (A : Fin m → Set E) (hA : ∀ k, MeasurableSet (A k))
    {g : ℕ → ℝ} (hg : StrictMono g) (hg0 : 0 ≤ g 0) (n : ℕ) :
    Indep (⨆ k, ⨆ _ : k < n, D.stepSigma A (g k) (g (k + 1)))
      (D.filtration.rightCont (g 0)) P :=
  Probability.indep_iSup_lt_of_indep
    (fun _ _ hab => D.filtration.rightCont.mono (hg.monotone hab))
    (fun k => D.filtration.rightCont.le (g k)) (fun _ => D.stepSigma_le A hA _ _)
    (fun k => (D.stepSigma_le_filtration A hA (hg (Nat.lt_succ_self k)).le).trans
      (D.filtration.le_rightCont (g (k + 1))))
    (fun k => (D.indep_stepSigma_rightCont A hA (hg0.trans (hg.monotone (Nat.zero_le k)))
      (hg (Nat.lt_succ_self k))).symm) n

/-- A Brownian increment measured from the start of the grid is measurable for the σ-algebra of
the successive increments. -/
theorem incrementSigma_start_le (j : Fin d) {g : ℕ → ℝ} {n : ℕ} (k : ℕ) (hk : k < n) :
    D.incrementSigma j (g 0) (g (k + 1))
      ≤ ⨆ l, ⨆ _ : l < n, D.incrementSigma j (g l) (g (l + 1)) := by
  induction k with
  | zero => exact le_iSup₂_of_le 0 hk le_rfl
  | succ k ih =>
    have heq : (fun ω => (D.W.W j).W (g (k + 2)) ω - (D.W.W j).W (g 0) ω)
        = fun ω => ((D.W.W j).W (g (k + 2)) ω - (D.W.W j).W (g (k + 1)) ω)
          + ((D.W.W j).W (g (k + 1)) ω - (D.W.W j).W (g 0) ω) := by
      funext ω; ring
    change MeasurableSpace.comap
      (fun ω => (D.W.W j).W (g (k + 2)) ω - (D.W.W j).W (g 0) ω) inferInstance ≤ _
    rw [heq]
    exact Probability.comap_add_le (le_iSup₂_of_le (k + 1) hk le_rfl)
      (ih (Nat.lt_of_succ_lt hk))

/-- A count measured from the start of the grid is measurable for the σ-algebra of the successive
counts. -/
theorem countSigma_start_le {A : Set E} (hA : MeasurableSet A) {g : ℕ → ℝ} (hg : Monotone g)
    {n : ℕ} (k : ℕ) (hk : k < n) :
    D.countSigma A (g 0) (g (k + 1))
      ≤ ⨆ l, ⨆ _ : l < n, D.countSigma A (g l) (g (l + 1)) := by
  induction k with
  | zero => exact le_iSup₂_of_le 0 hk le_rfl
  | succ k ih =>
    have hdisj : Disjoint (Set.Ioc (g 0) (g (k + 1)) ×ˢ A)
        (Set.Ioc (g (k + 1)) (g (k + 2)) ×ˢ A) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx'.1.1 (not_lt.2 hx.1.2)
    have hunion : Set.Ioc (g 0) (g (k + 2)) ×ˢ A
        = Set.Ioc (g 0) (g (k + 1)) ×ˢ A ∪ Set.Ioc (g (k + 1)) (g (k + 2)) ×ˢ A := by
      rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc (hg (Nat.zero_le _)) (hg (Nat.le_succ _))]
    have heq : (fun ω => D.N.N ω (Set.Ioc (g 0) (g (k + 2)) ×ˢ A))
        = fun ω => D.N.N ω (Set.Ioc (g 0) (g (k + 1)) ×ˢ A)
          + D.N.N ω (Set.Ioc (g (k + 1)) (g (k + 2)) ×ˢ A) := by
      funext ω
      rw [hunion, measure_union hdisj (measurableSet_Ioc.prod hA)]
    change MeasurableSpace.comap
      (fun ω => D.N.N ω (Set.Ioc (g 0) (g (k + 2)) ×ˢ A)) inferInstance ≤ _
    rw [heq]
    exact Probability.comap_add_le (ih (Nat.lt_of_succ_lt hk))
      (le_iSup₂_of_le (k + 1) hk le_rfl)

theorem stepSigma_start_le {m : ℕ} (A : Fin m → Set E) {g : ℕ → ℝ} (hg : Monotone g)
    (hA : ∀ k, MeasurableSet (A k)) (n : ℕ) :
    (⨆ k, ⨆ _ : k < n, D.stepSigma A (g 0) (g (k + 1)))
      ≤ ⨆ k, ⨆ _ : k < n, D.stepSigma A (g k) (g (k + 1)) := by
  refine iSup₂_le fun k hk => sup_le (iSup_le fun j => ?_) (iSup_le fun i => ?_)
  · exact (D.incrementSigma_start_le j k hk).trans
      (iSup₂_le fun l hl => le_iSup₂_of_le l hl
        (le_sup_of_le_left (le_iSup (fun j => D.incrementSigma j (g l) (g (l + 1))) j)))
  · exact (D.countSigma_start_le (hA i) hg k hk).trans
      (iSup₂_le fun l hl => le_iSup₂_of_le l hl
        (le_sup_of_le_right (le_iSup (fun i => D.countSigma (A i) (g l) (g (l + 1))) i)))

/-- **The increment tuples measured from the start of the grid are jointly independent of the
right-continuous filtration there.** -/
theorem indep_iSup_stepSigma_start {m : ℕ} (A : Fin m → Set E) (hA : ∀ k, MeasurableSet (A k))
    {g : ℕ → ℝ} (hg : StrictMono g) (hg0 : 0 ≤ g 0) (n : ℕ) :
    Indep (⨆ k, ⨆ _ : k < n, D.stepSigma A (g 0) (g (k + 1)))
      (D.filtration.rightCont (g 0)) P :=
  indep_of_indep_of_le_left (D.indep_iSup_stepSigma A hA hg hg0 n)
    (D.stepSigma_start_le A hg.monotone hA n)

end LevyDriver

end LevyStochCalc.Driver
