/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.SimpleChaos

/-!
# The degree-two chaos elements of a finite disjoint family of regions

`pairIndex k l` is the multi-degree carrying one unit at `k` and one at `l`. The chaos element of
that multi-degree is the product `Ñ(B k) Ñ(B l)` of two compensated counts when `k ≠ l`, and
`Ñ(B k) ^ 2 - N(B k)` when `k = l`. For two real profiles `c, c'` constant on each region of the
family, `markedSecondChaos N B c c'` is the quadratic polynomial
`(∑_k c_k Ñ(B k)) (∑_l c'_l Ñ(B l)) - ∑_k c_k c'_k N(B k)` in the counts of the family, and it
expands as the sum of the pair elements weighted by `c_k c'_l`.

On a pairwise disjoint family of regions of finite intensity these elements are centred, and
their Gram is `E[Ψ(c, c') Ψ(e, e')] = ⟨c, e⟩ ⟨c', e'⟩ + ⟨c, e'⟩ ⟨c', e⟩` for the bilinear form
`⟨a, a'⟩ = ∑_k a_k a'_k λ_k` built from the rates `λ_k = ν̂(B k)`; on strips
`B k = (a, b] ×ˢ A k` those rates are `(b - a) ν(A k)`. Both statements come from the
multi-degree orthogonality of `Poisson/SimpleChaos.lean`, the norming `∏_k α_k ! λ_k ^ α_k` at a
pair index, and the fact that two pair indices agree exactly when the pairs agree up to order.

Pairwise disjointness of the family is a hypothesis throughout; overlapping regions are not
covered. The bilinear form is degenerate wherever `λ_k = 0`, and the Gram reads `0 = 0` there.

## Main statements

* `LevyStochCalc.Poisson.pairIndex_eq_iff` — `pairIndex k l = pairIndex k' l'` exactly when
  `(k, l)` and `(k', l')` agree, possibly after a swap.
* `LevyStochCalc.Poisson.poissonChaosProd_pairIndex` — the pair element in closed form,
  `Ñ(B k) Ñ(B l) - δ_(k l) N(B k)`.
* `LevyStochCalc.Poisson.prod_pairIndex_norming` — the norming `∏_k α_k ! λ_k ^ α_k` at a pair
  index is `λ_k λ_l`, doubled on the diagonal.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_pairIndex_mul` — the bilinear moment of two
  pair elements.
* `LevyStochCalc.Poisson.markedSecondChaos_eq_sum` — the quadratic element is the sum of the
  pair elements weighted by `c_k c'_l`.
* `LevyStochCalc.Poisson.integral_markedSecondChaos` — the quadratic elements are centred.
* `LevyStochCalc.Poisson.integral_markedSecondChaos_mul` — the Gram
  `⟨c, e⟩ ⟨c', e'⟩ + ⟨c, e'⟩ ⟨c', e⟩`.
* `LevyStochCalc.Poisson.integral_markedSecondChaos_strip_mul` — the same on strips
  `(a, b] ×ˢ A k` over pairwise disjoint mark sets of finite intensity, at the rates
  `(b - a) ν(A k)`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The multi-degree of a pair of indices -/

/-- The multi-degree that puts one unit at `k` and one at `l`. -/
def pairIndex {p : ℕ} (k l : Fin p) : Fin p → ℕ :=
  fun j => (if j = k then 1 else 0) + (if j = l then 1 else 0)

/-- Two pair indices agree exactly when the pairs agree, possibly after a swap. -/
lemma pairIndex_eq_iff {p : ℕ} (k l k' l' : Fin p) :
    pairIndex k l = pairIndex k' l' ↔ (k = k' ∧ l = l') ∨ (k = l' ∧ l = k') := by
  classical
  constructor
  · intro h
    have hk := congrFun h k
    have hl := congrFun h l
    simp only [pairIndex] at hk hl
    by_cases h1 : k = l
    · subst h1
      by_cases h2 : k = k' <;> by_cases h3 : k = l' <;> simp_all
    · have h1' : l ≠ k := Ne.symm h1
      by_cases h2 : k = k' <;> by_cases h3 : k = l' <;> by_cases h4 : l = k' <;>
        by_cases h5 : l = l' <;> simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · funext j; simp [pairIndex, Nat.add_comm]

/-- A pair index is nonzero. -/
lemma pairIndex_ne_zero {p : ℕ} (k l : Fin p) : pairIndex k l ≠ fun _ => 0 := by
  intro h
  have hk := congrFun h k
  simp [pairIndex] at hk

/-- The chaos element of the pair `(k, l)` is the product of the two compensated counts when
`k ≠ l`. -/
lemma poissonChaosProd_pairIndex_of_ne (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) {k l : Fin p} (hkl : k ≠ l) (ω : Ω) :
    poissonChaosProd N (pairIndex k l) B ω
      = N.compensated (B k) ω * N.compensated (B l) ω := by
  classical
  rw [poissonChaosProd]
  rw [← Finset.prod_subset (Finset.subset_univ ({k, l} : Finset (Fin p))) ?_]
  · rw [Finset.prod_pair hkl]
    simp [pairIndex, hkl, Ne.symm hkl]
  · intro j _ hj
    have hjk : j ≠ k := fun h => hj (by simp [h])
    have hjl : j ≠ l := fun h => hj (by simp [h])
    simp [pairIndex, hjk, hjl]

/-- The chaos element of the pair `(k, k)` is the degree-two Charlier element of the region
`B k`. -/
lemma poissonChaosProd_pairIndex_self (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (k : Fin p) (ω : Ω) :
    poissonChaosProd N (pairIndex k k) B ω
      = N.compensated (B k) ω ^ 2 - (N.N ω (B k)).toReal := by
  classical
  rw [poissonChaosProd, Finset.prod_eq_single k]
  · rw [show pairIndex k k k = 2 by simp [pairIndex], poissonChaosStep_two]
  · intro j _ hj
    simp [pairIndex, hj]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

/-- The norming `∏_k α_k ! λ_k ^ α_k` at a pair index: `λ_k λ_l`, doubled on the diagonal. -/
lemma prod_pairIndex_norming {p : ℕ} (lam : Fin p → ℝ) (k l : Fin p) :
    (∏ j, ((pairIndex k l j).factorial : ℝ) * lam j ^ (pairIndex k l j))
      = if k = l then 2 * lam k * lam l else lam k * lam l := by
  classical
  by_cases hkl : k = l
  · subst hkl
    rw [Finset.prod_eq_single k, if_pos rfl]
    · rw [show pairIndex k k k = 2 by simp [pairIndex]]
      norm_num
      ring
    · intro j _ hj
      simp [pairIndex, hj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  · rw [if_neg hkl, ← Finset.prod_subset (Finset.subset_univ ({k, l} : Finset (Fin p))) ?_]
    · rw [Finset.prod_pair hkl]
      simp [pairIndex, hkl, Ne.symm hkl]
    · intro j _ hj
      have hjk : j ≠ k := fun h => hj (by simp [h])
      have hjl : j ≠ l := fun h => hj (by simp [h])
      simp [pairIndex, hjk, hjl]

/-- The bilinear moment of two pair chaos elements of a finite pairwise disjoint family of
regions of finite intensity. -/
theorem integral_poissonChaosProd_pairIndex_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (k l k' l' : Fin p) :
    ∫ ω, poissonChaosProd N (pairIndex k l) B ω
        * poissonChaosProd N (pairIndex k' l') B ω ∂P
      = (if k = k' ∧ l = l' then (referenceIntensity ν (B k)).toReal
            * (referenceIntensity ν (B l)).toReal else 0)
        + (if k = l' ∧ l = k' then (referenceIntensity ν (B k)).toReal
            * (referenceIntensity ν (B l)).toReal else 0) := by
  classical
  rw [integral_poissonChaosProd_mul N hB hd hfin,
    prod_pairIndex_norming (fun j => (referenceIntensity ν (B j)).toReal) k l]
  by_cases hp : pairIndex k l = pairIndex k' l'
  · rw [if_pos hp]
    rcases (pairIndex_eq_iff k l k' l').1 hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · by_cases hkl : k = l
      · subst hkl; simp; ring
      · simp [hkl]
    · by_cases hkl : k = l
      · subst hkl; simp; ring
      · simp [hkl]
  · rw [if_neg hp]
    have c1 : ¬(k = k' ∧ l = l') := fun h =>
      hp ((pairIndex_eq_iff k l k' l').2 (Or.inl h))
    have c2 : ¬(k = l' ∧ l = k') := fun h =>
      hp ((pairIndex_eq_iff k l k' l').2 (Or.inr h))
    rw [if_neg c1, if_neg c2, add_zero]

/-- The chaos element of a pair of indices, in closed form. -/
lemma poissonChaosProd_pairIndex (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (k l : Fin p) (ω : Ω) :
    poissonChaosProd N (pairIndex k l) B ω
      = N.compensated (B k) ω * N.compensated (B l) ω
        - (if k = l then (N.N ω (B k)).toReal else 0) := by
  classical
  by_cases hkl : k = l
  · subst hkl
    rw [poissonChaosProd_pairIndex_self, if_pos rfl, sq]
  · rw [poissonChaosProd_pairIndex_of_ne N B hkl, if_neg hkl, sub_zero]

/-! ### The quadratic element of two profiles -/

/-- The degree-two chaos element of a finite family of regions carried by two profiles constant
on each region: the product of the two compensated integrals minus the count of their product. -/
noncomputable def markedSecondChaos (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℝ) (ω : Ω) : ℝ :=
  (∑ k, c k * N.compensated (B k) ω) * (∑ l, c' l * N.compensated (B l) ω)
    - ∑ k, c k * c' k * (N.N ω (B k)).toReal

/-- The quadratic element is the sum of the pair elements weighted by `c_k c'_l`. -/
lemma markedSecondChaos_eq_sum (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℝ) (ω : Ω) :
    markedSecondChaos N B c c' ω
      = ∑ k, ∑ l, c k * c' l * poissonChaosProd N (pairIndex k l) B ω := by
  classical
  simp_rw [poissonChaosProd_pairIndex, mul_sub, Finset.sum_sub_distrib, markedSecondChaos,
    Finset.sum_mul_sum]
  refine congrArg₂ (· - ·) ?_ ?_
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Ne.symm hl]
    · intro hk; exact absurd (Finset.mem_univ k) hk

/-- The quadratic elements of a finite pairwise disjoint family of regions of finite intensity
are centred under `P`. -/
theorem integral_markedSecondChaos (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c c' : Fin p → ℝ) :
    ∫ ω, markedSecondChaos N B c c' ω ∂P = 0 := by
  classical
  have hpt : (fun ω => markedSecondChaos N B c c' ω)
      = fun ω => ∑ q : Fin p × Fin p,
          c q.1 * c' q.2 * poissonChaosProd N (pairIndex q.1 q.2) B ω := by
    funext ω
    rw [markedSecondChaos_eq_sum, Fintype.sum_prod_type]
  rw [hpt, integral_finsetSum _ fun q _ =>
    Integrable.const_mul (integrable_poissonChaosProd N hB hd hfin _) _]
  refine Finset.sum_eq_zero fun q _ => ?_
  rw [integral_const_mul,
    integral_poissonChaosProd_eq_zero N hB hd hfin (pairIndex_ne_zero q.1 q.2), mul_zero]

private lemma sum_prod_ite_diag {A : Type*} [Fintype A] [DecidableEq A] (f : A × A → ℝ) :
    ∑ r : A × A, (if r.1 = r.2 then f r else 0) = ∑ q : A, f (q, q) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq Finset.univ q (fun q' => f (q, q'))]
  simp

private lemma sum_prod_ite_swap {α : Type*} [Fintype α] [DecidableEq α]
    (f : (α × α) × (α × α) → ℝ) :
    ∑ r : (α × α) × (α × α), (if Prod.swap r.1 = r.2 then f r else 0)
      = ∑ q : α × α, f (q, Prod.swap q) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_ite_eq Finset.univ (Prod.swap q) (fun q' => f (q, q'))]
  simp

/-- The Gram of the quadratic elements of a finite pairwise disjoint family of regions of finite
intensity: with `⟨a, a'⟩ = ∑_k a_k a'_k λ_k` for the rates `λ_k = ν̂(B k)`,
`E[Ψ(c, c') Ψ(e, e')] = ⟨c, e⟩ ⟨c', e'⟩ + ⟨c, e'⟩ ⟨c', e⟩`. -/
theorem integral_markedSecondChaos_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (c c' e e' : Fin p → ℝ) :
    ∫ ω, markedSecondChaos N B c c' ω * markedSecondChaos N B e e' ω ∂P
      = (∑ k, c k * e k * (referenceIntensity ν (B k)).toReal)
          * (∑ k, c' k * e' k * (referenceIntensity ν (B k)).toReal)
        + (∑ k, c k * e' k * (referenceIntensity ν (B k)).toReal)
          * (∑ k, c' k * e k * (referenceIntensity ν (B k)).toReal) := by
  classical
  have hsum : ∀ (a a' : Fin p → ℝ) (ω : Ω), markedSecondChaos N B a a' ω
      = ∑ q : Fin p × Fin p, a q.1 * a' q.2 * poissonChaosProd N (pairIndex q.1 q.2) B ω := by
    intro a a' ω
    rw [markedSecondChaos_eq_sum, Fintype.sum_prod_type]
  have hpt : (fun ω => markedSecondChaos N B c c' ω * markedSecondChaos N B e e' ω)
      = fun ω => ∑ r : (Fin p × Fin p) × (Fin p × Fin p),
          (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
            * (poissonChaosProd N (pairIndex r.1.1 r.1.2) B ω
              * poissonChaosProd N (pairIndex r.2.1 r.2.2) B ω) := by
    funext ω
    rw [Fintype.sum_prod_type (f := fun r : (Fin p × Fin p) × (Fin p × Fin p) =>
      (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
        * (poissonChaosProd N (pairIndex r.1.1 r.1.2) B ω
          * poissonChaosProd N (pairIndex r.2.1 r.2.2) B ω))]
    rw [hsum, hsum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun q' _ => by ring
  rw [hpt, integral_finsetSum _ fun r _ =>
    Integrable.const_mul (integrable_poissonChaosProd_mul N hB hd hfin _ _) _]
  have hone : ∀ r : (Fin p × Fin p) × (Fin p × Fin p),
      ∫ ω, (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
          * (poissonChaosProd N (pairIndex r.1.1 r.1.2) B ω
            * poissonChaosProd N (pairIndex r.2.1 r.2.2) B ω) ∂P
        = (if r.1 = r.2 then (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
              * ((referenceIntensity ν (B r.1.1)).toReal
                * (referenceIntensity ν (B r.1.2)).toReal) else 0)
          + (if Prod.swap r.1 = r.2 then (c r.1.1 * c' r.1.2 * (e r.2.1 * e' r.2.2))
              * ((referenceIntensity ν (B r.1.1)).toReal
                * (referenceIntensity ν (B r.1.2)).toReal) else 0) := by
    intro r
    rw [integral_const_mul,
      integral_poissonChaosProd_pairIndex_mul N hB hd hfin r.1.1 r.1.2 r.2.1 r.2.2]
    have h1 : (r.1.1 = r.2.1 ∧ r.1.2 = r.2.2) ↔ r.1 = r.2 := by
      obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := r; simp [Prod.ext_iff]
    have h2 : (r.1.1 = r.2.2 ∧ r.1.2 = r.2.1) ↔ Prod.swap r.1 = r.2 := by
      obtain ⟨⟨a, b⟩, ⟨a', b'⟩⟩ := r; simp [Prod.ext_iff, and_comm]
    simp only [h1, h2, mul_add, mul_ite, mul_zero]
  simp_rw [hone]
  rw [Finset.sum_add_distrib, sum_prod_ite_diag, sum_prod_ite_swap]
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine congrArg₂ (· + ·) ?_ ?_
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
  · exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by
      simp only [Prod.swap_prod_mk]; ring

/-- The Gram of the quadratic elements carried by strips `(a, b] ×ˢ A k` over a finite pairwise
disjoint family of mark sets of finite intensity, at the rates `(b - a) ν(A k)`. -/
theorem integral_markedSecondChaos_strip_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l))
    (c c' e e' : Fin p → ℝ) :
    ∫ ω, markedSecondChaos N (fun k => Set.Ioc a b ×ˢ A k) c c' ω
        * markedSecondChaos N (fun k => Set.Ioc a b ×ˢ A k) e e' ω ∂P
      = (∑ k, c k * e k * ((b - a) * (ν (A k)).toReal))
          * (∑ k, c' k * e' k * ((b - a) * (ν (A k)).toReal))
        + (∑ k, c k * e' k * ((b - a) * (ν (A k)).toReal))
          * (∑ k, c' k * e k * ((b - a) * (ν (A k)).toReal)) := by
  have hdB : Pairwise fun k l =>
      Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  rw [integral_markedSecondChaos_mul N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))]
  simp_rw [referenceIntensity_strip_toReal ha hab]

end LevyStochCalc.Poisson
