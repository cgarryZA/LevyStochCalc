/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Data.Nat.Choose.Multinomial
import LevyStochCalc.Poisson.SecondChaos

/-!
# The degree-`s` chaos element of a profile on finitely many disjoint regions

For a Poisson random measure `N` with reference intensity `ν̂`, a finite family `B` of pairwise
disjoint regions of finite intensity `λ_k = ν̂(B k)` and a profile `c` constant on each region,
the degree-`s` element `D_s(c)` is the multinomial combination
`∑_(|α| = s) (s! / ∏_k α_k!) (∏_k c_k ^ α_k) ∏_k C_(α_k)(N(B k); λ_k)` of the products of Charlier
polynomials of the counts of the regions. It is a polynomial of degree `s` in those counts: the
degree-zero element is `1`, the degree-one element is `∑_k c_k Ñ(B k)`, and on a one-region
family the element is `c ^ s` times the degree-`s` Charlier element of the region.

The degree elements are square integrable, centred in positive degree and orthogonal across
degrees, with the Gram `E[D_s(c) D_t(c')] = δ_(s t) s! ⟨c, c'⟩ ^ s` for the bilinear form
`⟨c, c'⟩ = ∑_k c_k c'_k λ_k`; on strips `(a, b] ×ˢ A k` the rates are `(b − a) ν(A k)`. The Gram
rests on the orthogonality of the products of Charlier polynomials across multi-degrees, with the
norming `∏_k α_k! λ_k ^ α_k`, and on the multinomial identity
`∑_(|α| = s) (s! / ∏ α_k!) ^ 2 (∏ α_k!) ∏ x_k ^ α_k = s! (∑ x_k) ^ s`. The degree-two element of
one profile is the quadratic element `markedSecondChaos` carried by that profile twice.

The bilinear form is degenerate on a region of zero intensity. The profile is constant on the
regions of one given family: no mode of `L²(ν)` beyond such combinations of indicators enters, and
no common refinement of two families is formed.

## Main definitions

* `LevyStochCalc.Poisson.markedChaosDegree` — the degree-`s` element of a profile on a finite
  family of regions.

## Main statements

* `LevyStochCalc.Poisson.sum_piAntidiag_multinomial_sq` — the multinomial identity behind the
  norming.
* `LevyStochCalc.Poisson.markedChaosDegree_one`, `LevyStochCalc.Poisson.markedChaosDegree_fin_one`
  — the degree-one element and the one-region case.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_mul` — the Gram
  `E[D_s(c) D_t(c')] = δ_(s t) s! ⟨c, c'⟩ ^ s`.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_strip_mul` — the same on strips, at the rates
  `(b − a) ν(A k)`.
* `LevyStochCalc.Poisson.markedChaosDegree_two` — the degree-two element is the quadratic element
  of the profile.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The algebraic core -/

/-- The multinomial identity behind the norming of the degree-`s` elements. -/
lemma sum_piAntidiag_multinomial_sq {R : Type*} [CommSemiring R] {p : ℕ} (s : ℕ)
    (x : Fin p → R) :
    ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
        (Nat.multinomial Finset.univ α : R) * (Nat.multinomial Finset.univ α : R)
          * (∏ k, ((α k).factorial : R)) * ∏ k, x k ^ α k
      = (s.factorial : R) * (∑ k, x k) ^ s := by
  rw [Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin p)) x s, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hs : ∑ k, α k = s := (Finset.mem_piAntidiag.1 hα).1
  have hspec : (∏ k, ((α k).factorial : R)) * (Nat.multinomial Finset.univ α : R)
      = (s.factorial : R) := by
    have hsp := Nat.multinomial_spec (Finset.univ : Finset (Fin p)) α
    have := congrArg (fun n : ℕ => (n : R)) hsp
    push_cast at this
    rw [this, hs]
  calc (Nat.multinomial Finset.univ α : R) * (Nat.multinomial Finset.univ α : R)
        * (∏ k, ((α k).factorial : R)) * ∏ k, x k ^ α k
      = ((∏ k, ((α k).factorial : R)) * (Nat.multinomial Finset.univ α : R))
          * ((Nat.multinomial Finset.univ α : R) * ∏ k, x k ^ α k) := by ring
    _ = (s.factorial : R) * ((Nat.multinomial Finset.univ α : R) * ∏ k, x k ^ α k) := by
        rw [hspec]

/-! ### The degree-`s` element of a mark profile -/

/-- The degree-`s` chaos element of a finite family of regions carried by a profile constant on
each region: the multinomial combination of the chaos elements of the multi-degrees of total
degree `s`. -/
noncomputable def markedChaosDegree (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) : ℝ :=
  ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
    (Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k) * poissonChaosProd N α B ω

/-- The degree-zero element is `1`. -/
@[simp] lemma markedChaosDegree_zero (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N 0 B c ω = 1 := by
  rw [markedChaosDegree, Finset.piAntidiag_zero]
  simp [Nat.multinomial, poissonChaosProd]

/-- The multi-degrees of total degree one are the unit multi-degrees. -/
lemma piAntidiag_univ_one (p : ℕ) :
    Finset.piAntidiag (Finset.univ : Finset (Fin p)) 1
      = Finset.image (fun k : Fin p => Pi.single k 1) Finset.univ := by
  classical
  ext α
  simp only [Finset.mem_piAntidiag, Finset.mem_image, Finset.mem_univ, true_and, ne_eq,
    implies_true, and_true]
  constructor
  · intro hs
    have hs1 : ∑ j, α j = 1 := hs
    obtain ⟨k, hk⟩ : ∃ k, α k = 1 := by
      by_contra hcon
      have hz : ∀ k : Fin p, α k = 0 := by
        intro k
        have hle : α k ≤ ∑ j, α j :=
          Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _) (Finset.mem_univ k)
        have hne : α k ≠ 1 := fun h => hcon ⟨k, h⟩
        omega
      have hzero : ∑ j, α j = 0 := Finset.sum_eq_zero fun j _ => hz j
      omega
    refine ⟨k, ?_⟩
    funext j
    rcases eq_or_ne j k with rfl | hj
    · simp [hk]
    · have hj' : j ∈ Finset.univ.erase k := Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩
      have hsplit : α k + ∑ i ∈ Finset.univ.erase k, α i = ∑ i, α i :=
        Finset.add_sum_erase Finset.univ α (Finset.mem_univ k)
      have hsub : α j ≤ ∑ i ∈ Finset.univ.erase k, α i :=
        Finset.single_le_sum (f := α) (fun i _ => Nat.zero_le _) hj'
      have hzj : α j = 0 := by omega
      simp [Pi.single_eq_of_ne hj, hzj]
  · rintro ⟨k, rfl⟩
    simp

/-- The degree-one element is the combination `∑_k c_k Ñ(B k)` of the compensated counts. -/
lemma markedChaosDegree_one (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N 1 B c ω = ∑ k, c k * N.compensated (B k) ω := by
  classical
  rw [markedChaosDegree, piAntidiag_univ_one, Finset.sum_image ?_]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have h2 : ∏ j, c j ^ (Pi.single k (1 : ℕ) j) = c k := by
      rw [Finset.prod_eq_single k]
      · simp
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [poissonChaosProd_single_one, Nat.multinomial_single, h2]
    norm_num
  · intro k _ l _ hkl
    by_contra hne
    have hc := congrFun hkl k
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne hne] at hc
    exact absurd hc one_ne_zero

/-! ### Measurability, integrability and the Gram -/

/-- The degree elements of a family of measurable regions are measurable. -/
theorem measurable_markedChaosDegree (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℝ) :
    Measurable (markedChaosDegree N s B c) :=
  Finset.measurable_sum _ fun α _ => (measurable_poissonChaosProd N α hB).const_mul _

/-- The product of two degree elements, expanded over the multi-degrees. -/
lemma markedChaosDegree_mul_eq_sum (N : PoissonRandomMeasure P ν) {p : ℕ} (s t : ℕ)
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N s B c ω * markedChaosDegree N t B c' ω
      = ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
          ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (poissonChaosProd N α B ω * poissonChaosProd N β B ω) := by
  rw [markedChaosDegree, markedChaosDegree, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => by ring

/-- The product of two degree elements of a finite pairwise disjoint family of regions of finite
intensity is integrable. -/
theorem integrable_markedChaosDegree_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s t : ℕ) (c c' : Fin p → ℝ) :
    Integrable (fun ω => markedChaosDegree N s B c ω * markedChaosDegree N t B c' ω) P := by
  rw [funext fun ω => markedChaosDegree_mul_eq_sum N s t B c c' ω]
  exact integrable_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (integrable_poissonChaosProd_mul N hB hd hfin α β).const_mul _

/-- The degree elements of a finite pairwise disjoint family of regions of finite intensity are
integrable. -/
theorem integrable_markedChaosDegree (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℝ) :
    Integrable (markedChaosDegree N s B c) P := by
  simpa using integrable_markedChaosDegree_mul N hB hd hfin s 0 c c

/-- The degree elements of a finite pairwise disjoint family of regions of finite intensity are
square integrable. -/
theorem memLp_two_markedChaosDegree (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℝ) :
    MemLp (markedChaosDegree N s B c) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (measurable_markedChaosDegree N s hB c).aestronglyMeasurable).2 ?_
  simpa only [pow_two] using integrable_markedChaosDegree_mul N hB hd hfin s s c c

/-- The degree elements of a finite pairwise disjoint family of regions of finite intensity are
orthogonal across degrees, with `E[D_s(c) D_t(c')] = δ_(s t) s ! ⟨c, c'⟩ ^ s` for the bilinear
form `⟨c, c'⟩ = ∑_k c_k c'_k λ_k` built from the rates `λ_k = ν̂(B k)`. -/
theorem integral_markedChaosDegree_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s t : ℕ) (c c' : Fin p → ℝ) :
    ∫ ω, markedChaosDegree N s B c ω * markedChaosDegree N t B c' ω ∂P
      = if s = t then (s.factorial : ℝ)
          * (∑ k, c k * c' k * (referenceIntensity ν (B k)).toReal) ^ s else 0 := by
  classical
  rw [funext fun ω => markedChaosDegree_mul_eq_sum N s t B c c' ω]
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    (integrable_poissonChaosProd_mul N hB hd hfin α β).const_mul _]
  have hinner : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
      ∫ ω, ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
          ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
            * (poissonChaosProd N α B ω * poissonChaosProd N β B ω) ∂P
        = ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℝ)
                  * (referenceIntensity ν (B k)).toReal ^ α k else 0) := by
    intro α _
    rw [integral_finsetSum _ fun β _ =>
      (integrable_poissonChaosProd_mul N hB hd hfin α β).const_mul _]
    exact Finset.sum_congr rfl fun β _ => by
      rw [integral_const_mul, integral_poissonChaosProd_mul N hB hd hfin α β]
  rw [Finset.sum_congr rfl hinner]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    have hdiag : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
        (∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
            ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℝ)
                  * (referenceIntensity ν (B k)).toReal ^ α k else 0))
          = (Nat.multinomial Finset.univ α : ℝ) * (Nat.multinomial Finset.univ α : ℝ)
              * (∏ k, ((α k).factorial : ℝ))
              * ∏ k, (c k * c' k * (referenceIntensity ν (B k)).toReal) ^ α k := by
      intro α hα
      have hstep : ∀ β, ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
            * (if α = β then ∏ k, ((α k).factorial : ℝ)
                * (referenceIntensity ν (B k)).toReal ^ α k else 0)
          = if α = β then ((Nat.multinomial Finset.univ α : ℝ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
              * (∏ k, ((α k).factorial : ℝ)
                  * (referenceIntensity ν (B k)).toReal ^ α k) else 0 := by
        intro β; rw [mul_ite, mul_zero]
      simp_rw [hstep]
      rw [Finset.sum_ite_eq _ α (fun β => ((Nat.multinomial Finset.univ α : ℝ)
        * (∏ k, c k ^ α k)) * ((Nat.multinomial Finset.univ β : ℝ) * (∏ k, c' k ^ β k))
        * (∏ k, ((α k).factorial : ℝ)
            * (referenceIntensity ν (B k)).toReal ^ α k)), if_pos hα]
      have e1 : ∏ k, ((α k).factorial : ℝ) * (referenceIntensity ν (B k)).toReal ^ α k
          = (∏ k, ((α k).factorial : ℝ))
            * ∏ k, (referenceIntensity ν (B k)).toReal ^ α k := Finset.prod_mul_distrib
      have e2 : ∏ k, (c k * c' k * (referenceIntensity ν (B k)).toReal) ^ α k
          = (∏ k, c k ^ α k) * (∏ k, c' k ^ α k)
            * ∏ k, (referenceIntensity ν (B k)).toReal ^ α k := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [e1, e2]
      ring
    rw [Finset.sum_congr rfl hdiag,
      sum_piAntidiag_multinomial_sq s (fun k => c k * c' k * (referenceIntensity ν (B k)).toReal)]
  · rw [if_neg hst]
    refine Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun β hβ => ?_
    have hne : α ≠ β := by
      rintro rfl
      exact hst (((Finset.mem_piAntidiag.1 hα).1).symm.trans (Finset.mem_piAntidiag.1 hβ).1)
    rw [if_neg hne, mul_zero]

/-- The degree elements of positive degree of a finite pairwise disjoint family of regions of
finite intensity are centred under `P`. -/
theorem integral_markedChaosDegree_eq_zero (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) {s : ℕ} (hs : s ≠ 0)
    (c : Fin p → ℝ) :
    ∫ ω, markedChaosDegree N s B c ω ∂P = 0 := by
  have h := integral_markedChaosDegree_mul N hB hd hfin s 0 c c
  simp only [markedChaosDegree_zero, mul_one, if_neg hs] at h
  exact h

/-! ### A one-region family and strips -/

/-- On a one-region family the multi-degrees of total degree `s` form a singleton. -/
lemma piAntidiag_univ_fin_one (s : ℕ) :
    Finset.piAntidiag (Finset.univ : Finset (Fin 1)) s = {fun _ => s} := by
  classical
  ext α
  simp only [Finset.mem_piAntidiag, Finset.mem_singleton, ne_eq, Finset.mem_univ, implies_true,
    and_true]
  constructor
  · intro hs
    funext j
    have hs1 : α 0 = s := by simpa using hs
    rw [Subsingleton.elim j 0, hs1]
  · rintro rfl
    simp

/-- On a one-region family the degree-`s` element is the degree-`s` Charlier element of the one
region, scaled by the `s`-th power of the value of the profile. -/
lemma markedChaosDegree_fin_one (N : PoissonRandomMeasure P ν) (s : ℕ)
    (B : Fin 1 → Set (ℝ × E)) (c : Fin 1 → ℝ) (ω : Ω) :
    markedChaosDegree N s B c ω = c 0 ^ s * poissonChaosStep N s (B 0) ω := by
  classical
  rw [markedChaosDegree, piAntidiag_univ_fin_one, Finset.sum_singleton]
  have hm : Nat.multinomial (Finset.univ : Finset (Fin 1)) (fun _ => s) = 1 := by simp
  rw [hm, poissonChaosProd]
  simp

/-- The Gram of the degree elements carried by strips `(a, b] ×ˢ A k` over a finite pairwise
disjoint family of mark sets of finite intensity, at the rates `(b - a) ν(A k)`. -/
theorem integral_markedChaosDegree_strip_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (s t : ℕ)
    (c c' : Fin p → ℝ) :
    ∫ ω, markedChaosDegree N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * markedChaosDegree N t (fun k => Set.Ioc a b ×ˢ A k) c' ω ∂P
      = if s = t then (s.factorial : ℝ)
          * (∑ k, c k * c' k * ((b - a) * (ν (A k)).toReal)) ^ s else 0 := by
  have hdB : Pairwise fun k l =>
      Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  rw [integral_markedChaosDegree_mul N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))]
  simp_rw [referenceIntensity_strip_toReal ha hab]

/-! ### The degree-two element -/

/-- A pair index is symmetric in its two arguments. -/
lemma pairIndex_comm {p : ℕ} (k l : Fin p) : pairIndex l k = pairIndex k l :=
  (pairIndex_eq_iff l k k l).2 (Or.inr ⟨rfl, rfl⟩)

/-- The total degree of a pair index is two. -/
lemma sum_pairIndex {p : ℕ} (k l : Fin p) : ∑ j, pairIndex k l j = 2 := by
  classical
  simp [pairIndex, Finset.sum_add_distrib]

/-- A pair index has total degree two. -/
lemma pairIndex_mem_piAntidiag {p : ℕ} (k l : Fin p) :
    pairIndex k l ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) 2 :=
  Finset.mem_piAntidiag.2 ⟨sum_pairIndex k l, fun _ _ => Finset.mem_univ _⟩

/-- The product of a profile over a pair index. -/
lemma prod_pow_pairIndex {p : ℕ} (c : Fin p → ℝ) (k l : Fin p) :
    ∏ j, c j ^ (pairIndex k l j) = c k * c l := by
  classical
  by_cases hkl : k = l
  · subst hkl
    rw [Finset.prod_eq_single k]
    · rw [show pairIndex k k k = 2 by simp [pairIndex]]; ring
    · intro j _ hj; simp [pairIndex, hj]
    · intro hk; exact absurd (Finset.mem_univ k) hk
  · rw [← Finset.prod_subset (Finset.subset_univ ({k, l} : Finset (Fin p))) ?_]
    · rw [Finset.prod_pair hkl]
      simp [pairIndex, hkl, Ne.symm hkl]
    · intro j _ hj
      have hjk : j ≠ k := fun h => hj (by simp [h])
      have hjl : j ≠ l := fun h => hj (by simp [h])
      simp [pairIndex, hjk, hjl]

/-- The multinomial coefficient of a pair index. -/
lemma multinomial_pairIndex {p : ℕ} (k l : Fin p) :
    (Nat.multinomial (Finset.univ : Finset (Fin p)) (pairIndex k l) : ℝ)
      = if k = l then 1 else 2 := by
  classical
  have hspec := congrArg (fun n : ℕ => (n : ℝ))
    (Nat.multinomial_spec (Finset.univ : Finset (Fin p)) (pairIndex k l))
  push_cast at hspec
  rw [sum_pairIndex] at hspec
  have hprod := prod_pairIndex_norming (fun _ : Fin p => (1 : ℝ)) k l
  simp only [one_pow, mul_one] at hprod
  rw [hprod] at hspec
  have hfac : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hfac] at hspec
  by_cases hkl : k = l
  · rw [if_pos hkl]
    rw [if_pos hkl] at hspec
    linarith
  · rw [if_neg hkl]
    rw [if_neg hkl] at hspec
    linarith

/-- The pairs carrying a given pair index. -/
lemma filter_pairIndex_eq {p : ℕ} (k l : Fin p) :
    {q ∈ (Finset.univ : Finset (Fin p × Fin p)) | pairIndex q.1 q.2 = pairIndex k l}
      = ({(k, l), (l, k)} : Finset (Fin p × Fin p)) := by
  classical
  ext q
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton, Prod.ext_iff]
  exact pairIndex_eq_iff q.1 q.2 k l

/-- Every multi-degree of total degree two is a pair index. -/
lemma exists_pairIndex_of_mem_piAntidiag_two {p : ℕ} {α : Fin p → ℕ}
    (hα : α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) 2) :
    ∃ k l : Fin p, α = pairIndex k l := by
  classical
  have hs : ∑ j, α j = 2 := (Finset.mem_piAntidiag.1 hα).1
  have hone : ∀ k : Fin p, α k ≤ 2 := fun k =>
    le_of_le_of_eq (Finset.single_le_sum (f := α) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ k)) hs
  have hpair : ∀ {k l : Fin p}, k ≠ l → α k + α l ≤ 2 := by
    intro k l hkl
    have hle := Finset.sum_le_sum_of_subset (f := α)
      (Finset.subset_univ ({k, l} : Finset (Fin p)))
    rw [Finset.sum_pair hkl] at hle
    omega
  have htriple : ∀ {k l j : Fin p}, k ≠ l → k ≠ j → l ≠ j →
      α k + α l + α j ≤ 2 := by
    intro k l j hkl hkj hlj
    have hle := Finset.sum_le_sum_of_subset (f := α)
      (Finset.subset_univ ({k, l, j} : Finset (Fin p)))
    rw [Finset.sum_insert (by simp [hkl, hkj]), Finset.sum_pair hlj] at hle
    omega
  obtain ⟨k, hk⟩ : ∃ k, α k ≠ 0 := by
    by_contra hcon
    have hz : ∑ j, α j = 0 :=
      Finset.sum_eq_zero fun j _ => not_not.1 fun h => hcon ⟨j, h⟩
    omega
  have hk2 := hone k
  rcases (by omega : α k = 2 ∨ α k = 1) with h2 | h1
  · refine ⟨k, k, funext fun j => ?_⟩
    rcases eq_or_ne j k with rfl | hj
    · rw [h2, show pairIndex j j j = 2 by simp [pairIndex]]
    · have := hpair (k := k) (l := j) (Ne.symm hj)
      have hzj : α j = 0 := by omega
      rw [hzj]
      simp [pairIndex, hj]
  · have hrest : ∑ j ∈ Finset.univ.erase k, α j = 1 := by
      have hsplit : α k + ∑ j ∈ Finset.univ.erase k, α j = ∑ j, α j :=
        Finset.add_sum_erase Finset.univ α (Finset.mem_univ k)
      omega
    obtain ⟨l, hlmem, hl⟩ : ∃ l ∈ Finset.univ.erase k, α l ≠ 0 := by
      by_contra hcon
      have := Finset.sum_eq_zero (s := Finset.univ.erase k) (f := α)
        fun j hj => not_not.1 fun h => hcon ⟨j, hj, h⟩
      omega
    have hlk : l ≠ k := (Finset.mem_erase.1 hlmem).1
    have hl1 : α l = 1 := by
      have := hpair (k := k) (l := l) (Ne.symm hlk)
      omega
    refine ⟨k, l, funext fun j => ?_⟩
    rcases eq_or_ne j k with rfl | hjk
    · rw [h1]
      simp [pairIndex, Ne.symm hlk]
    · rcases eq_or_ne j l with rfl | hjl
      · rw [hl1]
        simp [pairIndex, hjk]
      · have := htriple (k := k) (l := l) (j := j) (Ne.symm hlk) (Ne.symm hjk) (Ne.symm hjl)
        have hzj : α j = 0 := by omega
        rw [hzj]
        simp [pairIndex, hjk, hjl]

/-- The degree-two element is the sum of the pair elements weighted by `c_k c_l`. -/
lemma markedChaosDegree_two_eq_sum (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N 2 B c ω
      = ∑ k, ∑ l, c k * c l * poissonChaosProd N (pairIndex k l) B ω := by
  classical
  have hprod2 : ∑ q : Fin p × Fin p, c q.1 * c q.2 * poissonChaosProd N (pairIndex q.1 q.2) B ω
      = ∑ k, ∑ l, c k * c l * poissonChaosProd N (pairIndex k l) B ω :=
    Fintype.sum_prod_type (f := fun q : Fin p × Fin p =>
      c q.1 * c q.2 * poissonChaosProd N (pairIndex q.1 q.2) B ω)
  rw [markedChaosDegree, ← hprod2,
    ← Finset.sum_fiberwise_of_maps_to (t := Finset.piAntidiag (Finset.univ : Finset (Fin p)) 2)
      (g := fun q : Fin p × Fin p => pairIndex q.1 q.2)
      (fun q _ => pairIndex_mem_piAntidiag q.1 q.2)
      (fun q => c q.1 * c q.2 * poissonChaosProd N (pairIndex q.1 q.2) B ω)]
  refine Finset.sum_congr rfl fun α hα => ?_
  obtain ⟨k, l, rfl⟩ := exists_pairIndex_of_mem_piAntidiag_two hα
  rw [filter_pairIndex_eq, multinomial_pairIndex, prod_pow_pairIndex]
  by_cases hkl : k = l
  · subst hkl
    rw [if_pos rfl]
    simp
  · rw [if_neg hkl, Finset.sum_pair (by simp [Prod.ext_iff, hkl])]
    simp only [pairIndex_comm l k]
    ring

/-- The degree-two element carried by one profile is the quadratic element carried by that
profile twice. -/
theorem markedChaosDegree_two (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegree N 2 B c ω = markedSecondChaos N B c c ω := by
  rw [markedChaosDegree_two_eq_sum, markedSecondChaos_eq_sum]

end LevyStochCalc.Poisson
