/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.SimpleChaosDegreeComplex
import LevyStochCalc.Poisson.SimpleProfile
import LevyStochCalc.Probability.CharlierAdd

/-!
# Refinement of the degree-`s` chaos element of a profile, and its Gram across families

For a finite pairwise disjoint family `B` of regions of finite intensity and a complex profile
`c` constant on each region, the degree-`s` element `D_s(c; B)` is `s!` times the coefficient of
`X ^ s` in the product `∏_k S(λ_k, N(B k); c_k)` of the Charlier generating series of the regions,
`λ_k = ν̂(B k)`. By the Charlier addition formula a product of such series at a common scalar is
the series of the summed rates and counts, and the series at the scalar zero is `1`. Since the
count and the intensity are additive over disjoint regions, `D_s(c; B)` is unchanged, almost
surely, when each region is split into finitely many disjoint regions carrying its value and
regions carrying the value zero are added. Over the concatenation of two families the element
splits binomially, `D_s = ∑_(a + b = s) (s choose a) D_a D_b`.

Any two finite pairwise disjoint families `B`, `B'` of regions of finite intensity have a common
refinement, the points of their union sorted by the region of each family that contains them.
Passing both elements to it turns the Gram on one family into the Gram across families,

  `E[D_s(c; B) D_t(c'; B')] = δ_(s t) s! (∑_(k, l) c_k c'_l ν̂(B k ∩ B' l)) ^ s`,

and, with the conjugate, `E[D_s(c; B) conj D_t(c'; B')] = δ_(s t) s! ⟨c, c'⟩ ^ s` for the pairing
`⟨c, c'⟩ = ∑_(k, l) c_k conj c'_l ν̂(B k ∩ B' l)`. On strips `(a, b] ×ˢ A k`, `(a, b] ×ˢ A' l` the
pairing is `(b − a) ∫ f conj g dν` for the functions `f = ∑_k c_k 𝟙_(A k)`, `g = ∑_l c'_l 𝟙_(A' l)`.

## Main definitions

* `LevyStochCalc.Poisson.regionIndex` — the region of a family containing a point, if any.
* `LevyStochCalc.Poisson.commonRefinement` — the common refinement of two finite families.
* `LevyStochCalc.Poisson.markProfileC` — the function `∑_k c_k 𝟙_(A k)` of a complex profile.

## Main statements

* `LevyStochCalc.Poisson.markedChaosDegreeC_eq_coeff` — `D_s(c; B) = s! [X ^ s] ∏_k S_k`.
* `LevyStochCalc.Poisson.markedChaosDegreeC_append` — the binomial split over the concatenation
  of two families.
* `LevyStochCalc.Poisson.markedChaosDegreeC_ae_eq_of_refine` — invariance under refinement.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul_cross`,
  `LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul_conj_cross` — the Gram across two
  families of regions.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_mul_cross`,
  `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_mul_conj_cross` — the same on strips.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_mul_conj_markProfileC` — the same
  through the functions of the profiles, `δ_(s t) s! ((b − a) ∫ f conj g dν) ^ s`.
* `LevyStochCalc.Poisson.integral_markedChaosDegree_simpleProfile_mul` — the real Gram of two
  simple mark profiles on different families, `δ_(s t) s! ((b − a) ∫ f g dν) ^ s`.
* `LevyStochCalc.Poisson.markedChaosDegreeC_zero`, `LevyStochCalc.Poisson.markedChaosDegreeC_one`
  — the degree-zero element is `1` and the degree-one element is `∑_k c_k Ñ(B k)`.
-/

open MeasureTheory ProbabilityTheory PowerSeries Finset
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

open LevyStochCalc.Probability

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The degree element as a coefficient of a product of generating series -/

/-- The coefficient of `X ^ d` in a finite product of power series, as a sum over the
multi-degrees of total degree `d`. -/
theorem coeff_prod_eq_sum_piAntidiag {R : Type*} [CommSemiring R] {ι : Type*} [DecidableEq ι]
    (f : ι → PowerSeries R) (d : ℕ) (s : Finset ι) :
    coeff d (∏ j ∈ s, f j) = ∑ α ∈ piAntidiag s d, ∏ i ∈ s, coeff (α i) (f i) := by
  rw [coeff_prod, finsuppAntidiag, sum_map]
  exact sum_attach (piAntidiag s d) (fun α => ∏ i ∈ s, coeff (α i) (f i))

/-- The degree-`s` element of a complex profile is `s!` times the coefficient of `X ^ s` in the
product over the family of the Charlier generating series of the regions, at their rates and
counts. -/
theorem markedChaosDegreeC_eq_coeff (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) :
    markedChaosDegreeC N s B c ω = (s.factorial : ℂ) * coeff s (∏ k, charlierSeries
      (referenceIntensity ν (B k)).toReal (N.N ω (B k)).toReal (c k)) := by
  classical
  rw [coeff_prod_eq_sum_piAntidiag, Finset.mul_sum, markedChaosDegreeC]
  refine Finset.sum_congr rfl fun α hα => ?_
  have hs : ∑ k, α k = s := (mem_piAntidiag.1 hα).1
  have hspec : (∏ k, ((α k).factorial : ℂ)) * (Nat.multinomial univ α : ℂ)
      = (s.factorial : ℂ) := by
    have h := Nat.multinomial_spec (univ : Finset (Fin p)) α
    rw [hs] at h
    exact_mod_cast h
  have hne : (∏ k, ((α k).factorial : ℂ)) ≠ 0 :=
    prod_ne_zero_iff.2 fun k _ => by exact_mod_cast (α k).factorial_ne_zero
  simp_rw [coeff_charlierSeries]
  rw [poissonChaosProd, Complex.ofReal_prod, Finset.prod_mul_distrib, Finset.prod_div_distrib,
    ← hspec]
  simp only [poissonChaosStep]
  field_simp

/-- The binomial split of the degree element over the concatenation of two families,
`D_s(c ⊔ c'; B ⊔ B') = ∑_(i + j = s) (s choose i) D_i(c; B) D_j(c'; B')`. -/
theorem markedChaosDegreeC_append (N : PoissonRandomMeasure P ν) {p q : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (B' : Fin q → Set (ℝ × E)) (c : Fin p → ℂ) (c' : Fin q → ℂ)
    (ω : Ω) :
    markedChaosDegreeC N s (Fin.append B B') (Fin.append c c') ω
      = ∑ ij ∈ antidiagonal s, (s.choose ij.1 : ℂ)
          * (markedChaosDegreeC N ij.1 B c ω * markedChaosDegreeC N ij.2 B' c' ω) := by
  rw [markedChaosDegreeC_eq_coeff, Fin.prod_univ_add, coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have hn : ij.1 + ij.2 = s := mem_antidiagonal.1 hij
  simp only [Fin.append_left, Fin.append_right]
  rw [markedChaosDegreeC_eq_coeff, markedChaosDegreeC_eq_coeff]
  have hc : (s.choose ij.1 : ℂ) * ((ij.1.factorial : ℂ) * (ij.2.factorial : ℂ))
      = (s.factorial : ℂ) := by
    rw [← hn, ← mul_assoc, Nat.choose_symm_add]
    exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial ij.1 ij.2
  rw [← hc]
  ring

/-! ### Refinement -/

/-- Over a finite family indexed by `ι` whose members are sent to regions by `g` (or to none),
the product of the generating series at the scalars pulled back along `g`, zero off the regions,
is the product over the regions of the series of the summed rates and arguments. -/
theorem prod_charlierSeries_fiberwise {ι : Type*} [Fintype ι] {p : ℕ} (g : ι → Option (Fin p))
    (lam x : ι → ℝ) (c : Fin p → ℂ) :
    ∏ i, charlierSeries (lam i) (x i) ((g i).elim 0 c)
      = ∏ k, charlierSeries (∑ i ∈ univ.filter (fun i => g i = some k), lam i)
          (∑ i ∈ univ.filter (fun i => g i = some k), x i) (c k) := by
  classical
  rw [← Finset.prod_fiberwise univ g, Fintype.prod_option]
  have hnone : ∏ i ∈ univ.filter (fun i => g i = none),
      charlierSeries (lam i) (x i) ((g i).elim 0 c) = 1 :=
    prod_eq_one fun i hi => by rw [(mem_filter.1 hi).2]; exact charlierSeries_zero_scalar _ _
  rw [hnone, one_mul]
  refine prod_congr rfl fun k _ => ?_
  rw [← prod_charlierSeries]
  exact prod_congr rfl fun i hi => by rw [(mem_filter.1 hi).2]; rfl

/-- **Refinement, as generating series.** If each region `B k` is the union of the members of a
finite pairwise disjoint family `R` of regions of finite intensity that `g` sends to `k`, then
almost surely `D_s(c; B)` is `s!` times the coefficient of `X ^ s` in the product over `R` of the
generating series at the scalars pulled back along `g`, zero on the members sent to none. -/
theorem ae_markedChaosDegreeC_eq_coeff_refine (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {ι : Type*} [Fintype ι] {B : Fin p → Set (ℝ × E)} {R : ι → Set (ℝ × E)}
    (hR : ∀ i, MeasurableSet (R i)) (hRd : Pairwise fun i j => Disjoint (R i) (R j))
    (hRfin : ∀ i, referenceIntensity ν (R i) ≠ ⊤) (g : ι → Option (Fin p))
    (hBR : ∀ k, B k = ⋃ i ∈ univ.filter (fun i => g i = some k), R i) (s : ℕ)
    (c : Fin p → ℂ) :
    ∀ᵐ ω ∂P, markedChaosDegreeC N s B c ω = (s.factorial : ℂ) * coeff s (∏ i, charlierSeries
      (referenceIntensity ν (R i)).toReal (N.N ω (R i)).toReal ((g i).elim 0 c)) := by
  classical
  have hfin : ∀ᵐ ω ∂P, ∀ i, N.N ω (R i) ≠ ⊤ := ae_all_iff.2 fun i =>
    (N.integer_valued (hR i) (hRfin i)).mono fun ω ⟨n, hn⟩ => by
      rw [hn]; exact ENNReal.natCast_ne_top n
  filter_upwards [hfin] with ω hω
  rw [markedChaosDegreeC_eq_coeff, prod_charlierSeries_fiberwise]
  have hdisj : ∀ k, (↑(univ.filter (fun i => g i = some k)) : Set ι).PairwiseDisjoint R :=
    fun k i _ j _ hij => hRd hij
  have hmeas : ∀ k, ∀ i ∈ univ.filter (fun i => g i = some k), MeasurableSet (R i) :=
    fun k i _ => hR i
  refine congrArg _ (congrArg _ (prod_congr rfl fun k _ => ?_))
  rw [hBR k, measure_biUnion_finset (hdisj k) (hmeas k), measure_biUnion_finset (hdisj k)
    (hmeas k), ENNReal.toReal_sum fun i _ => hRfin i, ENNReal.toReal_sum fun i _ => hω i]

/-- **Refinement.** If each region `B k` is the union of the members of a finite pairwise
disjoint family `R` of regions of finite intensity that `g` sends to `k`, listed through
`e : ι ≃ Fin n`, then `D_s(c; B)` agrees almost surely with the degree element of `R` carrying
the values of `c` pulled back along `g`, and zero on the members sent to none. -/
theorem markedChaosDegreeC_ae_eq_of_refine (N : PoissonRandomMeasure.{u, v, w} P ν) {p n : ℕ}
    {ι : Type*} [Fintype ι] (e : ι ≃ Fin n) {B : Fin p → Set (ℝ × E)} {R : ι → Set (ℝ × E)}
    (hR : ∀ i, MeasurableSet (R i)) (hRd : Pairwise fun i j => Disjoint (R i) (R j))
    (hRfin : ∀ i, referenceIntensity ν (R i) ≠ ⊤) (g : ι → Option (Fin p))
    (hBR : ∀ k, B k = ⋃ i ∈ univ.filter (fun i => g i = some k), R i) (s : ℕ)
    (c : Fin p → ℂ) :
    markedChaosDegreeC N s B c
      =ᵐ[P] markedChaosDegreeC N s (fun j => R (e.symm j)) (fun j => (g (e.symm j)).elim 0 c) := by
  filter_upwards [ae_markedChaosDegreeC_eq_coeff_refine N hR hRd hRfin g hBR s c] with ω hω
  rw [hω, markedChaosDegreeC_eq_coeff]
  congr 2
  exact (Fintype.prod_equiv e.symm _ _ fun j => rfl).symm

/-! ### The common refinement of two families -/

section Refinement

variable {α : Type*}

open scoped Classical in
/-- The region of a family containing a point, if there is one. -/
noncomputable def regionIndex {p : ℕ} (B : Fin p → Set α) (x : α) : Option (Fin p) :=
  if h : ∃ k, x ∈ B k then some h.choose else none

/-- For a pairwise disjoint family, the region index of a point is `k` exactly when the point
lies in the region `B k`. -/
theorem regionIndex_eq_some_iff {p : ℕ} {B : Fin p → Set α}
    (hd : Pairwise fun k l => Disjoint (B k) (B l)) {x : α} {k : Fin p} :
    regionIndex B x = some k ↔ x ∈ B k := by
  classical
  unfold regionIndex
  constructor
  · intro h
    split_ifs at h with hx
    · rw [← Option.some_injective _ h]
      exact hx.choose_spec
  · intro hk
    have hx : ∃ k, x ∈ B k := ⟨k, hk⟩
    rw [dif_pos hx]
    by_contra hne
    exact Set.disjoint_left.1 (hd fun h => hne (congrArg some h)) hx.choose_spec hk

/-- The region index of a point is none exactly when the point lies in no region. -/
theorem regionIndex_eq_none_iff {p : ℕ} {B : Fin p → Set α} {x : α} :
    regionIndex B x = none ↔ ∀ k, x ∉ B k := by
  classical
  unfold regionIndex
  split_ifs with hx
  · simp only [false_iff, not_forall, not_not]
    exact hx
  · simp only [true_iff]
    exact fun k hk => hx ⟨k, hk⟩

/-- The common refinement of two finite families of regions: the points of the union of the two
families having a prescribed region of each family containing them, or none. -/
def commonRefinement {p q : ℕ} (B : Fin p → Set α) (B' : Fin q → Set α)
    (i : Option (Fin p) × Option (Fin q)) : Set α :=
  {x | regionIndex B x = i.1 ∧ regionIndex B' x = i.2} ∩ ((⋃ k, B k) ∪ ⋃ l, B' l)

variable {p q : ℕ} {B : Fin p → Set α} {B' : Fin q → Set α}

/-- The members of the common refinement are pairwise disjoint. -/
theorem pairwise_disjoint_commonRefinement :
    Pairwise fun i j => Disjoint (commonRefinement B B' i) (commonRefinement B B' j) := by
  intro i j hij
  refine Set.disjoint_left.2 fun x hi hj => hij ?_
  exact Prod.ext (hi.1.1.symm.trans hj.1.1) (hi.1.2.symm.trans hj.1.2)

/-- The members of the common refinement lie in the union of the two families. -/
theorem commonRefinement_subset (i : Option (Fin p) × Option (Fin q)) :
    commonRefinement B B' i ⊆ (⋃ k, B k) ∪ ⋃ l, B' l :=
  Set.inter_subset_right

/-- For pairwise disjoint families, the member of the common refinement indexed by `(k, l)` is
`B k ∩ B' l`. -/
theorem commonRefinement_some_some (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hd' : Pairwise fun k l => Disjoint (B' k) (B' l)) (k : Fin p) (l : Fin q) :
    commonRefinement B B' (some k, some l) = B k ∩ B' l := by
  ext x
  simp only [commonRefinement, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_union,
    Set.mem_iUnion, regionIndex_eq_some_iff hd, regionIndex_eq_some_iff hd']
  exact ⟨fun h => h.1, fun h => ⟨h, Or.inl ⟨k, h.1⟩⟩⟩

/-- For a pairwise disjoint family `B`, the region `B k` is the union of the members of the
common refinement whose first index is `k`. -/
theorem iUnion_commonRefinement_fst (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (k : Fin p) :
    B k = ⋃ i ∈ univ.filter (fun i : Option (Fin p) × Option (Fin q) => i.1 = some k),
      commonRefinement B B' i := by
  ext x
  simp only [Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop]
  constructor
  · intro hx
    refine ⟨(some k, regionIndex B' x), rfl, ⟨(regionIndex_eq_some_iff hd).2 hx, rfl⟩,
      Or.inl (Set.mem_iUnion.2 ⟨k, hx⟩)⟩
  · rintro ⟨i, hi, hx⟩
    rw [← regionIndex_eq_some_iff hd, ← hi]
    exact hx.1.1

/-- For a pairwise disjoint family `B'`, the region `B' l` is the union of the members of the
common refinement whose second index is `l`. -/
theorem iUnion_commonRefinement_snd (hd' : Pairwise fun k l => Disjoint (B' k) (B' l))
    (l : Fin q) :
    B' l = ⋃ i ∈ univ.filter (fun i : Option (Fin p) × Option (Fin q) => i.2 = some l),
      commonRefinement B B' i := by
  ext x
  simp only [Set.mem_iUnion, mem_filter, mem_univ, true_and, exists_prop]
  constructor
  · intro hx
    refine ⟨(regionIndex B x, some l), rfl, ⟨rfl, (regionIndex_eq_some_iff hd').2 hx⟩,
      Or.inr (Set.mem_iUnion.2 ⟨l, hx⟩)⟩
  · rintro ⟨i, hi, hx⟩
    rw [← regionIndex_eq_some_iff hd', ← hi]
    exact hx.1.2

/-- For a pairwise disjoint family of measurable regions, the set of points with a given region
index is measurable. -/
theorem measurableSet_regionIndex_eq [MeasurableSpace α]
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (o : Option (Fin p)) : MeasurableSet {x | regionIndex B x = o} := by
  cases o with
  | none =>
    have h : {x | regionIndex B x = none} = ⋂ k, (B k)ᶜ := by
      ext x
      simp only [Set.mem_setOf_eq, regionIndex_eq_none_iff, Set.mem_iInter, Set.mem_compl_iff]
    rw [h]
    exact MeasurableSet.iInter fun k => (hB k).compl
  | some k =>
    have h : {x | regionIndex B x = some k} = B k := by
      ext x
      exact regionIndex_eq_some_iff hd
    rw [h]
    exact hB k

/-- For pairwise disjoint families of measurable regions, the members of the common refinement
are measurable. -/
theorem measurableSet_commonRefinement [MeasurableSpace α]
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hB' : ∀ l, MeasurableSet (B' l)) (hd' : Pairwise fun k l => Disjoint (B' k) (B' l))
    (i : Option (Fin p) × Option (Fin q)) : MeasurableSet (commonRefinement B B' i) :=
  ((measurableSet_regionIndex_eq hB hd i.1).inter (measurableSet_regionIndex_eq hB' hd' i.2)).inter
    ((MeasurableSet.iUnion hB).union (MeasurableSet.iUnion hB'))

/-- For families of regions of finite measure, the members of the common refinement have finite
measure. -/
theorem measure_commonRefinement_ne_top [MeasurableSpace α] {μ : Measure α}
    (hfin : ∀ k, μ (B k) ≠ ⊤) (hfin' : ∀ l, μ (B' l) ≠ ⊤)
    (i : Option (Fin p) × Option (Fin q)) : μ (commonRefinement B B' i) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (measure_mono (commonRefinement_subset i))
  refine ne_top_of_le_ne_top ?_ (measure_union_le _ _)
  refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
  · exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun k _ => hfin k)
      (measure_iUnion_fintype_le μ B)
  · exact ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun l _ => hfin' l)
      (measure_iUnion_fintype_le μ B')

end Refinement

/-! ### The Gram across two families -/

/-- **The Gram across two families.** For two finite pairwise disjoint families of regions of
finite intensity, the bilinear moment of their degree elements is
`E[D_s(c; B) D_t(c'; B')] = δ_(s t) s! (∑_(k, l) c_k c'_l ν̂(B k ∩ B' l)) ^ s`. -/
theorem integral_markedChaosDegreeC_mul_cross (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p q : ℕ} {B : Fin p → Set (ℝ × E)} {B' : Fin q → Set (ℝ × E)}
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (hB' : ∀ l, MeasurableSet (B' l))
    (hd' : Pairwise fun k l => Disjoint (B' k) (B' l))
    (hfin' : ∀ l, referenceIntensity ν (B' l) ≠ ⊤) (s t : ℕ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s B c ω * markedChaosDegreeC N t B' c' ω ∂P
      = if s = t then (s.factorial : ℂ) * (∑ k, ∑ l, c k * c' l
          * ((referenceIntensity ν (B k ∩ B' l)).toReal : ℂ)) ^ s else 0 := by
  classical
  set ι := Option (Fin p) × Option (Fin q)
  set R : ι → Set (ℝ × E) := commonRefinement B B' with hRdef
  set e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hR : ∀ i, MeasurableSet (R i) := measurableSet_commonRefinement hB hd hB' hd'
  have hRd : Pairwise fun i j => Disjoint (R i) (R j) := pairwise_disjoint_commonRefinement
  have hRfin : ∀ i, referenceIntensity ν (R i) ≠ ⊤ := measure_commonRefinement_ne_top hfin hfin'
  have h1 := markedChaosDegreeC_ae_eq_of_refine N e hR hRd hRfin (fun i => i.1)
    (iUnion_commonRefinement_fst hd) s c
  have h2 := markedChaosDegreeC_ae_eq_of_refine N e hR hRd hRfin (fun i => i.2)
    (iUnion_commonRefinement_snd hd') t c'
  have hRj : ∀ j, MeasurableSet (R (e.symm j)) := fun j => hR _
  have hRdj : Pairwise fun j j' => Disjoint (R (e.symm j)) (R (e.symm j')) :=
    fun j j' hjj => hRd (e.symm.injective.ne hjj)
  have hRfinj : ∀ j, referenceIntensity ν (R (e.symm j)) ≠ ⊤ := fun j => hRfin _
  have h12 : (fun ω => markedChaosDegreeC N s B c ω * markedChaosDegreeC N t B' c' ω)
      =ᵐ[P] fun ω => markedChaosDegreeC N s (fun j => R (e.symm j))
          (fun j => (e.symm j).1.elim 0 c) ω
        * markedChaosDegreeC N t (fun j => R (e.symm j)) (fun j => (e.symm j).2.elim 0 c') ω := by
    filter_upwards [h1, h2] with ω h h'
    rw [h, h']
  rw [integral_congr_ae h12, integral_markedChaosDegreeC_mul N hRj hRdj hRfinj]
  split_ifs with hst
  · congr 2
    rw [Fintype.sum_equiv e.symm _ (fun i => (i.1.elim 0 c) * (i.2.elim 0 c')
      * ((referenceIntensity ν (R i)).toReal : ℂ)) fun j => rfl]
    rw [Fintype.sum_prod_type, Fintype.sum_option]
    simp only [Option.elim_none, zero_mul, Finset.sum_const_zero, zero_add, Option.elim_some]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Fintype.sum_option]
    simp only [Option.elim_none, mul_zero, zero_mul, zero_add, Option.elim_some]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hRdef, commonRefinement_some_some hd hd']
  · rfl

/-- **The Hermitian Gram across two families.** For two finite pairwise disjoint families of
regions of finite intensity,
`E[D_s(c; B) conj D_t(c'; B')] = δ_(s t) s! (∑_(k, l) c_k conj c'_l ν̂(B k ∩ B' l)) ^ s`. -/
theorem integral_markedChaosDegreeC_mul_conj_cross (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p q : ℕ} {B : Fin p → Set (ℝ × E)} {B' : Fin q → Set (ℝ × E)}
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (hB' : ∀ l, MeasurableSet (B' l))
    (hd' : Pairwise fun k l => Disjoint (B' k) (B' l))
    (hfin' : ∀ l, referenceIntensity ν (B' l) ≠ ⊤) (s t : ℕ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s B c ω * (starRingEnd ℂ) (markedChaosDegreeC N t B' c' ω) ∂P
      = if s = t then (s.factorial : ℂ) * (∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l)
          * ((referenceIntensity ν (B k ∩ B' l)).toReal : ℂ)) ^ s else 0 := by
  simp_rw [conj_markedChaosDegreeC]
  exact integral_markedChaosDegreeC_mul_cross N hB hd hfin hB' hd' hfin' s t c _

/-- **The Gram across two families of strips.** For finite pairwise disjoint families `A`, `A'`
of mark sets of finite intensity and the strips over `(a, b]`,
`E[D_s(c; A) D_t(c'; A')] = δ_(s t) s! ((b − a) ∑_(k, l) c_k c'_l ν(A k ∩ A' l)) ^ s`. -/
theorem integral_markedChaosDegreeC_strip_mul_cross (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l)) (s t : ℕ)
    (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * markedChaosDegreeC N t (fun l => Set.Ioc a b ×ˢ A' l) c' ω ∂P
      = if s = t then (s.factorial : ℂ) * ((((b - a : ℝ)) : ℂ) * ∑ k, ∑ l, c k * c' l
          * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s else 0 := by
  have hdB : Pairwise fun k l => Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) :=
    fun k l hkl => Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  have hdB' : Pairwise fun k l => Disjoint (Set.Ioc a b ×ˢ A' k) (Set.Ioc a b ×ˢ A' l) :=
    fun k l hkl => Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd' hkl) hx.2 hx'.2
  rw [integral_markedChaosDegreeC_mul_cross N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))
    (fun l => measurableSet_Ioc.prod (hA' l)) hdB'
    (fun l => referenceIntensity_strip_ne_top ha (hAν' l)) s t c c']
  split_ifs
  · congr 2
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Set.prod_inter_prod, Set.inter_self,
      referenceIntensity_strip_toReal ha hab]
    push_cast
    ring
  · rfl

/-- **The Hermitian Gram across two families of strips.** For finite pairwise disjoint families
`A`, `A'` of mark sets of finite intensity and the strips over `(a, b]`,
`E[D_s(c; A) conj D_t(c'; A')] = δ_(s t) s! ((b − a) ∑_(k, l) c_k conj c'_l ν(A k ∩ A' l)) ^ s`. -/
theorem integral_markedChaosDegreeC_strip_mul_conj_cross (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l)) (s t : ℕ)
    (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * (starRingEnd ℂ) (markedChaosDegreeC N t (fun l => Set.Ioc a b ×ˢ A' l) c' ω) ∂P
      = if s = t then (s.factorial : ℂ) * ((((b - a : ℝ)) : ℂ) * ∑ k, ∑ l, c k
          * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s else 0 := by
  simp_rw [conj_markedChaosDegreeC]
  exact integral_markedChaosDegreeC_strip_mul_cross N ha hab hA hAν hd hA' hAν' hd' s t c _

/-- **The Gram of two simple mark profiles on different families.** For simple mark profiles `G`,
`G'` and the strips of their mark sets over `(a, b]`,
`E[D_s(G) D_t(G')] = δ_(s t) s! ((b − a) ∫ G G' dν) ^ s`. -/
theorem integral_markedChaosDegree_simpleProfile_mul (N : PoissonRandomMeasure.{u, v, w} P ν)
    (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (s t : ℕ) :
    ∫ ω, markedChaosDegree N s (fun k => Set.Ioc a b ×ˢ G.B k) G.c ω
        * markedChaosDegree N t (fun l => Set.Ioc a b ×ˢ G'.B l) G'.c ω ∂P
      = if s = t then (s.factorial : ℝ) * ((b - a) * ∫ e, G.toFun e * G'.toFun e ∂ν) ^ s
        else 0 := by
  have h := integral_markedChaosDegreeC_strip_mul_conj_cross N ha hab G.B_measurable G.B_finite
    G.B_disjoint G'.B_measurable G'.B_finite G'.B_disjoint s t (fun k => (G.c k : ℂ))
    (fun l => (G'.c l : ℂ))
  simp_rw [markedChaosDegreeC_ofReal, Complex.conj_ofReal] at h
  refine Complex.ofReal_injective ?_
  rw [← integral_complex_ofReal]
  push_cast
  rw [h, SimpleProfile.integral_toFun_mul]
  split_ifs
  · push_cast
    rfl
  · push_cast
    rfl

/-! ### Complex profiles on mark sets -/

/-- The degree-zero element of a complex profile is `1`. -/
@[simp] theorem markedChaosDegreeC_zero (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) :
    markedChaosDegreeC N 0 B c ω = 1 := by
  rw [markedChaosDegreeC, Finset.piAntidiag_zero]
  simp [Nat.multinomial, poissonChaosProd]

/-- The degree-one element of a complex profile is `∑_k c_k Ñ(B k)`. -/
theorem markedChaosDegreeC_one (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) :
    markedChaosDegreeC N 1 B c ω = ∑ k, c k * (N.compensated (B k) ω : ℂ) := by
  classical
  rw [markedChaosDegreeC, piAntidiag_univ_one, Finset.sum_image ?_]
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

omit [SigmaFinite ν] in
/-- On one family of pairwise disjoint mark sets the double sum of a pairing of two profiles
reduces to its diagonal. -/
theorem sum_sum_mul_measure_inter_self {p : ℕ} {A : Fin p → Set E}
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (c c' : Fin p → ℂ) :
    ∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A l)).toReal : ℂ)
      = ∑ k, c k * c' k * ((ν (A k)).toReal : ℂ) := by
  classical
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hlk => by
      rw [Set.disjoint_iff_inter_eq_empty.1 (hd (Ne.symm hlk)), measure_empty,
        ENNReal.toReal_zero, Complex.ofReal_zero, mul_zero])
    (fun h => absurd (Finset.mem_univ k) h), Set.inter_self]

/-- The complex function `∑_k c_k 𝟙_(A k)` carried by a complex profile on a family of mark
sets. -/
noncomputable def markProfileC {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℂ) (e : E) : ℂ :=
  ∑ k, c k * (A k).indicator (fun _ => (1 : ℂ)) e

omit [SigmaFinite ν] in
/-- The Hermitian `L²(ν)` pairing of the functions of two complex profiles, through the
intensities of the intersections of their mark sets. -/
theorem integral_markProfileC_mul_conj {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤) (hA' : ∀ l, MeasurableSet (A' l))
    (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ e, markProfileC A c e * (starRingEnd ℂ) (markProfileC A' c' e) ∂ν
      = ∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ) := by
  classical
  have hmeas : ∀ k l, MeasurableSet (A k ∩ A' l) := fun k l => (hA k).inter (hA' l)
  have hfin : ∀ k l, ν (A k ∩ A' l) ≠ ⊤ :=
    fun k l => ne_top_of_le_ne_top (hAν k) (measure_mono Set.inter_subset_left)
  have hpt : ∀ e, markProfileC A c e * (starRingEnd ℂ) (markProfileC A' c' e)
      = ∑ k, ∑ l, (A k ∩ A' l).indicator (fun _ => c k * (starRingEnd ℂ) (c' l)) e := by
    intro e
    rw [markProfileC, markProfileC, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    by_cases hk : e ∈ A k <;> by_cases hl : e ∈ A' l <;>
      simp [Set.indicator, hk, hl]
  have hint : ∀ k l, Integrable
      (fun e => (A k ∩ A' l).indicator (fun _ => c k * (starRingEnd ℂ) (c' l)) e) ν :=
    fun k l => memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (hmeas k l) _ (Or.inr (hfin k l)))
  simp_rw [hpt]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_indicator_const _ (hmeas k l), measureReal_def, Complex.real_smul]
  ring

/-- **The Hermitian Gram across two families of strips, through the profiles.** For complex
profiles on finite pairwise disjoint families `A`, `A'` of mark sets of finite intensity, with
functions `f = ∑_k c_k 𝟙_(A k)` and `g = ∑_l c'_l 𝟙_(A' l)`,
`E[D_s(c; A) conj D_t(c'; A')] = δ_(s t) s! ((b − a) ∫ f conj g dν) ^ s`. -/
theorem integral_markedChaosDegreeC_strip_mul_conj_markProfileC
    (N : PoissonRandomMeasure.{u, v, w} P ν) {p q : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {A : Fin p → Set E} {A' : Fin q → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l))
    (hA' : ∀ l, MeasurableSet (A' l)) (hAν' : ∀ l, ν (A' l) ≠ ⊤)
    (hd' : Pairwise fun k l => Disjoint (A' k) (A' l)) (s t : ℕ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω
        * (starRingEnd ℂ) (markedChaosDegreeC N t (fun l => Set.Ioc a b ×ˢ A' l) c' ω) ∂P
      = if s = t then (s.factorial : ℂ) * ((((b - a : ℝ)) : ℂ)
          * ∫ e, markProfileC A c e * (starRingEnd ℂ) (markProfileC A' c' e) ∂ν) ^ s
        else 0 := by
  rw [integral_markedChaosDegreeC_strip_mul_conj_cross N ha hab hA hAν hd hA' hAν' hd',
    integral_markProfileC_mul_conj hA hAν hA']

end LevyStochCalc.Poisson
