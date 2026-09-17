/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.SimpleChaosDegree

/-!
# The degree-`s` chaos element of a complex profile

For a complex profile `c` constant on each region of a finite pairwise disjoint family of finite
intensity, the degree-`s` element `D_s(c)` is the same multinomial combination of the products of
Charlier polynomials of the counts as for a real profile, with complex coefficients; at a real
profile it is the real element, and conjugating the profile conjugates the element. The elements
are square integrable, and their bilinear non-conjugated moment is
`E[D_s(c) D_t(c')] = δ_(s t) s! (∑_k c_k c'_k λ_k) ^ s` for the rates `λ_k = ν̂(B k)`, whence the
second moment of the modulus `E‖D_s(c)‖ ^ 2 = s! (∑_k ‖c_k‖ ^ 2 λ_k) ^ s` and the non-conjugated
second moment `E[D_s(c) ^ 2] = s! (∑_k c_k ^ 2 λ_k) ^ s`; on strips `(a, b] ×ˢ A k` the rates are
`(b − a) ν(A k)`. The element carries no factor `1 / s!`.

## Main definitions

* `LevyStochCalc.Poisson.markedChaosDegreeC` — the degree-`s` element of a complex profile.

## Main statements

* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_mul` — the bilinear non-conjugated moment.
* `LevyStochCalc.Poisson.integral_norm_sq_markedChaosDegreeC`,
  `LevyStochCalc.Poisson.integral_markedChaosDegreeC_sq` — the two second moments.
* `LevyStochCalc.Poisson.integral_markedChaosDegreeC_strip_sq`,
  `LevyStochCalc.Poisson.integral_norm_sq_markedChaosDegreeC_strip` — the same on strips.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Complex profiles -/

/-- The degree-`s` chaos element of a finite family of regions carried by a complex profile
constant on each region. -/
noncomputable def markedChaosDegreeC (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) : ℂ :=
  ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
    (Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k)
      * (poissonChaosProd N α B ω : ℂ)

/-- At a real profile the complex element is the real one. -/
lemma markedChaosDegreeC_ofReal (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℝ) (ω : Ω) :
    markedChaosDegreeC N s B (fun k => (c k : ℂ)) ω = (markedChaosDegree N s B c ω : ℂ) := by
  rw [markedChaosDegreeC, markedChaosDegree, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  push_cast
  ring

/-- Conjugating the profile conjugates the element. -/
lemma conj_markedChaosDegreeC (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    (B : Fin p → Set (ℝ × E)) (c : Fin p → ℂ) (ω : Ω) :
    (starRingEnd ℂ) (markedChaosDegreeC N s B c ω)
      = markedChaosDegreeC N s B (fun k => (starRingEnd ℂ) (c k)) ω := by
  rw [markedChaosDegreeC, markedChaosDegreeC, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_mul, map_prod]
  simp [map_pow]

/-- The complex degree elements of a family of measurable regions are measurable. -/
theorem measurable_markedChaosDegreeC (N : PoissonRandomMeasure P ν) {p : ℕ} (s : ℕ)
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℂ) :
    Measurable (markedChaosDegreeC N s B c) :=
  Finset.measurable_sum _ fun α _ =>
    (Complex.measurable_ofReal.comp (measurable_poissonChaosProd N α hB)).const_mul _

/-- The complex degree elements of a finite pairwise disjoint family of regions of finite
intensity are square integrable. -/
theorem memLp_two_markedChaosDegreeC (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℂ) :
    MemLp (markedChaosDegreeC N s B c) 2 P := by
  unfold markedChaosDegreeC
  exact memLp_finsetSum _ fun α _ =>
    ((memLp_two_poissonChaosProd N hB hd hfin α).ofReal).const_mul _

/-- The product of two complex degree elements, expanded over the multi-degrees. -/
lemma markedChaosDegreeC_mul_eq_sum (N : PoissonRandomMeasure P ν) {p : ℕ} (s t : ℕ)
    (B : Fin p → Set (ℝ × E)) (c c' : Fin p → ℂ) (ω : Ω) :
    markedChaosDegreeC N s B c ω * markedChaosDegreeC N t B c' ω
      = ∑ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
          ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * ((poissonChaosProd N α B ω * poissonChaosProd N β B ω : ℝ) : ℂ) := by
  rw [markedChaosDegreeC, markedChaosDegreeC, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
  push_cast
  ring

/-- The bilinear, non-conjugated moment of two complex degree elements of a finite pairwise
disjoint family of regions of finite intensity:
`E[D_s(c) D_t(c')] = δ_(s t) s ! (∑_k c_k c'_k λ_k) ^ s` for the rates `λ_k = ν̂(B k)`. -/
theorem integral_markedChaosDegreeC_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s t : ℕ) (c c' : Fin p → ℂ) :
    ∫ ω, markedChaosDegreeC N s B c ω * markedChaosDegreeC N t B c' ω ∂P
      = if s = t then (s.factorial : ℂ)
          * (∑ k, c k * c' k * ((referenceIntensity ν (B k)).toReal : ℂ)) ^ s else 0 := by
  classical
  rw [funext fun ω => markedChaosDegreeC_mul_eq_sum N s t B c c' ω]
  rw [integral_finsetSum _ fun α _ => integrable_finsetSum _ fun β _ =>
    ((integrable_poissonChaosProd_mul N hB hd hfin α β).ofReal).const_mul _]
  have hinner : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
      ∫ ω, ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
          ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
            * ((poissonChaosProd N α B ω * poissonChaosProd N β B ω : ℝ) : ℂ) ∂P
        = ∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) t,
            ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℂ)
                  * ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k else 0) := by
    intro α _
    rw [integral_finsetSum _ fun β _ =>
      ((integrable_poissonChaosProd_mul N hB hd hfin α β).ofReal).const_mul _]
    refine Finset.sum_congr rfl fun β _ => ?_
    rw [integral_const_mul, integral_complex_ofReal,
      integral_poissonChaosProd_mul N hB hd hfin α β]
    by_cases hab : α = β
    · rw [if_pos hab, if_pos hab, Complex.ofReal_prod]
      congr 1
      exact Finset.prod_congr rfl fun k _ => by push_cast; ring
    · rw [if_neg hab, if_neg hab, Complex.ofReal_zero]
  rw [Finset.sum_congr rfl hinner]
  by_cases hst : s = t
  · subst hst
    rw [if_pos rfl]
    have hdiag : ∀ α ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
        (∑ β ∈ Finset.piAntidiag (Finset.univ : Finset (Fin p)) s,
            ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * (if α = β then ∏ k, ((α k).factorial : ℂ)
                  * ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k else 0))
          = (Nat.multinomial Finset.univ α : ℂ) * (Nat.multinomial Finset.univ α : ℂ)
              * (∏ k, ((α k).factorial : ℂ))
              * ∏ k, (c k * c' k * ((referenceIntensity ν (B k)).toReal : ℂ)) ^ α k := by
      intro α hα
      have hstep : ∀ β, ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
            * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
            * (if α = β then ∏ k, ((α k).factorial : ℂ)
                * ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k else 0)
          = if α = β then ((Nat.multinomial Finset.univ α : ℂ) * (∏ k, c k ^ α k))
              * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
              * (∏ k, ((α k).factorial : ℂ)
                  * ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k) else 0 := by
        intro β; rw [mul_ite, mul_zero]
      simp_rw [hstep]
      rw [Finset.sum_ite_eq _ α (fun β => ((Nat.multinomial Finset.univ α : ℂ)
        * (∏ k, c k ^ α k)) * ((Nat.multinomial Finset.univ β : ℂ) * (∏ k, c' k ^ β k))
        * (∏ k, ((α k).factorial : ℂ) * ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k)),
        if_pos hα]
      have e1 : ∏ k, ((α k).factorial : ℂ)
            * ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k
          = (∏ k, ((α k).factorial : ℂ))
            * ∏ k, ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k := Finset.prod_mul_distrib
      have e2 : ∏ k, (c k * c' k * ((referenceIntensity ν (B k)).toReal : ℂ)) ^ α k
          = (∏ k, c k ^ α k) * (∏ k, c' k ^ α k)
            * ∏ k, ((referenceIntensity ν (B k)).toReal : ℂ) ^ α k := by
        simp_rw [mul_pow]
        rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
      rw [e1, e2]
      ring
    rw [Finset.sum_congr rfl hdiag, sum_piAntidiag_multinomial_sq s
      (fun k => c k * c' k * ((referenceIntensity ν (B k)).toReal : ℂ))]
  · rw [if_neg hst]
    refine Finset.sum_eq_zero fun α hα => Finset.sum_eq_zero fun β hβ => ?_
    have hne : α ≠ β := by
      rintro rfl
      exact hst (((Finset.mem_piAntidiag.1 hα).1).symm.trans (Finset.mem_piAntidiag.1 hβ).1)
    rw [if_neg hne, mul_zero]

/-- The second moment of the modulus of a complex degree element of a finite pairwise disjoint
family of regions of finite intensity: `E‖D_s(c)‖ ^ 2 = s ! (∑_k ‖c_k‖ ^ 2 λ_k) ^ s`. -/
theorem integral_norm_sq_markedChaosDegreeC (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℂ) :
    ∫ ω, ‖markedChaosDegreeC N s B c ω‖ ^ 2 ∂P
      = (s.factorial : ℝ)
        * (∑ k, ‖c k‖ ^ 2 * (referenceIntensity ν (B k)).toReal) ^ s := by
  have hpt : ∀ ω : Ω, ((‖markedChaosDegreeC N s B c ω‖ ^ 2 : ℝ) : ℂ)
      = markedChaosDegreeC N s B c ω
        * markedChaosDegreeC N s B (fun k => (starRingEnd ℂ) (c k)) ω := by
    intro ω
    rw [← conj_markedChaosDegreeC, Complex.mul_conj']
    push_cast
    ring
  have hkey : ((∫ ω, ‖markedChaosDegreeC N s B c ω‖ ^ 2 ∂P : ℝ) : ℂ)
      = (((s.factorial : ℝ)
          * (∑ k, ‖c k‖ ^ 2 * (referenceIntensity ν (B k)).toReal) ^ s : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    simp_rw [hpt]
    rw [integral_markedChaosDegreeC_mul N hB hd hfin s s c (fun k => (starRingEnd ℂ) (c k)),
      if_pos rfl]
    push_cast
    congr 1
    refine congrArg (· ^ s) (Finset.sum_congr rfl fun k _ => ?_)
    rw [mul_comm (c k) _, ← Complex.normSq_eq_conj_mul_self]
    push_cast [Complex.normSq_eq_norm_sq]
    ring
  exact Complex.ofReal_inj.1 hkey

/-- The non-conjugated second moment of a complex degree element of a finite pairwise disjoint
family of regions of finite intensity: `E[D_s(c) ^ 2] = s ! (∑_k c_k ^ 2 λ_k) ^ s`. -/
theorem integral_markedChaosDegreeC_sq (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (s : ℕ) (c : Fin p → ℂ) :
    ∫ ω, markedChaosDegreeC N s B c ω ^ 2 ∂P
      = (s.factorial : ℂ)
        * (∑ k, c k ^ 2 * ((referenceIntensity ν (B k)).toReal : ℂ)) ^ s := by
  have h := integral_markedChaosDegreeC_mul N hB hd hfin s s c c
  rw [if_pos rfl] at h
  rw [show (fun ω => markedChaosDegreeC N s B c ω ^ 2)
      = fun ω => markedChaosDegreeC N s B c ω * markedChaosDegreeC N s B c ω from
    funext fun ω => sq _, h]
  refine congrArg _ (congrArg (· ^ s) (Finset.sum_congr rfl fun k _ => ?_))
  rw [sq]

/-- The non-conjugated second moment of a complex degree element carried by strips
`(a, b] ×ˢ A k` over a finite pairwise disjoint family of mark sets of finite intensity. -/
theorem integral_markedChaosDegreeC_strip_sq (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (s : ℕ)
    (c : Fin p → ℂ) :
    ∫ ω, markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω ^ 2 ∂P
      = (s.factorial : ℂ)
        * (∑ k, c k ^ 2 * (((b - a) * (ν (A k)).toReal : ℝ) : ℂ)) ^ s := by
  have hdB : Pairwise fun k l =>
      Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  rw [integral_markedChaosDegreeC_sq N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))]
  simp_rw [referenceIntensity_strip_toReal ha hab]

/-- The second moment of the modulus of a complex degree element carried by strips
`(a, b] ×ˢ A k` over a finite pairwise disjoint family of mark sets of finite intensity. -/
theorem integral_norm_sq_markedChaosDegreeC_strip (N : PoissonRandomMeasure.{u, v, w} P ν)
    {p : ℕ} {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (s : ℕ) (c : Fin p → ℂ) :
    ∫ ω, ‖markedChaosDegreeC N s (fun k => Set.Ioc a b ×ˢ A k) c ω‖ ^ 2 ∂P
      = (s.factorial : ℝ) * (∑ k, ‖c k‖ ^ 2 * ((b - a) * (ν (A k)).toReal)) ^ s := by
  have hdB : Pairwise fun k l =>
      Disjoint (Set.Ioc a b ×ˢ A k) (Set.Ioc a b ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  rw [integral_norm_sq_markedChaosDegreeC N (fun k => measurableSet_Ioc.prod (hA k)) hdB
    (fun k => referenceIntensity_strip_ne_top ha (hAν k))]
  simp_rw [referenceIntensity_strip_toReal ha hab]

end LevyStochCalc.Poisson
