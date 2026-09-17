/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.ChaosStep
import Mathlib.Probability.Independence.Integration

/-!
# Chaos elements of a finite disjoint family of regions

For a Poisson random measure `N` and a finite family `B : Fin p → Set (ℝ × E)` of regions,
`poissonChaosProd N α B` is the product over the family of the Charlier elements
`poissonChaosStep N (α k) (B k)`, one factor per index, of the degree prescribed by the
multi-degree `α : Fin p → ℕ`. When the regions are pairwise disjoint their counts are jointly
independent, so the one-region orthogonality of `Poisson/ChaosStep.lean` multiplies out: the
elements of distinct multi-degrees are orthogonal under `P`, the element of multi-degree `α` has
second moment given by the norming `∏_k α_k ! λ_k ^ α_k` with `λ_k = ν̂(B k)`, the elements of
nonzero multi-degree are centred, and every element whose multi-degree is not `Pi.single m 1` is
orthogonal to the compensated count `Ñ(B m)` of the family.

Pairwise disjointness of the family is a hypothesis throughout, and it is what the independence
of the counts rests on; overlapping regions are not covered. Each factor is a polynomial in the
one count `N(B k)`, so the elements here are polynomials in the `p` counts of the family.

## Main statements

* `LevyStochCalc.Poisson.iIndepFun_count_fin` — the counts of a finite pairwise disjoint family
  of measurable regions are jointly independent.
* `LevyStochCalc.Poisson.poissonChaosProd_single_one` — the element of multi-degree
  `Pi.single m 1` is the compensated count `Ñ(B m)`.
* `LevyStochCalc.Poisson.integrable_poissonChaosProd_mul`,
  `LevyStochCalc.Poisson.integrable_poissonChaosProd` — an element of a pairwise disjoint family
  of regions of finite intensity, and a product of two of them, are integrable.
* `LevyStochCalc.Poisson.memLp_two_poissonChaosProd` — such an element lies in `L²`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_mul` —
  `E[C_α C_β] = δ_(α β) ∏_k α_k ! λ_k ^ α_k`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_eq_zero` — `E[C_α] = 0` for `α ≠ 0`.
* `LevyStochCalc.Poisson.integral_poissonChaosProd_mul_compensated_eq_zero` —
  `E[C_α Ñ(B m)] = 0` for `α ≠ Pi.single m 1`.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace LevyStochCalc.Poisson

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Joint independence of the counts of a finite disjoint family -/

/-- The counts of a finite family of pairwise disjoint measurable regions are jointly
independent under `P`. -/
theorem iIndepFun_count_fin (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l)) :
    iIndepFun (fun (k : Fin p) (ω : Ω) => N.N ω (B k)) P := by
  have h := N.independent_disjoint (fun o : ULift.{w} (Fin p) => B o.down)
    (fun o => hB o.down) fun o o' hoo' => hd fun h' => hoo' (by rw [ULift.ext_iff]; exact h')
  exact h.precomp (g := ULift.up.{w}) fun x y hxy => by simpa [ULift.ext_iff] using hxy

private lemma enorm_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ‖∏ i ∈ s, f i‖ₑ = ∏ i ∈ s, ‖f i‖ₑ := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons j s hj ih => rw [Finset.prod_cons, Finset.prod_cons, enorm_mul, ih]

/-! ### The chaos element of a multi-degree -/

/-- The chaos element of multi-degree `α` of a finite family of regions: the product over the
family of the Charlier elements of the matching degrees. -/
noncomputable def poissonChaosProd (N : PoissonRandomMeasure P ν) {p : ℕ} (α : Fin p → ℕ)
    (B : Fin p → Set (ℝ × E)) (ω : Ω) : ℝ :=
  ∏ k, poissonChaosStep N (α k) (B k) ω

/-- The chaos element of multi-degree `0` is `1`. -/
@[simp] lemma poissonChaosProd_zero (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (ω : Ω) : poissonChaosProd N (fun _ => 0) B ω = 1 := by
  simp [poissonChaosProd]

/-- The chaos element of multi-degree `Pi.single m 1` is the compensated count `Ñ(B m)`. -/
lemma poissonChaosProd_single_one (N : PoissonRandomMeasure P ν) {p : ℕ}
    (B : Fin p → Set (ℝ × E)) (m : Fin p) (ω : Ω) :
    poissonChaosProd N (Pi.single m 1) B ω = N.compensated (B m) ω := by
  rw [poissonChaosProd, Finset.prod_eq_single m]
  · rw [Pi.single_eq_same, poissonChaosStep_one]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj, poissonChaosStep_zero]
  · intro hm
    exact absurd (Finset.mem_univ m) hm

/-- A chaos element of a family of measurable regions is measurable. -/
theorem measurable_poissonChaosProd (N : PoissonRandomMeasure P ν) {p : ℕ} (α : Fin p → ℕ)
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) :
    Measurable (poissonChaosProd N α B) :=
  Finset.univ.measurable_prod fun k _ => measurable_poissonChaosStep N (α k) (hB k)

/-! ### Integrability -/

/-- A product of two chaos elements of a finite pairwise disjoint family of regions of finite
intensity is integrable. -/
theorem integrable_poissonChaosProd_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α β : Fin p → ℕ) :
    Integrable (fun ω => poissonChaosProd N α B ω * poissonChaosProd N β B ω) P := by
  classical
  set g : Fin p → Ω → ℝ := fun k ω =>
    poissonChaosStep N (α k) (B k) ω * poissonChaosStep N (β k) (B k) ω with hg
  have hgint : ∀ k, Integrable (g k) P :=
    fun k => integrable_poissonChaosStep_mul N (hB k) (hfin k) (α k) (β k)
  have hgmeas : ∀ k, Measurable (g k) := fun k =>
    (measurable_poissonChaosStep N (α k) (hB k)).mul (measurable_poissonChaosStep N (β k) (hB k))
  have hrw : (fun ω => poissonChaosProd N α B ω * poissonChaosProd N β B ω)
      = fun ω => ∏ k, g k ω :=
    funext fun ω => by rw [poissonChaosProd, poissonChaosProd, ← Finset.prod_mul_distrib]
  rw [hrw]
  refine ⟨(Finset.univ.measurable_prod fun k _ => hgmeas k).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have hind : iIndepFun (fun (k : Fin p) ω => ‖g k ω‖ₑ) P :=
    (iIndepFun_count_fin N B hB hd).comp (fun k (x : ℝ≥0∞) =>
      ‖Probability.charlierScaled (α k) (referenceIntensity ν (B k)).toReal x.toReal
        * Probability.charlierScaled (β k) (referenceIntensity ν (B k)).toReal x.toReal‖ₑ)
      (fun k => (((((Probability.continuous_charlierScaled (α k) _).measurable).comp
        ENNReal.measurable_toReal).mul
          (((Probability.continuous_charlierScaled (β k) _).measurable).comp
            ENNReal.measurable_toReal)).enorm))
  calc ∫⁻ ω, ‖∏ k, g k ω‖ₑ ∂P = ∫⁻ ω, ∏ k, ‖g k ω‖ₑ ∂P := by simp_rw [enorm_finset_prod]
    _ = ∏ k, ∫⁻ ω, ‖g k ω‖ₑ ∂P :=
        lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ _ hind fun k => (hgmeas k).enorm
    _ < ⊤ := ENNReal.prod_lt_top fun k _ =>
        hasFiniteIntegral_iff_enorm.1 (hgint k).hasFiniteIntegral

/-- A chaos element of a finite pairwise disjoint family of regions of finite intensity is
integrable. -/
theorem integrable_poissonChaosProd (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α : Fin p → ℕ) :
    Integrable (poissonChaosProd N α B) P := by
  simpa using integrable_poissonChaosProd_mul N hB hd hfin α (fun _ => 0)

/-- A chaos element of a finite pairwise disjoint family of regions of finite intensity lies in
`L²`. -/
theorem memLp_two_poissonChaosProd (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α : Fin p → ℕ) :
    MemLp (poissonChaosProd N α B) 2 P := by
  refine (memLp_two_iff_integrable_sq
    (measurable_poissonChaosProd N α hB).aestronglyMeasurable).2 ?_
  simpa only [pow_two] using integrable_poissonChaosProd_mul N hB hd hfin α α

/-! ### Orthogonality across multi-degrees -/

/-- The chaos elements of a finite pairwise disjoint family are orthogonal across multi-degrees,
with `E[C_α C_β] = δ_(α β) ∏_k α_k ! λ_k ^ α_k` for the rates `λ_k = ν̂(B k)`. -/
theorem integral_poissonChaosProd_mul (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) (α β : Fin p → ℕ) :
    ∫ ω, poissonChaosProd N α B ω * poissonChaosProd N β B ω ∂P
      = if α = β then ∏ k, ((α k).factorial : ℝ) * (referenceIntensity ν (B k)).toReal ^ α k
        else 0 := by
  classical
  have hX : iIndepFun (fun (k : Fin p) (ω : Ω) => N.N ω (B k)) P :=
    iIndepFun_count_fin N B hB hd
  have hmX : ∀ k, AEMeasurable (fun ω => N.N ω (B k)) P :=
    fun k => (N.measurable_eval (hB k)).aemeasurable
  set f : Fin p → ℝ≥0∞ → ℝ := fun k x =>
    Probability.charlierScaled (α k) (referenceIntensity ν (B k)).toReal x.toReal
      * Probability.charlierScaled (β k) (referenceIntensity ν (B k)).toReal x.toReal with hf
  have hfmeas : ∀ k, Measurable (f k) := fun k =>
    (((Probability.continuous_charlierScaled (α k) _).measurable).comp
        ENNReal.measurable_toReal).mul
      (((Probability.continuous_charlierScaled (β k) _).measurable).comp
        ENNReal.measurable_toReal)
  have key := hX.integral_fun_prod_comp hmX fun k => (hfmeas k).aestronglyMeasurable
  have hstep : ∫ ω, poissonChaosProd N α B ω * poissonChaosProd N β B ω ∂P
      = ∏ k, (if α k = β k then ((α k).factorial : ℝ)
          * (referenceIntensity ν (B k)).toReal ^ α k else 0) := by
    rw [show (fun ω => poissonChaosProd N α B ω * poissonChaosProd N β B ω)
        = fun ω => ∏ k, f k (N.N ω (B k)) from
      funext fun ω => by
        rw [poissonChaosProd, poissonChaosProd, ← Finset.prod_mul_distrib]; rfl]
    rw [key]
    exact Finset.prod_congr rfl fun k _ => by
      simpa [hf, poissonChaosStep] using integral_poissonChaosStep_mul N (hB k) (hfin k)
        (α k) (β k)
  rw [hstep]
  by_cases hab : α = β
  · subst hab
    simp
  · rw [if_neg hab]
    obtain ⟨k, hk⟩ : ∃ k, α k ≠ β k := by
      by_contra hcon
      exact hab (funext fun k => not_not.1 fun h => hcon ⟨k, h⟩)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

/-- The chaos elements of nonzero multi-degree of a finite pairwise disjoint family are centred
under `P`. -/
theorem integral_poissonChaosProd_eq_zero (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ}
    {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) {α : Fin p → ℕ} (hα : α ≠ fun _ => 0) :
    ∫ ω, poissonChaosProd N α B ω ∂P = 0 := by
  have h := integral_poissonChaosProd_mul N hB hd hfin α (fun _ => 0)
  simp only [poissonChaosProd_zero, mul_one, if_neg hα] at h
  exact h

/-- A chaos element of a finite pairwise disjoint family whose multi-degree is not
`Pi.single m 1` is orthogonal to the compensated count `Ñ(B m)` of the family. -/
theorem integral_poissonChaosProd_mul_compensated_eq_zero
    (N : PoissonRandomMeasure.{u, v, w} P ν) {p : ℕ} {B : Fin p → Set (ℝ × E)}
    (hB : ∀ k, MeasurableSet (B k)) (hd : Pairwise fun k l => Disjoint (B k) (B l))
    (hfin : ∀ k, referenceIntensity ν (B k) ≠ ⊤) {α : Fin p → ℕ} {m : Fin p}
    (hα : α ≠ Pi.single m 1) :
    ∫ ω, poissonChaosProd N α B ω * N.compensated (B m) ω ∂P = 0 := by
  rw [show (fun ω => poissonChaosProd N α B ω * N.compensated (B m) ω)
      = fun ω => poissonChaosProd N α B ω * poissonChaosProd N (Pi.single m 1) B ω from
    funext fun ω => by rw [poissonChaosProd_single_one]]
  rw [integral_poissonChaosProd_mul N hB hd hfin, if_neg hα]

end LevyStochCalc.Poisson
