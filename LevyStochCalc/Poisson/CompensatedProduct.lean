/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedProfileMoments
import LevyStochCalc.Poisson.SecondChaos

/-!
# The compensated product of two mark profiles over a step

For a mark profile `f : E → ℝ` write `J(f)` for its compensated integral over the step `(a, b]`
against a Poisson random measure `N` with intensity `ν` (`compensatedProfile`). The compensated
product of two mark profiles `f, g` over the step is

  `Q(f, g) = J(f) J(g) − J(f g) − (b − a) ∫ f g dν`.

For bounded square-integrable profiles the product `f g` is again bounded and square integrable,
so each term is a compensated integral of a square-integrable profile.

This file treats simple profiles. The functions of finitely many simple mark profiles are carried
by the mark sets of one simple profile, however the mark sets of different profiles overlap. On
such a common family `A_k`, with coefficient vectors `c, c'`, the compensated product is almost
surely the quadratic element

  `(∑ c_k Ñ(B_k)) (∑ c'_k Ñ(B_k)) − ∑ c_k c'_k N(B_k)`

of the strips `B_k = (a, b] ×ˢ A_k` (`markedSecondChaos`), whose mean, Gram and orthogonality to
the compensated counts come from `Poisson/SecondChaos.lean` and `Poisson/SimpleChaos.lean`. So at
simple profiles `Q` is square integrable and centred, it is orthogonal in `L²(P)` to the
compensated integral of every simple profile, and, with `⟨u, v⟩ = ∫ u v dν`,

  `E[Q(u₁, u₂) Q(u₃, u₄)] = (b − a)² (⟨u₁, u₃⟩ ⟨u₂, u₄⟩ + ⟨u₁, u₄⟩ ⟨u₂, u₃⟩)`.

The profiles need not have disjoint supports, so their compensated integrals need not be
independent. `Poisson/CompensatedProductMoments.lean` extends the identities to bounded
square-integrable profiles.

## Main definitions

* `LevyStochCalc.Poisson.compensatedProduct` — the compensated product of two mark profiles over
  a step.
* `LevyStochCalc.Poisson.SimpleProfile.withCoeff` — the simple profile on the mark sets of a given
  one carrying new coefficients.

## Main statements

* `LevyStochCalc.Poisson.SimpleProfile.exists_refinement` — a common refinement of finitely many
  simple mark profiles.
* `LevyStochCalc.Poisson.SimpleProfile.compensatedProduct_withCoeff_ae_eq` — on a common family
  the compensated product is the quadratic element of the strips.
* `LevyStochCalc.Poisson.SimpleProfile.memLp_compensatedProduct`,
  `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct` — square integrability and the
  mean at simple profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul` — the Gram at simple
  profiles.
* `LevyStochCalc.Poisson.SimpleProfile.integral_compensatedProduct_mul_compensatedProfile` —
  orthogonality to the first chaos at simple profiles.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The compensated product of two mark profiles over the step `(a, b]`,
`J(f) J(g) − J(f g) − (b − a) ∫ f g dν` with `J` the compensated integral over the step. It is
meant for bounded square-integrable profiles, whose product is again bounded and square
integrable. -/
noncomputable def compensatedProduct (N : PoissonRandomMeasure P ν) (f g : E → ℝ) (a b : ℝ)
    (ω : Ω) : ℝ :=
  compensatedProfile N f a b ω * compensatedProfile N g a b ω
    - compensatedProfile N (fun e => f e * g e) a b ω - (b - a) * ∫ e, f e * g e ∂ν

namespace SimpleProfile

/-- The simple mark profile on the mark sets of `H` carrying the coefficients `c`. -/
def withCoeff (H : SimpleProfile E ν) (c : Fin H.K → ℝ) : SimpleProfile E ν where
  K := H.K
  B := H.B
  B_measurable := H.B_measurable
  B_disjoint := H.B_disjoint
  B_finite := H.B_finite
  c := c

omit [SigmaFinite ν] in
/-- **Common refinement.** The functions of finitely many simple mark profiles are carried, with
suitable coefficients, by the mark sets of one simple mark profile. -/
theorem exists_refinement {ι : Type*} [Finite ι] (G : ι → SimpleProfile E ν) :
    ∃ (H : SimpleProfile E ν) (d : ι → Fin H.K → ℝ),
      ∀ i e, (H.withCoeff (d i)).toFun e = (G i).toFun e := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let U : Set E := ⋃ i, ⋃ k, (G i).B k
  let pat : E → ((i : ι) → Fin (G i).K → Bool) := fun e i k => decide (e ∈ (G i).B k)
  let A : ((i : ι) → Fin (G i).K → Bool) → Set E := fun σ => pat ⁻¹' {σ} ∩ U
  have hUm : MeasurableSet U :=
    MeasurableSet.iUnion fun i => MeasurableSet.iUnion fun k => (G i).B_measurable k
  have hAm : ∀ σ, MeasurableSet (A σ) := by
    intro σ
    refine MeasurableSet.inter ?_ hUm
    have hpre : pat ⁻¹' {σ} = ⋂ i, ⋂ k, {e | decide (e ∈ (G i).B k) = σ i k} := by
      ext e
      simp [pat, funext_iff]
    rw [hpre]
    refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun k => ?_
    cases σ i k
    · have hset : {e | decide (e ∈ (G i).B k) = false} = ((G i).B k)ᶜ := by
        ext e
        simp
      rw [hset]
      exact ((G i).B_measurable k).compl
    · have hset : {e | decide (e ∈ (G i).B k) = true} = (G i).B k := by
        ext e
        simp
      rw [hset]
      exact (G i).B_measurable k
  have hAfin : ∀ σ, ν (A σ) ≠ ⊤ := by
    intro σ
    by_cases h : ∃ i k, σ i k = true
    · obtain ⟨i, k, hik⟩ := h
      refine ne_top_of_le_ne_top ((G i).B_finite k) (measure_mono fun e he => ?_)
      have h1 : pat e i k = σ i k := by rw [he.1]
      simpa [pat, hik] using h1
    · simp only [not_exists] at h
      have hA0 : A σ = ∅ := by
        refine Set.eq_empty_of_forall_notMem fun e he => ?_
        obtain ⟨i, hi⟩ := Set.mem_iUnion.1 he.2
        obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hi
        have h1 : pat e i k = σ i k := by rw [he.1]
        simp [pat, hk, h i k] at h1
      rw [hA0, measure_empty]
      exact ENNReal.zero_ne_top
  have hAd : Pairwise fun σ τ => Disjoint (A σ) (A τ) := fun σ τ hστ =>
    Set.disjoint_left.2 fun e he he' => hστ ((he.1 : pat e = σ).symm.trans he'.1)
  let eqv := Fintype.equivFin ((i : ι) → Fin (G i).K → Bool)
  let H : SimpleProfile E ν :=
    { K := Fintype.card ((i : ι) → Fin (G i).K → Bool)
      B := fun j => A (eqv.symm j)
      B_measurable := fun j => hAm _
      B_disjoint := fun j j' hjj' => hAd (eqv.symm.injective.ne hjj')
      B_finite := fun j => hAfin _
      c := fun _ => 0 }
  let F : ι → ((i : ι) → Fin (G i).K → Bool) → ℝ :=
    fun i σ => ∑ k, (G i).c k * (if σ i k then 1 else 0)
  refine ⟨H, fun i j => F i (eqv.symm j), fun i e => ?_⟩
  by_cases he : e ∈ U
  · have hmem : e ∈ (H.withCoeff fun j => F i (eqv.symm j)).B (eqv (pat e)) := by
      change e ∈ A (eqv.symm (eqv (pat e)))
      rw [Equiv.symm_apply_apply]
      exact ⟨rfl, he⟩
    rw [toFun_of_mem _ hmem]
    change F i (eqv.symm (eqv (pat e))) = _
    rw [Equiv.symm_apply_apply, toFun]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : e ∈ (G i).B k <;> simp [pat, hk]
  · have h1 : ∀ j, e ∉ (H.withCoeff fun j => F i (eqv.symm j)).B j :=
      fun j hj => he hj.2
    rw [toFun_of_notMem _ h1, toFun_of_notMem]
    intro k hk
    exact he (Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨k, hk⟩⟩)

omit [SigmaFinite ν] in
/-- On the mark sets of one simple profile, the product of the functions carried by two
coefficient vectors is the function carried by their product. -/
theorem toFun_withCoeff_mul (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) (e : E) :
    (H.withCoeff c).toFun e * (H.withCoeff c').toFun e = (H.withCoeff (c * c')).toFun e := by
  by_cases h : ∃ k, e ∈ H.B k
  · obtain ⟨k, hk⟩ := h
    rw [toFun_of_mem (H.withCoeff c) (k := k) hk, toFun_of_mem (H.withCoeff c') (k := k) hk,
      toFun_of_mem (H.withCoeff (c * c')) (k := k) hk]
    rfl
  · simp only [not_exists] at h
    rw [toFun_of_notMem (H.withCoeff c) h, toFun_of_notMem (H.withCoeff (c * c')) h, zero_mul]

omit [SigmaFinite ν] in
/-- The integral of the function of a simple profile. -/
theorem integral_toFun (G : SimpleProfile E ν) :
    ∫ e, G.toFun e ∂ν = ∑ k, G.c k * (ν (G.B k)).toReal := by
  have hint : ∀ k : Fin G.K,
      Integrable (fun e => G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) e) ν := fun k =>
    (memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (G.B_measurable k) (1 : ℝ) (Or.inr (G.B_finite k)))).const_mul _
  simp only [toFun]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, integral_indicator_const (1 : ℝ) (G.B_measurable k), smul_eq_mul,
    mul_one, measureReal_def]

omit [SigmaFinite ν] in
/-- The integral of the function carried by a coefficient vector on the mark sets of a simple
profile. -/
theorem integral_toFun_withCoeff (H : SimpleProfile E ν) (c : Fin H.K → ℝ) :
    ∫ e, (H.withCoeff c).toFun e ∂ν = ∑ k, c k * (ν (H.B k)).toReal :=
  integral_toFun _

/-- The compensated step integral of the function carried by a coefficient vector on the mark
sets of a simple profile. -/
theorem stepIntegral_withCoeff (N : PoissonRandomMeasure P ν) (H : SimpleProfile E ν)
    (c : Fin H.K → ℝ) (a b : ℝ) (ω : Ω) :
    (H.withCoeff c).stepIntegral N a b ω = ∑ k, c k * N.compensated (Set.Ioc a b ×ˢ H.B k) ω :=
  rfl

omit [SigmaFinite ν] in
/-- The `L²(ν)` pairing of the functions carried by two coefficient vectors on the mark sets of
one simple profile. -/
theorem integral_toFun_withCoeff_mul (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) :
    ∫ e, (H.withCoeff c).toFun e * (H.withCoeff c').toFun e ∂ν
      = ∑ k, c k * c' k * (ν (H.B k)).toReal := by
  simp_rw [toFun_withCoeff_mul, integral_toFun_withCoeff]
  rfl

omit [SigmaFinite ν] in
/-- The strips over the mark sets of a simple profile are measurable. -/
private theorem measurableSet_strip (H : SimpleProfile E ν) (a b : ℝ) (k : Fin H.K) :
    MeasurableSet (Set.Ioc a b ×ˢ H.B k) :=
  measurableSet_Ioc.prod (H.B_measurable k)

omit [SigmaFinite ν] in
/-- The strips over the mark sets of a simple profile are pairwise disjoint. -/
private theorem pairwise_disjoint_strip (H : SimpleProfile E ν) (a b : ℝ) :
    Pairwise fun k l => Disjoint (Set.Ioc a b ×ˢ H.B k) (Set.Ioc a b ×ˢ H.B l) :=
  fun _ _ hkl => Set.disjoint_left.2 fun _ hx hx' =>
    Set.disjoint_left.1 (H.B_disjoint hkl) hx.2 hx'.2

/-- The strips over the mark sets of a simple profile have finite intensity. -/
private theorem referenceIntensity_strip_ne_top' (H : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a)
    (b : ℝ) (k : Fin H.K) : referenceIntensity ν (Set.Ioc a b ×ˢ H.B k) ≠ ⊤ :=
  referenceIntensity_strip_ne_top ha (H.B_finite k)

/-- **The compensated product on a common family.** For two coefficient vectors on the mark sets
of one simple profile, the compensated product of the functions they carry is almost surely the
quadratic element of the strips over those mark sets. -/
theorem compensatedProduct_withCoeff_ae_eq (N : PoissonRandomMeasure P ν) (H : SimpleProfile E ν)
    (c c' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b
      =ᵐ[P] markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' := by
  have hfun : (fun e => (H.withCoeff c).toFun e * (H.withCoeff c').toFun e)
      = (H.withCoeff (c * c')).toFun := funext (toFun_withCoeff_mul H c c')
  filter_upwards [compensatedProfile_toFun N (H.withCoeff c) ha hab,
    compensatedProfile_toFun N (H.withCoeff c') ha hab,
    compensatedProfile_toFun N (H.withCoeff (c * c')) ha hab] with ω h1 h2 h3
  have hN : ∀ k, (N.N ω (Set.Ioc a b ×ˢ H.B k)).toReal
      = N.compensated (Set.Ioc a b ×ˢ H.B k) ω + (b - a) * (ν (H.B k)).toReal := by
    intro k
    rw [PoissonRandomMeasure.compensated, referenceIntensity_strip_toReal ha hab]
    ring
  rw [compensatedProduct, hfun, h1, h2, h3, integral_toFun_withCoeff, markedSecondChaos,
    stepIntegral_withCoeff, stepIntegral_withCoeff, stepIntegral_withCoeff]
  simp only [Pi.mul_apply, hN, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  rw [sub_sub]
  congr 2
  exact Finset.sum_congr rfl fun k _ => by ring

/-- The quadratic element of the strips over the mark sets of a simple profile is square
integrable. -/
private theorem memLp_markedSecondChaos_strip (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    MemLp (markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c') 2 P := by
  rw [show markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c'
      = fun ω => ∑ k, ∑ l, c k * c' l
        * poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω from
    funext (markedSecondChaos_eq_sum N _ c c')]
  exact memLp_finsetSum _ fun k _ => memLp_finsetSum _ fun l _ =>
    (memLp_two_poissonChaosProd N (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
      (referenceIntensity_strip_ne_top' H ha b) _).const_mul _

/-- A pair index is not the multi-degree of a single unit. -/
private theorem pairIndex_ne_single {p : ℕ} (k l m : Fin p) : pairIndex k l ≠ Pi.single m 1 := by
  intro h
  have hs := congrArg (fun α : Fin p → ℕ => ∑ j, α j) h
  simp [pairIndex, Finset.sum_add_distrib] at hs

/-- The quadratic element of the strips over the mark sets of a simple profile is orthogonal to
the compensated count of each strip. -/
private theorem integral_markedSecondChaos_strip_mul_compensated (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) (m : Fin H.K) :
    ∫ ω, markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * N.compensated (Set.Ioc a b ×ˢ H.B m) ω ∂P = 0 := by
  have hint : ∀ k l : Fin H.K, Integrable (fun ω => c k * c' l
      * poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω
      * N.compensated (Set.Ioc a b ×ˢ H.B m) ω) P := fun k l =>
    (((memLp_two_poissonChaosProd N (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
      (referenceIntensity_strip_ne_top' H ha b) _).const_mul _).integrable_mul
        (H.memLp_compensated_step N ha b m))
  simp_rw [markedSecondChaos_eq_sum, Finset.sum_mul]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [show (fun ω => c k * c' l
        * poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω
        * N.compensated (Set.Ioc a b ×ˢ H.B m) ω)
      = fun ω => (c k * c' l)
        * (poissonChaosProd N (pairIndex k l) (fun k => Set.Ioc a b ×ˢ H.B k) ω
          * N.compensated ((fun k => Set.Ioc a b ×ˢ H.B k) m) ω) from funext fun ω => by ring,
    integral_const_mul, integral_poissonChaosProd_mul_compensated_eq_zero N
      (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
      (referenceIntensity_strip_ne_top' H ha b) (pairIndex_ne_single k l m), mul_zero]

/-! ### The compensated product on a common family -/

/-- On a common family, the compensated product is square integrable. -/
theorem memLp_compensatedProduct_withCoeff (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b) 2 P :=
  (memLp_markedSecondChaos_strip N H c c' ha b).ae_eq
    (compensatedProduct_withCoeff_ae_eq N H c c' ha hab).symm

/-- On a common family, the compensated product is centred. -/
theorem integral_compensatedProduct_withCoeff (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c c' : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b ω ∂P = 0 := by
  rw [integral_congr_ae (compensatedProduct_withCoeff_ae_eq N H c c' ha hab)]
  exact integral_markedSecondChaos N (measurableSet_strip H a b) (pairwise_disjoint_strip H a b)
    (referenceIntensity_strip_ne_top' H ha b) c c'

/-- On a common family, the Gram of two compensated products. -/
theorem integral_compensatedProduct_withCoeff_mul (N : PoissonRandomMeasure P ν)
    (H : SimpleProfile E ν) (c₁ c₂ c₃ c₄ : Fin H.K → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N (H.withCoeff c₁).toFun (H.withCoeff c₂).toFun a b ω
        * compensatedProduct N (H.withCoeff c₃).toFun (H.withCoeff c₄).toFun a b ω ∂P
      = (b - a) ^ 2
        * ((∫ e, (H.withCoeff c₁).toFun e * (H.withCoeff c₃).toFun e ∂ν)
            * (∫ e, (H.withCoeff c₂).toFun e * (H.withCoeff c₄).toFun e ∂ν)
          + (∫ e, (H.withCoeff c₁).toFun e * (H.withCoeff c₄).toFun e ∂ν)
            * (∫ e, (H.withCoeff c₂).toFun e * (H.withCoeff c₃).toFun e ∂ν)) := by
  rw [integral_congr_ae (by
    filter_upwards [compensatedProduct_withCoeff_ae_eq N H c₁ c₂ ha hab,
      compensatedProduct_withCoeff_ae_eq N H c₃ c₄ ha hab] with ω h1 h2
    rw [h1, h2])]
  have hs : ∀ x y : Fin H.K → ℝ, ∑ k, x k * y k * ((b - a) * (ν (H.B k)).toReal)
      = (b - a) * ∑ k, x k * y k * (ν (H.B k)).toReal := fun x y => by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [integral_markedSecondChaos_strip_mul N ha hab H.B_measurable H.B_finite H.B_disjoint,
    hs, hs, hs, hs]
  simp_rw [integral_toFun_withCoeff_mul]
  ring

/-- On a common family, the compensated product is orthogonal to the compensated integral of
every function carried by the family. -/
theorem integral_compensatedProduct_withCoeff_mul_compensatedProfile
    (N : PoissonRandomMeasure P ν) (H : SimpleProfile E ν) (c c' d : Fin H.K → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N (H.withCoeff c).toFun (H.withCoeff c').toFun a b ω
        * compensatedProfile N (H.withCoeff d).toFun a b ω ∂P = 0 := by
  rw [integral_congr_ae (by
    filter_upwards [compensatedProduct_withCoeff_ae_eq N H c c' ha hab,
      compensatedProfile_toFun N (H.withCoeff d) ha hab] with ω h1 h2
    rw [h1, h2])]
  have hint : ∀ m : Fin H.K, Integrable (fun ω =>
      markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * (d m * N.compensated (Set.Ioc a b ×ˢ H.B m) ω)) P := fun m =>
    (memLp_markedSecondChaos_strip N H c c' ha b).integrable_mul
      ((H.memLp_compensated_step N ha b m).const_mul _)
  simp only [stepIntegral_withCoeff, Finset.mul_sum]
  rw [integral_finsetSum _ fun m _ => hint m]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [show (fun ω => markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * (d m * N.compensated (Set.Ioc a b ×ˢ H.B m) ω))
      = fun ω => d m * (markedSecondChaos N (fun k => Set.Ioc a b ×ˢ H.B k) c c' ω
        * N.compensated (Set.Ioc a b ×ˢ H.B m) ω) from funext fun ω => by ring,
    integral_const_mul, integral_markedSecondChaos_strip_mul_compensated N H c c' ha b m,
    mul_zero]

/-! ### The compensated product of simple profiles -/

/-- The compensated product of the functions of two simple mark profiles is square integrable. -/
theorem memLp_compensatedProduct (N : PoissonRandomMeasure P ν) (G₁ G₂ : SimpleProfile E ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    MemLp (compensatedProduct N G₁.toFun G₂.toFun a b) 2 P := by
  obtain ⟨H, d, hd⟩ := exists_refinement ![G₁, G₂]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm]
  exact memLp_compensatedProduct_withCoeff N H _ _ ha hab

/-- The compensated product of the functions of two simple mark profiles is centred. -/
theorem integral_compensatedProduct (N : PoissonRandomMeasure P ν) (G₁ G₂ : SimpleProfile E ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N G₁.toFun G₂.toFun a b ω ∂P = 0 := by
  obtain ⟨H, d, hd⟩ := exists_refinement ![G₁, G₂]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm]
  exact integral_compensatedProduct_withCoeff N H _ _ ha hab

/-- **The Gram at simple profiles.** The `L²(P)` pairing of the compensated products of the
functions of simple mark profiles, with `⟨u, v⟩ = ∫ u v dν`:
`E[Q(u₁, u₂) Q(u₃, u₄)] = (b − a)² (⟨u₁, u₃⟩ ⟨u₂, u₄⟩ + ⟨u₁, u₄⟩ ⟨u₂, u₃⟩)`. -/
theorem integral_compensatedProduct_mul (N : PoissonRandomMeasure P ν)
    (G₁ G₂ G₃ G₄ : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N G₁.toFun G₂.toFun a b ω
        * compensatedProduct N G₃.toFun G₄.toFun a b ω ∂P
      = (b - a) ^ 2 * ((∫ e, G₁.toFun e * G₃.toFun e ∂ν) * (∫ e, G₂.toFun e * G₄.toFun e ∂ν)
        + (∫ e, G₁.toFun e * G₄.toFun e ∂ν) * (∫ e, G₂.toFun e * G₃.toFun e ∂ν)) := by
  obtain ⟨H, d, hd⟩ := exists_refinement ![G₁, G₂, G₃, G₄]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm,
    show G₃.toFun = (H.withCoeff (d 2)).toFun from funext fun e => (hd 2 e).symm,
    show G₄.toFun = (H.withCoeff (d 3)).toFun from funext fun e => (hd 3 e).symm]
  exact integral_compensatedProduct_withCoeff_mul N H _ _ _ _ ha hab

/-- **Orthogonality to the first chaos at simple profiles.** The compensated product of the
functions of two simple mark profiles is orthogonal to the compensated integral of the function
of a third. -/
theorem integral_compensatedProduct_mul_compensatedProfile (N : PoissonRandomMeasure P ν)
    (G₁ G₂ G₃ : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∫ ω, compensatedProduct N G₁.toFun G₂.toFun a b ω
        * compensatedProfile N G₃.toFun a b ω ∂P = 0 := by
  obtain ⟨H, d, hd⟩ := exists_refinement ![G₁, G₂, G₃]
  rw [show G₁.toFun = (H.withCoeff (d 0)).toFun from funext fun e => (hd 0 e).symm,
    show G₂.toFun = (H.withCoeff (d 1)).toFun from funext fun e => (hd 1 e).symm,
    show G₃.toFun = (H.withCoeff (d 2)).toFun from funext fun e => (hd 2 e).symm]
  exact integral_compensatedProduct_withCoeff_mul_compensatedProfile N H _ _ _ ha hab

end SimpleProfile

end LevyStochCalc.Poisson
