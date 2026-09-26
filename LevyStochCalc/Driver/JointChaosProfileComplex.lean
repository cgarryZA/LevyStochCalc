/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.AugmentedFiltration
import LevyStochCalc.Driver.JointChaosProfile
import LevyStochCalc.Poisson.SimpleChaosRefine

/-!
# Complex joint chaos elements of a step at a mark profile, across mark families

For a Lévy driver, a coordinate `j`, a step `(a, b]` with `τ = b − a`, a finite pairwise
disjoint family `A` of mark sets of finite intensity and a complex profile `c` constant on each of
them, the complex bidegree-`(r, s)` element of the step is `X_(r, s)(c; A) = H_r(ΔWʲ; τ) D_s(c)`,
the product of the degree-`r` Wiener chaos element of the increment and the degree-`s` element of
the profile over the strips `(a, b] ×ˢ A k`. The Brownian and the Poisson factors are independent,
so the bilinear moment of two such elements over different families `A`, `A'` factors into the
Hermite and the Charlier Gram across the families,

  `E[X_(r, s)(c; A) X_(r', s')(c'; A')] = δ_(r r') r! τ ^ r δ_(s s') s! (τ ⟨c, c'⟩) ^ s`,

with `⟨c, c'⟩ = ∑_(k, l) c_k c'_l ν(A k ∩ A' l)`; distinct bidegrees, and a fortiori distinct total
degrees, are orthogonal whatever the two families. Every element of the step is measurable for
the σ-algebra of the step over the strips of both families, which is independent of the joint
filtration at `a`, and also of the augmentation of its join with an initial σ-algebra independent
of the whole filtration. So against a coefficient measurable for such a node σ-algebra the pairing
of two elements is the mean of the coefficient times their pairing, and the conditional pairing
given the node σ-algebra is the constant pairing.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfileC` — the complex bidegree-`(r, s)` element.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfileC` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_cross`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfileC_mul_conj_cross` — the bidegree
  Gram across two mark families.
* `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_filtration`,
  `LevyStochCalc.Driver.LevyDriver.indep_stepSigma_aug_sup` — the σ-algebra of the step is
  independent of the joint filtration at the node, and of the augmentation of its join with an
  independent initial σ-algebra.
* `LevyStochCalc.Driver.LevyDriver.integral_mul_eq_mul_integral_of_indep_stepSigma` — the pairing
  of a variable of the step against a coefficient measurable at the node.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStepProfileC_mul_conj` — the
  same for the Hermitian pairing of two elements over different families.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfileC_mul_conj` — the conditional
  Hermitian pairing at the node is the constant Gram.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
  Filter
open scoped NNReal ENNReal Topology

universe u v w

section Elements

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Measurability -/

/-- A complex degree element of a profile on a finite family of measurable regions is measurable
for the Poisson σ-algebra of the driver. -/
theorem measurable_markedChaosDegreeC_sigmaPoisson (D : LevyDriver.{u, v, w} P d ν) {p : ℕ}
    (s : ℕ) {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℂ) :
    Measurable[sigmaPoisson D.N] (markedChaosDegreeC D.N s B c) :=
  Finset.measurable_sum _ fun α _ => (Complex.measurable_ofReal.comp
    (Finset.univ.measurable_prod fun k _ =>
      (((continuous_charlierScaled (α k) _).measurable).comp ENNReal.measurable_toReal).comp
        (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N (hB k))))).const_mul _

/-- A complex degree element of a profile on a family of regions, each of which is a member of the
family `C`, is measurable for the σ-algebra of the step over `C`. -/
theorem measurable_markedChaosDegreeC_stepSigma (D : LevyDriver.{u, v, w} P d ν) {m p : ℕ}
    (C : Fin m → Set (ℝ × E)) (s t : ℝ) (r : ℕ) {B : Fin p → Set (ℝ × E)}
    (hBC : ∀ k, ∃ i, C i = B k) (c : Fin p → ℂ) :
    Measurable[D.stepSigma C s t] (markedChaosDegreeC D.N r B c) := by
  have hcount : ∀ k, Measurable[D.stepSigma C s t] (fun ω => D.N.N ω (B k)) := by
    intro k
    obtain ⟨i, hi⟩ := hBC k
    rw [← hi]
    exact Measurable.of_comap_le
      (le_sup_of_le_right (le_iSup (fun i => D.regionSigma (C i)) i))
  exact Finset.measurable_sum _ fun α _ => (Complex.measurable_ofReal.comp
    (Finset.univ.measurable_prod fun k _ =>
      (((continuous_charlierScaled (α k) _).measurable).comp ENNReal.measurable_toReal).comp
        (hcount k))).const_mul _

/-! ### The complex bidegree element -/

/-- The complex joint chaos element of bidegree `(r, s)` of the step `(a, b]` of the driver at a
complex profile `c` on a finite family `A` of mark sets: the degree-`r` Wiener chaos element of the
increment of the coordinate `j` times the degree-`s` element of the profile over the strips
`(a, b] ×ˢ A k`. -/
noncomputable def jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (r s : ℕ) (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℂ) (ω : Ω) : ℂ :=
  (wienerChaosStep r (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℂ)
    * markedChaosDegreeC D.N s (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω

/-- At a real profile the complex element is the real one. -/
theorem jointChaosStepProfileC_ofReal (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (r s : ℕ)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℝ) (ω : Ω) :
    D.jointChaosStepProfileC j r s a b A (fun k => (c k : ℂ)) ω
      = (D.jointChaosStepProfile j r s a b A c ω : ℂ) := by
  rw [jointChaosStepProfileC, markedChaosDegreeC_ofReal, jointChaosStepProfile,
    Complex.ofReal_mul]

/-- Conjugating the profile conjugates the element. -/
theorem conj_jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (r s : ℕ)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℂ) (ω : Ω) :
    (starRingEnd ℂ) (D.jointChaosStepProfileC j r s a b A c ω)
      = D.jointChaosStepProfileC j r s a b A (fun k => (starRingEnd ℂ) (c k)) ω := by
  rw [jointChaosStepProfileC, jointChaosStepProfileC, map_mul, Complex.conj_ofReal,
    conj_markedChaosDegreeC]

/-- A complex joint chaos element of a step at a profile on a family of measurable mark sets is
measurable. -/
theorem measurable_jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (r s : ℕ) (a b : ℝ≥0) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (c : Fin p → ℂ) :
    Measurable (D.jointChaosStepProfileC j r s a b A c) :=
  (Complex.measurable_ofReal.comp ((measurable_wienerChaosStep r _).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _)))).mul
    (measurable_markedChaosDegreeC D.N s (fun k => measurableSet_Ioc.prod (hA k)) c)

/-- A complex joint chaos element of a step at a profile on a family of mark sets whose strips are
members of the family `C` is measurable for the σ-algebra of the step over `C`. -/
theorem measurable_jointChaosStepProfileC_stepSigma (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (r s : ℕ) (a b : ℝ≥0) {m p : ℕ} (C : Fin m → Set (ℝ × E)) {A : Fin p → Set E}
    (hAC : ∀ k, ∃ i, C i = Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) (c : Fin p → ℂ) :
    Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (D.jointChaosStepProfileC j r s a b A c) := by
  have hincr : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      (le_sup_of_le_left (le_iSup (fun i => D.incrementSigma i (a : ℝ) (b : ℝ)) j))
  exact (Complex.measurable_ofReal.comp ((measurable_wienerChaosStep r _).comp hincr)).mul
    (D.measurable_markedChaosDegreeC_stepSigma C _ _ s hAC c)

/-- A complex joint chaos element of a step at a profile on a finite pairwise disjoint family of
mark sets of finite intensity lies in `L²`. -/
theorem memLp_two_jointChaosStepProfileC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (r s : ℕ)
    (c : Fin p → ℂ) :
    MemLp (D.jointChaosStepProfileC j r s a b A c) 2 P := by
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hBd : Pairwise fun k l => Disjoint (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  have hBfin : ∀ k, referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) ≠ ⊤ :=
    fun k => referenceIntensity_strip_ne_top a.coe_nonneg (hAν k)
  have hW : Integrable (fun ω => ‖(wienerChaosStep r (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℂ)‖ ^ 2) P :=
    (Brownian.BrownianMotion.memLp_two_wienerChaosStep_increment (D.W.W j) a b hab
      r).ofReal.integrable_norm_pow two_ne_zero
  have hN : Integrable (fun ω => ‖markedChaosDegreeC D.N s
      (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω‖ ^ 2) P :=
    (memLp_two_markedChaosDegreeC D.N hBm hBd hBfin s c).integrable_norm_pow two_ne_zero
  have hind : IndepFun
      (fun ω => ‖(wienerChaosStep r (b - a)
        ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℂ)‖ ^ 2)
      (fun ω => ‖markedChaosDegreeC D.N s
        (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω‖ ^ 2) P :=
    D.indepFun_of_measurable
      (((continuous_norm.pow 2).measurable.comp
        (Complex.measurable_ofReal.comp (measurable_wienerChaosStep r _))).comp
          (Measurable.of_comap_le
            ((Brownian.comap_increment_le_sigmaBrownian (D.W.W j) (a : ℝ) (b : ℝ)).trans
              (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j))))
      ((continuous_norm.pow 2).measurable.comp
        (D.measurable_markedChaosDegreeC_sigmaPoisson s hBm c))
  refine (memLp_two_iff_integrable_sq_norm
    (D.measurable_jointChaosStepProfileC j r s a b hA c).aestronglyMeasurable).2 ?_
  refine (hind.integrable_mul hW hN).congr (Eventually.of_forall fun ω => ?_)
  simp only [Pi.mul_apply, jointChaosStepProfileC, norm_mul, mul_pow]

/-- **The bidegree Gram across two mark families.** The bilinear moment of complex joint chaos
elements of a step at profiles on two finite pairwise disjoint families of mark sets of finite
intensity is the Hermite Gram times the Charlier Gram across the families,
`δ_(r r') r! τ ^ r δ_(s s') s! (τ ∑_(k, l) c_k c'_l ν(A k ∩ A' l)) ^ s`. -/
theorem integral_jointChaosStepProfileC_mul_cross (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, D.jointChaosStepProfileC j r s a b A c ω
        * D.jointChaosStepProfileC j r' s' a b A' c' ω ∂P
      = (((if r = r' then (r.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ r else 0 : ℝ)) : ℂ)
        * (if s = s' then (s.factorial : ℂ) * ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
            * ∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s else 0) := by
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hBm' : ∀ l, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) :=
    fun l => measurableSet_Ioc.prod (hA' l)
  have hincr : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      ((Brownian.comap_increment_le_sigmaBrownian (D.W.W j) (a : ℝ) (b : ℝ)).trans
        (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j))
  set X : Ω → ℂ := fun ω => ((wienerChaosStep r (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * wienerChaosStep r' (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) : ℝ) : ℂ)
    with hXdef
  set Y : Ω → ℂ := fun ω =>
    markedChaosDegreeC D.N s (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
      * markedChaosDegreeC D.N s' (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) c' ω with hYdef
  have hX : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)] X :=
    Complex.measurable_ofReal.comp (((measurable_wienerChaosStep r _).mul
      (measurable_wienerChaosStep r' _)).comp hincr)
  have hY : Measurable[sigmaPoisson D.N] Y :=
    (D.measurable_markedChaosDegreeC_sigmaPoisson s hBm c).mul
      (D.measurable_markedChaosDegreeC_sigmaPoisson s' hBm' c')
  have hXm : Measurable X := hX.mono (iSup_le fun i => Brownian.sigmaBrownian_le _) le_rfl
  have hYm : Measurable Y := hY.mono (sigmaPoisson_le _) le_rfl
  have hrw : ∀ ω, D.jointChaosStepProfileC j r s a b A c ω
      * D.jointChaosStepProfileC j r' s' a b A' c' ω = X ω * Y ω := by
    intro ω
    simp only [jointChaosStepProfileC, hXdef, hYdef]
    push_cast
    ring
  rw [integral_congr_ae (Eventually.of_forall hrw),
    (D.indepFun_of_measurable hX hY).integral_fun_mul_eq_mul_integral
      hXm.aestronglyMeasurable hYm.aestronglyMeasurable]
  congr 1
  · rw [hXdef, integral_complex_ofReal,
      Brownian.BrownianMotion.integral_wienerChaosStep_increment_mul (D.W.W j) a b hab r r',
      NNReal.coe_sub hab]
  · exact integral_markedChaosDegreeC_strip_mul_cross D.N a.coe_nonneg (by exact_mod_cast hab)
      hA hAν hd hA' hAν' hd' s s' c c'

/-- **The Hermitian bidegree Gram across two mark families.**
`E[X_(r, s)(c; A) conj X_(r', s')(c'; A')]
  = δ_(r r') r! τ ^ r δ_(s s') s! (τ ∑_(k, l) c_k conj c'_l ν(A k ∩ A' l)) ^ s`. -/
theorem integral_jointChaosStepProfileC_mul_conj_cross (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    ∫ ω, D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω) ∂P
      = (((if r = r' then (r.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ r else 0 : ℝ)) : ℂ)
        * (if s = s' then (s.factorial : ℂ) * ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
            * ∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s
          else 0) := by
  simp_rw [conj_jointChaosStepProfileC]
  exact D.integral_jointChaosStepProfileC_mul_cross j hab hA hAν hd hA' hAν' hd' r s r' s' c _

end Elements

/-! ### The pairing at the node preceding the step -/

section Node

variable {Ω : Type u} {M 𝒢₀ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

/-- The σ-algebra of the step over `(a, b]` and a finite family of measurable regions inside
`(a, b] ×ˢ E` is independent of the joint filtration at `a`. -/
theorem indep_stepSigma_filtration (D : LevyDriver.{u, v, w} P d ν) {m : ℕ}
    (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hCs : ∀ k, C k ⊆ Set.Ioc a b ×ˢ Set.univ) :
    Indep (D.stepSigma C a b) (D.filtration a) P :=
  D.indep_stepSigma C hCm ha hab fun k =>
    (hCs k).trans (Set.prod_mono Set.Ioc_subset_Ioi_self le_rfl)

/-- The σ-algebra of the step over `(a, b]` and a finite family of measurable regions inside
`(a, b] ×ˢ E` is independent of the augmentation of `𝒢₀ ⊔ ℱ_a`, for an initial σ-algebra `𝒢₀`
independent of the whole joint filtration. -/
theorem indep_stepSigma_aug_sup (D : LevyDriver.{u, v, w} P d ν) {m : ℕ}
    (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k)) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) (hCs : ∀ k, C k ⊆ Set.Ioc a b ×ˢ Set.univ) (h𝒢₀ : 𝒢₀ ≤ mΩ)
    (hind₀ : Indep 𝒢₀ (⨆ t, D.filtration t) P) :
    Indep (D.stepSigma C a b) (aug (𝒢₀ ⊔ D.filtration a) mΩ P) P := by
  have hS := D.indep_stepSigma_filtration C hCm ha hab hCs
  have hSle : D.stepSigma C a b ≤ D.filtration b := D.stepSigma_le_filtration C hCm hab.le
    fun k => (hCs k).trans (Set.prod_mono Set.Ioc_subset_Iic_self le_rfl)
  have h2 : Indep 𝒢₀ (D.filtration a ⊔ D.stepSigma C a b) P :=
    indep_of_indep_of_le_right hind₀ (sup_le (le_iSup (fun t => D.filtration t) a)
      (hSle.trans (le_iSup (fun t => D.filtration t) b)))
  have h := indep_sup_left_of_indep (D.filtration.le a) h𝒢₀ (D.stepSigma_le C hCm a b)
    hS.symm h2
  rw [sup_comm] at h
  exact (indep_aug P h).symm

/-- Against a complex coefficient measurable for a σ-algebra `M` independent of the σ-algebra of
the step over `(s, t]` and a finite family of regions, the mean of the product with a complex
variable measurable for the latter factors. -/
theorem integral_mul_eq_mul_integral_of_indep_stepSigma (D : LevyDriver.{u, v, w} P d ν)
    {m : ℕ} (C : Fin m → Set (ℝ × E)) (hCm : ∀ k, MeasurableSet (C k)) (s t : ℝ)
    (hM : M ≤ mΩ) (hind : Indep (D.stepSigma C s t) M P)
    {Q Y : Ω → ℂ} (hQ : StronglyMeasurable[M] Q) (hY : Measurable[D.stepSigma C s t] Y) :
    ∫ ω, Q ω * Y ω ∂P = (∫ ω, Q ω ∂P) * ∫ ω, Y ω ∂P := by
  have hQY : IndepFun Q Y P :=
    (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_right
      (indep_of_indep_of_le_left hind.symm hQ.measurable.comap_le) hY.comap_le)
  exact hQY.integral_fun_mul_eq_mul_integral (hQ.mono hM).aestronglyMeasurable
    (hY.mono (D.stepSigma_le C hCm s t) le_rfl).aestronglyMeasurable

/-- The strips over `(a, b]` of two families of measurable mark sets, listed as one family, are
measurable. -/
theorem measurableSet_append_strip {p q : ℕ} (a b : ℝ≥0) {A : Fin p → Set E}
    {A' : Fin q → Set E} (hA : ∀ k, MeasurableSet (A k)) (hA' : ∀ l, MeasurableSet (A' l))
    (i : Fin (p + q)) :
    MeasurableSet (Fin.append (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) i) := by
  refine Fin.addCases (fun k => ?_) (fun l => ?_) i
  · rw [Fin.append_left]; exact measurableSet_Ioc.prod (hA k)
  · rw [Fin.append_right]; exact measurableSet_Ioc.prod (hA' l)

omit [MeasurableSpace E] in
/-- The strips over `(a, b]` of two families of mark sets, listed as one family, lie inside
`(a, b] ×ˢ E`. -/
theorem append_strip_subset {p q : ℕ} (a b : ℝ≥0) (A : Fin p → Set E) (A' : Fin q → Set E)
    (i : Fin (p + q)) :
    Fin.append (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l) i ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ := by
  refine Fin.addCases (fun k => ?_) (fun l => ?_) i
  · rw [Fin.append_left]; exact Set.prod_mono le_rfl (Set.subset_univ _)
  · rw [Fin.append_right]; exact Set.prod_mono le_rfl (Set.subset_univ _)

/-- The Hermitian pairing of two complex joint chaos elements of the step `(a, b]` over two
families of mark sets is measurable for the σ-algebra of the step over the strips of both
families. -/
theorem measurable_jointChaosStepProfileC_mul_conj_stepSigma (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) (a b : ℝ≥0) {p q : ℕ} (A : Fin p → Set E) (A' : Fin q → Set E)
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    Measurable[D.stepSigma (Fin.append (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
        (fun l => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A' l)) (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω)) := by
  simp_rw [conj_jointChaosStepProfileC]
  exact (D.measurable_jointChaosStepProfileC_stepSigma j r s a b _
      (fun k => ⟨Fin.castAdd q k, Fin.append_left _ _ k⟩) c).mul
    (D.measurable_jointChaosStepProfileC_stepSigma j r' s' a b _
      (fun l => ⟨Fin.natAdd p l, Fin.append_right _ _ l⟩) _)

/-- **The pairing at the node across two mark families.** Against a complex coefficient `Q`
measurable for a σ-algebra `M` independent of the σ-algebra of the step over `(a, b]` and every
finite family of measurable regions inside `(a, b] ×ˢ E` (such as the joint filtration at `a`),
the Hermitian pairing of two complex joint chaos elements of the step over two families of mark
sets is the mean of `Q` times their pairing. -/
theorem integral_coeff_mul_jointChaosStepProfileC_mul_conj (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hA' : ∀ l, MeasurableSet (A' l)) (hM : M ≤ mΩ)
    (hind : ∀ {m : ℕ} (C : Fin m → Set (ℝ × E)), (∀ k, MeasurableSet (C k)) →
      (∀ k, C k ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ) →
        Indep (D.stepSigma C (a : ℝ) (b : ℝ)) M P)
    {Q : Ω → ℂ} (hQ : StronglyMeasurable[M] Q) (r s r' s' : ℕ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) :
    ∫ ω, Q ω * (D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω)) ∂P
      = (∫ ω, Q ω ∂P) * ∫ ω, D.jointChaosStepProfileC j r s a b A c ω
          * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω) ∂P :=
  D.integral_mul_eq_mul_integral_of_indep_stepSigma _ (measurableSet_append_strip a b hA hA')
    _ _ hM (hind _ (measurableSet_append_strip a b hA hA') (append_strip_subset a b A A')) hQ
    (D.measurable_jointChaosStepProfileC_mul_conj_stepSigma j a b A A' r s r' s' c c')

/-- **The conditional pairing at the node across two mark families.** Given a σ-algebra `M`
independent of the σ-algebra of the step over `(a, b]` and every finite family of measurable
regions inside `(a, b] ×ˢ E` (such as the joint filtration at `a`), the conditional expectation
of the Hermitian pairing of two complex joint chaos elements of the step over two families of
mark sets is the constant bidegree Gram. -/
theorem condExp_jointChaosStepProfileC_mul_conj (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (hM : M ≤ mΩ)
    (hind : ∀ {m : ℕ} (C : Fin m → Set (ℝ × E)), (∀ k, MeasurableSet (C k)) →
      (∀ k, C k ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ) →
        Indep (D.stepSigma C (a : ℝ) (b : ℝ)) M P)
    (r s r' s' : ℕ) (c : Fin p → ℂ) (c' : Fin q → ℂ) :
    P[fun ω => D.jointChaosStepProfileC j r s a b A c ω
        * (starRingEnd ℂ) (D.jointChaosStepProfileC j r' s' a b A' c' ω) | M]
      =ᵐ[P] fun _ => (((if r = r' then (r.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ r
          else 0 : ℝ)) : ℂ)
        * (if s = s' then (s.factorial : ℂ) * ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
            * ∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)) ^ s
          else 0) := by
  have hCm := measurableSet_append_strip a b hA hA'
  have h := condExp_indep_eq (D.stepSigma_le _ hCm (a : ℝ) (b : ℝ)) hM
    (D.measurable_jointChaosStepProfileC_mul_conj_stepSigma j a b A A' r s r' s' c
      c').stronglyMeasurable (hind _ hCm (append_strip_subset a b A A'))
  rw [D.integral_jointChaosStepProfileC_mul_conj_cross j hab hA hAν hd hA' hAν' hd'] at h
  exact h

end Node

end LevyStochCalc.Driver.LevyDriver
