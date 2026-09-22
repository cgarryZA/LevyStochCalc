/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointChaosStep
import LevyStochCalc.Poisson.SimpleChaosDegree

/-!
# The joint chaos element of one step of a Lévy driver at a simple mark profile

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a finite pairwise disjoint family `A` of
mark sets of finite intensity carrying a profile `c` constant on each of them, the
bidegree-`(n, m)` element of the step is the product `H_n(ΔWʲ; b - a) D_m(c)` of the degree-`n`
Wiener chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` chaos element of the
profile over the strips `(a, b] ×ˢ A k`. Since `σ(W)` and `σ(N)` are independent, the expectation
of a product of a function of the increment and a function of the counts of the strips factors,
so the `L²` pairing of two such elements is the product of the Hermite and the Charlier factor,
`E[J_(n, m)(c) J_(n', m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m` for `τ = b - a` and
the bilinear form `⟨c, c'⟩ = ∑_k c_k c'_k τ ν(A k)`. Distinct bidegrees are therefore orthogonal,
and a fortiori so are distinct total degrees `n + m`. The step tuple is independent of the joint
filtration at `a`, so the conditional pairing at that node is the same constant.

One Brownian coordinate is covered, and the profile is constant on the sets of one given family:
no mode of `L²(ν)` beyond such combinations of indicators enters. On a one-set family the element
is the single-mark-set element of a step scaled by `c 0 ^ m`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStepProfile` — the bidegree-`(n, m)` element of a
  step at a mark profile.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.measurable_markedChaosDegree_sigmaPoisson` — a degree element
  of a profile is measurable for the Poisson σ-algebra of the driver.
* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_markedChaosDegree` — a Brownian increment
  of the driver is independent of a degree element of a profile of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStepProfile` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul` —
  `E[J_(n,m)(c) J_(n',m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_sq` — the second moment as the
  product of the Hermite and the Charlier factor.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStepProfile_mul_eq_zero_of_add_ne` —
  orthogonality across bidegrees and across total degrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStepProfile_mul` — the conditional pairing
  at the node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Independence of the Brownian and the Poisson data of a step -/

namespace LevyDriver

/-- A degree element of a profile on a finite family of measurable regions is measurable for the
Poisson σ-algebra of the driver. -/
theorem measurable_markedChaosDegree_sigmaPoisson (D : LevyDriver.{u, v, w} P d ν) {p : ℕ}
    (s : ℕ) {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k)) (c : Fin p → ℝ) :
    Measurable[sigmaPoisson D.N] (Poisson.markedChaosDegree D.N s B c) :=
  Finset.measurable_sum _ fun α _ =>
    (Finset.univ.measurable_prod fun k _ =>
        (((Probability.continuous_charlierScaled (α k) _).measurable).comp
            ENNReal.measurable_toReal).comp
          (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N (hB k)))).const_mul _

/-- An increment of one Brownian coordinate of the driver is independent of a degree element of a
profile on a finite family of measurable regions of its Poisson random measure. -/
theorem indepFun_increment_markedChaosDegree (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (s t : ℝ) {p : ℕ} (m : ℕ) {B : Fin p → Set (ℝ × E)} (hB : ∀ k, MeasurableSet (B k))
    (c : Fin p → ℝ) :
    IndepFun (fun ω => (D.W.W j).W t ω - (D.W.W j).W s ω)
      (Poisson.markedChaosDegree D.N m B c) P :=
  D.indepFun_of_measurable
    (Measurable.of_comap_le ((Brownian.comap_increment_le_sigmaBrownian (D.W.W j) s t).trans
      (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j)))
    (D.measurable_markedChaosDegree_sigmaPoisson m hB c)

/-! ### The element of a bidegree at a mark profile -/

/-- The joint chaos element of bidegree `(n, m)` of the step `(a, b]` of the driver at a profile
`c` on a finite family `A` of mark sets: the product of the degree-`n` Wiener chaos element of the
increment of the coordinate `j` and the degree-`m` chaos element of the profile over the strips
`(a, b] ×ˢ A k`. -/
noncomputable def jointChaosStepProfile (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℝ) (ω : Ω) : ℝ :=
  Probability.wienerChaosStep n (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω

/-- The bidegree-`(0, 0)` element of a step of the driver at a mark profile is `1`. -/
@[simp] theorem jointChaosStepProfile_zero_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (c : Fin p → ℝ) (ω : Ω) :
    D.jointChaosStepProfile j 0 0 a b A c ω = 1 := by
  simp [jointChaosStepProfile]

/-- On a one-set family the element at a mark profile is the single-mark-set element of the step
scaled by the `m`-th power of the value of the profile. -/
theorem jointChaosStepProfile_fin_one (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) (A : Fin 1 → Set E) (c : Fin 1 → ℝ) (ω : Ω) :
    D.jointChaosStepProfile j n m a b A c ω = c 0 ^ m * D.jointChaosStep j n m a b (A 0) ω := by
  rw [jointChaosStepProfile, Poisson.markedChaosDegree_fin_one, jointChaosStep]
  ring

/-- A joint chaos element of a step of the driver at a profile on a family of measurable mark
sets is measurable. -/
theorem measurable_jointChaosStepProfile (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k)) (c : Fin p → ℝ) :
    Measurable (D.jointChaosStepProfile j n m a b A c) :=
  ((Probability.measurable_wienerChaosStep n _).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _))).mul
    (Poisson.measurable_markedChaosDegree D.N m (fun k => measurableSet_Ioc.prod (hA k)) c)

/-- A joint chaos element of a step of the driver at a profile on a finite pairwise disjoint
family of mark sets of finite intensity lies in `L²`. -/
theorem memLp_two_jointChaosStepProfile (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m : ℕ)
    (c : Fin p → ℝ) :
    MemLp (D.jointChaosStepProfile j n m a b A c) 2 P := by
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hBd : Pairwise fun k l => Disjoint (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k)
      (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A l) := fun k l hkl =>
    Set.disjoint_left.2 fun x hx hx' => Set.disjoint_left.1 (hd hkl) hx.2 hx'.2
  have hBfin : ∀ k, Poisson.referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) ≠ ⊤ :=
    fun k => Poisson.referenceIntensity_strip_ne_top a.coe_nonneg (hAν k)
  have hW : Integrable (fun ω => Probability.wienerChaosStep n (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2) P := by
    simpa only [pow_two] using
      Brownian.BrownianMotion.integrable_wienerChaosStep_increment_mul (D.W.W j) a b hab n n
  have hN : Integrable (fun ω => Poisson.markedChaosDegree D.N m
      (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω ^ 2) P := by
    simpa only [pow_two] using
      Poisson.integrable_markedChaosDegree_mul D.N hBm hBd hBfin m m c c
  have hcomp : IndepFun
      (fun ω => Probability.wienerChaosStep n (b - a)
        ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2)
      (fun ω => Poisson.markedChaosDegree D.N m
        (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω ^ 2) P :=
    (D.indepFun_increment_markedChaosDegree j (a : ℝ) (b : ℝ) m hBm c).comp
      ((Probability.measurable_wienerChaosStep n _).pow_const 2) (measurable_id.pow_const 2)
  refine (memLp_two_iff_integrable_sq
    (D.measurable_jointChaosStepProfile j n m a b hA c).aestronglyMeasurable).2 ?_
  have hmul := hcomp.integrable_mul hW hN
  simp only [jointChaosStepProfile, mul_pow]
  exact hmul

/-- The `L²` pairing of the joint chaos elements of a step of the driver at mark profiles on a
finite pairwise disjoint family of mark sets of finite intensity factors into the Hermite and the
Charlier factor, so distinct bidegrees are orthogonal:
`E[J_(n,m)(c) J_(n',m')(c')] = δ_(n n') δ_(m m') n! τ ^ n m! ⟨c, c'⟩ ^ m` for `τ = b - a` and
`⟨c, c'⟩ = ∑_k c_k c'_k τ ν(A k)`. -/
theorem integral_jointChaosStepProfile_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m n' m' : ℕ)
    (c c' : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω
        * D.jointChaosStepProfile j n' m' a b A c' ω ∂P
      = (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (∑ k, c k * c' k * (((b : ℝ) - (a : ℝ)) * (ν (A k)).toReal)) ^ m else 0) := by
  classical
  have hBm : ∀ k, MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) :=
    fun k => measurableSet_Ioc.prod (hA k)
  have hincr : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      ((Brownian.comap_increment_le_sigmaBrownian (D.W.W j) (a : ℝ) (b : ℝ)).trans
        (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j))
  have hX : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)]
      (fun ω => Probability.wienerChaosStep n (b - a)
          ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
        * Probability.wienerChaosStep n' (b - a)
          ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)) :=
    ((Probability.measurable_wienerChaosStep n _).mul
      (Probability.measurable_wienerChaosStep n' _)).comp hincr
  have hY : Measurable[sigmaPoisson D.N]
      (fun ω => Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
        * Poisson.markedChaosDegree D.N m' (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c' ω) :=
    (D.measurable_markedChaosDegree_sigmaPoisson m hBm c).mul
      (D.measurable_markedChaosDegree_sigmaPoisson m' hBm c')
  have hXm : Measurable fun ω => Probability.wienerChaosStep n (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * Probability.wienerChaosStep n' (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    ((Probability.measurable_wienerChaosStep n _).mul
      (Probability.measurable_wienerChaosStep n' _)).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _))
  have hYm : Measurable fun ω =>
      Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
        * Poisson.markedChaosDegree D.N m' (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c' ω :=
    (Poisson.measurable_markedChaosDegree D.N m hBm c).mul
      (Poisson.measurable_markedChaosDegree D.N m' hBm c')
  have hrw : ∀ ω : Ω, D.jointChaosStepProfile j n m a b A c ω
      * D.jointChaosStepProfile j n' m' a b A c' ω
      = (Probability.wienerChaosStep n (b - a)
            ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * Probability.wienerChaosStep n' (b - a)
            ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω))
        * (Poisson.markedChaosDegree D.N m (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
          * Poisson.markedChaosDegree D.N m'
              (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c' ω) := by
    intro ω
    simp only [jointChaosStepProfile]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hrw),
    (D.indepFun_of_measurable hX hY).integral_fun_mul_eq_mul_integral
      hXm.aestronglyMeasurable hYm.aestronglyMeasurable]
  congr 1
  · rw [Brownian.BrownianMotion.integral_wienerChaosStep_increment_mul (D.W.W j) a b hab n n',
      NNReal.coe_sub hab]
  · exact Poisson.integral_markedChaosDegree_strip_mul D.N a.coe_nonneg
      (by exact_mod_cast hab) hA hAν hd m m' c c'

/-- Joint chaos elements of a step of the driver at mark profiles with different total degrees
are orthogonal. -/
theorem integral_jointChaosStepProfile_mul_eq_zero_of_add_ne (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) {n m n' m' : ℕ} (hdeg : n + m ≠ n' + m')
    (c c' : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω
      * D.jointChaosStepProfile j n' m' a b A c' ω ∂P = 0 := by
  classical
  rw [D.integral_jointChaosStepProfile_mul j hab hA hAν hd n m n' m' c c']
  rcases eq_or_ne n n' with rfl | hn
  · have hm : m ≠ m' := fun h => hdeg (by rw [h])
    simp [hm]
  · simp [hn]

/-- Joint chaos elements of a step of the driver at mark profiles of different bidegrees are
orthogonal. -/
theorem integral_jointChaosStepProfile_mul_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) {n m n' m' : ℕ}
    (hne : (n, m) ≠ (n', m')) (c c' : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω
      * D.jointChaosStepProfile j n' m' a b A c' ω ∂P = 0 := by
  classical
  rw [D.integral_jointChaosStepProfile_mul j hab hA hAν hd n m n' m' c c']
  rcases eq_or_ne n n' with rfl | hn
  · have hm : m ≠ m' := fun h => hne (by rw [h])
    simp [hm]
  · simp [hn]

/-- The second moment of a joint chaos element of a step of the driver at a mark profile is the
product of the Hermite and the Charlier factor,
`E[J_(n,m)(c) ^ 2] = n! τ ^ n m! (∑_k c_k ^ 2 τ ν(A k)) ^ m`. -/
theorem integral_jointChaosStepProfile_sq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m : ℕ)
    (c : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω ^ 2 ∂P
      = ((n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n)
        * ((m.factorial : ℝ)
          * (∑ k, c k ^ 2 * (((b : ℝ) - (a : ℝ)) * (ν (A k)).toReal)) ^ m) := by
  have h := D.integral_jointChaosStepProfile_mul j hab hA hAν hd n m n m c c
  rw [if_pos rfl, if_pos rfl] at h
  simp only [← pow_two] at h
  exact h

/-- The joint chaos elements of a step of the driver at a mark profile are centred in positive
total degree. -/
theorem integral_jointChaosStepProfile_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) {n m : ℕ}
    (hnm : n + m ≠ 0) (c : Fin p → ℝ) :
    ∫ ω, D.jointChaosStepProfile j n m a b A c ω ∂P = 0 := by
  have h := D.integral_jointChaosStepProfile_mul_eq_zero_of_add_ne j hab hA hAν hd
    (n := n) (m := m) (n' := 0) (m' := 0) (by simpa using hnm) c c
  simpa using h

/-- The conditional pairing of the joint chaos elements of a step of the driver at mark profiles,
taken at the node preceding the step, agrees with the unconditional one. -/
theorem condExp_jointChaosStepProfile_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (n m n' m' : ℕ)
    (c c' : Fin p → ℝ) :
    P[fun ω => D.jointChaosStepProfile j n m a b A c ω
        * D.jointChaosStepProfile j n' m' a b A c' ω | D.filtration (a : ℝ)]
      =ᵐ[P] fun _ => (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (∑ k, c k * c' k * (((b : ℝ) - (a : ℝ)) * (ν (A k)).toReal)) ^ m else 0) := by
  classical
  set C : Fin p → Set (ℝ × E) := fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k with hC
  have hCm : ∀ k, MeasurableSet (C k) := fun k => measurableSet_Ioc.prod (hA k)
  have hCs : ∀ k, C k ⊆ Set.Ioi (a : ℝ) ×ˢ Set.univ := fun k x hx => ⟨hx.1.1, trivial⟩
  have hindep : Indep (D.stepSigma C (a : ℝ) (b : ℝ)) (D.filtration (a : ℝ)) P :=
    D.indep_stepSigma C hCm a.coe_nonneg (by exact_mod_cast hab) hCs
  have hincr : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le
      (le_sup_of_le_left (le_iSup (fun i => D.incrementSigma i (a : ℝ) (b : ℝ)) j))
  have hcount : ∀ k, Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (fun ω => D.N.N ω (C k)) :=
    fun k => Measurable.of_comap_le
      (le_sup_of_le_right (le_iSup (fun k => D.regionSigma (C k)) k))
  have hmc : ∀ (r : ℕ) (e : Fin p → ℝ), Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (Poisson.markedChaosDegree D.N r C e) := fun r e =>
    Finset.measurable_sum _ fun α _ =>
      (Finset.univ.measurable_prod fun k _ =>
          (((Probability.continuous_charlierScaled (α k) _).measurable).comp
              ENNReal.measurable_toReal).comp (hcount k)).const_mul _
  have hstep : ∀ (q r : ℕ) (e : Fin p → ℝ), Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStepProfile j q r a b A e ω) := fun q r e =>
    ((Probability.measurable_wienerChaosStep q _).comp hincr).mul (hmc r e)
  have hmeas : StronglyMeasurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStepProfile j n m a b A c ω
        * D.jointChaosStepProfile j n' m' a b A c' ω) :=
    Measurable.stronglyMeasurable ((hstep n m c).mul (hstep n' m' c'))
  have h := condExp_indep_eq (D.stepSigma_le C hCm (a : ℝ) (b : ℝ)) (D.filtration.le (a : ℝ))
    hmeas hindep
  rw [D.integral_jointChaosStepProfile_mul j hab.le hA hAν hd n m n' m' c c'] at h
  exact h

end LevyDriver

end LevyStochCalc.Driver
