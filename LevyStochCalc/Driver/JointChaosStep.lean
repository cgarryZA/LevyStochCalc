/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.GridIncrement
import LevyStochCalc.Brownian.ChaosStep
import LevyStochCalc.Poisson.ChaosStep

/-!
# The joint chaos element of one step of a Lévy driver

For a Lévy driver, a coordinate `j`, a step `(a, b]` and a mark set `A`, the bidegree-`(n, m)`
element of the step is the product `H_n(ΔWʲ; b - a) C_m(N(B); ν̂(B))` of the degree-`n` Wiener
chaos element of the increment `ΔWʲ = Wʲ_b - Wʲ_a` and the degree-`m` Poisson chaos element of
the strip `B = (a, b] ×ˢ A`. Since `σ(W)` and `σ(N)` are independent, the expectation of a
product of a function of the increment and a function of the count factors, so the `L²` pairing
of two such elements is the product of the Brownian and the Poisson pairings,
`E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m` for `τ = b - a` and
`λ = (b - a) ν(A)`. Distinct bidegrees are therefore orthogonal, and a fortiori so are distinct
total degrees `n + m`. The step tuple is independent of the joint filtration at `a`, so the
conditional pairing at that node is the same constant.

One Brownian coordinate and one mark set are covered: these are polynomials of the single
increment `ΔWʲ` and the single count `N(B)`, with no mark profile beyond the indicator of `A`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosStep` — the bidegree-`(n, m)` element of a step.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.indepFun_increment_count` — a Brownian increment of the driver
  is independent of a count of its Poisson random measure.
* `LevyStochCalc.Driver.LevyDriver.integral_increment_count_mul` — the expectation of a product
  of a function of an increment and a function of a count factors.
* `LevyStochCalc.Driver.LevyDriver.memLp_two_jointChaosStep` — square integrability.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul` —
  `E[J_(n, m) J_(n', m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m`.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero_of_add_ne` — orthogonality
  across total degrees.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosStep_mul_eq_zero` — orthogonality across
  bidegrees.
* `LevyStochCalc.Driver.LevyDriver.condExp_jointChaosStep_mul` — the conditional pairing at the
  node preceding the step.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

section Independence

variable {γ δ : Type*} [MeasurableSpace γ] [MeasurableSpace δ]

/-- A variable measurable for the Brownian σ-algebra of the driver is independent of a variable
measurable for its Poisson σ-algebra. -/
theorem indepFun_of_measurable (D : LevyDriver.{u, v, w} P d ν) {X : Ω → γ} {Y : Ω → δ}
    (hX : Measurable[⨆ i, Brownian.sigmaBrownian (D.W.W i)] X)
    (hY : Measurable[sigmaPoisson D.N] Y) : IndepFun X Y P :=
  (IndepFun_iff_Indep _ _ _).2
    (indep_of_indep_of_le_right (indep_of_indep_of_le_left D.indep hX.comap_le) hY.comap_le)

/-- An increment of one Brownian coordinate of the driver is independent of a count of its
Poisson random measure. -/
theorem indepFun_increment_count (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    IndepFun (fun ω => (D.W.W j).W t ω - (D.W.W j).W s ω) (fun ω => D.N.N ω B) P :=
  D.indepFun_of_measurable
    (Measurable.of_comap_le ((Brownian.comap_increment_le_sigmaBrownian (D.W.W j) s t).trans
      (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) j)))
    (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N hB))

/-- The vector of Brownian increments of the driver over a step is independent of a count of its
Poisson random measure. -/
theorem indepFun_vectorIncrement_count (D : LevyDriver.{u, v, w} P d ν) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) :
    IndepFun (fun ω (i : Fin d) => (D.W.W i).W t ω - (D.W.W i).W s ω)
      (fun ω => D.N.N ω B) P :=
  D.indepFun_of_measurable
    (@measurable_pi_lambda Ω _ _ (⨆ i, Brownian.sigmaBrownian (D.W.W i)) _ _
      fun i => Measurable.of_comap_le
        ((Brownian.comap_increment_le_sigmaBrownian (D.W.W i) s t).trans
          (le_iSup (fun i => Brownian.sigmaBrownian (D.W.W i)) i)))
    (Measurable.of_comap_le (comap_count_le_sigmaPoisson D.N hB))

/-- The expectation of a product of a function of a Brownian increment of the driver and a
function of a count of its Poisson random measure factors. -/
theorem integral_increment_count_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) {f : ℝ → ℝ} {g : ℝ≥0∞ → ℝ} (hf : Measurable f)
    (hg : Measurable g) :
    ∫ ω, f ((D.W.W j).W t ω - (D.W.W j).W s ω) * g (D.N.N ω B) ∂P
      = (∫ ω, f ((D.W.W j).W t ω - (D.W.W j).W s ω) ∂P) * ∫ ω, g (D.N.N ω B) ∂P :=
  (D.indepFun_increment_count j s t hB).integral_fun_comp_mul_comp
    (((D.W.W j).measurable_eval t).sub ((D.W.W j).measurable_eval s)).aemeasurable
    (D.N.measurable_eval hB).aemeasurable hf.aestronglyMeasurable hg.aestronglyMeasurable

/-- The expectation of a product of a function of the vector of Brownian increments of the driver
and a function of a count of its Poisson random measure factors. -/
theorem integral_vectorIncrement_count_mul (D : LevyDriver.{u, v, w} P d ν) (s t : ℝ)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) {f : (Fin d → ℝ) → ℝ} {g : ℝ≥0∞ → ℝ}
    (hf : Measurable f) (hg : Measurable g) :
    ∫ ω, f (fun i => (D.W.W i).W t ω - (D.W.W i).W s ω) * g (D.N.N ω B) ∂P
      = (∫ ω, f (fun i => (D.W.W i).W t ω - (D.W.W i).W s ω) ∂P)
        * ∫ ω, g (D.N.N ω B) ∂P :=
  (D.indepFun_vectorIncrement_count s t hB).integral_fun_comp_mul_comp
    (measurable_pi_lambda _ fun i =>
      ((D.W.W i).measurable_eval t).sub ((D.W.W i).measurable_eval s)).aemeasurable
    (D.N.measurable_eval hB).aemeasurable hf.aestronglyMeasurable hg.aestronglyMeasurable

end Independence

/-- The joint chaos element of bidegree `(n, m)` of the step `(a, b]` of the driver over the mark
set `A`: the product of the degree-`n` Wiener chaos element of the increment of the coordinate
`j` and the degree-`m` Poisson chaos element of the strip `(a, b] ×ˢ A`. -/
noncomputable def jointChaosStep (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) (A : Set E) (ω : Ω) : ℝ :=
  Probability.wienerChaosStep n (b - a) ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * Poisson.poissonChaosStep D.N m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω

/-- The bidegree-`(0, 0)` element of a step of the driver is `1`. -/
@[simp] theorem jointChaosStep_zero_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (ω : Ω) : D.jointChaosStep j 0 0 a b A ω = 1 := by
  simp [jointChaosStep]

/-- The bidegree-`(1, 1)` element is the product of the Brownian increment and the compensated
count of the strip. -/
theorem jointChaosStep_one_one (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (ω : Ω) :
    D.jointChaosStep j 1 1 a b A ω
      = ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
        * D.N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω := by
  simp [jointChaosStep]

/-- A joint chaos element of a step of the driver over a measurable mark set is
measurable. -/
theorem measurable_jointChaosStep (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (n m : ℕ)
    (a b : ℝ≥0) {A : Set E} (hA : MeasurableSet A) :
    Measurable (D.jointChaosStep j n m a b A) :=
  ((Probability.measurable_wienerChaosStep n _).comp
      (((D.W.W j).measurable_eval _).sub ((D.W.W j).measurable_eval _))).mul
    (Poisson.measurable_poissonChaosStep D.N m (measurableSet_Ioc.prod hA))

/-- A joint chaos element of a step of the driver over a mark set of finite intensity lies in
`L²`. -/
theorem memLp_two_jointChaosStep (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m : ℕ) :
    MemLp (D.jointChaosStep j n m a b A) 2 P := by
  have hB : MeasurableSet (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) := measurableSet_Ioc.prod hA
  have hfin : Poisson.referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ≠ ⊤ := by
    rw [Poisson.referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
    refine ENNReal.mul_ne_top (ne_top_of_le_ne_top ?_ (measure_mono Set.inter_subset_left)) hAν
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  have hW : Integrable (fun ω => Probability.wienerChaosStep n (b - a)
      ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2) P := by
    simpa only [pow_two] using
      Brownian.BrownianMotion.integrable_wienerChaosStep_increment_mul (D.W.W j) a b hab n n
  have hN : Integrable (fun ω =>
      Poisson.poissonChaosStep D.N m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω ^ 2) P := by
    simpa only [pow_two] using Poisson.integrable_poissonChaosStep_mul D.N hB hfin m m
  have hcomp : IndepFun
      (fun ω => Probability.wienerChaosStep n (b - a)
        ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) ^ 2)
      (fun ω => Poisson.poissonChaosStep D.N m (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ω ^ 2) P :=
    (D.indepFun_increment_count j (a : ℝ) (b : ℝ) hB).comp
      ((Probability.measurable_wienerChaosStep n _).pow_const 2)
      ((((Probability.continuous_charlierScaled m _).measurable).comp
        ENNReal.measurable_toReal).pow_const 2)
  refine (memLp_two_iff_integrable_sq
    (D.measurable_jointChaosStep j n m a b hA).aestronglyMeasurable).2 ?_
  have := hcomp.integrable_mul hW hN
  simp only [jointChaosStep, mul_pow]
  exact this

/-- The `L²` pairing of the joint chaos elements of a step of the driver factors into the
Brownian and the Poisson pairing, so distinct bidegrees are orthogonal:
`E[J_(n,m) J_(n',m')] = δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m` for `τ = b - a` and
`λ = (b - a) ν(A)`. -/
theorem integral_jointChaosStep_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m n' m' : ℕ) :
    ∫ ω, D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω ∂P
      = (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) := by
  classical
  set B : Set (ℝ × E) := Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A with hBdef
  have hB : MeasurableSet B := measurableSet_Ioc.prod hA
  set lam : ℝ := (Poisson.referenceIntensity ν B).toReal with hlam
  set f : ℝ → ℝ := fun x => Probability.wienerChaosStep n (b - a) x
    * Probability.wienerChaosStep n' (b - a) x with hf
  set g : ℝ≥0∞ → ℝ := fun y => Probability.charlierScaled m lam y.toReal
    * Probability.charlierScaled m' lam y.toReal with hg
  have hfm : Measurable f :=
    (Probability.measurable_wienerChaosStep n _).mul (Probability.measurable_wienerChaosStep n' _)
  have hgm : Measurable g :=
    (((Probability.continuous_charlierScaled m lam).measurable).comp
        ENNReal.measurable_toReal).mul
      (((Probability.continuous_charlierScaled m' lam).measurable).comp
        ENNReal.measurable_toReal)
  have hrw : ∀ ω : Ω, D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω
      = f ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) * g (D.N.N ω B) := by
    intro ω
    simp only [jointChaosStep, hf, hg, Poisson.poissonChaosStep, hlam]
    ring
  rw [show (∫ ω, D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω ∂P)
      = ∫ ω, f ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) * g (D.N.N ω B) ∂P from
    integral_congr_ae (Filter.Eventually.of_forall hrw)]
  rw [D.integral_increment_count_mul j (a : ℝ) (b : ℝ) hB hfm hgm]
  congr 1
  · rw [Brownian.BrownianMotion.integral_wienerChaosStep_increment_mul (D.W.W j) a b hab n n',
      NNReal.coe_sub hab]
  · have := Poisson.integral_poissonChaosStep_strip_mul D.N (a := (a : ℝ)) (b := (b : ℝ))
      a.coe_nonneg (by exact_mod_cast hab) hA hAν m m'
    simpa only [Poisson.poissonChaosStep, hg, hlam, hBdef] using this

/-- Joint chaos elements of a step of the driver with different total degrees are orthogonal. -/
theorem integral_jointChaosStep_mul_eq_zero_of_add_ne (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {n m n' m' : ℕ} (hdeg : n + m ≠ n' + m') :
    ∫ ω, D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω ∂P = 0 := by
  classical
  rw [D.integral_jointChaosStep_mul j hab hA hAν n m n' m']
  rcases eq_or_ne n n' with rfl | hn
  · have hm : m ≠ m' := fun h => hdeg (by rw [h])
    simp [hm]
  · simp [hn]

/-- Joint chaos elements of a step of the driver of different bidegrees are orthogonal. -/
theorem integral_jointChaosStep_mul_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {n m n' m' : ℕ} (hne : (n, m) ≠ (n', m')) :
    ∫ ω, D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω ∂P = 0 := by
  classical
  rw [D.integral_jointChaosStep_mul j hab hA hAν n m n' m']
  rcases eq_or_ne n n' with rfl | hn
  · have hm : m ≠ m' := fun h => hne (by rw [h])
    simp [hm]
  · simp [hn]

/-- The `L²` norm of a joint chaos element of a step of the driver,
`E[J_(n,m) ^ 2] = n! τ ^ n m! λ ^ m`. -/
theorem integral_jointChaosStep_sq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m : ℕ) :
    ∫ ω, D.jointChaosStep j n m a b A ω ^ 2 ∂P
      = ((n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n)
        * ((m.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m) := by
  simpa [pow_two] using D.integral_jointChaosStep_mul j hab hA hAν n m n m

/-- The joint chaos elements of a step of the driver of positive total degree are centred. -/
theorem integral_jointChaosStep_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {n m : ℕ}
    (hnm : n + m ≠ 0) :
    ∫ ω, D.jointChaosStep j n m a b A ω ∂P = 0 := by
  have h := D.integral_jointChaosStep_mul_eq_zero_of_add_ne j hab hA hAν
    (n := n) (m := m) (n' := 0) (m' := 0) (by simpa using hnm)
  simpa using h

/-- The conditional pairing of the joint chaos elements of a step of the driver at the node
preceding the step agrees with the unconditional one. -/
theorem condExp_jointChaosStep_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m n' m' : ℕ) :
    P[fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω
        | D.filtration (a : ℝ)]
      =ᵐ[P] fun _ => (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) := by
  classical
  set B : Set (ℝ × E) := Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A with hBdef
  have hB : MeasurableSet B := measurableSet_Ioc.prod hA
  set C : Fin 1 → Set (ℝ × E) := fun _ => B with hC
  have hCm : ∀ k, MeasurableSet (C k) := fun _ => hB
  have hCs : ∀ k, C k ⊆ Set.Ioi (a : ℝ) ×ˢ Set.univ := fun _ x hx => ⟨hx.1.1, trivial⟩
  have hindep : Indep (D.stepSigma C (a : ℝ) (b : ℝ)) (D.filtration (a : ℝ)) P :=
    D.indep_stepSigma C hCm a.coe_nonneg (by exact_mod_cast hab) hCs
  have hincr : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) :=
    Measurable.of_comap_le (le_sup_of_le_left (le_iSup (fun i => D.incrementSigma i a b) j))
  have hcount : Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (fun ω => D.N.N ω B) :=
    Measurable.of_comap_le (le_sup_of_le_right
      (le_iSup (fun k => D.regionSigma (C k)) (0 : Fin 1)))
  have hstep : ∀ p q : ℕ, Measurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStep j p q a b A ω) := fun p q =>
    ((Probability.measurable_wienerChaosStep p _).comp hincr).mul
      ((((Probability.continuous_charlierScaled q _).measurable).comp
        ENNReal.measurable_toReal).comp hcount)
  have hmeas : StronglyMeasurable[D.stepSigma C (a : ℝ) (b : ℝ)]
      (fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω) :=
    Measurable.stronglyMeasurable ((hstep n m).mul (hstep n' m'))
  have h := condExp_indep_eq (D.stepSigma_le C hCm (a : ℝ) (b : ℝ)) (D.filtration.le (a : ℝ))
    hmeas hindep
  rw [D.integral_jointChaosStep_mul j hab.le hA hAν n m n' m'] at h
  exact h

end LevyDriver

end LevyStochCalc.Driver
