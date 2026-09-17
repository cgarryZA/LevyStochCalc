/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointChaosBlock

/-!
# Complex-scaled total-degree blocks of a step of a Lévy driver

For a step `(a, b]` of a Lévy driver and a family of complex numbers indexed by the bidegrees and
constant in the sample point, the block of total degree `e` is the sum, over the bidegrees
`(n, m)` with `n + m = e`, of the joint chaos elements of that bidegree scaled by those numbers.
Such a block is square integrable over a mark set of finite intensity, its complex conjugate is
the block of the conjugate scalars, and blocks of different total degree are orthogonal; at equal
total degree the bilinear pairing and the second moment of the modulus are the bidegree sums of
the products of the scalars against `n! τ ^ n m! λ ^ m`, for `τ = b - a` and `λ = (b - a) ν(A)`.
Against a bounded complex coefficient strongly measurable for the joint filtration at `a`, the
node preceding the step, the pairing of two joint chaos elements, and hence of two blocks, is the
mean of the coefficient times the bidegree pairing. Through `(ℑz)² = (‖z‖² − ℜ z²)/2` that
factorisation turns into the second moment of the imaginary part of the product of such a
coefficient with a block, read off the second moments of the two factors.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosBlockC` — the block of total degree `e` of a step at
  complex scalars.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlockC_mul` — the pairing of two
  complex-scaled blocks of a step.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlockC_sq` — the bilinear second moment of
  a complex-scaled block.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointChaosBlockC` — the second moment of the
  modulus of a complex-scaled block.
* `LevyStochCalc.Driver.LevyDriver.integral_coeffC_mul_jointChaosBlockC_mul` — the pairing of two
  complex-scaled blocks against a bounded complex coefficient measurable at the node preceding
  the step.
* `LevyStochCalc.Driver.LevyDriver.integral_sq_im_coeffC_mul_jointChaosBlockC` — the second
  moment of the imaginary part of such a coefficient times a block.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
open scoped NNReal ENNReal

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- The block of total degree `e` of a step at complex scalars: the joint chaos elements of the
bidegrees summing to `e`, each scaled by a complex number. -/
noncomputable def jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (c : ℕ × ℕ → ℂ) (e : ℕ) (ω : Ω) : ℂ :=
  ∑ p ∈ antidiagonal e, c p * (D.jointChaosStep j p.1 p.2 a b A ω : ℂ)

/-- The conjugate of a complex-scaled block is the block of the conjugate scalars. -/
theorem conj_jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (c : ℕ × ℕ → ℂ) (e : ℕ) (ω : Ω) :
    (starRingEnd ℂ) (jointChaosBlockC D j a b A c e ω)
      = jointChaosBlockC D j a b A (fun p => (starRingEnd ℂ) (c p)) e ω := by
  simp [jointChaosBlockC, map_sum]

/-- A complex-scaled block of a step over a mark set of finite intensity lies in `L²`. -/
theorem memLp_two_jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (c : ℕ × ℕ → ℂ) (e : ℕ) :
    MemLp (jointChaosBlockC D j a b A c e) 2 P := by
  have h := memLp_finsetSum (μ := P) (p := 2) (antidiagonal e)
    (f := fun p (ω : Ω) => c p * (D.jointChaosStep j p.1 p.2 a b A ω : ℂ))
    fun p _ => ((D.memLp_two_jointChaosStep j hab hA hAν p.1 p.2).ofReal).const_mul (c p)
  exact h

/-- The pairing of two complex-scaled blocks of a step: blocks of different total degree are
orthogonal, and at equal total degree the pairing is the bidegree sum of the products of the
scalars against `p.1! τ ^ p.1 p.2! λ ^ p.2`, for `τ = b - a` and `λ = (b - a) ν(A)`. -/
theorem integral_jointChaosBlockC_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (c c' : ℕ × ℕ → ℂ)
    (e e' : ℕ) :
    ∫ ω, jointChaosBlockC D j a b A c e ω * jointChaosBlockC D j a b A c' e' ω ∂P
      = if e = e' then ∑ p ∈ antidiagonal e, c p * c' p
          * ((((p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1)
              * ((p.2.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2) : ℝ) : ℂ)
        else 0 := by
  classical
  set F : ℕ × ℕ → ℕ × ℕ → Ω → ℂ := fun p q ω => (c p * c' q)
    * ((D.jointChaosStep j p.1 p.2 a b A ω
        * D.jointChaosStep j q.1 q.2 a b A ω : ℝ) : ℂ) with hF
  have hJJ : ∀ p q : ℕ × ℕ, Integrable (fun ω => D.jointChaosStep j p.1 p.2 a b A ω
      * D.jointChaosStep j q.1 q.2 a b A ω) P := fun p q =>
    (D.memLp_two_jointChaosStep j hab hA hAν p.1 p.2).integrable_mul
      (D.memLp_two_jointChaosStep j hab hA hAν q.1 q.2)
  have hterm : ∀ p q : ℕ × ℕ, Integrable (F p q) P :=
    fun p q => ((hJJ p q).ofReal).const_mul _
  have hexp : (fun ω => jointChaosBlockC D j a b A c e ω * jointChaosBlockC D j a b A c' e' ω)
      = fun ω => ∑ p ∈ antidiagonal e, ∑ q ∈ antidiagonal e', F p q ω := by
    funext ω
    simp only [jointChaosBlockC, Finset.sum_mul_sum, hF]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    push_cast
    ring
  have hinner : ∀ p q : ℕ × ℕ, ∫ ω, F p q ω ∂P
      = (c p * c' q) * (((if p.1 = q.1 then (p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1
              else 0)
            * (if p.2 = q.2 then (p.2.factorial : ℝ)
                * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2 else 0) : ℝ) : ℂ) := by
    intro p q
    rw [hF, integral_const_mul, integral_complex_ofReal,
      D.integral_jointChaosStep_mul j hab hA hAν p.1 p.2 q.1 q.2]
  rw [hexp, integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hterm p q]
  have hstep : ∀ p ∈ antidiagonal e, (∫ ω, ∑ q ∈ antidiagonal e', F p q ω ∂P)
      = ∑ q ∈ antidiagonal e', ∫ ω, F p q ω ∂P :=
    fun p _ => integral_finsetSum (antidiagonal e') (f := F p) fun q _ => hterm p q
  rw [Finset.sum_congr rfl hstep]
  simp only [hinner]
  have hkill : ∀ p q : ℕ × ℕ, p ≠ q →
      (((if p.1 = q.1 then (p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1 else 0)
        * (if p.2 = q.2 then (p.2.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2 else 0) : ℝ) : ℂ) = 0 := by
    intro p q hpq
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext_iff.2 ⟨h1, h⟩)
      simp [h2]
    · simp [h1]
  by_cases hee : e = e'
  · subst hee
    rw [if_pos rfl]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_eq_single_of_mem p hp fun q _ hqp => by
      rw [hkill p q (Ne.symm hqp), mul_zero]]
    simp
  · rw [if_neg hee]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have hpq : p ≠ q := by
      have hpe : p.1 + p.2 = e := by simpa using hp
      have hqe : q.1 + q.2 = e' := by simpa using hq
      intro h
      exact hee (by rw [← hpe, ← hqe, h])
    rw [hkill p q hpq, mul_zero]

/-- Complex-scaled blocks of different total degree are orthogonal. -/
theorem integral_jointChaosBlockC_mul_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (c c' : ℕ × ℕ → ℂ) {e e' : ℕ} (hee : e ≠ e') :
    ∫ ω, jointChaosBlockC D j a b A c e ω * jointChaosBlockC D j a b A c' e' ω ∂P = 0 := by
  rw [D.integral_jointChaosBlockC_mul j hab hA hAν c c' e e', if_neg hee]

/-- The bilinear second moment of a complex-scaled block of a step. -/
theorem integral_jointChaosBlockC_sq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (c : ℕ × ℕ → ℂ) (e : ℕ) :
    ∫ ω, jointChaosBlockC D j a b A c e ω ^ 2 ∂P
      = ∑ p ∈ antidiagonal e, c p ^ 2
          * ((((p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1)
              * ((p.2.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2) : ℝ) : ℂ) := by
  have h := D.integral_jointChaosBlockC_mul j hab hA hAν c c e e
  rw [if_pos rfl] at h
  simpa only [sq] using h

/-- The second moment of the modulus of a complex-scaled block of a step. -/
theorem integral_norm_sq_jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (c : ℕ × ℕ → ℂ) (e : ℕ) :
    ∫ ω, ‖jointChaosBlockC D j a b A c e ω‖ ^ 2 ∂P
      = ∑ p ∈ antidiagonal e, ‖c p‖ ^ 2
          * (((p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1)
              * ((p.2.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2)) := by
  have h := D.integral_jointChaosBlockC_mul j hab hA hAν c
    (fun p => (starRingEnd ℂ) (c p)) e e
  rw [if_pos rfl] at h
  have hpt : ∀ ω : Ω, ((‖jointChaosBlockC D j a b A c e ω‖ ^ 2 : ℝ) : ℂ)
      = jointChaosBlockC D j a b A c e ω
        * jointChaosBlockC D j a b A (fun p => (starRingEnd ℂ) (c p)) e ω := by
    intro ω
    rw [← conj_jointChaosBlockC D j a b A c e ω, Complex.mul_conj']
    push_cast
    ring
  refine Complex.ofReal_inj.mp ?_
  rw [← integral_complex_ofReal, integral_congr_ae (Filter.Eventually.of_forall hpt), h,
    Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Complex.mul_conj']
  push_cast
  ring

/-- The pairing of two joint chaos elements of a step, weighted by a bounded complex coefficient
measurable at the node preceding the step, is the mean of the coefficient times the bidegree
pairing. -/
theorem integral_coeffC_mul_jointChaosStep_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {c : Ω → ℂ} (hc : StronglyMeasurable[D.filtration (a : ℝ)] c) {Cb : ℝ}
    (hcb : ∀ ω, ‖c ω‖ ≤ Cb) (n m n' m' : ℕ) :
    ∫ ω, c ω * ((D.jointChaosStep j n m a b A ω
        * D.jointChaosStep j n' m' a b A ω : ℝ) : ℂ) ∂P
      = (∫ ω, c ω ∂P) * (((if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
          * (if m = m' then (m.factorial : ℝ)
              * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) : ℝ) : ℂ) := by
  classical
  set L : ℝ := (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
      * (if m = m' then (m.factorial : ℝ)
          * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) with hL
  have hm : (D.filtration (a : ℝ) : MeasurableSpace Ω) ≤ ‹MeasurableSpace Ω› := D.filtration.le _
  have hJJ : Integrable (fun ω => D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω) P :=
    (D.memLp_two_jointChaosStep j hab.le hA hAν n m).integrable_mul
      (D.memLp_two_jointChaosStep j hab.le hA hAν n' m')
  have hcre : StronglyMeasurable[D.filtration (a : ℝ)] (fun ω => (c ω).re) :=
    Complex.continuous_re.comp_stronglyMeasurable hc
  have hcim : StronglyMeasurable[D.filtration (a : ℝ)] (fun ω => (c ω).im) :=
    Complex.continuous_im.comp_stronglyMeasurable hc
  have hbre : ∀ ω, ‖(c ω).re‖ ≤ Cb := fun ω =>
    (Real.norm_eq_abs _ ▸ Complex.abs_re_le_norm (c ω)).trans (hcb ω)
  have hbim : ∀ ω, ‖(c ω).im‖ ≤ Cb := fun ω =>
    (Real.norm_eq_abs _ ▸ Complex.abs_im_le_norm (c ω)).trans (hcb ω)
  have hre := D.integral_coeff_mul_jointChaosStep_mul j hab hA hAν hcre hbre n m n' m'
  have him := D.integral_coeff_mul_jointChaosStep_mul j hab hA hAν hcim hbim n m n' m'
  rw [← hL] at hre him
  have hintre : Integrable (fun ω => (c ω).re * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω)) P :=
    hJJ.bdd_mul (hcre.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hbre)
  have hintim : Integrable (fun ω => (c ω).im * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω)) P :=
    hJJ.bdd_mul (hcim.mono hm).aestronglyMeasurable (Filter.Eventually.of_forall hbim)
  have hc_int : Integrable c P :=
    Integrable.mono' (integrable_const Cb) (hc.mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall hcb)
  have hpt : ∀ ω : Ω, c ω * ((D.jointChaosStep j n m a b A ω
        * D.jointChaosStep j n' m' a b A ω : ℝ) : ℂ)
      = (((c ω).re * (D.jointChaosStep j n m a b A ω
          * D.jointChaosStep j n' m' a b A ω) : ℝ) : ℂ)
        + (((c ω).im * (D.jointChaosStep j n m a b A ω
            * D.jointChaosStep j n' m' a b A ω) : ℝ) : ℂ) * Complex.I := by
    intro ω
    conv_lhs => rw [← Complex.re_add_im (c ω)]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_add (f := fun ω => (((c ω).re * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω) : ℝ) : ℂ))
    (g := fun ω => (((c ω).im * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω) : ℝ) : ℂ) * Complex.I)
    (hintre.ofReal) ((hintim.ofReal).mul_const Complex.I)]
  rw [integral_mul_const, integral_complex_ofReal, integral_complex_ofReal, hre, him]
  have hcc : (∫ ω, c ω ∂P) = ((∫ ω, (c ω).re ∂P : ℝ) : ℂ)
      + ((∫ ω, (c ω).im ∂P : ℝ) : ℂ) * Complex.I := by
    have h1 : ∫ ω, (c ω).re ∂P = (∫ ω, c ω ∂P).re :=
      Complex.reCLM.integral_comp_comm hc_int
    have h2 : ∫ ω, (c ω).im ∂P = (∫ ω, c ω ∂P).im :=
      Complex.imCLM.integral_comp_comm hc_int
    rw [h1, h2, Complex.re_add_im]
  rw [hcc]
  push_cast
  ring

/-- The pairing of two complex-scaled blocks of a step weighted by a bounded complex coefficient
measurable at the node preceding the step. -/
theorem integral_coeffC_mul_jointChaosBlockC_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {Q : Ω → ℂ} (hQ : StronglyMeasurable[D.filtration (a : ℝ)] Q) {Cb : ℝ}
    (hQb : ∀ ω, ‖Q ω‖ ≤ Cb) (c c' : ℕ × ℕ → ℂ) (e e' : ℕ) :
    ∫ ω, Q ω * (jointChaosBlockC D j a b A c e ω * jointChaosBlockC D j a b A c' e' ω) ∂P
      = (∫ ω, Q ω ∂P) * (if e = e' then ∑ p ∈ antidiagonal e, c p * c' p
          * ((((p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1)
              * ((p.2.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2) : ℝ) : ℂ)
        else 0) := by
  classical
  have hm : (D.filtration (a : ℝ) : MeasurableSpace Ω) ≤ ‹MeasurableSpace Ω› := D.filtration.le _
  set F : ℕ × ℕ → ℕ × ℕ → Ω → ℂ := fun p q ω => (c p * c' q)
    * (Q ω * ((D.jointChaosStep j p.1 p.2 a b A ω
        * D.jointChaosStep j q.1 q.2 a b A ω : ℝ) : ℂ)) with hF
  have hJJ : ∀ p q : ℕ × ℕ, Integrable (fun ω => D.jointChaosStep j p.1 p.2 a b A ω
      * D.jointChaosStep j q.1 q.2 a b A ω) P := fun p q =>
    (D.memLp_two_jointChaosStep j hab.le hA hAν p.1 p.2).integrable_mul
      (D.memLp_two_jointChaosStep j hab.le hA hAν q.1 q.2)
  have hQJ : ∀ p q : ℕ × ℕ, Integrable (fun ω => Q ω
      * ((D.jointChaosStep j p.1 p.2 a b A ω
          * D.jointChaosStep j q.1 q.2 a b A ω : ℝ) : ℂ)) P := fun p q =>
    ((hJJ p q).ofReal).bdd_mul (hQ.mono hm).aestronglyMeasurable
      (Filter.Eventually.of_forall hQb)
  have hterm : ∀ p q : ℕ × ℕ, Integrable (F p q) P := fun p q => (hQJ p q).const_mul _
  have hexp : (fun ω => Q ω * (jointChaosBlockC D j a b A c e ω
      * jointChaosBlockC D j a b A c' e' ω))
      = fun ω => ∑ p ∈ antidiagonal e, ∑ q ∈ antidiagonal e', F p q ω := by
    funext ω
    simp only [jointChaosBlockC]
    rw [Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [hF]
    push_cast
    ring
  have hinner : ∀ p q : ℕ × ℕ, ∫ ω, F p q ω ∂P
      = (c p * c' q) * ((∫ ω, Q ω ∂P)
          * (((if p.1 = q.1 then (p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1 else 0)
            * (if p.2 = q.2 then (p.2.factorial : ℝ)
                * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2 else 0) : ℝ) : ℂ)) := by
    intro p q
    rw [hF, integral_const_mul,
      D.integral_coeffC_mul_jointChaosStep_mul j hab hA hAν hQ hQb p.1 p.2 q.1 q.2]
  rw [hexp, integral_finsetSum _ fun p _ => integrable_finsetSum _ fun q _ => hterm p q]
  have hstep : ∀ p ∈ antidiagonal e, (∫ ω, ∑ q ∈ antidiagonal e', F p q ω ∂P)
      = ∑ q ∈ antidiagonal e', ∫ ω, F p q ω ∂P :=
    fun p _ => integral_finsetSum (antidiagonal e') (f := F p) fun q _ => hterm p q
  rw [Finset.sum_congr rfl hstep]
  simp only [hinner]
  have hkill : ∀ p q : ℕ × ℕ, p ≠ q →
      (((if p.1 = q.1 then (p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1 else 0)
        * (if p.2 = q.2 then (p.2.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2 else 0) : ℝ) : ℂ) = 0 := by
    intro p q hpq
    by_cases h1 : p.1 = q.1
    · have h2 : p.2 ≠ q.2 := fun h => hpq (Prod.ext_iff.2 ⟨h1, h⟩)
      simp [h2]
    · simp [h1]
  by_cases hee : e = e'
  · subst hee
    rw [if_pos rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    rw [Finset.sum_eq_single_of_mem p hp fun q _ hqp => by
      rw [hkill p q (Ne.symm hqp), mul_zero, mul_zero]]
    simp
    ring
  · rw [if_neg hee, mul_zero]
    refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
    have hpq : p ≠ q := by
      have hpe : p.1 + p.2 = e := by simpa using hp
      have hqe : q.1 + q.2 = e' := by simpa using hq
      intro h
      exact hee (by rw [← hpe, ← hqe, h])
    rw [hkill p q hpq, mul_zero, mul_zero]

/-- The second moment of the imaginary part of a complex-scaled block of a step against a bounded
complex coefficient measurable at the node preceding the step. -/
theorem integral_sq_im_coeffC_mul_jointChaosBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {Q : Ω → ℂ} (hQ : StronglyMeasurable[D.filtration (a : ℝ)] Q) {Cb : ℝ}
    (hQb : ∀ ω, ‖Q ω‖ ≤ Cb) (c : ℕ × ℕ → ℂ) (e : ℕ) :
    ∫ ω, ((Q ω * jointChaosBlockC D j a b A c e ω).im) ^ 2 ∂P
      = ((∫ ω, ‖Q ω‖ ^ 2 ∂P) * ∫ ω, ‖jointChaosBlockC D j a b A c e ω‖ ^ 2 ∂P
          - ((∫ ω, Q ω ^ 2 ∂P) * ∫ ω, jointChaosBlockC D j a b A c e ω ^ 2 ∂P).re) / 2 := by
  classical
  have hm : (D.filtration (a : ℝ) : MeasurableSpace Ω) ≤ ‹MeasurableSpace Ω› := D.filtration.le _
  set C : Ω → ℂ := jointChaosBlockC D j a b A c e with hC
  have hC2 : MemLp C 2 P := D.memLp_two_jointChaosBlockC j hab.le hA hAν c e
  -- the two node coefficients
  have hQn : StronglyMeasurable[D.filtration (a : ℝ)] (fun ω => ((‖Q ω‖ ^ 2 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.comp
      ((continuous_pow 2).comp continuous_norm)).comp_stronglyMeasurable hQ
  have hQnb : ∀ ω, ‖((‖Q ω‖ ^ 2 : ℝ) : ℂ)‖ ≤ Cb ^ 2 := by
    intro ω
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hQb ω) 2
  have hQs : StronglyMeasurable[D.filtration (a : ℝ)] (fun ω => Q ω ^ 2) := hQ.pow 2
  have hQsb : ∀ ω, ‖Q ω ^ 2‖ ≤ Cb ^ 2 := by
    intro ω
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hQb ω) 2
  -- first moment identity
  have h1 : ∫ ω, ‖Q ω * C ω‖ ^ 2 ∂P = (∫ ω, ‖Q ω‖ ^ 2 ∂P) * ∫ ω, ‖C ω‖ ^ 2 ∂P := by
    have hkey := D.integral_coeffC_mul_jointChaosBlockC_mul j hab hA hAν hQn hQnb c
      (fun p => (starRingEnd ℂ) (c p)) e e
    have hpt : ∀ ω : Ω, ((‖Q ω‖ ^ 2 : ℝ) : ℂ)
        * (jointChaosBlockC D j a b A c e ω
          * jointChaosBlockC D j a b A (fun p => (starRingEnd ℂ) (c p)) e ω)
        = ((‖Q ω * C ω‖ ^ 2 : ℝ) : ℂ) := by
      intro ω
      rw [← conj_jointChaosBlockC D j a b A c e ω, Complex.mul_conj', norm_mul, ← hC]
      push_cast
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_complex_ofReal] at hkey
    have hCC := D.integral_jointChaosBlockC_mul j hab.le hA hAν c
      (fun p => (starRingEnd ℂ) (c p)) e e
    have hnorm := D.integral_norm_sq_jointChaosBlockC j hab.le hA hAν c e
    rw [if_pos rfl] at hCC
    have hCsum : ((∫ ω, ‖C ω‖ ^ 2 ∂P : ℝ) : ℂ)
        = ∑ p ∈ antidiagonal e, c p * (starRingEnd ℂ) (c p)
          * ((((p.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ p.1)
              * ((p.2.factorial : ℝ) * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ p.2) : ℝ) : ℂ) := by
      rw [hC, hnorm, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Complex.mul_conj']
      push_cast
      ring
    rw [if_pos rfl, ← hCsum, integral_complex_ofReal] at hkey
    exact_mod_cast hkey
  -- second moment identity
  have h2 : ∫ ω, (Q ω * C ω) ^ 2 ∂P = (∫ ω, Q ω ^ 2 ∂P) * ∫ ω, C ω ^ 2 ∂P := by
    have hkey := D.integral_coeffC_mul_jointChaosBlockC_mul j hab hA hAν hQs hQsb c c e e
    have hpt : ∀ ω : Ω, Q ω ^ 2 * (jointChaosBlockC D j a b A c e ω
        * jointChaosBlockC D j a b A c e ω) = (Q ω * C ω) ^ 2 := by
      intro ω; rw [← hC]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)] at hkey
    have hCC := D.integral_jointChaosBlockC_sq j hab.le hA hAν c e
    rw [hkey, if_pos rfl, hC, hCC]
    exact congrArg _ (Finset.sum_congr rfl fun p _ => by rw [sq])
  -- integrability
  have hnC : Integrable (fun ω => ‖C ω‖ ^ 2) P := (hC2.norm).integrable_sq
  have hiQC : Integrable (fun ω => ‖Q ω * C ω‖ ^ 2) P := by
    have : Integrable (fun ω => ‖Q ω‖ ^ 2 * ‖C ω‖ ^ 2) P :=
      hnC.bdd_mul (((continuous_norm.comp_stronglyMeasurable
          (hQ.mono hm)).pow 2).aestronglyMeasurable)
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact pow_le_pow_left₀ (norm_nonneg _) (hQb ω) 2)
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [mul_pow])
  have hCsq : Integrable (fun ω => C ω * C ω) P := hC2.integrable_mul hC2
  have hi2 : Integrable (fun ω => (Q ω * C ω) ^ 2) P := by
    have := hCsq.bdd_mul ((hQs.mono hm).aestronglyMeasurable)
      (Filter.Eventually.of_forall hQsb)
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp [hC]; ring)
  have hre : Integrable (fun ω => ((Q ω * C ω) ^ 2).re) P := Complex.reCLM.integrable_comp hi2
  have hpt : ∀ ω : Ω, ((Q ω * C ω).im) ^ 2
      = (‖Q ω * C ω‖ ^ 2 - ((Q ω * C ω) ^ 2).re) / 2 := by
    intro ω
    have hz : ‖Q ω * C ω‖ ^ 2 = (Q ω * C ω).re ^ 2 + (Q ω * C ω).im ^ 2 := by
      rw [Complex.sq_norm]
      simp [Complex.normSq_apply]
      ring
    rw [hz]
    simp [pow_two, Complex.mul_re]
  have hrei : ∫ ω, ((Q ω * C ω) ^ 2).re ∂P = (∫ ω, (Q ω * C ω) ^ 2 ∂P).re :=
    Complex.reCLM.integral_comp_comm hi2
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_div,
    integral_sub hiQC hre, hrei, h1, h2]

end LevyStochCalc.Driver.LevyDriver
