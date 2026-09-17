/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointChaosStep

/-!
# Total-degree blocks of a step of a Lévy driver

For a step `(a, b]` with `a < b` and a coefficient `c` bounded and strongly measurable for the
joint filtration at `a`, the node preceding the step, the pairing `E[c J_(n, m) J_(n', m')]` of
two joint chaos elements of the step weighted by `c` is the mean `E[c]` of the coefficient times
the bidegree pairing `δ_(n n') δ_(m m') n! τ ^ n m! λ ^ m`, for `τ = b - a` and
`λ = (b - a) ν(A)`; elements of different bidegree therefore stay orthogonal against such a
coefficient. The block of total degree `e` is the sum over the bidegrees `(n, m)` with `n + m = e`
of the elements of that bidegree weighted by such coefficients, and two blocks of different total
degree are orthogonal in `L²(P)`.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointChaosBlock` — the block of total degree `e` of a step.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul` — the pairing of two
  elements of a step weighted by a bounded coefficient measurable at the node preceding the step
  is the mean of the coefficient times the bidegree pairing.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointChaosStep_mul_eq_zero` — orthogonality
  across bidegrees against such a coefficient.
* `LevyStochCalc.Driver.LevyDriver.integral_jointChaosBlock_mul_eq_zero` — orthogonality of two
  blocks of different total degree.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson
open scoped NNReal ENNReal

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- The pairing of two joint chaos elements of a step, weighted by a bounded coefficient
measurable at the node preceding the step, is the mean of the coefficient times the bidegree
pairing. -/
theorem integral_coeff_mul_jointChaosStep_mul (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {c : Ω → ℝ} (hc : StronglyMeasurable[D.filtration (a : ℝ)] c) {Cb : ℝ}
    (hcb : ∀ ω, ‖c ω‖ ≤ Cb) (n m n' m' : ℕ) :
    ∫ ω, c ω * (D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω) ∂P
      = (∫ ω, c ω ∂P)
        * ((if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
          * (if m = m' then (m.factorial : ℝ)
              * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0)) := by
  set L : ℝ := (if n = n' then (n.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ n else 0)
        * (if m = m' then (m.factorial : ℝ)
            * (((b : ℝ) - (a : ℝ)) * (ν A).toReal) ^ m else 0) with hL
  have hm : (D.filtration (a : ℝ) : MeasurableSpace Ω) ≤ ‹MeasurableSpace Ω› := D.filtration.le _
  have hcm : StronglyMeasurable c := hc.mono hm
  have hJJ : Integrable (fun ω => D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω) P :=
    (D.memLp_two_jointChaosStep j hab.le hA hAν n m).integrable_mul
      (D.memLp_two_jointChaosStep j hab.le hA hAν n' m')
  have hprod : Integrable (fun ω => c ω * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω)) P :=
    hJJ.bdd_mul hcm.aestronglyMeasurable (Filter.Eventually.of_forall hcb)
  have hmulEq : (fun ω => c ω * (D.jointChaosStep j n m a b A ω
      * D.jointChaosStep j n' m' a b A ω))
      = c * fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω := rfl
  have hstep := condExp_mul_of_stronglyMeasurable_left (μ := P)
    (m := (D.filtration (a : ℝ) : MeasurableSpace Ω)) hc (hmulEq ▸ hprod) hJJ
  have hcond := D.condExp_jointChaosStep_mul j hab hA hAν n m n' m'
  rw [hmulEq, ← integral_condExp hm (f := c * fun ω => D.jointChaosStep j n m a b A ω
    * D.jointChaosStep j n' m' a b A ω)]
  have : P[c * fun ω => D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω
      | (D.filtration (a : ℝ) : MeasurableSpace Ω)] =ᵐ[P] fun ω => c ω * L := by
    filter_upwards [hstep, hcond] with ω h1 h2
    rw [h1, Pi.mul_apply, h2]
  rw [integral_congr_ae this, integral_mul_const]

/-- Joint chaos elements of a step of different bidegrees stay orthogonal against a bounded
coefficient measurable at the node preceding the step. -/
theorem integral_coeff_mul_jointChaosStep_mul_eq_zero (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {c : Ω → ℝ} (hc : StronglyMeasurable[D.filtration (a : ℝ)] c) {Cb : ℝ}
    (hcb : ∀ ω, ‖c ω‖ ≤ Cb) {n m n' m' : ℕ} (hne : (n, m) ≠ (n', m')) :
    ∫ ω, c ω * (D.jointChaosStep j n m a b A ω * D.jointChaosStep j n' m' a b A ω) ∂P = 0 := by
  rw [D.integral_coeff_mul_jointChaosStep_mul j hab hA hAν hc hcb n m n' m']
  rcases (Prod.mk.injEq n m n' m' ▸ hne : ¬(n = n' ∧ m = m')) with h
  by_cases hn : n = n'
  · have hm : m ≠ m' := fun hm => h ⟨hn, hm⟩
    simp [hm]
  · simp [hn]

/-- The block of total degree `e` of a step: the joint chaos elements of bidegrees summing to `e`
weighted by coefficients measurable at the node preceding the step. -/
noncomputable def jointChaosBlock (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    (A : Set E) (c : ℕ × ℕ → Ω → ℝ) (e : ℕ) (ω : Ω) : ℝ :=
  ∑ p ∈ Finset.antidiagonal e, c p ω * D.jointChaosStep j p.1 p.2 a b A ω

/-- Blocks of different total degree of a step are orthogonal when their coefficients are bounded
and measurable at the node preceding the step. -/
theorem integral_jointChaosBlock_mul_eq_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a < b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {c : ℕ × ℕ → Ω → ℝ} (hc : ∀ p, StronglyMeasurable[D.filtration (a : ℝ)] (c p)) {Cb : ℝ}
    (hcb : ∀ p ω, ‖c p ω‖ ≤ Cb) {e e' : ℕ} (hee : e ≠ e') :
    ∫ ω, jointChaosBlock D j a b A c e ω * jointChaosBlock D j a b A c e' ω ∂P = 0 := by
  have hm : (D.filtration (a : ℝ) : MeasurableSpace Ω) ≤ ‹MeasurableSpace Ω› := D.filtration.le _
  have hbdd : ∀ p q : ℕ × ℕ, ∀ ω, ‖c p ω * c q ω‖ ≤ Cb * Cb := by
    intro p q ω
    have h0 : (0 : ℝ) ≤ Cb := le_trans (norm_nonneg _) (hcb p ω)
    calc ‖c p ω * c q ω‖ = ‖c p ω‖ * ‖c q ω‖ := norm_mul _ _
      _ ≤ Cb * Cb := mul_le_mul (hcb p ω) (hcb q ω) (norm_nonneg _) h0
  have hterm : ∀ p q : ℕ × ℕ, Integrable (fun ω => (c p ω * D.jointChaosStep j p.1 p.2 a b A ω)
      * (c q ω * D.jointChaosStep j q.1 q.2 a b A ω)) P := by
    intro p q
    have hJJ : Integrable (fun ω => D.jointChaosStep j p.1 p.2 a b A ω
        * D.jointChaosStep j q.1 q.2 a b A ω) P :=
      (D.memLp_two_jointChaosStep j hab.le hA hAν p.1 p.2).integrable_mul
        (D.memLp_two_jointChaosStep j hab.le hA hAν q.1 q.2)
    have := hJJ.bdd_mul (((hc p).mono hm).mul ((hc q).mono hm)).aestronglyMeasurable
      (Filter.Eventually.of_forall (hbdd p q))
    exact this.congr (Filter.Eventually.of_forall fun ω => by simp only [Pi.mul_apply]; ring)
  have hexp : (fun ω => jointChaosBlock D j a b A c e ω * jointChaosBlock D j a b A c e' ω)
      = fun ω => ∑ p ∈ Finset.antidiagonal e, ∑ q ∈ Finset.antidiagonal e',
          (c p ω * D.jointChaosStep j p.1 p.2 a b A ω)
            * (c q ω * D.jointChaosStep j q.1 q.2 a b A ω) := by
    funext ω; simp only [jointChaosBlock]; rw [Finset.sum_mul_sum]
  rw [hexp, integral_finsetSum _ fun p _ =>
    integrable_finsetSum _ fun q _ => hterm p q]
  refine Finset.sum_eq_zero fun p hp => ?_
  rw [integral_finsetSum _ fun q _ => hterm p q]
  refine Finset.sum_eq_zero fun q hq => ?_
  have hpq : (p.1, p.2) ≠ (q.1, q.2) := by
    have hpe : p.1 + p.2 = e := Finset.mem_antidiagonal.mp hp
    have hqe : q.1 + q.2 = e' := Finset.mem_antidiagonal.mp hq
    intro h
    exact hee (by rw [← hpe, ← hqe, (Prod.mk.injEq _ _ _ _ ▸ h : p.1 = q.1 ∧ p.2 = q.2).1,
      (Prod.mk.injEq _ _ _ _ ▸ h : p.1 = q.1 ∧ p.2 = q.2).2])
  have hre : (fun ω => (c p ω * D.jointChaosStep j p.1 p.2 a b A ω)
      * (c q ω * D.jointChaosStep j q.1 q.2 a b A ω))
      = fun ω => (c p ω * c q ω) * (D.jointChaosStep j p.1 p.2 a b A ω
          * D.jointChaosStep j q.1 q.2 a b A ω) := by
    funext ω; ring
  rw [hre]
  exact D.integral_coeff_mul_jointChaosStep_mul_eq_zero j hab hA hAν
    (((hc p).mul (hc q))) (hbdd p q) hpq

end LevyStochCalc.Driver.LevyDriver
