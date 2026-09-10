/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaExhaustion
import LevyStochCalc.Ito.JumpFormulaAssembly
import LevyStochCalc.Ito.JumpFormulaDictionary
import LevyStochCalc.Ito.JumpSplitting
import LevyStochCalc.Ito.JumpSumIdentity

/-!
# Reconciling the two drifts of the finite-activity Itô–Lévy formula

Splitting a finite-activity jump diffusion into a continuous Itô part and a pathwise jump sum
replaces the drift `μ` by `μ` minus the compensator `∫_A γ dν` of the jumps, while the pathwise
jump sum contributes the intensity integral of the jump increment `u(x + γ) − u(x)`. The
Itô–Lévy formula instead carries the drift `μ` itself and the compensator-drift integrand
`u(x + γ) − u(x) − ∑ᵢ γᵢ ∂ᵢu`. The two presentations differ by the first-order term
`∑ᵢ ∂ᵢu ∫_A γᵢ dν`, which the compensator subtracted from the drift supplies exactly.

The accumulated jumps taken at the arrival times capped at the horizon are constant in the index
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms. Between consecutive arrival times inside the window that accumulation gains
exactly the jump coefficient carried by the later arrival time and the mark enumerated with it.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.cappedJumpSum` — the jumps accumulated up to the arrival time
  capped at the horizon.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.setIntegral_compensatorDriftIntegrand_eq_sub` — the mark
  integral of the compensator-drift integrand as the jump increment's mark integral minus the
  first-order term.
* `LevyStochCalc.Ito.JumpFormula.setIntegral_firstOrder_add_compensatorDrift` — the drift
  reconciliation over a time window.
* `LevyStochCalc.Ito.JumpFormula.splitDrift_pointwise`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary` — the non-stochastic
  integrands of Itô's formula in the prepended coordinates, taken against the drift with the
  jump compensator subtracted, as the drift integrand minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum` — the Itô–Lévy identity in
  the vocabulary of `driftIntegrand` and `compensatorDriftIntegrand`, from the split-drift
  identity and the jump-sum identity.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSum_succ_eq` — past the horizon the capped jump sum
  no longer moves.
* `LevyStochCalc.Ito.JumpFormula.ae_eq_of_ae_eq_of_le_jumpTime` — an identity holding almost
  everywhere on each event where the chain of arrival times has passed the horizon holds almost
  everywhere.
* `LevyStochCalc.Ito.JumpFormula.jumpSum_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.cappedJumpSum_succ_eq_add_gamma`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_cappedJumpSum_succ` — the jump sum over a
  sub-window as the sum over the enumerated atoms it contains, and the increment of the capped
  jump sum between consecutive arrival times as the jump coefficient at the later arrival time
  and its mark.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section DriftReconciliation

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- The mark integral of the first-order term of the compensator-drift integrand is the gradient
contracted with the mark integrals of the components of the jump coefficient. -/
theorem setIntegral_firstOrder_eq (A : Set E) (s : ℝ) (x : Fin n → ℝ)
    (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν) :
    ∫ e in A, (∑ i : Fin n, γ s x e i * gradient u s x i) ∂ν
      = ∑ i : Fin n, gradient u s x i * ∫ e in A, γ s x e i ∂ν := by
  rw [integral_finsetSum _ fun i _ => (hγ i).mul_const (gradient u s x i)]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const]; ring

/-- The mark integral of the compensator-drift integrand is the mark integral of the jump
increment minus the gradient contracted with the mark integrals of the jump coefficient. -/
theorem setIntegral_compensatorDriftIntegrand_eq_sub (A : Set E) (s : ℝ) (x : Fin n → ℝ)
    (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν)
    (hΔ : IntegrableOn (fun e => u s (x + γ s x e) - u s x) A ν) :
    ∫ e in A, compensatorDriftIntegrand u γ s x e ∂ν
      = (∫ e in A, (u s (x + γ s x e) - u s x) ∂ν)
        - ∑ i : Fin n, gradient u s x i * ∫ e in A, γ s x e i ∂ν := by
  have hfo : IntegrableOn (fun e => ∑ i : Fin n, γ s x e i * gradient u s x i) A ν :=
    integrable_finsetSum _ fun i _ => (hγ i).mul_const _
  simp only [compensatorDriftIntegrand]
  rw [← setIntegral_firstOrder_eq (u := u) A s x hγ, ← integral_sub hΔ hfo]

omit [MeasurableSpace E] in
/-- The compensator-drift integrand vanishes at marks off the carrier of the jump
coefficient. -/
theorem compensatorDriftIntegrand_eq_zero_of_notMem {A : Set E}
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → γ s x e = 0)
    (s : ℝ) (x : Fin n → ℝ) {e : E} (he : e ∉ A) :
    compensatorDriftIntegrand u γ s x e = 0 := by
  simp [compensatorDriftIntegrand, hsupp s x e he]

/-- The compensator-drift integral over the mark space is its integral over the carrier of the
jump coefficient. -/
theorem integral_compensatorDriftIntegrand_eq_setIntegral {A : Set E}
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → γ s x e = 0)
    (s : ℝ) (x : Fin n → ℝ) :
    ∫ e, compensatorDriftIntegrand u γ s x e ∂ν
      = ∫ e in A, compensatorDriftIntegrand u γ s x e ∂ν :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ he =>
    compensatorDriftIntegrand_eq_zero_of_notMem hsupp s x he).symm

/-- Along a path the compensator-drift integral over a time window is the intensity integral of
the jump increment minus the first-order term. -/
theorem setIntegral_compensatorDrift_eq_sub (A : Set E) (x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => u s (x s + γ s (x s) e) - u s (x s)) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, compensatorDriftIntegrand u γ s (x s) e ∂ν)
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν)
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν := by
  rw [← integral_sub hΔt hgt]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  exact setIntegral_compensatorDriftIntegrand_eq_sub A s (x s) (hγ s hs) (hΔ s hs)

/-- **The drift reconciliation.** The first-order term that subtracting the jump compensator
removes from the drift is exactly the gap between the intensity integral of the jump increment
and the compensator-drift integral of the Itô–Lévy formula. -/
theorem setIntegral_firstOrder_add_compensatorDrift (A : Set E) (x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => u s (x s + γ s (x s) e) - u s (x s)) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (x s) i * ∫ e in A, γ s (x s) e i ∂ν)
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, compensatorDriftIntegrand u γ s (x s) e ∂ν
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, (u s (x s + γ s (x s) e) - u s (x s)) ∂ν := by
  have h := setIntegral_compensatorDrift_eq_sub (u := u) (γ := γ) A x T hγ hΔ hΔt hgt
  linarith

end DriftReconciliation

section SplitDrift

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

omit [MeasurableSpace E] ν in
/-- A double sum over the coordinates with a time coordinate prepended, weighted by a diffusion
matrix whose zeroth row vanishes, reduces to the double sum over the original coordinates. -/
theorem sum_succ_succ_of_row_zero (c : Fin (n + 1) → Fin (n + 1) → ℝ)
    (H : Fin (n + 1) → Fin d → ℝ) (h0 : ∀ j : Fin d, H 0 j = 0) :
    (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), c p q * ∑ j : Fin d, H p j * H q j)
      = ∑ p : Fin n, ∑ q : Fin n,
          c p.succ q.succ * ∑ j : Fin d, H p.succ j * H q.succ j := by
  rw [Fin.sum_univ_succ]
  have hzero : (∑ q : Fin (n + 1), c 0 q * ∑ j : Fin d, H 0 j * H q j) = 0 :=
    Finset.sum_eq_zero fun q _ => by simp [h0]
  rw [hzero, zero_add]
  exact Finset.sum_congr rfl fun p _ => by rw [Fin.sum_univ_succ]; simp [h0]

/-- The non-stochastic integrands of Itô's formula in the prepended coordinates, taken against
the drift with the jump compensator subtracted, make up the drift integrand of the Itô–Lévy
formula minus the first-order term of the compensator drift. -/
theorem splitDriftIntegrand_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y : Fin n → ℝ) :
    (coordDeriv f' 0 (Fin.cons s y) * 1
          + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
              * (coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
              * ∑ k : Fin d, coeffs.σ s y p k * coeffs.σ s y q k
      = driftIntegrand u coeffs s y
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s y e i ∂ν := by
  have hdict := driftIntegrand_dictionary (u := u) hfu hf hf' coeffs s y
  have hsplit : (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
        * (coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν))
      = (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s y q)
        - ∑ q : Fin n, gradient u s y q * ∫ e in A, coeffs.γ s y e q ∂ν := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coordDeriv_succ_cons_eq_gradient hfu hf s y q]
    ring
  rw [mul_one, hsplit]
  linarith

/-- The `coordDeriv₂` weights of a diffusion matrix whose zeroth row vanishes are carried by the
original coordinates only. -/
theorem sum_succ_succ_coordDeriv₂_of_row_zero (z : Fin (n + 1) → ℝ)
    (K : Fin (n + 1) → Fin d → ℝ) (h0 : ∀ j : Fin d, K 0 j = 0) :
    (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q z * ∑ j : Fin d, K p j * K q j)
      = ∑ p : Fin n, ∑ q : Fin n,
          coordDeriv₂ f'' p.succ q.succ z * ∑ j : Fin d, K p.succ j * K q.succ j :=
  sum_succ_succ_of_row_zero (fun p q => coordDeriv₂ f'' p q z) K h0

/-- The non-stochastic integrands of Itô's formula at a point of a path split at its jumps: with
a unit time drift, the drift with the jump compensator subtracted and a diffusion matrix whose
time row vanishes, they make up the drift integrand of the Itô–Lévy formula minus the
first-order term of the compensator drift. -/
theorem splitDrift_pointwise (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y : Fin n → ℝ) (b : Fin (n + 1) → ℝ) (K : Fin (n + 1) → Fin d → ℝ) (hb0 : b 0 = 1)
    (hbs : ∀ q : Fin n, b q.succ = coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν)
    (hK0 : ∀ j : Fin d, K 0 j = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d), K p.succ j = coeffs.σ s y p j) :
    (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
            coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j
      = driftIntegrand u coeffs s y
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s y e i ∂ν := by
  have h1 : (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
      = coordDeriv f' 0 (Fin.cons s y) * 1
        + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
            * (coeffs.μ s y q - ∫ e in A, coeffs.γ s y e q ∂ν) := by
    rw [Fin.sum_univ_succ, hb0]
    exact congrArg _ (Finset.sum_congr rfl fun q _ => by rw [hbs q])
  have h2 : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j)
      = ∑ p : Fin n, ∑ q : Fin n, coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
          * ∑ k : Fin d, coeffs.σ s y p k * coeffs.σ s y q k := by
    rw [sum_succ_succ_coordDeriv₂_of_row_zero (Fin.cons s y) K hK0]
    exact Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => by simp only [hKs]
  have h3 := splitDriftIntegrand_dictionary (ν := ν) hfu hf hf' coeffs A s y
  rw [h1, h2]
  linarith

/-- Along a path the non-stochastic terms of Itô's formula in the prepended coordinates, taken
against the drift with the jump compensator subtracted, integrate over a window to the drift
integral of the Itô–Lévy formula minus the first-order term of the compensator drift. -/
theorem setIntegral_splitDrift_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (T : ℝ)
    (x : ℝ → Fin n → ℝ) (b : Fin (n + 1) → ℝ → ℝ) (K : Fin (n + 1) → Fin d → ℝ → ℝ)
    (hb0 : ∀ s : ℝ, b 0 s = 1)
    (hbs : ∀ (q : Fin n) (s : ℝ),
      b q.succ s = coeffs.μ s (x s) q - ∫ e in A, coeffs.γ s (x s) e q ∂ν)
    (hK0 : ∀ (j : Fin d) (s : ℝ), K 0 j s = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d) (s : ℝ), K p.succ j s = coeffs.σ s (x s) p j)
    (hD : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv f' p (Fin.cons s (x s)) * b p s) (Set.Ioc (0 : ℝ) T) volume)
    (hQ : ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (Fin.cons s (x s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume) :
    (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (Fin.cons s (x s)) * b p s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (Fin.cons s (x s))
              * ∑ j : Fin d, K p j s * K q j s ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T,
          (driftIntegrand u coeffs s (x s)
            - ∑ i : Fin n, gradient u s (x s) i
                * ∫ e in A, coeffs.γ s (x s) e i ∂ν) ∂volume := by
  have hQint : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q (Fin.cons s (x s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume :=
    fun p => integrable_finsetSum _ fun q _ => hQ p q
  have hDsum : (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (Fin.cons s (x s)) * b p s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
          (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s (x s)) * b p s) ∂volume :=
    (integral_finsetSum _ fun p _ => hD p).symm
  have hQsum : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (Fin.cons s (x s))
          * ∑ j : Fin d, K p j s * K q j s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T, (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
          coordDeriv₂ f'' p q (Fin.cons s (x s))
            * ∑ j : Fin d, K p j s * K q j s) ∂volume := by
    have hstep : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv₂ f'' p q (Fin.cons s (x s))
            * ∑ j : Fin d, K p j s * K q j s ∂volume)
        = ∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T, (∑ q : Fin (n + 1),
            coordDeriv₂ f'' p q (Fin.cons s (x s))
              * ∑ j : Fin d, K p j s * K q j s) ∂volume :=
      Finset.sum_congr rfl fun p _ => (integral_finsetSum _ fun q _ => hQ p q).symm
    rw [hstep]
    exact (integral_finsetSum _ fun p _ => hQint p).symm
  have hDint : IntegrableOn (fun s => ∑ p : Fin (n + 1),
      coordDeriv f' p (Fin.cons s (x s)) * b p s) (Set.Ioc (0 : ℝ) T) volume :=
    integrable_finsetSum _ fun p _ => hD p
  have hQtot : IntegrableOn (fun s => 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
      coordDeriv₂ f'' p q (Fin.cons s (x s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume :=
    (integrable_finsetSum _ fun p _ => hQint p).const_mul _
  rw [hDsum, hQsum, ← integral_const_mul, ← integral_add hDint hQtot]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  exact splitDrift_pointwise hfu hf hf' coeffs A s (x s) (fun p => b p s)
    (fun p j => K p j s) (hb0 s) (fun q => hbs q s) (fun j => hK0 j s)
    (fun p j => hKs p j s)

end SplitDrift

section Assembly

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E}

/-- **The Itô–Lévy formula in its own vocabulary from the split-drift form.** If along a path the
increment of `u` splits into the drift integral taken against the drift with the jump compensator
subtracted, a diffusion term `Dm` and a jump term `Js`, and if the jump term is a compensated
term `Cm` plus the intensity integral of the jump increment, then the increment of `u` is the
drift integral of `driftIntegrand`, `Dm`, `Cm` and the integral of
`compensatorDriftIntegrand`. -/
theorem itoLevy_of_splitDrift_and_jumpSum {A : Set E} {x : ℝ → Fin n → ℝ} {T : ℝ}
    {Dm Cm Js : ℝ}
    (hsupp : ∀ (s : ℝ) (y : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s y e = 0)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => u s (x s + coeffs.γ s (x s) e) - u s (x s)) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, (u s (x s + coeffs.γ s (x s) e) - u s (x s)) ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => driftIntegrand u coeffs s (x s)) (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (x T) - u 0 (x 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (driftIntegrand u coeffs s (x s)
            - ∑ i : Fin n, gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, (u s (x s + coeffs.γ s (x s) e) - u s (x s)) ∂ν) :
    u T (x T) - u 0 (x 0)
      = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e, compensatorDriftIntegrand u coeffs.γ s (x s) e ∂ν := by
  have hE : (∫ s in Set.Icc (0 : ℝ) T,
        ∫ e, compensatorDriftIntegrand u coeffs.γ s (x s) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T,
          ∫ e in A, compensatorDriftIntegrand u coeffs.γ s (x s) e ∂ν :=
    setIntegral_congr_fun measurableSet_Icc fun s _ =>
      integral_compensatorDriftIntegrand_eq_setIntegral hsupp s (x s)
  have hcancel := setIntegral_firstOrder_add_compensatorDrift (u := u) (γ := coeffs.γ)
    A x T hγ hΔ hΔt hgt
  have hdsplit : (∫ s in Set.Icc (0 : ℝ) T, (driftIntegrand u coeffs s (x s)
        - ∑ i : Fin n, gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
      = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s))
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (x s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν :=
    integral_sub hdt hgt
  rw [hE]
  rw [hdsplit] at hsplit
  rw [hjump] at hsplit
  linarith

end Assembly

section CappedShift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The jumps of a mark set accumulated up to the `k`-th arrival time capped at the horizon. -/
noncomputable def cappedJumpSum (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (A : Set E) (T : ℝ) (k : ℕ) (ω : Ω) : Fin n → ℝ :=
  LevyStochCalc.Ito.JumpSplitting.jumpSum X A
    (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω) ω

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (A : Set E)

/-- The capped jump sum at the zeroth arrival time vanishes. -/
theorem cappedJumpSum_zero {T : ℝ} (hT : 0 ≤ T) (ω : Ω) : cappedJumpSum X A T 0 ω = 0 := by
  funext i
  rw [cappedJumpSum,
    LevyStochCalc.Brownian.Ito.clipTime_eq_zero hT (LevyStochCalc.Poisson.jumpTime_zero N A ω),
    LevyStochCalc.Ito.JumpSplitting.jumpSum_zero]
  rfl

/-- Past the horizon the capped jump sum is the jump sum over the whole window. -/
theorem cappedJumpSum_of_le {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSum X A T k ω = LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω := by
  rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_of_le hk]

/-- Past the horizon the capped jump sum no longer moves with the index. -/
theorem cappedJumpSum_succ_eq {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSum X A T (k + 1) ω = cappedJumpSum X A T k ω := by
  rw [cappedJumpSum_of_le X A hk,
    cappedJumpSum_of_le X A
      (hk.trans (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))]

/-- Past the horizon the telescope's jump term vanishes. -/
theorem jumpTerm_eq_zero_of_le {T : ℝ} {k : ℕ} {ω : Ω} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ)
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    f (y + cappedJumpSum X A T (k + 1) ω) - f (y + cappedJumpSum X A T k ω) = 0 := by
  rw [cappedJumpSum_succ_eq X A hk, sub_self]

/-- The chain of capped shifts reaches the whole jump sum at any index whose arrival time has
passed the horizon, so a path that splits at the horizon is the translated Itô path there. -/
theorem eq_add_cappedJumpSum_of_le {T : ℝ} {m : ℕ} {ω : Ω} {V : ℝ → Ω → Fin n → ℝ}
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω)
    (hsplit : ∀ i : Fin n, X.X T ω i
      = V T ω i + LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω i) (i : Fin n) :
    V T ω i + cappedJumpSum X A T m ω i = X.X T ω i := by
  rw [cappedJumpSum_of_le X A hm, hsplit i]

end CappedShift

section Exhaustion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

/-- Consecutive arrival times increase. -/
theorem jumpTime_le_jumpTime_succ (k : ℕ) (ω : Ω) :
    LevyStochCalc.Poisson.jumpTime N A k ω ≤ LevyStochCalc.Poisson.jumpTime N A (k + 1) ω :=
  LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω

/-- The chain of arrival times starts at the origin. -/
theorem jumpTime_chain_zero (ω : Ω) :
    LevyStochCalc.Poisson.jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ) :=
  LevyStochCalc.Poisson.jumpTime_zero N A ω

/-- The events on which the chain of arrival times has passed the horizon cover almost every
sample point. -/
theorem ae_exists_le_jumpTime (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ,
      ω ∈ {ω' : Ω | ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω'} := by
  filter_upwards [LevyStochCalc.Poisson.ae_jumpTime_chain N A hA hAν T] with ω hω
  exact hω.2

/-- An identity that holds almost everywhere on each event where the chain of arrival times has
passed the horizon holds almost everywhere. -/
theorem ae_eq_of_ae_eq_of_le_jumpTime (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {L R : Ω → ℝ}
    (h : ∀ m : ℕ, ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
      L ω = R ω) :
    L =ᵐ[P] R :=
  LevyStochCalc.Brownian.Ito.ae_eq_of_ae_eq_on_exhausting
    (S := fun m => {ω' : Ω | ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω'})
    (ae_exists_le_jumpTime N A hA hAν T) h

end Exhaustion

section MarkIdentification

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- The jump sum over a sub-window of an enumerated window is the sum of the jump coefficient
over the enumerated atoms whose times lie in the sub-window. -/
theorem jumpSum_eq_sum_atomEnum (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    {t : ℝ} (ht : t ≤ T) (i : Fin n) :
    LevyStochCalc.Ito.JumpSplitting.jumpSum X A t ω i
      = ∑ j : Fin K, if θ j ≤ t then coeffs.γ (θ j) (X.X (θ j) ω) (ε j) i else 0 := by
  classical
  have hmt : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hsub : (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ (Set.Ioc (0 : ℝ) t ×ˢ A) = Set.Ioc (0 : ℝ) t ×ˢ A :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)
  have hind := hsum ((Set.Ioc (0 : ℝ) t ×ˢ A).indicator
    fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
  rw [setIntegral_indicator hmt, hsub] at hind
  simp only [LevyStochCalc.Ito.JumpSplitting.jumpSum]
  rw [hind]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : θ j ≤ t
  · have hmemj : ((θ j, ε j) : ℝ × E) ∈ Set.Ioc (0 : ℝ) t ×ˢ A :=
      Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨(hmem j).1.1, hj⟩, (hmem j).2⟩
    rw [if_pos hj, Set.indicator_of_mem hmemj]
  · have hnot : ((θ j, ε j) : ℝ × E) ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hc =>
      hj (Set.mem_Ioc.mp (Set.mem_prod.mp hc).1).2
    rw [if_neg hj, Set.indicator_of_notMem hnot]

/-- Between consecutive arrival times inside the window the jump sum gains exactly the jump
coefficient carried by the later arrival time and its mark. -/
theorem cappedJumpSum_succ_eq_add_gamma (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hθ : Function.Injective θ)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ}
    (hlt : LevyStochCalc.Poisson.jumpTime N A k ω
      < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω)
    (hle : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)) :
    ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
      cappedJumpSum X A T (k + 1) ω
        = cappedJumpSum X A T k ω + coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  classical
  -- The two arrival times are finite reals `q < r ≤ T`, with `0 ≤ q`.
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    (hle.trans_lt (WithTop.coe_lt_top T)).ne
  have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((r : ℝ) : WithTop ℝ) := by
    rw [hr]; exact hlt.le
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (lt_of_le_of_lt hkle (WithTop.coe_lt_top r)).ne
  have hqr : q < r := by
    have := hlt
    rw [← hq, ← hr] at this
    exact_mod_cast this
  have hrT : r ≤ T := by
    have := hle
    rw [← hr] at this
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ q := by
    have := LevyStochCalc.Poisson.coe_zero_le_jumpTime N A k ω
    rw [← hq] at this
    exact_mod_cast this
  have hqT : q ≤ T := le_of_lt (lt_of_lt_of_le hqr hrT)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt hq0 hqr
  -- The later arrival time is one of the enumerated atom times.
  have hmemr : r ∈ Set.range θ := by
    rw [hrange]
    exact ⟨k + 1, hr.symm, hr0, hrT⟩
  obtain ⟨j₀, hj₀⟩ := hmemr
  refine ⟨j₀, by rw [← hr, hj₀], ?_⟩
  -- The two capped shifts are the jump sums at `r` and at `q`.
  have hck1 : cappedJumpSum X A T (k + 1) ω
      = LevyStochCalc.Ito.JumpSplitting.jumpSum X A r ω := by
    rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, min_eq_right hrT]
  have hck : cappedJumpSum X A T k ω = LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω := by
    rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm, min_eq_right hqT]
  -- Only the atom at the later arrival time enters the increment.
  have hkey : ∀ j : Fin K, j ≠ j₀ → (θ j ≤ r ↔ θ j ≤ q) := by
    intro j hj
    constructor
    · intro hjr
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i, hi, -, -⟩ := hmemj
      rcases le_or_gt i k with hik | hik
      · have := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi, ← hq] at this
        exact_mod_cast this
      · have := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi, ← hr] at this
        have hrj : r ≤ θ j := by exact_mod_cast this
        exact absurd (hθ (hj₀.trans (le_antisymm hrj hjr))).symm hj
    · intro hjq
      exact le_of_lt (lt_of_le_of_lt hjq hqr)
  funext i
  have h1 := jumpSum_eq_sum_atomEnum X hA hmem hsum hrT i
  have h2 := jumpSum_eq_sum_atomEnum X hA hmem hsum hqT i
  have hdiff : LevyStochCalc.Ito.JumpSplitting.jumpSum X A r ω i
      - LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω i
      = coeffs.γ (θ j₀) (X.X (θ j₀) ω) (ε j₀) i := by
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine (Finset.sum_eq_single j₀ ?_ ?_).trans ?_
    · intro j _ hj
      by_cases hjr : θ j ≤ r
      · rw [if_pos hjr, if_pos ((hkey j hj).mp hjr), sub_self]
      · rw [if_neg hjr, if_neg (fun hc => hjr ((hkey j hj).mpr hc)), sub_self]
    · intro hj
      exact absurd (Finset.mem_univ j₀) hj
    · rw [if_pos (le_of_eq hj₀), if_neg (by rw [hj₀]; exact not_le.mpr hqr), sub_zero]
  rw [hck1, hck]
  simp only [Pi.add_apply]
  linarith

/-- The jump sum over the whole enumerated window is the sum of the jump coefficient over the
enumerated atoms. -/
theorem jumpSum_eq_sum_atomEnum_horizon (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) :
    LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω
      = ∑ j : Fin K, coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  classical
  funext i
  rw [Finset.sum_apply, jumpSum_eq_sum_atomEnum X hA hmem hsum le_rfl i]
  exact Finset.sum_congr rfl fun j _ => if_pos (hmem j).1.2

end MarkIdentification

section MarkIdentificationAe

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- **The atoms of the window carry the increments of the capped jump sum.** Almost surely the
window of finite intensity carries a strictly increasing enumeration of its atoms which computes
every integral over the window, whose values sum to the jump sum over the window, and along
which the capped jump sum gains, between consecutive arrival times inside the window, exactly
the jump coefficient evaluated at the later arrival time and its mark. -/
theorem ae_exists_atomEnum_cappedJumpSum_succ
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω
        = ∑ j : Fin K, coeffs.γ (θ j) (X.X (θ j) ω) (ε j) ∧
      ∀ k : ℕ, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ) →
        ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
          cappedJumpSum X A T (k + 1) ω
            = cappedJumpSum X A T k ω + coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  filter_upwards [LevyStochCalc.Poisson.ae_exists_atomEnum_integral_eq_sum N A hA hAν T,
    LevyStochCalc.Poisson.ae_jumpTime_lt_jumpTime_succ N A hA hAν T] with ω hω hstrict
  obtain ⟨K, θ, ε, hmono, hrange, hmem, hsum⟩ := hω
  refine ⟨K, θ, ε, hmono, hmem, hsum,
    jumpSum_eq_sum_atomEnum_horizon X hA hmem hsum, fun k hk => ?_⟩
  exact cappedJumpSum_succ_eq_add_gamma X hA hmem hsum hmono.injective hrange
    (hstrict k hk) hk

end MarkIdentificationAe

end LevyStochCalc.Ito.JumpFormula
