/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaFiniteActivity
import LevyStochCalc.Ito.JumpFormulaMixed

/-!
# The split-drift dictionary for the mixed integrands

Splitting a finite-activity jump diffusion into a continuous Itô part and a pathwise jump sum
replaces the drift `μ` by `μ` minus the compensator `∫_A γ dν` of the jumps, while the pathwise
jump sum contributes the intensity integral of the jump increment. Read with the derivatives of
the state function at a state `y` and the coefficients at a state `x`, the two presentations of
the drift differ by the first-order term `∑ᵢ ∂ᵢu(s, y) ∫_A γᵢ(s, x) dν`, which the compensator
subtracted from the drift supplies exactly.

The statements below are the mixed forms of the drift reconciliation, of the split-drift
dictionary in the coordinates with a time coordinate prepended, and of the Itô–Lévy identity
assembled from them; the assembled identity carries the compensator-drift term over the mark set
carrying the jump coefficient. At `y = x` they are the statements of
`LevyStochCalc.Ito.JumpFormulaFiniteActivity`.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedFirstOrder_eq`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDriftIntegrand_eq_sub` — the mark
  integral of the mixed compensator-drift integrand as the mark integral of the mixed jump
  increment minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.setIntegral_mixedCompensatorDrift_eq_sub`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_firstOrder_add_mixedCompensatorDrift` — the drift
  reconciliation over a time window for the mixed integrands.
* `LevyStochCalc.Ito.JumpFormula.mixedDriftIntegrand_dictionary`,
  `LevyStochCalc.Ito.JumpFormula.splitDriftIntegrand_dictionary_mixed` — the non-stochastic
  integrands of Itô's formula in the prepended coordinates, with the derivatives at one state
  and the coefficients at another, as the mixed drift integrand and as the mixed drift integrand
  minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.splitDrift_pointwise_mixed`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary_mixed` — the same taken
  against a unit time drift, the drift with the jump compensator subtracted and a diffusion
  matrix whose time row vanishes, pointwise and integrated over a window.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed`,
  `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_of_support` — the
  Itô–Lévy identity for the mixed integrands from the split-drift identity and the jump-sum
  identity, with the compensator-drift term over the mark set and, for a jump coefficient
  carried by that set, over the whole mark space.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe v

section MixedDriftReconciliation

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- The mark integral of the first-order term of the mixed compensator-drift integrand is the
gradient at one state contracted with the mark integrals of the components of the jump
coefficient at the other. -/
theorem setIntegral_mixedFirstOrder_eq (A : Set E) (s : ℝ) (y x : Fin n → ℝ)
    (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν) :
    ∫ e in A, (∑ i : Fin n, γ s x e i * gradient u s y i) ∂ν
      = ∑ i : Fin n, gradient u s y i * ∫ e in A, γ s x e i ∂ν := by
  rw [integral_finsetSum _ fun i _ => (hγ i).mul_const (gradient u s y i)]
  exact Finset.sum_congr rfl fun i _ => by rw [integral_mul_const]; ring

/-- The mark integral of the mixed compensator-drift integrand is the mark integral of the mixed
jump increment minus the gradient contracted with the mark integrals of the jump coefficient. -/
theorem setIntegral_mixedCompensatorDriftIntegrand_eq_sub (A : Set E) (s : ℝ)
    (y x : Fin n → ℝ) (hγ : ∀ i : Fin n, IntegrableOn (fun e => γ s x e i) A ν)
    (hΔ : IntegrableOn (fun e => mixedJumpIncrement u γ s y x e) A ν) :
    ∫ e in A, mixedCompensatorDriftIntegrand u γ s y x e ∂ν
      = (∫ e in A, mixedJumpIncrement u γ s y x e ∂ν)
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, γ s x e i ∂ν := by
  have hfo : IntegrableOn (fun e => ∑ i : Fin n, γ s x e i * gradient u s y i) A ν :=
    integrable_finsetSum _ fun i _ => (hγ i).mul_const _
  simp only [mixedCompensatorDriftIntegrand, mixedJumpIncrement] at hΔ ⊢
  rw [← setIntegral_mixedFirstOrder_eq (u := u) A s y x hγ, ← integral_sub hΔ hfo]

omit [MeasurableSpace E] in
/-- The mixed compensator-drift integrand vanishes at marks off the carrier of the jump
coefficient. -/
theorem mixedCompensatorDriftIntegrand_eq_zero_of_notMem {A : Set E}
    (hsupp : ∀ (s : ℝ) (z : Fin n → ℝ) (e : E), e ∉ A → γ s z e = 0)
    (s : ℝ) (y x : Fin n → ℝ) {e : E} (he : e ∉ A) :
    mixedCompensatorDriftIntegrand u γ s y x e = 0 := by
  simp [mixedCompensatorDriftIntegrand, hsupp s x e he]

/-- The mixed compensator-drift integral over the mark space is its integral over the carrier of
the jump coefficient. -/
theorem integral_mixedCompensatorDriftIntegrand_eq_setIntegral {A : Set E}
    (hsupp : ∀ (s : ℝ) (z : Fin n → ℝ) (e : E), e ∉ A → γ s z e = 0)
    (s : ℝ) (y x : Fin n → ℝ) :
    ∫ e, mixedCompensatorDriftIntegrand u γ s y x e ∂ν
      = ∫ e in A, mixedCompensatorDriftIntegrand u γ s y x e ∂ν :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun _ he =>
    mixedCompensatorDriftIntegrand_eq_zero_of_notMem hsupp s y x he).symm

/-- Along a pair of paths the mixed compensator-drift integral over a time window is the
intensity integral of the mixed jump increment minus the first-order term. -/
theorem setIntegral_mixedCompensatorDrift_eq_sub (A : Set E) (y x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν)
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν := by
  rw [← integral_sub hΔt hgt]
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  exact setIntegral_mixedCompensatorDriftIntegrand_eq_sub A s (y s) (x s) (hγ s hs) (hΔ s hs)

/-- **The drift reconciliation for the mixed integrands.** The first-order term that subtracting
the jump compensator removes from the drift is exactly the gap between the intensity integral of
the mixed jump increment and the mixed compensator-drift integral. -/
theorem setIntegral_firstOrder_add_mixedCompensatorDrift (A : Set E) (y x : ℝ → Fin n → ℝ)
    (T : ℝ)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν)
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν := by
  have h := setIntegral_mixedCompensatorDrift_eq_sub (u := u) (γ := γ) A y x T hγ hΔ hΔt hgt
  linarith

end MixedDriftReconciliation

section MixedSplitDrift

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

omit [MeasurableSpace E] in
/-- The three non-stochastic terms of Itô's formula in the prepended coordinates, with the
derivatives of the representative at one state and the coefficients at another, make up the
mixed drift integrand. -/
theorem mixedDriftIntegrand_dictionary (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (s : ℝ)
    (y x : Fin n → ℝ) :
    coordDeriv f' 0 (Fin.cons s y)
        + (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s x q)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
              * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k
      = mixedDriftIntegrand u coeffs s y x := by
  have h1 : (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s x q)
      = ∑ i : Fin n, coeffs.μ s x i * gradient u s y i :=
    Finset.sum_congr rfl fun q _ => by
      rw [coordDeriv_succ_cons_eq_gradient hfu hf s y q, mul_comm]
  have h2 : (∑ p : Fin n, ∑ q : Fin n, coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
        * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k)
      = ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin d,
          coeffs.σ s x i k * coeffs.σ s x j k * hessian u s y i j := by
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    rw [coordDeriv₂_succ_succ_cons_eq_hessian hfu hf hf' s y p q, ← Finset.sum_mul]
    ring
  simp only [mixedDriftIntegrand]
  rw [coordDeriv_zero_cons_eq_timeDeriv hfu hf s y, h1, h2]
  ring

/-- The non-stochastic integrands of Itô's formula in the prepended coordinates, with the
derivatives of the representative at one state and the coefficients at another, taken against
the drift with the jump compensator subtracted, make up the mixed drift integrand minus the
first-order term of the mixed compensator drift. -/
theorem splitDriftIntegrand_dictionary_mixed (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y x : Fin n → ℝ) :
    (coordDeriv f' 0 (Fin.cons s y) * 1
          + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
              * (coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν))
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n,
            coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
              * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k
      = mixedDriftIntegrand u coeffs s y x
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s x e i ∂ν := by
  have hdict := mixedDriftIntegrand_dictionary (u := u) hfu hf hf' coeffs s y x
  have hsplit : (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
        * (coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν))
      = (∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y) * coeffs.μ s x q)
        - ∑ q : Fin n, gradient u s y q * ∫ e in A, coeffs.γ s x e q ∂ν := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [coordDeriv_succ_cons_eq_gradient hfu hf s y q]
    ring
  rw [mul_one, hsplit]
  linarith

/-- The non-stochastic integrands of Itô's formula at a pair of states, with the derivatives of
the representative at one and the coefficients at the other: with a unit time drift, the drift
with the jump compensator subtracted and a diffusion matrix whose time row vanishes, they make
up the mixed drift integrand minus the first-order term of the mixed compensator drift. -/
theorem splitDrift_pointwise_mixed (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (s : ℝ)
    (y x : Fin n → ℝ) (b : Fin (n + 1) → ℝ) (K : Fin (n + 1) → Fin d → ℝ) (hb0 : b 0 = 1)
    (hbs : ∀ q : Fin n, b q.succ = coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν)
    (hK0 : ∀ j : Fin d, K 0 j = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d), K p.succ j = coeffs.σ s x p j) :
    (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
            coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j
      = mixedDriftIntegrand u coeffs s y x
        - ∑ i : Fin n, gradient u s y i * ∫ e in A, coeffs.γ s x e i ∂ν := by
  have h1 : (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s y) * b p)
      = coordDeriv f' 0 (Fin.cons s y) * 1
        + ∑ q : Fin n, coordDeriv f' q.succ (Fin.cons s y)
            * (coeffs.μ s x q - ∫ e in A, coeffs.γ s x e q ∂ν) := by
    rw [Fin.sum_univ_succ, hb0]
    exact congrArg _ (Finset.sum_congr rfl fun q _ => by rw [hbs q])
  have h2 : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q (Fin.cons s y) * ∑ j : Fin d, K p j * K q j)
      = ∑ p : Fin n, ∑ q : Fin n, coordDeriv₂ f'' p.succ q.succ (Fin.cons s y)
          * ∑ k : Fin d, coeffs.σ s x p k * coeffs.σ s x q k := by
    rw [sum_succ_succ_coordDeriv₂_of_row_zero (Fin.cons s y) K hK0]
    exact Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun q _ => by simp only [hKs]
  have h3 := splitDriftIntegrand_dictionary_mixed (ν := ν) hfu hf hf' coeffs A s y x
  rw [h1, h2]
  linarith

/-- Along a pair of paths the non-stochastic terms of Itô's formula in the prepended
coordinates, with the derivatives of the representative along one path and the coefficients
along the other, taken against the drift with the jump compensator subtracted, integrate over a
window to the mixed drift integral minus the first-order term of the mixed compensator drift. -/
theorem setIntegral_splitDrift_dictionary_mixed (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E) (A : Set E) (T : ℝ)
    (y x : ℝ → Fin n → ℝ) (b : Fin (n + 1) → ℝ → ℝ) (K : Fin (n + 1) → Fin d → ℝ → ℝ)
    (hb0 : ∀ s : ℝ, b 0 s = 1)
    (hbs : ∀ (q : Fin n) (s : ℝ),
      b q.succ s = coeffs.μ s (x s) q - ∫ e in A, coeffs.γ s (x s) e q ∂ν)
    (hK0 : ∀ (j : Fin d) (s : ℝ), K 0 j s = 0)
    (hKs : ∀ (p : Fin n) (j : Fin d) (s : ℝ), K p.succ j s = coeffs.σ s (x s) p j)
    (hD : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv f' p (Fin.cons s (y s)) * b p s) (Set.Ioc (0 : ℝ) T) volume)
    (hQ : ∀ p q : Fin (n + 1), IntegrableOn
      (fun s => coordDeriv₂ f'' p q (Fin.cons s (y s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume) :
    (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (Fin.cons s (y s)) * b p s ∂volume)
        + 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (Fin.cons s (y s))
              * ∑ j : Fin d, K p j s * K q j s ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T,
          (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i
                * ∫ e in A, coeffs.γ s (x s) e i ∂ν) ∂volume := by
  have hQint : ∀ p : Fin (n + 1), IntegrableOn
      (fun s => ∑ q : Fin (n + 1),
        coordDeriv₂ f'' p q (Fin.cons s (y s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume :=
    fun p => integrable_finsetSum _ fun q _ => hQ p q
  have hDsum : (∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (Fin.cons s (y s)) * b p s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
          (∑ p : Fin (n + 1), coordDeriv f' p (Fin.cons s (y s)) * b p s) ∂volume :=
    (integral_finsetSum _ fun p _ => hD p).symm
  have hQsum : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (Fin.cons s (y s))
          * ∑ j : Fin d, K p j s * K q j s ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T, (∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
          coordDeriv₂ f'' p q (Fin.cons s (y s))
            * ∑ j : Fin d, K p j s * K q j s) ∂volume := by
    have hstep : (∑ p : Fin (n + 1), ∑ q : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv₂ f'' p q (Fin.cons s (y s))
            * ∑ j : Fin d, K p j s * K q j s ∂volume)
        = ∑ p : Fin (n + 1), ∫ s in Set.Ioc (0 : ℝ) T, (∑ q : Fin (n + 1),
            coordDeriv₂ f'' p q (Fin.cons s (y s))
              * ∑ j : Fin d, K p j s * K q j s) ∂volume :=
      Finset.sum_congr rfl fun p _ => (integral_finsetSum _ fun q _ => hQ p q).symm
    rw [hstep]
    exact (integral_finsetSum _ fun p _ => hQint p).symm
  have hDint : IntegrableOn (fun s => ∑ p : Fin (n + 1),
      coordDeriv f' p (Fin.cons s (y s)) * b p s) (Set.Ioc (0 : ℝ) T) volume :=
    integrable_finsetSum _ fun p _ => hD p
  have hQtot : IntegrableOn (fun s => 1 / 2 * ∑ p : Fin (n + 1), ∑ q : Fin (n + 1),
      coordDeriv₂ f'' p q (Fin.cons s (y s)) * ∑ j : Fin d, K p j s * K q j s)
      (Set.Ioc (0 : ℝ) T) volume :=
    (integrable_finsetSum _ fun p _ => hQint p).const_mul _
  rw [hDsum, hQsum, ← integral_const_mul, ← integral_add hDint hQtot]
  refine setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
  exact splitDrift_pointwise_mixed hfu hf hf' coeffs A s (y s) (x s) (fun p => b p s)
    (fun p j => K p j s) (hb0 s) (fun q => hbs q s) (fun j => hK0 j s)
    (fun p j => hKs p j s)

end MixedSplitDrift

section MixedAssembly

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E}

/-- **The Itô–Lévy formula for the mixed integrands from the split-drift form.** If along a pair
of paths the increment of `u` splits into the mixed drift integral taken against the drift with
the jump compensator subtracted, a diffusion term `Dm` and a jump term `Js`, and if the jump term
is a compensated term `Cm` plus the intensity integral of the mixed jump increment over a mark
set, then the increment of `u` is the mixed drift integral, `Dm`, `Cm` and the integral of the
mixed compensator-drift integrand over that mark set. -/
theorem itoLevy_of_splitDrift_and_jumpSum_mixed {A : Set E} {y x : ℝ → Fin n → ℝ} {T : ℝ}
    {Dm Cm Js : ℝ}
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn
      (fun s => ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s) (x s))
      (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν) :
    u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν := by
  have hcancel := setIntegral_firstOrder_add_mixedCompensatorDrift (u := u) (γ := coeffs.γ)
    A y x T hγ hΔ hΔt hgt
  have hdsplit : (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
        - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s))
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν :=
    integral_sub hdt hgt
  rw [hdsplit] at hsplit
  rw [hjump] at hsplit
  linarith

/-- The Itô–Lévy formula for the mixed integrands with the compensator-drift term over the whole
mark space, for a jump coefficient carried by the mark set of the jump term. -/
theorem itoLevy_of_splitDrift_and_jumpSum_mixed_of_support {A : Set E} {y x : ℝ → Fin n → ℝ}
    {T : ℝ} {Dm Cm Js : ℝ}
    (hsupp : ∀ (s : ℝ) (z : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s z e = 0)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn
      (fun s => ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s) (x s))
      (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν) :
    u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν := by
  have hE : (∫ s in Set.Icc (0 : ℝ) T,
        ∫ e, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T,
          ∫ e in A, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν :=
    setIntegral_congr_fun measurableSet_Icc fun s _ =>
      integral_mixedCompensatorDriftIntegrand_eq_setIntegral hsupp s (y s) (x s)
  rw [hE]
  exact itoLevy_of_splitDrift_and_jumpSum_mixed hγ hΔ hΔt hgt hdt hsplit hjump

end MixedAssembly

end LevyStochCalc.Ito.JumpFormula
