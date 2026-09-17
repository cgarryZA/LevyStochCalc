/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.ChaosStep
import LevyStochCalc.Probability.CharlierGenerating
import LevyStochCalc.Probability.L2Series

/-!
# The exponential vector of a Poisson region and its chaos expansion

For a Poisson random measure `N` with reference intensity `ν̂` and a region `B` of finite
intensity `λ = ν̂(B)`, the exponential vector at the jump mode `γ` is
`V = e^(-λ γ) (1 + γ) ^ N(B)`, and the degree-`s` Poisson chaos element of `B` scaled by
`γ ^ s / s!` is `C_s = (γ ^ s / s!) C_s(N(B); λ)`. The count `N(B)` is an extended nonnegative
real, so the exponent of the closed form is taken as its floor; the Charlier generating function
is stated at a natural argument, so the identity `∑_s C_s = V` holds on the almost sure event on
which `N(B)` is the value of a natural number, and there the floor is that natural number. The
exceptional set depends on the region.

The chaos elements are square integrable with `E‖C_s‖ ^ 2 = (‖γ‖ ^ 2 λ) ^ s / s!`, so their `L²`
norms are summable, and the series converges in `L²(P)`: absolute summability of the `L²` norms
gives a limit in `L²`, and that limit is identified with the almost everywhere pointwise sum
through convergence in measure. Square integrability of `V` is a consequence of that
identification rather than a hypothesis; for `‖1 + γ‖ > 1` the exponential vector is unbounded.

Only a single mark set enters: the chaos elements are polynomials of the one count `N(B)`, with
no mark profile beyond the indicator of the region, and `γ` is a free complex parameter. Nothing
here identifies `V` with a random variable of any model, nor the elements `C_s` with components
of an increment of any process.

## Main definitions

* `LevyStochCalc.Poisson.pointCount` — the number of points of `N` in the region `B`.
* `LevyStochCalc.Poisson.poissonExpVector` — the exponential vector `e^(-λ γ) (1 + γ) ^ N(B)`.
* `LevyStochCalc.Poisson.poissonChaosStepC` — the scaled chaos element `(γ ^ s / s!) C_s(N(B); λ)`.

## Main statements

* `LevyStochCalc.Poisson.integral_norm_sq_poissonChaosStepC_div` —
  `E‖C_s‖ ^ 2 = (‖γ‖ ^ 2 λ) ^ s / s!`.
* `LevyStochCalc.Poisson.hasSum_poissonChaosStepC` — `∑_s C_s = V` almost everywhere.
* `LevyStochCalc.Poisson.summable_norm_poissonChaosStepC` — the chaos elements are almost
  everywhere absolutely summable.
* `LevyStochCalc.Poisson.memLp_two_poissonExpVector` — the exponential vector lies in `L²`.
* `LevyStochCalc.Poisson.hasSum_toLp_poissonChaosStepC` — the series converges in `L²(P)` to the
  exponential vector.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Poisson

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The number of points of `N` in the region `B`. -/
noncomputable def pointCount (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) : ℕ :=
  ⌊(N.N ω B).toReal⌋₊

/-- The exponential vector of the region `B` at the jump mode `γ`,
`e ^ (-λ γ) (1 + γ) ^ N(B)` for the rate `λ = ν̂(B)`. -/
noncomputable def poissonExpVector (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (γ : ℂ)
    (ω : Ω) : ℂ :=
  Complex.exp (-((referenceIntensity ν B).toReal * γ)) * (1 + γ) ^ pointCount N B ω

/-- The degree-`s` Poisson chaos element of `B` scaled by `γ ^ s / s !`. -/
noncomputable def poissonChaosStepC (N : PoissonRandomMeasure P ν) (s : ℕ) (B : Set (ℝ × E))
    (γ : ℂ) (ω : Ω) : ℂ :=
  γ ^ s / (s.factorial : ℂ) * (poissonChaosStep N s B ω : ℂ)

/-- A scaled Poisson chaos element of a region of finite intensity lies in `L²`. -/
theorem memLp_two_poissonChaosStepC (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (γ : ℂ) (s : ℕ) :
    MemLp (fun ω => poissonChaosStepC N s B γ ω) 2 P :=
  ((memLp_two_poissonChaosStep N hB hfin s).ofReal).const_mul _

/-- The second moment of the modulus of a scaled Poisson chaos element of a region of finite
intensity, `(‖γ‖ ^ 2 λ) ^ s / s !` for the rate `λ = ν̂(B)`. -/
theorem integral_norm_sq_poissonChaosStepC_div (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (γ : ℂ) (s : ℕ) :
    ∫ ω, ‖poissonChaosStepC N s B γ ω‖ ^ 2 ∂P
      = (‖γ‖ ^ 2 * (referenceIntensity ν B).toReal) ^ s / (s.factorial : ℝ) := by
  have hpt : ∀ ω : Ω, ‖poissonChaosStepC N s B γ ω‖ ^ 2
      = (1 / ((s.factorial : ℝ) ^ 2)) * ‖γ ^ s * (poissonChaosStep N s B ω : ℂ)‖ ^ 2 := by
    intro ω
    rw [poissonChaosStepC, show γ ^ s / (s.factorial : ℂ) * (poissonChaosStep N s B ω : ℂ)
        = ((s.factorial : ℂ))⁻¹ * (γ ^ s * (poissonChaosStep N s B ω : ℂ)) by ring,
      norm_mul, mul_pow, norm_inv, Complex.norm_natCast]
    rw [one_div]
    congr 1
    rw [inv_pow]
  rw [show (fun ω => ‖poissonChaosStepC N s B γ ω‖ ^ 2)
      = fun ω => (1 / ((s.factorial : ℝ) ^ 2))
        * ‖γ ^ s * (poissonChaosStep N s B ω : ℂ)‖ ^ 2 from funext hpt,
    integral_const_mul, integral_norm_sq_poissonChaosStepC N hB hfin γ s]
  have hs : (0 : ℝ) < (s.factorial : ℝ) := by positivity
  rw [mul_pow, ← pow_mul, mul_comm 2 s, pow_mul]
  field_simp

/-- The scaled Poisson chaos elements of a region of finite intensity sum almost everywhere to
its exponential vector. -/
theorem hasSum_poissonChaosStepC (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (γ : ℂ) :
    ∀ᵐ ω ∂P, HasSum (fun s : ℕ => poissonChaosStepC N s B γ ω) (poissonExpVector N B γ ω) := by
  filter_upwards [N.integer_valued hB hfin] with ω hω
  obtain ⟨n, hn⟩ := hω
  have hreal : (N.N ω B).toReal = (n : ℝ) := by rw [hn]; simp
  have hcount : pointCount N B ω = n := by rw [pointCount, hreal, Nat.floor_natCast]
  have h := hasSum_charlierScaled (referenceIntensity ν B).toReal n γ
  rw [poissonExpVector, hcount]
  refine h.congr_fun fun s => ?_
  rw [poissonChaosStepC, poissonChaosStep, hreal]

/-- The scaled Poisson chaos elements of a region of finite intensity are almost everywhere
absolutely summable. -/
theorem summable_norm_poissonChaosStepC (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (γ : ℂ) :
    ∀ᵐ ω ∂P, Summable fun s : ℕ => ‖poissonChaosStepC N s B γ ω‖ := by
  filter_upwards [N.integer_valued hB hfin] with ω hω
  obtain ⟨n, hn⟩ := hω
  have hreal : (N.N ω B).toReal = (n : ℝ) := by rw [hn]; simp
  refine (summable_norm_charlierScaled (referenceIntensity ν B).toReal n γ).congr fun s => ?_
  rw [poissonChaosStepC, poissonChaosStep, hreal]

/-- The `L²` norms of the scaled Poisson chaos elements of a region of finite intensity are
summable. -/
theorem summable_sqrt_integral_norm_sq_poissonChaosStepC (N : PoissonRandomMeasure P ν)
    {B : Set (ℝ × E)} (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (γ : ℂ) :
    Summable fun s : ℕ => Real.sqrt (∫ ω, ‖poissonChaosStepC N s B γ ω‖ ^ 2 ∂P) := by
  refine Summable.congr (summable_sqrt_pow_div_factorial
    (x := ‖γ‖ ^ 2 * (referenceIntensity ν B).toReal)
    (by positivity)) fun s => ?_
  rw [integral_norm_sq_poissonChaosStepC_div N hB hfin γ s]

/-- The exponential vector of a region of finite intensity lies in `L²`. -/
theorem memLp_two_poissonExpVector (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (γ : ℂ) :
    MemLp (poissonExpVector N B γ) 2 P :=
  memLp_two_of_hasSum_ae (fun s => memLp_two_poissonChaosStepC N hB hfin γ s)
    (summable_sqrt_integral_norm_sq_poissonChaosStepC N hB hfin γ)
    (hasSum_poissonChaosStepC N hB hfin γ)

/-- The scaled Poisson chaos elements of a region of finite intensity sum in `L²(P)` to its
exponential vector. -/
theorem hasSum_toLp_poissonChaosStepC (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (γ : ℂ) :
    HasSum (fun s : ℕ => (memLp_two_poissonChaosStepC N hB hfin γ s).toLp
        (fun ω => poissonChaosStepC N s B γ ω))
      ((memLp_two_poissonExpVector N hB hfin γ).toLp (poissonExpVector N B γ)) :=
  hasSum_toLp_of_summable_norm _ _
    (summable_sqrt_integral_norm_sq_poissonChaosStepC N hB hfin γ)
    (hasSum_poissonChaosStepC N hB hfin γ)

end LevyStochCalc.Poisson
