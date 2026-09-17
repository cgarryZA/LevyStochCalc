/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.RandomMeasure
import LevyStochCalc.Probability.Charlier

/-!
# The Poisson chaos element of one strip at the mark-constant level

For a Poisson random measure `N` with reference intensity `ν̂ = volume.restrict [0, ∞) ⊗ ν` and a
region `B` of finite intensity, `poissonChaosStep N n B` is the Charlier polynomial of degree `n`
and rate `λ = ν̂(B)` evaluated at the count `N(B)`. On the strip `B = (a, b] ×ˢ A` the rate is
`(b - a) ν(A)`, the degree-one element is the compensated count `Ñ(B)` and the degree-two element
is `Ñ(B) ^ 2 - N(B)`. Under `P` the elements of positive degree are centred and the family is
orthogonal, with `E[C_n C_m] = δ_(n m) n! λ ^ n`; both come from the Charlier orthogonality under
a Poisson law, transferred along the law of the count.

Only a single mark set is covered: these are polynomials of the one count `N(B)`, with no mark
profile beyond the indicator of `A`, so the rate enters only through `ν̂(B)`.

## Main statements

* `LevyStochCalc.Poisson.poissonChaosStep_one` — the degree-one element is `Ñ(B)`.
* `LevyStochCalc.Poisson.poissonChaosStep_two` — the degree-two element is `Ñ(B) ^ 2 - N(B)`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_mul` — `E[C_n C_m] = δ_(n m) n! λ ^ n`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_eq_zero` — `E[C_n] = 0` for `n ≠ 0`.
* `LevyStochCalc.Poisson.integral_poissonChaosStep_strip_mul` — the same on a strip `(a, b] ×ˢ A`,
  with rate `(b - a) ν(A)`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Nat

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The degree-`n` element of the Poisson chaos of the region `B`: the Charlier polynomial of
degree `n` and rate `ν̂(B)`, evaluated at the count `N(B)`. -/
noncomputable def poissonChaosStep (N : PoissonRandomMeasure P ν) (n : ℕ) (B : Set (ℝ × E))
    (ω : Ω) : ℝ :=
  Probability.charlierScaled n (referenceIntensity ν B).toReal (N.N ω B).toReal

@[simp] theorem poissonChaosStep_zero (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) :
    poissonChaosStep N 0 B ω = 1 := by
  simp [poissonChaosStep]

/-- The degree-one element of the Poisson chaos of `B` is the compensated count `Ñ(B)`. -/
@[simp] theorem poissonChaosStep_one (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) :
    poissonChaosStep N 1 B ω = N.compensated B ω := by
  simp [poissonChaosStep, PoissonRandomMeasure.compensated]

/-- The degree-two element of the Poisson chaos of `B` is `Ñ(B) ^ 2 - N(B)`. -/
theorem poissonChaosStep_two (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) :
    poissonChaosStep N 2 B ω = N.compensated B ω ^ 2 - (N.N ω B).toReal := by
  simp [poissonChaosStep, Probability.charlierScaled_two, PoissonRandomMeasure.compensated]

theorem measurable_poissonChaosStep (N : PoissonRandomMeasure P ν) (n : ℕ) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) : Measurable (poissonChaosStep N n B) :=
  (((Probability.continuous_charlierScaled n _).measurable).comp
      ENNReal.measurable_toReal).comp (N.measurable_eval hB)

/-- Transfer of an integral of a function of the count along the Poisson law of that count. -/
private lemma integral_comp_count (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) {g : ℝ → ℝ} (hg : Measurable g) :
    ∫ ω, g (N.N ω B).toReal ∂P
      = ∫ k : ℕ, g (k : ℝ) ∂poissonMeasure (referenceIntensity ν B).toNNReal := by
  have hmeas : Measurable (fun ω => N.N ω B) := N.measurable_eval hB
  have hcomp : Measurable (fun x : ℝ≥0∞ => g x.toReal) := hg.comp ENNReal.measurable_toReal
  rw [show (∫ ω, g (N.N ω B).toReal ∂P) = ∫ x, g x.toReal ∂(P.map (fun ω => N.N ω B)) from
    (integral_map hmeas.aemeasurable hcomp.aestronglyMeasurable).symm, N.poisson_law hB hfin]
  change ∫ x, g x.toReal
      ∂((poissonMeasure (referenceIntensity ν B).toNNReal).map (fun k : ℕ => (k : ℝ≥0∞))) = _
  rw [integral_map measurable_from_nat.aemeasurable hcomp.aestronglyMeasurable]
  simp

/-- The Poisson chaos elements of a region of finite intensity are orthogonal under `P`, with
`E[C_n C_m] = δ_(n m) n! λ ^ n` for the rate `λ = ν̂(B)`. -/
theorem integral_poissonChaosStep_mul (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (n m : ℕ) :
    ∫ ω, poissonChaosStep N n B ω * poissonChaosStep N m B ω ∂P
      = if n = m then (n.factorial : ℝ) * (referenceIntensity ν B).toReal ^ n else 0 := by
  have hr : (((referenceIntensity ν B).toNNReal : ℝ≥0) : ℝ) = (referenceIntensity ν B).toReal :=
    ENNReal.coe_toNNReal_eq_toReal _
  have hcont : Continuous fun x : ℝ =>
      Probability.charlierScaled n (referenceIntensity ν B).toReal x
        * Probability.charlierScaled m (referenceIntensity ν B).toReal x :=
    (Probability.continuous_charlierScaled n _).mul (Probability.continuous_charlierScaled m _)
  rw [show (fun ω => poissonChaosStep N n B ω * poissonChaosStep N m B ω)
      = fun ω => (fun x : ℝ => Probability.charlierScaled n (referenceIntensity ν B).toReal x
          * Probability.charlierScaled m (referenceIntensity ν B).toReal x) (N.N ω B).toReal from
    rfl]
  rw [integral_comp_count N hB hfin hcont.measurable, ← hr]
  exact Probability.integral_charlierPoly_mul (referenceIntensity ν B).toNNReal n m

/-- The Poisson chaos elements of positive degree of a region of finite intensity are centred
under `P`. -/
theorem integral_poissonChaosStep_eq_zero (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, poissonChaosStep N n B ω ∂P = 0 := by
  have hr : (((referenceIntensity ν B).toNNReal : ℝ≥0) : ℝ) = (referenceIntensity ν B).toReal :=
    ENNReal.coe_toNNReal_eq_toReal _
  rw [show (fun ω => poissonChaosStep N n B ω)
      = fun ω => Probability.charlierScaled n (referenceIntensity ν B).toReal
          (N.N ω B).toReal from rfl]
  rw [integral_comp_count N hB hfin (Probability.continuous_charlierScaled n _).measurable, ← hr]
  exact Probability.integral_charlierPoly_eq_zero (referenceIntensity ν B).toNNReal hn

/-- The `L²` norm of a Poisson chaos element of a region of finite intensity,
`E[C_n ^ 2] = n! λ ^ n` for the rate `λ = ν̂(B)`. -/
theorem integral_poissonChaosStep_sq (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (n : ℕ) :
    ∫ ω, poissonChaosStep N n B ω ^ 2 ∂P
      = (n.factorial : ℝ) * (referenceIntensity ν B).toReal ^ n := by
  simpa [pow_two] using integral_poissonChaosStep_mul N hB hfin n n

private lemma referenceIntensity_strip {a b : ℝ} (ha : 0 ≤ a) (A : Set E) :
    referenceIntensity ν (Set.Ioc a b ×ˢ A) = ENNReal.ofReal (b - a) * ν A := by
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left
      (show Set.Ioc a b ⊆ Set.Ici 0 from fun x hx => ha.trans hx.1.le), Real.volume_Ioc]

private lemma referenceIntensity_strip_ne_top {a b : ℝ} (ha : 0 ≤ a) {A : Set E}
    (hAν : ν A ≠ ⊤) : referenceIntensity ν (Set.Ioc a b ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity_strip ha]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hAν

private lemma referenceIntensity_strip_toReal {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (A : Set E) :
    (referenceIntensity ν (Set.Ioc a b ×ˢ A)).toReal = (b - a) * (ν A).toReal := by
  rw [referenceIntensity_strip ha, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ b - a)]

/-- The Poisson chaos elements of a strip `(a, b] ×ˢ A` over a mark set of finite intensity are
orthogonal under `P`, with `E[C_n C_m] = δ_(n m) n! λ ^ n` for the rate `λ = (b - a) ν(A)`. -/
theorem integral_poissonChaosStep_strip_mul (N : PoissonRandomMeasure P ν) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (n m : ℕ) :
    ∫ ω, poissonChaosStep N n (Set.Ioc a b ×ˢ A) ω
        * poissonChaosStep N m (Set.Ioc a b ×ˢ A) ω ∂P
      = if n = m then (n.factorial : ℝ) * ((b - a) * (ν A).toReal) ^ n else 0 := by
  rw [integral_poissonChaosStep_mul N (measurableSet_Ioc.prod hA)
      (referenceIntensity_strip_ne_top ha hAν) n m,
    referenceIntensity_strip_toReal ha hab A]

/-- The Poisson chaos elements of positive degree of a strip `(a, b] ×ˢ A` over a mark set of
finite intensity are centred under `P`. -/
theorem integral_poissonChaosStep_strip_eq_zero (N : PoissonRandomMeasure P ν) {a b : ℝ}
    (ha : 0 ≤ a) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {n : ℕ} (hn : n ≠ 0) :
    ∫ ω, poissonChaosStep N n (Set.Ioc a b ×ˢ A) ω ∂P = 0 :=
  integral_poissonChaosStep_eq_zero N (measurableSet_Ioc.prod hA)
    (referenceIntensity_strip_ne_top ha hAν) hn

end LevyStochCalc.Poisson
