/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellOrthogonality
import LevyStochCalc.Brownian.ItoPullOut
import LevyStochCalc.Ito.SecondMomentQuadratic

/-!
# Conditional cell isometries for a Lévy driver

Over a cell `(a, b]` with `0 ≤ a < b` the increment of a Brownian Itô integral pairs with a
second such increment to the time integral of the product of the integrands over the cell, and
the pairing survives conditioning at the left endpoint: the conditional expectation at `ℱ a` of
the increment against the Brownian increment `W_b − W_a` is the conditional cell average of the
integrand. Restricting the integrand to the cell turns the increment into the integral at the
horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon isometry then
evaluates the pairing.

## Main statements

* `integral_brownian_cell_mul_brownian_cell` — the polarised Itô isometry over a cell.
* `condExp_brownian_cell_mul_increment` — the conditional Itô isometry over a cell, against the
  Brownian increment.
* `condExp_brownian_cell_mul_brownian_increment_eq_zero` — the increment against one coordinate
  is conditionally orthogonal to the increment of another coordinate.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The window indicator `1_{(a, b]}` is progressively measurable for `0 ≤ a < b`. -/
theorem progressivelyMeasurable_indIoc_of_nonneg (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) := by
  rcases eq_or_lt_of_le ha with rfl | ha'
  · exact progressivelyMeasurable_indIoc₀ ℱ hab
  · exact progressivelyMeasurable_indIoc ℱ ha' hab

/-- An integrand weighted by a weight bounded by one and by the window indicator has pointwise
square at most the square of the integrand. -/
theorem nnnorm_sq_mul_indIoc_mul_le {H V : Ω → ℝ → ℝ} (hVb : ∀ ω s, |V ω s| ≤ 1) (a b : ℝ)
    (ω : Ω) (s : ℝ) :
    (‖V ω s * indIoc Ω a b ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
  have hprod : |V ω s| * |indIoc Ω a b ω s| ≤ 1 := by
    have := mul_le_mul (hVb ω s) (indIoc_le_one a b ω s) (abs_nonneg _) zero_le_one
    simpa using this
  have hnorm : ‖V ω s * indIoc Ω a b ω s * H ω s‖ ≤ ‖H ω s‖ := by
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    simpa using mul_le_mul_of_nonneg_right hprod (abs_nonneg (H ω s))
  have hnn : (‖V ω s * indIoc Ω a b ω s * H ω s‖₊ : ℝ≥0∞) ≤ (‖H ω s‖₊ : ℝ≥0∞) := by
    exact_mod_cast hnorm
  exact pow_le_pow_left' hnn 2

end LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Driver

universe v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section BrownianCell

variable {H K : Ω → ℝ → ℝ}

omit [MeasurableSpace Ω] [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- For `0 ≤ a` the integral over the horizon `[0, b]` of a function extended by zero off
`(a, b]` is its integral over `(a, b]`. -/
theorem setIntegral_Icc_indicator_Ioc {a b : ℝ} (ha : 0 ≤ a) (f : ℝ → ℝ) :
    ∫ s in Set.Icc (0 : ℝ) b, (Set.Ioc a b).indicator f s ∂volume
      = ∫ s in Set.Ioc a b, f s ∂volume := by
  have hsub : Set.Ioc a b ⊆ Set.Icc (0 : ℝ) b := fun s hs => ⟨ha.trans hs.1.le, hs.2⟩
  rw [setIntegral_indicator measurableSet_Ioc, Set.inter_eq_right.mpr hsub]

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The product of two integrands restricted to `(a, b]` integrates over the horizon `[0, b]` to
the integral of the product of the integrands over `(a, b]`. -/
theorem setIntegral_Icc_indIoc_mul_mul {a b : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b,
        (indIoc Ω a b ω s * H ω s) * (indIoc Ω a b ω s * K ω s) ∂volume
      = ∫ s in Set.Ioc a b, H ω s * K ω s ∂volume := by
  have hpt : ∀ s : ℝ, (indIoc Ω a b ω s * H ω s) * (indIoc Ω a b ω s * K ω s)
      = (Set.Ioc a b).indicator (fun u => H ω u * K ω u) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hs]
  simp_rw [hpt]
  exact setIntegral_Icc_indicator_Ioc ha _

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- An integrand restricted to `(a, b]` integrates over the horizon `[0, b]` to its integral
over `(a, b]`. -/
theorem setIntegral_Icc_indIoc_mul {a b : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b, indIoc Ω a b ω s * H ω s ∂volume
      = ∫ s in Set.Ioc a b, H ω s ∂volume := by
  have hpt : ∀ s : ℝ, indIoc Ω a b ω s * H ω s = (Set.Ioc a b).indicator (H ω) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hs]
  simp_rw [hpt]
  exact setIntegral_Icc_indicator_Ioc ha _

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A weighted integrand restricted to `(a, b]`, paired with the window indicator, integrates
over the horizon `[0, b]` to the weight times the integral of the integrand over `(a, b]`. -/
theorem setIntegral_Icc_mul_indIoc_mul {V : Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b,
        (V ω * indIoc Ω a b ω s * H ω s) * indIoc Ω a b ω s ∂volume
      = V ω * ∫ s in Set.Ioc a b, H ω s ∂volume := by
  have hpt : ∀ s : ℝ, (V ω * indIoc Ω a b ω s * H ω s) * indIoc Ω a b ω s
      = (Set.Ioc a b).indicator (fun u => V ω * H ω u) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_mem hs]
    · rw [Set.indicator_of_notMem hs]
      simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hs]
  simp_rw [hpt]
  rw [setIntegral_Icc_indicator_Ioc ha _, integral_const_mul]

/-- **Polarised Itô isometry over a cell.** For `0 ≤ a < b` the pairing of the increments across
`(a, b]` of the Itô integrals of two integrands against the same Brownian coordinate is the
expected integral of the product of the integrands over `(a, b]`. -/
theorem integral_brownian_cell_mul_brownian_cell
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i : Fin d}
    (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
      * (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs a ω) ∂P
      = ∫ ω, ∫ s in Set.Ioc a b, H ω s * K ω s ∂volume ∂P := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hHm' : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * H ω s) :=
    Brownian.Ito.measurable_uncurry_indicator_Ioc_mul H hHm a b
  have hHp' : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * H ω s :=
    Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul ℱ H hHp a b
  have hHq' : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top (P := P) H hHs a b
  have hKm' : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * K ω s) :=
    Brownian.Ito.measurable_uncurry_indicator_Ioc_mul K hKm a b
  have hKp' : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * K ω s :=
    Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul ℱ K hKp a b
  have hKq' : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top (P := P) K hKs a b
  have hlocH : Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
        (fun ω s => indIoc Ω a b ω s * H ω s) hHm' hHp' hHq' b
      =ᵐ[P] fun ω =>
        Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω := by
    have h := Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc (D.W.W i) ℱ (hcoord i)
      H hHm hHp hHs ha hab hHm' hHp' hHq' hb
    rw [min_self, min_eq_left hab.le] at h
    exact h
  have hlocK : Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
        (fun ω s => indIoc Ω a b ω s * K ω s) hKm' hKp' hKq' b
      =ᵐ[P] fun ω =>
        Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs a ω := by
    have h := Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc (D.W.W i) ℱ (hcoord i)
      K hKm hKp hKs ha hab hKm' hKp' hKq' hb
    rw [min_self, min_eq_left hab.le] at h
    exact h
  have hpol := Ito.SecondMoment.integral_mul_stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
    hHm' hHp' hHq' hKm' hKp' hKq' hb
  have hleft : ∫ ω,
      (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
      * (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) K hKm hKp hKs a ω) ∂P
      = ∫ ω, Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
            (fun ω s => indIoc Ω a b ω s * H ω s) hHm' hHp' hHq' b ω
          * Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
            (fun ω s => indIoc Ω a b ω s * K ω s) hKm' hKp' hKq' b ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hlocH, hlocK] with ω e1 e2
    rw [e1, e2]
  rw [hleft, hpol]
  exact integral_congr_ae (Eventually.of_forall fun ω =>
    setIntegral_Icc_indIoc_mul_mul (H := H) (K := K) ha ω)

/-- **Conditional Itô isometry over a cell.** For `0 ≤ a < b` the conditional expectation at the
left endpoint of the increment across `(a, b]` of an Itô integral, paired with the increment of
the Brownian coordinate it is taken against, is the conditional expectation of the integral of
the integrand over `(a, b]`. -/
theorem condExp_brownian_cell_mul_increment
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i : Fin d}
    (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[fun ω =>
        (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * ((D.W.W i).W b ω - (D.W.W i).W a ω) | ℱ a]
      =ᵐ[P] P[fun ω => ∫ s in Set.Ioc a b, H ω s ∂volume | ℱ a] := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hIm : Measurable (Function.uncurry (indIoc Ω a b)) :=
    Brownian.Ito.measurable_uncurry_indIoc a b
  have hIp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) :=
    Brownian.Ito.progressivelyMeasurable_indIoc_of_nonneg ℱ ha hab
  have hIq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T hT => Brownian.Ito.lintegral_sq_indIoc_lt_top P a b T hT
  have hHm' : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * H ω s) :=
    Brownian.Ito.measurable_uncurry_indicator_Ioc_mul H hHm a b
  have hHp' : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * H ω s :=
    Brownian.Ito.progressivelyMeasurable_indicator_Ioc_mul ℱ H hHp a b
  have hHq' : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    Brownian.Ito.lintegral_sq_indicator_Ioc_mul_lt_top (P := P) H hHs a b
  have hlocH : Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
        (fun ω s => indIoc Ω a b ω s * H ω s) hHm' hHp' hHq' b
      =ᵐ[P] fun ω =>
        Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω := by
    have h := Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc (D.W.W i) ℱ (hcoord i)
      H hHm hHp hHs ha hab hHm' hHp' hHq' hb
    rw [min_self, min_eq_left hab.le] at h
    exact h
  have hincr : Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
        (indIoc Ω a b) hIm hIp hIq b
      =ᵐ[P] fun ω => (D.W.W i).W b ω - (D.W.W i).W a ω := by
    have h := Brownian.Ito.stochasticIntegralBrownian_indIoc (D.W.W i) ℱ (hcoord i) ha hab
      hIm hIp hIq hb.le
    rw [min_self, min_eq_left hab.le] at h
    exact h
  have hmemH : MemLp (fun ω =>
      Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
      2 P :=
    (Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b).sub
      (Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a)
  have hmemI : MemLp (fun ω => (D.W.W i).W b ω - (D.W.W i).W a ω) 2 P :=
    (Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hcoord i) (indIoc Ω a b)
      hIm hIp hIq b).ae_eq hincr
  have hgint : Integrable (fun ω =>
      (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
      * ((D.W.W i).W b ω - (D.W.W i).W a ω)) P := hmemH.integrable_mul hmemI
  have hfmeas : AEStronglyMeasurable (fun ω => ∫ s in Set.Ioc a b, H ω s ∂volume) P :=
    ((hHp.stronglyMeasurable_setIntegral measurableSet_Ioc Set.Ioc_subset_Iic_self
      volume).mono (ℱ.le b)).aestronglyMeasurable
  have hfsq : ∫⁻ ω, (‖∫ s in Set.Ioc a b, H ω s ∂volume‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
    have hle := Ito.Picard.lintegral_sq_setIntegral_le (P := P)
      (f := fun ω s => indIoc Ω a b ω s * H ω s) hHm' hb.le (hHq' b hb)
    simp_rw [setIntegral_Icc_indIoc_mul (H := H) ha] at hle
    exact lt_of_le_of_lt hle (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hHq' b hb))
  have hfint : Integrable (fun ω => ∫ s in Set.Ioc a b, H ω s ∂volume) P :=
    (Brownian.Ito.memLp_two_of_lintegral_sq_lt_top hfmeas hfsq).integrable (by norm_num)
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) hfint
    (fun S _ _ => integrable_condExp.integrableOn) (fun S hS _ => ?_)
    MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
  rw [setIntegral_condExp (ℱ.le a) hgint hS]
  set V : Ω → ℝ := S.indicator fun _ => (1 : ℝ) with hVdef
  have hV1 : ∀ ω, |V ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ S <;>
      simp [hVdef, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M := ⟨1, hV1⟩
  have hVm : Measurable V :=
    (measurable_const : Measurable fun _ : Ω => (1 : ℝ)).indicator (ℱ.le a S hS)
  have hVa : StronglyMeasurable[ℱ a] V := stronglyMeasurable_const.indicator hS
  have hvm : Measurable (Function.uncurry fun ω s => V ω * indIoc Ω a b ω s * H ω s) :=
    ((hVm.comp measurable_fst).mul hIm).mul hHm
  have hvp : Probability.ProgressivelyMeasurable ℱ
      fun ω s => V ω * indIoc Ω a b ω s * H ω s :=
    (Brownian.Ito.progressivelyMeasurable_mul_indIoc ℱ ha hab hVb hVm hVa).mul hHp
  have hvq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖V ω * indIoc Ω a b ω s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T hT
    refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => ?_) (hHs T hT)
    exact Brownian.Ito.nnnorm_sq_mul_indIoc_mul_le (H := H) (V := fun ω _ => V ω)
      (fun ω _ => hV1 ω) a b ω s
  have hpull := Brownian.Ito.mul_stochasticIntegralBrownian_indIoc (D.W.W i) ℱ (hcoord i)
    ha hab hVb hVm hVa H hHm hHp hHs hHm' hHp' hHq' hvm hvp hvq hb
  have hpol := Ito.SecondMoment.integral_mul_stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
    hvm hvp hvq hIm hIp hIq hb
  rw [← MeasureTheory.integral_indicator (ℱ.le a S hS),
    ← MeasureTheory.integral_indicator (ℱ.le a S hS)]
  have hleft : ∫ ω, S.indicator (fun ω =>
        (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * ((D.W.W i).W b ω - (D.W.W i).W a ω)) ω ∂P
      = ∫ ω, Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
            (fun ω s => V ω * indIoc Ω a b ω s * H ω s) hvm hvp hvq b ω
          * Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
            (indIoc Ω a b) hIm hIp hIq b ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hlocH, hincr, hpull] with ω e1 e2 e3
    rw [← e3, e1, e2]
    by_cases hω : ω ∈ S <;>
      simp [hVdef, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  rw [hleft, hpol]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  show ∫ s in Set.Icc (0 : ℝ) b, V ω * indIoc Ω a b ω s * H ω s * indIoc Ω a b ω s ∂volume
      = S.indicator (fun x => ∫ s in Set.Ioc a b, H x s ∂volume) ω
  rw [setIntegral_Icc_mul_indIoc_mul (H := H) (V := V) ha ω]
  by_cases hω : ω ∈ S <;>
    simp [hVdef, Set.indicator_of_mem, Set.indicator_of_notMem, hω]

/-- **Conditional orthogonality of a cell increment to a distinct Brownian increment.** For
distinct coordinates the increment across `(a, b]` of an Itô integral against one coordinate has
vanishing conditional expectation at `a` against the increment of the other coordinate. -/
theorem condExp_brownian_cell_mul_brownian_increment_eq_zero
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {i j : Fin d} (hij : i ≠ j)
    (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[fun ω =>
        (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * ((D.W.W j).W b ω - (D.W.W j).W a ω) | ℱ a] =ᵐ[P] 0 := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hIm : Measurable (Function.uncurry (indIoc Ω a b)) :=
    Brownian.Ito.measurable_uncurry_indIoc a b
  have hIp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b) :=
    Brownian.Ito.progressivelyMeasurable_indIoc_of_nonneg ℱ ha hab
  have hIq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T hT => Brownian.Ito.lintegral_sq_indIoc_lt_top P a b T hT
  have hb' : Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hcoord j)
        (indIoc Ω a b) hIm hIp hIq b
      =ᵐ[P] fun ω => (D.W.W j).W b ω - (D.W.W j).W a ω := by
    have h := Brownian.Ito.stochasticIntegralBrownian_indIoc (D.W.W j) ℱ (hcoord j) ha hab
      hIm hIp hIq hb.le
    rw [min_self, min_eq_left hab.le] at h
    exact h
  have ha' : Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hcoord j)
        (indIoc Ω a b) hIm hIp hIq a
      =ᵐ[P] fun ω => (D.W.W j).W a ω - (D.W.W j).W a ω := by
    have h := Brownian.Ito.stochasticIntegralBrownian_indIoc (D.W.W j) ℱ (hcoord j) ha hab
      hIm hIp hIq ha
    rw [min_self, min_eq_right hab.le] at h
    exact h
  have hcross := Brownian.Ito.condExp_mul_cross_increment_eq_zero D.W hcoord hHm hHp hHs
    hIm hIp hIq hij ha hab
  refine Filter.EventuallyEq.trans (MeasureTheory.condExp_congr_ae ?_) hcross
  filter_upwards [hb', ha'] with ω e1 e2
  rw [e1, e2]
  ring

end BrownianCell

end LevyDriver

end LevyStochCalc.Driver
