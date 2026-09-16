/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellConditionalIsometry
import LevyStochCalc.Poisson.CompensatedPullOut
import LevyStochCalc.Poisson.PathwiseIdentity

/-!
# Conditional cell isometries against the compensated Poisson random measure

Over a cell `(a, b]` with `0 ≤ a < b` and a mark set `A` of finite intensity, the increment of a
compensated integral across `(a, b]` pairs with the compensated count `Ñ((a, b] × A)` to the
integral of the integrand over the cell and over `A`, and the pairing survives conditioning at
the left endpoint. The compensated count is the compensated integral of the indicator integrand
of the rectangle `(a, b] × A`, restricting the integrand to the cell turns the increment into the
integral at the horizon `b`, a bounded weight measurable at `a` passes inside, and the horizon
isometry then evaluates the pairing.

## Main statements

* `stochasticIntegral_cellMarkIndicator_ae_eq` — the compensated count of `(a, b] × A` is the
  compensated integral of the indicator integrand of that rectangle.
* `condExp_compensated_cell_mul_compensated_count` — the conditional Itô–Lévy isometry over a
  cell, against the compensated count of `(a, b] × A`.
* `condExp_brownian_cell_mul_compensated_count_eq_zero` — a Brownian cell increment is
  conditionally orthogonal to the compensated count of `(a, b] × A`.

## References

* Karatzas and Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Brownian.Ito (indIoc)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section CompensatedCell

variable {φ : Ω → ℝ → E → ℝ} {A : Set E}

/-- The indicator integrand of the space-time rectangle `(a, b] × A`. -/
noncomputable def cellMarkIndicator (Ω) [MeasurableSpace Ω] (a b : ℝ) (A : Set E) :
    Ω → ℝ → E → ℝ :=
  fun _ s e => (Set.Ioc a b ×ˢ A).indicator (fun _ => (1 : ℝ)) (s, e)

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` vanishes off the mark set `A`. -/
theorem cellMarkIndicator_eq_zero_of_notMem {a b : ℝ} (ω : Ω) (s : ℝ) {e : E} (he : e ∉ A) :
    cellMarkIndicator Ω a b A ω s e = 0 :=
  Set.indicator_of_notMem (fun hm => he (Set.mem_prod.mp hm).2) _

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` vanishes off the cell `(a, b]`. -/
theorem cellMarkIndicator_eq_zero_of_notMem_Ioc {a b : ℝ} (ω : Ω) {s : ℝ}
    (hs : s ∉ Set.Ioc a b) (e : E) : cellMarkIndicator Ω a b A ω s e = 0 :=
  Set.indicator_of_notMem (fun hm => hs (Set.mem_prod.mp hm).1) _

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` is jointly measurable. -/
theorem measurable_cellMarkIndicator (hA : MeasurableSet A) (a b : ℝ) :
    Measurable fun p : Ω × ℝ × E => cellMarkIndicator Ω a b A p.1 p.2.1 p.2.2 :=
  (measurable_const.indicator (measurableSet_Ioc.prod hA)).comp measurable_snd

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` is predictable when `A` has finite intensity. -/
theorem markedPredictable_cellMarkIndicator {a b : ℝ} (ha : 0 ≤ a) (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) : Probability.MarkedPredictable ℱ ν (cellMarkIndicator Ω a b A) :=
  Probability.markedPredictable_rectIndicator ha hA hAν
    (c := fun _ : Ω => (1 : ℝ)) measurable_const

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The indicator integrand of `(a, b] × A` is marked progressively measurable when `A` has
finite intensity. -/
theorem markedProgressivelyMeasurable_cellMarkIndicator {a b : ℝ} (ha : 0 ≤ a)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) :
    Probability.MarkedProgressivelyMeasurable ℱ (cellMarkIndicator Ω a b A) :=
  (markedPredictable_cellMarkIndicator (ℱ := ℱ) ha hA hAν).markedProgressivelyMeasurable

omit [SigmaFinite ν] in
/-- The energy of the indicator integrand of `(a, b] × A` is finite when `A` has finite
intensity. -/
theorem lintegral_sq_cellMarkIndicator_lt_top (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (a b : ℝ) : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖cellMarkIndicator Ω a b A ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  intro T hT
  have hmark : ∀ (ω : Ω) (s : ℝ),
      ∫⁻ e, (‖cellMarkIndicator Ω a b A ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≤ ν A := by
    intro ω s
    have hpt : ∀ e : E, (‖cellMarkIndicator Ω a b A ω s e‖₊ : ℝ≥0∞) ^ 2
        ≤ A.indicator (fun _ => (1 : ℝ≥0∞)) e := by
      intro e
      by_cases he : e ∈ A
      · rw [Set.indicator_of_mem he]
        by_cases hs : s ∈ Set.Ioc a b
        · simp [cellMarkIndicator, Set.indicator_of_mem (Set.mk_mem_prod hs he)]
        · rw [cellMarkIndicator_eq_zero_of_notMem_Ioc (A := A) ω hs e]
          simp
      · rw [Set.indicator_of_notMem he,
          cellMarkIndicator_eq_zero_of_notMem (a := a) (b := b) ω s he]
        simp
    refine le_trans (lintegral_mono hpt) ?_
    rw [lintegral_indicator hA]
    simp
  have houter : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖cellMarkIndicator Ω a b A ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ≤ ν A * ENNReal.ofReal T := by
    intro ω
    refine le_trans (lintegral_mono (hmark ω)) ?_
    rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hconst : ∫⁻ _ω : Ω, ν A * ENNReal.ofReal T ∂P = ν A * ENNReal.ofReal T := by
    rw [lintegral_const, measure_univ, mul_one]
  exact lt_of_le_of_lt ((lintegral_mono houter).trans_eq hconst)
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hAν) ENNReal.ofReal_lt_top)

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The rectangle indicator on `(a, b] × A` reduces the horizon double integral of a marked
integrand to its integral over the cell and the mark set. -/
theorem setIntegral_Icc_mul_cellMarkIndicator {a b : ℝ} (ha : 0 ≤ a) (hA : MeasurableSet A)
    (F : ℝ → E → ℝ) (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) b, ∫ e, F s e * cellMarkIndicator Ω a b A ω s e ∂ν ∂volume
      = ∫ s in Set.Ioc a b, ∫ e in A, F s e ∂ν ∂volume := by
  have hpt : ∀ s : ℝ, (∫ e, F s e * cellMarkIndicator Ω a b A ω s e ∂ν)
      = (Set.Ioc a b).indicator (fun u => ∫ e in A, F u e ∂ν) s := by
    intro s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs]
      have hinner : ∀ e : E, F s e * cellMarkIndicator Ω a b A ω s e
          = A.indicator (fun u => F s u) e := by
        intro e
        by_cases he : e ∈ A
        · rw [Set.indicator_of_mem he]
          simp [cellMarkIndicator, Set.indicator_of_mem (Set.mk_mem_prod hs he)]
        · rw [Set.indicator_of_notMem he,
            cellMarkIndicator_eq_zero_of_notMem (a := a) (b := b) ω s he]
          ring
      simp_rw [hinner]
      exact integral_indicator hA
    · rw [Set.indicator_of_notMem hs]
      have hinner : ∀ e : E, F s e * cellMarkIndicator Ω a b A ω s e = 0 := by
        intro e
        rw [cellMarkIndicator_eq_zero_of_notMem_Ioc (A := A) ω hs e]
        ring
      simp_rw [hinner]
      exact integral_zero E ℝ
  simp_rw [hpt]
  exact setIntegral_Icc_indicator_Ioc ha _

/-- **The compensated count of a rectangle is a compensated integral.** For `0 ≤ a < b` and a
mark set of finite intensity, the compensated integral at the horizon `b` of the indicator
integrand of `(a, b] × A` is the compensated count `Ñ((a, b] × A)`. -/
theorem stochasticIntegral_cellMarkIndicator_ae_eq
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hm : Measurable fun p : Ω × ℝ × E => cellMarkIndicator Ω a b A p.1 p.2.1 p.2.2)
    (hp : Probability.MarkedProgressivelyMeasurable ℱ (cellMarkIndicator Ω a b A))
    (hq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖cellMarkIndicator Ω a b A ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (cellMarkIndicator Ω a b A) hm hp hq b
      =ᵐ[P] fun ω => D.N.compensated (Set.Ioc a b ×ˢ A) ω := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hsub : Set.Ioc a b ×ˢ A ⊆ Set.Ioc (0 : ℝ) b ×ˢ A :=
    Set.prod_mono (Set.Ioc_subset_Ioc_left ha) Set.Subset.rfl
  have hpath := Poisson.Compensated.stochasticIntegral_ae_eq_pathwise D.N ℱ hℱN
    (cellMarkIndicator Ω a b A) hm hp hq hA
    (markedPredictable_cellMarkIndicator (ℱ := ℱ) ha hA hAν) hAν
    (fun ω s e he => cellMarkIndicator_eq_zero_of_notMem (a := a) (b := b) ω s he) hb
  refine hpath.trans (Eventually.of_forall fun ω => ?_)
  have hone : ∀ μ : Measure (ℝ × E), ∫ q in Set.Ioc (0 : ℝ) b ×ˢ A,
      cellMarkIndicator Ω a b A ω q.1 q.2 ∂μ = (μ (Set.Ioc a b ×ˢ A)).toReal := by
    intro μ
    have hfun : (fun q : ℝ × E => cellMarkIndicator Ω a b A ω q.1 q.2)
        = (Set.Ioc a b ×ˢ A).indicator fun _ => (1 : ℝ) := rfl
    rw [hfun, setIntegral_indicator (measurableSet_Ioc.prod hA), Set.inter_eq_right.mpr hsub,
      setIntegral_const]
    simp [MeasureTheory.measureReal_def]
  show (∫ q in Set.Ioc (0 : ℝ) b ×ˢ A, cellMarkIndicator Ω a b A ω q.1 q.2 ∂D.N.N ω)
      - ∫ q in Set.Ioc (0 : ℝ) b ×ˢ A, cellMarkIndicator Ω a b A ω q.1 q.2
          ∂Poisson.referenceIntensity ν
    = D.N.compensated (Set.Ioc a b ×ˢ A) ω
  rw [hone, hone]
  rfl

/-- An integrand restricted to the cell `(a, b]`, as a marked horizon integrand at `b`. -/
noncomputable def cellIntegrand (P) [IsProbabilityMeasure P] (ν) [SigmaFinite ν]
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {φ : Ω → ℝ → E → ℝ}
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Poisson.Compensated.MarkedHorizonIntegrand P ν ℱ b where
  toFun := fun ω s e => indIoc Ω a b ω s * φ ω s e
  measurable_uncurry := Poisson.Compensated.measurable_indIoc_mul hφm a b
  progressive := Poisson.Compensated.markedProgressivelyMeasurable_indIoc_mul hφp a b
  vanishing := fun ω s e hs => by
    have hnot : s ∉ Set.Ioc a b := fun hmem => hs ⟨ha.trans hmem.1.le, hmem.2⟩
    simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hnot]
  energy_ne_top :=
    (Poisson.Compensated.sq_int_global_indIoc_mul hφs a b b (ha.trans_lt hab)).ne

/-- **Conditional Itô–Lévy isometry over a cell.** For `0 ≤ a < b` and a mark set of finite
intensity, the conditional expectation at the left endpoint of the increment across `(a, b]` of a
compensated integral, paired with the compensated count of `(a, b] × A`, is the conditional
expectation of the integral of the integrand over the cell and over `A`. -/
theorem condExp_compensated_cell_mul_compensated_count
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    (hφm : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hφp : Probability.MarkedProgressivelyMeasurable ℱ φ)
    (hφs : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[fun ω => (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs b ω
          - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs a ω)
        * D.N.compensated (Set.Ioc a b ×ˢ A) ω | ℱ a]
      =ᵐ[P] P[fun ω => ∫ s in Set.Ioc a b, ∫ e in A, φ ω s e ∂ν ∂volume | ℱ a] := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hψm := measurable_cellMarkIndicator (Ω := Ω) hA a b
  have hψp := markedProgressivelyMeasurable_cellMarkIndicator (ℱ := ℱ) (b := b) ha hA hAν
  have hψq := lintegral_sq_cellMarkIndicator_lt_top (P := P) (ν := ν) hA hAν a b
  have hcount := stochasticIntegral_cellMarkIndicator_ae_eq (D := D) hℱN hA hAν ha hab
    hψm hψp hψq
  have hFint : Integrable (fun p : Ω × ℝ × E =>
      φ p.1 p.2.1 p.2.2 * cellMarkIndicator Ω a b A p.1 p.2.1 p.2.2)
      (P.prod ((volume.restrict (Set.Icc (0 : ℝ) b)).prod ν)) :=
    (Ito.SecondMoment.memLp_two_prod_marked hφm (hφs b hb)).integrable_mul
      (Ito.SecondMoment.memLp_two_prod_marked hψm (hψq b hb))
  have hfae : (fun ω => ∫ q : ℝ × E, φ ω q.1 q.2 * cellMarkIndicator Ω a b A ω q.1 q.2
        ∂((volume.restrict (Set.Icc (0 : ℝ) b)).prod ν))
      =ᵐ[P] fun ω => ∫ s in Set.Ioc a b, ∫ e in A, φ ω s e ∂ν ∂volume := by
    filter_upwards [hFint.prod_right_ae] with ω hω
    rw [integral_prod _ hω]
    exact setIntegral_Icc_mul_cellMarkIndicator ha hA (φ ω) ω
  have hfint : Integrable (fun ω => ∫ s in Set.Ioc a b, ∫ e in A, φ ω s e ∂ν ∂volume) P :=
    hFint.integral_prod_left.congr hfae
  have hmemφ : MemLp (fun ω =>
      Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs b ω
        - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs a ω) 2 P :=
    (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN φ hφm hφp hφs b).sub
      (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN φ hφm hφp hφs a)
  have hmemN : MemLp (fun ω => D.N.compensated (Set.Ioc a b ×ˢ A) ω) 2 P :=
    (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN (cellMarkIndicator Ω a b A)
      hψm hψp hψq b).ae_eq hcount
  have hgint : Integrable (fun ω =>
      (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs b ω
        - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs a ω)
      * D.N.compensated (Set.Ioc a b ×ˢ A) ω) P := hmemφ.integrable_mul hmemN
  refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) hfint
    (fun S _ _ => integrable_condExp.integrableOn) (fun S hS _ => ?_)
    MeasureTheory.stronglyMeasurable_condExp.aestronglyMeasurable
  rw [setIntegral_condExp (ℱ.le a) hgint hS]
  set V : Ω → ℝ := S.indicator fun _ => (1 : ℝ) with hVdef
  have hV1 : ∀ ω, |V ω| ≤ 1 := by
    intro ω
    by_cases hω : ω ∈ S <;>
      simp [hVdef, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  have hVa : StronglyMeasurable[ℱ a] V := stronglyMeasurable_const.indicator hS
  set G := cellIntegrand P ν ℱ hφm hφp hφs ha hab with hGdef
  have hGfun : ∀ (ω : Ω) (s : ℝ) (e : E), G.toFun ω s e = indIoc Ω a b ω s * φ ω s e := by
    intro ω s e
    rw [hGdef]
    rfl
  have hGa : ∀ (ω : Ω) (s : ℝ) (e : E), s ≤ a → G.toFun ω s e = 0 := by
    intro ω s e hs
    have hnot : s ∉ Set.Ioc a b := fun hmem => absurd hs (not_le.mpr hmem.1)
    rw [hGfun]
    simp [Brownian.Ito.indIoc, Set.indicator_of_notMem hnot]
  set GV := G.mulLeft hGa hVa hV1 with hGVdef
  have hGVfun : ∀ (ω : Ω) (s : ℝ) (e : E), GV.toFun ω s e = V ω * G.toFun ω s e := by
    intro ω s e
    rw [hGVdef]
    rfl
  have hlocG : Poisson.Compensated.stochasticIntegral D.N ℱ hℱN G.toFun G.measurable_uncurry
        G.progressive G.sq_int_global b
      =ᵐ[P] fun ω => Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs b ω
        - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs a ω :=
    Poisson.Compensated.stochasticIntegral_indicator_Ioc D.N hℱN hφm hφp hφs ha hab
  have hpull : Poisson.Compensated.stochasticIntegral D.N ℱ hℱN GV.toFun GV.measurable_uncurry
        GV.progressive GV.sq_int_global b
      =ᵐ[P] fun ω => V ω * Poisson.Compensated.stochasticIntegral D.N ℱ hℱN G.toFun
        G.measurable_uncurry G.progressive G.sq_int_global b ω :=
    Poisson.Compensated.MarkedHorizonIntegrand.integral_mulLeft D.N hℱN hb G ha hab.le hGa
      hVa hV1
  have hpol := Ito.SecondMoment.integral_mul_stochasticIntegral D.N ℱ hℱN
    GV.measurable_uncurry GV.progressive GV.sq_int_global hψm hψp hψq hb
  rw [← MeasureTheory.integral_indicator (ℱ.le a S hS),
    ← MeasureTheory.integral_indicator (ℱ.le a S hS)]
  have hleft : ∫ ω, S.indicator (fun ω =>
        (Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs b ω
          - Poisson.Compensated.stochasticIntegral D.N ℱ hℱN φ hφm hφp hφs a ω)
        * D.N.compensated (Set.Ioc a b ×ˢ A) ω) ω ∂P
      = ∫ ω, Poisson.Compensated.stochasticIntegral D.N ℱ hℱN GV.toFun GV.measurable_uncurry
            GV.progressive GV.sq_int_global b ω
          * Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (cellMarkIndicator Ω a b A)
            hψm hψp hψq b ω ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hlocG, hcount, hpull] with ω e1 e2 e3
    rw [e3, e1, e2]
    by_cases hω : ω ∈ S <;>
      simp [hVdef, Set.indicator_of_mem, Set.indicator_of_notMem, hω]
  rw [hleft, hpol]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  have hpt : ∀ (s : ℝ) (e : E), GV.toFun ω s e * cellMarkIndicator Ω a b A ω s e
      = V ω * (φ ω s e * cellMarkIndicator Ω a b A ω s e) := by
    intro s e
    rw [hGVfun, hGfun]
    by_cases hs : s ∈ Set.Ioc a b
    · have h1 : indIoc Ω a b ω s = 1 := by
        simp [Brownian.Ito.indIoc, Set.indicator_of_mem hs]
      rw [h1]
      ring
    · rw [cellMarkIndicator_eq_zero_of_notMem_Ioc (A := A) ω hs e]
      ring
  show ∫ s in Set.Icc (0 : ℝ) b, ∫ e,
        GV.toFun ω s e * cellMarkIndicator Ω a b A ω s e ∂ν ∂volume
      = S.indicator (fun x => ∫ s in Set.Ioc a b, ∫ e in A, φ x s e ∂ν ∂volume) ω
  simp_rw [hpt, integral_const_mul]
  rw [setIntegral_Icc_mul_cellMarkIndicator ha hA (φ ω) ω]
  by_cases hω : ω ∈ S <;>
    simp [hVdef, Set.indicator_of_mem, Set.indicator_of_notMem, hω]

/-- **Conditional orthogonality of a Brownian cell increment to a compensated count.** For
`0 ≤ a < b` and a mark set of finite intensity, the increment across `(a, b]` of an Itô integral
against a Brownian coordinate has vanishing conditional expectation at the left endpoint against
the compensated count of `(a, b] × A`. -/
theorem condExp_brownian_cell_mul_compensated_count_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d}
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
    (hℱN : Poisson.IsPoissonFiltration D.N ℱ)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[fun ω =>
        (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
          - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
        * D.N.compensated (Set.Ioc a b ×ˢ A) ω | ℱ a] =ᵐ[P] 0 := by
  have hb : (0 : ℝ) < b := ha.trans_lt hab
  have hψm := measurable_cellMarkIndicator (Ω := Ω) hA a b
  have hψp := markedProgressivelyMeasurable_cellMarkIndicator (ℱ := ℱ) (b := b) ha hA hAν
  have hψq := lintegral_sq_cellMarkIndicator_lt_top (P := P) (ν := ν) hA hAν a b
  have hcount := stochasticIntegral_cellMarkIndicator_ae_eq (D := D) hℱN hA hAν ha hab
    hψm hψp hψq
  have hIm : Measurable (Function.uncurry (indIoc Ω a b)) :=
    Brownian.Ito.measurable_uncurry_indIoc a b
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
  have hmemH : MemLp (fun ω =>
      Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
      2 P :=
    (Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b).sub
      (Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a)
  have hmemN : MemLp (fun ω => D.N.compensated (Set.Ioc a b ×ˢ A) ω) 2 P :=
    (Poisson.Compensated.stochasticIntegral_memLp D.N ℱ hℱN (cellMarkIndicator Ω a b A)
      hψm hψp hψq b).ae_eq hcount
  have hgint : Integrable (fun ω =>
      (Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs b ω
        - Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i) H hHm hHp hHs a ω)
      * D.N.compensated (Set.Ioc a b ×ˢ A) ω) P := hmemH.integrable_mul hmemN
  refine (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le a) hgint
    (fun S _ _ => (integrable_zero Ω ℝ P).integrableOn) (fun S hS _ => ?_)
    (aestronglyMeasurable_const (b := (0 : ℝ)))).symm
  simp only [Pi.zero_apply, MeasureTheory.integral_zero]
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
  have hzero : ∫ ω, Brownian.Ito.stochasticIntegralBrownian (D.W.W i) ℱ (hcoord i)
        (fun ω s => V ω * indIoc Ω a b ω s * H ω s) hvm hvp hvq b ω
      * Poisson.Compensated.stochasticIntegral D.N ℱ hℱN (cellMarkIndicator Ω a b A)
        hψm hψp hψq b ω ∂P = 0 :=
    integral_stochasticIntegral_mul_compensated_eq_zero 𝒲 hcoord hℱN hvm hvp hvq
      hψm hψp hψq hb.le
  refine (Eq.trans ?_ hzero).symm
  rw [← MeasureTheory.integral_indicator (ℱ.le a S hS)]
  refine integral_congr_ae ?_
  filter_upwards [hlocH, hcount, hpull] with ω e1 e2 e3
  rw [← e3, e1, e2]
  by_cases hω : ω ∈ S <;>
    simp [hVdef, Set.indicator_of_mem, Set.indicator_of_notMem, hω]

end CompensatedCell

end LevyDriver

end LevyStochCalc.Driver
