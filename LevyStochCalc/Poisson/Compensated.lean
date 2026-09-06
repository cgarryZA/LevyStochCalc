/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.RandomMeasure
import LevyStochCalc.Poisson.NaturalFiltration
import LevyStochCalc.Poisson.CompensatedProcessQuadVar
import LevyStochCalc.Martingale.CadlagModification
import Mathlib.Probability.Martingale.Basic

/-!
# Compensated Poisson L²-Itô–Lévy integral

The L²-Itô–Lévy integral against the compensated Poisson random measure `Ñ`,
with its martingale, quadratic-variation, isometry, and càdlàg properties
(Applebaum 2009 §4.2, Theorems 4.2.3 and 4.2.4).

`stochasticIntegral` is the càdlàg adapted modification (`exists_cadlag_modification`)
of the `L²` integral process `process` (`Poisson/CompensatedProcess.lean`), the
`L²`-limit at every time of the integrals of the mark-step approximants of the
integrand (`Poisson/CompensatedApprox.lean`). `itoIsometry_compensated_unified_existence`
packages the martingale property, the quadratic variation, the L²-isometry, and the
càdlàg paths of `stochasticIntegral` in one 4-conjunct existential;
`itoLevyIsometry`, `quadVar_stochasticIntegral`, `martingale_stochasticIntegral`,
`cadlag_modification_exists`, and `L2Isometry.itoLevyIsometry` are its conjuncts.

`itoIsometry_diff_compensated` (cited axiom #18) is the per-difference L²-isometry
for this integral — a consequence of L²-linearity and isometry (Applebaum
Thm 4.2.3 step II). It is stated separately for now: `stochasticIntegral` is a
modification chosen per integrand, and the difference isometry is to be derived from
the cross-difference isometry of the mark-step approximants of the two integrands. It
is consumed by `Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise` and mirrors
`Brownian.Ito.itoIsometry_diff_brownian`.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2 (Thm 4.2.3/4.2.4).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is scoped per-declaration (`open Classical in`) rather than
-- at file scope.

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Integral

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : ∀ t : ℝ,
    @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
      (@Prod.instMeasurableSpace Ω (ℝ × E)
        ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
        inferInstance)
      (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- The `L²` integral process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` has a modification adapted to
the right-continuous natural filtration whose paths are almost surely càdlàg. -/
theorem exists_cadlag_modification :
    ∃ Y : ℝ → Ω → ℝ, Adapted (naturalFiltration N).rightCont Y ∧
      (∀ t, Y t =ᵐ[P] process N φ h_meas h_progMeas h_sq_int_global t) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)) ∧
          ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L) :=
  LevyStochCalc.Martingale.exists_adapted_ae_cadlag_of_eLpNorm
    (martingale_rightCont_process N φ h_meas h_progMeas h_sq_int_global)
    (process_eLpNorm_two_right_tendsto N φ h_meas h_progMeas h_sq_int_global)
    (fun _ ht => process_ae_zero_of_nonpos N φ h_meas h_progMeas h_sq_int_global ht.le)

/-- The L² Itô–Lévy integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` against the compensated
measure of a Poisson random measure: the càdlàg adapted modification of the `L²` integral
process `process`, the `L²`-limit of the integrals of the mark-step approximants of `φ`. -/
noncomputable def stochasticIntegral (T : ℝ) : Ω → ℝ :=
  Classical.choose (exists_cadlag_modification N φ h_meas h_progMeas h_sq_int_global) T

lemma stochasticIntegral_adapted :
    Adapted (naturalFiltration N).rightCont
      (stochasticIntegral N φ h_meas h_progMeas h_sq_int_global) :=
  (Classical.choose_spec (exists_cadlag_modification N φ h_meas h_progMeas h_sq_int_global)).1

/-- The stochastic integral agrees almost surely with the `L²` integral process at every
time. -/
lemma stochasticIntegral_ae_eq_process (t : ℝ) :
    stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] process N φ h_meas h_progMeas h_sq_int_global t :=
  (Classical.choose_spec
    (exists_cadlag_modification N φ h_meas h_progMeas h_sq_int_global)).2.1 t

/-- The paths of the stochastic integral are almost surely càdlàg. -/
lemma stochasticIntegral_cadlag :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => stochasticIntegral N φ h_meas h_progMeas h_sq_int_global s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t ω))
        ∧ ∃ L : ℝ,
            Filter.Tendsto
              (fun s => stochasticIntegral N φ h_meas h_progMeas h_sq_int_global s ω)
              (nhdsWithin t (Set.Iio t)) (nhds L) :=
  (Classical.choose_spec
    (exists_cadlag_modification N φ h_meas h_progMeas h_sq_int_global)).2.2

/-- The stochastic integral is a martingale on the right-continuous natural filtration. -/
theorem martingale_stochasticIntegral_rightCont :
    Martingale (stochasticIntegral N φ h_meas h_progMeas h_sq_int_global)
      (naturalFiltration N).rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_rightCont_process N φ h_meas h_progMeas h_sq_int_global)
    (fun t => (stochasticIntegral_adapted N φ h_meas h_progMeas h_sq_int_global
      t).stronglyMeasurable)
    (stochasticIntegral_ae_eq_process N φ h_meas h_progMeas h_sq_int_global)

/-- The compensated square `M_t² − ∫_0^t ∫_E φ(s, e)² ν(de) ds` of the stochastic integral is a
martingale on the right-continuous natural filtration. -/
theorem martingale_quadVar_stochasticIntegral_rightCont :
    Martingale
      (fun t ω => (stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν)
      (naturalFiltration N).rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_rightCont_quadVar_process N φ h_meas h_progMeas h_sq_int_global)
    (fun t => ((stochasticIntegral_adapted N φ h_meas h_progMeas h_sq_int_global
      t).stronglyMeasurable.pow 2).sub
      ((compensator_stronglyAdapted N φ h_progMeas t).mono ((naturalFiltration N).le_rightCont t)))
    (fun t => by
      filter_upwards [stochasticIntegral_ae_eq_process N φ h_meas h_progMeas h_sq_int_global t]
        with ω hω
      show (stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 - _
        = (process N φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 - _
      rw [hω]
      rfl)

/-- The Itô–Lévy isometry of the stochastic integral at every time `T > 0`. -/
theorem isometry_stochasticIntegral (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N φ h_meas h_progMeas h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← process_lintegral_sq' N φ h_meas h_progMeas h_sq_int_global hT.le]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegral_ae_eq_process N φ h_meas h_progMeas h_sq_int_global T]
    with ω hω
  rw [hω]

include h_meas h_progMeas h_sq_int_global in
/-- **Unified L²-Itô-Lévy integral with martingale + quadVar + isometry + càdlàg.**

For predictable square-integrable `φ : Ω → ℝ → E → ℝ`, there exists a process
`F : ℝ → Ω → ℝ` and a filtration `Filt` such that:

* `F` is a martingale wrt `Filt`,
* `(F t)² − ∫_0^t ∫_E |φ(s, e)|² ν(de) ds` is a martingale wrt `Filt`
  (quadratic variation identity),
* `∫⁻ ω, ‖F T‖₊² ∂P`
  `= ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖φ ω s e‖₊² ∂ν ∂volume ∂P`
  for every `T > 0` with `h_meas + h_sq_int` (L²-isometry),
* `F` has càdlàg paths.

`F` is the canonical L²-Itô-Lévy integral `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`.
Consolidates Applebaum 2009 Thm 4.2.3 + Thm 4.2.4.

The integrand hypotheses (`h_meas` joint measurability on `Ω×ℝ×E`,
`h_progMeas` progressive measurability w.r.t. `(naturalFiltration N).seq t`,
`h_sq_int_global` a global L² bound) are taken as *outer* hypotheses, mirroring
the Brownian-side statement; the existential body is then unconditional on them.
This matches Applebaum Thm 4.2.3's predictable-`φ` hypothesis class and prevents
a `Measurable`-only `F ≡ 0` from satisfying the conjuncts vacuously. `Filt` is
pinned to `(naturalFiltration N).rightCont`, ruling out trivial-filtration
witnesses such as `Filt = const ⊤`.

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed.,
CUP 2009, **Theorem 4.2.3** (martingale + quadratic variation + L²-isometry of
the L² Itô-Lévy integral) + **Theorem 4.2.4** (càdlàg modification); Ikeda &
Watanabe, *SDEs and Diffusion Processes*, 2nd ed., North-Holland 1989, **Section
II.3**.

**Construction**: `F := stochasticIntegral`, the càdlàg adapted modification
(`exists_cadlag_modification`, from the quasimartingale regularisation of
`RemyDegenne/brownian-motion`) of the `L²` integral process `process`
(`Poisson/CompensatedProcess.lean`), itself the `L²`-limit at every time of the
integrals of the mark-step approximants of `φ` (`Poisson/CompensatedApprox.lean`).
Conjunct 1 is `martingale_stochasticIntegral_rightCont`, conjunct 2 is
`martingale_quadVar_stochasticIntegral_rightCont` (the stage compensated squares
are martingales by the set-level increment isometries, and converge in `L¹`),
conjunct 3 is `isometry_stochasticIntegral`, conjunct 4 is
`stochasticIntegral_cadlag`. -/
theorem itoIsometry_compensated_unified_existence :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = (LevyStochCalc.Poisson.naturalFiltration N).rightCont ∧
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2
          - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν) Filt P ∧
      (∀ T : ℝ, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Ioi t)) (nhds (F t ω))
          ∧ ∃ L : ℝ,
              Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Iio t)) (nhds L)) :=
  ⟨stochasticIntegral N φ h_meas h_progMeas h_sq_int_global, (naturalFiltration N).rightCont, rfl,
    martingale_stochasticIntegral_rightCont N φ h_meas h_progMeas h_sq_int_global,
    martingale_quadVar_stochasticIntegral_rightCont N φ h_meas h_progMeas h_sq_int_global,
    isometry_stochasticIntegral N φ h_meas h_progMeas h_sq_int_global,
    stochasticIntegral_cadlag N φ h_meas h_progMeas h_sq_int_global⟩

/-- Itô-Lévy L² isometry on the bounded interval `[0, T]`.

  `𝔼[ (∫_0^T ∫_E φ(s, e) Ñ(ds, de))² ] = 𝔼[ ∫_0^T ∫_E |φ(s, e)|² ν(de) ds ]`

ENNReal form. -/
theorem itoLevyIsometry (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N φ h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P :=
  isometry_stochasticIntegral N φ h_meas h_progMeas h_sq_int_global T hT

/-- **Quadratic variation of the L² Itô-Lévy integral.**

For predictable square-integrable `φ`, the process
`t ↦ (M_t)² − ∫_0^t ∫_E |φ(s, e)|² ν(de) ds` is a martingale, where
`M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the L² Itô-Lévy integral. -/
theorem quadVar_stochasticIntegral :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν)
        F P :=
  ⟨(naturalFiltration N).rightCont,
    martingale_quadVar_stochasticIntegral_rightCont N φ h_meas h_progMeas h_sq_int_global⟩

/-- **The L² Itô-Lévy integral is a martingale.**

The compensated-Poisson stochastic integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`
is a square-integrable martingale w.r.t. the right-continuous natural filtration of `N`. -/
theorem martingale_stochasticIntegral :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t) F P :=
  ⟨(naturalFiltration N).rightCont,
    martingale_stochasticIntegral_rightCont N φ h_meas h_progMeas h_sq_int_global⟩

/-- **Càdlàg modification of L² Itô-Lévy integral.**

The compensated-Poisson stochastic integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`
admits a càdlàg modification: there exists `M' : ℝ → Ω → ℝ` equal to
`stochasticIntegral N φ` a.s. at each `t`, with càdlàg paths a.s. The integral is
itself càdlàg, so `M' := stochasticIntegral N φ`. -/
theorem cadlag_modification_exists :
    ∃ M' : ℝ → Ω → ℝ,
      (∀ t : ℝ, ∀ᵐ ω ∂P,
        M' t ω = stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t ω) ∧
      (∀ᵐ ω ∂P,
        ∀ t : ℝ,
          (Filter.Tendsto (fun s => M' s ω) (nhdsWithin t (Set.Ioi t))
              (nhds (M' t ω)))
            ∧ ∃ L : ℝ,
                Filter.Tendsto (fun s => M' s ω) (nhdsWithin t (Set.Iio t))
                  (nhds L)) :=
  ⟨stochasticIntegral N φ h_meas h_progMeas h_sq_int_global,
    fun _ => Filter.Eventually.of_forall (fun _ => rfl),
    stochasticIntegral_cadlag N φ h_meas h_progMeas h_sq_int_global⟩

end Integral

/-- **CITED AXIOM (Tier 1 #18): L²-isometry for the *difference* of two
compensated-Poisson Itô-Lévy integrals.**

For two jointly-measurable, progressively-measurable, L²-bounded
integrands `φ₁, φ₂ : Ω → ℝ → E → ℝ`, the difference
`M¹_T - M²_T := ∫_0^T ∫_E φ₁ Ñ - ∫_0^T ∫_E φ₂ Ñ` satisfies the
L²-isometry against the *integrand difference*:

  `𝔼 |M¹_T - M²_T|² = 𝔼 ∫_0^T ∫_E |φ₁(s, e) - φ₂(s, e)|² ν(de) ds`.

This is a standard consequence of L²-linearity + isometry of the L²
Itô-Lévy integral as a continuous linear isometry from
`L²(Ω × [0, T] × E, dP ⊗ ds ⊗ dν)` to `L²(Ω, dP)`. `stochasticIntegral N φ`
is the càdlàg modification of the `L²` integral process of `φ`, and the
difference isometry is to be derived from the cross-difference isometry of
the mark-step approximants of the two integrands (the route that discharged
the Brownian-side `itoIsometry_diff_brownian`, formerly cited axiom #17);
until then it is stated as a separate axiom.

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*,
2nd ed., CUP 2009, **Theorem 4.2.3** — the L²-Itô-Lévy integral is
constructed as the unique continuous linear extension from simple
predictable processes (Applebaum 4.2.3 step (II): the map
`φ ↦ I(φ)` is a linear isometry from `H²([0,T], E)` to `L²(Ω, ℱ_T, P)`,
where `H²` is the predictable L² space `L²(Ω × [0,T] × E, dP ⊗ ds ⊗ dν)`).
The difference identity is the per-`(φ₁, φ₂)` instance of that linearity
+ isometry: `‖I(φ₁) - I(φ₂)‖_{L²(Ω)}² = ‖I(φ₁ - φ₂)‖_{L²(Ω)}² =
‖φ₁ - φ₂‖_{H²}²`. See also Ikeda-Watanabe **Section II.3** for the same
construction.

**Replacement plan**: the cross-difference isometry of the stage approximants
(`MarkStep.lintegral_integral_sub_sq_at` on a common dyadic refinement) and the
`L²`-limits of both sides. Tracked in `tools/cited_axioms.md` Tier 1 #18. -/
axiom itoIsometry_diff_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (h_meas₁ : Measurable (fun (p : Ω × ℝ × E) => φ₁ p.1 p.2.1 p.2.2))
    (h_meas₂ : Measurable (fun (p : Ω × ℝ × E) => φ₂ p.1 p.2.1 p.2.2))
    (h_progMeas₁ : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2))
    (h_progMeas₂ : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2))
    (h_sq_int_global₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_sq_int_global₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (_hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T ω
              - stochasticIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T ω‖₊
            : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P


end LevyStochCalc.Poisson.Compensated
