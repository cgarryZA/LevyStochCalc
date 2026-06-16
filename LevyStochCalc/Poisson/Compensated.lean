/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.RandomMeasure
import LevyStochCalc.Poisson.NaturalFiltration
import Mathlib.Probability.Martingale.Basic

/-!
# Compensated Poisson L²-Itô–Lévy integral

The L²-Itô–Lévy integral against the compensated Poisson random measure `Ñ`,
with its martingale, quadratic-variation, isometry, and càdlàg properties. The
integral is the L²-completion of the simple-integrand integral built in
`Poisson/CompensatedSimple.lean` (Applebaum 2009 §4.2, Stage 3).

`stochasticIntegral` is obtained by `Classical.choose` on the unified-existence
axiom `itoIsometry_compensated_unified_existence` (cited axiom #6), which packages
the martingale property, quadratic variation, L²-isometry, and a càdlàg
modification in one 4-conjunct existential. Consequently `itoLevyIsometry`,
`quadVar_stochasticIntegral`, `martingale_stochasticIntegral`,
`cadlag_modification_exists`, and `L2Isometry.itoLevyIsometry` are proven theorems
forwarding to its conjuncts.

`itoIsometry_diff_compensated` (cited axiom #18) is the per-difference L²-isometry
for this integral — a standard consequence of L²-linearity and isometry (Applebaum
Thm 4.2.3 step II). It is stated separately because the `Classical.choose`-built
`stochasticIntegral` does not expose linearity directly; it is consumed by
`Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise` and mirrors
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

/-- **CITED AXIOM: Unified L²-Itô-Lévy integral with martingale + quadVar + isometry
+ càdlàg.**

For predictable square-integrable `φ : Ω → ℝ → E → ℝ`, there exists a process
`F : ℝ → Ω → ℝ` and a filtration `Filt` such that:

* `F` is a martingale wrt `Filt`,
* `(F t)² − ∫_0^t ∫_E |φ(s, e)|² ν(de) ds` is a martingale wrt `Filt`
  (quadVar identity),
* `∫⁻ ω, ‖F T‖₊² ∂P`
  `= ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖φ ω s e‖₊² ∂ν ∂volume ∂P`
  for every `T > 0` with `h_meas + h_sq_int` (L²-isometry),
* `F` has a càdlàg modification.

`F` is the canonical L²-Itô-Lévy integral `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`.
Consolidates Applebaum 2009 Thm 4.2.3 + Thm 4.2.4.

The integrand hypotheses (`h_meas` joint measurability on `Ω×ℝ×E`,
`h_progMeas` progressive measurability w.r.t. `(naturalFiltration N).seq t`,
`h_sq_int_global` a global L² bound) are taken as *outer* hypotheses, mirroring
the Brownian-side axiom #5; the existential body is then unconditional on them.
This matches Applebaum Thm 4.2.3's predictable-`φ` hypothesis class and prevents
a `Measurable`-only `F ≡ 0` from satisfying the conjuncts vacuously. `Filt` is
pinned to `(naturalFiltration N).rightCont`, ruling out trivial-filtration
witnesses such as `Filt = const ⊤`.

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed.,
CUP 2009, **Theorem 4.2.3** (martingale + quadratic variation + L²-isometry of
the L² Itô-Lévy integral) + **Theorem 4.2.4** (càdlàg modification); Ikeda &
Watanabe, *SDEs and Diffusion Processes*, 2nd ed., North-Holland 1989, **Section
II.3**.

**Standard proof outline**: Construct `F` as the L²-limit of
`simpleIntegral N (G n) t` for an adapted Cauchy approximating sequence
(`adaptedSimple_dense_L2_compensated` + `cauchySeq_simpleIntegralLp_compensated`).
Each `simpleIntegral N (G n) ·` is a martingale (independence of disjoint
compensated-Poisson increments + zero-mean compensation). The L²-limit of
martingales is a martingale via L²-continuity of conditional expectation.
The quadVar identity holds at simple level via `simpleIntegral_offDiagonal` +
`compensated_second_moment` and passes to the limit. The L²-isometry is
preserved through `Filter.limUnder` (already proven for the per-T case via
`itoIntegralLp_compensated_L2_isometry`). The càdlàg modification follows from
Doob's L²-maximal inequality applied to the simpleIntegral approximations
(piecewise constant in t, hence càdlàg; the L²-limit inherits a càdlàg
modification).

**Replacement plan**: when the unified F-construction-across-all-t is fully
formalized for Compensated (mirror of the analogous Brownian-side construction),
this `axiom` becomes a `theorem`. Tracked in `tools/cited_axioms.md` Tier 1. -/
axiom itoIsometry_compensated_unified_existence
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
    -- Outer integrand hypotheses (mirroring the Brownian-side axiom): callers
    -- supply joint Ω×ℝ×E measurability, progressive measurability, and a global
    -- L² bound — per-mark adaptedness of the integrand alone would not suffice.
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int_global : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    -- `Filt` pinned to `(naturalFiltration N).rightCont` (parallel to the
    -- Brownian-side axiom), closing the trivial-filtration-witness route.
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
              Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Iio t)) (nhds L))

/-- The *L² stochastic integral* `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` against
the compensated measure of a Poisson random measure.

Defined via `Classical.choose` on the 4-conjunct unified-existence axiom
`itoIsometry_compensated_unified_existence` (martingale + quadVar + isometry +
càdlàg); the resulting `F` is the canonical L²-Itô-Lévy integral. -/
noncomputable def stochasticIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
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
    (T : ℝ) : Ω → ℝ :=
  (Classical.choose
    (itoIsometry_compensated_unified_existence N φ h_meas h_progMeas h_sq_int_global)) T

/-- Itô-Lévy L² isometry on the bounded interval `[0, T]`.

  `𝔼[ (∫_0^T ∫_E φ(s, e) Ñ(ds, de))² ] = 𝔼[ ∫_0^T ∫_E |φ(s, e)|² ν(de) ds ]`

ENNReal form. Forwards to the L²-isometry conjunct of the unified-existence
axiom #6. -/
theorem itoLevyIsometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
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
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N φ h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P := by
  unfold stochasticIntegral
  exact (Classical.choose_spec
    (itoIsometry_compensated_unified_existence N φ h_meas h_progMeas h_sq_int_global)
      ).choose_spec.2.2.2.1 T hT

/-- **Quadratic variation of the L² Itô-Lévy integral.**

For predictable square-integrable `φ`, the process
`t ↦ (M_t)² − ∫_0^t ∫_E |φ(s, e)|² ν(de) ds` is a martingale, where
`M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the L² Itô-Lévy integral.

Extracts conjunct 2 (quadratic variation) of the unified-existence axiom #6. -/
theorem quadVar_stochasticIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int_global : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν)
        F P := by
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (itoIsometry_compensated_unified_existence N φ h_meas h_progMeas h_sq_int_global)
      ).choose,
    (Classical.choose_spec
      (itoIsometry_compensated_unified_existence N φ h_meas h_progMeas h_sq_int_global)
        ).choose_spec.2.2.1⟩

/-- **The L² Itô-Lévy integral is a martingale.**

The compensated-Poisson stochastic integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`
is a square-integrable martingale w.r.t. the natural filtration of `N`.

Extracts conjunct 1 (martingale property) of the unified-existence axiom #6. -/
theorem martingale_stochasticIntegral
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int_global : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t) F P := by
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (itoIsometry_compensated_unified_existence N φ h_meas h_progMeas h_sq_int_global)
      ).choose,
    (Classical.choose_spec
      (itoIsometry_compensated_unified_existence N φ h_meas h_progMeas h_sq_int_global)
        ).choose_spec.2.1⟩

/-- **Càdlàg modification of L² Itô-Lévy integral.**

The compensated-Poisson stochastic integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`
admits a càdlàg modification: there exists `M' : ℝ → Ω → ℝ` equal to
`stochasticIntegral N φ` a.s. at each `t`, with càdlàg paths a.s.

The unified `F` from the existence axiom #6 already has càdlàg paths
(conjunct 4); take `M' := stochasticIntegral N φ` (the unified `F` by
construction), so per-`t` equality is `rfl` and the càdlàg property extracts. -/
theorem cadlag_modification_exists
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
        (@Prod.instMeasurableSpace Ω (ℝ × E)
          ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
          inferInstance)
        (fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2))
    (h_sq_int_global : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ M' : ℝ → Ω → ℝ,
      (∀ t : ℝ, ∀ᵐ ω ∂P,
        M' t ω = stochasticIntegral N φ h_meas h_progMeas h_sq_int_global t ω) ∧
      (∀ᵐ ω ∂P,
        ∀ t : ℝ,
          (Filter.Tendsto (fun s => M' s ω) (nhdsWithin t (Set.Ioi t))
              (nhds (M' t ω)))
            ∧ ∃ L : ℝ,
                Filter.Tendsto (fun s => M' s ω) (nhdsWithin t (Set.Iio t))
                  (nhds L)) := by
  refine ⟨stochasticIntegral N φ h_meas h_progMeas h_sq_int_global,
    fun t => Filter.Eventually.of_forall (fun _ => rfl), ?_⟩
  unfold stochasticIntegral
  exact (Classical.choose_spec
    (itoIsometry_compensated_unified_existence N φ h_meas h_progMeas h_sq_int_global)
      ).choose_spec.2.2.2.2

/-- **CITED AXIOM (Tier 1 #18): L²-isometry for the *difference* of two
compensated-Poisson Itô-Lévy integrals.**

For two jointly-measurable, progressively-measurable, L²-bounded
integrands `φ₁, φ₂ : Ω → ℝ → E → ℝ`, the difference
`M¹_T - M²_T := ∫_0^T ∫_E φ₁ Ñ - ∫_0^T ∫_E φ₂ Ñ` satisfies the
L²-isometry against the *integrand difference*:

  `𝔼 |M¹_T - M²_T|² = 𝔼 ∫_0^T ∫_E |φ₁(s, e) - φ₂(s, e)|² ν(de) ds`.

This is a standard consequence of L²-linearity + isometry of the L²
Itô-Lévy integral as a continuous linear isometry from
`L²(Ω × [0, T] × E, dP ⊗ ds ⊗ dν)` to `L²(Ω, dP)`. In the present
axiomatization, `stochasticIntegral N φ` is constructed via
`Classical.choose` on `itoIsometry_compensated_unified_existence`
(Tier 1 #6), which does not expose linearity directly (each integrand
gets an independent existence witness, so the "difference of choices"
and "choice of difference" are not syntactically equal). We therefore
state this difference-form isometry as a separate axiom, mirroring the
analogous Brownian-side `itoIsometry_diff_brownian` (cited axiom #17).

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

**Replacement plan**: derive as a theorem from a Mathlib-level linearity
result on the L²-Itô-Lévy integral when that machinery becomes available
(blocked on Mathlib gaining the compensated-Poisson L²-integral).
Tracked in `tools/cited_axioms.md` Tier 1 #18. -/
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
