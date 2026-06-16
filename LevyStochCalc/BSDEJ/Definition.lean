/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Multidim
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Poisson.L2Isometry
import LevyStochCalc.Poisson.NaturalFiltration

/-!
# BSDEJ structure and solution predicate

A *Backward Stochastic Differential Equation with Jumps* (BSDEJ) is a triple
`(Y, Z, U)` of adapted processes satisfying

  `Y_t = g(X_T) + ∫_t^T f(s, X_{s-}, Y_{s-}, Z_s, U_s) ds`
       `   − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`,

where `f : [0,T] × ℝⁿ × ℝ × ℝ^d × L²(ν) → ℝ` is the *generator* (driver) and
`g : ℝⁿ → ℝ` is the *terminal condition*. `Y` is scalar, `Z` is `d`-dimensional
matching `W`, and `U_s : E → ℝ` is the *jump integrand*. The references used
here (Tang–Li 1994, Bouchard–Elie 2008, Pardoux–Răşcanu, Andersson–Gnoatto–
Patacca–Picarelli 2025) all treat scalar `Y`; vector-`Y` BSDEJs need a
different existence/uniqueness apparatus and are out of scope.

## The solution space

`IsBSDEJSolution` formalises the literature solution space `S² × H² × H²_N`:

* `Y ∈ S²`: jointly measurable, L²-sup-bounded, and a.s. càdlàg. The càdlàg
  paths are what make the L²-supremum `⨆_{t ∈ [0,T]} ‖Y_t‖²` an honest
  measurable function of `ω`.
* `Z ∈ H²` and each mark-slice `s ↦ U_s(e) ∈ H²_N`: L²-integrable and
  progressively measurable (`IsStronglyProgressive`).
* The equation is expressed through two martingale legs `M_W, M_N` *pinned*
  to the canonical integrals — `M_W` to the multidim Brownian Itô integral of
  `Z`, `M_N` to the compensated-Poisson L² integral of `U` — rather than to
  arbitrary L²-isometric stand-ins. Both are martingales for the same
  filtration `Filt`, pinned to the right-continuous augmentation of
  `σ(W, N) = (⨆ᵢ σ(W_i)) ∨ σ(N)`.

Adaptedness is essential, not cosmetic: for `f = 0, g = 0` the non-adapted
process `Y_t = W¹_T − W¹_t` solves the equation (with `Z ≡ 1`, `U = 0`), so
without adaptedness the uniqueness clause of an existence/uniqueness statement
would be unsatisfiable. Pinning `Filt` to the canonical filtration and
requiring `Y` adapted excludes it, since `W¹_T` is not `Filt_t`-measurable for
`t < T`; then `Y_t = 𝔼[Y_t | Filt_t] = 0` from the martingale property of
`M_W, M_N`.

`IsStronglyProgressive` is the closest Mathlib analogue of the literature's
"predictable": progressive ⊇ predictable in general, but the L² Itô and
Itô–Lévy integrals are defined on progressively-measurable integrands and are
insensitive to a.e. modifications, and every progressive L² process is
a.e.-equal to a predictable one (predictable projection; Dellacherie–Meyer
VI.45, Protter IV.57). So the formalised solution space coincides with the
literature one modulo this identification.

## Structural regression tests

The extractor theorems below (`filtration_eq_canonical`, `Y_cadlag`,
`Y_adapted_canonical`, `Z_isStronglyProgressive_canonical`,
`U_isStronglyProgressive_canonical`, `M_W_eq_canonical_brownianIto`,
`M_N_eq_canonical_compensatedPoisson`) each extract one strengthening of the
predicate as a public lemma. They double as a compile-time guard: weakening
the predicate (relaxing the `Filt` pin, demoting `IsStronglyProgressive` to
`Adapted`, dropping the canonical-integral pins, or removing `Y`'s càdlàg
paths) makes them fail to elaborate, breaking the build. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Definition

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- BSDEJ data: terminal condition `g` and generator `f`, with the
measurability of each carried as a structural field.

`Y` is scalar-valued (`g : (Fin n → ℝ) → ℝ`, `f` returns `ℝ`), matching the
scalar-`Y` literature (Tang–Li 1994 SIAM J. Control Optim. 32(5) Thm 3.1;
Bouchard–Elie 2008 SPA 118(1) Thm 2.1; Andersson–Gnoatto–Patacca–Picarelli
2025 arXiv:2211.04349 Thm 2.4). A vector-`Y` generalisation would add a
dimension `m` and change `g`/`f` to return `Fin m → ℝ`; it is out of scope.

The `f_measurable`/`g_measurable` fields prevent `IsBSDEJSolution` from being
evaluated on non-measurable drivers, where the Bochner integral would default
to `0` and make the equation `Y_t = g + 0` trivially solvable:
- `g : (Fin n → ℝ) → ℝ` is Borel-measurable in `x`;
- `f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` is jointly
  measurable in its five arguments for the product σ-algebra on
  `ℝ × (Fin n → ℝ) × ℝ × (Fin d → ℝ) × (E → ℝ)` (the `(E → ℝ)` slot carries
  the product σ-algebra, matching the `Ψ_t = ∫ U_t(z) ν(dz)` channel). -/
structure BSDEJData (n d : ℕ) (E : Type v) where
  /-- Generator `f(t, x, y, z, u)`. -/
  f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ
  /-- Terminal condition `g(x)`. -/
  g : (Fin n → ℝ) → ℝ
  /-- `g` is Borel-measurable. -/
  g_measurable : Measurable g
  /-- `f` is jointly measurable in `(t, x, y, z, u)`. The 5-arg product
  σ-algebra is the canonical one on
  `ℝ × (Fin n → ℝ) × ℝ × (Fin d → ℝ) × (E → ℝ)`. -/
  f_measurable : Measurable
    (fun (p : ℝ × (Fin n → ℝ) × ℝ × (Fin d → ℝ) × (E → ℝ)) =>
      f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- Predicate: `(Y, Z, U)` solves the BSDEJ with data `bsdej`, driven by
`(W, N)` and the forward process `X`, on the time horizon `[0, T]`.

The conclusion is built from two process martingales `M_W, M_N` pinned to the
canonical Brownian Itô integral of `Z` and the compensated-Poisson integral of
`U`. See the module docstring for the solution space `S² × H² × H²_N` and the
adaptedness discussion. -/
def IsBSDEJSolution
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (Y : ℝ → Ω → ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (U : ℝ → Ω → E → ℝ)
    (T : ℝ) : Prop :=
  Measurable (Function.uncurry Y)
    ∧ (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    ∧ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    ∧ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    -- Y ∈ S²: a.s. càdlàg paths (right-continuous with left limits), which
    -- make the L²-supremum `⨆ t ∈ [0,T] ‖Y_t‖²` honestly measurable in ω.
    ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
          ∧ ∃ L : ℝ,
              Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
    -- Adaptedness layer. `Filt` is pinned to the right-continuous augmentation
    -- of `σ(W, N) = (⨆ i, naturalFiltration (W.W i)) ⊔ naturalFiltration N`
    -- (the literature filtration; `.rightCont` is needed for Doob's
    -- L²-maximal, optional stopping, and the càdlàg modification). Pinning by
    -- equality, not by `≤ Filt`, avoids the vacuous `Filt = ⊤`. M_W is pinned
    -- to the canonical Brownian Itô integral of Z, so the per-component Z
    -- hypotheses are bundled inside the existential to type that integral.
    ∧ (∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
        Filt = ((⨆ i : Fin d,
                  LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i))
                  ⊔ LevyStochCalc.Poisson.naturalFiltration N).rightCont ∧
        -- H²/H²_N legs: Z and each mark-slice `s ↦ U s ω e` are progressively
        -- measurable; Y stays `Adapted` (it is the S² càdlàg leg).
        MeasureTheory.Adapted Filt Y ∧
        MeasureTheory.IsStronglyProgressive Filt Z ∧
        (∀ e : E, MeasureTheory.IsStronglyProgressive Filt (fun s ω => U s ω e)) ∧
        ∃ M_W M_N : ℝ → Ω → ℝ,
          Measurable (Function.uncurry M_W) ∧
          Measurable (Function.uncurry M_N) ∧
          MeasureTheory.Adapted Filt M_W ∧
          MeasureTheory.Adapted Filt M_N ∧
          -- M_W pinned to the canonical multidim Brownian Itô integral of Z;
          -- the Z hypotheses (per-component measurability / progressive
          -- measurability / L²-bound) are bundled here to type the integral.
          (∃ (h_Z_meas : ∀ i : Fin d,
                Measurable (Function.uncurry (fun ω s => Z s ω i)))
             (h_Z_progMeas : ∀ i : Fin d, ∀ t : ℝ,
                @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
                  (@Prod.instMeasurableSpace Ω ℝ
                    ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i)).seq t)
                    inferInstance)
                  (fun p : Ω × ℝ => Z p.2 p.1 i))
             (h_Z_sq : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
                ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
                  (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
            ∀ T' : ℝ, ∀ᵐ ω ∂P,
              M_W T' ω =
                LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
                  W Z h_Z_meas h_Z_progMeas h_Z_sq T' ω) ∧
          -- M_N pinned to the canonical compensated-Poisson L² integral of U;
          -- the U-side hypotheses are bundled here likewise (mirror of M_W).
          (∃ (h_U_meas : Measurable
                (fun (p : Ω × ℝ × E) =>
                  (fun ω' s e => U s ω' e) p.1 p.2.1 p.2.2))
             (h_U_progMeas : ∀ t : ℝ,
                @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
                  (@Prod.instMeasurableSpace Ω (ℝ × E)
                    ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
                    inferInstance)
                  (fun p : Ω × ℝ × E => (fun ω' s e => U s ω' e) p.1 p.2.1 p.2.2))
             (h_U_sq : ∀ T' : ℝ, 0 < T' →
                ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
                  (‖(fun ω' s e => U s ω' e) ω s e‖₊ : ℝ≥0∞) ^ 2
                    ∂ν ∂volume ∂P < ⊤),
            ∀ T' : ℝ, ∀ᵐ ω ∂P,
              M_N T' ω =
                LevyStochCalc.Poisson.Compensated.stochasticIntegral N
                  (fun ω' s e => U s ω' e) h_U_meas h_U_progMeas h_U_sq T' ω) ∧
          -- M_W and M_N are martingales w.r.t. the same Filt:
          MeasureTheory.Martingale M_W Filt P ∧
          MeasureTheory.Martingale M_N Filt P ∧
          -- BSDEJ equation at every t, with the same (M_W, M_N):
          (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
            Y t ω = bsdej.g (X T ω)
              + ∫ s in Set.Icc t T,
                  bsdej.f s (X s ω) (Y s ω) (Z s ω) (U s ω)
              - (M_W T ω - M_W t ω) - (M_N T ω - M_N t ω)))

/-! ## Structural regression tests for `IsBSDEJSolution`

These extractor theorems guard the predicate's literature-strength conjuncts.
Weakening the predicate (relaxing the `Filt` pin to a `≤ Filt` constraint,
demoting `IsStronglyProgressive` back to `Adapted`, removing the
canonical-integral pins on `M_W`/`M_N`, or dropping the càdlàg paths on `Y`)
makes them fail to elaborate, breaking the build — catching exactly the
non-uniqueness an adaptedness-free predicate admits (`Y₁ = 0` and
`Y₂ = W_T − W_t` would both qualify).

Each test extracts a single strengthening as a public lemma, so it is both
(a) consumable by downstream callers needing that strengthening and (b) a
build-time regression check on the predicate's surface API. -/

namespace IsBSDEJSolution

variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {ν : Measure E} [SigmaFinite ν]
variable {n d : ℕ}
variable {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
variable {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
variable {bsdej : BSDEJData n d E}
variable {X : ℝ → Ω → (Fin n → ℝ)}
variable {Y : ℝ → Ω → ℝ}
variable {Z : ℝ → Ω → (Fin d → ℝ)}
variable {U : ℝ → Ω → E → ℝ}
variable {T : ℝ}

/-- **Regression test #1 (Filt pin)**: The filtration witnessed by an
`IsBSDEJSolution` is exactly the right-continuous augmentation of the join of
`W`'s component natural filtrations with `N`'s natural filtration. Pinning by
equality (rather than allowing any `Filt` containing the natural one, which
`Filt = ⊤` satisfies vacuously) forces the literature-correct filtration and
preserves the adaptedness rule-out of the `Y = W_T − W_t` non-solution. -/
theorem filtration_eq_canonical
    (h : IsBSDEJSolution W N bsdej X Y Z U T) :
    ∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      Filt = ((⨆ i : Fin d,
                  LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i))
                  ⊔ LevyStochCalc.Poisson.naturalFiltration N).rightCont := by
  obtain ⟨_, _, _, _, _, Filt, hFilt_eq, _⟩ := h
  exact ⟨Filt, hFilt_eq⟩

/-- **Regression test #2 (càdlàg Y)**: The `Y` component of every solution
has a.s.-càdlàg paths (right-continuous with left limits at every point).
This is the Tang-Li / Pardoux-Răşcanu `S²` solution-space requirement,
without which the L²-supremum `⨆ t ∈ [0,T] ‖Y t‖²` is not honestly
measurable as a function of ω. -/
theorem Y_cadlag
    (h : IsBSDEJSolution W N bsdej X Y Z U T) :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
        ∧ ∃ L : ℝ,
            Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L) := by
  obtain ⟨_, _, _, _, h_cadlag, _⟩ := h
  exact h_cadlag

/-- **Regression test #3 (Y adapted to canonical Filt)**: The `Y`
component is `Filt`-adapted where `Filt` is the canonical filtration. -/
theorem Y_adapted_canonical
    (h : IsBSDEJSolution W N bsdej X Y Z U T) :
    ∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      Filt = ((⨆ i : Fin d,
                  LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i))
                  ⊔ LevyStochCalc.Poisson.naturalFiltration N).rightCont ∧
      MeasureTheory.Adapted Filt Y := by
  obtain ⟨_, _, _, _, _, Filt, hFilt_eq, hY_adapted, _⟩ := h
  exact ⟨Filt, hFilt_eq, hY_adapted⟩

/-- **Regression test #4 (Z strongly progressive)**: The `Z` component is
`IsStronglyProgressive` w.r.t. the canonical filtration (strictly stronger
than per-`t` adaptedness). This is the Tang–Li / Pardoux–Răşcanu H²
solution-space requirement: H² is the L² space of progressively measurable
processes. -/
theorem Z_isStronglyProgressive_canonical
    (h : IsBSDEJSolution W N bsdej X Y Z U T) :
    ∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      Filt = ((⨆ i : Fin d,
                  LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i))
                  ⊔ LevyStochCalc.Poisson.naturalFiltration N).rightCont ∧
      MeasureTheory.IsStronglyProgressive Filt Z := by
  obtain ⟨_, _, _, _, _, Filt, hFilt_eq, _, hZ_prog, _⟩ := h
  exact ⟨Filt, hFilt_eq, hZ_prog⟩

/-- **Regression test #5 (U strongly progressive per mark)**: For every
mark `e : E`, the per-mark slice `s ↦ U s · e` is `IsStronglyProgressive`
w.r.t. the canonical filtration (H²_N solution-space requirement). -/
theorem U_isStronglyProgressive_canonical
    (h : IsBSDEJSolution W N bsdej X Y Z U T) :
    ∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      Filt = ((⨆ i : Fin d,
                  LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i))
                  ⊔ LevyStochCalc.Poisson.naturalFiltration N).rightCont ∧
      ∀ e : E, MeasureTheory.IsStronglyProgressive Filt (fun s ω => U s ω e) := by
  obtain ⟨_, _, _, _, _, Filt, hFilt_eq, _, _, hU_prog, _⟩ := h
  exact ⟨Filt, hFilt_eq, hU_prog⟩

/-- **Regression test #6 (M_W pinned to canonical Brownian Itô integral)**:
The Brownian martingale leg `M_W` of every solution agrees a.s. (at every
T') with the canonical multidim Brownian Itô integral
`MultidimBrownianMotion.stochasticIntegral W Z ...` — not merely with some
L²-isometric stand-in (which would leave a gap between the predicate and the
literature claim). The per-component Z hypotheses are bundled as existential
witnesses to make the canonical-integral expression well-typed. -/
theorem M_W_eq_canonical_brownianIto
    (h : IsBSDEJSolution W N bsdej X Y Z U T) :
    ∃ M_W : ℝ → Ω → ℝ,
      ∃ (h_Z_meas : ∀ i : Fin d,
            Measurable (Function.uncurry (fun ω s => Z s ω i)))
         (h_Z_progMeas : ∀ i : Fin d, ∀ t : ℝ,
            @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
              (@Prod.instMeasurableSpace Ω ℝ
                ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i)).seq t)
                inferInstance)
              (fun p : Ω × ℝ => Z p.2 p.1 i))
         (h_Z_sq : ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
              (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
        ∀ T' : ℝ, ∀ᵐ ω ∂P,
          M_W T' ω =
            LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
              W Z h_Z_meas h_Z_progMeas h_Z_sq T' ω := by
  obtain ⟨_, _, _, _, _, _Filt, _, _, _, _,
          M_W, _, _, _, _, _,
          ⟨h_Z_meas, h_Z_progMeas, h_Z_sq, hM_W_pin⟩, _, _, _, _⟩ := h
  exact ⟨M_W, h_Z_meas, h_Z_progMeas, h_Z_sq, hM_W_pin⟩

/-- **Regression test #7 (M_N pinned to canonical compensated-Poisson
integral)**: The Poisson martingale leg `M_N` of every solution agrees a.s.
(at every T') with the canonical compensated-Poisson L² integral
`Compensated.stochasticIntegral N U ...` — not merely with some
L²-isometric stand-in. The U-side hypotheses are bundled as existential
witnesses to make the canonical-integral expression well-typed (per-mark
adaptedness of `U` alone would not type-check the canonical compensator). -/
theorem M_N_eq_canonical_compensatedPoisson
    (h : IsBSDEJSolution W N bsdej X Y Z U T) :
    ∃ M_N : ℝ → Ω → ℝ,
      ∃ (h_U_meas : Measurable
            (fun (p : Ω × ℝ × E) =>
              (fun ω' s e => U s ω' e) p.1 p.2.1 p.2.2))
         (h_U_progMeas : ∀ t : ℝ,
            @MeasureTheory.StronglyMeasurable (Ω × ℝ × E) ℝ _
              (@Prod.instMeasurableSpace Ω (ℝ × E)
                ((LevyStochCalc.Poisson.naturalFiltration N).seq t)
                inferInstance)
              (fun p : Ω × ℝ × E => (fun ω' s e => U s ω' e) p.1 p.2.1 p.2.2))
         (h_U_sq : ∀ T' : ℝ, 0 < T' →
            ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
              (‖(fun ω' s e => U s ω' e) ω s e‖₊ : ℝ≥0∞) ^ 2
                ∂ν ∂volume ∂P < ⊤),
        ∀ T' : ℝ, ∀ᵐ ω ∂P,
          M_N T' ω =
            LevyStochCalc.Poisson.Compensated.stochasticIntegral N
              (fun ω' s e => U s ω' e) h_U_meas h_U_progMeas h_U_sq T' ω := by
  obtain ⟨_, _, _, _, _, _Filt, _, _, _, _,
          _, M_N, _, _, _, _,
          _, ⟨h_U_meas, h_U_progMeas, h_U_sq, hM_N_pin⟩, _, _, _⟩ := h
  exact ⟨M_N, h_U_meas, h_U_progMeas, h_U_sq, hM_N_pin⟩

end IsBSDEJSolution

end LevyStochCalc.BSDEJ.Definition
