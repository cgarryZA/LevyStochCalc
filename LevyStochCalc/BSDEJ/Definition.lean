/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Ito
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Poisson.L2Isometry
import LevyStochCalc.Poisson.NaturalFiltration

/-!
# Layer 3 substrate: Continuous BSDEJ structure

A *Backward Stochastic Differential Equation with Jumps* (BSDEJ) is a triple
`(Y, Z, U)` of adapted processes satisfying

  `Y_t = g(X_T) + ∫_t^T f(s, X_{s-}, Y_{s-}, Z_s, U_s) ds`
       `   − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`,

where `f : [0,T] × ℝⁿ × ℝ × ℝ^d × L²(ν) → ℝ` is the *generator* (or driver)
and `g : ℝⁿ → ℝ` is the *terminal condition*. `Y` is scalar, `Z` is `d`-dim
matching `W`, `U_s : E → ℝ` is the *jump integrand*.

Reference: User's dissertation
[ch02_mathematical_framework.tex](
D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex)
Definition 2 (line 238 onwards).

## Status

**Strengthened predicate (2026-05-11 recursive audit fix).** Previous
version had a vacuous per-`(t, ω)` existential

  `∃ (BM_term jump_term : ℝ), Y t ω = g + ∫f - BM_term - jump_term`

which is satisfiable by ANY L²-bounded `(Y, Z, U)`. Replaced with an
OUTER existential `∃ M_W M_N : ℝ → Ω → ℝ` of process martingales
pinned to `Z, U`.

**Re-strengthened (2026-05-21, red-team P05 + P12 fix).** The
2026-05-11 strengthening was incomplete. Persona 12 of the 12-persona
red team constructed a concrete counterexample to the
`continuousBSDEJ_exists_unique` axiom for `(f=0, g=0)`:

* `Y₁ t ω := 0` with `Z = U = 0`, `M_W = M_N = 0`,
* `Y₂ t ω := W₁_T ω - W₁_t ω` with `Z s ω = 1`, `U = 0`,
  `M_W = -W₁`, `M_N = 0`.

Both `(Y₁, Z₁, U₁)` and `(Y₂, Z₂, U₂)` satisfy the 2026-05-11
strengthened predicate (Y is L²-bounded; M_W is L²-isometric to Z and a
martingale; M_N pins to `Compensated.stochasticIntegral N 0 ≡ 0`; the
equation holds). So the predicate had multiple distinct "solutions",
and `continuousBSDEJ_exists_unique`'s `∃ Y, ∀ Y', sol Y' → Y =ᵃᵉ Y'`
clause was unsatisfiable — i.e. the axiom was **mathematically false
as stated**.

The 2026-05-21 fix adds an **adaptedness** layer: an outer
`∃ Filt : Filtration ℝ ‹MeasurableSpace Ω›` such that

* `Y` is `Filt`-adapted (each `Y t` is `(Filt t)`-measurable),
* `Z` is `Filt`-adapted (each `Z t` is `(Filt t)`-measurable, valued in
  `Fin d → ℝ` with its product σ-algebra),
* `U` is pointwise-in-mark `Filt`-adapted: for every `e : E`, the
  process `s ↦ U s · e` is `Filt`-adapted,
* `M_W, M_N` are both `Filt`-adapted and `Filt`-martingales.

`Y₂ t ω = W₁_T ω - W₁_t ω` is excluded because for `t < T`, `W₁_T` is
not `(Filt t)`-measurable for any filtration containing `W`'s natural
filtration. Under adaptedness, the BSDEJ equation `Y_t = -(M_W T − M_W
t) - (M_N T − M_N t)` (for `f=0, g=0`) combined with `M_W, M_N` being
`Filt`-martingales forces `Y_t = E[Y_t | (Filt t)] = -E[M_W T − M_W t
| (Filt t)] - E[M_N T − M_N t | (Filt t)] = 0`. Uniqueness for `(f=0,
g=0)` is therefore restored at the predicate level; the literature
Tang–Li uniqueness covers the general Lipschitz case once the
predicate is honest.

**Predicate hardening complete (2026-05-24, Cu01 forwarder bullet-proof
pass)**. The previous "remaining slack" note (M_W only L²-isometric) is
RESOLVED: M_W is now pinned to the canonical multidim Brownian Itô
integral `MultidimBrownianMotion.stochasticIntegral W Z h_Z_meas
h_Z_progMeas h_Z_sq` (commit 2026-05-22), and M_N is pinned to the
canonical compensated-Poisson L² integral `Compensated.stochasticIntegral
N U h_U_meas h_U_progMeas h_U_sq` (commit 2026-05-23). The Filt witness
is pinned EXACTLY to `((⨆ i, naturalFiltration W_i) ⊔ naturalFiltration
N).rightCont` (M11-CRIT fix, 2026-05-23, P12 F1 closure), Z and U_e are
strengthened to `IsStronglyProgressive` (P4 F1 fix, 2026-05-23), and Y
carries a càdlàg-paths field (P4 H fix, 2026-05-23). Every conjunct is
load-bearing for the literature `S² × H² × H²_N` solution space.

**Structural regression canary**: the extractor theorems
`filtration_eq_canonical`, `Y_cadlag`, `Y_adapted_canonical`,
`Z_isStronglyProgressive_canonical`, `U_isStronglyProgressive_canonical`,
`M_W_eq_canonical_brownianIto`, `M_N_eq_canonical_compensatedPoisson`
below this docstring guard each of the seven hardening targets via a
public extractor. If anyone weakens the predicate (e.g., relaxes the Filt
pin to `≤`, demotes IsStronglyProgressive to Adapted, removes the
canonical-integral pins on M_W/M_N, or drops the càdlàg paths on Y),
these extractors will fail to elaborate and the build will break. -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Definition

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- BSDEJ data: terminal condition `g`, generator `f`.

**Scope note (red-team M10, 2026-05-22)**: `Y` is scalar-valued
(`g : (Fin n → ℝ) → ℝ` and the `f` driver returns `ℝ`). This matches the
literature references actually used by this library:

* Tang & Li 1994 SIAM J. Control Optim. 32(5), Theorem 3.1 — scalar `Y`.
* Andersson-Gnoatto-Patacca-Picarelli 2025 arXiv:2211.04349 Theorem 2.4 —
  scalar `Y`.
* Bouchard & Elie 2008 SPA 118(1) Theorem 2.1 — scalar `Y`.

Vector-`Y` BSDEJs (reflected, quadratic-growth, FBSDEJ couples) require a
different existence-uniqueness apparatus and are **outside the current
scope**. A vector-`Y` generalization would parameterize this structure by
an additional `m : ℕ` (the `Y`-dimension) and change `g : (Fin n → ℝ) →
(Fin m → ℝ)`, `f : … → (Fin m → ℝ)`. Tracked as future work; not a defect
in the present scalar-`Y` chain.

**Measurability invariants (red-team 2nd audit P12 F4, 2026-05-23)**:
`BSDEJData` now carries `f_measurable` and `g_measurable` as structural
fields, so that downstream `IsBSDEJSolution` cannot be evaluated on
pathological non-measurable drivers (where the Bochner integral
`integral_undef`-defaults to 0, making the BSDEJ equation `Y_t = g + 0`
trivially solvable). Both fields use the joint measurability appropriate
for the integrand role:
- `g : (Fin n → ℝ) → ℝ` is jointly Borel-measurable in `x`.
- `f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` is jointly
  measurable in its 5 arguments (modulo the (E → ℝ) slot which uses the
  product σ-algebra on E-indexed reals — appropriate for the
  `Ψ_t = ∫ U_t(z) ν(dz)` channel). -/
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
  f_measurable : Measurable (fun (p : ℝ × (Fin n → ℝ) × ℝ × (Fin d → ℝ) × (E → ℝ)) =>
    f p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

/-- Predicate: `(Y, Z, U)` solves the BSDEJ with data `bsdej`, driven by
`(W, N)` and the forward process `X`, on the time horizon `[0, T]`.

See module docstring for the 2026-05-11 strengthening that replaced a
vacuous per-`(t, ω)` existential with an outer existential of two
process martingales `M_W, M_N` constrained to `Z, U` via L²-isometry +
direct compensated-Poisson-integral pin. -/
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
    -- 2026-05-23 strengthening (P4 H càdlàg fix): Tang-Li / Pardoux-Răşcanu
    -- solution space `S²` requires Y to be càdlàg-adapted. The previous
    -- joint-measurability-only requirement was strictly weaker (e.g., the
    -- supremum `⨆ t ∈ [0,T] ‖Y_t‖²` above is ill-typed as a measurable
    -- function of ω without càdlàg paths). Adding `Y_cadlag` makes the
    -- supremum honestly measurable and matches the literature S² space.
    ∧ (∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
          ∧ ∃ L : ℝ,
              Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
    -- 2026-05-21 strengthening 1: adaptedness layer (rules out
    -- Y = W₁_T − W₁_t counterexample).
    -- 2026-05-22 strengthening 2 (H2 fix): M_W is now PINNED to the
    -- canonical multidim Brownian Itô integral of Z (not just L²-isometric).
    -- This requires the per-component Z hypotheses (joint measurability,
    -- progressive measurability w.r.t. W's component natural filtrations,
    -- per-component L² bound) to be bundled inside the existential.
    -- 2026-05-23 strengthening 3 (M11-CRIT fix per red-team 2nd-audit P12):
    -- `Filt` was previously existential with the constraint
    -- `naturalFiltration ≤ Filt`, but that constraint is satisfied vacuously
    -- by `Filt = ⊤` (the maximal filtration), defeating the stated
    -- "rule out trivial constant filtrations" purpose. Now pinned EXACTLY
    -- to the **right-continuous augmentation** of the join of natural
    -- filtrations via `Filt = joint_natural.rightCont` inside the existential,
    -- where `joint_natural := (⨆ i, naturalFiltration (W.W i)) ⊔ naturalFiltration N`
    -- (literature `σ(W, N) = ⨆ᵢ σ(W_i) ∨ σ(N)`).
    -- P7 F4 closure (red-team 2nd audit, 2026-05-23): Tang-Li 1994 /
    -- Pardoux-Răşcanu solution space uses the right-continuous augmented
    -- filtration (needed for Doob's L²-maximal, optional stopping, càdlàg
    -- modification). Previous version used the RAW natural filtration —
    -- strictly weaker than literature. `.rightCont` is the Mathlib operator
    -- for right-continuization; the P-null-set augmentation step is a
    -- separate strengthening (deferred — Mathlib lacks a clean primitive).
    ∧ (∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
        Filt = ((⨆ i : Fin d,
                  LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i))
                  ⊔ LevyStochCalc.Poisson.naturalFiltration N).rightCont ∧
        -- P4 F1 fix (red-team 2nd audit, 2026-05-23): Tang-Li 1994 /
        -- Pardoux-Răşcanu 2014 / Bichteler use the solution space
        -- `S² × H² × H²_N` where H² is the L² space of PROGRESSIVELY
        -- MEASURABLE (= ProgMeasurable Filt, equivalent to predictable
        -- under the usual hypotheses on Filt) processes. The previous
        -- `Adapted Filt Z` / `Adapted Filt (fun s ω => U s ω e)` were
        -- per-t measurable only and did NOT imply joint measurability
        -- on the progressive σ-algebra. Strengthened to ProgMeasurable
        -- for Z and U_e (Y stays Adapted since it's the S²-càdlàg leg).
        MeasureTheory.Adapted Filt Y ∧
        MeasureTheory.IsStronglyProgressive Filt Z ∧
        (∀ e : E, MeasureTheory.IsStronglyProgressive Filt (fun s ω => U s ω e)) ∧
        ∃ M_W M_N : ℝ → Ω → ℝ,
          Measurable (Function.uncurry M_W) ∧
          Measurable (Function.uncurry M_N) ∧
          MeasureTheory.Adapted Filt M_W ∧
          MeasureTheory.Adapted Filt M_N ∧
          -- M_W is PINNED to the canonical multidim Brownian Itô integral of Z.
          -- Hypotheses on Z (per-component measurability / progressive measurability
          -- / L²-bound) are bundled inside this existential so that
          -- `MultidimBrownianMotion.stochasticIntegral W Z ... T'` is well-typed.
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
          -- M_N is pinned to the canonical compensated-Poisson L² integral of U.
          -- H6 fix (red-team 2nd audit, 2026-05-23): U-side hypotheses bundled
          -- here (mirror of how M_W bundles h_Z hypotheses). Closes the prior
          -- "hollow M_N pin" issue (Persona 7 F1+F2) where per-e adaptedness
          -- of U was insufficient.
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

These extractor theorems are the structural canary for the `IsBSDEJSolution`
predicate's literature-strength conjuncts. If anyone weakens the predicate
(e.g., relaxes the `Filt` pin to a `≤ Filt` constraint, demotes
`IsStronglyProgressive` back to `Adapted`, removes the canonical-integral
pins on `M_W`/`M_N`, or drops the càdlàg paths on `Y`), these theorems will
fail to elaborate and the build will break — exactly the kind of soundness
regression that the P12 F1 red-team counterexample
(`Y₁ = 0` vs `Y₂ = W_T − W_t` both satisfying a weakened predicate) was
designed to catch.

The tests are deliberately load-bearing: each one extracts a single
strengthening as a public extractor, so it can be both (a) consumed by
downstream callers needing the strengthening, and (b) used as a build-time
regression check on the predicate's surface API. -/

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
`IsBSDEJSolution` is EXACTLY the right-continuous augmentation of the
join of `W`'s component natural filtrations with `N`'s natural filtration.

This is the M11-CRIT fix and the P12 F1 closure: previously, the predicate
allowed any filtration containing the natural one, which is satisfied
vacuously by `Filt = ⊤` — defeating the adaptedness rule-out of the
`Y = W_T − W_t` counterexample. Pinning to the canonical augmentation
forces the literature-correct filtration. -/
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
than per-`t` adaptedness, per the P4 F1 fix). This is the
Tang-Li / Pardoux-Răşcanu H² solution-space requirement: H² is the L²
space of progressively measurable processes. -/
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
L²-isometric stand-in. The per-component Z hypotheses are bundled as
existential witnesses to make the canonical-integral expression well-typed.
This is the H2 fix: previously M_W was only L²-isometric to Z, which left a
non-trivial gap between the predicate and the literature claim. -/
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
witnesses to make the canonical-integral expression well-typed. This is the
H6 closure: previously the M_N pin was hollow because per-e adaptedness of
U was insufficient to type-check the canonical compensator. -/
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
