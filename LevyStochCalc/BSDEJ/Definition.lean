import LevyStochCalc.Brownian.Ito
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Poisson.L2Isometry

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
[ch02_mathematical_framework.tex](D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex)
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

**Remaining slack acknowledged in `tools/cited_axioms.md` #9**:
`M_W` is still only L²-isometric to `Z`, not pinned to literally
`∑_i ∫_0^t Z_i dW_i`. Tightening this requires a multidim Brownian
stochastic integral primitive with progressively-measurable
integrands; tracked as follow-up. The adaptedness fix is sufficient
to close the soundness defect (uniqueness is now formally derivable
from adaptedness + martingale property as sketched above). -/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Definition

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- BSDEJ data: terminal condition `g`, generator `f`. -/
structure BSDEJData (n d : ℕ) (E : Type v) where
  /-- Generator `f(t, x, y, z, u)`. -/
  f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ
  /-- Terminal condition `g(x)`. -/
  g : (Fin n → ℝ) → ℝ

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
    -- 2026-05-21 strengthening 1: adaptedness layer (rules out
    -- Y = W₁_T − W₁_t counterexample).
    -- 2026-05-22 strengthening 2 (H2 fix): M_W is now PINNED to the
    -- canonical multidim Brownian Itô integral of Z (not just L²-isometric).
    -- This requires the per-component Z hypotheses (joint measurability,
    -- progressive measurability w.r.t. W's component natural filtrations,
    -- per-component L² bound) to be bundled inside the existential.
    ∧ (∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
        MeasureTheory.Adapted Filt Y ∧
        MeasureTheory.Adapted Filt Z ∧
        (∀ e : E, MeasureTheory.Adapted Filt (fun s ω => U s ω e)) ∧
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
          -- M_N is pinned to the canonical compensated-Poisson L² integral of U:
          (∀ T' : ℝ, ∀ᵐ ω ∂P,
            M_N T' ω =
              LevyStochCalc.Poisson.Compensated.stochasticIntegral N
                (fun ω' s e => U s ω' e) T' ω) ∧
          -- M_W and M_N are martingales w.r.t. the same Filt:
          MeasureTheory.Martingale M_W Filt P ∧
          MeasureTheory.Martingale M_N Filt P ∧
          -- BSDEJ equation at every t, with the same (M_W, M_N):
          (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
            Y t ω = bsdej.g (X T ω)
              + ∫ s in Set.Icc t T,
                  bsdej.f s (X s ω) (Y s ω) (Z s ω) (U s ω)
              - (M_W T ω - M_W t ω) - (M_N T ω - M_N t ω)))

end LevyStochCalc.BSDEJ.Definition
