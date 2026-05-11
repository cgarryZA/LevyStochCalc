import LevyStochCalc.Brownian.Ito
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

which is satisfiable by ANY L²-bounded `(Y, Z, U)` — pick `BM_term := g
+ ∫f - Y t ω`, `jump_term := 0` to make the equation trivially hold.
Under that predicate, `Y = 0` and `Y = 1` BOTH "solve" the BSDEJ
trivially, and the `continuousBSDEJ_exists_unique` axiom asserts a
uniqueness claim that's mathematically false (the existential of a
unique `Y` whose a.e.-equals every other "solution" can't be satisfied
when multiple distinct "solutions" exist).

Replaced with an OUTER existential `∃ M_W M_N : ℝ → Ω → ℝ` (one pair of
processes for the whole equation, not one pair of reals per `(t, ω)`):

* `M_N` is pinned to equal the canonical compensated-Poisson stochastic
  integral of `U` (via `LevyStochCalc.Poisson.Compensated.stochasticIntegral`).
  This rules out arbitrary `M_N` with vacuous values.
* `M_W` is constrained by the multidim Brownian Itô L²-isometry against
  `Z`: `𝔼[‖M_W(T')‖²] = 𝔼[∫_0^{T'} ‖Z_s‖² ds]` for every `T' > 0`. (We
  don't pin `M_W` to a specific functional of `Z` because the multidim
  Brownian stochastic integral primitive would need `h_progMeas` threaded
  through; the isometry constraint together with the martingale
  requirement is enough to exclude the trivial witnesses.)
* Both `M_W` and `M_N` must be martingales w.r.t. a common filtration.
* The BSDEJ equation `Y t ω = g(X_T) + ∫_t^T f - (M_W T − M_W t) - (M_N
  T − M_N t)` holds at every `t ∈ [0, T]` simultaneously, using the
  *same* `M_W, M_N` (not freshly-chosen per `(t, ω)`).

Under this strengthening, `Y = 0` no longer satisfies the predicate for
generic `(g, f, X)`: the equation forces `(M_W T − M_W t) + (M_N T − M_N
t) = g(X_T) + ∫_t^T f(s, X_s, 0, 0, 0)` to be a difference of
martingales — which requires `g + ∫f` to be of the form `const −
martingale_drift`, which fails for non-zero `f` integrated
deterministically.

The strengthened predicate is still slightly weaker than the literature
(it doesn't pin `M_W` to be literally `∫ Z · dW`, only an isometric
martingale), but it is non-vacuous: the literature solution satisfies
it, and trivial constant `Y` does not. Sufficient for the cited axioms
`continuousBSDEJ_exists_unique` and `bsdej_path_regularity` to assert
substantive content. -/

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
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
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
    -- Strengthened equation conjunct: one pair of martingales (M_W, M_N)
    -- pinned to (Z, U), satisfying the BSDEJ equation at every t.
    ∧ (∃ M_W M_N : ℝ → Ω → ℝ,
        Measurable (Function.uncurry M_W) ∧
        Measurable (Function.uncurry M_N) ∧
        -- M_W satisfies the multidim Brownian L²-Itô isometry against Z:
        (∀ T', 0 < T' →
          ∫⁻ ω, (‖M_W T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
            ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
              ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) ∧
        -- M_N is pinned to the canonical compensated-Poisson L² integral of U:
        (∀ T' : ℝ, ∀ᵐ ω ∂P,
          M_N T' ω =
            LevyStochCalc.Poisson.Compensated.stochasticIntegral N
              (fun ω' s e => U s ω' e) T' ω) ∧
        -- M_W and M_N are martingales w.r.t. a common filtration:
        (∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
          MeasureTheory.Martingale M_W Filt P ∧
          MeasureTheory.Martingale M_N Filt P) ∧
        -- BSDEJ equation at every t, with the same (M_W, M_N):
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          Y t ω = bsdej.g (X T ω)
            + ∫ s in Set.Icc t T,
                bsdej.f s (X s ω) (Y s ω) (Z s ω) (U s ω)
            - (M_W T ω - M_W t ω) - (M_N T ω - M_N t ω)))

end LevyStochCalc.BSDEJ.Definition
