# Axiom #5 — `itoIsometry_brownian_unified_existence` — construction plan

**Target (Plan.md A1).** Replace the `axiom` in `Brownian/ItoL2Completion.lean`
with a `theorem`: for predictable square-integrable `H`, a single process
`F : ℝ → Ω → ℝ` and the filtration `Filt = (naturalFiltration W).rightCont` with
1. `Martingale F Filt P`,
2. `Martingale (fun t ω => (F t ω)^2 − ∫_{[0,t]} (H ω s)^2 ds) Filt P`,
3. `∀ T>0, ∫⁻ ω, ‖F T ω‖₊² ∂P = ∫⁻ ω, ∫⁻_{[0,T]} ‖H ω s‖₊² ∂vol ∂P`.
(Karatzas–Shreve 3.2.6 / Le Gall 5.4 + (5.8).) Discipline: build sorry-free
lemmas with the axiom in place; swap only when the full theorem is sorry-free
(then repoint `quadVar_stochasticIntegral` + `martingale_stochasticIntegral`,
drop entry from `cited_axioms.md`, 13→12).

## What is ALREADY proved (sorry-free, reusable)

- Simple-integrand layer (`Brownian/ItoSimple.lean`): `simpleIntegral`,
  `simpleIntegral_isometry` / `simpleIntegral_L2_isometry_brownian`,
  `martingale_simpleIntegral_brownian` (simple-level **martingale**),
  `simpleIntegral_condExp_brownian` (its condExp identity),
  `simpleIntegral_diagonal` / `simpleIntegral_offDiagonal` (the orthogonal-
  increment pieces — seeds for the quadVar identity).
- Density + Cauchy (`Brownian/ItoDensity.lean`): `simplePredictable_dense_L2`,
  `adaptedSimple_dense_L2_brownian`, `predictableDyadicSimple_brownian_L2_cauchy`,
  `L2_cauchy_of_L2_tendsto_brownian`.
- Lp-completion (`Brownian/ItoL2Completion.lean`): `simpleIntegralLp_brownian`
  (the simple integral as an `Lp` element), `cauchySeq_simpleIntegralLp_brownian`,
  `itoIntegralLp_brownian_L2_isometry`, and the **per-`T`** existence
  `exists_itoIntegralL2_brownian_progMeas` / `itoIsometry_brownian_existence`.
- `simpleIntegral_integrable_brownian`, `simpleIntegral_stronglyAdapted_brownian`.

## The gap (documented in-code at `ItoL2Completion.lean:615`)

The per-`T` extraction uses `Classical.choose` independently for each `T`, so the
witness is **incoherent** across `t` and carries no martingale property
(`stochasticIntegral_isometry_only_brownian` docstring says this). Need instead a
**coherent** `F` from one fixed approximating sequence, then martingale + quadVar
pass to the L²-limit.

## Construction (the route to build)

Fix the adapted approximating sequence `G : ℕ → SimplePredictable …` from
`predictableDyadicSimple_brownian` (already `L²`-Cauchy, adapted). Define
`F t := ` the `L²(P)`-limit of `fun ω => simpleIntegral W (G n) t ω` (coherent:
**same `G n` for all `t`**). Concretely either (a) `F t := ↑↑(L²-lim of
`simpleIntegralLp_brownian (G n) t`)` via `cauchySeq_…` + `CompleteSpace`, or
(b) a pointwise a.e. limit along an a.e.-convergent subsequence. (a) keeps the
`Lp` structure and is preferred.

Then three lemmas:

1. **`F` martingale.** Each `fun ω => simpleIntegral W (G n) t ω` is a martingale
   (`martingale_simpleIntegral_brownian` ⇒ `simpleIntegral_condExp_brownian`:
   `condExp (·|F_s)(simpleIntegral (G n) t) =ᵐ simpleIntegral (G n) s`). Pass to
   the limit: `condExp` is `L¹`-continuous (`condExpL1CLM` is a `→L[ℝ]`, and
   `condExp_ae_eq_condExpL1`). From `L²`-convergence + finite measure get `L¹`-
   convergence (`MemLp.mono_exponent`/`eLpNorm` monotonicity), then
   `condExp (F t|F_s) =ᵐ F s`. Tool options: `condExpL1CLM` continuity, or
   `tendsto_condExp_unique` (needs a dominated bound — the `condExpL1CLM` CLM
   route avoids the domination hypothesis and is cleaner). Adaptedness +
   integrability of `F t` from the `Lp`/`lpMeas` membership of the limit.
2. **quadVar martingale.** Simple-level identity: for `s ≤ t`,
   `condExp(·|F_s)((simpleIntegral (G n) t)^2 − ∫_{[0,t]} (G n)^2)
     =ᵐ (simpleIntegral (G n) s)^2 − ∫_{[0,s]} (G n)^2`
   (orthogonal increments: `simpleIntegral_diagonal`/`_offDiagonal` give the
   `𝔼[(I_t−I_s)^2|F_s] = 𝔼[∫_s^t (G n)^2|F_s]` increment identity). Then
   `(simpleIntegral (G n) t)^2 → (F t)^2` in `L¹` (from `simpleIntegral (G n) t →
   F t` in `L²`, since `a_n→a` in `L²` ⇒ `a_n²→a²` in `L¹`), and the `∫(G n)^2`
   term → `∫ H²` (the isometry/density convergence). Apply the same condExp-
   limit lever.
3. **isometry.** Already have it per `T` (`itoIntegralLp_brownian_L2_isometry`);
   re-derive for the coherent `F` (its `T`-slice equals the same `L²`-limit).

Finally bundle with `Filt := (naturalFiltration W).rightCont` (the martingales
above are wrt `naturalFiltration W`; lift to its right-continuous augmentation —
a martingale wrt a sub-filtration extends, or use that `rightCont` agrees on the
relevant σ-algebras; cf. how `martingale_stochasticIntegral` states the pinned
`Filt`).

## Key mathlib levers (verified present on the pin)

- `MeasureTheory.condExpL1CLM : (α →₁[μ] E) →L[ℝ] (α →₁[μ] E)` (continuous) +
  `condExp_ae_eq_condExpL1` — `L¹`-continuity of conditional expectation.
- `MeasureTheory.condExpL2 : (α →₂[μ] E) →L[𝕜] lpMeas …` (continuous).
- `MeasureTheory.tendsto_condExp_unique` (dominated-convergence form; fallback).
- `MeasureTheory.Martingale` (`condExp_ae_eq` / `Martingale.condExp_ae_eq`).

## First concrete coding step

A reusable **martingale-`L²`-limit** lemma (also needed for #6): given a
filtration `ℱ`, a sequence `Mₙ : ℝ → Ω → ℝ` of `ℱ`-martingales with, for each
`t`, `Mₙ t → F t` in `L²(P)` (P finite), and `F t` `ℱ`-adapted + integrable, then
`Martingale F ℱ P`. Prove via `condExpL1CLM` continuity + `condExp_ae_eq_condExpL1`.
Then specialize to the Itô coherent `F`. (Quadratic-variation lemma mirrors it.)

## Discipline

No new `sorry` in the built library; keep the axiom until the full theorem is
sorry-free; four-way invariant green every commit; no pin bump.
