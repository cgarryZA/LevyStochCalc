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

## Progress (reusable engines — DONE, sorry-free, in `ItoL2Completion.lean`)

- ✅ **`martingale_of_tendsto_eLpNorm_one`** — the L¹-limit of `ℱ`-martingales is
  an `ℱ`-martingale (conjunct-1 engine; reusable for #6). Proof: conditional
  expectation is an L¹-contraction (`eLpNorm_one_condExp_le_eLpNorm`) +
  `condExp_sub`, so `μ[Mₙt|ℱs] =ᵐ Mₙs` passes to the L¹-limit (squeeze of the
  target seminorm by `‖Mₙt−Ft‖₁ + ‖Mₙs−Fs‖₁ → 0`).
- ✅ **`tendsto_eLpNorm_one_of_eLpNorm_two`** — on a probability measure,
  `L²`-null ⇒ `L¹`-null (`eLpNorm_le_eLpNorm_of_exponent_le`), bridging the
  `L²`-Cauchy approximating sequence to the L¹ hypothesis above.
- ✅ **`eLpNorm_one_mul_le`** — `L²` Hölder product `‖f·g‖₁ ≤ ‖f‖₂·‖g‖₂` (from
  `ENNReal.lintegral_mul_le_Lp_mul_Lq` + `enorm_mul`). General-purpose.
- ✅ **`tendsto_eLpNorm_one_sq_sub`** — `aₙ→b` in `L²` ⇒ `aₙ²→b²` in `L¹`
  (conjunct-2 engine; uses the Hölder product + triangle `‖aₙ+b‖₂ ≤ ‖aₙ−b‖₂+2‖b‖₂`).

**So both conjuncts' analysis engines are now in place** — conjunct 1 via
`martingale_of_tendsto_eLpNorm_one` (+ the L²→L¹ bridge), conjunct 2 via
`tendsto_eLpNorm_one_sq_sub`. The ∫`(Gₙ)²`→∫`H²` term of conjunct 2 reuses the
isometry/density convergence already proven. **The only remaining piece is the
coherent `F` (below): once it exists with `simpleIntegral W (Gₙ) t → F t` in `L²`
for each `t`, both conjuncts follow by feeding these engines.**

## Remaining steps (resume here)

1. **Coherent `F`.** The per-`T` construction (`exists_itoIntegralL2_brownian`)
   takes an approximating sequence `G : ℕ → SimplePredictable Ω T` on a **fixed
   `T`**, so building a single `F : ℝ → Ω → ℝ` needs consistency across `T` (the
   `[0,T']` integral restricted to `[0,t]`, `t ≤ T'`, equals the `[0,t]` one).
   Define `F t :=` the L²-limit of `simpleIntegral W (Gₙ) t` for one fixed
   adapted `Gₙ` (`predictableDyadicSimple_brownian`), with adaptedness +
   integrability; show `simpleIntegral W (Gₙ) t → F t` in L² (Cauchy + complete),
   hence (by `tendsto_eLpNorm_one_of_eLpNorm_two`) in L¹.
2. **Conjunct 1 (martingale):** each `simpleIntegral W (Gₙ) ·` is an
   `ℱ`-martingale (`martingale_simpleIntegral_brownian`); feed step 1's L¹
   convergence to `martingale_of_tendsto_eLpNorm_one`. ⇒ `Martingale F ℱ P`.
3. **Conjunct 2 (quadVar):** simple-level identity from `simpleIntegral_diagonal`
   /`_offDiagonal` gives `(simpleIntegral (Gₙ) ·)² − ∫(Gₙ)²` a martingale; needs
   the **squares-converge engine** `(Mₙt)² → (Ft)²` in L¹ from `Mₙt→Ft` in L²
   (Cauchy–Schwarz: `‖a²−b²‖₁ ≤ ‖a−b‖₂‖a+b‖₂`; the L² Hölder-product norm
   inequality is the missing mathlib lever — search `eLpNorm`/`lintegral`
   Hölder, or use the `L²` inner-product `inner_mul_le_norm_mul_norm`). Then the
   same `martingale_of_tendsto_eLpNorm_one`.
4. **Isometry + bundle** on `(naturalFiltration W).rightCont`; replace the axiom;
   repoint `quadVar_/martingale_stochasticIntegral`; drop #5 (13→12).

## Discipline

No new `sorry` in the built library; keep the axiom until the full theorem is
sorry-free; four-way invariant green every commit; no pin bump.
