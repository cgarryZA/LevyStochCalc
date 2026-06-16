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

## UPDATE 2026-06-16 — rightCont blocker RESOLVED + orthogonality engines

Three new general, sorry-free lemmas in `ItoL2Completion.lean` (all build-green,
lint-clean, contract-green):

- ✅ **`martingale_rightCont_of_tendsto_eLpNorm_one`** — the **rightCont obstacle is
  gone**. An `ℱ`-martingale on `ℝ` whose slices are right-`L¹`-continuous
  (`eLpNorm (F r − F s) 1 P → 0` as `r ↓ s`) is a martingale wrt `ℱ₊`. *No
  Blumenthal / axiom #4.* Proof: an `ℱ₊ s`-measurable `A` lies in every `ℱ r`
  (`r > s`) since `ℱ₊ s = ⨅ r>s, ℱ r`; the martingale identity makes `r ↦ ∫_A F r`
  constantly `∫_A F t` near `s⁺`, and right-`L¹`-continuity sends it to `∫_A F s`,
  so `∫_A F s = ∫_A F t`, i.e. `P[F t | ℱ₊ s] =ᵐ F s` (via
  `ae_eq_condExp_of_forall_setIntegral_eq` + `tendsto_setIntegral_of_L1'` +
  `Martingale.setIntegral_eq` + `Ioo_mem_nhdsGT`). **Both conjunct-1 and conjunct-2
  rightCont bundling now reduce to providing right-`L¹`-continuity of the slice.**
- ✅ **`integral_sq_increment_eq_of_martingale`** — martingale Pythagoras:
  `∫(M t − M s)² = ∫(M t)² − ∫(M s)²` for an L² martingale (cross term via
  `condExp_mul_of_stronglyMeasurable_left` pull-out + `Martingale.condExp_ae_eq`).
- ✅ **`integral_sq_mono_of_martingale`** — `∫(M s)² ≤ ∫(M t)²` for `s ≤ t`
  (corollary: `∫(M t−M s)² ≥ 0`).

**Consequence — Cauchy-at-each-`t` needs NO general-`t` refinement.** For the fixed
adapted dyadic sequence `Gₙ` on horizon `T`, the difference process
`Dₙₘ := simpleIntegral W Gₙ · − simpleIntegral W Gₘ ·` is a `naturalFiltration`-
martingale (`Martingale.sub` of two `martingale_simpleIntegral_brownian`s). Hence
for `t ≤ T`,
`‖Dₙₘ(t)‖₂² = ∫ Dₙₘ(t)² ≤ ∫ Dₙₘ(T)² = ‖Dₙₘ(T)‖₂²` (by `integral_sq_mono`),
and the RHS `→ 0` by the **endpoint** difference isometry `diff_isometry_simple`
(already proven) + the `h_cauchy_eval` hypothesis. So `n ↦ simpleIntegral W Gₙ t`
is `L²`-Cauchy at every `t ≤ T` — the general-`t` refine/`sub_on_common` chain is
NOT required. (Needs: `MemLp (simpleIntegral W Gₙ t) 2 P` at general `t`, available
from `simpleIntegral_intermediate_isometry` finiteness; `Dₙₘ(0) = 0` is automatic.)

**And the F-level right-`L²`-continuity (for the rightCont lift) is also free of a
clamped re-derivation:** once `F` is the coherent limit with conjunct-1 (martingale)
and conjunct-3 (isometry `∫ F_T² = ∫∫_{[0,T]}‖H‖²`), the increment identity gives
`‖F_r − F_s‖₂² = ∫ F_r² − ∫ F_s² = (∫∫_{[0,r]}‖H‖²) − (∫∫_{[0,s]}‖H‖²)`, which
`→ 0` as `r ↓ s` by right-continuity of `r ↦ ∫∫_{[0,r]}‖H‖²` (DCT / `tendsto_setLIntegral_zero`
on the shrinking slab `(s,r]`). Then `‖·‖₁ ≤ ‖·‖₂` (prob. measure) feeds
`martingale_rightCont_of_tendsto_eLpNorm_one`. Conjunct-2's rightCont lift uses the
same lever with `F_t² − A_t` (right-`L¹`-continuous: `F_r² → F_s²` in L¹ via
`tendsto_eLpNorm_one_sq_sub`, `A` continuous).

**Remaining gap = (a) coherent-`F` definition + (b) unbounded-horizon exhaustion.**
The per-horizon-`T` truncation/diagonal is `exists_itoIntegralL2_brownian_progMeas`;
the open task is to thread a *single* sequence across growing horizons (or define
`F` per-`t` from a horizon-indexed family proven consistent on overlaps) so the
process is defined on all of `ℝ₊`, then assemble conjuncts 1–3 + the two rightCont
lifts. The horizon-exhaustion/consistency is the principal remaining construction.

## Remaining steps (resume here)

**Analytic toolkit DONE (8 sorry-free lemmas in `ItoL2Completion.lean`).** Limit
engines: `martingale_of_tendsto_eLpNorm_one`, `tendsto_eLpNorm_one_of_eLpNorm_two`,
`eLpNorm_one_mul_le`, `tendsto_eLpNorm_one_sq_sub`. Intermediate-isometry cores
(general times, not just endpoint `T`): `diagonal_increment_lint`,
`offDiagonal_increment_integral_zero`, `increment_sq_integrable`,
`diagonal_increment_bochner`.

**The intermediate-time isometry now reduces to a clamped Bochner ASSEMBLY**
(`simpleIntegral W H t = ∑ᵢ ξᵢ·(W_{pᵢ₊₁∧t} − W_{pᵢ∧t})`, `aᵢ := pᵢ∧t`,
`bᵢ := pᵢ₊₁∧t`):
1. **Clamped cross-integrability** (`Integrable (termᵢ·termⱼ)`): mirror
   `cross_sq_integrable`, with `increment_sq_integrable` for genuine increments
   and `aᵢ = bᵢ ⇒ increment 0` for degenerate ones (`ξ`s bounded via `H.ξ_bounded`).
2. **Clamped Bochner sq** `∫ (∑ termᵢ)² = ∑ᵢ (bᵢ − aᵢ)·∫ ξᵢ²`: expand via
   `Finset.sum_mul_sum`, then per pair `(i,j)`:
   - `i=j`, `aᵢ<bᵢ` ⇒ `diagonal_increment_bochner` (note `aᵢ<bᵢ ⇒ t>pᵢ ⇒ aᵢ=pᵢ`,
     so `ξᵢ` is `F_{aᵢ}`-measurable); `aᵢ=bᵢ` ⇒ term `0`.
   - `i<j` (and symmetric): degenerate `j` ⇒ `termⱼ=0`; else
     `offDiagonal_increment_integral_zero` with `a₁=pᵢ, b₁=bᵢ ≤ pⱼ=a₂, b₂=bⱼ`
     (`bᵢ = min(pᵢ₊₁,t) ≤ pᵢ₊₁ ≤ pⱼ`).
3. **`ofReal`/lint conversion** + **clamped outer**
   `∑ᵢ ofReal(bᵢ−aᵢ)·∫⁻ξᵢ² = ∫⁻∫⁻_{[0,t]}‖H.eval‖²` (clamped `lintegral_eval_sq_outer`).
   Gives `intermediate isometry`: `∫⁻‖simpleIntegral W H t‖² = ∫⁻∫⁻_{[0,t]}‖H.eval‖²`.

**Then the coherent `F` + axiom replacement** (all engines ready):
4. `F t :=` `L²`-limit (Cauchy from step 3's difference form + completeness) of
   `simpleIntegral W (Gₙ) t`, `Gₙ` the fixed dyadic sequence. `→ F t` in `L²`,
   hence `L¹` (`tendsto_eLpNorm_one_of_eLpNorm_two`).
5. Conjunct 1: `martingale_of_tendsto_eLpNorm_one`. Conjunct 2: step-3 quadVar +
   `tendsto_eLpNorm_one_sq_sub`. Conjunct 3: isometry from step 3 + density.
   Bundle on `rightCont`; replace axiom; repoint consumers; drop #5 (13→12).

Steps 1–3 are the remaining ~250 lines (intricate but mechanical, all pieces
proven); steps 4–5 then assemble via the engines.

## Discipline

No new `sorry` in the built library; keep the axiom until the full theorem is
sorry-free; four-way invariant green every commit; no pin bump.
