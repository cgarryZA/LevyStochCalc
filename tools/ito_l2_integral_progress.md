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
4. `F t :=` `L²`-limit of `simpleIntegral W (Gₙ) t`, `Gₙ` the fixed dyadic
   sequence. **Cauchy-at-each-`t` is now DONE** (see UPDATE below): no general-`t`
   difference isometry needed. `→ F t` in `L²`, hence `L¹`
   (`tendsto_eLpNorm_one_of_eLpNorm_two`).
5. Conjunct 1 (naturalFiltration): `martingale_of_tendsto_eLpNorm_one`. Conjunct 3
   (isometry ∀T): intermediate isometry + density. Conjuncts 1,2 lifted to
   `rightCont` via `martingale_rightCont_of_tendsto_eLpNorm_one` — slice
   right-`L²`-continuity from `integral_sq_increment_eq_of_martingale` (conjuncts
   1+3) + right-continuity of `r ↦ ∫∫_{[0,r]}‖H‖²`. Conjunct 2 quadVar: simple-level
   orthogonal-increment identity + `tendsto_eLpNorm_one_sq_sub`.

**Steps 1–3 DONE** (`simpleIntegral_intermediate_isometry`).

## UPDATE 2026-06-16 (session 2) — Cauchy-at-each-`t` + orthogonality DONE

Landed (all sorry-free, build/lint/contract green):
- ✅ `simpleIntegral_memLp_intermediate_brownian` — `MemLp (simpleIntegral W H t) 2 P`
  for `t ≤ T` (measurability + intermediate isometry bounded by finite endpoint).
- ✅ `integral_sq_increment_eq_of_martingale`, `integral_sq_mono_of_martingale` —
  martingale Pythagoras + 2nd-moment monotonicity (pointwise-`MemLp` API).
- ✅ `simpleIntegral_lintegral_sq_sub_le_endpoint_brownian` — **Cauchy-at-each-`t`**:
  `∫⁻‖I₁(t)−I₂(t)‖² ≤ ∫⁻∫⁻_{[0,T]}‖eval diff‖²` for `t ≤ T`, via the difference
  martingale's 2nd-moment monotonicity + endpoint `diff_isometry_simple`.
- ✅ `martingale_rightCont_of_tendsto_eLpNorm_one` — rightCont lift (no Blumenthal).

**Remaining for #5 (the principal construction left):**
A. **Coherent `F` for one horizon `T`.** For `t ≤ T`, `F^T t := ↑↑(L²-lim of
   `simpleIntegralLp_brownian (Gₙ) t)` via `CompleteSpace` + the Cauchy-at-each-`t`
   bound (need a general-`t` `simpleIntegralLp` / `cauchySeq…` mirror — small, the
   bound is in hand). Then `simpleIntegral W Gₙ t → F^T t` in `L²` ∀`t≤T`.
B. **Unbounded horizon.** Thread `F^T` consistently across `T` (overlap consistency
   on `[0, T₁]` for `T₁ ≤ T₂`, both being the same `L²`-limit) to get `F` on all
   `ℝ₊`; OR exhaust along `T = k ∈ ℕ`. This is the main open architectural piece.
C. **Right-continuity of `r ↦ ∫∫_{[0,r]}‖H‖²`** (DCT / `tendsto_setLIntegral_zero`
   on the slab `(s,r]` under the product measure) — feeds the rightCont lifts.
D. **Assemble** conjuncts 1,3 (engines), 2 (simple quadVar + sq engine), lift 1,2 to
   `rightCont`; replace axiom; repoint `quadVar_stochasticIntegral` +
   `martingale_stochasticIntegral`; drop #5 from `cited_axioms.md` (13→12).

## UPDATE 2026-06-16 (session 3) — ALL analytic engines for #5 are DONE

Landed (sorry-free, four-way green):
- ✅ **General-`t` refinement chain** (`SimplePredictableRefine.lean`):
  `W_telescope_via_g_clamped`, `fiber_sum_telescope_clamped`,
  `simpleIntegral_refine_intermediate`, `simpleIntegral_sub_on_common_intermediate`
  — the `min(·,t)`-clamped analogues of the endpoint refinement machinery
  (telescoping is value-agnostic, so the clamp passes through unchanged).
- ✅ **`simpleIntegral_intermediate_diff_isometry`** — `∫⁻‖I₁(t)−I₂(t)‖² =
  ∫⁻∫⁻_{[0,t]}‖eval diff‖²` at every `t` (common endpoint). The exact isometry
  for `L²`-Cauchy-at-each-`t` AND cross-horizon consistency.
- ✅ **`tendsto_setLIntegral_Ioc_prod_zero`** — right-continuity of the horizon
  integral (piece C above): `∫⁻ω∫⁻_{(s₀,r]}φ → 0` as `r ↓ s₀`.

**Engine inventory (all present, sorry-free):** general-`t` difference isometry ·
`integral_sq_increment_eq_of_martingale` · `integral_sq_mono_of_martingale` ·
`martingale_rightCont_of_tendsto_eLpNorm_one` · `tendsto_setLIntegral_Ioc_prod_zero` ·
`martingale_of_tendsto_eLpNorm_one` · `tendsto_eLpNorm_one_of_eLpNorm_two` ·
`eLpNorm_one_mul_le` · `tendsto_eLpNorm_one_sq_sub` · `simpleIntegral_memLp_intermediate_brownian`.

**The only thing left is the CONSTRUCTION (no new analytic ideas needed):**
1. **Zero-extension** `SimplePredictable.appendInterval H T'` (`H_last < T'`,
   append one interval with `ξ = 0` via `Fin.snoc`): `eval`/`simpleIntegral`
   unchanged, adapted. (Needed so two different-horizon dyadic approximants share
   an endpoint for the difference isometry → cross-horizon Cauchy.)
2. **Master sequence** `Gₙ` on growing horizons (dyadic mesh + truncation level +
   horizon, a diagonal-of-diagonals built from `predictableDyadicSimple_brownian`
   + the existing per-`T` truncation in `exists_itoIntegralL2_brownian_progMeas`),
   with `∫⁻∫⁻_{[0,n]}‖Gₙ.eval − H‖² → 0`.
3. **`F t := ↑↑(Filter.limUnder atTop (fun n => (memLp_intermediate (Gₙ↑) t).toLp))`**
   (zero-extend `Gₙ` to a common horizon ≥ t); `CauchySeq` from
   `simpleIntegral_intermediate_diff_isometry` + step 2. `Iₙ(t) → F t` in `L²` ∀t.
4. **Conjunct 3** (isometry ∀T): `eLpNorm² (F T) = ∫⁻∫⁻_{[0,T]}‖H‖²` from the
   per-`t` isometry-limit (mirrors `itoIntegralLp_brownian_L2_isometry`).
5. **Conjunct 1** (naturalFiltration martingale): `martingale_of_tendsto_eLpNorm_one`
   + `tendsto_eLpNorm_one_of_eLpNorm_two` on `Iₙ(t) → F t`.
6. **Lift conjunct 1 to `rightCont`**: slice right-`L²`-continuity via
   `integral_sq_increment_eq_of_martingale` (gives `‖F_r−F_s‖₂² = ∫∫_{(s,r]}‖H‖²`)
   + `tendsto_setLIntegral_Ioc_prod_zero` → `martingale_rightCont_of_tendsto_eLpNorm_one`.
7. **Conjunct 2** (quadVar martingale on `rightCont`): simple-level
   `(Iₙ(t))² − ∫_{[0,t]}Gₙ²` is a `naturalFiltration`-martingale (orthogonal
   increments — `simpleIntegral_diagonal`/`offDiagonal` in `ItoSimple.lean`); pass
   to the limit (`tendsto_eLpNorm_one_sq_sub` for `Iₙ²→F²`, isometry for the
   compensator); lift to `rightCont` (right-`L¹`-continuity of `F² − A`).
8. **Replace axiom**, repoint `quadVar_stochasticIntegral` +
   `martingale_stochasticIntegral`, drop #5 from `cited_axioms.md` (13→12), confirm
   `#print axioms` clean on consumers.

Steps 1–3 (zero-extension + master sequence + `F`) are the bulk of the remaining
construction; 4–8 then assemble via the engines above.

## UPDATE 2026-06-16 (session 4) — the integral process F is CONSTRUCTED

The entire **existence** construction is done, sorry-free, four-way green:
- ✅ `SimplePredictable.appendInterval` (+ eval/simpleIntegral/adapt/partition_last)
  — zero-extension to a larger horizon.
- ✅ `exists_adaptedSimple_within`, `masterApprox` (+ `_adapt`, `_within`) — the
  master approximating sequence on growing horizons `(n:ℝ)+1`.
- ✅ `masterApprox_diff_isometry` — cross-horizon difference isometry (extend both
  to a common horizon, then the general-`t` difference isometry).
- ✅ `masterApprox_eval_tendsto`, `masterApprox_cauchy_le` — per-`t` eval
  convergence + the Cauchy bound (triangle, joint measurability).
- ✅ `masterLp` (+ `_coeFn`, `_cauchySeq`) + `eLpNorm_two_rpow_eq_lintegral_sq` —
  the `Lp` lift, `L²`-Cauchy at each `t`.
- ✅ **`stochasticIntegralBrownian`** (= `t ↦ ∫_0^t H dW`) + `masterApprox_tendsto_L2`
  — `F` is the `L²`-limit; `simpleIntegral W (masterApprox n) t → F t` in `L²` ∀`t≥0`.

**Remaining: the 3 conjuncts + rightCont + axiom swap.** Subtleties identified:
- **Conjunct 3 (isometry ∀T):** `∫⁻‖F T‖² = ∫⁻∫⁻_{[0,T]}‖H‖²`. Needs eLpNorm
  continuity (`Iₙ(T)→F T` ⇒ `‖Iₙ(T)‖₂→‖F T‖₂`, square the limit) + the **eval-L²-norm
  convergence** `∫⁻∫⁻_{[0,T]}‖Gₙ.eval‖² → ∫⁻∫⁻_{[0,T]}‖H‖²` (product-space `L²` norm
  continuity via Tonelli on `P ⊗ vol|_{[0,T]}`, from `masterApprox_eval_tendsto`).
- **Conjunct 1 (martingale):** `martingale_of_tendsto_eLpNorm_one` is ready (`Iₙ`
  martingales via `martingale_simpleIntegral_brownian`; `L¹` convergence from
  `masterApprox_tendsto_L2` + `tendsto_eLpNorm_one_of_eLpNorm_two`). **Gap:** the
  engine wants *honest* `StronglyAdapted ℱ F`, but `F t = ↑↑(limUnder)` is only
  *AE*-adapted. Fix: pick the `lpMeas`-representative (the ℱ_t-measurable L² closed
  subspace contains `Flp t`) or build `F` as that representative.
- **rightCont lift (conjuncts 1,2):** `martingale_rightCont_of_tendsto_eLpNorm_one`
  with slice right-`L²`-continuity = `integral_sq_increment_eq_of_martingale`
  (conjuncts 1+3) + `tendsto_setLIntegral_Ioc_prod_zero`. Ready once 1,3 land.
- **Conjunct 2 (quadVar):** the hardest. Needs the simple-level quadVar martingale
  `(Iₙ(t))² − ∫_{[0,t]}Gₙ²` (orthogonal increments from `simpleIntegral_diagonal`/
  `_offDiagonal` in `ItoSimple.lean` — not yet assembled), then the limit
  (`tendsto_eLpNorm_one_sq_sub` + the compensator convergence) + the rightCont lift.

## Discipline

No new `sorry` in the built library; keep the axiom until the full theorem is
sorry-free; four-way invariant green every commit; no pin bump.

## UPDATE 2026-06-17 (session 5) — F + conjuncts 1 & 3 DONE

The integral process and TWO of the three conjuncts are now fully proved (sorry-free,
four-way green, committed):
- ✅ `stochasticIntegralBrownian` — the L² Itô integral process, honestly ℱ_t-adapted
  (lpMeas representative), with `Iₙ(t) → F t` in L² (`masterApprox_tendsto_L2`).
- ✅ **Conjunct 1** `martingale_stochasticIntegralBrownian` — F is a
  `naturalFiltration`-martingale (via `martingale_of_tendsto_eLpNorm_one`).
- ✅ **Conjunct 3** `isometry_stochasticIntegralBrownian` — `∫⁻‖F T‖² =
  ∫⁻∫⁻_{[0,T]}‖H‖²` ∀T>0 (norm continuity + eval-norm convergence + uniqueness;
  the eval-norm convergence `masterApprox_evalNorm_tendsto` is the product-space
  Tonelli lift).
- ✅ supporting: `eval_lintegral_sq_finite`, `simpleIntegral_eq_zero_of_nonpos`,
  `stochasticIntegralBrownian_{ae_eq,stronglyAdapted,ae_zero_of_neg}`.

**Remaining for the axiom swap:**
- **rightCont lift of conjunct 1** — `martingale_rightCont_of_tendsto_eLpNorm_one`
  with right-L²-continuity of F: `∫⁻‖F r − F s‖² = ∫⁻∫⁻_{(s,r]}‖H‖²` (orthogonality
  `integral_sq_increment_eq_of_martingale` + isometry conjunct + Icc additivity) → 0
  by `tendsto_setLIntegral_Ioc_prod_zero`. Edge cases at `s ≤ 0` (F vanishes).
- **Conjunct 2 (quadVar martingale)** — the hard one: the simple-level
  `(Iₙ(t))² − ∫_{[0,t]}Gₙ.eval²` is a `naturalFiltration`-martingale (conditional
  Itô isometry: indicator-weighted diagonal/off-diagonal from `simpleIntegral_diagonal`/
  `_offDiagonal` in `ItoSimple.lean`, tested against ℱ_s-sets via
  `ae_eq_condExp_of_forall_setIntegral_eq`), then the L¹-limit
  (`tendsto_eLpNorm_one_sq_sub` for `Iₙ²→F²` + compensator convergence
  `∫Gₙ.eval²→∫H²` in L¹), then the rightCont lift (right-L¹-continuity of `F²−A`).
- **Axiom assembly** — bundle the three conjuncts on `(naturalFiltration W).rightCont`,
  replace the axiom, repoint `quadVar_stochasticIntegral`/`martingale_stochasticIntegral`,
  drop #5 from `cited_axioms.md` (13→12).
