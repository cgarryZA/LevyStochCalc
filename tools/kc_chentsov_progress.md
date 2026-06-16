# Kolmogorov–Chentsov continuous modification — progress notes

**Goal (Plan.md Phase 3 #3).** Replace the cited axiom
`LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification` with a
fully `sorry`-free theorem, proved from scratch on the **current** mathlib
pin (no bump), using `ProbabilityTheory.IsKolmogorovProcess`.

Axiom statement (target theorem signature, in `Brownian/Continuity.lean`):

```
theorem kolmogorovChentsov_modification
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (hq : 1 < q) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω)
```

Do **not** weaken `p`, `q`, `M` or the conclusion: the consumer
`brownian_continuous_modification` instantiates it at `p = 4, q = 2, M = 3`
(Brownian fourth moment), and the dissertation forwards through
`brownian_continuous_modification` → `MultidimBrownianMotion.exists` etc.

## What mathlib gives us (verified on the pinned rev)

`Mathlib/Probability/Process/Kolmogorov.lean` has **only the condition**, no
continuity conclusion. Usable API on `hX : IsKolmogorovProcess X P p q M`:

- `hX.kolmogorovCondition s t : ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P ≤ M * edist s t ^ q`
- `hX.measurable s : Measurable (X s)`         (needs `SecondCountableTopology`, ℝ has it)
- `hX.measurable_edist : Measurable fun ω => edist (X s ω) (X t ω)`
- `hX.p_pos`, `hX.q_pos`
- `IsKolmogorovProcess.mk_of_secondCountableTopology` (constructor; already used
  by `brownian_continuous_modification` to build the `p=4,q=2,M=3` instance).

There is **no** chaining / covering-number / Hölder infrastructure in mathlib's
`Probability/Process/*` (checked: only Adapted, Filtration, FiniteDimensionalLaws,
HittingTime, Kolmogorov, LocalProperty, PartitionFiltration, Predictable, Stopping).

## What is ALREADY proved in `Brownian/Continuity.lean` (green, sorry-free)

The two "outer" thirds AND the deterministic core of the middle third are now
done. What remains is the *probabilistic* supply of the increment bound
(Borel–Cantelli) plus the interval/patching plumbing.

**Outer thirds:**

1. `holder_dense_extends_continuous` — **extension step.** An α-Hölder function
   on a dense set `D ⊆ ℝ` extends to a (unique) continuous function on ℝ, equal
   to `f` on `D`, via `Dense.uniformContinuous_extend`. *(DONE)* ⚠ needs a
   scale-limited variant — see "Extension" below.

2. `dyadicRationals`, `dense_dyadicRationals`, `exists_seq_dyadic_tendsto` — the
   dense dyadic set + a dyadic sequence `↗ t` for every `t`. *(DONE)*

3. `kolmogorov_markov_bound` — per-pair Markov/Chebyshev tail bound
   `P {ω | lam ≤ edist (X s ω) (X t ω)} ≤ M * edist s t ^ q / lam ^ p`
   for `0 < lam < ⊤`. *(DONE)*
   `kolmogorov_real_tail_bound` — its real-threshold form
   `P {ω | lam < |X s ω − X t ω|} ≤ M · edist s t ^ q / (ofReal lam)^p`
   (`lam > 0`); ready to feed Lemma A. *(DONE, NEW)*

4. `kolmogorov_modification_ae_eq` — **a.e.-equality step.** GIVEN a candidate
   `Y` a.s. continuous and a.s. equal to `X` on every dyadic, concludes
   `∀ t, Y t =ᵐ[P] X t`. *(DONE)*

**Deterministic dyadic chaining (the hard middle core — NEW, all sorry-free):**

5. `dyadicTrunc n x := ⌊x·2ⁿ⌋/2ⁿ` with `dyadicTrunc_le`,
   `dyadicTrunc_mem_dyadicRationals`, `floor_two_mul_bounds`. *(DONE)*
6. `dyadicTrunc_succ_step` — `|f(trunc_{n+1}x) − f(trunc_n x)| ≤ b(n+1)` for
   `x ∈ [0,1]` (one consecutive level-`(n+1)` increment). *(DONE)*
7. `dyadicTrunc_telescope` — `|f(trunc_L x) − f(trunc_m x)| ≤ ∑_{m<n≤L} b n`. *(DONE)*
8. `dyadicTrunc_near_step` — cross-point level-`m` bound for `|s−t| ≤ 2^{−m}`. *(DONE)*
9. `dyadicTrunc_eventually_eq` — dyadic `s` ⇒ `trunc_L s = s` for large `L`. *(DONE)*
10. `sum_Ico_geometric_le`, `exists_dyadic_scale`, `rpow_half_pow_le` — geometric
    tail bound, optimal dyadic scale `(1/2)^{m+1} < d ≤ (1/2)^m`, and
    `((1/2)^α)^m ≤ 2^α·d^α`. *(DONE)*
11. **`dyadic_holder_chaining`** — the payoff: if consecutive level-`n` dyadic
    increments on `[0,1]` are `≤ C·((1/2)^α)^n` for all `n ≥ N`, then
    `∃ K ≥ 0, ∀ s,t ∈ dyadics∩[0,1], |s−t| ≤ 2^{−N} → |f s − f t| ≤ K·|s−t|^α`.
    *(DONE — this is KS 2.2.8's chaining, fully formalized.)*

**Probabilistic supply (Borel–Cantelli) — NEW this session, all sorry-free:**

12. `kc_exponent_identity` — real exponent collapse
    `2^n·((1/2)^n)^q/((1/2)^α)^n)^p = ((1/2)^{q−αp−1})^n`. *(DONE)*
13. `kolmogorov_real_tail_bound` — real-threshold tail bound (item 3). *(DONE)*
14. **`kc_level_bad_measure`** (Lemma A) — `P(⋃_{k<2^n} {rⁿ < |incrₙₖ|}) ≤
    ofReal((M:ℝ)·ρⁿ)`, `ρ = (1/2)^{q−αp−1}`. *(DONE)*
15. **`kc_ae_increment_bound`** (Lemma B) — for `αp < q−1`: a.e. `ω`,
    `∃ N, ∀ n ≥ N, ∀ k:ℤ, 0≤k, k+1≤2ⁿ, |X((k+1)/2ⁿ)ω − X(k/2ⁿ)ω| ≤ ((1/2)^α)ⁿ`.
    Via summable `∑ ofReal(M·ρⁿ)` (`ρ<1`) ⇒ `measure_limsup_atTop_eq_zero` ⇒
    `mem_limsup_iff_frequently_mem`/`eventually_atTop`, then ℤ↔ℕ index bridge.
    *(DONE — this is exactly the hypothesis `dyadic_holder_chaining` consumes.)*

So **everything except the final topological assembly is done.** Remaining:
**(i)** a bounded-interval continuous-extension lemma (D dense in `[0,1]`,
scale-limited Hölder ⇒ continuous on `[0,1]`), since `dyadic_holder_chaining`
gives Hölder only for `s,t ∈ [0,1]` (the existing `holder_dense_extends_continuous`
extends from `D` dense in ALL of ℝ, which our `[0,1]`-localized bound does not
give); **(ii)** assemble on `[0,1]`: from `kc_ae_increment_bound` +
`dyadic_holder_chaining` + (i), build `Y` continuous on `[0,1]`, agreeing with `X`
on dyadics a.s., then `kolmogorov_modification_ae_eq` ⇒ `Y =ᵐ X` on `[0,1]`;
**(iii)** patch ℝ: the Kolmogorov condition is translation-invariant
(`edist (s+j) (t+j) = edist s t`), so apply the `[0,1]` construction to `X(·+j)`
for each `j:ℤ`, giving modifications on each `[j,j+1]`; glue (they agree at integer
endpoints a.s.) into a global continuous `Y` via a `ContinuousOn`-cover argument.
Steps (i)+(ii)+(iii) are the only remaining work; everything they call is proven.

  ⚠ Alternative to (iii)'s gluing: `IsDenseInducing.continuous_extend` — define
  `Y t ω := lim_{dyadic s→t} X s ω`; local Hölder gives the limit at each `t`,
  yielding a global continuous extension without explicit interval gluing.

### Final-assembly recipe (refined; `extendFrom` is the right tool)

`translation_invariance` is now proven (`isKolmogorovProcess_comp_add_right`).
The extension tool is `Mathlib/Topology/ExtendFrom.lean` — **no subtypes, no
manual gluing**:
  - `extendFrom A f x := limUnder (𝓝[A] x) f`;
  - `continuous_extendFrom (hA : Dense A) (hf : ∀ x, ∃ y, Tendsto f (𝓝[A] x) (𝓝 y))
     : Continuous (extendFrom A f)`;
  - `extendFrom_extends (hf : ContinuousOn f A) : ∀ x ∈ A, extendFrom A f x = f x`.

Define, per good `ω`, `Y t ω := extendFrom dyadicRationals (fun s => X s ω) t`
(and `0` off the good set, a null set). Then:
  - **Continuity** from `continuous_extendFrom dense_dyadicRationals (limit hf)`.
  - **Agreement on dyadics** from `extendFrom_extends` (needs
    `ContinuousOn (fun s => X s ω) dyadicRationals`, which the local Hölder gives).
  - Feed to `kolmogorov_modification_ae_eq` ⇒ the modification property.

The one remaining lemma to build — **limit existence at every `t`**:
`∀ t, ∃ y, Tendsto (fun s => X s ω) (𝓝[dyadicRationals] t) (𝓝 y)`. Route:
  1. **Local Hölder on an OPEN neighborhood of `t`** (not just one unit interval):
     apply `kc_ae_increment_bound` + `dyadic_holder_chaining` to `X(·+j)` for
     `j ∈ {⌊t⌋−1, ⌊t⌋, ⌊t⌋+1}` (via `isKolmogorovProcess_comp_add_right`), giving
     Hölder on `[j,j+1]` dyadics. For a *straddling* pair `s < j' < s'` (sharing
     integer `j'`), chain through `j'`:
     `|f s − f s'| ≤ |f s − f j'| + |f j'− f s'| ≤ K|s−j'|^α + K|j'−s'|^α ≤ 2K|s−s'|^α`
     (since `|s−j'|,|j'−s'| ≤ |s−s'|`). So `f` is α-Hölder (const `2K`, scale
     `≤ 2^{−N}`) on `dyadicRationals ∩ (⌊t⌋−1, ⌊t⌋+2)`, an open nbhd of `t`.
  2. **Cauchy ⇒ limit** (ℝ complete): show `Cauchy (map f (𝓝[A] t))` via
     `Metric.cauchy_iff` — `NeBot` from `t ∈ closure A` (`A` dense) and the diam
     bound `∀ ε>0, ∃ V ∈ 𝓝[A] t, ∀ s s'∈V, dist (f s)(f s') < ε` from step 1
     (take `V = A ∩ ball t ρ`, `ρ` small so `2K(2ρ)^α < ε` and `2ρ ≤ 2^{−N}`).
     Then `CompleteSpace.complete` gives `∃ y, map f (𝓝[A]t) ≤ 𝓝 y` = the limit.
  Estimated ~150–200 lines; this is the only remaining work to close the axiom.

## The missing middle third — proof plan (Karatzas–Shreve 2.2.8 / Le Gall 2.9)

Work first on a **bounded interval** `[0, 1]` (or `[0, T]`), then patch ℝ as a
countable union of unit intervals (see "Patching" below).

Fix `α` with `0 < α < (q - 1) / p` (exists since `q > 1, p > 0`). Then
`q - α·p > 1`, i.e. the exponent below is `< 0`.

**Lemma A (per-level bound).** ✅ DONE (`kc_level_bad_measure`). Original plan: for level `n`, let
`A n := {ω | ∃ k : Fin (2^n), 2^(-α n) ≤ edist (X (k/2^n) ω) (X ((k+1)/2^n) ω)}`
(consecutive dyadic increments at resolution `2^n` inside `[0,1]`). Then

  `P (A n) ≤ ∑_{k<2^n} M * (2^(-n))^q / (2^(-αn))^p = M * 2^(n(1 - q + α p))`.

Proof: `measure_iUnion_fin_le`/`measure_biUnion_finset_le` over `k`, each term
bounded by `kolmogorov_markov_bound (k/2^n) ((k+1)/2^n) …` with
`edist (k/2^n) ((k+1)/2^n) = ENNReal.ofReal (2^(-n))` and `lam = 2^(-αn)`. Note
`edist` on ℝ is `ofReal |·|`; the dyadic gap is `2^(-n)`.

**Lemma B (Borel–Cantelli).** ✅ DONE (`kc_ae_increment_bound`). Original plan: `∑_n P (A n) < ∞` because `1 - q + αp < 0`
(geometric series, `ENNReal.summable_geometric` / `tsum` of `r^n` with `r < 1`;
the constant `M` factors out). Hence by Borel–Cantelli (mathlib:
`MeasureTheory.measure_limsup_atTop_eq_zero` for a summable family, or
`ProbabilityTheory.measure_limsup_eq_zero`), `P (limsup A n) = 0`. So for a.e.
`ω` there is `N(ω)` with: for all `n ≥ N(ω)`, every consecutive level-`n` dyadic
increment is `< 2^(-αn)`.

  ⚠ API to confirm: the exact name/shape of the Borel–Cantelli lemma on the pin.
  Candidates: `MeasureTheory.measure_limsup_eq_zero` (needs `∑ measure < ⊤`),
  `ENNReal.tsum_*` for summability. Search `Mathlib/Probability/BorelCantelli.lean`
  and `Mathlib/MeasureTheory/.../Borel*`.

**Lemma C (deterministic dyadic chaining).** ✅ **DONE** this session —
`dyadic_holder_chaining` (see item 11). Its increment hypothesis is exactly:
`∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2^n →`
`  |f ((k+1)/2^n) − f (k/2^n)| ≤ C * ((1/2)^α)^n`,
and it outputs `∃ K ≥ 0, ∀ s,t ∈ dyadics, 0≤s≤1, 0≤t≤1, |s−t| ≤ (1/2)^N →`
`  |f s − f t| ≤ K·|s−t|^α`. So Lemmas A+B below need only produce, a.s., that
increment hypothesis (with `f := fun x => X x ω`, some `C ≥ 0`, some `N(ω)`).

### Remaining step 1 — probabilistic increment bound (Lemmas A + B)

Goal: `∀ᵐ ω ∂P, ∃ N : ℕ, ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k+1 ≤ 2^n →`
`  |X ((k+1)/2^n) ω − X (k/2^n) ω| ≤ ((1/2)^α)^n` (i.e. `C = 1`).

Fix `α` with `0 < α < (q−1)/p` (exists: `q>1, p>0`). Let `r := (1/2)^α ∈ (0,1)`.

**Lemma A (per-level bad set).** `A n := ⋃_{k=0}^{2^n−1} {ω | rⁿ < |X((k+1)/2^n)ω − X(k/2^n)ω|}`.
Target: `P(A n) ≤ ENNReal.ofReal ((M:ℝ) · ρ^n)` with `ρ := (1/2)^(q−αp−1) ∈ (0,1)`.
Route (now that `kolmogorov_real_tail_bound` is available):
  - `measure_biUnion_finset_le (Finset.range (2^n))` ⇒
    `P(A n) ≤ ∑_{k<2^n} P {ω | rⁿ < |incr_{n,k}|}`;
  - each summand `≤ M · edist(k/2^n,(k+1)/2^n)^q / (ofReal rⁿ)^p` by
    `kolmogorov_real_tail_bound … (hlam := rⁿ > 0)`;
  - `edist (↑k/2^n) (↑(k+1)/2^n) = ENNReal.ofReal ((1/2)^n)` (compute the gap `1/2^n`);
  - push to reals: `(ofReal a)^q = ofReal (a^q)` via `ENNReal.ofReal_rpow_of_pos`,
    `M * ofReal x / ofReal y = ofReal (M·x/y)` via `ENNReal.ofReal_mul/ofReal_div_of_pos`;
  - sum of `2^n` equal terms = `ofReal (2^n · M · ((1/2)^n)^q / ((1/2)^{αn})^p)`;
  - **the exponent identity** (the genuinely fiddly bit, do it in ℝ then `ofReal`):
    `2^n · ((1/2)^n)^q / ((1/2)^{αn})^p = ((1/2)^(q−αp−1))^n = ρ^n`. Prove via
    `Real.rpow_natCast`/`Real.rpow_mul` to turn each `(·)^{nat}`-of-`rpow` into a
    single `(1/2)^(real·n)`, then combine exponents `−nq + αnp + n = −n(q−αp−1)`.
    Mirror the technique already used in `rpow_half_pow_le`.
  ⚠ Most ENNReal/rpow-heavy step. The real-only exponent collapse is already
    done: **`kc_exponent_identity`** proves, in ℝ,
    `2^n · ((1/2)^n)^q / ((1/2)^α)^n)^p = ((1/2)^(q−αp−1))^n`. So Lemma A now
    reduces to: union bound (`measure_biUnion_finset_le`) + per-term
    `kolmogorov_real_tail_bound` + the `ofReal`/`edist` pushforward, then
    `rw [kc_exponent_identity]` to land on `ofReal ((M:ℝ) · ρ^n)`, `ρ < 1`.

**Lemma B (Borel–Cantelli).** `∑ₙ P(A n) < ∞` (geometric, ratio `2^(−(q−1−αp)) < 1`).
Use `MeasureTheory.measure_limsup_atTop_eq_zero` (summable family ⇒ `P(limsup Aₙ)=0`),
giving a.e. `ω`: `∃ N, ∀ n ≥ N, ω ∉ A n`, i.e. every level-`n` increment with
`0 ≤ k < 2^n` is `≤ rⁿ`. (Off `[0,1)` the `k+1 ≤ 2^n` constraint of
`dyadic_holder_chaining` confines `k` to `0..2^n−1`, matching `A n`.)
  ⚠ Confirm the exact Borel–Cantelli name on the pin: search
  `Mathlib/Probability/BorelCantelli.lean`, `measure_limsup_atTop_eq_zero`,
  `ENNReal`-summable hypotheses.

### Remaining step 2 — extension (scale-limited)

`dyadic_holder_chaining` gives Hölder only for `|s−t| ≤ 2^{−N}`. That is enough
for UNIFORM continuity on the dyadics (for `ε`, take `δ = min(2^{−N}, (ε/K)^{1/α})`).
So generalize `holder_dense_extends_continuous` to a hypothesis
`∀ s t ∈ D, |s−t| ≤ δ₀ → |f s − f t| ≤ K|s−t|^α` (`δ₀ > 0`); the existing UC
proof only needs `δ := min δ₀ ((ε/C)^{1/α})`. This variant still yields a global
continuous extension on ℝ. ⚠ Note: the bound is `[0,1]`-localized in `s,t`, so
the extension is naturally on `[0,1]` — do the extension on `[0,1]` (D = dyadics
∩ [0,1], dense in [0,1]); see patching.

### Remaining step 3 — assembly on [0,1] + ℝ patching

Assembly on `[0,1]`: per good `ω`, `dyadic_holder_chaining` gives the scale-
limited Hölder bound; extend to continuous `Y(·)ω` on `[0,1]`, agreeing with
`X(·)ω` on dyadics; off the null set set `Y := 0`. Then
`∀ᵐ ω, ContinuousOn (Y · ω) [0,1]` and `∀ dyadic s, ∀ᵐ ω, Y s ω = X s ω`;
apply `kolmogorov_modification_ae_eq` (restricted to `[0,1]`).

Patching ℝ: `ℝ = ⋃_{j∈ℤ} [j,j+1]`. Apply the `[0,1]` construction to the shifted
process `X(·+j)` (the Kolmogorov condition is translation-invariant: `edist`
depends only on `|s−t|`), giving continuous `Y_j` on `[j,j+1]`. On a full-measure
set the pieces agree at integer endpoints (both `=ᵐ X j`), so glue:
`Y` is continuous because it is `ContinuousOn` each closed `[j,j+1]` and these
form a locally finite closed cover overlapping at integers (mathlib:
`continuousOn_of_locallyFinite` / glue via `ContinuousAt` from one-sided pieces).
Countable intersection of the per-`j` full-measure sets stays full.
  ⚠ The glue is the fiddliest non-mathematical step; budget it.

## Discipline / guardrails for the next session

- Keep the `axiom kolmogorovChentsov_modification` IN PLACE until the theorem is
  100% `sorry`-free. Do NOT introduce any `sorry` into a built module (it would
  break `tools/sorry_baseline.txt`, which must stay at exactly the one documented
  Picard entry). Develop Lemmas A/B/C as standalone sorry-free lemmas first;
  only when the full `theorem kolmogorovChentsov_modification := …` is complete
  do you (a) delete the axiom, (b) point `brownian_continuous_modification` at
  the theorem, (c) drop entry #3 from `tools/cited_axioms.md` (the
  `grep -c "^### [0-9]"` count goes 14 → 13), (d) update `_audit.lean` if needed,
  (e) confirm `lint.sh` shows one fewer axiom.
- After the swap, `brownian_continuous_modification` and the audit line for
  `kolmogorovChentsov_modification` should show only `propext/Classical.choice/
  Quot.sound` (no `kolmogorovChentsov_modification` axiom).
- Four-way invariant (`lake build`, `lint.sh`, `verify_import_contract.sh`, +
  the dissertation leg) green after every commit.

## Status update (2026-06-16, session 2)

- **Completed the entire deterministic dyadic chaining** (items 5–11 above),
  all sorry-free and committed: truncation API, single-step, telescope,
  cross-point step, dyadic eventual-equality, geometric tail bound, dyadic scale
  selection, the `((1/2)^α)^m ≤ 2^α d^α` rpow comparison, and the assembled
  `dyadic_holder_chaining` (KS 2.2.8's chaining, the hard combinatorial core).
- Remaining to close the axiom: Lemma A (per-level union bound — ENNReal-heavy),
  Lemma B (Borel–Cantelli summability), the scale-limited extension variant, the
  `[0,1]` assembly, and the ℝ-patching glue. These are now "plumbing": each has a
  precise plan above and uses only already-proven pieces + standard mathlib.
- The axiom `kolmogorovChentsov_modification` remains IN PLACE (untouched); the
  library is green (zero new sorries, 14 cited axioms unchanged).

## Status (2026-06-16, session 1)

- Added `kolmogorov_markov_bound` (sorry-free) and refactored
  `kolmogorov_modification_ae_eq` to consume it (net code reduction).
- Confirmed mathlib still lacks the continuity conclusion.
- Remaining: Lemmas A (per-level union bound), B (Borel–Cantelli summability),
  C (dyadic chaining — the bulk), assembly, ℝ-patching. C is the critical path.
