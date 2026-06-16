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

These are the two "outer" thirds of the proof; the missing third is the middle
(a.s. dyadic Hölder construction).

1. `holder_dense_extends_continuous` — **extension step.** An α-Hölder function
   on a dense set `D ⊆ ℝ` extends to a (unique) continuous function on ℝ, equal
   to `f` on `D`. Proof via `Dense.uniformContinuous_extend`. *(DONE)*

2. `dyadicRationals`, `zero_mem_…`, `intCast_mem_…`, `dense_dyadicRationals`,
   `exists_seq_dyadic_tendsto` — the dense dyadic set + a dyadic sequence
   `↗ t` for every `t`. *(DONE)*

3. `kolmogorov_markov_bound` *(NEW this session, sorry-free)* — the per-pair
   Markov/Chebyshev tail bound
   `P {ω | lam ≤ edist (X s ω) (X t ω)} ≤ M * edist s t ^ q / lam ^ p`
   for `0 < lam < ⊤`. This is the foundation of BOTH the convergence-in-measure
   step (4) and the missing per-dyadic-level Borel–Cantelli step. Already used
   to simplify (4).

4. `kolmogorov_modification_ae_eq` — **a.e.-equality step.** GIVEN a candidate
   `Y` that is a.s. continuous and a.s. equals `X` on every dyadic, concludes
   `∀ t, Y t =ᵐ[P] X t` (the modification property). Proof: `X(u_n) → X(t)` in
   measure (via `kolmogorov_markov_bound` + `u_n → t`), extract an a.s.-convergent
   subsequence, and use continuity of `Y` + dyadic agreement + limit uniqueness.
   *(DONE)*

So the remaining gap is: **construct that `Y`.** Concretely, prove that the
dyadic restriction `t ↦ X t ω` is a.s. α-Hölder on `dyadicRationals`, then feed
`holder_dense_extends_continuous` (per ω, on the full-measure Hölder set) to get
`Y`, with `Y = X` on dyadics by construction, and apply
`kolmogorov_modification_ae_eq`.

## The missing middle third — proof plan (Karatzas–Shreve 2.2.8 / Le Gall 2.9)

Work first on a **bounded interval** `[0, 1]` (or `[0, T]`), then patch ℝ as a
countable union of unit intervals (see "Patching" below).

Fix `α` with `0 < α < (q - 1) / p` (exists since `q > 1, p > 0`). Then
`q - α·p > 1`, i.e. the exponent below is `< 0`.

**Lemma A (per-level bound).** For level `n`, let
`A n := {ω | ∃ k : Fin (2^n), 2^(-α n) ≤ edist (X (k/2^n) ω) (X ((k+1)/2^n) ω)}`
(consecutive dyadic increments at resolution `2^n` inside `[0,1]`). Then

  `P (A n) ≤ ∑_{k<2^n} M * (2^(-n))^q / (2^(-αn))^p = M * 2^(n(1 - q + α p))`.

Proof: `measure_iUnion_fin_le`/`measure_biUnion_finset_le` over `k`, each term
bounded by `kolmogorov_markov_bound (k/2^n) ((k+1)/2^n) …` with
`edist (k/2^n) ((k+1)/2^n) = ENNReal.ofReal (2^(-n))` and `lam = 2^(-αn)`. Note
`edist` on ℝ is `ofReal |·|`; the dyadic gap is `2^(-n)`.

**Lemma B (Borel–Cantelli).** `∑_n P (A n) < ∞` because `1 - q + αp < 0`
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

**Lemma C (deterministic dyadic chaining — the hard combinatorial core).**
Fix `ω` with the "good" property from B (call the level `N`). Claim: there is a
constant `C` (depending on `α`, `N(ω)`) such that for all dyadic `s, t ∈ [0,1]`,
`|X s ω - X t ω| ≤ C * |s - t|^α`.

Standard proof (KS 2.2.8): for dyadic `s < t` in `[0,1]` with
`2^(-(m+1)) < t - s ≤ 2^(-m)` (so `m ≥ N`), write each of `s, t` as a finite
sum of dyadic steps refining from level `m`; telescope using the good bound
`|increment at level n| < 2^(-αn)` at each level `n > m`, giving a geometric
sum `≤ 2 * ∑_{n>m} 2^(-αn) = C' 2^(-αm) ≤ C |t - s|^α`. This is the step with
**no mathlib support** — it is the bulk of the remaining work. Suggested
decomposition into Lean-sized pieces:

  C1. "One-step refinement": any dyadic in `[k/2^n, (k+1)/2^n]` at level `n+1`
      is `k/2^n` or the midpoint; bound `|X(dyadic) - X(k/2^n)|` by one good
      increment.
  C2. "Dyadic expansion": every dyadic `x ∈ [0,1]` with denominator `2^L` equals
      `(⌊x·2^m⌋/2^m)` plus a finite sum of level-`(m+1..L)` midpoint steps;
      bound `|X x ω - X(⌊x·2^m⌋/2^m) ω| ≤ ∑_{n=m+1}^L 2^(-αn) ≤ C 2^(-αm)`.
  C3. Combine for `s, t`: pick `m` with `2^(-(m+1)) < |t-s| ≤ 2^(-m)`; `s, t`
      share (or are adjacent on) level-`m` grid; bound via two C2 tails plus at
      most one level-`m` increment. Yields `|X s ω - X t ω| ≤ C |t-s|^α`.

  This is finicky in Lean (index bookkeeping over `Fin`, `Int.floor`, `zpow`).
  Budget it as its own session. Consider proving C on `[0,1]` with denominators
  bounded, i.e. for dyadics `k·2^(-L)`, by induction on `L`.

**Assembly on [0,1].** From C, per good `ω`, `t ↦ X t ω` is α-Hölder on
`dyadicRationals ∩ [0,1]`; `holder_dense_extends_continuous` (with `D` the
dyadics, dense; note we need density of the dyadics used — restrict to `[0,1]`
or use all dyadics with the global Hölder bound) yields a continuous
`Y(·) ω` equal to `X(·) ω` on dyadics. Define `Y t ω := extend …` on the good
set and `Y t ω := 0` off it (a null set). Then:
  - `∀ᵐ ω, Continuous (Y · ω)` — good set is full measure.
  - `∀ s ∈ dyadics, ∀ᵐ ω, Y s ω = X s ω` — by the extension's agreement on `D`.
Apply `kolmogorov_modification_ae_eq` to get `∀ t, Y t =ᵐ X t`. ∎ (on [0,1])

**Patching ℝ.** The axiom is on all of ℝ. Two options:
  (i) Run the [0,1] construction on each `[j, j+1]`, `j : ℤ`; on a full-measure
      set the pieces agree at integer endpoints (both equal `X j` a.s. via the
      ae_eq), so they glue to a global continuous `Y`. Countable intersection of
      full sets is full. Slightly fiddly at the seams.
  (ii) Cleaner: redo Lemmas A–C directly with dyadics on each `[j, j+1]` and a
      per-`j` Hölder constant, then the GLOBAL function is continuous because it
      is continuous on each closed unit interval and they overlap at integers.
      `holder_dense_extends_continuous` is already stated for `D ⊆ ℝ` dense in
      all of ℝ, so if Lemma C is proved globally (Hölder for ALL dyadic `s,t`
      with `|s-t| ≤ 1`, constant depending on the unit interval), the extension
      is directly global. Recommended: prove C as "local α-Hölder with modulus
      valid for `|s-t| ≤ 1`", which is enough for uniform continuity hence the
      extend.

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

## Status this session (2026-06-16)

- Added `kolmogorov_markov_bound` (sorry-free) and refactored
  `kolmogorov_modification_ae_eq` to consume it (net code reduction).
- Confirmed mathlib still lacks the continuity conclusion.
- Remaining: Lemmas A (per-level union bound), B (Borel–Cantelli summability),
  C (dyadic chaining — the bulk), assembly, ℝ-patching. C is the critical path.
