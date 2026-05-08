# `stochasticIntegral_strong_exists_brownian` — diagnosis and refactor plan

## Current statement (in `LevyStochCalc/Brownian/Ito.lean`)

```lean
private lemma stochasticIntegral_strong_exists_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      ∀ T, 0 < T → Measurable (Function.uncurry H) →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
```

## Why the current statement is unprovable for arbitrary `H`

The statement quantifies over **all** `H : Ω → ℝ → ℝ` with no
measurability or integrability hypothesis. This makes the
**unconditional conjunct 2** mathematically impossible:

> Conjunct 2: `Martingale (fun t ω => (F t ω) ^ 2 - ∫_0^t (H ω s)^2 ds) Filt P`

For any `F` chosen, conjunct 2 demands the process
`G_t(ω) := (F_t ω)² − ∫_0^t (H ω s)² ds` be a martingale. Take
`F = 0` (the natural "trivial" witness for non-measurable `H`):

* `G_t = −∫_0^t (H ω s)² ds`.
* `∫_0^t (H ω s)² ds` is **non-decreasing** in `t` (the integrand
  `(H ω s)²` is non-negative).
* `−∫_0^t (H ω s)² ds` is therefore non-increasing in `t`.
* A non-increasing process is a martingale **iff** it is constant in
  `t`, equivalent to `(H ω s)² = 0` for almost every `s` — i.e.,
  `H ≡ 0` a.e. in `s` (for almost every `ω`).

So `F = 0` satisfies conjunct 2 only when `H ≡ 0`. Worse, **no**
constant-in-`ω` `F` can satisfy it because the martingale property
demands `F²` to grow at exactly the rate `∫_0^t H² ds` (this is
**Itô's quadratic-variation identity**: for `F` the genuine Itô
integral, `F²_t − ∫_0^t H²_s ds` IS a martingale; for any other
`F`, it is not, because the quadratic-variation process is the
unique pathwise quadratic variation of the integral).

Concretely: take `H ω s = 1` (constant). Then `∫_0^t 1² ds = t`.
Conjunct 2 with `F = 0` becomes "`-t` is a martingale", which is
false for any non-trivial filtration with multiple time levels.

The same obstruction occurs if `H` is jointly measurable but
non-`L²`-integrable: the Bochner integral `∫_0^t (H ω s)² ds` may
be finite or `0` (by Mathlib's convention for non-Bochner-integrable
functions), but its `t`-dependence is not martingale-shaped without
`F` matching the Itô integral.

## What the strong-exists is `actually` claiming (literature)

The literature theorem (Karatzas–Shreve 1991 §3.2.B; Revuz–Yor 1999
III.1.4) constructs the **L² Itô integral** for **predictable
square-integrable integrands** `H ∈ L²(P × ds)`. The conditions are:

* `H : Ω → ℝ → ℝ` is **jointly measurable** (`Function.uncurry H` is
  measurable).
* `H` is **adapted** (or more generally **predictable**) wrt the
  Brownian filtration.
* `H ∈ L²(P × ds)` on `[0, T]` (square-integrability):
  `∫⁻ ω, ∫⁻ s in [0, T], ‖H ω s‖₊² ∂vol ∂P < ⊤`.

Under these hypotheses, the Itô integral `M_t = ∫_0^t H_s dW_s`
exists, is a martingale, has quadratic variation `⟨M⟩_t = ∫_0^t H_s²
ds`, and satisfies the L² isometry. **All three conjuncts of the
strong-exists are provable.** Without these hypotheses, the
strong-exists is false (as shown above).

## Refactor plan (Option β)

Rewrite the strong-exists to take the literature hypotheses as
inputs:

```lean
private lemma stochasticIntegral_strong_exists_brownian
    {P : Measure Ω} [IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (hH_meas : Measurable (Function.uncurry H))
    (hH_adapt : ∀ s, AEStronglyMeasurable
      (fun ω => H ω s) (P.trim
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le' s)))
    (hH_sq_int : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      ∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
```

(The conditional `Measurable + h_sq_int` of conjunct 3 in the old
statement is now subsumed by the global hypotheses.)

## Caller impact

Only callers within `LevyStochCalc/Brownian/Ito.lean` use the
strong-exists. They are:

1. `noncomputable def stochasticIntegral` — uses `Classical.choose`
   on the strong-exists. Will need a measurability/sq-integrability
   hypothesis (or fallback to a default value when not satisfied).
2. `theorem itoIsometry` — already takes `Measurable + h_sq_int`. Can
   pass them to the refactored strong-exists.
3. `theorem quadVar_stochasticIntegral` — currently unconditional.
   Will need to take measurability + sq-integrability + adaptedness.
4. `theorem martingale_stochasticIntegral` — currently unconditional.
   Same as above.

The refactor strengthens (3) and (4) with explicit hypotheses, which
matches the literature statements (Karatzas–Shreve Theorem 3.2.6
explicitly requires `H ∈ L²(P × ds)` for the martingale property).

## Construction of `F` (after refactor)

With the new hypotheses in hand:

* For each fixed `T > 0`, apply `simplePredictable_dense_L2` to get
  an approximating sequence `Hn : ℕ → SimplePredictable Ω T` with
  `(Hn n).eval → H` in `L²(P × ds)` on `[0, T]`. The sequence is
  also adapted (use the dyadic construction's structure with
  `hH_adapt`).
* By C0b.9 `cauchy_of_L2_dense_simple`, the simpleIntegrals are
  L²-Cauchy in `Lp ℝ 2 P`.
* By C0b.10 `itoIntegralLp_brownian` + Lp completeness, the L²-limit
  exists.
* `F(T)(ω) := ↑↑(itoIntegralLp_brownian ...) ω` (extracted via
  `Lp.coeFn`).
* For `t ≠ T`, similarly using the same `(Hn)` truncated to `[0, t]`.

The conjuncts then follow:

* **Conjunct 1** (Martingale `F`): each `simpleIntegral W (Hn) t` is
  a martingale (by `martingale_simpleIntegral_brownian`). The L²
  limit of L²-bounded martingales is a martingale by
  `MeasureTheory.tendsto_eLpNorm_condExp` (Mathlib) +
  `MeasureTheory.condExp_continuous` continuity in L¹.
* **Conjunct 2** (Martingale `F² − ∫H²`): the simples-version
  identity `(simpleIntegral H_n)² − ∫_0^t (H_n.eval)²` is a martingale
  (Itô's identity at simples — needs `quadVar_simpleIntegral_brownian`,
  which is a separate sub-task: the orthogonal-increments expansion
  `(F_t − F_s)² = ∑ ξ_i² (ΔW_i)²` mod cross terms vanishing, plus
  the variance identity `E[(ΔW_i)² | ℱ_{t_i}] = Δt_i`). Take L²-limits.
* **Conjunct 3** (isometry at `T`): direct from
  `itoIntegralLp_brownian_L2_isometry` (already closed in C0b.10-post7)
  + `Lp.enorm_def`.

## Sub-tasks for closure

- [ ] Step 1 (this note): committed.
- [ ] Step 2: enumerate callers via `grep`.
- [ ] Step 3: refactor strong-exists signature; update callers.
- [ ] Step 4: build `F` from `exists_itoIntegralL2_brownian` +
      time-parametrization.
- [ ] Step 5: prove conjunct 1 via L²-limit-of-martingales.
- [ ] Step 6: prove conjunct 2 — needs `quadVar_simpleIntegral_brownian`
      (also a baseline-blocking sorry) + L²-limit of quadVar property.
- [ ] Step 7: prove conjunct 3 via post7 + integrability cast.
- [ ] Step 8: remove `stochasticIntegral_strong_exists_brownian` from
      baseline.
- [ ] Step 9: remove `Brownian.Ito.{itoIsometry,
      quadVar_stochasticIntegral, martingale_stochasticIntegral}`
      from baseline.
- [ ] Step 10: mirror for compensated Poisson side.

## References

- Karatzas, I.; Shreve, S. *Brownian Motion and Stochastic Calculus*,
  Springer 1991, Chapter 3.
- Revuz, D.; Yor, M. *Continuous Martingales and Brownian Motion*,
  Springer 1999, Chapter III §1–4.
- Protter, P. *Stochastic Integration and Differential Equations*,
  Springer 2005, Chapter II.
