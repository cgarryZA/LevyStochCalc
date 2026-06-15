# GOAL.md — the end state (north star)

This file is the **invariant definition of done**. Unlike `Plan.md` (the current
route, regenerated as phases complete), `GOAL.md` does not change as work
progresses — it changes only if the *destination itself* changes. Every session
should be able to read this file and answer one question: *are we done yet, and
if not, what is the nearest gap?*

> **Loop contract.** When `Plan.md` is fully checked off but the acceptance
> criteria below are **not** all met, the old plan is finished — git history is
> its archive. Write a **new `Plan.md`** whose phases close the remaining
> `GOAL.md` gaps (smallest, dissertation-blocking gaps first; see §3), then begin
> step 1 of the new plan. We are *done* only when every box in §1 is checkable-true.

---

## 1. Acceptance criteria (all must hold)

A criterion is "done" only if it is **mechanically checkable** and currently
checks true. Each lists how to verify it.

### A. Soundness — no cheats, no holes
- [ ] **Zero `sorry`/`admit`/`sorryAx`.** `tools/sorry_baseline.txt` is empty;
      `grep -rn '\bsorry\b\|\badmit\b' LevyStochCalc/` finds only prose.
- [ ] **Zero custom axioms.** `#print axioms` over the *entire public API*
      (extend `_audit.lean` to cover every exported decl) prints only
      `propext`, `Classical.choice`, `Quot.sound`. `tools/cited_axioms.md` lists
      no live `axiom` (it becomes a provenance/history note, not a budget).
- [ ] **No trust escapes.** No `native_decide`, `@[implemented_by]`, `@[extern]`,
      `opaque`, `unsafe`, `partial def`, or `set_option … (kernel|debug).*` in
      load-bearing math. `Float` never appears in a statement.

### B. Non-vacuity — the theorems mean something
This is the criterion a naive "zero sorry" pass misses. A theorem can be fully
proved and still say nothing. For **every headline result** (the 14 cited results
in `tools/cited_axioms.md` and every symbol in `tools/import_contract.md`):
- [ ] **Objects are inhabited, not assumed.** Existence is a *proved theorem*
      with a *constructed* witness — never a `Classical.choose` of an existence
      axiom, and never `[Nonempty _]`/`[Inhabited _]` summoning junk. (BM,
      Poisson random measure, the Itô/compensated integrals, and the BSDEJ
      solution each have a real construction.)
- [ ] **Hypotheses are satisfiable.** For each theorem there is an `example`
      that discharges its hypotheses on a concrete, *non-degenerate* model — so
      it cannot be vacuously true via contradictory assumptions, an empty index
      type, or a measure-zero / empty carrier.
- [ ] **Conclusions are non-degenerate.** The objects are not secretly the
      trivial one (the zero process, the zero measure, `default`, `∅`, the
      constant map). e.g. the constructed BM has *non-zero* variance; the Itô
      integral is *not* identically `0`; the BSDEJ solution is the intended one,
      not the zero solution sneaking through a junk witness.
- [ ] **Statements are not trivially `True`.** Nothing reduces to `x = x`,
      `True`, `0 ≤ ‖·‖`, or an `Iff` whose sides are both trivial after
      unfolding; no result is only the `n = 0` / `T = 0` / `σ = 0` /
      deterministic special case wearing the general name.
- [ ] A single `examples/Nonvacuity.lean` (or similar) collects the per-result
      witnesses above and builds — making non-vacuity a CI-checked artifact, not
      a promise.

### C. Faithfulness — it models the right mathematics
- [ ] **Definitions match the literature** (Karatzas–Shreve / Applebaum /
      Jacod–Shiryaev as cited) and, where mathlib has the predicate, are tied to
      it (`IsBrownianReal`, `HasIndepIncrements`, `IsGaussianProcess`, …) rather
      than re-asserted weaker.
- [ ] **No silent over-assumption.** No unused hypotheses (`linter.unusedVariables`
      clean; a listed-but-unused hypothesis is a red flag that the statement is
      weaker than it reads). Quantifier order is the intended one (`∀∃` vs `∃∀`).

### D. Mathlib-grade form
- [ ] Every file ≤ ~600 lines, `section … variable … end` structured, **precise
      imports** (no `import Mathlib` umbrella), ≤100 columns.
- [ ] Docstrings are **math only** — no `Tier 1`, `red-team`, `Agent N`,
      milestone tags, dated change-logs, or `D:/…` paths.
- [ ] Upstreamable results live in the `ProbabilityTheory` namespace under
      `Mathlib/Probability/<Area>/…` shape and are registered.

### E. Dissertation never regresses (see §3 for priority)
- [ ] `tools/verify_import_contract.sh` passes; the dissertation at
      `D:/Dissertation` builds against this repo unmodified (forwarding stubs at
      old paths whenever something moves/renames).

### F. Upstreamed
- [ ] Every *closed, general* result is either merged into mathlib or has an open
      PR, each with AI-use disclosure + the `LLM-generated` label.

### G. Green
- [ ] CI is green: `lake build` · `tools/lint.sh` at baseline-0 ·
      `tools/verify_import_contract.sh` — on every commit.

---

## 2. Ways this can be silently wrong (audit checklist)

Run this lens whenever closing an axiom/`sorry` or writing a new statement. The
danger is always the proof that *succeeds* while proving the wrong/empty thing.

1. **Existence by fiat** — `Classical.choose` of an existence axiom gives an
   object with no usable properties; downstream "theorems" about it are vacuous.
   Fix: construct, then prove the characterizing API.
2. **Vacuous hypotheses** — `False`, contradictory typeclass assumptions, an
   empty/`Subsingleton` index, or a measure that is `0` makes everything provable
   and meaningless. Refute with a concrete satisfying `example`.
3. **Degenerate witness** — `∃ X, IsSolution X` discharged by the zero process;
   `∃ μ, …` by the zero measure. Demand a non-triviality conjunct.
4. **Special case mislabeled** — proving `n = 0`, `T = 0`, `σ = 0`, jump-free, or
   deterministic and naming it the general theorem.
5. **Trivial reduction** — statement is `True`/`x = x`/`0 ≤ ‖·‖`/both-trivial
   `Iff` after unfolding; `simp` closes it instantly because it says nothing.
6. **A.e./measure-zero hollow truth** — an a.e. equality that holds because the
   exceptional set is everything, or an integral identity over a null set.
7. **Definition drift** — a "Brownian motion" without independent increments /
   Gaussian law / continuity; a "martingale" without the filtration condition.
   Type-checks, models nothing.
8. **Over-assumption** — an unused hypothesis silently strengthens the premise;
   the theorem reads general but only fires in a corner.
9. **Quantifier inversion** — `∃ C, ∀ x` vs `∀ x, ∃ C`; the weak one is easy and
   wrong.
10. **Trust escape** — `native_decide`, `@[implemented_by]`, `opaque`, `unsafe`,
    `partial`, kernel/`decide` options; `autoImplicit true` turning a typo into a
    spurious universe/implicit variable.
11. **Inconsistent axiom set** — two axioms that jointly prove `False` (then
    *everything* is "provable"). Eliminating all custom axioms closes this for
    good; until then, sanity-check new axioms against a model.
12. **Lying docstring** — claims a property the statement does not establish.

---

## 3. Prioritization — dissertation first

The dissertation at `D:/Dissertation` consumes a fixed surface
(`tools/import_contract.md`: 12 modules + 21 symbols). That surface is the
**critical path** and orders the work:

1. **Never regress it.** Any change keeps the contract resolving and the
   dissertation building (criterion E) — this dominates all other goals.
2. **Harden it first.** When choosing which axiom/`sorry`/cleanup to tackle next,
   prefer the one **closest to a dissertation-consumed symbol** — close those
   gaps before purely-internal or not-yet-cited results.
3. **Then breadth.** Once the consumed surface is axiom-free and non-vacuous,
   widen to the rest of the library and to upstreaming (criteria D, F).

Within equal priority, follow the ponytail discipline (`CLAUDE.md`): smallest
diff, delete more than you add, one idea per file.

---

## 4. Relationship to the other docs

- **`GOAL.md`** (this file) — the destination. Rarely changes.
- **`Plan.md`** — the current route to the destination. Regenerated when
  exhausted (see the loop contract at the top).
- **`CLAUDE.md`** — the standing rules/invariants and a map of the repo.
- **`tools/import_contract.md`** — the dissertation surface (the §3 critical path).
- **`tools/cited_axioms.md`** / **`tools/sorry_baseline.txt`** — the live debt
  that criteria A and B must drive to zero.
