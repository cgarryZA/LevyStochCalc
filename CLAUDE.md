# CLAUDE.md

## Where we're going, and how — read these first

- **[`GOAL.md`](GOAL.md) is the north star** — the invariant definition of done
  (zero sorries, zero custom axioms, no vacuity, mathlib-grade form,
  dissertation never regresses). It rarely changes. Use it to decide whether the
  work is finished and what the nearest gap is.
- **[`Plan.md`](Plan.md) is the current route** — the phases/task-checklist
  toward `GOAL.md`, with the per-axiom close-out order and the destination map
  into mathlib's tree. Consult it at the start of any session; keep it updated as
  tasks are checked off.

**Loop discipline.** Continue the current `Plan.md`. If every box in `Plan.md` is
checked but `GOAL.md`'s acceptance criteria are not all met, the plan is done
(git is its archive) — write a **new `Plan.md`** that closes the remaining
`GOAL.md` gaps (dissertation-blocking gaps first, per `GOAL.md` §3) and start
step 1. The work is complete only when every `GOAL.md` §1 box is checkable-true.

## What this repo is

A Lean 4 + Mathlib formalization of Lévy-driven stochastic calculus (L² Itô
integrals, the Itô–Lévy formula, BSDEs with jumps). It is the substrate the main
dissertation (`D:/Dissertation`) imports for its continuous-time foundations.

All 14 cited results are currently **upstream of** mathlib (no Itô integral,
BSDE, Poisson random measure, or PRP exists in mathlib yet), so the math here is
being proved, not ported. See `Plan.md` for the verified comparison.

## Hard invariants (never break)

After every change, all four must stay green:

```
lake build
bash tools/lint.sh                    # axiom/sorry baseline
bash tools/verify_import_contract.sh  # dissertation import contract
# and: D:/Dissertation `lake build`
```

- **Import contract** (`tools/import_contract.md`): 12 modules + 21 symbols under
  `LevyStochCalc.*` must keep resolving from their pinned path. On in-tree
  splits, keep pinned symbols in the module of record (no forwarding stubs); a
  deliberate relocation updates the dissertation's import. Don't rename public
  symbols or the top-level namespace in-tree.
- **Mathlib gates** (for upstreamable code): 3 standard axioms only, no `sorry`,
  ≤100 cols, no `import Mathlib`, math-only docstrings. Disclose AI use + add the
  `LLM-generated` label on every mathlib PR.
- **Ponytail:** git is the archive (no in-tree dated copies); one idea per file;
  don't refactor speculatively; prefer the diff that deletes more than it adds.

## Reference docs

- `Plan.md` — the roadmap (start here).
- `tools/cited_axioms.md` — the 14 axioms with paper references.
- `tools/sorry_baseline.txt` — currently-deferred theorems.
- `STATUS.md` — point-in-time build/axiom status.
- `_audit.lean` — `#print axioms` budget check (input to `tools/lint.sh`).

## Prove2Me (planned; nothing uploaded yet)

`PROVE2ME.md` is the plan of record for publishing on [Prove2Me](https://prove2.me), the
collaborative Lean platform Anthropic's FLT formalization was assembled on. The
`prove2me` skill under `.claude/skills/` loads the upstream agent skill.

- **Blocked on the pin.** Prove2Me has an environment at Mathlib
  `c5ea00351c28e24afc9f0f84379aa41082b1188f` / `v4.30.0` — the Dissertation's exact pin.
  This repo is on `0e208554…` / `v4.30.0-rc2` and matches none. Imports never cross
  environments, so nothing here can connect to Dissertation nodes until the pin moves.
  `Plan.md`'s "no pin bump" rule was written to protect the Dissertation build; verify on
  the real machine whether that repo has already moved ahead of us.
- **The payload is the debt, not the library.** The 11 cited axioms and the one
  `PicardSpace.lean` `sorry` are the natural Open nodes — each already carries a precise
  literature citation in `tools/cited_axioms.md`. Publishing them makes the boundary
  machine-visible instead of ledger-visible.
- **A badge is not non-vacuity.** `GOAL.md` §1.B is unaffected by any platform verdict;
  the platform type-checks, it does not audit meaning.
