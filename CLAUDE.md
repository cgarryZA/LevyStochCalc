# CLAUDE.md

## Current plan — read this first

**The active roadmap lives in [`Plan.md`](Plan.md).** It is the single source of
truth for the refactor-to-mathlib effort: phases, the exact task checklist, the
per-axiom close-out order, and the destination map into mathlib's tree. Consult
it at the start of any session and keep it updated as tasks are checked off.

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
  `LevyStochCalc.*` must keep resolving; move/rename only behind a forwarding
  stub. Don't rename public symbols or the top-level namespace in-tree.
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
