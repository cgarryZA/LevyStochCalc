# Contributing to LevyStochCalc

Thanks for your interest in contributing! `GOAL.md` is the definition of done and `Plan.md` the
current route; read both first.

## Setup

```
git clone https://github.com/cgarryZA/LevyStochCalc.git
cd LevyStochCalc
lake exe cache get    # Mathlib's compiled cache
lake build
```

## Workflow

1. Open an issue describing what you intend to do.
2. Branch from `master`.
3. Before opening a PR, all of these pass:
   * `lake build` (not `lake env lean <file>`, which checks against stale imports after a
     cross-file change);
   * `bash tools/lint.sh` (build, axiom audit, documentation consistency);
   * `bash tools/verify_import_contract.sh` (the dissertation's import contract).
4. Sign off commits Mathlib-style with co-author attribution.

## Key principles

* **No `sorry`, no `axiom`.** `tools/sorry_baseline.txt` is empty and stays empty, and the
  library declares no axioms: every declaration reduces to `propext`, `Classical.choice` and
  `Quot.sound`. A result that cannot be proved yet is not added; it goes in `Plan.md` or an
  issue. `tools/cited_axioms.md` is the history of the axioms the library used to carry, not a
  place to add new ones.
* **Correct claims openly; never weaken them quietly.** If a statement says more than the
  proof delivers, the first job is to diagnose why. If the statement is true, fix the proof. If
  it is false, as several were (see `tools/cited_axioms.md`), say so in the PR, state the
  corrected result, and record what changed and why. Never relax a hypothesis or a conclusion
  just to get a proof through.
* **No vacuous statements.** No trivial-witness patterns (`refine ⟨0, 0, 0, …⟩` for a vacuous
  existential), and no hypotheses that cannot be satisfied together. A new headline result gets
  a non-vacuity example under `examples/` (`GOAL.md` §1.B).

## Adding a new theorem

1. State the intended mathematical result, with its assumptions explicit and each one needed.
   Prefer the more general statement when it costs nothing. Don't quantify over arbitrary
   measurable maps when the theorem only holds for predictable ones.
2. Give it a mathlib-style docstring: one or two sentences on the mathematical object, no
   history or audit status.
3. Add the theorem to `_audit.lean`, which must cover every declaration
   `tools/gen_audit_names.lean` lists.
4. Check that `bash tools/lint.sh` passes.

## Style

* Mathlib-style copyright headers in every file.
* Lines at most 100 columns; specific Mathlib imports, never `import Mathlib`.
* One idea per file. Git is the archive: no dated copies in the tree.
* Annotate `set_option maxHeartbeats N in` with an explanatory comment.
* Replace deprecated Mathlib API uses as you encounter them.
* Don't rename public symbols or move modules pinned in `tools/import_contract.md`; a deliberate
  relocation updates the contract and its consumers in the same change.

## Reviewing

Before merging, the reviewer checks that:
* `lake build` succeeds with no new warnings;
* `bash tools/lint.sh` and `bash tools/verify_import_contract.sh` pass;
* the audit reports only `propext`, `Classical.choice` and `Quot.sound` for every name;
* each new statement says what its docstring and the cited source say: a kernel check does not
  make a statement faithful;
* no new theorem statement or proof uses a trivial-witness pattern.
