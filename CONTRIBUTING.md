# Contributing to LevyStochCalc

Thanks for your interest in contributing!

## Setup

```
git clone <repo-url>
cd LevyStochCalc
lake update           # fetches Mathlib + deps
lake build            # 8402 jobs
bash tools/lint.sh    # checks build + sorry baseline
```

## Workflow

1. Open an issue describing what you intend to do.
2. Branch from `master`.
3. Build green (`lake build`) and lint pass (`bash tools/lint.sh`) before
   opening a PR.
4. Sign-off commits Mathlib-style with co-author attribution.

## Key principles (Rule 0)

* **Never weaken claims to match content.** If a theorem statement claims
  more than the proof delivers, fix the proof — don't relax the claim.
* **Never add new axioms** unless they are paper-cited theorems documented
  in `tools/cited_axioms.md` (Tier 1 cited axioms).
* **Never use trivial-witness patterns** — e.g., `refine ⟨0, 0, 0, …⟩` to
  satisfy a vacuous existential. Pin existentials to their literature
  integral forms.

## Adding a new theorem

1. State the theorem with the strongest hypotheses that make the conclusion
   true. Don't quantify over arbitrary measurable maps when the theorem only
   holds for predictable ones.
2. If proof is deferred, add the theorem name to `tools/sorry_baseline.txt`
   with the literature reference in the docstring.
3. Update `_audit.lean` to `#print axioms` the new theorem.
4. Verify `bash tools/lint.sh` still passes.

## Adding a new cited axiom

1. The axiom statement must match a published theorem citation precisely.
2. Add a Tier 1 entry to `tools/cited_axioms.md` with paper reference,
   Mathlib status, and replacement plan.
3. Update `_audit.lean` and `tools/full_audit.lean` to include it.
4. Verify `bash tools/lint.sh` still passes.

## Style

* Mathlib-style copyright headers in every file.
* Annotate `set_option maxHeartbeats N in` with an explanatory comment.
* Use `change` (not `show`) when the tactic mutates the goal.
* Replace deprecated Mathlib API uses as you encounter them.
* Prefer specific Mathlib imports over `import Mathlib` for faster incremental
  builds (Notation.lean and Basic.lean still use bare imports — see L3/L4 in
  the red-team backlog).

## Reviewing

Before merging, the reviewer should verify:
* `lake build` succeeds with no new warnings.
* `bash tools/lint.sh` passes at-or-below baseline.
* `_audit.lean` axiom set for affected theorems matches the documented
  Tier 1 inventory (no `sorryAx` leakage).
* No trivial-witness patterns in any new theorem statements or proofs.
