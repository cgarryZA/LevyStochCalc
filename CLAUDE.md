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

`tools/cited_axioms.md` is the per-axiom ledger of record — read it there rather than
re-deriving counts here. One cited axiom is live (#16, the Itô–Lévy formula's jump residual,
`Ito/JumpFormula.lean`), and it is the only `axiom` declaration in the repository. Of the rest,
nine are theorems, four were retired as unsound statements, and the others were deleted or
re-derived; the ledger's index says which. Two upstream `lake require`s at the shared Mathlib
pin are load-bearing: `RemyDegenne/brownian-motion` discharges Brownian existence (#1) and
supplies the càdlàg regularisation behind #6 and #13b; `raphaelrrcoelho/formal-mathfin`
supplies Doob's `L²` maximal inequality (`Probability/DoobContinuous.lean`) and an Itô–Lévy
isometry bridge (`Poisson/MathFinBridge.lean`) that #6 did not need in the end. Mathlib still
has no Itô integral, BSDE, Poisson random measure or PRP, so this math is being proved, not
ported. See `Plan.md`.

## Hard invariants (never break)

After every change, all four must stay green:

```
lake build
bash tools/lint.sh                    # axiom/sorry baseline
bash tools/verify_import_contract.sh  # dissertation import contract
# and: D:/Dissertation `lake build`
```

- **Import contract** (`tools/import_contract.md`): 12 modules + 19 symbols under
  `LevyStochCalc.*` must keep resolving from their pinned path. On in-tree
  splits, keep pinned symbols in the module of record (no forwarding stubs); a
  deliberate relocation updates the dissertation's import. Don't rename public
  symbols or the top-level namespace in-tree.
- **Mathlib gates** (for upstreamable code): 3 standard axioms only, no `sorry`,
  ≤100 cols, no `import Mathlib`, math-only docstrings. Disclose AI use + add the
  `LLM-generated` label on every mathlib PR.
- **Ponytail:** git is the archive (no in-tree dated copies); one idea per file;
  don't refactor speculatively; prefer the diff that deletes more than it adds.
- **`lake build`, not `lake env lean <file>`, after a cross-file change.** `lake env lean` on a
  single file type-checks it against the *existing* oleans of its imports; if you edited an
  import in the same round it silently checks against the stale one and reports success. Use it
  only for a self-contained file whose imports are already built.

## Reference docs

- `Plan.md` — the roadmap (start here).
- `tools/cited_axioms.md` — the per-axiom ledger: every cited result, its status, the
  declaration that carries it now, and the paper reference. Authoritative for counts.
- `tools/sorry_baseline.txt` — declarations still carrying `sorry` (one: the canonical assembly
  `itoLevyFormula_jumpResidual_canonical`, seven Stage-2 obligations).
- `_audit.lean` — `#print axioms` budget check (input to `tools/lint.sh`).

## Prove2Me (planned; nothing uploaded yet)

`PROVE2ME.md` is the plan of record for publishing on [Prove2Me](https://prove2.me), the
collaborative Lean platform Anthropic's FLT formalization was assembled on. The
`prove2me` skill under `.claude/skills/` loads the upstream agent skill.

- **Pin vs. environments.** Since decision D1 (2026-09-05) both repos sit on
  `leanprover/lean4:v4.32.0` / Mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`, which
  matches **no** Prove2Me environment (nearest: `c5ea003` behind, `0df444a` ahead, as the
  platform listed them on 2026-09-05). Imports never cross environments, so any upload is
  re-verified against the environment it targets; see `PROVE2ME.md`.
- **The payload is the debt, not the library.** That debt is one node: cited axiom #16,
  `itoLevyFormula_jumpResidual_canonical_axiom`. (`tools/sorry_baseline.txt` holds one further
  open node, the canonical assembly `itoLevyFormula_jumpResidual_canonical` with seven `sorry`
  obligations; it is Stage-2 work, not an upload candidate.) The axiom already carries a
  precise literature citation in
  `tools/cited_axioms.md`; publishing it makes the boundary machine-visible instead of
  ledger-visible. The four statements retired as unsound in 2026-09 (#9, #10, #13a, #15) are
  *not* upload candidates until they are restated (`Plan.md` A6, A7, B5).
- **A badge is not non-vacuity.** `GOAL.md` §1.B is unaffected by any platform verdict;
  the platform type-checks, it does not audit meaning.
