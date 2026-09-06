# Prove2Me — plan of record for this repository

**Status: PLAN ONLY. Nothing has been uploaded. No account exists yet.**
Written 2026-09-05 on branch `claude/fermats-last-theorem-49ojhj`.

Companion file: `../Dissertation/PROVE2ME.md`. Read that one first for the platform
mechanics and the honesty rule; this file covers only what is specific to
LevyStochCalc. Origin: Anthropic's *Formalizing Fermat's Last Theorem* (2026-09-04),
assembled on **Prove2Me** (<https://prove2.me>, arXiv:2608.28433).

---

## 1. Why this repo is the interesting one

The dissertation's Level-A/Level-C gap bottoms out **here**. `PaperC_CoverageMatrix.md`
names one open analytic boundary — `BackwardStepStochasticInputs` — and its discharge
is a LevyStochCalc problem (Jacod–Yor PRP + Itô–Lévy isometry from real increments).
`GOAL.md` §1.A already demands what Prove2Me would make publicly checkable:

- **10 live cited axioms** (`grep -c "^### [0-9]" tools/cited_axioms.md`; #1 closed 2026-09-05)
- **1 real `sorry`** — `PicardSpace.lean:955`, surfacing as 4 baseline entries in
  `tools/sorry_baseline.txt`
- **6 of those axioms gate the pinned dissertation surface** (`Plan.md`): #5, #6, #15,
  #16, #9, #10 — of which #5 and #17 are since closed, leaving #6, #15, #16, #9, #10

That list is not a weakness to hide. On Prove2Me it is a **ready-made decomposition
DAG**: each cited axiom is a published theorem from the literature, which is exactly
what the platform's `source` field is designed to carry ("Applebaum, *Lévy Processes and
Stochastic Calculus*, 2nd ed., CUP 2009, Theorem 2.3.1"). Every entry in
`tools/cited_axioms.md` already contains a precise citation — the expensive part of a
`submit-problem` payload is done.

**The honest gain, stated precisely:** an `axiom` in a Lean file is trusted silently by
every downstream consumer, and its existence is discoverable only by reading a markdown
ledger. The same statement as an **Open theorem on Prove2Me** is trusted by nobody, is
visible to everybody, and makes any consumer that imports it `SKETCH_ACCEPTED` rather
than `Proved` until it is discharged. That is the `GOAL.md` §2 audit lens
("existence by fiat", "inconsistent axiom set") enforced by a machine instead of by
discipline. It is also the only mechanism here that could bring in outside help.

Do **not** invert this. Uploading a `Proved` wrapper whose hardness has been relocated
into an assumed hypothesis field is the de-citation failure mode `../Dissertation/CLAUDE.md`
explicitly forbids ("de-citation must be genuine discharge, not relocation of an axiom's
statement into a (possibly false) hypothesis field"). A green badge earned that way is
worse than the axiom it replaced, because the axiom was at least labelled.

---

## 2. The environment problem (blocking, and worth fixing anyway)

| | toolchain | Mathlib |
|---|---|---|
| **This repo** (`master` / this branch) | `v4.30.0-rc2` | `0e208554a6143756c125878a8fe8b17a331d39f7` |
| Dissertation | `v4.30.0` | `c5ea00351c28e24afc9f0f84379aa41082b1188f` |
| Prove2Me env #2 | `v4.30.0` | `c5ea003…` ✅ |
| Prove2Me default env | `v4.33.1` | `0df444a…` |

**Update 2026-09-05 (decision D1).** Both repos now sit on Mathlib `81a5d257` / Lean `v4.32.0`
(formal-mathfin's pin). The cross-repo discrepancy below is resolved; the Prove2Me mismatch is
now *shared* by both repos and accepted knowingly — the platform's nearest environments are
`c5ea003` (v4.30.0) behind and `0df444a` (v4.33.1) ahead.

**This repo's pin matched no Prove2Me environment.** The Dissertation's matches one
exactly. Two independent consequences:

1. **Prove2Me is blocked here until the pin moves to `c5ea003…` / `v4.30.0`.** There is
   no cross-environment import: a theorem in one env is invisible from another, so
   LevyStochCalc nodes could not be imported by Dissertation nodes at all.
2. **Independently of Prove2Me, this looks like a live inconsistency.** The Dissertation's
   `README.md` states its pin was "bumped from `v4.30.0-rc2` 2026-06-19 to match the live
   `LevyStochCalc`" — but `master` here is still on `v4.30.0-rc2` / `0e208554…`, and
   `lake-manifest.json` has `fixedToolchain: true`. Because Lake resolves Mathlib from
   the *root* package, a Dissertation build silently compiles these sources against
   `c5ea003…` while `lake build` here uses `0e208554…`. The two builds are not testing
   the same thing. **Verify this on the real machine before acting on it** — the
   `../LevyStochCalc-diss` working-tree override described in `../Dissertation/CLAUDE.md`
   may already carry a bumped pin that is deliberately never committed.

`Plan.md`'s rules of engagement say "**No pin bump** (cross-repo mismatch risk)". That
rule was written to protect the Dissertation build. If the Dissertation has already
moved, the rule now points the other way, and a bump *closes* a mismatch instead of
opening one. This is a judgement call for Christian, not a change to make unilaterally:
a Mathlib bump across 11 axioms and ~28k lines of stochastic analysis is a real project.

**Gate before any Prove2Me work here:** `lake build` green on `c5ea003…` / `v4.30.0`,
`bash tools/lint.sh` at baseline, `bash tools/verify_import_contract.sh` passing, and the
Dissertation still building.

---

## 3. What to upload, in what order

Not the library. The **10 cited axioms as Open theorems**, plus the definitions their
statements need. That is a `submit-problem` batch, not the full-project transplant
playbook — a fundamentally smaller and safer job than the Dissertation's Stage 3–6.

Priority follows `GOAL.md` §3 (dissertation-critical path first), which for once
coincides with mathematical foundation order:

| Order | Axiom | Why first |
|---|---|---|
| 1 | #6 `itoIsometry_compensated_unified_existence` | `Plan.md` A2, in progress; #15/#16/#9/#10 all carry it transitively |
| 2 | #15 — retired 2026-09-06 (its Lean statement was trivially satisfiable; the content is #16) | — |
| 3 | #16 `itoLevyFormula_jumpResidual_canonical_axiom` | Itô–Lévy layer |
| 4 | #13b (conditional-expectation bridge); #13a retired 2026-09-06 as refutable — the PRP returns after X2 | **the Dissertation's `BackwardStepStochasticInputs` bottleneck** |
| 5 | #9, #10 — retired 2026-09-06 as refutable statements; restated after X2 | BSDEJ layer |
| 6 | #2, #4, #18 — all theorems since 2026-09-06 | were cited but off the pinned surface |

Then the `sorry`: `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`
(`PicardSpace.lean:955`) is a single Bielecki-norm contraction argument that four baseline
entries forward to. As an Open theorem with its Tang–Li citation it is a well-posed,
self-contained target — the best candidate on either repo for an outside agent to close.

**Sequencing rule:** a `submit-problem` payload is immutable. Write each statement against
`tools/cited_axioms.md`'s existing citation, and get an independent read-back
(`references/mission_auditor.md` — blind natural-language testimony of what the Lean says)
before submitting. A wrong hypothesis, published permanently, is worse than the axiom.

---

## 4. What does not change

Everything in `GOAL.md` and `CLAUDE.md` stands. Specifically:

- The four hard invariants stay green after every change: `lake build`,
  `tools/lint.sh`, `tools/verify_import_contract.sh`, and the Dissertation's `lake build`.
- The import contract (12 modules + 21 symbols) is untouched by any of this. Prove2Me
  nodes are a *parallel publication*, not a refactor; no pinned symbol moves.
- `GOAL.md` §1.B non-vacuity is **not** satisfied by a Prove2Me badge. A `Proved` verdict
  on a statement with contradictory hypotheses is still vacuous — the platform type-checks,
  it does not audit meaning. `examples/Nonvacuity.lean` remains the artifact that does that
  job, and remains unwritten.
- Ponytail discipline: this file and the CLAUDE.md section are the whole documentation
  footprint of this idea. No dated copies, no parallel tracker.

## 5. Operational note

This session runs on Linux at `/home/user/LevyStochCalc`, not `D:\`. There is no elan,
lake, or Mathlib cache in this container, so none of the build gates above have been run
here — every build-state claim in this file is read from committed files and git history,
not from a build.
