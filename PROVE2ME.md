# Prove2Me — plan of record for this repository

**Status: PLAN ONLY. Nothing has been uploaded. No account exists yet.**
Written 2026-09-05; every repository-state claim below was re-verified against the tree on
2026-09-08 (§5 says against what).

Companion file: `../Dissertation/PROVE2ME.md`. Read that one first for the platform
mechanics and the honesty rule; this file covers only what is specific to
LevyStochCalc. Origin: Anthropic's *Formalizing Fermat's Last Theorem* (2026-09-04),
assembled on **Prove2Me** (<https://prove2.me>, arXiv:2608.28433).

---

## 1. Why this repo is the interesting one

The dissertation's Level-A/Level-C gap bottoms out **here**. `PaperC_CoverageMatrix.md`
names one open analytic boundary — `BackwardStepStochasticInputs` — and its discharge
is a LevyStochCalc problem (Jacod–Yor PRP + Itô–Lévy isometry from real increments).
`GOAL.md` §1.A already demands what Prove2Me would make publicly checkable. That axiom debt
has shrunk to a single node:

- **1 live cited axiom** — #16 `itoLevyFormula_jumpResidual_canonical_axiom`
  (`grep -c "^### [0-9]" tools/cited_axioms.md` = 1). It is the only `axiom` declaration in
  the repository, at `LevyStochCalc/Ito/JumpFormula.lean:189`.
- **No `sorry`** — `tools/sorry_baseline.txt` is empty, no `#print axioms` report names
  `sorryAx`, and `sorry`/`admit` occur in the sources only as words inside docstrings. The
  Picard-chain wrap-up that carried the last `sorry` was discharged and deleted on 2026-09-07.
- **#16 is the whole of the pinned dissertation surface's axiom debt.** Exactly one
  dissertation declaration depends on it, `Dissertation.Continuous.itoLevyFormula` (through
  the library's `itoLevyFormula`); apart from #16 and its two consumers in
  `Ito/JumpFormula.lean`, every declaration in either repository's audit is on the three
  standard axioms. The other entries that once gated that surface — #5, #6, #9, #10, #15 —
  are theorems or retired.

The `BackwardStepStochasticInputs` boundary is a different kind of debt. Since A5-1
(2026-09-06) the library states no predictable representation property at all — #13a was
deleted as a refutable statement — so there is no Lean statement to publish for it until it
is restated (`Plan.md` B5; Epic A in `../Dissertation/WORK_BREAKDOWN.md`). An Open node
cannot carry a theorem that does not yet exist.

That is not a weakness to hide, and it is also no longer a decomposition DAG: it is one
problem. Each cited entry is a published theorem from the literature, which is exactly what
the platform's `source` field is designed to carry ("Applebaum, *Lévy Processes and Stochastic
Calculus*, 2nd ed., CUP 2009, Theorem 2.3.1"). Every entry in `tools/cited_axioms.md` already
contains a precise citation — the expensive part of a `submit-problem` payload is done.

**A caution that grew as the debt shrank.** Four entries (#9, #10, #13a, #15) were retired in
2026-09 because the *Lean* statement was refutable or trivially satisfiable while the citation
looked impeccable. A platform verdict would not have caught any of them: type-checking a
statement is not auditing it. Anything uploaded here must survive the read-back described
below before it is submitted, because uploaded statements are immutable.

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
| **This repo** (`lean-toolchain`, `lake-manifest.json`) | `v4.32.0` | `81a5d257…` |
| Dissertation (same two files) | `v4.32.0` | `81a5d257…` |
| Prove2Me env #2 | Lean 4.30.0 | `c5ea003…` (behind) |
| Prove2Me default env | Lean 4.33.1 | `0df444a…` (ahead) |

In full, both repos: `leanprover/lean4:v4.32.0` and Mathlib
`81a5d257c8e410db227a6665ed08f64fea08e997`. The two Prove2Me rows are as the platform listed
its environments on 2026-09-05 and are not re-checked here.

**Decision D1 (2026-09-05) closed the cross-repo half of this.** Both repos sit on Mathlib
`81a5d257` / Lean `v4.32.0` — formal-mathfin's pin, which is what let `MathFin` and
`BrownianMotion` become `lake require`s without building a second Mathlib. An earlier version
of this section described a silent cross-repo pin mismatch; D1 resolved it, and the pins are
verifiable from `lean-toolchain` and `lake-manifest.json` in each repo.

**What remains is the platform half: this pin matches no Prove2Me environment.** The mismatch
is now *shared* by both repos, so it is a single decision rather than a cross-repo hazard, but
it still blocks uploads that are meant to interoperate:

1. **There is no cross-environment import.** A theorem in one environment is invisible from
   another, so LevyStochCalc nodes could not be imported by Dissertation nodes unless both
   target the same environment.
2. **Every call must pass `env=` explicitly** — `submit-problem`, `submit-definition`,
   `GET /theorems`. Whichever environment is chosen, the statement has to be re-verified
   against it: a proof that compiles at `81a5d257` is not thereby a proof at `c5ea003`.

`Plan.md`'s rules of engagement say "**No pin bump** (cross-repo mismatch risk)". D1 was that
bump, taken deliberately with both repos moving together. A *further* bump to reach `0df444a`
would be the same kind of project again and is a judgement call for Christian, not a change to
make unilaterally.

**Gate before any Prove2Me work here:** `lake build` green, `bash tools/lint.sh` at baseline,
`bash tools/verify_import_contract.sh` passing, and the Dissertation still building — all four
at the pin actually committed, and the upload re-verified at the environment it targets.

---

## 3. What to upload, in what order

Not the library. The payload is **one Open theorem — cited axiom #16 — plus the definitions
its statement needs**. That is a small `submit-definition` / `submit-problem` batch, not the
full-project transplant playbook, and a fundamentally smaller job than the Dissertation's
Stage 3–6. The earlier plan for a ten-node decomposition DAG is moot: nine of those nodes are
now theorems and four were retired as unsound statements (§1).

1. **The definitional closure of #16's statement**, as `submit-definition` nodes. Read off
   `Ito/JumpFormula.lean:189`: the driver structures `Brownian.Multidim.MultidimBrownianMotion`
   and `Poisson.PoissonRandomMeasure`; the filtration predicates `IsBrownianFiltration` and
   `IsPoissonFiltration`; `Ito.Setting.JumpDiffusionCoeffs` and `JumpDiffusion`; the two
   `stochasticIntegral`s, hence their constructions (`stochasticIntegralBrownian`, the
   compensated `process` and its càdlàg modification) and the progressive-measurability
   predicates they take; and the `Ito.JumpFormula` integrands (`diffusionIntegrand`,
   `driftIntegrand`, `compensatorDriftIntegrand`). This closure is the expensive part: the
   integrals are built, not assumed, so their definitions drag in the `L²` constructions
   behind them. Nothing here is an Open node; it is what the Open node is *about*.
2. **#16 itself as an Open theorem** — `itoLevyFormula_jumpResidual_canonical_axiom`, with
   the `source` field "Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009,
   Theorem 4.4.10 and Theorem 4.4.7 step (II)". Its statement was audited on 2026-09-06 (two
   missing hypotheses added, `tools/cited_axioms.md` entry #16) and restated over a common
   filtration under X2-3; upload the statement as it stands in the file, not an earlier form.
3. **Nothing else.** The retired statements #9, #10, #13a, #15 are not candidates until they
   are restated (`Plan.md` A6, A7, B5) — uploading a statement that was deleted as refutable
   would publish the defect permanently. The theorems (#1–#6, #11–#14, #13b, #17, #18) are
   not debt; publishing them is a `Proved`-badge exercise with no honesty gain (§1), and the
   dissertation's coverage question is untouched by it.

What the platform would then show is one Open node whose only importer on the dissertation
side is `Dissertation.Continuous.itoLevyFormula` — the axiom boundary that
`tools/cited_axioms.md` records, made machine-visible.

**Sequencing rule:** a `submit-problem` payload is immutable. Write the statement against
`tools/cited_axioms.md`'s existing citation, and get an independent read-back — a blind
natural-language rendering of what the Lean statement says, by a reader who has not seen the
citation — before submitting. The four retired entries are the reason: a wrong hypothesis,
published permanently, is worse than the axiom.

---

## 4. What does not change

Everything in `GOAL.md` and `CLAUDE.md` stands. Specifically:

- The four hard invariants stay green after every change: `lake build`,
  `tools/lint.sh`, `tools/verify_import_contract.sh`, and the Dissertation's `lake build`.
- The import contract (12 modules + 19 symbols) is untouched by any of this. Prove2Me
  nodes are a *parallel publication*, not a refactor; no pinned symbol moves.
- `GOAL.md` §1.B non-vacuity is **not** satisfied by a Prove2Me badge. A `Proved` verdict
  on a statement with contradictory hypotheses is still vacuous — the platform type-checks,
  it does not audit meaning. `examples/Nonvacuity.lean` remains the artifact that does that
  job, and remains unwritten.
- Ponytail discipline: this file and the CLAUDE.md section are the whole documentation
  footprint of this idea. No dated copies, no parallel tracker.

## 5. Provenance of the claims above

Every repository-state claim in this file is read from the tree, not from the platform and
not from a build: the pins from `lean-toolchain` and `lake-manifest.json`; the axiom count
from the one `axiom` declaration under `LevyStochCalc/`; the `sorry` state from
`tools/sorry_baseline.txt` and the grep `GOAL.md` §1.A prescribes; the dependency claims from
`audit_output.txt`, the `#print axioms` report `tools/lint.sh` writes (untracked), and from the
Dissertation's own audit. None of the gates in §2 has been run against a Prove2Me environment.
