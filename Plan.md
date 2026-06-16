# LevyStochCalc → Mathlib-Grade Library — Master Plan

**Goal.** Turn this repo from an axiom-spined dissertation substrate into a
proper, mathlib-shaped stochastic-calculus library: close every custom axiom
and `sorry` with real proofs, refactor the layout to mathlib's conventions, and
upstream the general results — solo, incrementally, without ever breaking the
dissertation that depends on it.

**Status as of 2026-06-15 (audit baseline).** 14 custom `axiom`s, 1 real `sorry`
(+4 forwarders), 31 source files / ~18.4k lines. Builds clean; lint green.

**Verified fact that frames everything.** All 14 citations are *upstream of*
current mathlib. Grepped against mathlib `master` (2026-06-15) and our pinned
rev (`0e20855`, 2026-05-01): mathlib has **no** stochastic/Itô integral, **no**
BSDE, **no** Poisson random measure, **no** predictable representation, **no**
càdlàg regularization, and only the Kolmogorov *condition* (not the continuity
conclusion). Mathlib's new `Probability/BrownianMotion/` has BM *predicates* +
projective family but **not** the construction (its own docstring: Kolmogorov
extension theorem "not in Mathlib yet"). So nothing here is redundant — we are
ahead of mathlib on the Itô/BSDE layer and co-temporal on the BM/KC layer.

---

## Rules of engagement (apply to every task below)

- **Invariant after every commit:** `lake build` ✅ · `bash tools/lint.sh` at
  baseline ✅ · `bash tools/verify_import_contract.sh` ✅ · dissertation
  (`D:/Dissertation`) `lake build` ✅. If any go red, the step isn't done.
- **Never break the import contract** (`tools/import_contract.md`): 12 pinned
  modules + 21 pinned symbols under `LevyStochCalc.*`. Rename/move only behind a
  forwarding stub at the old path. Do **not** rename public symbols or the
  top-level namespace in-tree — that is PR-prep, done per-result at extraction
  time (Phase 4), not during in-tree refactor.
- **Ponytail (look for a reason *not* to write code):** git history is the
  archive — never keep dated copies in-tree. One mathematical idea per file.
  Don't split/refactor a file speculatively; do it when extraction or size
  forces it. The best diff is the one that deletes more than it adds.
- **Mathlib hard gates** (for anything destined upstream): only the 3 standard
  axioms, zero `sorry`, ≤100 cols, no `import Mathlib` umbrella, copyright header
  (already correct), math-only docstrings (no `Tier 1`/`red-team`/`D:/...`),
  `ProbabilityTheory` namespace, file under `Mathlib/Probability/...`, registered
  in `Mathlib.lean`. **Disclose AI use in every PR + add `LLM-generated` label.**

---

## Phase 0 — De-clutter & build the safety net (low risk, do first)

- [x] **0.1** Delete `redteam_findings/2026-05-20-archive/` (13 files). Git keeps
      it; an in-tree dated duplicate is exactly the junk to remove. *(done
      2026-06-15 on `claude/refactor-phase0-declutter`; STATUS.md pointer updated.)*
- [x] **0.2** Collapse the 12 live `redteam_findings/NN_*.md` persona files into a
      single `redteam_findings/SUMMARY.md` (or delete if superseded). Keep
      `STATUS.md` and `tools/*.md` as workflow docs but treat them as *this repo's*
      scaffolding — they never travel into a mathlib PR. *(done 2026-06-15: the 12
      personas were superseded by the existing deduplicated meta-summary, which was
      renamed `SUMMARY.md`; the 12 raw reports + audit scaffolding deleted, git-archived.)*
- [x] **0.3** Strip in-source narrative comments project-wide: `P1 F2
      INVESTIGATION`, `red-team Nth audit`, milestone tags, `D:/...` paths, dated
      change-logs. Move any still-useful rationale into the decl docstring as math.
      *(done 2026-06-16: all 18 source files cleaned; a project-wide scan for
      red-team/audit/persona tags, `D:/` paths, and dated change-logs is empty.
      Removed ~8 deleted-code tombstone blocks (git is the archive); rewrote the
      JumpFormula/MartingaleRepresentation/Definition status sections and the
      citation-correction narrative to math-only. Four-way invariant green.)*
- [x] **0.4** Confirm the four-way green invariant is reproducible from a clean
      clone *before* refactoring. This is the regression guard for all of Phase 1.
      *(done 2026-06-16: fresh `git clone` of the branch from origin →
      `lake exe cache get` + `lake build` + `tools/lint.sh` + `verify_import_contract.sh`
      all green; all build configs and the 21 library `.lean` files are git-tracked
      and the working tree is clean. The `D:/Dissertation` leg can't build in the web
      container; the contract check is its proxy, per the session brief.)*

## Phase 1 — Structural refactor (in-tree, contract-safe)

- [x] **1.1** Consolidate the 10 `Ito/Picard*.lean` files (4739 lines, one
      theorem) → 2–3 files organized by mathematics, not proof-iteration. None are
      pinned in the contract, so this is free. **Highest-value cleanup.** *(done
      2026-06-15: → `Picard.lean` (operator + estimates + self-map + contraction),
      `PicardSpace.lean` (complete metric space + baseline sorry), `PicardFixedPoint.lean`
      (Banach existence/uniqueness). Bodies/namespaces/sorry/axiom preserved verbatim;
      root imports 10→3; four-way invariant green.)*
- [ ] **1.2** Split the 3 oversized files along mathematical seams, each with a
      forwarding aggregator at the old path so pinned imports still resolve:
      - `Brownian/Ito.lean` (3999) → simple-integrand integral / isometry
        extension / martingale & quadratic variation.
      - `Poisson/Compensated.lean` (2102) → integral construction / isometry /
        martingale property.
      - `Brownian/SimplePredictableRefine.lean` (2290) → density / refinement.
      Target: no file > ~600 lines (mathlib `Probability/` p90).
- [ ] **1.3** Add `section … variable … end` blocks to every multi-concept file
      (currently 0 in the big files). Pure hygiene, breaks nothing.
- [ ] **1.4** Wrap the 180 lines > 100 cols. Replace the `import Mathlib` umbrella
      in `Basic.lean` with precise imports (the file already flags this as
      mandatory PR-prep); push the `ProbabilityTheory.*` imports down into the
      consumer files as needed.
- [ ] **1.5** Re-title module docstrings to describe the mathematics only; keep
      the existing (good) per-decl docstring density.

## Phase 2 — Align to mathlib's existing API (shrink the surface)

- [ ] **2.1** Re-express the Brownian layer against mathlib: map our
      `BrownianMotion` structure onto `ProbabilityTheory.IsBrownianReal` /
      `IsPreBrownianReal`, and reuse `HasIndepIncrements`, `IsGaussianProcess`,
      `BrownianReal.projectiveFamily`. This shrinks axioms #1/#3/#4 down to the
      genuinely-missing pieces (Kolmogorov extension + KC continuity).
- [ ] **2.2** Track mathlib (Degenne et al. BM project). When the Kolmogorov
      extension theorem + KC continuity conclusion land, bump the mathlib pin and
      collapse #1/#3 to imports.

## Phase 3 — Close the axioms, object by object (the real math)

Bottom-up by dependency. Each item: prove the statement as a real `theorem`,
delete the `axiom`, update `_audit.lean`, drop it from `cited_axioms.md`. The
single `sorry` (`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`)
disappears with the #9 chain.

**Tier A — mathlib scaffolds it, finish the gap:**
- [ ] **#3** `kolmogorovChentsov_modification` — KC continuity conclusion
      (Karatzas–Shreve 2.2.8). Closest to landing upstream.
- [ ] **#1** `BrownianMotion.exists` — construction via Kolmogorov extension.
- [ ] **#4** `brownian_martingale_rightCont` — BM martingale wrt right-cont
      filtration (KS 2.7.7/2.7.9), once #1 exists.

**Tier B — partial machinery, theorem is greenfield:**
- [ ] **#2** `PoissonRandomMeasure.exists_of_sigmaFinite` — via Ionescu–Tulcea
      (Applebaum 2.3.1).
- [ ] **#13b** `condExp_to_PRP_martingale_form_axiom` — Doob L² càdlàg
      regularization (KS I.3.13) + Blumenthal 0-1.
- [ ] **#13a** `jacodYor_PRP_martingale_axiom` — predictable representation
      property (Jacod 1975 / Jacod–Shiryaev III.4.34).

**Tier C — pure greenfield (deepest; each ~a mathlib project):**
- [ ] **#5** `itoIsometry_brownian_unified_existence` — L² Itô integral
      construction + isometry (KS 3.2.6). *Foundational for the rest of C.*
- [ ] **#6** `itoIsometry_compensated_unified_existence` — compensated-Poisson L²
      integral + isometry (Applebaum 4.2.3/4.2.4).
- [ ] **#17 / #18** per-difference L² isometries — fall out of #5 / #6.
- [ ] **#15** `itoFormula_continuousSemimartingale_axiom` — Itô formula
      (KS 3.3.6).
- [ ] **#16** `itoLevyFormula_jumpResidual_canonical_axiom` — Itô–Lévy jump
      residual (Applebaum 4.4.10 + 4.4.7).
- [ ] **#9** `continuousBSDEJ_exists_unique` — BSDEJ existence/uniqueness via the
      Picard chain (Tang–Li 1994 / AGPP 2025). **Replaces the lone `sorry`.**
- [ ] **#10** `bsdej_path_regularity` — BSDEJ path regularity (Bouchard–Elie
      2008).

## Phase 4 — Upstream to mathlib (per result, solo-friendly)

For each *closed, general* result, in this order of mathlib-readiness:
- [ ] **4.1** Smallest clean leaves first — the `Basic.lean` `eLpNorm`
      reverse-triangle / L²-continuity helpers. Ideal first PR.
- [ ] **4.2** BM-layer pieces — coordinate on Zulip with the active BM project
      *before* writing, to avoid duplicate effort and align names.
- [ ] **4.3** Then PointProcess (Poisson random measure) → StochasticIntegral →
      SDE → BSDE, as each layer's axioms close.
- [ ] **Per-PR checklist:** re-home to `ProbabilityTheory` + `Mathlib/Probability/
      <Area>/...`; precise imports; ≤100 cols; jargon-free docstrings; register in
      `Mathlib.lean`; `#print axioms` shows only the 3 standard; **AI disclosure +
      `LLM-generated` label**; leave a forwarding stub here so the dissertation
      keeps building against the old `LevyStochCalc.*` path.

## Phase 5 — Definition of done (steady state)

The full, authoritative definition of done — including the non-vacuity and
faithfulness criteria a "zero sorry" pass misses — lives in [`GOAL.md`](GOAL.md)
§1. This phase is complete exactly when every `GOAL.md` §1 box is
checkable-true. In brief: zero `sorry`/custom-axiom (`#print axioms` →
`propext`/`Classical.choice`/`Quot.sound` only), no vacuity (`GOAL.md` §2),
mathlib-grade form, dissertation builds via stubs, CI green, general results
merged or PR-open.

When this phase is reached but `GOAL.md` is not yet fully met, regenerate this
`Plan.md` per the loop contract at the top of `GOAL.md`.

---

## Destination map (where each area goes in mathlib's tree)

| This repo | Mathlib destination | mathlib status |
|---|---|---|
| `Brownian/{Construction,Continuity,Martingale,Multidim}` | `Mathlib/Probability/BrownianMotion/` | dir exists; align to `IsBrownianReal` |
| `Brownian/{Ito,MultidimIto,SimplePredictableRefine}` | `Mathlib/Probability/StochasticIntegral/` | greenfield |
| `Poisson/*` | `Mathlib/Probability/PointProcess/` | greenfield |
| `Ito/{Setting,JumpFormula,Picard*}` | `Mathlib/Probability/SDE/` (+ Itô formula in StochasticIntegral) | greenfield |
| `BSDEJ/*` | `Mathlib/Probability/BSDE/` | greenfield |

## Sequencing summary

Phase 0 → 1 are safe in-tree refactors (do now, in order). Phase 2 shrinks the
BM surface. Phase 3 is the multi-year math, ordered #5 first (the integral
unblocks all of Tier C). Phase 4 upstreams opportunistically as Phase 3 closes
each object. Never advance a phase with the four-way invariant red.
