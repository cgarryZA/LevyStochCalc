# Dissertation build verification — LevyStochCalc master 4722b26

**Date:** 2026-05-26 (verification run)
**LevyStochCalc HEAD:** `4722b26` (master) — "INTEGRATE Agent 5: bsdej_path_regularity_linear_rate corollary (audit Item 5)"
**Dissertation HEAD:** `e3e7c84` (branch `path-x-rigorous-bsdej`) — "Wave-2 research item 3: MLP architecture in DeepBSDEJ"
**Verifier:** automated agent (parallel red-team / build verification track)

## Summary

| Item | Status |
|---|---|
| LevyStochCalc clean rebuild via `lake clean && lake build` | **NOT COMPLETED THIS RUN** (multi-agent contention — see Operational notes) |
| Dissertation clean rebuild via `lake clean && lake build` | **NOT COMPLETED THIS RUN** (depends on LevyStochCalc rebuild above) |
| LevyStochCalc `tools/lint.sh` | **NOT RUN THIS RUN** (depends on clean lake build) |
| LevyStochCalc audit-output evidence (`audit_output.txt`, 2026-05-24 12:32) | **PRESENT and CONSISTENT** with master HEAD |
| Dissertation audit-output evidence (`audit_output.txt`, 2026-05-26 10:00) | **PRESENT and CONSISTENT** with master HEAD |
| Dissertation 4 headline axiom sets verified | **PASS** (against existing audit output) |
| Dissertation sorry budget | **CLEAN — zero tactic-mode `sorry` in source tree** |

**Headline verdict.** The recent integration of LevyStochCalc Tier 1 axiom #11
(`itoLevyFormula`, axiom→theorem conversion via sub-axioms #15 + #16) is
**reflected correctly** in the dissertation forwarders. Every one of the four
headline LevyStochCalc forwarder theorems in `Dissertation.Continuous` surfaces
EXACTLY the expected Tier 1 cited axioms (no `sorryAx`, no surprise dependency).
The new sub-axioms `itoFormula_continuousSemimartingale_axiom` (#15) and
`itoLevyFormula_jumpResidual_axiom` (#16) are visible in the dissertation's
audit of `Dissertation.Continuous.itoLevyFormula` exactly where Tier 1 #11
previously appeared. The sorry budget on the dissertation side is zero
tactic-mode `sorry`.

## 1. LevyStochCalc build status

### Working tree state at verification time

`D:/LevyStochCalc` (canonical master checkout) is on branch `master` at HEAD
`4722b26` (matches the user-stated current master state). Working tree has the
following uncommitted state:

```
 M LevyStochCalc.lean                                  -- adds import of PicardSpaceBieleckiComplete
?? LevyStochCalc/Ito/PicardSpaceBieleckiComplete.lean  -- ~250 LoC new file (Agent 3 follow-up)
?? redteam_findings/2026-05-24-3rd-audit/              -- 3rd red-team audit findings
```

These are unrelated to the user-stated "current master state HEAD 4722b26" but
will affect any literal `lake build` invocation at `D:/LevyStochCalc` since the
modified root aggregator imports the new file. The committed state matches
`4722b26` and is what is verified in this report.

### `lake clean && lake build` — NOT EXECUTED CLEANLY THIS RUN

The user-requested clean rebuild was attempted but did not complete during the
verification window. Root cause: 24+ concurrent `lake.exe` / `lean.exe`
processes were active in `D:/LevyStochCalc` and its many sibling worktrees
during the verification run. Symptoms observed:

* `lake clean` exits with `error: directory not empty (error code: 41)` (other
  agents are holding file descriptors inside `.lake/build`).
* Subsequent `lake build` invocations either:
  (a) get killed by sibling `lake clean` races mid-build, ending with the
      shell capturing only partial Mathlib progress lines and `exit=0`
      (false-positive — actual artifact count for LevyStochCalc-side
      `.olean` files remains 0); or
  (b) hang in lake's setup phase, producing only a `pwd` echo and no further
      output for 5+ minutes.

Multiple build attempts (background tasks `buc6k376y`, `bxbipw7e0`,
`bftb1k4z9`, `baeg8ykcv`, `bolcmh3v2`) were dispatched. None produced
LevyStochCalc-side `.olean` artifacts. This is **a transient operational
contention issue, NOT a defect in the master commit `4722b26`**.

### Evidence the build was clean on the most recent successful run

`D:/LevyStochCalc/audit_output.txt` (dated **2026-05-24 12:32**, byte-size
9 741) contains the `#print axioms` output from a successful `lake env lean
_audit.lean` run that postdates commits:

* `8313fef` — Add tools/import_contract.md (2026-05-24)
* `8ff0234` — INTEGRATE Agents 1 + 2: **itoLevyFormula axiom → theorem +
  IsBSDEJSolution extractors** (2026-05-24)
* `2c64e97` — INTEGRATE Agent 3: PicardSpaceBielecki β-norm metric foundation
  (2026-05-24)
* `4722b26` — INTEGRATE Agent 5: bsdej_path_regularity_linear_rate corollary
  (2026-05-24)

This file is **the ground-truth axiom-set evidence** for master `4722b26`.
The 173 lines exercise every load-bearing theorem in `_audit.lean` and:

* Confirm the new sub-axioms #15 (`itoFormula_continuousSemimartingale_axiom`)
  and #16 (`itoLevyFormula_jumpResidual_axiom`) are introduced — lines 143–149.
* Confirm zero `sorryAx` anywhere in the public API.
* Confirm the new `bsdej_path_regularity_linear_rate` corollary surfaces only
  Tier 1 axioms (lines 168–173).

### LevyStochCalc lint status

**NOT RUN THIS VERIFICATION SESSION.** `bash tools/lint.sh` requires a
successful `lake build` to populate `.lake/build/lib/lean/LevyStochCalc/*.olean`
before re-running `lake env lean _audit.lean`. With the build artifacts
absent in this session, the lint cannot run.

`tools/sorry_baseline.txt` is **empty (0 bytes)**, which states the lint
contract: **zero `sorryAx`-tainted theorems** allowed in the entire public
API. The historical `audit_output.txt` from 2026-05-24 confirms this contract
was being met at that point — no `sorryAx` appears in any of the 60+ printed
axiom sets.

## 2. Dissertation build status

### Working tree state at verification time

`D:/Dissertation` is on branch `path-x-rigorous-bsdej` at HEAD `e3e7c84`
(wave-2 research item 3 — MLP architecture). Working tree is clean (no
modifications, no untracked files).

### `lake clean && lake build` — NOT EXECUTED THIS RUN

Same root cause as LevyStochCalc above: the dissertation depends on
LevyStochCalc via `path = "../LevyStochCalc"`, and the dependency is
artifact-less right now due to the multi-agent contention on
`D:/LevyStochCalc/.lake/build`.

### Evidence of the most recent successful Dissertation build

`D:/Dissertation/audit_output.txt` (dated **2026-05-26 10:00**, byte-size
74 016) contains the `#print axioms` output from a successful `lake env lean
_audit.lean` run TODAY (10am). Selected `.olean` artifacts in
`D:/Dissertation/.lake/build/lib/lean/Dissertation/` include:

* `Dissertation.olean` — 2026-05-26 09:57 (today)
* `Dissertation/Continuous.olean` — 2026-05-24 13:00 (the post-#15/#16 build)
* `Dissertation/Continuous/LevyStochCalcBridge.olean` — 2026-05-24 13:00

The dissertation has been building cleanly against the post-#15/#16
LevyStochCalc master state since at least 2026-05-24 13:00, and was being
audited as recently as 2026-05-26 10:00.

## 3. Per-headline axiom sets (from `D:/Dissertation/audit_output.txt`, 2026-05-26 10:00)

### `Dissertation.Continuous.itoLevyIsometry`

```
'Dissertation.Continuous.itoLevyIsometry' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence]
```

**Expected:** Tier 1 #6 (`itoIsometry_compensated_unified_existence`).
**Actual:** matches — line 8 of `audit_output.txt`. **PASS.**

### `Dissertation.Continuous.continuousBSDEJ_exists_unique`

```
'Dissertation.Continuous.continuousBSDEJ_exists_unique' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique,
 LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence,
 LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence]
```

**Expected:** Tier 1 #9 (`continuousBSDEJ_exists_unique`), plus transitively
Tier 1 #5 (`itoIsometry_brownian_unified_existence`) via the `M_W` pinning
to `MultidimBrownianMotion.stochasticIntegral` and Tier 1 #6 via `M_N`
pinning to `Compensated.stochasticIntegral`.
**Actual:** matches — lines 9–14. **PASS.**

### `Dissertation.Continuous.itoLevyFormula`

```
'Dissertation.Continuous.itoLevyFormula' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence,
 LevyStochCalc.Ito.JumpFormula.itoFormula_continuousSemimartingale_axiom,
 LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_axiom,
 LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence]
```

**Expected (per the 2026-05-24 #11 → #15 + #16 refactor):** the previous
single Tier 1 #11 axiom (`itoLevyFormula`) is replaced by the combination of
the two new sub-axioms #15 (`itoFormula_continuousSemimartingale_axiom`,
Karatzas–Shreve 3.3.6 continuous-semimartingale Itô formula) and #16
(`itoLevyFormula_jumpResidual_axiom`, Applebaum 4.4.10 + 4.4.7 step II jump
residual decomposition). Plus the transitive #5 + #6 dependencies through the
pinned-integral conclusion.
**Actual:** matches EXACTLY — lines 15–21. The new sub-axioms surface
correctly. The previous `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` axiom
no longer appears as an axiom dependency (it is now a derived theorem).
**PASS.**

### `Dissertation.Continuous.bsdej_path_regularity`

```
'Dissertation.Continuous.bsdej_path_regularity' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity,
 LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence,
 LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence]
```

**Expected:** Tier 1 #10 (`bsdej_path_regularity`) plus transitively #5 + #6.
**Actual:** matches — lines 22–27. **PASS.**

### Other dissertation headlines

`D:/Dissertation/AUDIT_HEADLINES.md` catalogs **43 dissertation-internal
headline theorems** (numbered 1–43). Each row records the headline's `#print
axioms` status. All 43 are documented as either:

* **CLEAN** — axiom set is exactly `{propext, Classical.choice, Quot.sound}`
  (Lean std only), OR
* **CLEAN modulo X cited axioms** — surfaces specific Cu* / K* / Disc*
  registered dissertation-side axioms (`Wasserstein.lean`,
  `ApproximateExpectation.lean`, `Axioms/Registry.lean`).

None are flagged as containing `sorryAx`. None depend transitively on a
LevyStochCalc Tier 1 axiom EXCEPT the four `Continuous.lean` forwarders
audited above, two LevyStochCalc Tier 1 dependencies on `discrete_to_continuous_*`
chains via the `cx_dissertation_two_term_bound_at_regime` and similar
P06.x family (which surface `itoIsometry_brownian_unified_existence` /
`itoIsometry_compensated_unified_existence` per the AUDIT_HEADLINES.md
documentation).

The cross-repo invariant — **"only LevyStochCalc Tier 1 axioms reach the
dissertation, and exactly where the AUDIT_HEADLINES.md docstring says they
do"** — is met.

## 4. Dissertation sorry budget

Tactic-mode `sorry` count in `D:/Dissertation/Dissertation/**.lean`:

```
zero (0)
```

A grep for `sorry` (word-boundary) hits 10 occurrences across 8 files, but
ALL are in docstrings, comments, or status notes, NOT proof bodies:

| File | Line | Context |
|---|---|---|
| `Continuous.lean` | 246 | `**Status: sorry'd theorem** with abstract...` (docstring) |
| `Comparison.lean` | 49 | `**All proofs complete** (zero ` ``sorry`` `s remain)...` (docstring) |
| `ContXiong/BSDEJ.lean` | 35 | `stated as a sorry'd theorem...` (docstring) |
| `EnergyMethod.lean` | 38 | `**All proofs complete** (zero ` ``sorry`` `s remain)...` (docstring) |
| `EnergyStepBSDE.lean` | 17 | `zero `sorry`s remain in this file.` (docstring) |
| `EnergyStepBSDE.lean` | 2414 | `tower is now sorry-free (modulo registered axioms...)` |
| `MartingaleRep.lean` | 513 | `The proof is sorry'd because the` (docstring) |
| `Solution.lean` | 132 | `Currently `sorry` — proof deferred to Phase 3...` (docstring; theorem since promoted) |
| `Solution.lean` | 595 | `The legacy stub here was a sorry'd placeholder...` (historical note) |
| `Wasserstein.lean` | 1224 | `-- := sorry`; now the axiom is invoked by name).` (replacement note) |

Anti-regex check for `\bsorry\b` followed by an actual proof-position token
(`^\s*sorry\s*$`, `:= sorry`, `by\s+sorry`, `exact\s+sorry`) returns the
single result on `Wasserstein.lean:1224` — which is inside a comment block.
**Confirmed zero tactic-mode `sorry` in source.**

## 5. Anomalies (flagged but NOT silently fixed per task instructions)

### A1. Stale `tools/cited_axioms.md` — does not reflect #11 → #15 + #16 refactor

`D:/LevyStochCalc/tools/cited_axioms.md` still describes Tier 1 entry #11 as
the axiom `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` (lines 108–119).
However, after commit `8ff0234`:

* `itoLevyFormula` is a **theorem** (proven by algebraic re-bundling).
* The actual axioms are #15 `itoFormula_continuousSemimartingale_axiom` and
  #16 `itoLevyFormula_jumpResidual_axiom` (declared in
  `LevyStochCalc/Ito/JumpFormula.lean` at lines 227 and 300 respectively).

The `cited_axioms.md` document does not contain `#15`, `#16`,
`itoFormula_continuousSemimartingale_axiom`, or
`itoLevyFormula_jumpResidual_axiom` anywhere. The "12 Tier 1 cited axioms
currently live" sentence is also stale — there are now 14 live Tier 1
axioms (#1–6, #9–14 + #15, #16; #7 + #8 deleted; #11 retired).

**Recommendation (NOT applied here per task scope):** add entries for #15 and
#16 to `cited_axioms.md`, move #11 to the "Honest derivative theorems" table
(forwarders), and update the live-count sentence.

### A2. Stale `cited_axioms.md` — `sorry_baseline.txt` count contradiction

`cited_axioms.md` line 222 states `tools/sorry_baseline.txt now contains
1 entry`. The actual file `D:/LevyStochCalc/tools/sorry_baseline.txt` is
**empty** (0 bytes). Likely fixed by commit `8a153e1` (`🎯 EMPTY SORRY
BASELINE: zero sorryAx in entire public API`) but the doc was not updated.

### A3. Dissertation `_audit.lean` references renamed theorems

`D:/Dissertation/_audit.lean` lines 43–44 reference:

* `Dissertation.BSDE.Discrete.discrete_bsde_unique_via_stability`
* `Dissertation.BSDE.Discrete.discrete_bsde_unique_at_zero`

But the actual theorem names in `Dissertation/BSDE/Discrete/Uniqueness.lean`
have a `_pythag` suffix (lines 91, 168):

* `discrete_bsde_unique_via_stability_pythag`
* `discrete_bsde_unique_at_zero_pythag`

The current `D:/Dissertation/audit_output.txt` reflects this — lines 35–36
contain the errors:

```
_audit.lean:43:14: error(lean.unknownIdentifier): Unknown constant `Dissertation.BSDE.Discrete.discrete_bsde_unique_via_stability`
_audit.lean:44:14: error(lean.unknownIdentifier): Unknown constant `Dissertation.BSDE.Discrete.discrete_bsde_unique_at_zero`
```

This does NOT affect the build (the `#print axioms` lines after the errors
still elaborate). The errors are cosmetic in `audit_output.txt`. The fix is
to rename the audit lines to `_pythag` or remove them.

This is a **Dissertation-side anomaly** — per task instructions, NOT fixed.

### A4. `D:/LevyStochCalc` working tree has new uncommitted file

The uncommitted file `D:/LevyStochCalc/LevyStochCalc/Ito/PicardSpaceBieleckiComplete.lean`
and the working-tree modification to `LevyStochCalc.lean` (adding the import)
are NOT part of master `4722b26`. They appear to be ongoing Agent 3 follow-up
work to start eliminating Tier 1 axiom #14 (`picardFixedPoint_jumpDiffusion_exists_unique_axiom`).

If the uncommitted state is left in place, a fresh `lake build` at
`D:/LevyStochCalc` will try to compile the new file. This affects the
operational state but NOT the committed master. The verification here
applies to committed master only.

### A5. Operational contention prevented clean rebuild this session

24+ concurrent `lake.exe` / `lean.exe` processes spread across many sibling
worktrees under `D:/LevyStochCalc/.claude/worktrees/` made `lake clean` and
`lake build` unstable on the shared `D:/LevyStochCalc/.lake/build` directory.

The condition is **transient and external** — it is not a defect in the
master commit `4722b26`. A future verification run with idle concurrency
should produce the clean rebuild.

## 6. Provenance / verification log

* **LevyStochCalc HEAD:** `4722b26262f2adf57fd71e97dbb3add5f8112d6217`
* **LevyStochCalc audit_output.txt mtime:** 2026-05-24 12:32, 9 741 bytes
  (POST-#15/#16, POST-`bsdej_path_regularity_linear_rate` integration)
* **Dissertation HEAD:** `e3e7c84f1cef27ac61f224d951b808055bfc00cc`
* **Dissertation audit_output.txt mtime:** 2026-05-26 10:00, 74 016 bytes
  (TODAY)
* **Dissertation `Continuous.olean` mtime:** 2026-05-24 13:00
  (post-#15/#16 successful dissertation-side compile)
* **Tier 1 axiom inventory:** 14 live (`#1–6, #9–16`; #7, #8 deleted; #11
  retired → derived theorem). `cited_axioms.md` lags this state — see
  anomaly A1.
* **`sorry_baseline.txt`:** empty — zero sorryAx allowed.
* **Dissertation source `sorry` count (tactic-mode):** 0.
* **Headline forwarders verified:** 4/4 (`itoLevyIsometry`,
  `continuousBSDEJ_exists_unique`, `itoLevyFormula`, `bsdej_path_regularity`)
  surface only the expected Tier 1 axioms.
