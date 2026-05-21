# Shared context OVERRIDE — LevyStochCalc target

You are one of 12 reviewers performing a parallel adversarial audit of a **Lean 4 stochastic calculus library**. **Read this file in full before doing anything else. This file SUPERSEDES `D:\LeanRedTeam\shared_context.md`** because the target is not the dissertation but its sister project.

## The target

- **Repository**: `D:\LevyStochCalc\`
- **What it is**: A Lean 4 + Mathlib formalisation of L² Itô and Itô–Lévy stochastic calculus + BSDEJ existence/path regularity. Foundational library — no finance, no MFG, no deep learning of its own.
- **Sister repo**: `D:\Dissertation\` — a Durham MSc dissertation that *forwards* into LevyStochCalc for 4 headline theorems (`itoLevyIsometry`, `continuousBSDEJ_exists_unique`, `itoLevyFormula`, `bsdej_path_regularity`). The dissertation is **NOT your audit target**. Anything you'd want to say about the dissertation, the Cont–Xiong model, deep BSDEJ, MFG, viva defence, financial-mathematics realism, etc., is **out of scope for this audit**.

## What's already been established (before you arrive)

- The library exposes **11 Tier 1 cited axioms** documented in `D:\LevyStochCalc\tools\cited_axioms.md`. Each is a real published theorem (Karatzas–Shreve, Applebaum 2009, Tang–Li 1994, Bouchard–Elie–Touzi 2009, etc.) declared as Lean `axiom` with a paper citation in its docstring.
- Around 16 "honest derivative theorems" are derived from those axioms (e.g., `Compensated.itoLevyIsometry` extracts one conjunct of the unified-existence cited axiom).
- A recursive trivial-witness audit was run very recently (commit `db582f9` on `master`, 2026-05-11). That audit caught two real defects:
  1. `Ito.JumpFormula.itoLevyFormula` had been a `theorem` whose proof body was the literal trivial-witness pattern `refine ⟨0, 0, 0, fun ω => u T (X T ω) - u 0 (X 0 ω), ?_⟩; simp`. It was demoted to a documented `axiom` (Tier 1 entry #11, Applebaum 2009 Thm 4.4.7).
  2. `BSDEJ.Definition.IsBSDEJSolution`'s last conjunct used a per-`(t, ω)` existential `∃ BM_term jump_term : ℝ` of reals that was satisfiable by any L²-bounded `(Y, Z, U)` — making the Tang–Li uniqueness axiom mathematically false as written. The predicate was strengthened to an outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of process martingales with `M_N` pinned to `Compensated.stochasticIntegral N U` and `M_W` constrained by the multidim Brownian L²-Itô isometry against `Z`.
- Build state: `cd D:\LevyStochCalc && bash tools/lint.sh` → **8401 jobs, PASS at baseline** (no `sorryAx`). `D:\LevyStochCalc\tools\sorry_baseline.txt` is empty.
- The full per-theorem axiom audit is in `D:\LevyStochCalc\tools\full_audit_output.txt`.

## Term mapping (dissertation → LevyStochCalc)

When your persona file (and the original `shared_context.md`) mentions dissertation-specific concepts, translate as follows:

| Dissertation term | LevyStochCalc equivalent |
|---|---|
| "the 43 headline theorems" | **The 11 Tier 1 cited axioms + ~16 honest derivative theorems** (see `tools/cited_axioms.md` and `tools/full_audit.lean`) |
| `AUDIT_HEADLINES.md` | `tools/cited_axioms.md` |
| `_audit.lean` | `tools/full_audit.lean` (output in `tools/full_audit_output.txt`) |
| `Dissertation/Axioms/Registry.lean` | No registry attribute — axioms are plain `axiom` declarations with paper-citation docstrings; `tools/cited_axioms.md` is the canonical inventory |
| `cx_dissertation_full_closure_concrete` (master headline) | No master headline; the 4 "exposed" theorems are `itoLevyIsometry`, `continuousBSDEJ_exists_unique`, `itoLevyFormula`, `bsdej_path_regularity` |
| Cont–Xiong / ContXiong | **Out of scope** — that lives in dissertation only |
| MFG / Wasserstein / deep BSDE / DeepBSDE | **Out of scope** |
| `Dissertation/Continuous.lean` 4 forwarders | The targets of those forwarders ARE inside LevyStochCalc; verify the LevyStochCalc side directly |
| `mcp__lean2latex__list_known_headlines` (et al.) | The lean2latex MCP server is dissertation-side; you may not have it. Use `Grep`/`Read` for theorem signatures, and `mcp__lean-lsp__lean_verify` / `lean_hover_info` / `lean_declaration_file` for semantics |

## Project structure

```
D:\LevyStochCalc\
├── LevyStochCalc.lean              ← top-level imports (lists all modules)
├── lakefile.toml
├── lean-toolchain
├── LevyStochCalc/
│   ├── Basic.lean
│   ├── Notation.lean
│   ├── Brownian/
│   │   ├── BrownianMotion.lean     ← 1D Brownian (Tier 1 #1: BrownianMotion.exists)
│   │   ├── Construction.lean
│   │   ├── Continuity.lean         ← Tier 1 #3 kolmogorovChentsov_modification
│   │   ├── Martingale.lean         ← Tier 1 #4 brownian_martingale_rightCont
│   │   ├── Multidim.lean           ← MultidimBrownianMotion
│   │   ├── Ito.lean
│   │   └── SimplePredictableRefine.lean ← Tier 1 #5 itoIsometry_brownian_unified_existence
│   ├── Poisson/
│   │   ├── RandomMeasure.lean      ← Tier 1 #2 PoissonRandomMeasure.exists_of_sigmaFinite
│   │   ├── NaturalFiltration.lean
│   │   ├── Compensated.lean        ← Tier 1 #6 itoIsometry_compensated_unified_existence, #7 cauchySeq_simpleIntegralLp_compensated, #8 adaptedSimple_dense_L2_compensated
│   │   └── L2Isometry.lean         ← 1-line forwarder over Compensated.itoLevyIsometry
│   ├── Ito/
│   │   ├── Setting.lean            ← JumpDiffusionCoeffs, JumpDiffusion structures
│   │   └── JumpFormula.lean        ← Tier 1 #11 itoLevyFormula (newly demoted, 2026-05-11)
│   └── BSDEJ/
│       ├── Definition.lean         ← IsBSDEJSolution (predicate strengthened 2026-05-11)
│       ├── MartingaleRepresentation.lean  ← jacodYor_representation
│       ├── Existence.lean          ← Tier 1 #9 continuousBSDEJ_exists_unique
│       └── PathRegularity.lean     ← Tier 1 #10 bsdej_path_regularity
└── tools/
    ├── cited_axioms.md             ← canonical Tier 1 inventory + citations + Mathlib status + replacement plan
    ├── full_audit.lean             ← #print axioms on every theorem
    ├── full_audit_output.txt       ← latest audit output
    ├── lint.sh                     ← build + audit script
    └── sorry_baseline.txt          ← empty
```

## What you must do

1. **Read everything relevant to your persona.** Don't skim. Coverage matters; you'll be asked to report how many files you read.
2. **Use real tools — never fabricate.**
   - `Grep`, `Glob`, `Read` for code.
   - `mcp__lean-lsp__lean_verify`, `lean_hover_info`, `lean_declaration_file`, `lean_diagnostic_messages`, `lean_goal` for Lean semantics. **Load deferred tools via `ToolSearch` first** (e.g. `ToolSearch query="select:mcp__lean-lsp__lean_verify,mcp__lean-lsp__lean_hover_info,mcp__lean-lsp__lean_declaration_file" max_results=10`).
   - `mcp__lean-lsp__lean_leansearch` / `lean_loogle` / `lean_local_search` for Mathlib lemma lookup.
   - `WebSearch` / `WebFetch` for citations, paper claims, Mathlib lemma names.
   - The `mcp__lean2latex__*` MCP tools mentioned in some personas live on the dissertation side. If they're unavailable, fall back to Lean LSP + `Read`/`Grep`.
3. **Write findings to `D:\LevyStochCalc\redteam_findings\<your_persona_filename_stem>.md`** using the structure in `D:\LeanRedTeam\output_template.md`. Overwrite any existing file. **NOTE the output template says `D:\Dissertation\redteam_findings\` — that is the dissertation default. For THIS audit, write to `D:\LevyStochCalc\redteam_findings\`.**
4. **No hedging.** The user has been explicit across multiple sessions: cosmetic axiom-cleanliness is worse than a documented axiom. If you find a real problem, say so plainly. If you can't find anything in your area, say so honestly — don't invent issues to look thorough.
5. **No edits to LevyStochCalc source.** You are a read-only auditor. Recommendations go in the report; the orchestrator decides what to act on.

## Calibration for each persona

Some personas in `D:\LeanRedTeam\personas\` were calibrated for the dissertation. Apply the following recalibration:

- **Persona 1 (Lean formalisation)**: Sharpen — this IS a pure Lean formalisation. Comment on idiom, naming, Mathlib alignment, build hygiene, universe polymorphism, etc.
- **Persona 2 (Software engineering)**: Same as 1.
- **Persona 3 (Financial mathematician)**: LevyStochCalc has no finance content. Your scope is narrowed to: "would this library, as currently designed, support the kinds of Itô–Lévy stochastic calculus used in mathematical finance (e.g., Heston-with-jumps, Merton jump-diffusion, Lévy-driven BSDEs)? Are there design choices that would make downstream finance work harder than necessary?" Most headline-verdict cells will be OUT-OF-SCOPE-FOR-MY-LENS.
- **Persona 4 (Pure mathematician)**: Sharp focus on whether definitions match the standard literature (Karatzas–Shreve, Le Gall, Applebaum, Revuz–Yor). Check the predicate definitions carefully.
- **Persona 5 (Proof theorist / axiom hygiene)** — ★ **HIGHEST PRIORITY**. Apply your full axiom-dependency-closure + trivial-witness lens to the 11 Tier 1 axioms + the derived theorems. The recursive audit on 2026-05-11 already caught two patterns; verify nothing similar remains.
- **Persona 6 (Numerical analyst)**: LevyStochCalc has no numerical content. Most of your audit will be OUT-OF-SCOPE-FOR-MY-LENS. Focus on: "do any of the cited-axiom statements include hidden constants that downstream numerical work would need to know?"
- **Persona 7 (Stochastic analyst)** — ★ **HIGH PRIORITY for THIS target**. This IS your domain. Apply your full lens to the predicate definitions (`IsBSDEJSolution`, `PoissonRandomMeasure`, `MultidimBrownianMotion`, `JumpDiffusion`, etc.), the unified-existence axioms, and the four exposed forwarder targets. The recent strengthening of `IsBSDEJSolution` is exactly the kind of fix you should be checking.
- **Persona 8 (MFG specialist)**: Out of scope. Briefly note that LevyStochCalc could in principle support MFG-via-BSDEJ work in the future, but you have nothing concrete to audit here. Write a short report.
- **Persona 9 (Deep learning)**: Out of scope. Same as 8.
- **Persona 10 (Dissertation examiner)**: Reframe as "**library quality reviewer for a stand-alone Lean 4 stochastic calculus library**". Would this library be accepted into Mathlib? Is it well-documented? Could a new user pick it up? Are the cited axioms documented honestly enough that a Mathlib reviewer wouldn't be deceived?
- **Persona 11 (Citation verifier)** — ★ **HIGH PRIORITY**. Every Tier 1 axiom claims a specific paper + theorem number (e.g., "Applebaum 2009 Theorem 4.2.3"). Verify each citation actually says what the Lean axiom claims it says. Use `WebSearch`/`WebFetch` for paper abstracts, Google Books, secondary sources.
- **Persona 12 (Adversarial hole hunter)** — ★ **HIGHEST PRIORITY**. The 2026-05-11 recursive audit already found `itoLevyFormula` was a fake theorem. Your job is to find any patterns the recursive audit missed. The 11 axioms + ~16 derived theorems are your hunting ground.

## Key files to read first

| Path | Why |
|---|---|
| `tools/cited_axioms.md` | Canonical 11-axiom inventory + citations + Mathlib status + replacement plans |
| `tools/full_audit.lean` | Lists every public theorem we ran `#print axioms` on |
| `tools/full_audit_output.txt` | The audit's verbatim output — every theorem's axiom set |
| `tools/sorry_baseline.txt` | Empty (no sorries in baseline) |
| `LevyStochCalc.lean` | Top-level imports (full module list) |
| `LevyStochCalc/BSDEJ/Definition.lean` | Just-strengthened `IsBSDEJSolution` predicate |
| `LevyStochCalc/Ito/JumpFormula.lean` | Just-demoted `itoLevyFormula` axiom |
| `LevyStochCalc/Poisson/Compensated.lean` | Houses 3 of the 11 Tier 1 axioms + the `stochasticIntegral` definition |
| `LevyStochCalc/Brownian/SimplePredictableRefine.lean` | Houses `itoIsometry_brownian_unified_existence` |
| `LevyStochCalc/Poisson/L2Isometry.lean` | 1-line forwarder over `Compensated.itoLevyIsometry` |

## Severity ladder for findings

- **CRITICAL**: an axiom statement is mathematically false (asserts a non-existent object), a theorem has a soundness bug, a trivial-witness pattern hides where the library claims literature-strength, a citation is fabricated.
- **HIGH**: a definition diverges from standard literature in a way that would mislead a Mathlib reviewer; a paper citation misattributes a theorem number; a "unified existence" axiom's conjuncts are jointly inconsistent; a predicate is vacuous in a way that lets downstream axioms be vacuously true.
- **MEDIUM**: hypothesis is over-strong, naming is misleading, the cited paper supports the claim but a tighter / more recent reference exists, predicate could be tightened further.
- **LOW**: style, formatting, naming convention, dead code, redundant imports, missing docstring, unused universe variables.

Each finding must include: file path, line number (if applicable), severity, evidence (a quote, theorem signature, or web-source quote — verbatim), recommendation.

## Coordination

- Your findings file path: `D:\LevyStochCalc\redteam_findings\<persona_filename_stem>.md`.
- If your work needs to touch Lean source files (it shouldn't — you are read-only), STOP. Log the proposed change in your findings under "Recommendations" instead.
- Do NOT modify `D:\LeanRedTeam\`. That folder is the canonical setup pack.
- You have no awareness of other personas' findings. Do your own work.
- Per-headline verdicts: where the original template says "the 43 headline theorems," apply your verdicts to the 11 Tier 1 cited axioms + the ~16 honest derivative theorems listed in `tools/full_audit.lean`. Use the same EARNED / WEAK / TRIVIAL / UNVERIFIABLE / OUT-OF-SCOPE-FOR-MY-LENS verdict labels.

## Anti-patterns the user has been hunting (read carefully)

The user has been chasing trivial-witness patterns for weeks across both repos. The 2026-05-11 recursive audit caught:
1. **The `⟨0, 0, 0, change⟩; simp` pattern** in `itoLevyFormula` — three zero processes + entire change stuffed into the fourth.
2. **The `∃ BM_term jump_term : ℝ` per-`(t, ω)` existential** in `IsBSDEJSolution` — for any L²-bounded Y, the existential is satisfiable trivially, making the axiom built on top mathematically false.

Your job is to find any remaining instances of these or related patterns. Common variants:
- `Classical.choose` applied to an existential that is itself vacuous.
- A "unified existence" axiom whose conjuncts are independently strong but JOINTLY satisfiable by a single trivial witness (e.g., `F ≡ 0` satisfying martingale + isometry + càdlàg when `φ ≡ 0`).
- A predicate that LOOKS like the literature predicate but where one parameter is existentially quantified in a way that makes it trivially solvable.
- A forwarder whose conclusion has been silently weakened from the LevyStochCalc-side statement.

Be ruthless. Polite findings get ignored. Don't soften.
