# Red Team Audit: Deep Learning / Scientific ML Specialist

**Auditor lens**: ML PhD focused on neural-network-based PDE/SDE solvers (Deep BSDE, DGM, Hure-Pham-Warin), examining whether network approximation assumptions, loss functions, and training claims are honestly stated.
**Date**: 2026-05-20
**Coverage**: 4 framing files read in full (`shared_context.md`, `shared_context_override.md`, persona spec, output template) + `tools/cited_axioms.md` (Tier 1 inventory, first 80 lines) + full repo file inventory + targeted Grep over the entire Lean source tree. No DL-relevant Lean files exist to audit.

## Executive summary (<= 3 sentences)

`LevyStochCalc` contains zero deep-learning content: no Python, no neural-network primitives, no DeepBSDEJ algorithm, no loss-function definitions, no approximator hypotheses, no `DeepBSDEJApproximationHypotheses` or `CXDiscretisationRegularity`. The only matches for tokens like "deep" or "network" in the entire repo are docstring path references to the sibling LaTeX repo `D:/DeepBSDE/report/dissertation_study/` and the standard measure-theoretic concept `NaturalFiltration` (no relation to neural networks). The lens for which this persona was calibrated lives on the dissertation side (`D:\Dissertation\ContXiong\Wasserstein.lean` and `D:\DeepBSDE\src\**`), not here, so the report is honestly scope-empty other than one secondary observation about computability/extractability for future deep-BSDEJ work that would build on this library.

## Top findings (ranked by severity, highest first)

### Finding 1 -- LevyStochCalc has no deep-learning surface to audit
- **Severity**: N/A (scope note, not a defect)
- **Location**: Repo-wide.
- **Evidence**: Full Lean source tree (verified via `Get-ChildItem -Recurse D:\LevyStochCalc\LevyStochCalc`):
  - `Basic.lean`, `Notation.lean`
  - `Brownian/{Construction,Continuity,Ito,Martingale,Multidim,SimplePredictableRefine}.lean`
  - `BSDEJ/{Definition,Existence,MartingaleRepresentation,PathRegularity}.lean`
  - `Ito/{JumpFormula,Setting}.lean`
  - `Poisson/{Compensated,L2Isometry,Martingale,NaturalFiltration,RandomMeasure}.lean`

  No `Deep*.lean`, `Network*.lean`, `Approximation*.lean`, `Wasserstein*.lean` files exist. `Get-ChildItem -Recurse D:\LevyStochCalc -Filter *.py` returns empty. A case-insensitive Grep for `deep|neural|network|DeepBSDE|loss|gradient|tensorflow|pytorch|approximator|DGM|Han.?Jentzen|universal.?approximation|backprop|optimizer|ResNet|MLP|FNN|Hornik|Cybenko` finds matches only in (a) docstring file-path references to the sibling repo `D:/DeepBSDE/report/dissertation_study/ch02_mathematical_framework.tex` (used as a paper-citation pointer in module docstrings of `BSDEJ/Definition.lean`, `Ito/JumpFormula.lean`, `Ito/Setting.lean`, `Poisson/Compensated.lean`, `Brownian/Construction.lean`, `BSDEJ/MartingaleRepresentation.lean`, `BSDEJ/Existence.lean`, `Brownian/Ito.lean`), and (b) the unrelated measure-theory concept `NaturalFiltration` in `Poisson/NaturalFiltration.lean`.
- **Why this matters**: The persona brief itself states (item 9 of recalibration in `shared_context_override.md`): "Persona 9 (Deep learning): Out of scope. Same as 8." No findings to report. This block exists to confirm coverage was attempted, not as padding.
- **Recommendation**: None. DL audit belongs to the dissertation-side audit pass over `D:\Dissertation\ContXiong\Wasserstein.lean`, `D:\Dissertation\BSDE\Discrete\`, and `D:\DeepBSDE\src\**`.

### Finding 2 -- Forward-compatibility note: definitions are `noncomputable`, so a future deep-BSDEJ extraction layer cannot evaluate them directly
- **Severity**: LOW (and possibly OUT-OF-SCOPE-FOR-MY-LENS; recorded only because the orchestrator's note allowed flagging design choices that would matter for future deep-BSDE work using this library as foundation)
- **Location**: Repo-wide; `noncomputable` appears in 11 source files including `Brownian/Ito.lean:9`, `Poisson/Compensated.lean:20`, `Brownian/SimplePredictableRefine.lean:21`, `BSDEJ/PathRegularity.lean:2`, etc. `Classical.choose` / `Classical.choice` appears ~61 times across the same files.
- **Evidence**: Grep `Classical\.choice|Classical\.choose|noncomputable` returned 61 occurrences across 11 files. The 11 Tier 1 axioms in `tools/cited_axioms.md` are all existence statements (`∃ probability space ...`, `∃ process F ...`, `∃ adapted sequence ...`), each consumed downstream via `Classical.choose`.
- **Why this matters**: This is the correct and standard way to formalize measure-theoretic stochastic calculus in Lean 4 -- there is no constructive realisation of Brownian motion, Wiener measure, or Poisson random measures, so `noncomputable` and classical choice are unavoidable. A future Lean-formalised deep-BSDEJ solver building on this library would therefore not be able to `#eval` or extract a runnable solver from the library's definitions (the Lean theorems would prove properties of an abstract solver, while the actual numerical run would still live in Python under `D:\DeepBSDE\`). This is fine and matches the published literature (Han-Jentzen-E 2017, Hure-Pham-Warin 2020 are existence-and-error-bound theorems, not extraction artefacts). The library should not be criticised for this; future work should simply state plainly that the Lean-side `θ` exists by classical choice and is unrelated to the gradient-descent `θ` Python actually computes -- the same gap dissertation persona 9 is calibrated to find on the dissertation side.
- **Recommendation**: None for this library. If/when a `Dissertation/ContXiong/Wasserstein.lean` `DeepBSDEJApproximationHypotheses` interface is added on the dissertation side, ensure its docstring acknowledges that the population-loss `L(θ)` and the existential `θ*` are non-constructive and have no formal link to gradient descent on the empirical loss in `D:\DeepBSDE\src\`.

## Per-claim verdicts on the headline theorems

For LevyStochCalc, "headline theorems" = the 11 Tier 1 cited axioms + ~16 honest derivatives listed in `tools/full_audit.lean` (per `shared_context_override.md` term mapping). None of them are DL-related.

| Theorem | Verdict | One-line note |
|---|---|---|
| `Brownian.BrownianMotion.exists` | OUT-OF-SCOPE-FOR-MY-LENS | Pure measure-theoretic existence; no DL angle. |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | OUT-OF-SCOPE-FOR-MY-LENS | Pure measure-theoretic existence; no DL angle. |
| `Brownian.Continuity.kolmogorovChentsov_modification` | OUT-OF-SCOPE-FOR-MY-LENS | Path-regularity result; no DL angle. |
| `Brownian.Martingale.brownian_martingale_rightCont` | OUT-OF-SCOPE-FOR-MY-LENS | Filtration property; no DL angle. |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` | OUT-OF-SCOPE-FOR-MY-LENS | L^2-Ito construction; no DL angle. |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` | OUT-OF-SCOPE-FOR-MY-LENS | L^2-compensated construction; no DL angle. |
| `Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` | OUT-OF-SCOPE-FOR-MY-LENS | Lifting lemma; no DL angle. |
| `Poisson.Compensated.adaptedSimple_dense_L2_compensated` | OUT-OF-SCOPE-FOR-MY-LENS | Density lemma; no DL angle. |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` | OUT-OF-SCOPE-FOR-MY-LENS | Continuous-time BSDEJ well-posedness; no DL approximation claim; deep-BSDE persona checks live on dissertation side. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` | OUT-OF-SCOPE-FOR-MY-LENS | Path-regularity of BSDEJ solution; no DL angle. |
| `Ito.JumpFormula.itoLevyFormula` | OUT-OF-SCOPE-FOR-MY-LENS | Ito-Levy change-of-variables; no DL angle. |
| 16 honest derivatives in `tools/full_audit.lean` | OUT-OF-SCOPE-FOR-MY-LENS | Glue / forwarder theorems over Tier 1 axioms; no DL angle. |

## Tools and sources used

- **Lean tools called**: None. The repo has no DL content, so no `lean_verify` / `lean_hover_info` / `lean_declaration_file` calls were warranted. (Would have wasted budget given the scope-empty result.)
- **Filesystem tools**: `Get-ChildItem -Recurse D:\LevyStochCalc\LevyStochCalc` (full module list), `Get-ChildItem -Recurse D:\LevyStochCalc -Filter *.py` (empty), Grep over the full source tree for DL/ML token list, Grep for `Classical.choose|noncomputable` for the forward-compat note.
- **Web searches**: None. No Lean DL content to cross-reference against the Han-Jentzen-E / Hure-Pham-Warin / Hornik / Cybenko literature.
- **Web fetches**: None.
- **Papers consulted**: None for this audit. The DL persona's reading list (Han-Jentzen-E 2017, Beck-E-Jentzen 2019, Hure-Pham-Warin 2020, Sirignano-Spiliopoulos 2018, Hornik 1991, Cybenko 1989) is fully applicable to the dissertation-side audit, not this library.

## What you couldn't verify

- I could not audit the actual `DeepBSDEJApproximationHypotheses`, `CXDiscretisationRegularity`, the `L(θ)` definition, the loss-function cross-check against `D:\DeepBSDE\src\**\*.py`, the universal-approximation citation, the Monte-Carlo / sample-complexity gap, or the `E12_mesh_refinement` numerical-experiment cross-check, because none of those live in `D:\LevyStochCalc\`. They live in `D:\Dissertation\` and `D:\DeepBSDE\`. The orchestrator should ensure a separate dissertation-side persona-9 pass covers them.

## Recommendations for the project (<= 5 bullets)

- (Library-side, optional) When/if a downstream `Dissertation/ContXiong/Wasserstein.lean` adds a `DeepBSDEJApproximationHypotheses` interface that calls into LevyStochCalc, keep the Lean side cleanly insulated from the network-architecture assumptions. The current `BSDEJ.Definition.IsBSDEJSolution` is a pure mathematical predicate with no `θ` parameter -- preserve that, and put any approximator interface on the dissertation side. (No action needed in this repo today.)
- (Library-side, optional) The 11 Tier 1 axioms are existence statements consumed via `Classical.choose`. If a future dissertation-side persona-9 audit needs to assert "the solution Y constructed by the Lean theorem is the same Y the Python network targets", the cleanest interface is to expose Y via a named accessor (e.g., `BSDEJ.solutionY`) with the existence axiom rewritten as `BSDEJ.solutionY` plus a separate "spec" theorem. This is purely a future-design hint -- no current defect.
- No other recommendations. The library is honestly out of scope for this persona.
