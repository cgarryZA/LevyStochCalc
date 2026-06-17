# Dissertation Import Contract

The dissertation at `D:/Dissertation` (Lake path-dependency on `../LevyStochCalc`)
imports a fixed set of `LevyStochCalc` modules and references a fixed set of
symbols from them. This file enumerates the contract.

**Promise**: the modules and symbols listed below MUST continue to resolve from
the public API of `LevyStochCalc` (on `master`) at the documented module path.

In-tree refactors keep this promise by *not relocating the pinned symbols*: when
a file is split for size, the pinned symbols stay in the module of record and the
non-pinned content moves into new sub-modules it imports. We do **not** add
forwarding-stub files — those are dead-weight indirection. If a pinned symbol is
ever genuinely relocated (e.g. Phase 4 upstreaming into mathlib's
`ProbabilityTheory` namespace), the fix is to update the consumer's import in the
dissertation repo, not to leave a stub behind here.

## 1. Pinned modules (12)

| # | Module path                              | File                                           | Used by                                                       |
|---|------------------------------------------|------------------------------------------------|---------------------------------------------------------------|
| 1 | `LevyStochCalc.Poisson.RandomMeasure`    | `LevyStochCalc/Poisson/RandomMeasure.lean`     | `Dissertation/Continuous.lean`                                |
| 2 | `LevyStochCalc.Brownian.Multidim`        | `LevyStochCalc/Brownian/Multidim.lean`         | `Dissertation/Continuous.lean`                                |
| 3 | `LevyStochCalc.BSDEJ.Definition`         | `LevyStochCalc/BSDEJ/Definition.lean`          | `Dissertation/Continuous.lean`, `ContXiong/*.lean`            |
| 4 | `LevyStochCalc.BSDEJ.Existence`          | `LevyStochCalc/BSDEJ/Existence.lean`           | `Dissertation/Continuous.lean`                                |
| 5 | `LevyStochCalc.BSDEJ.PathRegularity`     | `LevyStochCalc/BSDEJ/PathRegularity.lean`      | `Dissertation/Continuous.lean`                                |
| 6 | `LevyStochCalc.Ito.Setting`              | `LevyStochCalc/Ito/Setting.lean`               | `Dissertation/Continuous.lean`                                |
| 7 | `LevyStochCalc.Ito.JumpFormula`          | `LevyStochCalc/Ito/JumpFormula.lean`           | `Dissertation/Continuous.lean`                                |
| 8 | `LevyStochCalc.Brownian.Construction`    | `LevyStochCalc/Brownian/Construction.lean`     | (transitive via Multidim / Setting)                           |
| 9 | `LevyStochCalc.Brownian.Continuity`      | `LevyStochCalc/Brownian/Continuity.lean`       | (transitive via Multidim / Setting)                           |
| 10 | `LevyStochCalc.Brownian.Martingale`      | `LevyStochCalc/Brownian/Martingale.lean`       | `Dissertation/Continuous.lean` (`naturalFiltration`)          |
| 11 | `LevyStochCalc.Poisson.L2Isometry`       | `LevyStochCalc/Poisson/L2Isometry.lean`        | `Dissertation/Continuous.lean`, `Continuous/LevyStochCalcBridge.lean` |
| 12 | `LevyStochCalc.Poisson.Compensated`      | `LevyStochCalc/Poisson/Compensated.lean`       | `Dissertation/Continuous.lean`, `Continuous/LevyStochCalcBridge.lean` |

## 2. Pinned symbols

Symbols the dissertation references via fully-qualified names. Each MUST
remain reachable under the listed namespace prefix.

### `LevyStochCalc.Poisson`

| Symbol                                                      | Defined in                                |
|-------------------------------------------------------------|-------------------------------------------|
| `PoissonRandomMeasure`                                      | `Poisson/RandomMeasure.lean`              |
| `naturalFiltration`                                         | `Poisson/NaturalFiltration.lean`          |
| `Compensated.stochasticIntegral`                            | `Poisson/Compensated.lean`                |
| `Compensated.itoIsometry_compensated_unified_existence`     | `Poisson/Compensated.lean` (cited axiom #6) |
| `L2Isometry.itoLevyIsometry`                                | `Poisson/L2Isometry.lean`                 |

### `LevyStochCalc.Brownian`

| Symbol                                                      | Defined in                                |
|-------------------------------------------------------------|-------------------------------------------|
| `Multidim.MultidimBrownianMotion`                           | `Brownian/Multidim.lean`                  |
| `Multidim.MultidimBrownianMotion.stochasticIntegral`        | `Brownian/MultidimIto.lean` (transitively reachable from `Brownian.Multidim` consumers via the `Setting`/`BSDEJ.Definition` chain) |
| `Martingale.naturalFiltration`                              | `Brownian/Martingale.lean`                |

### `LevyStochCalc.Ito`

| Symbol                                                      | Defined in                                |
|-------------------------------------------------------------|-------------------------------------------|
| `Setting.JumpDiffusionCoeffs`                               | `Ito/Setting.lean`                        |
| `Setting.JumpDiffusion`                                     | `Ito/Setting.lean`                        |
| `JumpFormula.diffusionIntegrand`                            | `Ito/JumpFormula.lean`                    |
| `JumpFormula.compensatorDriftIntegrand`                     | `Ito/JumpFormula.lean`                    |
| `JumpFormula.driftIntegrand`                                | `Ito/JumpFormula.lean`                    |
| `JumpFormula.itoLevyFormula`                                | `Ito/JumpFormula.lean` (cited axiom)      |

### `LevyStochCalc.BSDEJ`

| Symbol                                                      | Defined in                                |
|-------------------------------------------------------------|-------------------------------------------|
| `Definition.BSDEJData`                                      | `BSDEJ/Definition.lean`                   |
| `Definition.IsBSDEJSolution`                                | `BSDEJ/Definition.lean`                   |
| `Existence.Lipschitz`                                       | `BSDEJ/Existence.lean`                    |
| `Existence.continuousBSDEJ_exists_unique`                   | `BSDEJ/Existence.lean` (cited axiom)      |
| `PathRegularity.conditionalTimeAverage_Z`                   | `BSDEJ/PathRegularity.lean`               |
| `PathRegularity.conditionalTimeAverage_U`                   | `BSDEJ/PathRegularity.lean`               |
| `PathRegularity.bsdej_path_regularity`                      | `BSDEJ/PathRegularity.lean` (cited axiom) |

## 3. Refactor protocol

**Splitting a pinned file for size (the common case).** Keep the pinned
symbols (§2) in the module of record at their pinned path; move only the
*non-pinned* content into new sub-modules that the module of record imports.
The pinned path still resolves natively, so nothing downstream changes. Run
`tools/verify_import_contract.sh` — it must stay green.

**Relocating a pinned symbol (rare — e.g. Phase 4 upstreaming).** If a pinned
symbol genuinely has to leave its pinned path:

1. Update the consumer import in the dissertation repo (`D:/Dissertation`) to
   the new path; rebuild it there with `lake build`. Do **not** leave a
   forwarding stub in this repo.
2. Update this file: change the symbol's path in §2 (and the module row in §1
   if a module is retired), and note the dissertation commit that tracks it.
3. Run `tools/lint.sh` (baseline 0) and `tools/verify_import_contract.sh`. If a
   pinned symbol moved, update the probe in `verify_import_contract.sh` to its
   new path in the same commit, so the contract guard tracks reality.

The dissertation cannot be built from the web container; relocations of pinned
symbols are therefore coordinated with whoever can build `D:/Dissertation`.

## 4. How to (re-)verify the contract

```bash
# From D:/LevyStochCalc
lake build                                  # 1. LevyStochCalc itself builds
bash tools/lint.sh                          # 2. lint passes at baseline 0
bash tools/verify_import_contract.sh        # 3. import contract resolves
                                            #    (added 2026-05-27, audit HIGH #6)

# From D:/Dissertation
lake build                                  # 4. dissertation builds
```

All four must pass. If (3) fails, a pinned symbol stopped resolving from its
pinned path on the LevyStochCalc side — move it back (or re-export it from the
module of record) and re-run (3). A deliberate relocation of a pinned symbol
follows §3: update the dissertation import (4) and the §2 path together.

Step (3) is now automated in CI (`.github/workflows/ci.yml`, the
`tools/verify_import_contract.sh` step) — so the contract cannot be
broken on `master` without the build going red.

## 5. Audit history

| Date       | Verified-against master HEAD | Notes                                                         |
|------------|------------------------------|---------------------------------------------------------------|
| 2026-05-24 | `7a6be4d`                    | Initial contract. All 12 paths present + dissertation builds. |
| 2026-05-27 | (this branch)                | Added `tools/verify_import_contract.sh` + CI step. Closes red-team 3rd-audit HIGH #6. |
