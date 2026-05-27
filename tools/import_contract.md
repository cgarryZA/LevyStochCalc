# Dissertation Import Contract

The dissertation at `D:/Dissertation` (Lake path-dependency on `../LevyStochCalc`)
imports a fixed set of `LevyStochCalc` modules and references a fixed set of
symbols from them. This file enumerates the contract.

**Promise**: the modules and symbols listed below MUST continue to resolve from
the public API of `LevyStochCalc` (on `master`) at the documented module path.
A refactor that deletes or renames any of them must, at minimum, leave a
forwarding stub at the old path so the dissertation continues to build without
edits.

A forwarding stub is a `.lean` file at the old path containing only:
```
import LevyStochCalc.<NewPath>
-- optional: re-export specific names
export LevyStochCalc.<NewPath> (sym1 sym2 ...)
```

Last verified: 2026-05-24 against master `7a6be4d` (LevyStochCalc) +
dissertation `Continuous.lean` HEAD.

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

Before merging a branch that deletes or renames any path in §1 or any
symbol in §2:

1. **Build the dissertation against the branch.** From `D:/Dissertation`:
   ```
   lake build
   ```
   This must succeed. If it fails because a path moved, add a forwarding
   stub at the old path.

2. **Forwarding-stub template.** Suppose `LevyStochCalc/Old/Path.lean` moved
   to `LevyStochCalc/New/Path.lean`. Recreate the old file as:
   ```
   /-
   Forwarding stub: this module was relocated to `LevyStochCalc.New.Path`.
   Retained so the dissertation (and any other downstream consumer) keeps
   building against the old import path.
   -/
   import LevyStochCalc.New.Path

   -- Optionally re-export specific names if the namespace also changed:
   -- export LevyStochCalc.New.Path (symA symB ...)
   ```
   The stub adds ~3 lines and zero load-bearing logic, so it does not
   affect axiom counts or sorry baselines.

3. **Update this file.** Replace the row's "File" column with the new
   path (keep the old module path in column 2 so the forwarding-stub
   guarantee remains visible).

4. **Run `tools/lint.sh`.** Must stay at baseline 0.

5. **Coordinate with the dissertation.** If a rename is desired on the
   dissertation side too (so the stub can eventually be removed), open
   a PR over there and reference this contract. Don't delete a stub
   until the dissertation has merged the new import path AND the next
   dissertation release is cut.

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

All four must pass. If (3) fails the contract has been silently broken on
the LevyStochCalc side; if (4) fails on a missing module/symbol, restore
or add a forwarding stub on the LevyStochCalc side and re-run (3) — do
NOT edit the dissertation imports as a first response.

Step (3) is now automated in CI (`.github/workflows/ci.yml`, the
`tools/verify_import_contract.sh` step) — so the contract cannot be
broken on `master` without the build going red.

## 5. Audit history

| Date       | Verified-against master HEAD | Notes                                                         |
|------------|------------------------------|---------------------------------------------------------------|
| 2026-05-24 | `7a6be4d`                    | Initial contract. All 12 paths present + dissertation builds. |
| 2026-05-27 | (this branch)                | Added `tools/verify_import_contract.sh` + CI step. Closes red-team 3rd-audit HIGH #6. |
