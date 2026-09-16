#!/usr/bin/env bash
# Verify the dissertation-import contract from `tools/import_contract.md`.
#
# The dissertation at `D:/Dissertation` imports a fixed set of `LevyStochCalc`
# modules and references a fixed set of symbols from them. This script checks
# that each pinned module + symbol resolves on the current branch — refactors
# that delete or rename any of them MUST leave a forwarding stub at the old
# path so the dissertation continues to build without edits.
#
# What's verified:
# 1. Every module in `tools/import_contract.md` §1 resolves (file exists at the
#    documented path AND `import <Module>` succeeds in a probe).
# 2. Every fully-qualified symbol in §2 resolves (`#check <Symbol>` succeeds in
#    a probe — equivalent to "the symbol is reachable from `LevyStochCalc`'s
#    public API on the current branch").
#
# Run manually:    bash tools/verify_import_contract.sh
# Wire into CI:    `.github/workflows/ci.yml` (added 2026-05-27, audit HIGH #6)
#
# Closes red-team 3rd-audit HIGH #6: "CI does NOT verify the
# dissertation-import-contract".
set -euo pipefail

cd "$(git rev-parse --show-toplevel 2>/dev/null)" || cd "$(dirname "$0")/.."

# 1. Pinned modules — file paths must exist.
#    (Mirrors `tools/import_contract.md` §1.)
MODULES=(
  "LevyStochCalc/Poisson/RandomMeasure.lean"
  "LevyStochCalc/Brownian/Multidim.lean"
  "LevyStochCalc/BSDEJ/Definition.lean"
  "LevyStochCalc/BSDEJ/Existence.lean"
  "LevyStochCalc/BSDEJ/PathRegularity.lean"
  "LevyStochCalc/Ito/Setting.lean"
  "LevyStochCalc/Ito/JumpFormula.lean"
  "LevyStochCalc/Ito/ItoLevyFormulaGeneral.lean"
  "LevyStochCalc/Brownian/Construction.lean"
  "LevyStochCalc/Brownian/Continuity.lean"
  "LevyStochCalc/Brownian/Martingale.lean"
  "LevyStochCalc/Poisson/L2Isometry.lean"
  "LevyStochCalc/Poisson/Compensated.lean"
  "LevyStochCalc/Driver/PredictableRepresentation.lean"
  "LevyStochCalc/Driver/VectorIncrement.lean"
  "LevyStochCalc/Poisson/CompensatedIsometry.lean"
  "LevyStochCalc/BSDEJ/ExistenceUniqueness.lean"
)

# Imports = module paths converted to `LevyStochCalc.<...>` form.
IMPORTS=(
  "LevyStochCalc.Poisson.RandomMeasure"
  "LevyStochCalc.Brownian.Multidim"
  "LevyStochCalc.BSDEJ.Definition"
  "LevyStochCalc.BSDEJ.Existence"
  "LevyStochCalc.BSDEJ.PathRegularity"
  "LevyStochCalc.Ito.Setting"
  "LevyStochCalc.Ito.JumpFormula"
  "LevyStochCalc.Ito.ItoLevyFormulaGeneral"
  "LevyStochCalc.Brownian.Construction"
  "LevyStochCalc.Brownian.Continuity"
  "LevyStochCalc.Brownian.Martingale"
  "LevyStochCalc.Poisson.L2Isometry"
  "LevyStochCalc.Poisson.Compensated"
  "LevyStochCalc.Driver.PredictableRepresentation"
  "LevyStochCalc.Driver.VectorIncrement"
  "LevyStochCalc.Poisson.CompensatedIsometry"
  "LevyStochCalc.BSDEJ.ExistenceUniqueness"
)

# 2. Pinned symbols — fully-qualified names (must `#check` cleanly via the
#    `LevyStochCalc` umbrella import).
SYMBOLS=(
  # Poisson
  "LevyStochCalc.Poisson.PoissonRandomMeasure"
  "LevyStochCalc.Poisson.naturalFiltration"
  "LevyStochCalc.Poisson.Compensated.stochasticIntegral"
  "LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence"
  "LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry"
  # Brownian
  "LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion"
  "LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral"
  "LevyStochCalc.Brownian.Martingale.naturalFiltration"
  # Ito
  "LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs"
  "LevyStochCalc.Ito.Setting.JumpDiffusion"
  "LevyStochCalc.Ito.JumpFormula.diffusionIntegrand"
  "LevyStochCalc.Ito.JumpFormula.compensatorDriftIntegrand"
  "LevyStochCalc.Ito.JumpFormula.driftIntegrand"
  "LevyStochCalc.Ito.JumpFormula.itoLevyFormula_general"
  # BSDEJ
  "LevyStochCalc.BSDEJ.Definition.BSDEJData"
  "LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution"
  "LevyStochCalc.BSDEJ.Existence.Lipschitz"
  "LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_Z"
  "LevyStochCalc.BSDEJ.PathRegularity.cellTimeAverage_U"
  "LevyStochCalc.BSDEJ.Solves.augJoint"
  "LevyStochCalc.BSDEJ.Solves.SolvesBSDEJ"
  "LevyStochCalc.BSDEJ.Solves.exists_unique_solvesBSDEJ"
  # Driver (2026-09-15)
  "LevyStochCalc.Driver.LevyDriver"
  "LevyStochCalc.Driver.LevyDriver.filtration"
  "LevyStochCalc.Driver.LevyDriver.isBrownianFiltration"
  "LevyStochCalc.Driver.LevyDriver.isPoissonFiltration"
  "LevyStochCalc.Driver.LevyDriver.jointIntegral"
  "LevyStochCalc.Driver.LevyDriver.exists_predictable_jointIntegral"
  "LevyStochCalc.Driver.LevyDriver.incrementSigma"
  "LevyStochCalc.Driver.LevyDriver.regionSigma"
  "LevyStochCalc.Driver.LevyDriver.indep_stepSigma"
  # Consumed by Dissertation/CoupledFBSDEJ/LevyGridDrivers.lean (2026-09-15)
  "LevyStochCalc.Brownian.sigmaBrownian"
  "LevyStochCalc.Brownian.indep_iSup_sigmaBrownian_ne"
  "LevyStochCalc.Brownian.comap_increment_le_sigmaBrownian"
  "LevyStochCalc.Brownian.BrownianMotion.increment_gaussian"
  "LevyStochCalc.Poisson.referenceIntensity"
  "LevyStochCalc.Poisson.PoissonRandomMeasure.indep_iSup_comap_of_disjoint"
  "LevyStochCalc.Poisson.Compensated.compensated_mean_zero"
  "LevyStochCalc.Poisson.Compensated.compensated_second_moment"
  "LevyStochCalc.Poisson.Compensated.compensated_sq_integrable"
  "LevyStochCalc.Probability.comap_pi_eq_iSup"
)

# Step A: file-existence check (fast).
echo "==> Step A: pinned-module file existence"
MISSING_FILES=""
for f in "${MODULES[@]}"; do
  if [[ ! -f "$f" ]]; then
    MISSING_FILES+="$f"$'\n'
  fi
done
if [[ -n "$MISSING_FILES" ]]; then
  echo "FAIL: pinned module file(s) missing — dissertation-import contract broken:"
  echo "$MISSING_FILES" | sed 's/^/  /'
  echo ""
  echo "If a file was moved, add a forwarding stub at the old path per"
  echo "tools/import_contract.md §3."
  exit 1
fi
echo "  OK: all ${#MODULES[@]} pinned module files exist."

# Step B: each pinned import + symbol resolves via a single probe file.
echo "==> Step B: import + symbol resolution probe"
PROBE_FILE="_import_contract_probe.lean"
{
  echo "/-"
  echo " Auto-generated by tools/verify_import_contract.sh. Probes that the"
  echo " dissertation-import contract resolves on the current branch."
  echo ""
  echo " Do NOT commit — this file is .gitignored and the probe script"
  echo " removes it after running."
  echo "-/"
  for m in "${IMPORTS[@]}"; do
    echo "import $m"
  done
  echo ""
  for s in "${SYMBOLS[@]}"; do
    # `#check Name` works uniformly: for a structure/inductive it prints the
    # type-constructor's signature; for a theorem/axiom/definition it prints
    # the symbol's elaborated type. The probe just needs the elaborator to
    # find the name in the environment — we don't inspect the printed type.
    echo "#check $s"
  done
} > "$PROBE_FILE"

# Capture the probe output. `lake env lean` returns non-zero on probe failure;
# we want to capture and inspect either way.
set +e
PROBE_OUTPUT=$(lake env lean "$PROBE_FILE" 2>&1)
PROBE_RC=$?
set -e
rm -f "$PROBE_FILE"

if [[ $PROBE_RC -ne 0 ]]; then
  echo "FAIL: import-contract probe did not elaborate cleanly (rc=$PROBE_RC):"
  echo "$PROBE_OUTPUT" | sed 's/^/  /'
  echo ""
  echo "Likely a pinned symbol was renamed/deleted. Restore it or add a"
  echo "forwarding alias per tools/import_contract.md §3."
  exit 1
fi

# Even on rc=0 Lean can emit `unknown identifier` warnings; treat them as
# failures (the symbol contract says the name must resolve, not just compile).
if echo "$PROBE_OUTPUT" | grep -qE "unknown identifier|unknown constant|unresolved"; then
  echo "FAIL: import-contract probe reported unresolved identifiers:"
  echo "$PROBE_OUTPUT" | grep -E "unknown identifier|unknown constant|unresolved" | sed 's/^/  /'
  exit 1
fi

echo "  OK: all ${#IMPORTS[@]} imports + ${#SYMBOLS[@]} symbols resolved."
echo "PASS: dissertation-import contract verified."
