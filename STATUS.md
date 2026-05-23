# LevyStochCalc — Status (2026-05-22)

## Headline

**Library builds clean** (`lake build`: 8402 jobs, no errors).
**Lint passes** (`bash tools/lint.sh`: PASS at baseline of 2 sorry'd
theorems).

## Sorry baseline (2 entries)

Both are genuinely-deferred classical theorems with real statements:

| Theorem | Citation | Sorry size |
|---|---|---|
| `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` | Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV | Picard iteration in `S²([0,T]; ℝⁿ)` |
| `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` | Jacod 1976 / Jacod-Shiryaev Thm III.4.34 | Predictable-projection chaos decomposition |

Both have honest statements (no trivial-witness in the conclusion):
the Brownian and compensated-Poisson integrals are pinned to the
canonical `MultidimBrownianMotion.stochasticIntegral` /
`Compensated.stochasticIntegral` (the SDE coefficients and BSDEJ
integrands are bundled in existentials inside the predicate).

## Tier 1 cited axioms (9 currently live)

See `tools/cited_axioms.md` for the full inventory. P10 F2 fix
(red-team 2nd audit, 2026-05-23): previous count of "11" included the
two dead density-chain axioms (`cauchySeq_simpleIntegralLp_compensated`,
`adaptedSimple_dense_L2_compensated`) that the 2026-05-10
unified-existence refactor made redundant; both were deleted per M4.
Current count: 9. Summary:

* **Brownian foundations** (4 axioms): `BrownianMotion.exists`,
  `kolmogorovChentsov_modification`, `brownian_martingale_rightCont`,
  `itoIsometry_brownian_unified_existence`.
* **Compensated-Poisson foundations** (2 axioms):
  `PoissonRandomMeasure.exists_of_sigmaFinite`,
  `itoIsometry_compensated_unified_existence`.
* **BSDEJ + Itô-Lévy** (3 axioms): `continuousBSDEJ_exists_unique`,
  `bsdej_path_regularity`, `itoLevyFormula`.

## Recent activity (2026-05-22)

Following a 12-persona red-team audit that identified 24+ findings, all
9 CRITICAL and 8 HIGH findings were closed:

* **Soundness (C1, H1, H2)**: `IsBSDEJSolution` predicate strengthened
  with adaptedness layer + canonical multidim Brownian Itô integral
  pin for `M_W`.
* **Trivial-witness (C2, C3, C4, M1)**: `itoLevyFormula` axiom statement
  pinned to literature integral forms for all 4 terms; trivial-witness
  proof bodies on `JumpDiffusion.exists_unique` /
  `jacodYor_representation` replaced with honest sorries (in baseline);
  8 `True := trivial` stub lemmas deleted.
* **Hidden sorryAx (C5)**: `kolmogorov_modification_ae_eq` fully proved
  (no longer sorryAx); `poissonRandomMeasure_finite_exists` forwarded
  to the σ-finite cited axiom; `simplePredictable_dense_L2` dead chain
  (~540 lines) deleted.
* **Citations (C6, C7, H7, H8, M13)**: Gnoatto 2025 fabrication →
  Andersson-Gnoatto-Patacca-Picarelli 2025; Bouchard-Elie-Touzi 2009
  → Bouchard-Elie 2008; 3 Le Gall theorem-number errors corrected.
* **Git hygiene (C8, C9, H10)**: previously-untracked source files +
  build configs committed; `tools/lint.sh` hardened to fail on missing
  `_audit.lean`; `lake-manifest.json` fixed.
* **Hypothesis hygiene (H4, H5)**: Lipschitz + L²-terminal hypotheses
  added to BSDEJ axioms; `itoIsometry_compensated_unified_existence`
  gained `h_meas`/`h_sq_int` outer hypotheses to close the
  `integral_undef` exploit.
* **Path regularity (H3)**: `Z_avg`/`U_avg` pinned to
  `conditionalTimeAverage_*` projections.
* **Dead-code cleanup (M2, M3)**: 677-line orphan `Poisson/Martingale.lean`
  deleted; 4 dead-code `sorry` private lemmas eliminated.
* **Documentation (M6)**: `tools/cited_axioms.md` status section
  refreshed with full per-finding fix log.

## Architecture

```
LevyStochCalc/
├── Basic.lean                                 — common imports
├── Notation.lean                              — (mostly empty, future)
├── Brownian/
│   ├── Construction.lean                      — BrownianMotion structure + Tier 1 #1 axiom
│   ├── Continuity.lean                        — KC modification + ae_eq
│   ├── Martingale.lean                        — naturalFiltration W + Tier 1 #4 axiom
│   ├── Ito.lean                               — L² Itô integral (4000+ lines)
│   ├── SimplePredictableRefine.lean           — Tier 1 #5 axiom
│   ├── Multidim.lean                          — multidim BM structure
│   └── MultidimIto.lean                       — multidim L² Itô integral
├── Poisson/
│   ├── RandomMeasure.lean                     — Tier 1 #2 axiom + structure
│   ├── NaturalFiltration.lean                 — filtration definition
│   ├── Compensated.lean                       — L² Itô-Lévy integral (2900+ lines)
│   └── L2Isometry.lean                        — public isometry forwarder
├── Ito/
│   ├── Setting.lean                           — JumpDiffusion structure (sorry)
│   └── JumpFormula.lean                       — Tier 1 #11 axiom
└── BSDEJ/
    ├── Definition.lean                        — IsBSDEJSolution predicate
    ├── Existence.lean                         — Tier 1 #9 axiom
    ├── PathRegularity.lean                    — Tier 1 #10 axiom
    └── MartingaleRepresentation.lean          — Jacod-Yor (sorry)
```

## Build instructions

```
cd D:/LevyStochCalc
lake build           # 8402 jobs
bash tools/lint.sh   # checks build + sorry baseline
```

## See also

* `tools/cited_axioms.md` — full Tier 1 axiom inventory with paper references.
* `tools/sorry_baseline.txt` — currently-sorry'd theorems.
* `_audit.lean` — load-bearing axiom-budget audit.
* `redteam_findings/_REDTEAM_SUMMARY.md` — 2026-05-20 red-team audit
  (meta-summary across 12 personas).
