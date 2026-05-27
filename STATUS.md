# LevyStochCalc — Status (2026-05-27)

## Headline

**Library builds clean** (`lake build`: 8402 jobs, no errors).
**Lint passes** (`bash tools/lint.sh`: PASS at baseline of the
JumpDiffusion Picard-chain wrap-up sorry — see below).

## Sorry baseline (1 mathematical entry; 4 transitive forwarders)

There is a single genuinely-deferred classical theorem; the four
`tools/sorry_baseline.txt` lines are forwarders that all bottom out in
the same wrap-up sorry:

| Theorem | Citation | Role |
|---|---|---|
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` | Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV | Single explicit `sorry` for the Picard iteration in `S²([0,T]; ℝⁿ)` |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom` | (transitive) | 1-line forwarder over `_via_aeQuot` |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique` | (transitive) | 1-line forwarder |
| `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` | (transitive) | 1-line forwarder |

The wrap-up theorem has an honest statement (no trivial-witness in the
conclusion): the SDE integral equation is the `JumpDiffusion W N coeffs x₀`
structure's `is_solution` field, which is the literature Itô-with-jumps
integral equation in full form.

Previously, `BSDEJ.MartingaleRepresentation.jacodYor_representation` and
`Ito.JumpFormula.itoLevyFormula` were sorry'd. Both are now derived
theorems forwarding through honest Tier 1 cited axioms (the
#13a + #13b decomposition for jacodYor; #15 + #16 for itoLevyFormula).

## Tier 1 cited axioms (14 currently live)

See `tools/cited_axioms.md` for the full inventory. Numbering history:
#7 + #8 deleted 2026-05-22 (dead post-refactor per M4); #11 retired
2026-05-24 by decomposition into #15 + #16; #12 + #13 added 2026-05-23
via theorem→axiom promotion and then demoted axiom→theorem 2026-05-26
via the #13a/#13b decomposition + Bielecki AE-quotient wrap-up; #14
added 2026-05-23 then demoted axiom→theorem 2026-05-26; #16 narrowed
2026-05-26 from universal-`R` to canonical-`R` form; #17 + #18 added
in source 2026-05-23 and formally numbered in `tools/cited_axioms.md`
on 2026-05-27 (3rd-audit CRITICAL #1 closure). **Sorry baseline now has
1 entry**: `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`
(carries the entire literature Picard chain for Applebaum 6.2.9).

* **Brownian foundations** (4 axioms): `BrownianMotion.exists` (#1),
  `kolmogorovChentsov_modification` (#3), `brownian_martingale_rightCont`
  (#4), `itoIsometry_brownian_unified_existence` (#5).
* **Compensated-Poisson foundations** (2 axioms):
  `PoissonRandomMeasure.exists_of_sigmaFinite` (#2),
  `itoIsometry_compensated_unified_existence` (#6).
* **BSDEJ** (4 axioms): `continuousBSDEJ_exists_unique` (#9),
  `bsdej_path_regularity` (#10), `jacodYor_PRP_martingale_axiom` (#13a),
  `condExp_to_PRP_martingale_form_axiom` (#13b).
* **Itô-Lévy formula** (2 axioms):
  `itoFormula_continuousSemimartingale_axiom` (#15),
  `itoLevyFormula_jumpResidual_canonical_axiom` (#16).
* **Per-difference L²-isometries** (2 axioms — used by Picard contraction
  estimates and the #16 `ε → 0` limit): `itoIsometry_diff_brownian`
  (#17), `itoIsometry_diff_compensated` (#18).

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
* `redteam_findings/_REDTEAM_SUMMARY.md` — 2026-05-22 (2nd audit)
  meta-summary across 12 personas; the 1st-audit (2026-05-20) version
  is archived at `redteam_findings/2026-05-20-archive/_REDTEAM_SUMMARY.md`
  (P10 F10 fix per red-team 2nd audit 2026-05-23).
