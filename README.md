# LevyStochCalc

A Lean 4 + Mathlib formalization of Lévy-driven stochastic calculus, with
emphasis on:

* L² Itô integrals against Brownian motion and compensated Poisson random
  measures (the Itô-Lévy isometry).
* The Itô-Lévy formula for `C^{1,2}` functions of jump diffusions
  (Applebaum 2009 Thm 4.4.7).
* Backward stochastic differential equations with jumps (BSDEJs) — existence,
  uniqueness, and path regularity (Tang-Li 1994 / Bouchard-Elie 2008).

This library is the substrate the main dissertation
(`D:/Dissertation`) forwards into for its continuous-time stochastic
foundations.

## Build

```
lake build                            # 8402 jobs
bash tools/lint.sh                    # checks build + sorry baseline
bash tools/verify_import_contract.sh  # checks dissertation-import contract
                                      # (paths from tools/import_contract.md)
```

Lean toolchain: `leanprover/lean4:v4.30.0-rc2`. Mathlib pin: see
`lakefile.toml`.

## Layout

```
LevyStochCalc/
├── Basic.lean                                 — common imports + L² bridge lemmas
├── Brownian/
│   ├── Construction.lean                      — BrownianMotion structure + Tier 1 #1 axiom
│   ├── Continuity.lean                        — KC modification + ae_eq (proven)
│   ├── Martingale.lean                        — naturalFiltration W + Tier 1 #4 axiom
│   ├── Ito.lean                               — L² Itô integral (4000+ lines)
│   ├── SimplePredictableRefine.lean           — Tier 1 #5 axiom
│   ├── Multidim.lean                          — multidim BM structure
│   └── MultidimIto.lean                       — multidim L² Itô integral
├── Poisson/
│   ├── RandomMeasure.lean                     — Tier 1 #2 axiom + structure
│   ├── NaturalFiltration.lean                 — filtration definition
│   ├── Compensated.lean                       — L² Itô-Lévy integral (2400+ lines)
│   │                                            + Tier 1 auxiliary axiom
│   │                                            itoIsometry_diff_compensated
│   └── L2Isometry.lean                        — public isometry forwarder
├── Ito/
│   ├── Setting.lean                           — JumpDiffusion structure (baseline sorry)
│   ├── JumpFormula.lean                       — Tier 1 #15 + #16 axioms + derived #11/#16 thms
│   ├── Picard.lean                            — Picard map + Bielecki β-norm framework,
│   │                                            σ/γ L² Lipschitz bounds (auxiliary axiom
│   │                                            itoIsometry_diff_brownian), self-map and
│   │                                            Bielecki contraction
│   ├── PicardSpace.lean                       — complete metric space of bounded processes:
│   │                                            discrete metric + Bielecki β-norm AE-quotient
│   │                                            and wrap-up (single explicit baseline sorry
│   │                                            for the entire Picard chain)
│   └── PicardFixedPoint.lean                  — Banach-shim + JumpDiffusion.exists_unique
│                                                forwarder (ex-Tier-1-axiom #14, now theorem)
└── BSDEJ/
    ├── Definition.lean                        — IsBSDEJSolution predicate + regression-test
    │                                            extractors (Y-cadlag, Z/U progressive, M_W
    │                                            and M_N canonical-integral pins)
    ├── Existence.lean                         — Tier 1 #9 axiom (Y-only uniqueness)
    ├── PathRegularity.lean                    — Tier 1 #10 axiom + linear-rate corollary
    └── MartingaleRepresentation.lean          — Tier 1 #13a + #13b sub-axioms; #13 is now
                                                  a derived theorem forwarder
```

## Tier 1 cited axioms

**14 axioms total** (as of 2026-05-27, 3rd-audit reconciliation), each a
published theorem from the literature with paper references in
`tools/cited_axioms.md`. Numbering history:

* #7 and #8 deleted by the 2026-05-22 M4 cleanup (dead post-refactor).
* #11 (`itoLevyFormula`) retired 2026-05-24 by decomposition into the two
  narrower axioms #15 + #16; `itoLevyFormula` is now a derived theorem.
* #12 (`JumpDiffusion.exists_unique`) and #13
  (`jacodYor_representation_axiom`) were promoted theorem→axiom on
  2026-05-23 and then demoted axiom→theorem on 2026-05-26 via the
  Bielecki AE-quotient wrap-up + #13a/#13b decomposition.
* #14 (`picardFixedPoint_jumpDiffusion_exists_unique_axiom`) was added
  2026-05-23 then demoted axiom→theorem on 2026-05-26 (forwards through
  the wrap-up `_via_aeQuot`, which carries the single explicit baseline
  `sorry`).
* #16 (`itoLevyFormula_jumpResidual_canonical_axiom`) was NARROWED on
  2026-05-26 from the universal-`R` form to the canonical-`R` form; the
  universal-`R` form is now a derived theorem.
* #17 (`itoIsometry_diff_brownian`) and #18 (`itoIsometry_diff_compensated`)
  were added in source on 2026-05-23 but first formally numbered in
  `tools/cited_axioms.md` on 2026-05-27 (3rd-audit CRITICAL #1 closure).

Currently-live axioms:

1. `BrownianMotion.exists` — Karatzas-Shreve Thm 2.2.2+2.2.8 / Le Gall Def 2.1+2.12+Cor 2.11.
2. `PoissonRandomMeasure.exists_of_sigmaFinite` — Applebaum 2009 Thm 2.3.1.
3. `kolmogorovChentsov_modification` — Karatzas-Shreve Thm 2.2.8 / Le Gall Thm 2.9.
4. `brownian_martingale_rightCont` — Karatzas-Shreve Thm 2.7.7+2.7.9 / Le Gall Thm 2.13.
5. `itoIsometry_brownian_unified_existence` — Karatzas-Shreve Thm 3.2.6 / Le Gall Thm 5.4.
6. `itoIsometry_compensated_unified_existence` — Applebaum 2009 Thm 4.2.3+4.2.4.
9. `continuousBSDEJ_exists_unique` — Tang-Li 1994 / Andersson-Gnoatto-Patacca-Picarelli 2025.
10. `bsdej_path_regularity` — Bouchard-Elie 2008 SPA 118(1) pp 53-75.
13a. `jacodYor_PRP_martingale_axiom` — Jacod 1975 / Jacod-Shiryaev Thm III.4.34 (martingale-input form).
13b. `condExp_to_PRP_martingale_form_axiom` — Karatzas-Shreve Thm I.3.13 (Doob L² càdlàg regularization) + Thm 2.7.17 (Blumenthal 0-1) + Applebaum Thm 2.3.7.
15. `itoFormula_continuousSemimartingale_axiom` — Karatzas-Shreve Thm 3.3.6 / Le Gall Thm 5.10.
16. `itoLevyFormula_jumpResidual_canonical_axiom` — Applebaum 2009 Thm 4.4.10 + Thm 4.4.7 step (II) (canonical-`R` form).
17. `itoIsometry_diff_brownian` — Karatzas-Shreve Thm 3.2.6 + §3.2.B eq. (2.20) (per-difference L²-isometry).
18. `itoIsometry_diff_compensated` — Applebaum 2009 Thm 4.2.3 step (II) (per-difference L²-isometry).

(Retired entries #7, #8, #11, #12, #13, #14 are kept in `tools/cited_axioms.md`
for traceability.)

## Sorry baseline

**1 mathematical entry (as of 2026-05-27)**, with 4 transitive
forwarders bottoming out in it. The single sorry is in the wrap-up
theorem `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`
(Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV — the literature Picard
iteration in `S²([0,T]; ℝⁿ)`). The previous Tier 1 axiom #14 was
demoted to a theorem on 2026-05-26 with the literature dependency moved
into this single explicit sorry, making the unresolved analytical content
visible to the lint pipeline rather than hidden behind an axiom.

See `STATUS.md` and `tools/sorry_baseline.txt` for the full chain.

## Scope (deliberate omissions)

P3 F7-F9, P8, P9 F1-F2 (red-team 2nd audit 2026-05-23): documented
out-of-scope items so downstream readers don't expect content the
library doesn't claim.

* **`BSDEJData` is scalar-Y, Lipschitz-driver only.** Vector-Y BSDEJ
  (FBSDEJ couples, multi-Y systems), quadratic-growth drivers
  (Becherer 2006 utility hedging), and reflected/constrained BSDEJ
  are NOT covered. The current scope matches Tang-Li 1994 + AGPP 2025
  + Delong 2013 + Bouchard-Elie 2008 exactly.
* **`X` in `IsBSDEJSolution` is exogenous.** The predicate takes `X`
  as a bare jointly-measurable function without requiring it to be
  the strong solution of any forward SDE. Decoupled FBSDEJ structure
  (where `X` solves a forward jump-SDE driven by the SAME `(W, N)`)
  is delivered separately by the `JumpDiffusion W N coeffs x₀`
  structure and `JumpDiffusion.exists_unique`; combining them into a
  single FBSDEJ predicate is a downstream extension.
* **No Lévy-process structure.** `PoissonRandomMeasure` is the
  underlying building block; the Lévy-measure integrability condition
  `∫(1 ∧ |x|²) ν(dx) < ∞` is NOT required (we only need σ-finite ν
  per Applebaum 2.3.1). Specific Lévy processes (α-stable, variance-
  gamma, CGMY, etc.) are not constructed — they are downstream
  applications of the PRM + compensated-integral toolkit.
* **No deep-learning code.** The dissertation that motivates this
  formalization includes deep-BSDE training code; that code lives in
  `D:/DeepBSDE/` and is OUT of `LevyStochCalc`'s scope. LevyStochCalc
  provides the literature-pinned axiom layer (Tier 1 cited axioms +
  honest derivative theorems) that the dissertation imports.
* **`Classical.choose`-based `noncomputable`.** The stochasticIntegral
  definitions use `Classical.choose` on the unified-existence axioms,
  hence are `noncomputable`. This is mathematically correct (no
  algorithm extracts the L²-Itô integral from its defining axiom) but
  means future numerical extraction layers must wrap them with
  separate computable approximations (e.g., simpleIntegral on a
  partition).

## Lint

`tools/lint.sh` runs `lake build` + `_audit.lean` and fails on any new
`sorryAx`-tainted theorem beyond the baseline. Wire into pre-commit via:

```
cp tools/lint.sh .git/hooks/pre-commit
```

## License

Apache 2.0 — see [LICENSE](LICENSE).

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## Status

See [STATUS.md](STATUS.md) for current state and recent activity.

## Authors

Christian Garry.
