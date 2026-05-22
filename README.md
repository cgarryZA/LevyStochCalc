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
lake build                # 8402 jobs
bash tools/lint.sh        # checks build + sorry baseline
```

Lean toolchain: `leanprover/lean4:v4.30.0-rc2`. Mathlib pin: see
`lakefile.toml`.

## Layout

```
LevyStochCalc/
├── Basic.lean                                 — common imports
├── Notation.lean                              — local notation (empty)
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
│   └── L2Isometry.lean                        — public isometry forwarder
├── Ito/
│   ├── Setting.lean                           — JumpDiffusion structure (baseline sorry)
│   └── JumpFormula.lean                       — Tier 1 #11 axiom
└── BSDEJ/
    ├── Definition.lean                        — IsBSDEJSolution predicate
    ├── Existence.lean                         — Tier 1 #9 axiom
    ├── PathRegularity.lean                    — Tier 1 #10 axiom
    └── MartingaleRepresentation.lean          — Jacod-Yor (baseline sorry)
```

## Tier 1 cited axioms

9 axioms total, each a published theorem from the literature with paper
references in `tools/cited_axioms.md`. Headlines:

1. `BrownianMotion.exists` — Karatzas-Shreve Thm 2.1.5 / Le Gall Def 2.1+2.12+Cor 2.11.
2. `PoissonRandomMeasure.exists_of_sigmaFinite` — Applebaum 2009 Thm 2.3.1.
3. `kolmogorovChentsov_modification` — Karatzas-Shreve Thm 2.2.8 / Le Gall Thm 2.9.
4. `brownian_martingale_rightCont` — Karatzas-Shreve Thm 2.7.7+2.7.9 / Le Gall Thm 2.13.
5. `itoIsometry_brownian_unified_existence` — Karatzas-Shreve Thm 3.2.6 / Le Gall Thm 5.4.
6. `itoIsometry_compensated_unified_existence` — Applebaum 2009 Thm 4.2.3+4.2.4.
9. `continuousBSDEJ_exists_unique` — Tang-Li 1994 / Andersson-Gnoatto-Patacca-Picarelli 2025.
10. `bsdej_path_regularity` — Bouchard-Elie 2008 SPA 118(1) pp 53-75.
11. `itoLevyFormula` — Applebaum 2009 Thm 4.4.7.

(Original Tier 1 #7 + #8 were deleted 2026-05-22 as dead post-refactor.)

## Sorry baseline

`tools/sorry_baseline.txt` contains 2 deferred classical theorems:

* `JumpDiffusion.exists_unique` — Picard iteration for jump-diffusion SDEs
  (Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV).
* `jacodYor_representation` — Jacod 1976 / Jacod-Shiryaev Thm III.4.34
  martingale representation theorem.

Both have honest statements: integrand outputs pinned to the canonical
`MultidimBrownianMotion.stochasticIntegral` and
`Compensated.stochasticIntegral` (no trivial-witness escape).

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
