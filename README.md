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

**11 axioms total** (as of 2026-05-23), each a published theorem from the
literature with paper references in `tools/cited_axioms.md`. Numbering:
#7 and #8 deleted by the 2026-05-22 M4 cleanup (dead post-refactor);
#12 and #13 added 2026-05-23 by promoting the two previously sorry-bodied
theorems (`JumpDiffusion.exists_unique`, `jacodYor_representation`) to
honest Tier 1 axioms per Rule 0 (the `theorem ... := by sorry` form was
dishonest; the `axiom` form makes the claim match the content).

1. `BrownianMotion.exists` — Karatzas-Shreve Thm 2.2.2+2.2.8 / Le Gall Def 2.1+2.12+Cor 2.11.
2. `PoissonRandomMeasure.exists_of_sigmaFinite` — Applebaum 2009 Thm 2.3.1.
3. `kolmogorovChentsov_modification` — Karatzas-Shreve Thm 2.2.8 / Le Gall Thm 2.9.
4. `brownian_martingale_rightCont` — Karatzas-Shreve Thm 2.7.7+2.7.9 / Le Gall Thm 2.13.
5. `itoIsometry_brownian_unified_existence` — Karatzas-Shreve Thm 3.2.6 / Le Gall Thm 5.4.
6. `itoIsometry_compensated_unified_existence` — Applebaum 2009 Thm 4.2.3+4.2.4.
7. (deleted: `cauchySeq_simpleIntegralLp_compensated` — dead post-refactor 2026-05-22)
8. (deleted: `adaptedSimple_dense_L2_compensated` — dead post-refactor 2026-05-22)
9. `continuousBSDEJ_exists_unique` — Tang-Li 1994 / Andersson-Gnoatto-Patacca-Picarelli 2025.
10. `bsdej_path_regularity` — Bouchard-Elie 2008 SPA 118(1) pp 53-75.
11. `itoLevyFormula` — Applebaum 2009 Thm 4.4.7.
12. `JumpDiffusion.exists_unique` — Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV.
13. `jacodYor_representation` — Jacod 1975 / Jacod-Shiryaev Thm III.4.34.

## Sorry baseline

**EMPTY as of 2026-05-23.** The 2 previously sorry-bodied theorems were
promoted to Tier 1 cited axioms #12 and #13 per Rule 0 (claim = content).
The library now has **zero `sorryAx`** in its public API. The lint script
(`tools/lint.sh`) enforces this — any new sorry FAILs the lint.

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
