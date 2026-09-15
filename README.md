# LevyStochCalc

A Lean 4 + Mathlib formalization of Lévy-driven stochastic calculus, with
emphasis on:

* L² Itô integrals against Brownian motion and compensated Poisson random
  measures (the Itô-Lévy isometry).
* The Itô-Lévy formula for `C^{1,2}` functions of jump diffusions
  (Applebaum 2009 Thm 4.4.7).
* Strong existence and uniqueness for the jump-diffusion SDE (Applebaum 2009
  Thm 6.2.9), and the solution predicate for backward SDEs with jumps.

This library is the substrate the main dissertation
(`D:/Dissertation`) forwards into for its continuous-time stochastic
foundations.

## What is and is not established

`tools/cited_axioms.md` is the ledger of record for every result this library cites rather than
proves; nothing in this README overrides it. Its current state:

* **No cited axiom is live, and there is no `axiom` declaration in the repository** (since
  2026-09-15). The last entry, #16 `Ito.JumpFormula.itoLevyFormula_jumpResidual_canonical_axiom`
  (Applebaum 2009 Thm 4.4.10 + Thm 4.4.7 step II), was deleted because its statement could not
  be proved: it asserted the formula at an arbitrary filtration unrelated to the solution's.
  The result it stood for — the Itô–Lévy formula for a `C²` function of a jump diffusion with
  no bound on the derivatives — is the theorem `Ito.JumpFormula.itoLevyFormula_general`
  (`Ito/ItoLevyFormulaGeneral.lean`, the same day), on the three standard axioms, stated at the
  solution's own filtration with the hypotheses ledger entry `Resolved #16` records; the
  dissertation forwards that theorem. Its bounded-derivative case
  `itoLevyFormula_of_boundedDerivs` (`Ito/ItoLevyBoundedDerivsSolution.lean`) is the milestone
  the proof is built on.
* **No `sorry`-carrying declaration.** `tools/sorry_baseline.txt` is empty since 2026-09-15
  (its last entry, the canonical assembly `itoLevyFormula_jumpResidual_canonical`, was deleted
  with `Ito/JumpFormulaAssembled.lean` when `itoLevyFormula_general` superseded it). No
  `#print axioms` report names `sorryAx`, and `sorry`/`admit` occur in the `.lean` sources only
  as words inside docstrings and comments.
* **Four entries were retired as unsound statements**, not proved and not weakened: BSDEJ
  existence (#9), BSDEJ path regularity (#10), the predictable representation property (#13a)
  and the continuous-semimartingale Itô formula (#15). The first three were refutable as
  written and the fourth trivially satisfiable; the declarations were deleted on 2026-09-06.
  Of these, BSDEJ existence and uniqueness returned on 2026-09-15 as the theorem
  `BSDEJ.Solves.exists_unique_solvesBSDEJ` (`BSDEJ/ExistenceUniqueness.lean`, ledger entry
  `Resolved #9`): over the augmented joint filtration of a Lévy driver, for a generator Lipschitz
  in `(y, z, u)` with the `L²(ν)` distance in the jump variable and a square integrable terminal
  datum, by the Picard scheme (`BSDEJ/PicardStep.lean` … `BSDEJ/PicardLimit.lean`) and the
  contraction in an exponentially weighted norm (`BSDEJ/PicardContraction.lean`), with the bridge
  `isBSDEJSolution_of_solvesBSDEJ` back to the earlier predicate. Path regularity (#10) and the
  single-driver PRP (#13a) remain statements to prove — `Plan.md` A7 and B5 — with the hypotheses
  the literature assumes; #15's content is #16's.

A `#print axioms` report of `{propext, Classical.choice, Quot.sound}` certifies the logical
trust base only. It is not evidence that a Lean statement is a faithful rendering of the result
it cites — that question is the subject of the per-entry statement audits in
`tools/cited_axioms.md`, several of which found statements that type-checked and said the wrong
thing.

## Build

```
lake build
bash tools/lint.sh                    # build + `#print axioms` audit
bash tools/verify_import_contract.sh  # checks dissertation-import contract
                                      # (paths from tools/import_contract.md)
```

Lean toolchain: `leanprover/lean4:v4.32.0` (see `lean-toolchain`). Mathlib pin:
`81a5d257c8e410db227a6665ed08f64fea08e997`; the `BrownianMotion` and `MathFin` requires are
pinned by commit in `lakefile.toml` to revisions that resolve to the same Mathlib.

## Layout

```
LevyStochCalc/
├── Basic.lean         — common imports + L² bridge lemmas
├── Analysis/          — Gronwall, sorted grids, scaled trigonometric bounds
├── Probability/       — filtrations, progressive measurability, conditional
│                        expectation limits, independence, transport
├── Brownian/          — Brownian motion, its filtration, the L² Itô integral
│                        and its algebra, Itô's formula, the Brownian PRP
├── Poisson/           — Poisson random measures, the compensated L² Itô-Lévy
│                        integral, mark-step calculus, MathFin bridge
├── Martingale/        — right-continuity, càdlàg modification, BDG, compensators
├── Driver/            — the joint Lévy driver (W, N): existence, germ
│                        independence, the càdlàg conditional-expectation martingale
├── Ito/               — the jump-diffusion setting, the Itô-Lévy formula
│                        (JumpFormula.lean holds the integrand vocabulary; the
│                        formula at bounded derivatives is ItoLevyBoundedDerivsSolution.lean),
│                        and the Picard well-posedness chain
└── BSDEJ/             — the BSDEJ data and solution predicate, the Picard map,
                         interval time-averages, the conditional-expectation
                         bridge to the PRP
```

Module-level detail is in each file's docstring; `tools/import_contract.md` lists the 13
modules and 19 symbols the dissertation pins.

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
  `D:/DeepBSDE/` and is OUT of `LevyStochCalc`'s scope.
* **`Classical.choose` in one integral.** The Brownian `stochasticIntegral` is a genuine
  construction (`stochasticIntegralBrownian`, the L² limit of the simple integrals). The
  compensated-Poisson `stochasticIntegral` is `Classical.choose` of `exists_cadlag_modification`
  — a proved theorem, not an axiom, but a choice all the same (as is the stage sequence of
  approximants beneath it, `Poisson/CompensatedApprox.lean`) — so it is `noncomputable` and its
  API is the `choose_spec` lemmas. A numerical extraction layer would have to wrap it in a
  separate computable approximation.
* **Non-vacuity witnesses are the `LevyStochCalcExamples` library** (`examples/`, 18 files,
  built by CI and by every local gate run). For each of the 14 cited results and the 41 pinned
  symbols of `tools/import_contract.md` a file applies the theorem by name to a concrete model
  (`d ∈ {1, 2}`, mark intensity `δ₁`, drivers from `LevyDriver.exists`) and exhibits a
  non-degenerate conclusion (a specific nonzero moment, a σ-algebra other than `⊥`, a solution
  that is not almost surely `0`). The models are finite-activity; the caveats each file states
  (the Kolmogorov constant is `𝔼[Z⁴]` rather than the literal `3`, the representing pair of
  `W_1` has nonzero energy but its Itô/marked split is not claimed, the separated cell-average
  rate is an upper bound) are listed in `Plan.md` C1.

## Lint

`tools/lint.sh` runs `lake build`, then `_audit.lean` (`#print axioms` over every load-bearing
declaration, written to `audit_output.txt`), and fails on any `sorryAx`-tainted theorem beyond
`tools/sorry_baseline.txt` (empty). The script is authoritative for what it enforces;
its hardening — failing on a failed audit run, an axiom allowlist, coverage of every audit
target, and a documentation-consistency check — is tracked as `X1b`–`X1g` and `X3i` in
`../Dissertation/RELEASE_READINESS.md`. Wire into pre-commit via:

```
cp tools/lint.sh .git/hooks/pre-commit
```

## License

Apache 2.0 — see [LICENSE](LICENSE).

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md).

## Status

Current state is whatever `lake build` and `bash tools/lint.sh` report; the per-result state is
`tools/cited_axioms.md`, and `GOAL.md` §1 is the definition of done.

## Authors

Christian Garry.
