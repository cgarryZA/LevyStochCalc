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

* **One cited axiom is live** — entry #16,
  `Ito.JumpFormula.itoLevyFormula_jumpResidual_canonical_axiom` (Applebaum 2009 Thm 4.4.10 +
  Thm 4.4.7 step II, the canonical-`R` form). It is the only `axiom` declaration in the
  repository, at `LevyStochCalc/Ito/JumpFormula.lean:189`. Three declarations in the library
  depend on it — itself, `itoLevyFormula_jumpResidual_axiom` and `itoLevyFormula` — and one
  downstream, the dissertation forwarder `Dissertation.Continuous.itoLevyFormula`.
* **No `sorry`.** `tools/sorry_baseline.txt` is empty, no `#print axioms` report names
  `sorryAx`, and `sorry`/`admit` occur in the `.lean` sources only as words inside docstrings
  and comments. The Picard-chain wrap-up that held the last baseline entry was discharged and
  deleted on 2026-09-07.
* **Four entries were retired as unsound statements**, not proved and not weakened: BSDEJ
  existence (#9), BSDEJ path regularity (#10), the predictable representation property (#13a)
  and the continuous-semimartingale Itô formula (#15). The first three were refutable as
  written and the fourth trivially satisfiable; the declarations were deleted on 2026-09-06.
  The BSDEJ layer therefore states the solution predicate and the Picard map, but **not**
  existence, path regularity or the PRP. Now that the integrals are stated over a common
  filtration (`Plan.md` X2), those three return as statements to prove — `Plan.md` A6, A7 and
  B5 — with the hypotheses the literature assumes; #15's content is #16's.

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
│                        (JumpFormula.lean holds the one live cited axiom),
│                        and the Picard well-posedness chain
└── BSDEJ/             — the BSDEJ data and solution predicate, the Picard map,
                         interval time-averages, the conditional-expectation
                         bridge to the PRP
```

Module-level detail is in each file's docstring; `tools/import_contract.md` lists the 12
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
* **Non-vacuity is not yet a CI artifact.** `GOAL.md` §1.B asks for an
  `examples/Nonvacuity.lean` collecting, per headline result, an `example` that discharges its
  hypotheses on a concrete non-degenerate model. It is not written. The satisfiability that
  *is* established is the filtration hypothesis of the integrals
  (`Driver.exists_isBrownianFiltration_and_isPoissonFiltration`); whether the SDE, the
  Itô-Lévy formula's hypotheses or a BSDEJ have solutions is separate and open.

## Lint

`tools/lint.sh` runs `lake build`, then `_audit.lean` (`#print axioms` over every load-bearing
declaration, written to `audit_output.txt`), and fails on any `sorryAx`-tainted theorem beyond
`tools/sorry_baseline.txt` (which is empty). The script is authoritative for what it enforces;
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
