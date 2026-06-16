# LevyStochCalc → Mathlib-Grade Library — Master Plan (v2)

**Regenerated 2026-06-16** per the `GOAL.md` loop contract: Phase 0 (declutter)
and Phase 1 (structural refactor) are complete, and Phase 3 #3
(Kolmogorov–Chentsov continuous modification) is proved. Git history holds the
old plan + the detailed per-phase notes. This v2 plan closes the remaining
`GOAL.md` §1 gaps, **dissertation-blocking axioms first** (`GOAL.md` §3).

## Where we stand (verified 2026-06-16)

- **13 custom axioms** remain (`#print axioms` over `_audit.lean`; `cited_axioms.md`
  "13 live"). The 3 standard axioms (`propext`/`Classical.choice`/`Quot.sound`)
  are the only others.
- **1 documented `sorry`** (`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`,
  `tools/sorry_baseline.txt`) — disappears with the #9 chain.
- **6 of the 13 axioms gate the pinned dissertation surface** (the 21
  `import_contract.md` symbols), traced via `#print axioms`:
  **#5** `itoIsometry_brownian_unified_existence`,
  **#6** `itoIsometry_compensated_unified_existence`,
  **#15** `itoFormula_continuousSemimartingale_axiom`,
  **#16** `itoLevyFormula_jumpResidual_canonical_axiom`,
  **#9** `continuousBSDEJ_exists_unique`,
  **#10** `bsdej_path_regularity`.
  The other 7 (#1, #2, #4, #13a, #13b, #17, #18) are cited results but **not**
  reached by the pinned surface.
- **#5/#6 are foundational**: the audit shows #15, #16, #9, #10 *already carry*
  #5/#6 transitively, so the Itô-formula and BSDE layers cannot go axiom-free
  until the L² integrals are built. Hence #5 → #6 first.
- Four-way invariant green; build = 2904 jobs.

## Rules of engagement (unchanged, apply to every task)

- **Invariant after every commit:** `lake build` ✅ · `bash tools/lint.sh` at
  baseline (one documented sorry + the live axioms) ✅ ·
  `bash tools/verify_import_contract.sh` ✅ · (dissertation proxy) — if any goes
  red and isn't fixable fast, revert that step.
- **Never break the import contract** (`tools/import_contract.md`): 12 modules +
  21 symbols resolve from their pinned path; no forwarding stubs; don't rename
  public symbols or the top-level namespace.
- **Axiom→theorem discipline** (as used for KC #3): develop the proof as
  sorry-free standalone lemmas with the `axiom` left in place; only when the full
  `theorem` is sorry-free do you replace the axiom, repoint consumers, drop the
  entry from `tools/cited_axioms.md`, and confirm `#print axioms` shows the
  consumers clean. **Never** commit a new `sorry` to the built library.
- **No pin bump** (cross-repo mismatch risk). **Ponytail:** smallest diff, delete
  more than you add, one idea per file.

## Phase A — Close the 6 dissertation-surface axioms (critical path)

Bottom-up; each is a real `theorem` replacing its `axiom`, then drop from
`cited_axioms.md` + repoint consumers.

- [ ] **A1 / #5** `itoIsometry_brownian_unified_existence` — the L² Itô integral
      `t ↦ ∫_0^t H_s dW_s` against `W`, as a single `F : ℝ → Ω → ℝ` on
      `(naturalFiltration W).rightCont`, with **(i)** martingale, **(ii)** the
      quadratic-variation martingale `(F_t)² − ∫_0^t H² ds`, **(iii)** the
      L²-isometry at every `T` (KS 3.2.6). **Already sorry-free** (in
      `ItoSimple`/`ItoDensity`/`SimplePredictableRefine`/`ItoL2Completion`): the
      simple-integrand isometry (`simpleIntegral_isometry`), density
      (`simplePredictable_dense_L2`), Lp-Cauchy (`cauchySeq_simpleIntegralLp_brownian`),
      and the **per-`T`** isometry existence (`exists_itoIntegralL2_brownian`,
      `itoIntegralLp_brownian_L2_isometry`, `itoIsometry_brownian_existence`).
      **Gap to close:** (a) a single `F` across all `t` (not per-`T`); (b) its
      martingale property on `rightCont` (have the simple-level ingredients:
      `simpleIntegral_condExp_brownian`, `simpleIntegral_stronglyAdapted_brownian`,
      `simpleIntegral_integrable_brownian` — pass to the L²-limit via condExp
      L²-continuity); (c) the quadVar martingale (simple-level orthogonal-increment
      identity → limit). **Foundational — do first.**
- [ ] **A2 / #6** `itoIsometry_compensated_unified_existence` — compensated-Poisson
      analogue (Applebaum 4.2.3/4.2.4). Mirror A1 using the proved
      `Poisson/Compensated*` machinery (`CompensatedSimple`, `CompensatedIsometry`).
- [ ] **A3 / #17, #18** `itoIsometry_diff_brownian`, `itoIsometry_diff_compensated`
      — the per-difference L² isometries; fall out of A1/A2 (linearity of the
      integral). Close immediately after. *(Off the pinned surface but trivial
      once A1/A2 land; closing them removes axioms the Picard chain carries.)*
- [ ] **A4 / #15** `itoFormula_continuousSemimartingale_axiom` — Itô formula for
      continuous semimartingales (KS 3.3.6), now resting on a real A1.
- [ ] **A5 / #16** `itoLevyFormula_jumpResidual_canonical_axiom` — Itô–Lévy jump
      residual (Applebaum 4.4.10 + 4.4.7), on A2/A4.
- [ ] **A6 / #9** `continuousBSDEJ_exists_unique` — BSDEJ existence/uniqueness via
      the Picard chain (Tang–Li 1994 / AGPP 2025). **Retires the lone `sorry`**
      (`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`).
- [ ] **A7 / #10** `bsdej_path_regularity` — BSDEJ path regularity (Bouchard–Elie
      2008), on A6.

## Phase B — Close the 7 off-critical-path axioms (breadth)

- [ ] **B1 / #4** `brownian_martingale_rightCont` — BM is a martingale wrt the
      right-continuous augmentation (KS 2.7.7/2.7.9 + Blumenthal 0-1). Now more
      tractable since the continuity/KC machinery exists.
- [ ] **B2 / #1** `BrownianMotion.exists` — BM construction via Kolmogorov
      extension (KS 2.2 / Le Gall 2). Pairs with mathlib's BM project (Phase D
      alignment); consider `IsBrownianReal`/projective-family reuse first.
- [ ] **B3 / #2** `PoissonRandomMeasure.exists_of_sigmaFinite` — via Ionescu–Tulcea
      (`Mathlib/Probability/Kernel/IonescuTulcea/`), Applebaum 2.3.1.
- [ ] **B4 / #13b** `condExp_to_PRP_martingale_form_axiom` — Doob L² càdlàg
      regularization (KS I.3.13) + Blumenthal 0-1.
- [ ] **B5 / #13a** `jacodYor_PRP_martingale_axiom` — predictable representation
      property (Jacod 1975 / Jacod–Shiryaev III.4.34).

## Phase C — Non-vacuity artifact (`GOAL.md` §B)

- [ ] **C1** Add `examples/Nonvacuity.lean`: per cited result + pinned symbol, an
      `example` discharging the hypotheses on a concrete non-degenerate model
      (non-zero-variance BM, non-zero Itô integral, the intended BSDEJ solution),
      so non-vacuity is CI-checked, not promised. Start with the now-closed
      results (KC: the `brownian_continuous_modification` instantiation).

## Phase D — Mathlib-grade form + upstreaming (`GOAL.md` §D, §F)

- [ ] **D1** Align the BM layer to mathlib predicates (`IsBrownianReal`,
      `HasIndepIncrements`, `IsGaussianProcess`); track the Degenne BM project.
- [ ] **D2** Per closed, general result, in mathlib-readiness order (smallest
      `Basic.lean` `eLpNorm` helpers first; then BM/KC pieces — coordinate on
      Zulip; then PointProcess → StochasticIntegral → SDE → BSDE): re-home to
      `ProbabilityTheory` + `Mathlib/Probability/<Area>/…`, register, AI-disclosure
      + `LLM-generated` label, update the dissertation import to the mathlib path.

## Definition of done

Exactly `GOAL.md` §1: zero `sorry`/custom-axiom, non-vacuity CI artifact,
mathlib-grade form, dissertation builds against pinned symbols, CI green, general
results merged/PR-open. Regenerate this plan if it is exhausted before then.

## Sequencing

A1 (#5) → A2 (#6) → A3 (#17/#18) unblock A4/A5 (Itô/Lévy formula) and A6/A7
(BSDE), in that order — this clears the entire pinned surface. Phase B widens to
the remaining citations; C makes non-vacuity mechanical; D upstreams. Never
advance with the four-way invariant red.
