# LevyStochCalc → Mathlib-Grade Library — Master Plan (v2)

**Regenerated 2026-06-16** per the `GOAL.md` loop contract: Phase 0 (declutter)
and Phase 1 (structural refactor) are complete, and Phase 3 #3
(Kolmogorov–Chentsov continuous modification) is proved. Git history holds the
old plan + the detailed per-phase notes. This v2 plan closes the remaining
`GOAL.md` §1 gaps, **dissertation-blocking axioms first** (`GOAL.md` §3).

## Where we stand (verified 2026-06-16)

- **0 custom axioms** remain — #16 deleted 2026-09-15 as unprovable as stated and the general
  statement it stood for **proved** the same day (`itoLevyFormula_general`,
  `tools/cited_axioms.md`, `Resolved #16`) (was 13; **#5 and #17 closed 2026-06-17**, **#1
  closed 2026-09-05** via `RemyDegenne/brownian-motion`, **#4, #6, #18, #2 and #13b closed
  2026-09-06**,
  **#15 retired 2026-09-06** as a vacuous statement, **#9, #10, #13a retired 2026-09-06 as
  refutable statements** — deleted, not relocated). `cited_axioms.md` "1 live". The 3 standard
  axioms (`propext`/`Classical.choice`/`Quot.sound`) are the only others. **The BSDEJ layer no
  longer states existence, path regularity or the PRP**; those return, correctly stated, with X2.
- **Integrand-class audit 2026-09-06**: every integral's `h_progMeas` hypothesis admits only
  integrands a.s. constant in `ω` at each time (no `s ≤ t` restriction; `ℱ 0` P-trivial), so
  the proved integral theorems are about Wiener integrals of deterministic integrands and the
  SDE/BSDEJ layers are confined to that class — see `tools/cited_axioms.md`, "Integrand-class
  audit". Fixed by X2.
- **Statement audit 2026-09-06 (#16)**: the Itô–Lévy axiom lacked `u ∈ C²` and drift
  integrability and was refutable; both are now hypotheses (see `tools/cited_axioms.md` #16).
  The same audit found that the library's `L²` integrals accept only integrands adapted to
  the natural filtration of a *single* driver, so `JumpDiffusion.is_solution` and the PRP/BSDEJ
  statements (#13a, #13b, #9, #10) are faithful only for uncoupled coefficients — the
  common-filtration generalization **X2** below now precedes A5–A7.
- **`sorry` status (2026-09-15)**: `tools/sorry_baseline.txt` is empty — its last entry, the
  canonical assembly `itoLevyFormula_jumpResidual_canonical` (`Ito/JumpFormulaAssembled.lean`,
  seven `sorry` blocks), was deleted with its file when the general Itô–Lévy formula became the
  theorem `itoLevyFormula_general` (`Ito/ItoLevyFormulaGeneral.lean`, M3, 2026-09-15). The
  bounded-derivative milestone M16
  (`itoLevyFormula_jumpResidual_of_boundedDerivs`) is proved with no `sorry` (2026-09-10) and
  takes no cross witness (2026-09-11, B4-C12) and is callable from the solution data
  (2026-09-11, B4-C13); the locality of the compensated integral at a stopping time, the
  Stage-2 transfer tool, is proved in `Ito/CompensatedLocality.lean` (2026-09-11, B4-L4).
  Its everywhere-left-limit hypothesis is discharged rather than assumed since 2026-09-11:
  `itoLevyFormula_jumpResidual_of_sdeData` transports the identity through the càdlàg
  representative (`Ito/ItoLevyBoundedDerivsSolution.lean`), leaving the three derivative bounds
  as the only genuine narrowing against #16 (`tools/cited_axioms.md`, statement audit).
  **Stage 2 (B4-L5) route, refined 2026-09-11.** Apply M16 to `cutoffFun₂ u R` and transfer on
  the event the path stays in the ball of radius `R` up to `T` (`openExitTime`,
  `boundedPathSet`): endpoints and the drift integral by `driftIntegrand_cutoffFun₂`
  (`Ito/CutoffPathAgreement.lean`, B4-L2), the Brownian term by
  `stochasticIntegralBrownian_congr_of_le` (B4-L3). The jump terms do **not** transfer
  separately — `u(x + γ)` leaves the ball for large marks — but their *sum* does, at a mark set
  `A` of finite intensity: `stochasticIntegral_ae_eq_pathwise`
  (`Poisson/PathwiseIdentity.lean`) writes the compensated integral as the atom sum against
  `N` minus the intensity integral, so the sum of the compensated and compensator-drift terms
  reads `u` only at the realised path values `X_{s−}` and `X_{s−} + γ(s, X_{s−}, e)` and at
  `∇u(s, X_{s−})`. `Ito/AtomJumpRelation.lean` closes the three pieces that needed
  (2026-09-11/12, B4-L5a/b/c): the jump sum over the window is a step function of the arrival
  times (`ae_exists_atomEnum_jumpSumLeftAt_eq_sum`); a path that is a continuous process plus
  that jump sum jumps at each arrival time by exactly `γ(s, X_{s−}, e)`
  (`ae_exists_atomEnum_jump_eq_gamma`), so the shifted state reached at an atom is again a path
  value; and the compensated integral plus the compensator-drift term cancels the integrand's
  own intensity integral, leaving the atom values and the first-order correction
  (`stochasticIntegral_add_setIntegral_sub_eq_pathwise_sub`); and hence the cut-off transfers on
  the jump side along a confined path (`Ito/CutoffPathAgreement.lean`,
  `ae_setIntegral_jumpIncrement_cutoffFun₂_eq` for the atom values and
  `gradient_cutoffFun₂_leftLim_eq_of_boundedPath` for the first-order term), with no bound on the
  jump coefficient. **Correction (2026-09-15): B4-L5 is not assembly only.**
  `ae_jumpSide_cutoffFun₂_eq` (`Ito/CutoffJumpTransfer.lean`, B4-L5h) is conditional on
  `hsplit`: at every level `j` of `spanningSets ν`, `X` is a continuous process plus the
  left-limit jump sum over that level. The splitting lemma
  (`ae_forall_eq_add_jumpSumLeftAt_of_path`) discharges that only for the truncated path — it
  needs `γ` supported in the mark set — and not for `X`, whose remainder carries the jumps
  outside the level. Behind `hsplit` is the jump relation `X_θ = X_{θ−} + γ(θ, X_{θ−}, ε)` at
  the atoms of a finite-intensity mark set, which is **unproved for `X`** (gap G; route:
  `Poisson/CompensatedCadlagMod.lean` + `Probability/DoobContinuous.lean`). Order of work:
  Z1a (delete the unprovable axiom, re-point its consumers at the bounded-derivative theorem
  under a name that says so, keep #16 open), M1 (gap G, remove `hsplit`), M2 (trade
  `hReg`/`hLip` for the `SdeData` energies; the point-value/left-limit and
  iterated/reference-intensity transfers, `Ito/JumpIntegrandLeftLim.lean`,
  `integral_window_eq_and_integrableOn`), M3 (assembly and exhaustion in `m`), M4 (close-out).
  The target statement with every hypothesis exposed is `tools/cited_axioms.md`, entry 16,
  "Stage-2 status (2026-09-15)".
  **Z1a and M1 done 2026-09-15**: the axiom is deleted (`Open #16`), and the jump relation at
  the arrival times is a theorem for a solution (`Ito/JumpSplittingRemainder.lean`,
  `ae_exists_atomEnum_jump_eq_gamma_of_sdeData`); `hsplit` is gone from the Stage-2 chain.
  **M2 (first half) done 2026-09-15**: `itoLevyFormula_jumpResidual_of_sdeData` takes joint
  measurability of the coefficients and the drift energy instead of `IsRegular`/`IsLipschitz`.
  **M2 (second half), M3 and M4 done 2026-09-15**: `itoLevyFormula_general`
  (`Ito/ItoLevyFormulaGeneral.lean`) is the target statement of `tools/cited_axioms.md` entry
  `Resolved #16` — no derivative bound, no Lipschitz or growth condition — over the three
  standard axioms; `Ito/JumpFormulaAssembled.lean` is deleted, the sorry baseline is empty, and
  the import contract and the dissertation forwarder Cu03 point at the general theorem.
  The papers' quadratic and bilinear Itô formulas in expectation form — `𝔼[X_T²]`, its
  `e^{βT}`-weighted form and `𝔼[X_T Y_T]` for Itô–Lévy processes over a Lévy driver under the
  `L²` hypotheses alone — are `Ito/SecondMoment.lean` (2026-09-11, D-Itô-E); the pathwise
  formula with local integrals stays open (Epic D). `Ito/StabilityEstimate.lean` applies the
  weighted identity: the difference of two such processes is one (`isItoLevyProcess_sub`), and
  one-sided Lipschitz coefficient bounds give `𝔼[|ΔX_T|²] ≤ e^{(2L + 2L²)T} 𝔼[|ΔX₀|²]` and
  pathwise-at-each-time uniqueness (2026-09-11, DE-5). This is the fixed-time `L²` estimate
  only; the supremum-in-time estimates the papers also use need Doob/BDG and are not proved.
  The Picard chain is complete since 2026-09-07 —
  `Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn` builds the solution window by
  window, glues the windows along `⌈t⌉₊`, and populates every field of `JumpDiffusion`. Two
  statement audits landed with it (uniqueness is relative to the filtration; the drift integral
  in `is_solution` needed parenthesising) — see `tools/cited_axioms.md` #12.
- **No live cited axiom** since 2026-09-15: #16 was deleted (unprovable as stated), and the
  general Itô–Lévy formula it stood for is the theorem `itoLevyFormula_general`
  (`tools/cited_axioms.md` entry `Resolved #16`).
- **6 of the 13 axioms gate the pinned dissertation surface** (the 21
  `import_contract.md` symbols), traced via `#print axioms`:
  **#5** `itoIsometry_brownian_unified_existence`,
  **#6** `itoIsometry_compensated_unified_existence`,
  **#15** `itoFormula_continuousSemimartingale_axiom`,
  **#16** `itoLevyFormula_jumpResidual_canonical_axiom`,
  **#9** `continuousBSDEJ_exists_unique`,
  **#10** `bsdej_path_regularity`.
  The other 6 (#2, #4, #13a, #13b, #17, #18) were cited results but **not**
  reached by the pinned surface (#2, #4, #17, #18 are theorems now).
- **#5/#6 are foundational**: the audit shows #15, #16, #9, #10 *already carry*
  #5/#6 transitively, so the Itô-formula and BSDE layers cannot go axiom-free
  until the L² integrals are built. Hence #5 → #6 first.
- Four-way invariant green; build = 2904 jobs.

## Cross-repo roadmap and an upstream discharge of #6 (2026-09-05)

The end-to-end program for the three papers now lives in
`../Dissertation/WORK_BREAKDOWN.md`; this file remains the route for the foundations
(its WP5–WP9 are Phase A/B here). Two facts it records that bear on this plan directly:

- **A2/#6 has a partial upstream discharge.** `raphaelrrcoelho/formal-mathfin`
  (`MathFin/Foundations/PoissonCompensatedIntegralL2*.lean`, Apache-2.0, sorry-free, build-audited)
  proves the compensated-Poisson isometry for simple integrands with `L²` closure and cites
  this repo's axiom #6 by name as the statement it proves. It does **not** build the process
  (the càdlàg conjunct — the exact residue named under A2 above) nor the CLM over the
  *predictable* `L²`, which it calls "a declared, deferred Summit". So the isometry conjunct
  can become a forwarder once the pins agree; the càdlàg build stays ours.
  **Done 2026-09-05 (as far as it goes):** formal-mathfin is a `lake require`; `Poisson/MathFinBridge.lean`
  maps our PRM to theirs (`toMathFin`, via the σ-algebra scattering theorem in
  `Poisson/IndependentScattering.lean`) and reads back `itoLevyIntegralL2_norm`. #6 stays an axiom: the
  density of progressively measurable integrands in their closure, the martingale conjuncts and the
  càdlàg modification are not upstream (see `tools/cited_axioms.md` #6).
- **Pins do not agree.** formal-mathfin is at Mathlib `81a5d257` (v4.32.0, 2026-07-13); this
  repo is at `0e208554` (v4.30.0-rc2), the Dissertation at `c5ea003` (v4.30.0), Prove2Me's
  default at `0df444a` (v4.33.1). Our `c5ea003` is a verified ancestor of `81a5d257`, 1,306
  commits back. The "No pin bump" rule below was written to protect the Dissertation build;
  consuming the discharge requires revisiting it deliberately (roadmap decision **D1**).

## Release-readiness tickets (2026-09-08)

The verification-integrity, CI, documentation-truth and API-hygiene findings of the 2026-09-08
external audits are ticketed in the Dissertation repo's `RELEASE_READINESS.md` (53 leaves, all
S; the `(S, L)` and `(S, D+L)` rows are this repo's). They add no theorem and sit outside the
phases below. The ones that change this repo's gates: `X1b`–`X1g` (`tools/lint.sh` must fail on
a failed audit, a missing name, a primed name, or any axiom off an allowlist), `X2f` (CI on every
branch), `X3a`–`X3d` (README/CLAUDE/PROVE2ME/cited_axioms counts and pins), `X4a`–`X4c`
(`picardMap` placeholder, the broken `examples/` library), `X6c` (file splits).

The 2026-09-08 architecture review's LevyStochCalc tickets are group `Z` of the Dissertation
repo's `ARCHITECTURE.md` (26 leaves, all S): the duplicated martingale identity (`Z1`), the five
generic `L²` facts the Poisson layer reaches into `Brownian/` for (`Z2`), the `ItoDensity` /
`CompensatedDensity` deduplication (`Z3`), the integrand bundles and an `Lp`-valued integral
map (`Z4`, `Z5`), a public SDE surface (`Z6`), hygiene (`Z7`), and the upstream pilot (`P8`).

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
- **Pin policy (decision D1, 2026-09-05):** both repos sit on Mathlib
  `81a5d257c8e410db227a6665ed08f64fea08e997` / Lean `v4.32.0` — formal-mathfin's exact pin.
  A bump is a deliberate, cross-repo event: both repos together, the four-way invariant green
  before either commit, never incrementally. **Ponytail:** smallest diff, delete
  more than you add, one idea per file.

## Phase A — Close the 6 dissertation-surface axioms (critical path)

Bottom-up; each is a real `theorem` replacing its `axiom`, then drop from
`cited_axioms.md` + repoint consumers.

- [x] **A1 / #5** `itoIsometry_brownian_unified_existence` — **DONE 2026-06-17**
      (axiom→`theorem`; `cited_axioms.md` 13→12; `#print axioms` of it and its
      consumers `itoIsometry`/`quadVar_stochasticIntegral`/`martingale_stochasticIntegral`
      = the 3 standard only). `F := stochasticIntegralBrownian` on
      `(naturalFiltration W).rightCont`. Conjunct 2 (the quadVar martingale) was the
      gap: closed via the set-level Itô isometry at simple level
      (`simpleIntegral_sub_eq_clamp_sum` → `offDiagonal_increment_integral_zero_weighted`
      → `simpleIntegral_sub_sq_bochner_clamped_weighted`) + real clamped compensator
      (`setIntegral_eval_sq_Icc_clamped`) → simple-level quadVar martingale
      (`martingale_simpleIntegral_sq_sub_compensator`) → compensator `L¹`-convergence
      (`masterApprox_compensator_tendsto_L1`) → conjunct 2 on naturalFiltration
      (`martingale_quadVar_stochasticIntegralBrownian`) then `rightCont`
      (`martingale_rightCont_quadVar_stochasticIntegralBrownian`).
- [x] **A2 / #6** `itoIsometry_compensated_unified_existence` — **DONE 2026-09-06**
      (axiom→theorem; cited_axioms.md 10→9). Compensated-Poisson analogue of A1
      (Applebaum 4.2.3/4.2.4), built in stages below; the assembly is in
      `Poisson/Compensated.lean`: `stochasticIntegral` is now the càdlàg adapted
      modification (`exists_cadlag_modification`, from the Layer-0.5 brick applied to
      `martingale_rightCont_process`, `process_eLpNorm_two_right_tendsto`,
      `process_ae_zero_of_nonpos`) of the `L²` integral process `process`; the four
      conjuncts transfer along `stochasticIntegral_ae_eq_process`
      (`martingale_stochasticIntegral_rightCont`,
      `martingale_quadVar_stochasticIntegral_rightCont`, `isometry_stochasticIntegral`,
      `stochasticIntegral_cadlag`). The statement, the name and the signature of
      `stochasticIntegral` are unchanged; the consumers `itoLevyIsometry`,
      `quadVar_stochasticIntegral`, `martingale_stochasticIntegral`,
      `cadlag_modification_exists` now forward to the construction.
      - *Density layer (`Poisson/CompensatedDensity.lean`) — DONE 2026-06-17.* The
        analogue of Brownian `ItoDensity`. Time-discretisation (`dyadicEvalShifted`,
        adapted, → φ in L²) **plus** the genuinely new mark-space piece kept fully
        **general in `E`** (no countable-generation/standard-Borel): rectangle-simple
        functions `∑ cⱼ 𝟙_{Aⱼ×ˢBⱼ}` are dense in `L²(μ)` on `Ω × E` via monotone-class
        over the product π-system — `rectApprox_indicator` → `rectApprox_indicator_const`
        / `RectApprox.const_smul` → `rectSimple_dense_L2` (`MemLp.induction_dense`) →
        `rectSimple_L2_tendsto` (convergent sequence).
      - *Step-integral foundation (`CompensatedDensity.lean`) — DONE 2026-06-17.*
        `SimplePredictable` carries one mark set `Aᵢ`+coefficient `ξᵢ` per (strictly
        increasing) time-piece, so its `eval` is rank-1 in the mark on each interval and
        cannot represent `∑ⱼ ξⱼ(ω)𝟙_{Bⱼ}(e)`. The mark-discretised approximant is a
        **finite sum** of pieces, captured by `stepIntegral N (Φ : Fin k → SimplePredictable)
        = ∑ⱼ simpleIntegral N (Φ j)` — proved `martingale_stepIntegral_compensated`
        (sum of per-piece martingales), `stepIntegral_zero`, `stepIntegral_memLp_compensated`
        (all by reusing the proven `CompensatedMartingale`/`CompensatedIsometry` lemmas
        untouched). The bilinear isometry's cross terms vanish on disjoint sets:
        `compensated_cross_disjoint_zero` (`E[Ñ(B)Ñ(B')]=0` for `Disjoint B B'`, via the
        PRM `independent_disjoint` field + `compensated_mean_zero`).
      - *Covariance + cross-term theory (`CompensatedDensity.lean`) — DONE 2026-06-17.*
        All atomic lemmas for the multi-mark isometry are proved, and **no strengthening
        of the per-box past/future independence (cited axiom #2) is needed**: the same-time
        disjoint-mark weighted cross term is killed by polarising through the union box.
        Bricks: `compensated_cross_disjoint_zero`, `compensated_diff_sq_disjoint`,
        `compensated_inter_add_diff_ae`, `compensated_diff_sq_expand`,
        `compensated_cross_covariance` (`E[Ñ(B)Ñ(B')]=ν̂(B∩B')`),
        `weighted_box_sq_eq` (`E[g·Ñ(box)²]=E[g]·ν̂(box)`),
        `weighted_box_cross_disjoint_zero` (`E[g·Ñ(R)Ñ(R')]=0`, same-time disjoint marks).
        Decision: **multi-mark** design (per user) — K disjoint mark-sets per shared
        time-partition; isometry = ∑ₖ per-mark isometry (cross-mark terms vanish: same-time
        via `weighted_box_cross_disjoint_zero`, time-ordered via the off-diagonal arg).
      - *Cross-φ bilinear vanishing — DONE 2026-06-17.* `weighted_box_sq_eq` (weighted
        future-box 2nd moment), `weighted_box_cross_disjoint_zero` (same-time disjoint
        marks), `weighted_box_cross_timeordered_zero` (time-ordered, weight adapted to the
        later interval's start), and `crossSum_disjointMark_zero`
        (`E[(∑ᵢ ξᵢ Ñ((pᵢ,pᵢ₊₁]×Aᵢ))·(∑ⱼ ξ'ⱼ Ñ((pⱼ,pⱼ₊₁]×A'ⱼ))]=0` for a shared partition
        and disjoint marks). All atomic isometry content for the multi-mark design is now
        proved, structure-free, using only the existing per-box independence.
      - *Multi-mark isometry — DONE 2026-06-17.* `stepIntegral_multimark_isometry`:
        `E[(∑ₖ∑ᵢ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = ∑ₖ∑ᵢ ν̂((pᵢ,pᵢ₊₁]×Bₖ)·E[ξᵢₖ²]` for a shared
        partition, pairwise-disjoint marks, adapted bounded coeffs. Builds the single-mark
        `SimplePredictable` per mark, expands at the `k`-level, diagonal via
        `simpleIntegral_L2_isometry_compensatedPoisson_sumForm`, cross via
        `crossSum_disjointMark_zero`. **The full isometry conjunct for general (rank->1)
        integrands is now proved** — no axiom strengthening, mark space `E` fully general.
      - *Overlapping-mark route enabled — 2026-06-17.* To avoid disjointifying the marks of
        integrand *differences* in `masterApprox`, the same-time bilinear covariance is now
        weighted: `weighted_box_diff_sq_disjoint` and `weighted_box_cross_sametime`
        (`E[g·Ñ((a,b]×A)·Ñ((a,b]×A')] = E[g]·ν̂((a,b]×(A∩A'))`, arbitrary marks). With these
        + `weighted_box_cross_timeordered_zero`, the **overlapping-mark** step-integral
        isometry `E[(stepIntegral)²] = E[∫∫ integrand²]` holds for any marks (the cleanest
        Cauchy input). **Both isometry routes are now fully supported** (disjoint capstone
        `stepIntegral_multimark_isometry`, and the overlapping bilinear pieces).
      - *Overlapping-mark isometry + Tonelli bridge — DONE 2026-06-17.* The textbook
        isometry `markSumProcess_isometry_L2`:
        `E[(∑ᵢ∑ₖ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = E[∫_E∫_{[0,T]} eval² ds dν]` for **arbitrary
        (overlapping) marks**, via `markSumProcess_isometry` (LHS = sum-form) and
        `markSumProcess_L2_eq` (RHS = sum-form, Tonelli of `timeIndicator_sq_integral` ×
        `mark_sq_integral` + `referenceIntensity_Ioc_prod_eq`). **The entire isometry
        conjunct for general integrands is proved**, no axiom strengthening, `E` general.
      - *masterApprox **density** — DONE 2026-06-18.* The adapted step (Euler) approximants
        are `L²(P⊗vol⊗ν)`-dense in `φ`: `exists_markEval_L2_tendsto`. Built bottom-up:
        `lintegral_prod_trim_left` (trim–product bridge) + `IsRectSimple.eq_finSum` →
        `exists_markSimple_adapted_within` (per-time-piece mark discretisation at the
        sub-σ-algebra `ℱ_{pᵢ}`, forcing **adapted** rectangle sides via `Measure.trim`);
        `dyadicAvg_shifted_adapted_prod` (mark-joint adaptedness of the shifted average);
        `sq_nnnorm_disjoint_indicator_sum` (disjoint-interval collapse) →
        `exists_markEval_close_dyadic` (mark-half within `T·δ`); diagonalised against the
        time-half (`dyadicEvalShifted_L2_tendsto`) via `sq_nnnorm_add_le_two_mul` +
        `lintegral_triple_add`/`_const_mul` + squeeze. **Mark space `E` fully general** (no
        countable-generation). This was the sole analytical gate for dissertation #2(B).
      - *Cross-resolution diff isometry — DONE 2026-06-19.* The full chain making the Euler
        integrals `L²(P)`-Cauchy: mark collection to shared `Fin K`
        (`exists_sharedMark_blockDiag`) → per-resolution isometry (`markStepIntegral_isometry`)
        and same-partition diff isometry (`markStepIntegral_diff_isometry`, via `Fin.append`);
        dyadic refinement (`compensated_Ioc_split`/`_telescope`, `indicator_Ioc_telescope`,
        `dyadic_sum_split`, `dyadicCoarse`, `dyadic_point_coarse`, `dyadic_fine_endpoints`,
        `dyadic_indicator_refine`/`dyadic_compensated_refine`,
        `stepIntegral_dyadic_refine_integral`/`_eval`, `dyadic_coarse_point_le`,
        `dyadic_refine_adapted`) → **`stepIntegral_crossres_diff_isometry`**:
        `‖Iₙ−Iₘ‖²_{L²(P)} = ‖evalₙ−evalₘ‖²_{L²(P⊗vol⊗ν)}` for any dyadic levels `n ≤ m`.
        Plus `L²`-membership of the Euler integral (`compensated_memLp`, `memLp_bdd_mul`,
        `eulerStepIntegral_memLp`). **The entire novel content of #2(B) and #6's isometry
        conjunct is formalised.**
      - *Dissertation #2(B) — DONE 2026-06-19.* **`compensated_eulerSum_L2_limit`**: the
        adapted Euler step integrals converge in `L²(P)` to an `L²` limit `F` (the L²-Itô-Lévy
        integral). Final assembly: `lintegral_sq_eq_ofReal_integral` +
        `triple_ofReal_integral_eq_lintegral` (real↔`ℝ≥0∞` bridges) + `eulerStepIntegral_memLp`
        + `eulerStepIntegral_cauchy_le` (`‖Iₘ−Iₙ‖² ≤ 2Aφₘ+2Aφₙ` via the crossres diff isometry
        + triple bridge + Tonelli swap + `2(a²+b²)` triangle) + `eLpNorm_two_rpow_eq_lintegral_sq`
        + `EMetric.cauchySeq_iff` (`δ=ε²/4`) + `exists_L2_limit_of_memLp_cauchySeq`. The
        dissertation's Euler-sum → stochastic-integral identification is formalised.
      - *Remaining for #6 (drop the axiom): the process + càdlàg.* `compensated_eulerSum_L2_limit`
        builds the integral at a fixed horizon as an `L²` RV; #6's `axiom` is the whole process
        `F : ℝ → Ω → ℝ` with martingale + quadVar-martingale + isometry + **càdlàg** on
        `(naturalFiltration N).rightCont`. The martingale/quadVar/isometry conjuncts mirror #5
        (per-`t` limit of `martingale_stepIntegral_compensated`); the **càdlàg** conjunct needs
        continuous-time Doob `L²` regularization — *not in Mathlib*, only the discrete bricks
        `martingale_norm_submartingale`/`_tail_maximal` exist. **#6 stays an axiom until the Doob
        càdlàg build lands** (a separate sizeable project).
      - *Càdlàg brick — DONE 2026-09-06* (`Martingale/CadlagModification.lean`). Instead of a
        Doob build, the `brownian-motion` dependency's right-limit regularisation of real
        quasimartingales (`rightContModif`, `cadlagModif`; sorry-free at the pinned rev) is
        used: `isRealQuasimartingale` (a martingale is a quasimartingale — fills the
        upstream `sorry` of the same statement), `exists_adapted_ae_isCadlag_nnreal`
        (`ℝ≥0` index), and `exists_adapted_ae_cadlag(_of_eLpNorm)` (`ℝ` index, via
        `restrictNNReal` and zero-extension to negative times): a martingale on a
        right-continuous filtration, right-`L²`-continuous in time and null at negative
        times, has an adapted modification with a.s. càdlàg paths, in exactly the form of
        #6's fourth conjunct. Remaining for #6: the process construction (mirror of #5:
        master approximants across horizons from `exists_markEval_L2_tendsto` +
        truncation, `Filter.limUnder`, martingale/quadVar/isometry conjuncts), then feed
        `martingale_rightCont_of_tendsto_eLpNorm_one` and this brick.
      - *Mark-step calculus — DONE 2026-09-06* (`Poisson/MarkStep.lean`). The simple class for
        the process construction: `TimeGrid` (finite time grid) and `MarkStep g` (shared
        marks, bounded coefficients) with `integral` (compensated integral up to `t`),
        `full`, `eval`, `Adapted`; martingale property and `L²` membership (through
        `stepIntegral`); the isometry at every time `t ≥ 0` (`integral_sq_at`,
        `lintegral_integral_sq_at`) via the clamped grid `TimeGrid.clamp`; sums/negation on
        a common grid and the difference isometry (`lintegral_integral_sub_sq_at`); the
        set-level increment isometry between grid points against an earlier-measurable
        weight (`integral_weight_increment_sq`, the input for the quadratic-variation
        conjunct); dyadic grids with refinement (`full_dyadicRefine`) and prefix
        restriction (`full_dyadicRestrict`).
      - *Master approximating sequence — DONE 2026-09-06* (`Poisson/CompensatedApprox.lean`).
        `truncate` (clip + finite-measure mark restriction, with joint/progressive
        measurability) and `exists_truncate_close`; `exists_markStep_close`: for a
        square-integrable progressively measurable `φ`, an adapted mark-step integrand on a
        dyadic grid of any prescribed minimal level within `ε` of `φ` on `[0, T]`. The
        master sequence `master n` (horizon `2ⁿ`, levels increasing by at least one per
        stage, error `< (n+1)⁻¹`), `stageIntegral` (martingale, `L²`), and the Cauchy
        bound `stageIntegral_sub_sq_le`: for `n ≤ n'` and `t ≤ 2ⁿ`,
        `E|Iₙ(t) − Iₙ'(t)|² ≤ 2(n+1)⁻¹ + 2(n'+1)⁻¹` (restrict the later stage to `[0, 2ⁿ]`,
        refine the earlier one, difference isometry, martingale monotonicity of
        `E|M_t|²`).
      - *The `L²` process — DONE 2026-09-06* (`Poisson/CompensatedProcess.lean`). `process`
        is the `ℱ_t`-measurable representative of `processLp t := limUnder` of the stage
        integrals in `L²(P)` (`lpMeas` closedness); `martingale_process` (natural
        filtration), `process_ae_zero_of_nonpos`, `process_lintegral_sq'` (the isometry
        `∫⁻‖F_t‖² = ∫⁻∫⁻_{[0,t]}∫⁻‖φ‖²` at every `t ≥ 0`, through the product measure
        `P ⊗ ν ⊗ vol|[0,t]`), `process_eLpNorm_two_right_tendsto` (right-`L²`-continuity,
        from the martingale Pythagoras identity and right-continuity of the horizon
        integral `horizonInt`), and `martingale_rightCont_process` on
        `(naturalFiltration N).rightCont`. This is conjuncts 1 and 3 of #6 for the
        constructed process.
      - *Conjunct 2 at stage level — DONE 2026-09-06* (`Martingale/SquareCompensator.lean`,
        `Poisson/CompensatedQuadVar.lean`, increment section of `Poisson/MarkStep.lean`).
        `martingale_sq_sub_of_setIntegral` is the generic brick: for a square-integrable
        martingale `M` and adapted integrable `A`, `M² − A` is a martingale as soon as
        `∫_B (M_t − M_s)² = ∫_B (A_t − A_s)` for `B ∈ ℱ_s`. For a mark-step integrand `G`,
        `compensator t := ∫_{[0,t]} ∫_E G(u,e)² ν(de) du` is bounded, integrable and
        `ℱ_t`-measurable (`compensator_stronglyMeasurable`, via the clamped integrand
        viewed as a `MarkStep` over `ℱ_t`); the set-level identity
        `setIntegral_increment_sq_eq` comes from the weighted increment isometries
        `integral_weight_incr_sq` (`0 < s < t`, increment grid `TimeGrid.incr`) and
        `integral_weight_zero_sq` (`s ≤ 0 < t`) with the indicator of `B` as weight, plus
        Fubini in `(u, e)`. `martingale_sq_sub_compensator`: `I_G(t)² − A_G(t)` is a
        natural-filtration martingale.
      - *Conjunct 2 for the process — DONE 2026-09-06*
        (`Poisson/CompensatedProcessQuadVar.lean`). The compensator
        `compensator ν φ t := ∫_{[0,t]} ∫_E φ(u,e)² ν(de) du` is adapted (progressive
        measurability through `prodAssoc` and two parametrised Bochner integrals) and
        integrable (square-integrability of `φ` for the horizon measure
        `P ⊗ vol|[0,t] ⊗ ν`); the stage integrands converge to `φ` in `L²` of the horizon
        measure (`stageEval_tendsto`, from `master_err`), so their squares converge in
        `L¹` and the stage compensators converge in `L¹(P)` to the compensator
        (`stage_compensator_tendsto_L1`). `martingale_quadVar_process` (natural filtration,
        via `martingale_of_tendsto_eLpNorm_one`) and `martingale_rightCont_quadVar_process`
        (right-`L¹`-continuity of `F²` and of the compensator, the latter from the slab
        integral `∫⁻∫⁻_{(s,r]} markSq → 0`).
      - *Assembly — DONE 2026-09-06* (see the head of this item).
- [x] **A3 / #17** `itoIsometry_diff_brownian` — **DONE 2026-06-17** (axiom→theorem;
      cited_axioms.md 12→11). Required redefining `stochasticIntegral :=
      stochasticIntegralBrownian` (genuine construction, not `Classical.choose`),
      then `isometry_diff_stochasticIntegralBrownian` (cross-integrand simple diff
      isometry + L²-limit). **#18** `itoIsometry_diff_compensated` — **DONE 2026-09-06**
      (axiom→theorem; cited_axioms.md 9→8): `process_sub_lintegral_sq`
      (`Poisson/CompensatedDiff.lean`) refines the stage approximants of the two
      integrands to a common dyadic grid (`MarkStep.integral_dyadicRefine`, from the
      martingale property at the common horizon), applies the same-grid difference
      isometry at every time, and passes both sides to the `L²`-limit; the integrals are
      modifications of the processes.
- [x] **A4 / #15** `itoFormula_continuousSemimartingale_axiom` — **RETIRED 2026-09-06**
      (cited_axioms.md 7→6). Statement audit: the Lean statement was an unconstrained
      existential `∃ R, …`, satisfied by the trivial residual, so it carried none of
      KS 3.3.6's content; it was not discharged by that witness. Instead
      `itoLevyFormula` is now derived from #16 alone (the canonical-residual identity
      rearranged) and the axiom was deleted. The continuous Itô formula (KS 3.3.6) is
      part of A5's content. Candidate route for it: `formal-mathfin`'s
      `ito_formula_td_L2_bddDeriv` / `ito_formula_td_process` (time-dependent,
      one-dimensional, over `IsPreBrownianReal` and its `L²` Itô integral; sorry-free)
      through a Brownian bridge `BrownianMotion → IsPreBrownianReal` and an integral
      bridge to `stochasticIntegralBrownian`, extended to `d` coordinates and to Itô
      processes; the jump part (Applebaum 4.4.10 + 4.4.7 (II)) in-house on
      `Compensated.stochasticIntegral`.
- [x] **A5 route notes 2026-09-08** (B0a and B0b landed 2026-09-09; #16 closed 2026-09-15) —
      an external review of the #16 programme was checked and
      ticketed in `../Dissertation/WORK_BREAKDOWN.md` Epic B (review notes; new leaves `B0a`,
      the decomposition-based statement `X = X₀ + ∫b + ∫σ dW + ∫γ dÑ` with the SDE form as a
      corollary, and `B0b`, the `X_{s−}` convention justified by the `L²` class argument rather
      than the `Ñ ⊗ P`-null claim in `Ito/Setting.lean`). Epic B does not depend on the PRP.
- [x] **A5-0 / #16 statement audit** — DONE 2026-09-06: added `hu : ContDiff ℝ 2 (uncurry u)`
      and `h_μ_int` (drift integrable on `[0, T]` along the path) to the axiom, its two derived
      theorems and the dissertation forwarder; without them the statement was refutable
      (indicator `u` along `W`; `u = t·x` with `μ = 1/s`). Recorded the single-driver
      filtration scope of the whole SDE layer (`cited_axioms.md` #16 "Scope").
- [x] **X2 — rebuild the interface of the `L²` integrals: genuine progressive measurability
      over a common filtration** (new, 2026-09-06; blocks A5–A7 and B4/B5). Two defects,
      fixed together: (i) the hypothesis `h_progMeas : ∀ t, StronglyMeasurable[ℱ t ⊗ Borel]
      (uncurry H)` has no `s ≤ t` restriction, so (`ℱ 0` being P-trivial) every admissible
      integrand is a.s. constant in `ω` at each time — the library's integrals are Wiener
      integrals of deterministic integrands (`tools/cited_axioms.md`, "Integrand-class
      audit"); the fix is Mathlib's `IsStronglyProgressive` (`Set.Iic t × Ω`), and every proof
      that silently used the over-strength must be repaired; (ii) today
      `MultidimBrownianMotion.stochasticIntegral` needs `H_j` progressive for
      `naturalFiltration (W.W j)` and `Compensated.stochasticIntegral` for `naturalFiltration N`.
      Stages:
      - [x] **X2-0 foundation** (2026-09-06): `Probability/IndepLimit.lean` (a σ-algebra
            independent of each term of an a.e.-convergent sequence is independent of the
            limit, via bounded continuous test functions), `Probability/IndepJoin.lean`
            (`m₁ ⟂ m₃` and `m₂ ⟂ m₁ ⊔ m₃` give `m₁ ⊔ m₂ ⟂ m₃`), `Brownian/Filtered.lean`
            (`IsBrownianFiltration W ℱ`: adapted + increments after `s` independent of `ℱ s`;
            instances: the natural filtration, any smaller adapted filtration, `ℱ₊`),
            `Poisson/Filtered.lean` (`IsPoissonFiltration N ℱ`, same three instances),
            `Driver/Joint.lean` (`LevyDriver`: `W`, `N` with `σ(W) ⟂ σ(N)`; its joint natural
            filtration `(⨆ i, ℱ^{Wⁱ}) ⊔ ℱ^N` is Brownian for every coordinate and Poisson
            for `N`). Axiom set: the 3 standard.
      - [x] **X2-1 Brownian chain** (2026-09-06). `Probability/Progressive.lean` defines
            `ProgressivelyMeasurable ℱ H` (`(ω, s) ↦ 1_{s ≤ t} H ω s` is `ℱ t ⊗ Borel`-measurable
            for every `t`; equivalent to Mathlib's `IsStronglyProgressive` in both directions;
            adaptedness, continuous images fixing `0`, and `ℱ t`-measurability of
            `∫_S H ω s ds` for `S ⊆ (-∞, t]`). `ItoSimple` → `ItoDensity` → `ItoMartingale` →
            `SimplePredictableRefine` → `ItoL2Completion` → `MultidimIto` now take
            `(ℱ, hℱ : IsBrownianFiltration W ℱ)` and `h_progMeas : ProgressivelyMeasurable ℱ H`
            (one `ℱ` for all coordinates in `MultidimIto`); the adaptedness-only lemmas (density
            of adapted simple processes, `masterApprox`) no longer mention `W`. The
            natural-filtration bricks are replaced by the conditional expectation of an increment
            given a σ-algebra independent of it (`condExp_increment_eq_zero_of_indep`) and
            `IsBrownianFiltration.condExp_eq` (`E[W_t | ℱ s] = W_s`).
            `Brownian/MultidimFiltered.lean`: the joint natural filtration `W.naturalFiltration`
            of a multidimensional Brownian motion is Brownian for every coordinate
            (`isBrownianFiltration_natural`, through `IsBrownianFiltration.of_le_sup`), and
            `LevyDriver.isBrownianFiltration` is now derived from it. The consumers
            (`Ito/Setting`, `Ito/Picard`, `Ito/JumpFormula`, `BSDEJ/Definition`, the
            dissertation's Cu03) pass `W.naturalFiltration`; their Poisson integrands still use
            `naturalFiltration N` (X2-2), so the common filtration of `(W, N)` is X2-3. Axiom
            set: the 3 standard.
      - [x] **X2-2 Poisson chain** (2026-09-06). `MarkedProgressivelyMeasurable ℱ φ`
            (`Probability/Progressive.lean`: `(ω, s, e) ↦ 1_{s ≤ t} φ ω s e` is
            `ℱ t ⊗ Borel ⊗ 𝓔`-measurable for every `t`; continuous images fixing `0`,
            restriction of the marks to a measurable set, `ℱ t ⊗ 𝓔`-measurability of
            `∫_S φ ds` and `ℱ t`-measurability of `∫_S ∫_E φ dν ds` for `S ⊆ (-∞, t]`).
            `CompensatedIsometry` → `CompensatedMartingale` → `CompensatedDensity` → `MarkStep` →
            `CompensatedApprox` → `CompensatedProcess` → `CompensatedQuadVar` →
            `CompensatedProcessQuadVar` → `CompensatedDiff` → `Compensated` → `L2Isometry` now
            take `(ℱ, hℱ : IsPoissonFiltration N ℱ)` and
            `h_progMeas : MarkedProgressivelyMeasurable ℱ φ`; the past-measurability and the
            future-independence of `N` enter only through `hℱ.measurable` and `hℱ.indep`, and
            `MarkStep.Adapted ℱ G` replaces `MarkStep.Adapted N G`. The consumers pass
            `naturalFiltration N` for the Poisson integrands and `W.naturalFiltration` for the
            Brownian ones; the common filtration of `(W, N)` is X2-3. Axiom set: the 3 standard.
      - [x] **X2-3 consumers** (2026-09-06). Every consumer now carries ONE filtration `ℱ`
            together with the two driver properties, so the diffusion and jump integrands are
            progressive for the same `ℱ` and coupled `(σ, γ)` are in scope.
            `Ito/Setting.is_solution` opens with
            `∃ ℱ, (∀ j, IsBrownianFiltration (W.W j) ℱ) ∧ IsPoissonFiltration N ℱ ∧ …` and both
            coefficient bundles are progressive for that `ℱ`; `Ito/JumpFormula` (#16 and its two
            derived theorems), `Ito/Picard*` and `BSDEJ/Definition.IsBSDEJSolution` (over `ℱ₊`,
            with `ℱ` and the two properties existentially bound) take `(ℱ, hℱW, hℱN)` the same
            way. #13b (`BSDEJ/MartingaleRepresentation`) is stated over a `LevyDriver D` and its
            `D.filtration.rightCont`, which also supplies the `σ(W) ⟂ σ(N)` hypothesis its
            `M₀ = 𝔼 ξ` clause needs. A `LevyDriver` is *not* required elsewhere: an arbitrary
            common `ℱ` is the weaker (so more general) hypothesis, and X2-4 supplies the witness
            that the conjunction is satisfiable. #9, #10, #13a stay deleted (A5-1) and return as
            statements to prove, not axioms. Axiom set: the 3 standard.
      - [x] **X2-4 non-vacuity** (2026-09-06). `Probability/Transport.lean`: independence of
            σ-algebras, of a pair and of a family of random variables transports backwards
            along a measure-preserving map (the two `private` copies in `Brownian/Multidim.lean`
            were deleted in favour of it). `Brownian/Transport.lean` and
            `Poisson/Transport.lean`: `W` and `N` pulled back along such a map are again a
            Brownian motion, a `d`-dimensional Brownian motion and a Poisson random measure.
            `Driver/Existence.lean`: on `Ω₁ × Ω₂` with `P₁.prod P₂` both projections are
            measure preserving, `σ(W)` factors through the first coordinate and `σ(N)` through
            the second, and the coordinates are independent (`indepFun_prod`), so
            `LevyDriver.exists` holds for every `d` and every σ-finite `ν` on a standard Borel
            space. `exists_isBrownianFiltration_and_isPoissonFiltration` states the consequence
            the SDE/BSDEJ layer needs: a filtration carrying both driver properties exists.
            This is *satisfiability of the filtration hypothesis*, not existence of solutions —
            SDE/BSDEJ existence is A6/A7. Axiom set: the 3 standard.
      - [x] **X2-5** (2026-09-06) dissertation forwarders (Cu03 takes `(ℱ, hℱW, hℱN)`; I02 keeps
            `naturalFiltration N`, the right filtration for the Poisson-only isometry), import
            contract re-verified (12 modules + 19 symbols), ledgers updated in both repos.
- [x] **A5 / #16** `itoLevyFormula_jumpResidual_canonical_axiom` — Itô–Lévy jump
      residual (Applebaum 4.4.10 + 4.4.7), on A2/A4 and X2. Axiom deleted 2026-09-15 (Z1a);
      the general statement proved the same day as `itoLevyFormula_general`
      (`Ito/ItoLevyFormulaGeneral.lean`, M1–M4; `tools/cited_axioms.md` entry `Resolved #16`).
- [x] **A6-0 / #9 statement audit** — RETIRED 2026-09-06 (refutable: arbitrary non-adapted
      `X`; single-driver integrand class); the axiom and the dissertation forwarder Cu01 were
      deleted. **A6** becomes: after X2, state and prove BSDEJ existence/uniqueness over the
      joint filtration via the Picard chain (Tang–Li 1994 / AGPP 2025). The Picard chain's
      last `sorry` was discharged 2026-09-07 with #12/#14 (`ba5e214`), so A6 is now the BSDEJ
      existence statement alone.
      **A6-1 statement narrowing done 2026-09-06**: the four theorems of the chain asserted a
      solution for an arbitrary `(W, N)`; since X2-3 that is false for a dependent pair (no
      filtration carries both driver properties — see `tools/cited_axioms.md`, Retired #14,
      statement audit), so the `sorry` was undischargeable as stated. All four now take
      `(ℱ, hℱW, hℱN)`. What remains for A6 is the analytic chain itself.
      **A6 planned 2026-09-15** (`../Dissertation/WORK_BREAKDOWN.md`, "Epic A6", 21 leaves): over
      `Brownian.augFiltration D.filtration P` via the joint PRP and the weighted second-moment
      identity (no Itô formula, no Grönwall); two statement defects to fix first — `Lipschitz`'s
      `.toReal` (D1) and the product-σ-algebra `f_measurable` field, which forces `f` constant
      in `u` for atomless `ν` (D2) — and a driver-pinned `SolvesBSDEJ` for uniqueness (D4).
      **Waves 0–1 landed 2026-09-15** (L01–L07): D1 and D2 fixed (`BSDEJ/Existence.lean`,
      `BSDEJ/Definition.lean`, degeneracy theorem `BSDEJ/GeneratorDegeneracy.lean`), `SolvesBSDEJ`
      (`BSDEJ/Solves.lean`), marked-progressive slices, usual conditions for the augmented joint
      filtration at `t = 0`, the everywhere-càdlàg vector Brownian integral, both legs vanishing
      at `t ≤ 0`. **Waves 3–5 (same day):** L08 integrand dictionary, L09 `S²` bound, L10a the
      generator along a mark-step integrand (Carathéodory), L11 its energy bound, L15 the backward
      weighted inequality, L16 Young + Lipschitz and the factor `1/4`, L10b the progressive
      modification of the generator along a process (`BSDEJ/GeneratorModification.lean`), L12 and
      L13a–d the terminal datum, the càdlàg legs, the drift leg and the assembled Picard step
      (`BSDEJ/PicardStep.lean`: `PicardOutput`, `exists_picardOutput`; `SolvesBSDEJ` gained the `S²`
      field), L14 locality after the horizon and the Itô–Lévy structure of the frozen output
      (`BSDEJ/PicardItoLevy.lean`), L13e the step with a drift progressive for the right-continuous
      filtration, L17 the contraction of factor `1/4` in the weighted norm
      (`BSDEJ/PicardContraction.lean`). **Closed 2026-09-15** (L10c, L18–L21): the modification
      progressive for the filtration itself (`BSDEJ/DriftModification.lean`, Lebesgue
      differentiation from the left), uniqueness (`BSDEJ/Uniqueness.lean`, `SolvesBSDEJ.unique`),
      the iterates and their geometric Cauchy bound (`BSDEJ/PicardIterates.lean`), the limit and
      the fixed point (`BSDEJ/PicardLimit.lean`, `exists_solvesBSDEJ`), the headline
      `exists_unique_solvesBSDEJ` (`BSDEJ/ExistenceUniqueness.lean`) and the bridge
      `isBSDEJSolution_of_solvesBSDEJ` (`BSDEJ/Bridge.lean`; proving it exposed and fixed finding
      D3, the mis-parenthesised equation conjunct of `IsBSDEJSolution`). Ledger entry
      `Resolved #9`. Not done: a non-vacuity witness with `f ≠ 0` (`GOAL.md` §1.B), the
      forward-coupled generator (A7's business).
- [x] **A7-0 / #10 statement audit** — RETIRED 2026-09-06 (refutable: the `C·Δt` rate for
      merely measurable `g`, `X`; `1_{W_T>0}` has rate `Δt^{1/2}`); the axiom, its two
      corollaries, the dissertation forwarder Cu05 and the dissertation's bridge section were
      deleted. **A7** becomes: after A6, state and prove Bouchard–Elie path regularity with its
      regularity hypotheses (Lipschitz `g`, Lipschitz jump diffusion `X`).
      **Scoped 2026-09-15 — deferred.** The cited proof is Malliavin-based and every literature
      route needs a differentiable dependence on the state; blockers: a generator reading the
      forward process (L), a flow `X^{t,x}` with the Markov property (XL), the flow derivative or
      a Malliavin calculus (XL), and the scheme error the dissertation actually consumes (XL).
      Reachable now: A7′ — for a generator not reading `X` and a solution with deterministic
      Lipschitz `Z = h(s)`, the rate `E∫|Z − Z̄^π|² ≤ (K δ)² T`; the deterministic half is
      `energy_sub_cellTimeAverage_le_of_lipschitz` (`BSDEJ/CellAverageRate.lean`,
      2026-09-15) and the transfer to every solution of the `f = y` equation is
      `energy_sub_cellAverage_le_of_solvesBSDEJ` (`examples/NonvacuityBSDEJRate.lean`, same day;
      pathwise cell average, no stochastic content beyond uniqueness). Also reachable: the qualitative `E∫|Z − Z̄^π|² → 0` for every solution.
      Record in `tools/cited_axioms.md`, `Retired #10`, replacement plan.

## Phase B — Close the 7 off-critical-path axioms (breadth)

- [x] **B1 / #4** `brownian_martingale_rightCont` — **DONE 2026-09-06** (axiom→theorem;
      cited_axioms.md 8→7), without Blumenthal 0-1: the natural-filtration martingale
      (`brownian_martingale_natural`) lifts to `ℱ₊` by the generic right-`L¹`-continuity
      brick `martingale_rightCont_of_tendsto_eLpNorm_one` (moved from
      `Brownian/ItoL2Completion.lean` to `Martingale/RightCont.lean` so the Brownian
      layer can use it), the continuity coming from `𝔼|W_r − W_s|² = r − s`.
- [x] **B2 / #1** `BrownianMotion.exists` — closed 2026-09-05: `Brownian/Existence.lean`
      forwards to `isBrownianReal_brownian` (`RemyDegenne/brownian-motion` @ `4d52fa77`, a
      `lake require` since D1); real-time extension + weak Markov property for the
      σ-algebra field; `ULift` transport to `Type u`. Axiom set: the 3 standard.
- [x] **B3 / #2** `PoissonRandomMeasure.exists_of_sigmaFinite` — closed 2026-09-06 by the
      Poisson recipe (Applebaum 2.3.1 / Kallenberg 3.6), statement unchanged:
      - *S1 `Poisson/PoissonSplitting.lean`*: a Poisson(r) number `K` of iid marks with law
        `ρ`, independent of `K`, scattered over disjoint measurable `B₁, …, Bₙ`: the counts
        `∑_{j<K} 1_{Bᵢ}(Xⱼ)` are independent, `Poisson(r ρ(Bᵢ))` (characteristic functions:
        `E exp(i ∑ tᵢ Nᵢ) = ∑ₙ P(K=n) cⁿ`, the exponential series, `charFun_pi`,
        `Measure.ext_of_charFun`).
      - *S2/S3 `Poisson/PoissonSuperposition.lean`* (+ `Probability/IndepGrouping.lean`):
        pieces `(r p, ρ p)` on the product space `ι → ULift ℕ × (ℕ → 𝓧)` with
        `Measure.infinitePi`; `N := Measure.sum` of the atomic piece measures; mean
        `𝔼 N(B) = Λ(B)` (so a.s. finite on finite-intensity sets); Poisson law via the
        characteristic-function limit of the Poisson partial sums along a finset exhaustion
        of `ι`; a.s. `∞` on infinite-intensity sets since `Po(λ)([0,k]) → 0` as `λ → ∞`;
        independence on disjoint sets by `iIndepFun_uncurry'` + fibre grouping.
      - *S4 `Poisson/RandomMeasure.lean`*: cells `[n, n+1) × sₘ` of a σ-finite
        decomposition, index = cells of positive intensity (so no probability measure on
        `ℝ × E` is needed when `E` is empty), `ρ p := Λ|_{A p} / Λ(A p)`; the past/future
        σ-algebra field from `Poisson/RegionIndependence.lean` (the former
        `IndependentScattering.lean` argument over a raw random measure; that file now
        forwards). Axiom set: the 3 standard.
- [x] **B4 / #13b** `condExp_to_PRP_martingale_form` — **CLOSED 2026-09-06.** Doob L² càdlàg
      regularization (KS I.3.13) + Blumenthal 0-1, both built in-house.
      - [x] *Right `L²`-continuity of the conditional expectation* along a right-continuous
        filtration on `ℝ` (`Probability/CondExpRightContinuous.lean`,
        `tendsto_condExpL2_nhdsGT`), over `Probability/ProjectionLimit.lean`,
        `Probability/AEMeasurableInf.lean` and `Probability/CondExpInf.lean`. Axiom set:
        the 3 standard.
      - [x] *Blumenthal 0-1 for the driver's joint filtration* (`Driver/GermIndep.lean`,
        `isTrivialSigma_rightCont_zero`), the càdlàg modification
        (`Probability/CondExpModification.lean`, `Driver/CadlagMartingale.lean`) and the
        assembly. Tickets `A2`, `A3` of `../Dissertation/WORK_BREAKDOWN.md`. Axiom set: the 3
        standard.
- [x] **B5-0 / #13a statement audit** — RETIRED 2026-09-06 (refutable: single-driver
      integrands for a joint-filtration martingale; `W·Ñ`); the axiom and the derived
      `jacodYor_representation(_axiom)` were deleted. **B5** becomes: after X2, state the
      predictable representation property over the joint filtration of an independent pair
      `(W, N)` (Jacod 1975 / Jacod–Shiryaev III.4.34) and prove it.
      - [x] *Single-driver halves, 2026-09-08.* Brownian:
        `Brownian/PRPMultidimAssembly.lean` (`exists_vectorIntegral_augFiltration`). Poisson:
        `Poisson/PredictableRepresentation.lean` (`exists_markedHorizonIntegrand_of_le_aug`, for
        any filtration whose horizon σ-algebra sits below the augmented natural one;
        instantiated for the natural filtration and its `0`-clamped augmentation). The
        separation input is the window-character totality of `Poisson/WindowFiltration.lean`
        fed by the Grönwall vanishing of `Poisson/CharacterVanish.lean`. Axiom set: the 3
        standard. The joint statement is `../Dissertation/WORK_BREAKDOWN.md` A4d.

## Phase C — Non-vacuity artifact (`GOAL.md` §B)

- [x] **C1** Add `examples/Nonvacuity.lean`: per cited result + pinned symbol, an
      `example` discharging the hypotheses on a concrete non-degenerate model
      (non-zero-variance BM, non-zero Itô integral, the intended BSDEJ solution),
      so non-vacuity is CI-checked, not promised. Start with the now-closed
      results (KC: the `brownian_continuous_modification` instantiation).
      **Partly done 2026-09-15** (`LevyStochCalcExamples` roots): `examples/NonvacuityDrivers.lean`
      — a Brownian motion has second moment `t` at time `t > 0` and is not a.e. zero, a Poisson
      random measure has mean `T ν(A)` on a box and is not a.e. zero, the Brownian integral of `1`
      and the compensated integral of a mark indicator have second moments `T` and `T ν(A)` (also at
      the drivers' natural filtrations); `examples/NonvacuityItoLevy.lean` — every hypothesis of
      `itoLevyFormula_general` is discharged for `μ = 0`, `σ = 1`, `γ = e`, `ν = δ₁`, `u = x²`
      (whose gradient is provably unbounded, `not_bddAbove_gradient_uSq`) on a solution built by
      `exists_globalSolution` over a driver from `LevyDriver.exists`; `examples/NonvacuityBSDEJ.lean`
      (2026-09-15) — every hypothesis of `exists_unique_solvesBSDEJ` is discharged for the generator
      `f(s, y, z, u) = y`, terminal datum `W_1`, horizon `1`, `ν = δ₁` on a driver from
      `LevyDriver.exists`, and every solution has `Y_1 =ᵐ W_1`, not a.e. zero, so the conclusion is
      not the zero triple; `examples/NonvacuityBSDEJZ.lean` (2026-09-15) — for `f = 0`, `ξ = W_1`,
      `T = 1` the explicit triple (a continuous modification of `W`, `Z = 1_{(0,1]}`, `U = 0`) is a
      `SolvesBSDEJ`, its `Z` has energy `1`, and by uniqueness every solution's `Z` has energy `1`
      (`stochasticIntegralBrownian_one` in `Brownian/ItoIncrement.lean` is the new brick);
      `examples/NonvacuityBSDEJExp.lean` (2026-09-15) — for the `f = y` equation the explicit triple
      `Y = e^{1−t} W̃_t`, `Z = e^{1−s} 1_{(0,1]}`, `U = 0` is a `SolvesBSDEJ` (Itô's formula
      `IsVectorItoVersion.itoFormulaTime` at `augJoint D`), the energy of `Z` is `(e² − 1)/2`, and by
      uniqueness every solution's `Z` has that energy: nonzero generator and nonzero `Z` together.
      `examples/NonvacuityItoLevyPath.lean` (2026-09-15) — every path solving the Itô–Lévy example's
      equation from `0` has second moment `2` at time `1` (the expectation form of the quadratic Itô
      formula, with the driver's cross witness carried to the augmented right-continuation of the
      joint filtration), so it is not a.e. zero there; `examples/NonvacuityBSDEJRate.lean`
      (2026-09-15) — the A7′ cell-average rate `(e δ)²` for every solution of the `f = y` equation
      and every strictly monotone partition of `[0, 1]` of mesh `δ`, exhibited on the uniform
      partitions (`(e/M)²`). **C1 is closed for the headline results**: the drivers, the integrals,
      the Itô–Lévy formula, BSDEJ existence and uniqueness and A7′ each have a witness with
      satisfiable hypotheses and a non-degenerate conclusion. **Inventory 2026-09-15** (scratch
      `nonvacuity_inventory.md`): 20 of the 41 pinned symbols are covered, 21 are not or only
      partly (the σ-algebra symbols of `Driver/VectorIncrement.lean` and `Brownian/MultidimFiltered.lean`,
      the compensated-box lemmas, `jointIntegral`, the PRP, `BSDEJData`/`IsBSDEJSolution`,
      `Existence.Lipschitz`, `cellTimeAverage_U`), and 11 of the 14 cited theorems are reached
      only through wrappers, never applied by name. **The structural gap, closed the same day**: the
      four earlier BSDEJ witnesses all had `U ≡ 0` (no terminal datum or generator read the jump
      mark); `examples/NonvacuityBSDEJJump.lean` takes the terminal datum `ξ = J_1`, the compensated
      integral of the window indicator, so the solution is the càdlàg version of `J`, `Z = 0`,
      `U = 1_{(0,1]}` with marked energy `1`, and by uniqueness every solution's `U` has marked
      energy `1`. **Contract-symbol witnesses (2026-09-15)**: `examples/NonvacuityBSDEJData.lean` —
      the concrete `BSDEJData` of the `f = y` equation with its `Existence.Lipschitz` proof, the
      `IsBSDEJSolution` of the bridge on the `f = 0`, `ξ = W_1` model, and the driver's
      `jointIntegral` on each leg with a nonzero conclusion; `examples/NonvacuityContract.lean` —
      the unit increment has law `𝒩(0, 1)` and is positive with probability exactly `1/2`, so
      `sigmaBrownian`, the increment σ-algebra and `incrementSigma` are not `⊥`
      (`comap_increment_le_sigmaBrownian` applied); a region of intensity `Λ` is missed with
      probability exactly `exp (-Λ)`, so `regionSigma` and the step σ-algebra are not `⊥` and
      `indep_stepSigma` is applied to the unit step against `D.filtration 0` (which is trivial
      modulo null sets — the file does not claim otherwise); `compensated_mean_zero`,
      `compensated_second_moment`, `compensated_sq_integrable` applied to the compensated count on
      `(0, 1] × ℝ`; `BrownianMotion.exists`, `exists_of_sigmaFinite`,
      `itoIsometry_brownian_unified_existence`, `itoIsometry_compensated_unified_existence`,
      `itoIsometry_diff_brownian`, `itoIsometry_diff_compensated` applied by name. **Count**: 36 of
      the 41 pinned symbols now occur in a concrete-model witness; the five without one are
      `indep_iSup_sigmaBrownian_ne` (needs `d = 2`), `comap_pi_eq_iSup`,
      `indep_iSup_comap_of_disjoint`, `exists_predictable_jointIntegral` and
      `cellTimeAverage_U` — **all five closed by wave 12 (2026-09-15)**:
      `examples/NonvacuityScattering.lean` applies `indep_iSup_comap_of_disjoint` to the windows
      `(0, 1] × ℝ` and `(1, 2] × ℝ` (both count σ-algebras non-trivial, each count vanishing
      with probability exactly `exp (-1)`, joint vanishing with probability `exp (-1) ^ 2`);
      `examples/NonvacuityTwoCoordinates.lean` applies `indep_iSup_sigmaBrownian_ne` at `d = 2`
      and `comap_pi_eq_iSup` to the pair of unit increments (both coordinate σ-algebras
      non-trivial; the pair σ-algebra is the join and is not contained in either increment's,
      via "a σ-algebra independent of itself carries only events of probability 0 or 1");
      `examples/NonvacuityPRP.lean` applies `exists_predictable_jointIntegral` to `W_1` (any
      representing joint integral has second moment `1` and a representing pair of nonzero Itô
      energy or nonzero marked energy; the quantitative split Itô energy `1`, marked energy `0` is
      not claimed); `BSDEJ/CellAverageRateMarked.lean` (new library file) gives the cell-average
      rate `(K δ)² T ∫ φ² dν` for a separated marked integrand `h s · φ e`, and
      `examples/NonvacuityBSDEJRateU.lean` instantiates `cellTimeAverage_U` on the jump
      model: the cell average of the window indicator is the indicator itself (marked energy `1`,
      averaging error `0`), every solution's jump integrand differs from it by marked energy `0`
      and, at the mark `1` carried by `δ₁`, has the same cell averages almost surely; the separated
      rate is exhibited as an upper bound `(e / M)²` (its left side is not shown nonzero).
      **Count**: all 41 pinned symbols now occur in a concrete-model witness. Of the cited theorems,
      #1, #2, #5, #6, #9, #16, #17, #18 are applied by name; #3, #4, #12, #13b, #14 are still
      reached only through wrappers — **all five closed by wave 13 (2026-09-15)**:
      `examples/NonvacuityBrownianCited.lean` applies `kolmogorovChentsov_modification` (#3) to a
      Brownian motion with exponents `(4, 2)` and the constant `𝔼[Z⁴]` (the library's
      `gaussianFourthMoment`, shown positive; the closed form `3` is not in Mathlib at this pin
      and is not claimed) — the modification has second moment `1` at time `1`; and
      `brownian_martingale_rightCont` (#4), with `(naturalFiltration W).rightCont 1 ≠ ⊥` and the
      martingale non-constant (`W_0 = 0`, `𝔼 W_1² = 1`); the continuity conclusion of #3 is also a
      structure field of `BrownianMotion`, so the load-bearing content of that witness is the
      Kolmogorov condition itself. `examples/NonvacuityJumpDiffusionCited.lean` applies
      `picardFixedPoint_jumpDiffusion_exists_unique` (#14) and `JumpDiffusion.exists_unique` (#12)
      to the Itô–Lévy model over the augmented right-continuation of the joint filtration: the
      solution has second moment `2` at time `1` and every competitor solving on all horizons
      is not almost surely `0` there. `examples/NonvacuityMartingaleForm.lean` applies
      `condExp_to_PRP_martingale_form` (#13b) to `W_1`: a càdlàg martingale with `M_0 = 0`,
      `M_1 = W_1`, `M_1 ≠ M_0` almost surely, `𝔼 M_1² = 1`. **Status of `GOAL.md` §1.B
      (2026-09-15)**: every one of the 14 cited results and 41 pinned symbols has a witness in
      the `LevyStochCalcExamples` library (18 files, built by CI and by every gate run), each
      applying the result by name on a concrete model (`d ∈ {1, 2}`, `ν = δ₁`, finite activity)
      with a non-degenerate conclusion; the five boxes are ticked on that basis, with the
      standing caveats: the models are finite-activity; the KC constant is `𝔼[Z⁴]`, not `3`;
      the representing pair of `W_1` has nonzero energy but its Itô/marked split is not shown;
      the separated marked cell-average rate is an upper bound whose left side is not shown
      nonzero; cell averages of a solution's jump integrand agree with the window indicator only
      at the mark carried by `δ₁`; `D.filtration 0` is trivial modulo null sets and no witness
      claims otherwise.

## Phase C′ — Faithfulness (`GOAL.md` §C)

- [ ] **C′1** Faithfulness audit (report first, fixes second): compare `BrownianMotion`,
      `MultidimBrownianMotion`, `PoissonRandomMeasure`, `LevyDriver`, `IsBrownianFiltration`,
      `IsPoissonFiltration`, the two `L²` integrals, `JumpDiffusion`/`SolvesOn`, `SolvesBSDEJ`
      and `cellTimeAverage_Z/U` against the cited definitions (Karatzas–Shreve,
      Applebaum, Jacod–Shiryaev, Delong, Bouchard–Elie); for each of the 14 cited statements
      check quantifier order (`∀∃` vs `∃∀`) and that every hypothesis is used. Record every
      discrepancy as a ledger finding and fix or restate. **Audit done 2026-09-15** (scratch
      `audit_w14_faithfulness.md`; no unsoundness; findings are prose-over-artifact gaps, dead
      hypotheses and stated weakenings). Register and disposition:
      - F1 `BSDEJ/Definition.lean` — `filtration_eq_canonical`'s conclusion is `∃ Filt, Filt =
        ℱ.rightCont` (a shape guard, not a statement about the solution) and the module docstring
        claims the filtration is pinned to `σ(W, N)` (it is any driver filtration). → docstrings
        (wave 15).
      - F2 `Ito/Setting.lean` — `is_solution` docstring says `∀ᵐ ω, ∀ t`; binder is `∀ t, ∀ᵐ ω`.
        → docstring (wave 15); the pathwise form needs a càdlàg Brownian leg (open).
      - F3 #5/#6 — the unified-existence conclusions never name `W`/`N`; only the docstring says
        `F` is the canonical integral. The pinned forms (`itoIsometry_diff_*`, `isometry_*`) do
        name it. → docstrings (wave 15); the statements are consumed downstream and stay.
      - F4 #13b — `condExp_to_PRP_martingale_form` contains no representation (Doob
        regularisation + Blumenthal); the name and module header over-promise; `_hT` unused.
        → docstring/header (wave 15), `_hT` removed (wave 15); the name stays (consumed by name in
        the ledger and examples) — a rename is a Phase D decision.
      - F5 `JumpDiffusion` has no adaptedness field; `exists_unique`'s docstring says "adapted".
        → docstring (wave 15); adaptedness of `X` as a field is open (structural).
      - F6 `BSDEJData` docstring claims the slice-measurability fields exclude the junk Bochner
        integral; they do not (the composite in `u` need not be measurable; the repair is
        `GeneratorModification`). → docstring (wave 15).
      - F7 `martingale_stochasticIntegral`/`quadVar_stochasticIntegral` (both sides) conclude
        `∃ F : Filtration, …` while their docstrings name `ℱ.rightCont`; the pinned lemmas
        `martingale_rightCont_*` exist. → docstrings point to the pinned lemmas (wave 15).
      - F8 `IsPoissonFiltration.indep` is single-strip, weaker than "past ⟂ future"; the joint
        form is recovered only from `LevyDriver.indep`. → closed structurally 2026-09-16 (D3):
        the fields of `IsBrownianFiltration` and `IsPoissonFiltration` are now `indep_future`,
        independence of `ℱ s` (`s ≥ 0`) from the σ-algebra of all increments `W t − W s`, `t > s`,
        resp. of all counts on measurable regions of `(s, ∞) × E`; the single-strip statements
        are the theorems `IsBrownianFiltration.indep` / `IsPoissonFiltration.indep` with the old
        binders, so no caller changed. Every constructor was re-proved (natural filtrations from
        `Brownian/FutureIndependence.lean` and `Poisson/PastFutureIndependence.lean`, `of_le`,
        `rightCont` by finite subfamilies and the limit along `r ↓ s`, augmentation, the
        multidimensional natural filtration, `combineBM` through
        `indep_naturalFiltration_iSup_future`, the joint and cross filtrations of a driver);
        `IsBrownianFiltration.of_le_sup` now asks its side σ-algebra to be independent of the
        joint future. The pinned `LevyDriver.isBrownianFiltration` / `isPoissonFiltration` keep
        their names, statements and module.
      - F9 `PoissonRandomMeasure.integer_valued` is `∀ B, ∀ᵐ ω` and atomicity is not a field;
        `Poisson/Atomic.lean` repairs it on finite windows under `CountablyGenerated`. →
        docstring (wave 15); structural (open).
      - F10 `itoLevyFormula_general` is a single-time identity `∀ T, ∀ᵐ ω`, not pathwise. →
        recorded (docstring is honest); pathwise form open.
      - F11 uniqueness is modification, not indistinguishability; `Y_cadlag` permits the upgrade
        on `[0, T]`. → new theorem (wave 15).
      - F12 `cellTimeAverage_Z/U` are pathwise cell averages (docstring says so); the former
        pinned names `conditionalTimeAverage_Z/U` suggested conditional projections. → closed
        2026-09-16: renamed to `cellTimeAverage_Z/U`, with every derived name, the pinned rows
        of `tools/import_contract.md` and both repositories updated, and no forwarding stubs.
      - F13 dead binders: `[StandardBorelSpace E]` on #2 and `LevyDriver.exists`, `_h_finite` on
        `poissonRandomMeasure_finite_exists`, `_hT` on #13b, the inert SDE data of the two
        `picardFixedPoint` shims. → removed with callers updated (wave 15).
      - F14 `BrownianMotion.increment_independent` is derivable from
        `joint_increment_independent` (redundant field). → Phase D structural simplification.
      - F15 over-assumptions: `Y_cadlag`/`Z_vanish`/`U_vanish`/`HorizonIntegrand.vanishing` for
        every `ω`; `hu : ContDiff ℝ 2` jointly (C² in `t`, the literature needs C^{1,2}). →
        recorded; each is a widening of the hypothesis class. The path half closed 2026-09-16
        by theorem (`BSDEJ/SolvesAe.lean`): `SolvesBSDEJAe` asks the three path conditions
        almost surely, `SolvesBSDEJ.toAe` embeds, and `SolvesBSDEJAe.exists_modification`
        (uniform form `exists_modification_indistinguishable`) returns a `SolvesBSDEJ` triple
        agreeing with the given one off one null set, so uniqueness of `Y` up to
        indistinguishability transfers; the pinned structure is unchanged. The `C^{1,2}` half
        is open, with its groundwork landed the same day (`Ito/C12.lean`: the predicate `IsC12`,
        `IsC12.of_contDiff`, and the strictness witness `(t, x) ↦ t|t| x₀²`, which is `C^{1,2}`
        and not jointly `C²`; `Ito/C12Mollify.lean`: the time mollification `mollifyTime`, its
        joint continuity, `C^N` regularity in time at a fixed state, pointwise convergence, and
        the commutation of `timeDeriv`, `gradient`, `hessian` with it for a `C^{1,2}` function).
        Route settled by a read-only trace of the proof chain (same day): joint `C²` of `u` is
        consumed at exactly one structural site, `Ito/FiniteActivityMixed.lean` (`timeAugFun u`
        fed to the state-only vector Itô formula, whose cubic Taylor step needs the full Hessian
        of the augmented function); everything above it uses only the six `IsC12` fields. So:
        (1) `IsC12.mul_contDiff` for the cut-off products; (2) joint mollification
        `mollifyJoint` on `ℝ × (Fin n → ℝ)` (joint smoothness from Mathlib's convolution theory,
        the three derivative identities by differentiation under the integral, uniform derivative
        bounds, pointwise convergence); (3) `itoLevyFormula_jumpResidual_of_boundedDerivs_c12`
        by the limit `u_ε → u` at the bounded-derivative level through the existing domination
        toolkit; (4) thread `IsC12` up through the continuity/Taylor/cut-off lemmas as `_c12`
        duplicates, keeping every pinned `ContDiff` statement and `Dissertation/Continuous.lean`
        untouched; (5) `itoLevyFormula_general_c12`. Steps (1) and (2) landed the same day:
        `Ito/C12Product.lean` (`IsC12.mul`, `IsC12.mul_contDiff`, the Leibniz rules for the
        three derivative families, `IsC12.add/const_mul/neg/sub`, `isC12_cutoffFun₂`) and
        `Ito/C12MollifyJoint.lean` (`mollifyJoint` on `ℝ × (Fin n → ℝ)`, joint `C^N` regularity
        by convolution, `isC12_mollifyJoint`, the three commutation identities, the uniform
        derivative bounds in the shapes of `itoLevyFormula_jumpResidual_of_boundedDerivs`, and
        pointwise convergence along bumps with `rOut → 0`). Step (3) landed too:
        `Ito/ItoLevyBoundedDerivsC12.lean` (`itoLevyFormula_jumpResidual_of_boundedDerivs_c12`,
        byte-identical to the bounded-derivative theorem except for `hu : IsC12 u`; the
        admissibility inputs of each mollification are derived from the uniform bounds, the
        two stochastic integrals pass to the limit in `L²` and along a subsequence almost
        surely, the two Lebesgue integrals by dominated convergence;
        `Ito/ItoLevyBoundedDerivsC12Limits.lean` holds the convergence lemmas). Open: (4) the
        `_c12` helper layer above the bounded-derivative level and (5) the threading up to
        `itoLevyFormula_general_c12`.
      - F16 every jump-side witness uses `ν = δ₁` (finite activity); no infinite-activity Lévy
        measure is exercised. → wave 16 candidate (`ν = volume` on `ℝ`).
      **Wave 15 (2026-09-16)** closed F1, F2, F3, F4, F6, F7, F9 (docstrings), F13 (binders
      removed; `poissonRandomMeasure_finite_exists` deleted as a verbatim duplicate) and F11
      (`BSDEJ/UniquenessIndistinguishable.lean`, `Ito/PicardFixedPointIndistinguishable.lean`).
      **Wave 16 (2026-09-16)** closed F14 (`increment_independent` is a theorem derived from
      the σ-algebra field; the structure has one field fewer) and F16
      (`examples/NonvacuityInfiniteActivity.lean`: `ν = volume` on `ℝ`, σ-finite with infinite
      total mass — the library assumes only σ-finiteness, not the truncated second-moment
      condition of a Lévy measure — the count on `(0, 1] × ℝ` is almost surely infinite by the
      field `infinite_at_infinite_intensity`, the count on `(0, 1] × [0, 1]` has mean `1` and
      vanishes with probability `exp (-1)`, the compensated integral of `1_{[0,1]}` has second
      moment `1`, and `exists_unique_solvesBSDEJ` holds with `ν = volume` with a non-degenerate
      terminal value; the `Z`-energy transfer of `NonvacuityBSDEJZ` is typed at `δ₁` and is not
      repeated). **Wave 17 (2026-09-16)** closed F5 as a theorem
      (`Ito/JumpDiffusionAdapted.lean`: under the usual conditions every jointly measurable
      `S²`-bounded solution on all horizons is `StronglyMeasurable[ℱ t]` at every `t ≥ 0`, so
      `JumpDiffusion.exists_unique_adapted` restates existence and uniqueness with adaptedness of
      the solution and of every competitor; the structure itself still has no adaptedness field,
      and the compensated integral is adapted only to `ℱ.rightCont`, which the usual conditions
      absorb). **Wave 20 (2026-09-16)** closed F8 for the natural filtration
      (`Poisson/PastFutureIndependence.lean`: the counts on the measurable subsets of two disjoint
      regions generate independent σ-algebras, so `naturalFiltration N s` is independent of the
      σ-algebra generated by all counts on regions inside `(s, ∞) × E`; the single-strip field
      and `IsPoissonFiltration.indep` are unchanged, and the joint form is not claimed for an
      arbitrary filtration satisfying the single-strip predicate, where it fails in general) and
      closed F9 by design (atomicity is not a field because it is a theorem of the fields on every
      window of finite intensity under `CountablyGenerated E`, `Poisson.ae_isIntegerValued_restrict`
      and `ae_exists_eq_sum_dirac`; the structure docstring says so). **Wave 21 (2026-09-16)**
      closed F10 (`Ito/ItoLevyFormulaPathwise.lean`: `itoLevyFormula_general_pathwise` states the
      four-term identity at every horizon `T ≥ 0` off one null set, by right-continuity of both
      sides along almost every path and density of the rational horizons; the Brownian leg, which
      the `L²` construction defines one time at a time with no path regularity, enters as a
      prescribed right-continuous version, and `exists_itoLevyFormula_general_pathwise` supplies
      one that is adapted to the right-continuous filtration, jointly measurable, càdlàg at every
      sample point and a martingale; the compensator drift is assumed integrable over every window
      and the drift and integrated compensator-drift integrands locally integrable along almost
      every path). **Wave 26 (2026-09-16)** gave the Brownian half of the joint form
      (`Brownian/FutureIndependence.lean`: `BrownianMotion.indep_naturalFiltration_future`, the
      natural filtration at `s ≥ 0` is independent of the σ-algebra generated by every increment
      based at `s`, and `indep_naturalFiltration_increments` for the increments over subintervals
      of `[s, ∞)`; from Mathlib's `IsPreBrownianReal.indepFun_shift` through the bridge, with the
      negative times absorbed by the null-or-conull σ-algebra); the structural strengthening of
      the two filtration predicates is D3 below. Open: F15 (D3 in progress).
      **Wave 26** also opened the cell layer of the a-posteriori bridge (Epic A4′ of the
      dissertation's `WORK_BREAKDOWN.md`): `Brownian/ItoCellIsometry.lean` and
      `Ito/CompensatedCellIsometry.lean` (the two isometries for the increment across a cell
      `(a, b]`, `0 ≤ a < b`), `Driver/CellOrthogonality.lean` (Kunita–Watanabe orthogonality of
      the two cell increments, orthogonality across distinct Brownian coordinates, and
      orthogonality of either increment to every square-integrable weight measurable at `a`).
      **Wave 27 (2026-09-16)** continued it: `Driver/JointPRPProcess.lean` (the conditional
      expectation of each `L²` integral at `t ≤ T` for the right-continuous filtration, the
      process `jointIntegralProcess`, and the process-level form
      `exists_jointIntegralProcess_augFiltration_of_mean_zero` of the joint predictable
      representation), `Driver/AugJointRightCont.lean` (the augmented joint filtration is
      right-continuous at every `t ≥ 0`, `rightCont_augFiltration_eq`, through the σ-algebra
      criterion `le_aug_of_indep_of_le_sup`), and, on the dissertation side, the backward scheme
      read off a BSDEJ solution with its per-step stochastic-input bundle. Also landed:
      `Brownian/MultidimItoCongr.lean`, `BSDEJ/SolvesAe.lean` (F15, path half), `Ito/C12.lean`,
      `Ito/C12Mollify.lean` (F15, `C^{1,2}` groundwork), and the removal of the duplicate
      `stochasticIntegralBrownian_congr_ae` from `Ito/ItoIntegrandAeCongr.lean`.
      **A7 by hypothesis (2026-09-16, `BSDEJ/CellRegularity.lean`):** the `ℱ_{tᵢ}`-conditional
      cell averages `condCellAverage_Z/U` (distinct from the pathwise `cellTimeAverage_Z/U`,
      equal to them for deterministic integrands) and the predicate `CellRegularity`, the
      `L²`-path-regularity rate of Zhang (2004) and Bouchard–Elie (2008) on uniform grids,
      carried as an explicit named hypothesis because its published proofs need Malliavin
      calculus or a differentiable PIDE representation (ledger, Retired #10). It is not a
      theorem of this library. `examples/NonvacuityBSDEJCellRegularity.lean` inhabits it for the
      `f = y`, `ξ = W₁` equation with `C = e²`; that witness covers only the case where the
      conditional and the pathwise averages coincide (deterministic `Z`), and its `rate_U` half
      is degenerate (`U = 0`), so it exercises the statement, not the stochastic content.
      Also FAITHFUL with no action: `BrownianMotion` (tied to Mathlib both ways),
      `MultidimBrownianMotion`, `LevyDriver`, `IsBrownianFiltration`, both integrands and
      integrals (`ProgressivelyMeasurable ↔ IsStronglyProgressive`), `SolvesBSDEJ` (pinned
      filtration and integrals), #1, #4, #12/#14 (relative to the fixed filtration), #17, #18,
      the terminal-time PRP.
- [x] **C′2** Tie the BM layer to the mathlib predicates at the pin
      (`ProbabilityTheory.IsPreBrownianReal`, `IsBrownianReal`, `IsGaussianProcess`,
      `HasIndepIncrements` — all present in Mathlib `81a5d257`): the converse direction
      `BrownianMotion.ofIsPreBrownianReal` exists (`Brownian/Existence.lean`); the forward
      direction is `Brownian/MathlibBridge.lean` (2026-09-15): `BrownianMotion.hasLaw_eval`
      (`W_t ∼ 𝒩(0, t)`), `hasIndepIncrements` (mutual independence of the increments along any
      monotone tuple, from the σ-algebra field through the chain criterion
      `iIndep_of_indep_biSup_lt`), `isPreBrownianReal` (via Mathlib's
      `HasIndepIncrements.isPreBrownianReal_of_hasLaw`), `isBrownianReal`, `isGaussianProcess`,
      and the round trip `ofIsPreBrownianReal_w_ae_eq` (the rebuilt motion has paths
      `r ↦ W_r − W_0`, equal to `W_r` almost surely at `r ≥ 0`; it needs everywhere-continuous
      paths because `ofIsPreBrownianReal` does). Index set `ℝ≥0` on the Mathlib side. **Done**;
      this is also `D1`.

## Phase D — Mathlib-grade form + upstreaming (`GOAL.md` §D, §F)

- [x] **D0** Inventory (2026-09-15): 340 library files, 38 over 600 lines (largest
      `Poisson/CompensatedDensity.lean` 4471, `Brownian/ItoL2Completion.lean` 4252,
      `Ito/Picard.lean` 2919, `Brownian/ItoDensity.lean` 2550, `Ito/SecondMoment.lean` 2053);
      **wave 17 (2026-09-16)** split the three largest into thematic parts (10, 8 and 6 modules,
      each ≤ 598 lines) with the original module kept as the aggregating import, every
      declaration keeping its name and statement (two formerly private lemmas became public,
      `master_horizon_pos`, `bounded_locallyIntegrable`); **wave 18 (2026-09-16)** split
      `Brownian/ItoDensity.lean` (2550 → 5 parts, 21 private helpers made public, one part at
      625 lines to avoid shadowing the ancestor-namespace name
      `eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero`), `Ito/SecondMoment.lean` (2053 → 4, sections
      regrouped in dependency order, bodies unchanged), `Ito/PicardOutput.lean` (1963 → 4) and
      `Poisson/CompensatedMartingale.lean` (1516 → 3); **wave 19 (2026-09-16)** split
      `Poisson/MarkStep.lean` (1355 → 3), `Brownian/SimplePredictableRefine.lean` (1342 → 3, one
      private lemma made public, `strictMono_partition_tiles`; two parts at 611 and 624 lines to
      keep each theme whole), `Ito/ItoFormulaUnbounded.lean` (1254 → 3) and
      `Ito/JumpFormulaFiniteActivity.lean` (1202 → 3); **wave 20 (2026-09-16)** split
      `Ito/CompensatedLocality.lean` (1097 → 3), `Brownian/ItoAlgebra.lean` (1078 → 3),
      `Brownian/ItoFourthMoment.lean` (1066 → 3) and `Driver/CellGronwall.lean` (988 → 2), no
      private helper made public; **wave 21 (2026-09-16)** split `Brownian/ItoSimple.lean`
      (1023 → 3, two private lemmas made public, `simpleIntegral_diagonal_bochner` and
      `cross_sq_integrable`), `Ito/PicardSpace.lean` (946 → 3),
      `Ito/ItoLevyBoundedDerivsSolution.lean` (913 → 3) and `BSDEJ/PicardContraction.lean`
      (847 → 3); 22 files over 600 lines remain, the largest
      `Brownian/Continuity.lean` (1412, pinned: `kolmogorovChentsov_modification` must stay in it),
      `Poisson/CompensatedIsometry.lean` (1338, pinned), `Brownian/Martingale.lean` (1039, pinned),
      `Ito/PicardContraction.lean` (908), `Brownian/CrossOrthogonality.lean` (792); two files
      are dominated by a single proof and are left whole, `Ito/ItoLevyBoundedDerivs.lean` (913,
      `itoLevyFormula_jumpResidual_of_boundedDerivs` alone spans 608 lines) and
      `Ito/FiniteActivityMixed.lean` (834, one theorem of 716 lines); **wave 22 (2026-09-16)**
      split `Ito/PicardContraction.lean` (908 → 2), `Brownian/CrossOrthogonality.lean`
      (792 → 2), `Brownian/VectorItoQuadVarRiemann.lean` (771 → 2) and
      `Ito/JumpFormulaGeneralShift.lean` (762 → 2); **wave 23 (2026-09-16)** took the three
      pinned modules, each keeping its pinned symbols at the pinned path:
      `Brownian/Continuity.lean` (1412 → 444, `kolmogorovChentsov_modification` and the Brownian
      application stay, the dyadic chaining and the Kolmogorov bounds move to two imported
      modules), `Brownian/Martingale.lean` (1039 → 219, `naturalFiltration` and the moment
      lemmas stay, the conditional expectations, the martingale and quadratic-variation
      theorems and the right-continuous versions move to three modules that import it, with
      `Brownian/Filtered.lean` importing the first of them) and
      `Poisson/CompensatedIsometry.lean` (1338 → 497, the moment lemmas including the three
      pinned ones stay, the orthogonality and `L²` material move to two modules that import
      it, with `Poisson/CompensatedMartingaleAdapted.lean` importing the second); the downstream
      shape is recorded in `tools/import_contract.md` §3; **wave 24 (2026-09-16)** split the eight
      remaining files above 630 lines (`Brownian/ItoIncrementMoment`, `Ito/PicardIntegrand`,
      `BSDEJ/PicardIterates`, `Ito/JumpFormulaCutoff`, `Ito/ItoFormulaSimpleShift`,
      `Ito/JumpSplittingPath`, `Ito/JumpSplittingRemainder`, `Ito/JumpCoefficientPredictable`,
      each into two parts); of the 7 files still over 600 lines, two are the single-proof
      files above and the other 5 sit within 5 % of the target and are left whole
      (`Brownian/ItoDensityUnbounded.lean` 625, `Brownian/SimplePredictableRefineCommon.lean` 624,
      `Brownian/SimplePredictableRefineInvariance.lean` 611, `Brownian/ItoLocality.lean` 604,
      `Brownian/ItoQuadVarSum.lean` 603); the library has 452 files;
      no `import Mathlib` umbrella; six library docstrings still narrate dated retirements
      (`BSDEJ/MartingaleRepresentation`, `BSDEJ/Existence`, `BSDEJ/PathRegularity`,
      `Ito/JumpFormula`, `Ito/PicardFixedPoint` ×2) — the dates move to the ledger (wave 14).
      File splits keep every pinned symbol in its module of record (no forwarding stubs).
      The file-length pass is complete except for the two single-proof files, which are not
      pure moves and stay open below.
- [x] **D0′** Factor the two single-proof files below 600 lines by extracting their inner
      `have` blocks as standalone lemmas. **Wave 25 (2026-09-16):** `Ito/ItoLevyBoundedDerivs.lean`
      913 → 597 (fourteen lemmas and the relocated `tendsto_setIntegral_of_dominated_ae` in
      `Ito/ItoLevyBoundedDerivsSteps.lean`, since split into two parts) and
      `Ito/FiniteActivityMixed.lean` 834 → 570 (nine lemmas in
      `Ito/FiniteActivityMixedSteps.lean`, 456 lines); the two main theorems keep byte-identical statements, every extracted lemma takes exactly the local
      facts its block used, and one dead `have` was dropped from each proof. Six files remain
      at 602–625 lines, within the `~600` tolerance of GOAL §D, which is ticked on that basis.
- [x] **D1** Align the BM layer to mathlib predicates (`IsBrownianReal`,
      `HasIndepIncrements`, `IsGaussianProcess`) — see C′2 (`Brownian/MathlibBridge.lean`).
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
