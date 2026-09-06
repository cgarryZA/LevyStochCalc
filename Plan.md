# LevyStochCalc → Mathlib-Grade Library — Master Plan (v2)

**Regenerated 2026-06-16** per the `GOAL.md` loop contract: Phase 0 (declutter)
and Phase 1 (structural refactor) are complete, and Phase 3 #3
(Kolmogorov–Chentsov continuous modification) is proved. Git history holds the
old plan + the detailed per-phase notes. This v2 plan closes the remaining
`GOAL.md` §1 gaps, **dissertation-blocking axioms first** (`GOAL.md` §3).

## Where we stand (verified 2026-06-16)

- **2 custom axioms** remain — #13b and #16 (was 13; **#5 and #17 closed 2026-06-17**, **#1
  closed 2026-09-05** via `RemyDegenne/brownian-motion`, **#4, #6, #18 and #2 closed 2026-09-06**,
  **#15 retired 2026-09-06** as a vacuous statement, **#9, #10, #13a retired 2026-09-06 as
  refutable statements** — deleted, not relocated). `cited_axioms.md` "2 live". The 3 standard
  axioms (`propext`/`Classical.choice`/`Quot.sound`) are the only others. **The BSDEJ layer no
  longer states existence, path regularity or the PRP**; those return, correctly stated, with X2.
- **Statement audit 2026-09-06 (#16)**: the Itô–Lévy axiom lacked `u ∈ C²` and drift
  integrability and was refutable; both are now hypotheses (see `tools/cited_axioms.md` #16).
  The same audit found that the library's `L²` integrals accept only integrands adapted to
  the natural filtration of a *single* driver, so `JumpDiffusion.is_solution` and the PRP/BSDEJ
  statements (#13a, #13b, #9, #10) are faithful only for uncoupled coefficients — the
  common-filtration generalization **X2** below now precedes A5–A7.
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
  The other 6 (#2, #4, #13a, #13b, #17, #18) were cited results but **not**
  reached by the pinned surface (#2, #4, #17, #18 are theorems now).
- **#5/#6 are foundational**: the audit shows #15, #16, #9, #10 *already carry*
  #5/#6 transitively, so the Itô-formula and BSDE layers cannot go axiom-free
  until the L² integrals are built. Hence #5 → #6 first.
- Four-way invariant green; build = 2904 jobs.

## Cross-repo roadmap and an upstream discharge of #6 (2026-09-05)

The end-to-end program for the three papers now lives in
`../Dissertation/FORMALIZATION_ROADMAP.md`; this file remains the route for the foundations
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
- [x] **A5-0 / #16 statement audit** — DONE 2026-09-06: added `hu : ContDiff ℝ 2 (uncurry u)`
      and `h_μ_int` (drift integrable on `[0, T]` along the path) to the axiom, its two derived
      theorems and the dissertation forwarder; without them the statement was refutable
      (indicator `u` along `W`; `u = t·x` with `μ = 1/s`). Recorded the single-driver
      filtration scope of the whole SDE layer (`cited_axioms.md` #16 "Scope").
- [ ] **X2 — common filtration for the `L²` integrals** (new, 2026-09-06; blocks A5–A7 and
      B4/B5 from being faithful for coupled coefficients). Today
      `MultidimBrownianMotion.stochasticIntegral` needs `H_j` progressively measurable for
      `naturalFiltration (W.W j)` and `Compensated.stochasticIntegral` for `naturalFiltration N`.
      Plan: (1) an abstract driver-with-filtration layer — a filtration `ℱ`, `W` an
      `ℱ`-Brownian motion (increments independent of `ℱ_s`), `N` an `ℱ`-Poisson random measure
      (future counts independent of `ℱ_s`), with the joint natural filtration of `(W, N)` as the
      canonical instance and independence of `W` and `N` bundled; (2) re-parametrize the
      simple-integrand, isometry, martingale, `L²`-completion and càdlàg-modification files by
      `ℱ` (the proofs use only `ℱ`-adaptedness of simple integrands, independence of increments
      from `ℱ_s` and `ℱ`-martingale arguments; ≈500 `naturalFiltration` sites across
      `Brownian/*`, `Poisson/Compensated*`, `Ito/Picard`, `BSDEJ/Definition`); (3) restate
      `JumpDiffusion`, the Picard chain, #16, #13a/#13b, #9/#10 over the joint filtration;
      (4) keep the pinned dissertation symbols resolving; update `Continuous.lean`.
- [ ] **A5 / #16** `itoLevyFormula_jumpResidual_canonical_axiom` — Itô–Lévy jump
      residual (Applebaum 4.4.10 + 4.4.7), on A2/A4 and X2.
- [x] **A6-0 / #9 statement audit** — RETIRED 2026-09-06 (refutable: arbitrary non-adapted
      `X`; single-driver integrand class); the axiom and the dissertation forwarder Cu01 were
      deleted. **A6** becomes: after X2, state and prove BSDEJ existence/uniqueness over the
      joint filtration via the Picard chain (Tang–Li 1994 / AGPP 2025); retires the lone
      `sorry` (`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`).
- [x] **A7-0 / #10 statement audit** — RETIRED 2026-09-06 (refutable: the `C·Δt` rate for
      merely measurable `g`, `X`; `1_{W_T>0}` has rate `Δt^{1/2}`); the axiom, its two
      corollaries, the dissertation forwarder Cu05 and the dissertation's bridge section were
      deleted. **A7** becomes: after A6, state and prove Bouchard–Elie path regularity with its
      regularity hypotheses (Lipschitz `g`, Lipschitz jump diffusion `X`).

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
- [ ] **B4 / #13b** `condExp_to_PRP_martingale_form_axiom` — Doob L² càdlàg
      regularization (KS I.3.13) + Blumenthal 0-1.
- [x] **B5-0 / #13a statement audit** — RETIRED 2026-09-06 (refutable: single-driver
      integrands for a joint-filtration martingale; `W·Ñ`); the axiom and the derived
      `jacodYor_representation(_axiom)` were deleted. **B5** becomes: after X2, state the
      predictable representation property over the joint filtration of an independent pair
      `(W, N)` (Jacod 1975 / Jacod–Shiryaev III.4.34) and prove it.

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
