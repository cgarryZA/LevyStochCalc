# Cited Axioms

The ledger of record for the **paper-cited stochastic calculus results** of
`LevyStochCalc`. Each numbered entry is a real published theorem that was at some point
introduced as `axiom <name> : <statement>` with a docstring giving the citation; most are now
Lean `theorem`s or have been deleted, and the entry records which.

A cited axiom is a Lean `axiom` declaration, so it does not carry `sorryAx` and a `sorryAx`
check does not see it; it is visible instead as a non-standard name in a `#print axioms`
report, which is what an axiom allowlist (`X1e` in `../Dissertation/RELEASE_READINESS.md`)
checks.

## Tier 1: cited axioms (0 currently live)

**No cited axiom is live, and the repository contains no `axiom` declaration** (since
2026-09-15). The last one, #16 `itoLevyFormula_jumpResidual_canonical_axiom`, was deleted
because its statement could not be proved: it asserted the Itô–Lévy formula at an arbitrary
filtration unrelated to the one the solution solves against. The result it stood for — the
Itô–Lévy formula for a `C²` state function of a jump diffusion, with no bound on the
derivatives — is the theorem `itoLevyFormula_general` (`Ito/ItoLevyFormulaGeneral.lean`, later
the same day), stated at the solution's own filtration; the entry `### Resolved #16` below
records the statement with every hypothesis exposed and the proof route, and the
bounded-derivative case `itoLevyFormula_of_boundedDerivs`
(`Ito/ItoLevyBoundedDerivsSolution.lean`) is the milestone it is built on. Deleting an
unprovable axiom was clean-up; the theorem is the closure. The count in the heading above and
the file agree by construction: only a digit-leading `### <n>.` heading marks a live axiom, so
`grep -c "^### [0-9]" tools/cited_axioms.md == 0`. `### Resolved #N` / `### Retired #N` /
`### Open #N` headings are kept for traceability and are not counted.

Twenty numbered entries have existed, and they closed in three different ways, which the index
below distinguishes because they are not equally good news:

* **Proved** (#1–#6, #13b, #17, #18) — now carried by a Lean `theorem` over the three standard
  axioms. #1–#4 keep the statement they had as axioms; #5, #6, #17, #18 were restated on the
  way (the integrand class and the filtration argument, X2-1/X2-2) and #13b now takes a
  `LevyDriver` (X2-3) — each entry records the change.
* **Re-derived from narrower entries** (#11, #12, #14) — also theorems, but that is a claim
  about the derivation, not about grounding: #12 and the surviving #14 name are on the three
  standard axioms; #11 `itoLevyFormula` was deleted with #16 on 2026-09-15 (its statement was
  #16's, at an arbitrary filtration), and the four-term formula the dissertation forwards is now
  `itoLevyFormula_general`, on the three standard axioms.
* **Deleted, then proved** (#16) — the `axiom` was deleted on 2026-09-15 as unprovable as
  stated (an arbitrary filtration unrelated to the solution's); the general Itô–Lévy formula it
  stood for is the theorem `itoLevyFormula_general` of the same day, at the solution's own
  filtration, with exactly the hypotheses its entry records as the target and nothing narrower.
* **Retired as unsound** (#9, #10, #13a, #15) — the *Lean* statement was found refutable or
  trivially satisfiable, and the declaration was deleted rather than weakened or relocated into
  a hypothesis. The cited literature result is not proved and not disproved by the retirement;
  with the integrals now stated over a common filtration (`Plan.md` X2), it returns as a
  statement to prove with the hypotheses the literature actually assumes. For #9 that statement
  is now the theorem `exists_unique_solvesBSDEJ` (`Plan.md` A6, closed 2026-09-15; entry
  `### Resolved #9`); #10 and #13a wait on A7 and B5; #15's content is #16's.
* **Deleted as dead** (#7, #8) — superseded by a refactor, reachable from nothing. The derived
  #13 was deleted with #13a, which it was built on.

The index names, for each entry, the declaration that carries it now and the commit that closed
it; the sections after it carry the statement, citation, mathlib status and replacement plan.
#7 and #8 are cited by date and red-team finding (M4), #3 by date.

### Index

* **#1** `Brownian.BrownianMotion.exists` — theorem since 2026-09-05 in
  `Brownian/Existence.lean`, over the `BrownianMotion` require (`3486f07`).
* **#2** `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` — theorem since 2026-09-06 in
  `Poisson/RandomMeasure.lean` (`9888119`).
* **#3** `Brownian.Continuity.kolmogorovChentsov_modification` — theorem since 2026-06-16 in
  `Brownian/Continuity.lean`, proved from scratch.
* **#4** `Brownian.Martingale.brownian_martingale_rightCont` — theorem since 2026-09-06 in
  `Brownian/Martingale.lean` (`900bb55`).
* **#5** `Brownian.Ito.itoIsometry_brownian_unified_existence` — theorem since 2026-06-17 in
  `Brownian/ItoL2Completion.lean` (`d899e08`).
* **#6** `Poisson.Compensated.itoIsometry_compensated_unified_existence` — theorem since
  2026-09-06 in `Poisson/Compensated.lean` (`9456014`).
* **#7** `Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` — deleted 2026-05-22 with
  its dead superseded chain (red-team finding M4).
* **#8** `Poisson.Compensated.adaptedSimple_dense_L2_compensated` — deleted 2026-05-22 alongside
  #7 (M4).
* **#9** `BSDEJ.Existence.continuousBSDEJ_exists_unique` — retired and deleted 2026-09-06 as a
  refutable statement (`7dad5c2`); the corrected statement, over the augmented joint filtration of a
  Lévy driver, is the theorem `BSDEJ.Solves.exists_unique_solvesBSDEJ` since 2026-09-15
  (`### Resolved #9`).
* **#10** `BSDEJ.PathRegularity.bsdej_path_regularity` — retired and deleted 2026-09-06 as a
  refutable statement (`7dad5c2`); restated after X2.
* **#11** `Ito.JumpFormula.itoLevyFormula` — axiom→theorem 2026-05-24 (`8ff0234`), derived
  from #16 alone; deleted with #16 on 2026-09-15. The four-term formula the dissertation
  forwards is `Ito.JumpFormula.itoLevyFormula_general` (`Ito/ItoLevyFormulaGeneral.lean`).
* **#12** `Ito.Setting.JumpDiffusion.exists_unique` — axiom→theorem 2026-05-26; the chain's last
  `sorry` was closed 2026-09-07 (`ba5e214`) and the theorem is in `Ito/PicardFixedPoint.lean`.
* **#13** `BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom` — decomposed into #13a +
  #13b 2026-05-26 (`76ca7ef`); the derived theorem was deleted 2026-09-06 with #13a (`7dad5c2`).
* **#13a** `BSDEJ.MartingaleRepresentation.jacodYor_PRP_martingale_axiom` — retired and deleted
  2026-09-06 as a refutable statement (`7dad5c2`); the PRP returns after X2.
* **#13b** `BSDEJ.MartingaleRepresentation.condExp_to_PRP_martingale_form` — theorem since
  2026-09-06 in `BSDEJ/MartingaleRepresentation.lean` (`a50d97b`).
* **#14** `Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom` — axiom→theorem
  2026-05-26 (`bec976e`); the forwarder and its `_via_aeQuot` wrap-up were deleted 2026-09-07
  (`ba5e214`), which also discharged the wrap-up's `sorry`.
* **#15** `Ito.JumpFormula.itoFormula_continuousSemimartingale_axiom` — retired and deleted
  2026-09-06 as a trivially satisfiable statement (`df95191`); its content is #16's.
* **#16** `Ito.JumpFormula.itoLevyFormula_jumpResidual_canonical_axiom` — **deleted, then
  proved** 2026-09-15: the axiom was deleted (unprovable as stated), and the general statement
  it stood for is the theorem `Ito.JumpFormula.itoLevyFormula_general`
  (`Ito/ItoLevyFormulaGeneral.lean`), built on the bounded-derivative case
  `itoLevyFormula_of_boundedDerivs`.
* **#17** `Brownian.Ito.itoIsometry_diff_brownian` — theorem since 2026-06-17 in
  `Ito/Picard.lean` (`ad63700`).
* **#18** `Poisson.Compensated.itoIsometry_diff_compensated` — theorem since 2026-09-06 in
  `Poisson/Compensated.lean` (`6ddf8ca`).

`tools/sorry_baseline.txt` is empty (since 2026-09-15; its last entry, the canonical assembly
`itoLevyFormula_jumpResidual_canonical` of the deleted `Ito/JumpFormulaAssembled.lean`, was
superseded by `itoLevyFormula_general`), and `sorry`/`admit` occur in the `.lean` sources only
as words in docstrings and comments; no `#print axioms` report over `_audit.lean` names
`sorryAx` or an axiom outside the three standard ones, and the repository contains no `axiom`
declaration. A `#print axioms` report of `{propext, Classical.choice,
Quot.sound}` certifies the logical trust base only; it says nothing about whether a statement is
faithful to the result it cites, which is what the per-entry statement audits below record.

### History

* #17 and #18 were added in source on 2026-05-23 but first assigned Tier 1 numbers in this file
  on 2026-05-27 (3rd-audit reconciliation, CRITICAL #1); they are the per-difference
  L²-isometries used by the Picard contraction estimates and the Itô–Lévy formula (#16).
* #12 and #13 were added 2026-05-23 by theorem→axiom conversion of the previously sorry-bodied
  `JumpDiffusion.exists_unique` and `jacodYor_representation`, then demoted again on 2026-05-26.
* #14 was added 2026-05-23 and converted axiom→theorem 2026-05-26 via the Bielecki AE-quotient
  infrastructure in `PicardSpace.lean`, leaving a single explicit `sorry` in the wrap-up; that
  `sorry` was discharged on 2026-09-07 and the redundant intermediates were deleted.
* #16 was narrowed 2026-05-26 (`f70f66a`) from the universal-`R` form
  `itoLevyFormula_jumpResidual_axiom` to the canonical-`R` form; the universal-`R` form is now a
  derived theorem.

These axioms state real published theorems. The LevyStochCalc-side `axiom` declaration is
intended to match the cited statement faithfully; where an audit found it did not, the entry
below says so. When Mathlib formalises the underlying theorem, the `axiom` is replaced with a
`theorem` forwarding to the Mathlib version, no other changes needed downstream.

### Resolved #1: `LevyStochCalc.Brownian.BrownianMotion.exists` (proved axiom→theorem 2026-09-05)

* **Status**: `theorem` in `LevyStochCalc/Brownian/Existence.lean`, derived from
  `ProbabilityTheory.isBrownianReal_brownian` (`RemyDegenne/brownian-motion` @ `4d52fa77`, Mathlib
  `81a5d257`) through `BrownianMotion.ofIsPreBrownianReal`; axiom set `{propext, Classical.choice,
  Quot.sound}`. The sorry-bearing modules of that dependency (`Auxiliary/StandardBorel`,
  `StochasticIntegral/*`, `Choquet/*`) are outside the imported closure.
* **Statement**: There exists a probability space carrying a 1-dimensional Brownian motion.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 2.2.2** (Daniell-Kolmogorov consistency) + **Theorem 2.2.8** (Kolmogorov-Čentsov continuous-modification existence) — Chapter 2 §2.2 "First Construction of Brownian Motion" pp. 49-56 (correcting the previous "Theorem 2.1.5" citation flagged by red-team P11 2nd audit — §2.1 of K-S is the chapter Introduction, no theorem 2.1.5 exists); Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Definition 2.1** / **Definition 2.12** / **Corollary 2.11** (the Brownian-motion construction; correcting the previous "Theorem 2.1" citation flagged by red-team P11 — Le Gall 2016 has no "Theorem 2.1"; the existence statement combines the definition + the explicit Wiener-measure construction in Chapter 2). Wiener measure construction via Kolmogorov extension + KC modification.
* **Mathlib status (May 2026)**: No current `MeasureTheory.WienerMeasure` or `BrownianMotion` definition. Adjacent infrastructure exists: `ProbabilityTheory.gaussianReal` (Real Gaussian distribution), `ProbabilityTheory.IsGaussianProcess`, `MeasureTheory.IsProjectiveLimit`, `Probability.Kernel.IonescuTulcea.trajMeasure` (dyadic-time Markov chains). The "Degenne et al stochastic integration" effort (arXiv:2511.20118, late 2025) is the most active push toward Mathlib-Brownian; no Mathlib PR merged at time of writing.
* **Replacement plan**: `theorem BrownianMotion.exists := <Mathlib forwarder>` when `MeasureTheory.WienerMeasure` lands.

### Resolved #2: `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` (proved axiom→theorem 2026-09-06)

* **Statement**: For σ-finite intensity ν on a measurable mark space E, ∃ probability space carrying a Poisson random measure with intensity `vol[0,∞) ⊗ ν`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 2.3.1**; Kallenberg, *Random Measures, Theory and Applications*, Springer 2017, **Proposition 3.6**.
* **Status**: No longer an axiom — proved as a `theorem` in `Poisson/RandomMeasure.lean`, statement unchanged, by the Poisson recipe (Mathlib has `ProbabilityTheory.poissonMeasure` but no Poisson random measure). The time-space is cut into the cells `[n, n+1) × sₘ` of a σ-finite decomposition; each cell of positive intensity `Λ(A)` carries a `Poisson(Λ(A))` number of independent marks with law `Λ|_A / Λ(A)`; the cells are independent (`Measure.infinitePi` over `ULift ℕ × (ℕ → ℝ × E)`) and superposed. Ingredients: `Poisson/PoissonSplitting.lean` (the counts of a Poisson number of iid marks on disjoint sets are independent Poisson, by characteristic functions), `Probability/IndepGrouping.lean` (an independent family indexed by pairs stays independent after grouping along a coordinate), `Poisson/PoissonSuperposition.lean` (the superposition: mean `= Λ(B)` hence a.s. finite on finite-intensity sets, Poisson law by the characteristic-function limit of the Poisson partial sums, a.s. infinite on infinite-intensity sets since `Po(λ)([0,k]) → 0` as `λ → ∞`, independence on disjoint sets by grouping), and `Poisson/RegionIndependence.lean` (the σ-algebra past/future field from countable independence, the former `IndependentScattering.lean` argument over a raw random measure). `#print axioms` lists only the three standard axioms; `poissonRandomMeasure_finite_exists` and the consumers are unchanged. The former `[StandardBorelSpace E]` hypothesis was never used by the construction and was removed from the statement on 2026-09-15 (faithfulness audit F13).

### Resolved #3: `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification` (proved axiom→theorem 2026-06-16)

* **Statement**: A real-valued process satisfying the Kolmogorov moment condition with `q > 1` admits a modification with continuous paths.
* **Reference**: Karatzas–Shreve **Theorem 2.2.8**; Le Gall **Theorem 2.9**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Springer 1999, **Theorem I.2.1**.
* **Status**: No longer an axiom — proved from scratch as a `theorem` (mathlib has only `IsKolmogorovProcess`, the condition; the continuity conclusion is supplied here). Proof: `kc_level_bad_measure` (per-level Markov/union bound) → `kc_ae_increment_bound` (Borel–Cantelli) → `dyadic_holder_chaining` + `kc_ae_nbhd_holder` (a.s. local Hölder) → `exists_tendsto_of_local_holder` + `continuous_extendFrom` (continuous modification) → `kolmogorov_modification_ae_eq` (modification property). `#print axioms` → `propext, Classical.choice, Quot.sound` only.

### Resolved #4: `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont` (proved axiom→theorem 2026-09-06)

* **Statement**: Brownian motion is a martingale w.r.t. the right-continuous augmentation of its natural filtration.
* **Reference**: Karatzas–Shreve **Theorem 2.7.7** (Blumenthal 0-1) + **Theorem 2.7.9** (right-continuity of augmented filtration); Le Gall **Theorem 2.13** (Blumenthal 0-1 for Brownian motion; correcting the previous "Proposition 2.10" citation flagged by red-team P11 — Le Gall 2016 p. 25 "Lemma 2.10" is a deterministic real-analysis Hölder lemma; Blumenthal is Le Gall p. 30 Theorem 2.13).
* **Status**: No longer an axiom — proved as a `theorem` in `Brownian/Martingale.lean`, statement unchanged, without Blumenthal's 0-1 law: the natural-filtration martingale property (`brownian_martingale_natural`, the former body of `brownian_martingale`) lifts to `ℱ₊` by `Martingale/RightCont.lean`'s `martingale_rightCont_of_tendsto_eLpNorm_one` (an `ℱ₊ s`-measurable set lies in every `ℱ r`, `r > s`, and right-`L¹`-continuity carries the martingale identity down to `s`), the right-`L¹`-continuity coming from `𝔼|W_r − W_s|² = r − s` (the Gaussian increment law, `gaussianReal_second_moment`) and `W = 0` at negative times. `#print axioms` lists only the three standard axioms; the consumer `brownian_filtration_rightContinuous` is unchanged.

### Resolved #5: `LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence` (proved axiom→theorem 2026-06-17)

* **Statement**: For predictable square-integrable `H`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t H² ds` is a `Filt`-martingale (quadratic variation identity), and the L²-isometry `∫⁻ ‖F T‖₊² = ∫⁻ ∫⁻ ‖H‖² over [0,T]` holds at every `T > 0`.
* **Reference**: Karatzas–Shreve **Theorem 3.2.6** (unified martingale + quadratic variation + L²-isometry); Le Gall **Theorem 5.4** + equation **(5.8)** (Itô isometry).
* **Status**: No longer an axiom — proved as a `theorem` in `Brownian/ItoL2Completion.lean`. The witness is `F := stochasticIntegralBrownian` (the coherent `L²`-limit of the `masterApprox` simple integrals), `Filt := (naturalFiltration W).rightCont`. Conjunct 1 = `martingale_rightCont_stochasticIntegralBrownian`; conjunct 2 = `martingale_rightCont_quadVar_stochasticIntegralBrownian` (set-level Itô isometry at simple level → `L¹`-limit of the compensated squares → `rightCont` right-`L¹`-continuity); conjunct 3 = `isometry_stochasticIntegralBrownian`. The consumers `itoIsometry`, `quadVar_stochasticIntegral`, `martingale_stochasticIntegral` (and `stochasticIntegral` itself, via `Classical.choose`) are unchanged. `#print axioms` for these now lists only `propext, Classical.choice, Quot.sound`.
* **Integrand-class caveat (2026-09-06) — resolved the same day (X2-1)**: the original `h_progMeas` hypothesis admitted only integrands a.s. constant in `ω` for each time (see "Integrand-class audit" below). The theorem is now stated for `Probability.ProgressivelyMeasurable ℱ H` (genuine progressive measurability, equivalent to Mathlib's `IsStronglyProgressive`) with respect to any filtration `ℱ` for which `W` is a Brownian motion (`IsBrownianFiltration W ℱ`), and `stochasticIntegral` takes `(ℱ, hℱ)` as arguments; the proof was re-run over that class without any change to the analytic argument. `#print axioms` still lists only the three standard axioms.

### Resolved #6: `LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence` (proved axiom→theorem 2026-09-06)

* **Statement**: For predictable square-integrable `φ`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t ∫_E φ² ν(de) ds` is a `Filt`-martingale, the L²-isometry holds at every `T > 0`, and `F` has càdlàg paths.
* **Reference**: Applebaum 2009 **Theorem 4.2.3** (martingale + quadVar + L²-isometry) + **Theorem 4.2.4** (càdlàg modification); Ikeda–Watanabe **Section II.3**.
* **Status**: No longer an axiom — proved as a `theorem` in `Poisson/Compensated.lean`, statement unchanged. The witness is `F := stochasticIntegral`, now *defined* as the càdlàg adapted modification (`exists_cadlag_modification`) of the `L²` integral process `process` (`Poisson/CompensatedProcess.lean`: the `L²`-limit at every time of the integrals of the mark-step approximants of `φ`, `Poisson/MarkStep.lean` + `Poisson/CompensatedApprox.lean`), `Filt := (naturalFiltration N).rightCont`. Conjunct 1 = `martingale_stochasticIntegral_rightCont` (from `martingale_rightCont_process`); conjunct 2 = `martingale_quadVar_stochasticIntegral_rightCont` (from `martingale_rightCont_quadVar_process`: set-level increment isometries of the mark-step integrals ⇒ the stage compensated squares are martingales, `L¹`-limit, right-`L¹`-continuity); conjunct 3 = `isometry_stochasticIntegral` (from `process_lintegral_sq'`); conjunct 4 = `stochasticIntegral_cadlag` (the Layer-0.5 brick `Martingale/CadlagModification.lean`: a martingale is a quasimartingale, and the quasimartingale regularisation of `RemyDegenne/brownian-motion` gives the adapted càdlàg modification). The consumers `itoLevyIsometry`, `quadVar_stochasticIntegral`, `martingale_stochasticIntegral`, `cadlag_modification_exists` are unchanged in statement and now forward to the construction. `#print axioms` for all of these lists only `propext, Classical.choice, Quot.sound`. The upstream `formal-mathfin` isometry (below) was not used in the end: the isometry is proved in-house through the mark-step calculus, so the general-`E` density question it left open does not arise.
* **Partial upstream discharge (2026-09-05)**: `raphaelrrcoelho/formal-mathfin` (@ `784a8311`, a `lake require`)
  proves the compensated-Poisson `L²` isometry for the continuous linear extension of the elementary
  integral to the `L²`-closure of *marked simple* integrands (`MathFin.itoLevyIntegralL2_norm`), over its
  own `PoissonRandomMeasure` structure. `Poisson/MathFinBridge.lean` shows every PRM of this library is one
  of theirs (`toMathFin`; the σ-algebra independent-scattering field is `indep_of_disjoint_region`,
  proved in `Poisson/IndependentScattering.lean`) and reads the isometry back
  (`PoissonRandomMeasure.itoLevyIntegralL2_norm`). **What this does not discharge** — and why the axiom
  stays live: (i) that every progressively measurable `L²` integrand `φ` of the axiom's hypothesis class lies
  in that closure (the predictable-`L²` density the upstream calls a deferred summit), (ii) the martingale
  and compensator-martingale conjuncts, (iii) the càdlàg modification. The bridge is a `def`, not a
  relocation of the axiom's statement.
* **Integrand-class caveat (2026-09-06) — resolved the same day (X2-2)**: the original `h_progMeas` hypothesis admitted only integrands a.s. constant in `ω` for each time (see "Integrand-class audit" below). The theorem is now stated for `Probability.MarkedProgressivelyMeasurable ℱ φ` (genuine progressive measurability of the marked integrand) with respect to any filtration `ℱ` for which `N` is a Poisson random measure (`IsPoissonFiltration N ℱ`), and `stochasticIntegral` takes `(ℱ, hℱ)` as arguments; the proof was re-run over that class without any change to the analytic argument. `#print axioms` still lists only the three standard axioms.

### Retired #7: `LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` (DELETED 2026-05-22)

This axiom was deleted on 2026-05-22 as dead code. It was the Compensated
Cauchy-completion step in the L² Itô-Lévy construction route that was
superseded by the 2026-05-10 unified-existence axiom refactor. Per
red-team finding M4, neither this axiom nor its downstream chain
(`simpleIntegralLp_compensated` → `itoIntegralLp_compensated` →
`exists_itoIntegralL2_compensated` → `itoIsometry_compensated_existence`
→ `stochasticIntegral_isometry_only_compensated`) was reachable from any
audited load-bearing theorem; the public `Compensated.stochasticIntegral`
is built directly from `itoIsometry_compensated_unified_existence`
(Tier 1 #6).

Original statement (recoverable from git history before commit deleting
the chain): for an adapted sequence `(G n)` of `SimplePredictable Ω E ν T`
with shared endpoint and `(G n).eval` Cauchy in `L²(P × ds × dν)`, the
lifted `simpleIntegralLp_compensated (G n)` is Cauchy in `Lp ℝ 2 P`
(Applebaum 2009 Equation 4.3.1 + Lemma 4.2.5).

### Retired #8: `LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated` (DELETED 2026-05-22)

This axiom was deleted on 2026-05-22 as dead code, alongside #7. It was
the Compensated L²-density-of-adapted-simple-predictables step in the
same superseded chain. Per red-team finding M4, not reachable from any
audited load-bearing theorem.

Original statement (recoverable from git history): for progressively-
measurable `φ : Ω → ℝ → E → ℝ` with finite L² norm on `[0, T]`, there
exists a sequence of adapted simple predictables `G n` with `(G n).eval`
converging to `φ` in `L²(P × ds × dν)` plus the shared endpoint + joint
measurability properties needed downstream (Applebaum 2009 Lemma 4.2.2).

### Retired #9: `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique` (RETIRED 2026-09-06 — statement refutable; DELETED)

*The corrected statement is proved: see `### Resolved #9` below. This entry is kept as the record of what was retired and why.*

* **Statement audit (2026-09-06)**: the axiom quantified over an arbitrary *measurable* forward process `X` (no adaptedness) and asked for a solution in `IsBSDEJSolution`, which pins `Y` adapted to the joint filtration and `Z`, `U` progressively measurable for the natural filtration of a *single* driver (`naturalFiltration (W.W i)` per coordinate, `naturalFiltration N` alone). Two refutations: (i) on a product space `Ω_W × Ω_N × [0,1]` take `g(x) = x₁` and `X_T := ` the third coordinate — `ξ = g(X_T)` is independent of `(W, N)`, yet the solution equation at `t = T` forces `Y_T = ξ` a.s. with `Y_T` `Filt_T`-measurable, impossible for a non-degenerate independent variable; (ii) `n = 2`, `X_T = (W_T, Ñ_T)`, `g(x) = x₁ x₂`, `f = 0`: the unique solution has `Z_s = Ñ_{s-}`, which is not adapted to `ℱ^W`, so no solution exists in the pinned class. The axiom and its dissertation forwarder `Dissertation.Continuous.continuousBSDEJ_exists_unique` (Cu01) were deleted; `picardMap` and `Lipschitz` remain. The corrected statement — `X` adapted (a jump diffusion), integrands over the joint filtration of `(W, N)` — returns with work package X2 (`Plan.md`).

* **Statement**: Under Lipschitz hypotheses on `(f, g)` and L² integrability of terminal data, the continuous BSDEJ has a unique adapted solution triple `(Y, Z, U) ∈ S² × H² × H²_N` satisfying the strengthened `IsBSDEJSolution` predicate.
* **Reference**: Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, DOI 10.1137/S0363012992233858 (historical first BSDEJ existence reference per Papapantoleon-Possamaï-Saplaouras 2018; specific theorem number paywalled and unverified per red-team P11 2nd audit 2026-05-23 — primary numbered citation is AGPP 2025 below); Andersson, Gnoatto, Patacca & Picarelli, *A deep solver for BSDEs with jumps*, SIAM J. Financial Math. / arXiv:2211.04349, 2025, **Theorem 2.4** (correcting the previous fabricated citation "Gnoatto 2025 *Quantitative Finance* primer" flagged by red-team P11 — no such paper exists per DBLP); Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer EAA 2013 (first edition, DOI 10.1007/978-1-4471-5331-3), **Theorem 4.1.3** (jumps case, directly applicable). For continuous-only background see also Pardoux & Răşcanu, *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*, Springer 2014, **Theorem 4.79** — but note Pardoux-Răşcanu does NOT cover the BSDEJ (jump) case per red-team P11 2nd audit 2026-05-23; the jump-case authority is Tang-Li + Delong + AGPP.
* **Predicate state (2026-05-11)**: The `IsBSDEJSolution` predicate was tightened on 2026-05-11 — the previous vacuous per-`(t, ω)` existential `∃ BM_term jump_term : ℝ, …` (which made the axiom mathematically false as written, since multiple distinct `Y` could trivially satisfy it) was replaced with an outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to `Z, U` via L²-isometry (for `M_W` vs `Z`) and direct equality to `Compensated.stochasticIntegral` (for `M_N` vs `U`). The strengthened predicate is no longer vacuously satisfiable by constant `Y` for generic `(f, g)`. Documented in `BSDEJ/Definition.lean` module docstring.
* **Mathlib status (May 2026)**: No BSDEJ in Mathlib. `Mathlib.Analysis.SpecificLimits.Basic` has Picard / contraction-mapping infrastructure (`ContractingWith.fixedPoint`) usable for the proof body once the L² Itô-Lévy + martingale representation pieces land.
* **Replacement plan**: `theorem continuousBSDEJ_exists_unique := <Picard contraction proof>` when the L² Itô-Lévy chain is fully formalized (after items 5 + 6 above). Further predicate-tightening (pinning `M_W` to the actual multidim Brownian stochastic integral, not just an isometric martingale) is a separate downstream item — needs `h_progMeas` threaded through `IsBSDEJSolution`.
* **Findings on the restatement (2026-09-15, Epic A6 wave 0)**: two statement defects in the surviving scaffolding were fixed before any existence proof. (D1) `BSDEJ.Existence.Lipschitz` measured the jump distance by `(∫⁻ …).toReal.sqrt`; since `(⊤).toReal = 0`, the clause forced `f` to be constant in `u` across pairs with `u₁ − u₂ ∉ L²(ν)`. It is restated in `ℝ≥0∞` (`Existence.lean`), with `abs_sub_le_of_lipschitz` recovering the real form under finiteness. (D2) `BSDEJData.f_measurable` asked joint measurability for the product σ-algebra on `E → ℝ`; a product-measurable function depends on countably many coordinates, so for an atomless `ν` the Lipschitz clause forces `f` constant in the jump variable — the theorem `BSDEJ.GeneratorDegeneracy.f_const_of_measurable_of_lipschitz` (`BSDEJ/GeneratorDegeneracy.lean`). The field is now `f_measurable_slice` (measurability of the `(t, x, y, z)`-slice at each fixed `u`). The driver-pinned solution predicate `BSDEJ.Solves.SolvesBSDEJ` (`BSDEJ/Solves.lean`: over the augmented joint filtration `augJoint D`, the canonical integrals, `Z` and `U` vanishing off `[0, T]`) is the target of the existence-and-uniqueness statement; its bridge to `IsBSDEJSolution` is `BSDEJ.Solves.isBSDEJSolution_of_solvesBSDEJ` (`BSDEJ/Bridge.lean`, 2026-09-15, leaf L21a). Leaf plan: `D:/Dissertation/WORK_BREAKDOWN.md`, Epic A6.
* **Finding D3 (2026-09-15, found while proving the bridge)**: the equation conjunct of `IsBSDEJSolution` was mis-parenthesised. Mathlib's `∫ s in S, body` notation takes the longest possible body, so `Y t ω = g (X T ω) + ∫ s in Icc t T, f … - (M_W T ω - M_W t ω) - (M_N T ω - M_N t ω)` placed both martingale increments *under* the drift integral: the predicate asserted `Y_t = g(X_T) + ∫_t^T (f(s, …) − ΔM_W − ΔM_N) ds`, which differs from the intended equation by the factor `T − t` on the martingale part, and no triple with a non-vanishing martingale part satisfied it. None of the seven regression extractors touched the equation, and no theorem in either repository consumed that conjunct (the dissertation's `ContXiong` files use the joint-measurability conjunct only). Fixed by parenthesising the integral (`BSDEJ/Definition.lean`, as `SolvesBSDEJ.eqn` already did) and guarded by the new extractor `IsBSDEJSolution.eqn_canonical`, which restates the equation with the increments beside the integral and fails to elaborate against the greedy reading.

### Resolved #9: `LevyStochCalc.BSDEJ.Solves.exists_unique_solvesBSDEJ` (the statement the retired #9 stood for, restated over the augmented joint filtration of a Lévy driver and proved 2026-09-15)

* **Statement (as proved)**: `LevyStochCalc.BSDEJ.Solves.exists_unique_solvesBSDEJ` (`BSDEJ/ExistenceUniqueness.lean`). Data: a Lévy driver `D : LevyDriver P d ν` on a probability space `(Ω, P)`, with `d` Brownian coordinates and a Poisson random measure of σ-finite intensity `ν` on a mark space `E` that is countably generated with measurable singletons; a generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` with `hf` (measurability of `(t, y, z) ↦ f t y z u` at each fixed jump variable `u`) and `hlip` (the `ℝ≥0∞` Lipschitz bound `‖f s y₁ z₁ u₁ − f s y₂ z₂ u₂‖₊ ≤ ofReal L · (‖y₁ − y₂‖₊ + ‖z₁ − z₂‖₊ + (∫ ‖u₁ − u₂‖₊² dν)^{1/2})` with `hL : 0 ≤ L`); a horizon `hT : 0 < T` with `hf0 : ∫₀ᵀ ‖f(s, 0, 0, 0)‖₊² ds < ⊤`; a terminal datum `ξ` with `hξ2 : MemLp ξ 2 P` and `hξm : AEStronglyMeasurable[augJoint D T] ξ P`. Conclusion: `(∃ Y Z U, SolvesBSDEJ D f ξ T Y Z U) ∧ ∀ Y₁ Y₂ Z₁ Z₂ U₁ U₂, SolvesBSDEJ D f ξ T Y₁ Z₁ U₁ → SolvesBSDEJ D f ξ T Y₂ Z₂ U₂ → (∀ t ∈ [0, T], Y₁ t =ᵐ[P] Y₂ t) ∧ (∀ j, energy P T (Z₁ j − Z₂ j) = 0) ∧ markedEnergy P ν T (U₁ − U₂) = 0`. The class `SolvesBSDEJ` (`BSDEJ/Solves.lean`) is `S² × H² × H²_ν` over `augJoint D := Brownian.augFiltration D.filtration P`: `Y` càdlàg at every sample point, adapted to `(augJoint D).rightCont`, jointly measurable, with square integrable running supremum on `[0, T]`; `Z` and `U` jointly measurable and (marked) progressive for `augJoint D`, vanishing off `[0, T]` and of finite energy there; and the equation `Y_t = ξ + ∫_t^T f(s, Y_s, Z_s, U_s) ds − ∫_t^T Z dW − ∫_t^T ∫_E U dÑ` almost surely at each `t ∈ [0, T]`, with the two stochastic integrals the canonical ones of this library for `augJoint D`. `#print axioms`: `propext`, `Classical.choice`, `Quot.sound` (the logical trust base only).
* **The pieces**: existence is `exists_solvesBSDEJ` (`BSDEJ/PicardLimit.lean`), uniqueness `SolvesBSDEJ.unique` with `unique_Y_Icc`, `unique_Z`, `unique_U` (`BSDEJ/Uniqueness.lean`); the bridge `isBSDEJSolution_of_solvesBSDEJ` (`BSDEJ/Bridge.lean`) lands a `SolvesBSDEJ` triple in the earlier predicate `IsBSDEJSolution D.W D.N (bsdejDataOfGenerator f hf) X Y Z U T` for any forward process `X` with `X T ω 0 = ξ ω`.
* **What changed against the retired statement**: the generator no longer reads a forward process (the retired axiom's `f(s, X_s, …)` with an arbitrary measurable `X` was refutation (i)); the integrand class is the augmented joint filtration of `(W, N)`, not a single driver's natural filtration (refutation (ii)); the Lipschitz clause is in `ℝ≥0∞` (finding D1) and the generator's measurability is slice-wise (finding D2); the equation conjunct of `IsBSDEJSolution` is parenthesised as intended (finding D3). A generator reading a forward jump diffusion is not covered — that is Epic A7's setting.
* **Proof route** (`../Dissertation/WORK_BREAKDOWN.md`, Epic A6, leaves L01–L21, all on the three standard axioms; no Itô formula and no Grönwall lemma): the Picard step via the joint predictable representation (`BSDEJ/PicardTerminal.lean`, `CadlagLegs.lean`, `DriftLeg.lean`, `PicardStep.lean`), the output frozen at the horizon as an Itô–Lévy process (`PicardItoLevy.lean`), the backward weighted second-moment inequality (`Ito/SecondMomentBackward.lean`), Young + Lipschitz (`YoungLipschitz.lean`) giving the contraction of factor `1/4` at the weight `β = max 2 (24 L²)` (`PicardContraction.lean`), progressive modifications of the drift (`GeneratorModification.lean`, `DriftModification.lean`), the iterates and their geometric Cauchy bound (`PicardIterates.lean`), the limit in the energy norms and one further step giving the fixed point (`PicardLimit.lean`).
* **Reference**: Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, Theorem 3.1; Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer EAA 2013, Theorem 4.1.3; Andersson, Gnoatto, Patacca & Picarelli, arXiv:2211.04349, Theorem 2.4 (see the reference bullet of `### Retired #9` for the audit history of these citations).
* **Not claimed**: path regularity (#10, A7); the forward-coupled generator; comparison theorems; a non-vacuity witness with a non-zero generator (`GOAL.md` §1.B, queued).

### Retired #10: `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity` (RETIRED 2026-09-06 — statement refutable; DELETED)

* **Statement audit (2026-09-06)**: the axiom asserted the Bouchard–Elie rate `C · Δt`, with `C` independent of the partition, for *every* measurable `g` and *every* measurable `X` with `𝔼|g(X_T)|² < ∞`. Bouchard & Elie assume a Lipschitz `g` and a forward jump diffusion with Lipschitz coefficients; for `d = 1`, `ν = 0`, `X = W`, `g = 1_{x > 0}` the solution exists in the pinned class (`Z` is `ℱ^W`-adapted) and `𝔼 ∫_0^T |Z_s − Z̄_s|² ds` decays like `Δt^{1/2}` only (fractional smoothness `1/2`, Geiss–Geiss–Gobet 2012), so the claimed bound fails as `Δt → 0`. The axiom, its corollaries `bsdej_path_regularity_linear_rate` and `bsdej_U_L2_regularity_linear_rate`, the dissertation forwarder `Dissertation.Continuous.bsdej_path_regularity` (Cu05) and the dissertation's `LevyStochCalcBridge` section (which used only the positivity of the constant) were deleted; `cellTimeAverage_Z/U` remain. The corrected statement returns with work package X2, with the regularity hypotheses of the cited theorem.

* **Statement**: For the unique BSDEJ solution (satisfying the strengthened `IsBSDEJSolution` predicate from item 9), the L²-time modulus + projection errors of `(Z, U)` over a partition with mesh `Δt` are bounded by `C · Δt`.
* **Reference**: Bouchard & Elie, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, Stochastic Processes Appl. **118(1)**, **2008**, pp. 53–75, **Theorem 2.1** (correcting the previous misattribution to "Bouchard, Elie & Touzi 2009 SPA 119(11)" — Touzi is not an author and no such 2009 paper exists; flagged by red-team P06/P07/P10/P11, verified via Bouchard's slides + HAL hal-00015486 + Kharroubi–Lim 2018 citing "Bouchard and Elie [4]"). For continuous-only background see also Pardoux & Răşcanu, Springer 2014, **Theorem 5.42** (continuous case, NOT BSDEJ) — Pardoux-Răşcanu does NOT cover the jump case per red-team P11 2nd audit 2026-05-23.
* **Predicate state**: Same strengthening note as item 9.
* **Mathlib status (May 2026)**: `MeasureTheory.Submartingale.upcrossingsBefore_le` and adjacent Doob's L²-maximal inequality infrastructure exists in `Mathlib.Probability.Martingale`. The Grönwall integral lemma `Mathlib.Analysis.Gronwall` is also available. Combining these into the path regularity bound is mechanical once items 5 + 6 + 9 land.
* **Replacement plan (corrected 2026-09-15)**: the earlier line here ("`<Doob + Grönwall combination>` when items 5, 6, 9 are theorems") was wrong. Bouchard–Elie's Theorem 2.1 is proved by Malliavin calculus (`Z_t = D_t Y_t`, the derivative of the solution of the forward jump diffusion; cf. arXiv:1103.3029 §1, which states that the method rests on a regularity result for `Z` given by Malliavin tools), and every alternative route in the literature (Zhang 2004, Ma–Zhang 2002, the PIDE route) goes through a differentiable dependence of the solution on the state. Blockers in this library, with sizes: a generator reading the forward process (`SolvesBSDEJ` takes `f` deterministic in `ω`; retyping it and re-running the twelve Picard files — L), a two-parameter flow `X^{t,x}` with the Markov property (absent — XL), the first variation of the flow or a Malliavin calculus (absent — XL), and the discrete-scheme error itself, which is what `../Dissertation/BSDE/Discrete/DiscretizationConvergence.lean` consumes as `ψ(h)` (absent — XL). A7 is therefore deferred. What is within reach and true: (W1) for every `SolvesBSDEJ` triple the cell-projection error `E∫|Z − Z̄^π|²` tends to `0` (pure `L²` approximation, no rate); (W2, "A7′") for a generator not reading `X` and a solution whose `Z` is a deterministic Lipschitz function `h(s)`, the rate `E∫_0^T|Z − Z̄^π|² ≤ (K δ)² T` (`K` the Lipschitz constant, `δ` the mesh): the deterministic half is the theorem `BSDEJ.PathRegularity.energy_sub_cellTimeAverage_le_of_lipschitz` (`BSDEJ/CellAverageRate.lean`, 2026-09-15, for the process `Z s ω i = h s` and the pathwise cell average `cellTimeAverage_Z`); the transfer to every solution of the equation with generator `f(s, y, z, u) = y`, terminal datum `W_1` and horizon `1` is `Examples.Nonvacuity.energy_sub_cellAverage_le_of_solvesBSDEJ` (`examples/NonvacuityBSDEJRate.lean`, 2026-09-15; every solution's `Z` agrees a.e. with `e^{1−s}` by the uniqueness conjunct of `exists_unique_solvesBSDEJ`, so the deterministic bound transfers; exhibited on the uniform partitions as `(e/M)²`). This is the whole of what is proved about path regularity: one equation, the pathwise cell average, a deterministic bound carried along an a.e. identification. Note also that `BSDEJ.PathRegularity.cellTimeAverage_Z/_U` are pathwise cell averages, measurable at the right end of each cell, not the `F_{t_i}`-conditional projections of the paper (their docstrings said otherwise until 2026-09-15); the pathwise average is the `L²(dt)`-orthogonal projection onto the larger space of all cell-constant processes, so a rate for the conditional projection transfers to it, not conversely.
* **Public-API specialization** (added 2026-05-24): the derived theorem `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity_linear_rate` exposes the same bound in the simplified `∃ C : ℝ, 0 < C ∧ ∀ partition, bound ≤ ENNReal.ofReal (C · Δt)` form (a single positive real `C` instead of the polynomial-exponential closure `K · (1+T)^p · exp(α·L·T) · (1+ξ)` evaluated at `(T, L, ‖ξ‖_L²)`). This is what downstream chapters need to set `ψ(h) := C · h` (e.g. the parked `D:/Dissertation/Dissertation/BSDE/Discrete/DiscretizationConvergence.lean`, which uses the BET 2008 linear-rate `ψ(h) = C · h` as the discretization-error hypothesis driving its `discrete_to_continuous_convergence_sq` headline). The corollary is an `honest derivative theorem`: `#print axioms` surfaces exactly `{propext, Classical.choice, Quot.sound, bsdej_path_regularity}` — no new axiom.

### Retired #11: `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` (RETIRED axiom→theorem 2026-05-24; ENTRY KEPT FOR HISTORY)

On 2026-05-24 this axiom was retired and `itoLevyFormula` became a Lean
**theorem**, derived by algebraic re-bundling from TWO narrower Tier 1
sub-axioms `itoFormula_continuousSemimartingale_axiom` (Tier 1 #15) and
the (then-)Tier-1 axiom `itoLevyFormula_jumpResidual_axiom` (Tier 1 #16,
itself further refactored axiom→theorem on 2026-05-26 — see #16 entry
below). The qualified theorem name
`LevyStochCalc.Ito.JumpFormula.itoLevyFormula` is preserved so the
dissertation forwarder (`Dissertation.Continuous.itoLevyFormula`) is
unaffected by the refactor.

**Original statement** (recoverable from git history prior to commit
retiring #11): For a `C^{1,2}` function `u` and a jump diffusion
`X = (μ, σ, γ)`-driven by `(W, N)`, the chain-rule decomposition
(Applebaum 2009 Thm 4.4.7) — `u(T, X_T) − u(0, X_0) = drift + diff_mart
+ jump_mart + comp_drift` — with ALL FOUR terms pinned to their
literature integral forms.

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.4.7**; Cont & Tankov, *Financial Modelling with Jump Processes*, Chapman & Hall/CRC 2003, **Proposition 8.18**.

### Retired #15: `LevyStochCalc.Ito.JumpFormula.itoFormula_continuousSemimartingale_axiom` (RETIRED 2026-09-06 — statement trivially satisfiable; content in #16)

* **Statement**: For `u ∈ C^{1,2}` and a jump-diffusion `X = (μ, σ, γ)`-driven by `(W, N)`, the classical continuous-semimartingale Itô formula (Karatzas–Shreve 3.3.6) applied to `u(t, X^c_t)` (where `X^c` is the continuous-semimartingale part in the Lévy–Itô decomposition `X = X^c + X^d`) produces the drift + diff-mart identity with an existential residual `R`: there exists `R : ℝ → Ω → ℝ` such that a.s.,  `u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω`.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer 1991, **Theorem 3.3.6** (Itô formula for continuous semimartingales — multidimensional vector form, equation (3.3.5)); Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 5.10**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer 1999, **Theorem IV.3.3**.
* **Mathlib status (May 2026)**: No Itô formula in Mathlib (waits on Brownian motion construction + L² Itô integral; tracked alongside Tier 1 #5). The Degenne et al stochastic-integration effort (arXiv:2511.20118, late 2025) is the most active push toward a Mathlib Itô formula; no PR merged at time of writing.
* **Replacement plan**: when Mathlib gains the Itô formula for continuous semimartingales (Karatzas–Shreve 3.3.6), this axiom is replaced by a forwarder that decomposes `X = X^c + X^d` via the Lévy–Itô decomposition and applies the Mathlib theorem to `X^c`.
* **Statement audit (2026-09-06)**: as written in Lean, the axiom asserts only `∃ R, ∀ᵐ ω, u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω` with `R` unconstrained, which is satisfied by `R T ω := u(T, X_T ω) − u(0, X_0 ω) − drift − diff_mart` and therefore carries **no** content of Karatzas–Shreve 3.3.6: the Lean statement and the cited result do not match (a prose-vs-artifact gap). It has deliberately **not** been discharged by that trivial witness, since doing so would relocate rather than close the gap. The analytical content of the Itô–Lévy formula lives entirely in #16 (which pins the canonical residual to the jump terms); `itoLevyFormula` needs #15 only to name an `R`. Retired the same day: `itoLevyFormula` is now derived from #16 alone (the canonical-residual identity rearranged), the axiom declaration was deleted from `Ito/JumpFormula.lean`, and no theorem in the library depends on it. The Itô formula for continuous semimartingales (KS 3.3.6) that this entry cited is part of the content of #16 and will be proved there (WP8).

### Resolved #16: `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_canonical_axiom` (axiom DELETED 2026-09-15 as unprovable as stated; the general Itô–Lévy formula it stood for is the theorem `itoLevyFormula_general` since 2026-09-15; narrowed 2026-05-26 from the previous monolithic #16)

* **Statement**: For the *canonical* residual `R_canonical T ω := u(T, X_T) − u(0, X_0) − drift − diff_mart` (constructed by direct subtraction from the LHS, with no quantification over arbitrary `R`s), we have `R_canonical T ω = jump_mart_T(ω) + comp_drift_T(ω)` a.s., where `jump_mart_T = Compensated.stochasticIntegral N (u(·+γ) − u along X) T` and `comp_drift_T(ω) = ∫_0^T ∫_E [u(·+γ) − u − γᵀ∇u](s, X_s, e) ν(de) ds`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.4.10** (small/large jump decomposition); same source **Theorem 4.4.7** proof **step (II)** for the `ε → 0` limit (page 240); Ikeda–Watanabe **Section II.5**; Cont–Tankov **Proposition 8.18** + Chapter 8.
* **Narrowness (2026-05-26 narrowing)**: the previous monolithic #16 (`itoLevyFormula_jumpResidual_axiom`, universal-`R` form) quantified over *any* `R` satisfying a continuous-part identity `u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω`. The 2026-05-26 narrowing eliminates that quantifier: the axiom now asserts the identity only for the canonical `R` constructed by direct subtraction. The universal-`R` form (`itoLevyFormula_jumpResidual_axiom`) is now a derived theorem forwarding over this canonical axiom by per-ω algebra (`R = R_canonical` a.s. when both satisfy the continuous-part identity). The narrower axiom captures exactly the analytical content of Applebaum 4.4.10 + 4.4.7 step II (the small/large-jump decomposition + ε→0 L²-limit + Lévy-Itô combinatorial step); the universal-`R` form adds only algebraic glue.
* **Statement audit (2026-09-06) — two missing hypotheses, now added.** The statement had no smoothness hypothesis on `u` and no integrability of the drift `μ(s, X_s)` along the path. Its derivative-based integrands use Mathlib's `fderiv`/`deriv`, which are `0` off the differentiability set, and its drift term is a Bochner integral, which is `0` on non-integrable integrands; so the statement as written was refutable, not merely unproved: (i) `n = d = 1`, `(μ, σ, γ) = (0, 1, 0)`, `X = W`, `u(t, x) = 1_{x > 0}` — every integrand vanishes, all hypotheses hold, and the conclusion reads `1_{W_T > 0} = 0` a.s.; (ii) even for smooth `u`, `μ(s, x) = 1/s` makes the SDE drift integral silently `0` (so `X = x₀ + W`), and for `u(t, x) = t x` the claimed identity is off by `T`. The corrected statement assumes `hu : ContDiff ℝ 2 (Function.uncurry u)` (joint `C²`, which contains the cited `C^{1,2}` class) and `h_μ_int : ∀ᵐ ω, ∀ i, IntegrableOn (fun s => μ s (X s ω) i) (Icc 0 T)`; the derived theorems `itoLevyFormula_jumpResidual_axiom`, `itoLevyFormula` and the dissertation forwarder `Dissertation.Continuous.itoLevyFormula` carry both. (Integrability of the drift integrand `∂ₜu + 𝓛u` along the path follows from these and the structure's `sup_L2`/càdlàg fields and is not assumed.) No `sorry` and no change to the conclusion; the axiom is *narrower* than before.
* **Statement audit (2026-09-10) — SIX further hypotheses are missing (a seventh, item 2, was WITHDRAWN the same day), and the axiom as it
  currently stands CANNOT BE PROVED. Corrections identified, NOT YET APPLIED.** Assembling the
  replacement proof (Epic B, `../Dissertation/WORK_BREAKDOWN.md` B4) surfaced these gaps between what
  the statement assumes and what the cited theorem needs. Each is faithful to Applebaum individually
  — several restore hypotheses the source assumes that this Lean transcription dropped — but the
  aggregate is a substantive change to what is being proved, and it is recorded here **before** the
  closure rather than presented afterwards as a clean discharge of the statement as written.
  1. `[MeasurableSpace.CountablyGenerated E]` and `[MeasurableSingletonClass E]` on the mark space.
     Not derivable: they are what makes the realised counting measure on a finite-activity window a
     *nameable* finite sum of Diracs, and the pathwise jump sum rests entirely on that enumeration.
     Applebaum's mark space is `ℝᵈ ∖ {0}`, a Borel subset of a Polish space, which has both.
  2. ~~`∀ s ≤ 0, ∀ x e, coeffs.γ s x e = 0`~~ — **WITHDRAWN 2026-09-10, the same day, as mis-framed.**
     This was listed as a hypothesis the *coefficient* must satisfy. That was wrong. It is an
     artefact of **this tree's** `markedPredictableSigma`, whose generators are the rectangles
     `F ×ˢ (Ioc r q ×ˢ B)` with `0 ≤ r`, leaving the whole nonpositive strip a single atom. The
     literature's marked predictable σ-algebra is the **product** `𝒫 ⊗ ℰ` of the predictable
     σ-algebra with the mark σ-algebra, under which `1_A(e)` is measurable outright and the mark cut
     preserves predictability with no hypothesis whatever. The obstruction is in the Lean
     definition, not in the mathematics, and it does not narrow #16.
     **The right adjustment is a convention on the integrand, not an assumption on the model**:
     extend by zero below the time domain, `Ĥ(ω, s, e) = if 0 < s then H(ω, s, e) else 0`. It is the
     *integrand* that is zeroed, not the coefficient or the initial state — zeroing the input tuple
     would not suffice when the coefficient is nonzero at the origin.
     `Ito/JumpCoefficientPredictable.lean`'s `markedPredictable_ite_of_predictable` already gives
     predictability of the extension with **no** extra hypothesis, and the two checks that make the
     convention free are proved in `Ito/JumpFormulaClosure.lean`: `zeroExtPos_of_pos`, the extension
     agrees with the integrand at every positive time; and `zeroExtPos_ae_eq`, it has the same class
     for `markedEnergyMeasure P ν T`, so the compensated integral is unchanged — that intensity is
     `dt ν(de)` on `[0, T]`, which meets the nonpositive times only at `{0}`. The pathwise jump sum
     integrates over `(0, t]` and never sees them; the drift integral over `[0, t]` differs on a
     Lebesgue-null set.
  3. `∀ t, Measurable[ℱ t] (X.X t)`. **This is a defect in `JumpDiffusion`, not in #16.** The
     structure's docstring calls its solution "adapted" (`Ito/Setting.lean`) but carries no such
     field, and adaptedness does not follow from `is_solution`: the two stochastic terms are
     `ℱ t`-measurable, but the drift term is not known to be, and proving it would already require
     `X` adapted. In the literature a solution is adapted by definition.
  4. Càdlàg paths at **every** sample point, not almost every. Predictability is a pointwise
     statement about a σ-algebra; off the null set where the structure's field says nothing,
     `Function.leftLim` falls back to the point value, which is progressive but not predictable. The
     same applies to continuity of the continuous part, which the per-interval Itô layer needs
     pointwise while the splitting supplies it only almost surely. Both are **bridged** in
     `Ito/JumpFormulaClosure.lean` (`repairOn`, `repairOn_cadlag`, `repairOn_continuous`) by
     replacing the path on a null set, which is sound because the conclusion is an almost-sure
     identity whose terms depend on the path only through null-insensitive integrals.
  5. Measurability and an `L²` bound for `μ(·, X_·)` on windows. The structure needs neither, since
     its drift term is a Bochner integral, and #16 assumes only pathwise integrability. Derivable
     from `JumpDiffusionCoeffs.IsRegular` + `IsLipschitz` + `sup_L2` via `Ito/PicardIntegrand.lean`,
     so a consumer with coefficient-level hypotheses discharges them — but **`IsLipschitz` must not
     be added to #16**: it belongs to Applebaum Thm 6.2.9 (SDE existence), not Thm 4.4.7, which is
     stated for predictable square-integrable integrands with no Lipschitz condition. Adding it
     would narrow the statement past its own source.
  6. Joint measurability of `γ` — the third conjunct of `IsRegular`, which the bare coefficient
     bundle does not carry.
  7. A **pointwise-in-the-mark** bound `‖γ s (X_s ω) e‖ ≤ M` along the path, needed by the
     localisation that removes the derivative bounds #16 does not assume. Genuinely not implied by
     the coefficient data: `IsLipschitz` constrains `γ` only in the state and only in an `L²(ν)`-in-`e`
     sense, and `IsRegular` bounds only `∫⁻ e, ‖γ s 0 e‖²`. Neither gives a pointwise bound in `e`.
* **Assembly re-scoped (2026-09-10; plan of record `../Dissertation/WORK_BREAKDOWN.md`, "B4 re-scoped" and
  "B4-P0 comparison").** The assembled theorem in `Ito/JumpFormulaAssembled.lean` carries seven
  `sorry`s. Scoping them found: its limit interface is in the pure form while the truncated path's
  integrands run along the original path; the truncated stochastic terms need bounded derivatives;
  the axiom's `ℱ` and the SDE's existential `ℱ₀` are unrelated in the statement (correction 8, taken
  as: usual conditions on `ℱ` and the SDE data at `ℱ` — the papers' own setting, dischargeable from
  `PicardFixedPoint.exists_unique`'s `SolvesOn`); and correction 7's pointwise-in-mark bound is not
  the papers' Assumption 2.3, which is `L²(ν)`-Lipschitz. **Next deliverable: milestone M16**, the
  formula for `u` with bounded `∂ₜu`, `∇u`, `Hess u`. **M16 is narrower than this axiom and does not
  close #16**; #16 stays live until the general statement is proved or explicitly retired.
  **The papers do not apply this statement's shape:** WP (4.5) uses Itô only for `e^s|δY|²` and
  `⟨Gx, y⟩`, with a jump term the paper says has no square moments and handles by the compensation
  formula, and a local-martingale Brownian term; this axiom's `h_jumpInt_sq` / `h_sigmaGrad_sq`
  exclude that use. Nothing here validates the papers' Itô applications; that formula ("D-Itô",
  Epic D) needs local stochastic integrals the tree does not have. The "Applebaum Thm 4.4.7"
  attribution is the Dissertation's tag, not checked against the book's statement (B4-P2).
* **Scope (recorded 2026-09-06; resolved the same day by X2-3, at the end of this bullet).** The
  progressive-measurability hypotheses `h_sigmaGrad_progMeas` / `h_jumpInt_progMeas` are relative to
  the natural filtration of a *single* driver (`naturalFiltration (W.W j)` per Brownian coordinate,
  `naturalFiltration N` alone), because the library's `L²` integrals (`Brownian/MultidimIto.lean`,
  `Poisson/Compensated.lean`) are built on that class. For the same reason
  `JumpDiffusion.is_solution` (`Ito/Setting.lean`) is inhabitable only when `σ(s, X_s) i j` is
  adapted to `ℱ^{W^j}` alone and `γ(s, X_s, e)` to `ℱ^N` alone — i.e. for uncoupled coefficients.
  The cited theorem is stated for integrands adapted to a common filtration to which `W` is a
  Brownian motion and `N` a Poisson random measure (the joint filtration of `(W, N)`); until the
  integrals are generalized to that filtration (X2), #16 is a faithful statement only on that
  restricted scope, and the same restriction affects #13a (whose representing integrands are asked
  to be single-driver adapted while the martingale is a `jointFiltration W N` martingale), #9 and
  #10. **X2-1/X2-2 (2026-09-06)**: the Brownian integrands `h_sigmaGrad_progMeas` are now
  `ProgressivelyMeasurable W.naturalFiltration`, the joint natural filtration of all coordinates of
  `W`, and the Poisson integrand `h_jumpInt_progMeas` is `MarkedProgressivelyMeasurable
  (naturalFiltration N)`; both are genuinely progressive, but for two separate filtrations, so the
  scope restriction stands until X2-3. **X2-3 (2026-09-06) — resolved**: #16 now takes a single
  filtration `ℱ` with `(∀ j, IsBrownianFiltration (W.W j) ℱ)` and `IsPoissonFiltration N ℱ`, and
  both `h_sigmaGrad_progMeas` and `h_jumpInt_progMeas` are progressive for that one `ℱ`; likewise
  `JumpDiffusion.is_solution`, `Ito/Picard*` and `IsBSDEJSolution`. The statement now matches the
  cited theorem's hypothesis (integrands adapted to a common filtration for which `W` is Brownian
  and `N` Poisson), so coupled `(σ, γ)` are in scope. #13a, #9 and #10 stay deleted (A5-1) and
  return as statements to prove.
* **Mathlib status (May 2026)**: No compensated-Poisson integral in Mathlib (waits on PRM construction). The small/large decomposition is itself a derived statement once the integral exists; the `ε → 0` limit uses `itoIsometry_diff_compensated` (Tier 1 #18, in `Poisson/Compensated.lean`).
* **Replacement plan** (Epic B in `../Dissertation/WORK_BREAKDOWN.md`): derive as a theorem —
  the continuous part through an Itô formula for the library's Brownian integral, the jump part
  in-house on `Compensated.stochasticIntegral` via `itoIsometry_diff_compensated`.
* **Progress (B1a-1, 2026-09-06) — the algebra of the `L²` Brownian integral.** The continuous half is a Riemann-sum argument, and the integral as built exposed no algebra to rewrite those sums with: it is a limit of elementary integrals of simple integrands, but nothing said that feeding a *simple* integrand back into it returns the elementary integral it came from, nor how to move an `ℱ`-measurable factor across it. `Brownian/ItoAlgebra.lean` supplies that layer. A simple integrand is progressively measurable (`SimplePredictable.progressivelyMeasurable_eval`) and square-integrable on every window, so it is an admissible integrand; `stochasticIntegralBrownian_eval_simple` identifies its `L²` integral with its elementary integral (both are `L²` limits of the master approximating sequence, using a difference isometry — `simpleIntegral_diff_isometry_of_adapted` — that no longer requires the two horizons to agree); `isometry_simple_sub_stochasticIntegralBrownian` then measures an elementary integral against a general `L²` integral. On top of that, `SimplePredictable.mul_on_common` carries the product of two simple integrands on their common refinement, `sum_xi_mul_simpleIntegral_sub` is the combinatorial identity that summing the increments of one elementary integral against the coefficients of another gives the elementary integral of the product, and `stochasticIntegralBrownian_integralAgainst` passes that to the limit: for `M_t = ∫_0^t H dW` and adapted simple `G`, `∑ᵢ G.ξᵢ (M_{tᵢ₊₁∧t} − M_{tᵢ∧t}) = ∫_0^t G.eval·H dW` a.s. That last identity is what rewrites every Riemann sum in the Taylor expansion. All of it is in `_audit.lean` over the three standard axioms.
* **Upstream survey (2026-09-06, ticket B0 of `../Dissertation/WORK_BREAKDOWN.md`) — the continuous part does NOT port from `formal-mathfin`.** The candidate named in the replacement plan was `MathFin.ito_formula_td_process`. Reading it and its neighbours against #16:
  * `MathFin.ito_formula_td_process` (`Foundations/ItoFormulaProcess.lean`, sorry-free) is Itô's formula for `f(t, B_t)` where `B` is a **single scalar** `IsPreBrownianReal` motion. It assumes six **global** derivative bounds — `|f_t| ≤ C_t`, `|f_x| ≤ C_1`, `|f_xx| ≤ C_2`, `|f_tt| ≤ C_tt`, `|f_tx| ≤ C_tx` and `|f_xxx| ≤ C_xxx` — so `f` is `C³` with a bounded third derivative.
  * `MathFin.ito_formula_itoProcess` (`Foundations/ItoFormulaItoProcess.lean`) is the closest to what #16 needs, but only for a **constant-coefficient** Itô process `X_t = X₀ + b·t + σ·B_t` with scalar `b, σ`, and `f ∈ C³` of at-most-exponential growth. Its own module docstring states the limit: *"general adapted coefficients (the full semimartingale Itô formula, needing the Itô integral against random integrands) remain the open frontier."*
  * `MathFin.ito_formula_unrestricted` / `ItoFormulaUnrestrictedLocMart.lean` package the same `f(t, B_t)` statement with the local-martingale property; they do not widen the class of `X`.
  * There is no Itô formula in `formal-mathfin` for a multidimensional state, for state-dependent coefficients, or at merely `C²`.
  #16 needs `u(t, X_t)` for `u : ℝ → (Fin n → ℝ) → ℝ` with `ContDiff ℝ 2 (uncurry u)` and `X` a jump-diffusion whose coefficients `μ(s, X_s)`, `σ(s, X_s)`, `γ(s, X_s, e)` depend on the state. Each of the four gaps — multidimensional state, state-dependent coefficients, `C²` rather than `C³`-with-bounded-third-derivative, and jumps — is on its own enough to block the port; the second is what `formal-mathfin` itself names as its frontier. **Conclusion: the continuous half of #16 is a proof, not a port**, and the Epic B sizing note that called it a port was wrong. This repo also has no Brownian counterpart of `Poisson/MathFinBridge.lean`, so even the constant-coefficient statement would need a bridge built first.
* **Progress (2026-09-10) — where the discharge stands. The axiom is still live; nothing below
  changes that.** The *continuous* half is complete at the generality #16 needs:
  `Ito/ItoFormulaUnbounded.lean`'s `itoFormula_of_unbounded` is Itô's formula for a `C²` function
  of a multidimensional Itô process with adapted coefficients, with **no** bound on the
  coefficients or on the derivatives (the two obstructions are separated — an `L²` truncation for
  the coefficients, a cutoff at an exit time for the derivatives — and composed through the
  hypothesis-based `IsVectorItoVersion.itoFormula_localise`); `Ito/ItoFormulaStoppedLimit.lean`
  and `Ito/ItoFormulaIncrement.lean` give the stopped form for a general stopping time and the
  increment between two stopping times; `Ito/ItoFormulaTimeUnbounded.lean` gives the
  time-augmented form, which is the one #16's `u : ℝ → (Fin n → ℝ) → ℝ` needs. On the *jump*
  side: `Ito/JumpSplitting.lean` splits a finite-activity jump diffusion as a continuous Itô
  version plus a pathwise jump sum, `Poisson/JumpTimes.lean` makes the arrival times stopping
  times, and `Ito/SmallJumpProcess.lean` carries the `ε → 0` limit (Applebaum 4.4.7 step II) on
  the everywhere-càdlàg modification of `Poisson/CompensatedCadlagMod.lean`, which is what makes
  the big-jump process jointly measurable and hence gives convergence at almost every time.
  **What is still missing**, and why the axiom cannot yet be deleted: the Itô formula for a
  function shifted by an `ℱ_σ`-measurable random vector (the shift is the jump accumulation
  frozen on each inter-jump interval; the `L²` limit from simple to general shifts currently
  needs global bounds on the first two derivatives, which #16 does not assume, so a localisation
  step must remove them again); the telescoped assembly over the arrival times; and the
  dictionary between #16's integrand vocabulary and the Itô machinery's. These are tracked
  leaf-by-leaf as B3a-1d, B3a-2, B3a-3 and B4-0 in `../Dissertation/WORK_BREAKDOWN.md`.
* **Progress (2026-09-10, OB-1) — milestone M16 is assembled with no `sorry`; the axiom is
  still live.** `Ito/ItoLevyBoundedDerivs.lean`'s `itoLevyFormula_jumpResidual_of_boundedDerivs`
  now has a complete proof and leaves `tools/sorry_baseline.txt`; the finite-activity identity
  along each truncated path, in the mixed form, is `Ito/FiniteActivityMixed.lean`'s
  `itoLevy_finiteActivity_mixed`. It telescopes Itô's formula for the *time-augmented* continuous
  part between consecutive capped arrival times (`itoFormula_between_measurableShift` with the
  shift `y(σ_k) − V(σ_k)`, which is known at `σ_k` because both paths are progressive, then
  `itoFormula_chain`), reads the increments across the arrival times as the atom sum of the
  mixed jump increment at the left limits (`sum_range_jumpTerm_eq_sum_atomEnum_of_shift` in
  dimension `n + 1`, with `leftLim_timeAugProcess_eq_cons`), identifies that atom sum with the
  pathwise form of the compensated integral of the left-limit integrand (its zero extension is
  marked predictable by `MarkedPredictable.comp_measurable`; the point-evaluated integrand of the
  statement has the same compensated integral by `compensatedIntegral_congr_of_countable_ne`,
  the two paths being càdlàg), and closes with the mixed dictionary in its almost-every-time
  form (`itoLevy_of_splitDrift_and_jumpSum_mixed_ae`). Two interface changes were needed, both
  recorded here rather than hidden: (i) the five shift formulas (`ItoFormulaGeneralShift`,
  `ItoFormulaGridShift`, `ItoFormulaGridShiftClosed`, `ItoFormulaMeasurableShift`) now ask the
  Hessian bound only against the quadratic covariation density,
  `|∂ₚ∂_q f z| · |∑ₖ H p k H q k| ≤ K₂ · |∑ₖ H p k H q k|`, because the time-augmented
  representative of `u` has unbounded `∂ₜ²u` and `∂ₜ∇u` which never meet the diffusion (its time
  row is zero); the old bound implies the new one in one line, and the conclusions are unchanged;
  (ii) the vector Itô formula between the arrival times used to consume a `CrossWitness`
  (an enlarged filtration for which the coordinate stays Brownian while the other coordinates'
  increments are known), and on 2026-09-10 M16 carried one as an extra hypothesis. **Removed
  2026-09-11 (B4-C12).** `Brownian/CrossOrthogonality.lean` now proves the cross orthogonality
  `E[Z (Wⁱ_b − Wⁱ_a)(Wʲ_b − Wʲ_a)] = 0`, for a bounded `ℱ_a`-measurable `Z`, from the
  per-coordinate Brownian property of `ℱ` and the independence of the coordinates alone
  (`integral_mul_increment_mul_increment_eq_zero`: the product of the two increments telescopes
  along a uniform grid of `[a, b]`, the cell terms with a past factor are killed by conditioning,
  and the cell-wise cross sum has second moment `(b − a)²/m` by `W.components_independent`), and
  the witness binder is gone from the whole chain — `integral_cross_increment_eq_zero`,
  `CrossVariation`, `CrossVariationSum`, `VectorItoQuadVarRiemann`, `VectorItoFormula`, the
  Itô/shift theorems, `PRPMultidimRange`, the driver's joint range,
  `itoLevy_finiteActivity_mixed` and M16 — and the `CrossWitness` structure is deleted. The
  2026-09-10 note that per-coordinate `IsBrownianFiltration` "does not imply it without Lévy's
  characterisation" was wrong. M16's statement is again exactly the approved one: bounded
  `∂ₜu`, `∇u`, `Hess u`, usual conditions on `S.ℱ`, the SDE data at `S.ℱ`, no `L⁴`, and the four
  admissibility hypotheses on the derived integrands (their discharge from the solution data is
  ticket B4-C13).
* **Progress (2026-09-11, B4-C13) — M16 is callable from the solution data.**
  `Ito/ItoLevyBoundedDerivsSolution.lean`'s `itoLevyFormula_jumpResidual_of_solvesOn` takes
  regular Lipschitz coefficients, a right-continuous filtration containing the null sets at time
  zero (the hypotheses of `exists_globalSolution`), a `C²` state function with bounded `∂ₜu`,
  `∇u`, `Hess u` and a horizon, and returns a jump diffusion solving the equation on every window
  relative to that filtration, with progressively measurable coordinates and càdlàg paths at
  every sample point and every time, together with M16's conclusion along it — every
  admissibility input of the two stochastic integrals in the conclusion is a proved lemma of
  that file, not a hypothesis. The inputs are produced as follows: the solution of
  `exists_globalSolution` is replaced by its representative `cadlagRep G X` on a measurable full
  set `G` where the paths are càdlàg (the constant zero path off `G`, the zero state before time
  zero), which has left limits at every sample point and every time (`cadlagRep_leftLim`), is
  adapted because `G` lies in the initial σ-algebra and progressively measurable because it is
  right-continuous everywhere (`progressivelyMeasurable_cadlagRep`), and solves the same window
  equations because the Picard step reads its input only on the class of `P ⊗ ds`
  (`solvesOn_cadlagRep`, from `picardStep_congr_ae` at positive times and
  `ae_picardStep_zero` at time zero); adaptedness is the evaluation of progressive
  measurability (`measurable_of_progressivelyMeasurable`); the drift along the path is
  progressively measurable and of finite energy by composition with the progressive state and
  the linear-growth bound (`progressivelyMeasurable_comp_state`,
  `lintegral_sq_mu_lt_top_of_energy`); `(∇u)ᵀσ` and `u(x + γ) − u(x)` along the path are jointly
  measurable, (marked) progressively measurable and of finite energy by composing the continuous
  gradient with the progressive state and by the gradient bound
  (`measurable_diffusionIntegrand_path`, `progressivelyMeasurable_diffusionIntegrand_path`,
  `lintegral_sq_diffusionIntegrand_path_lt_top`, `measurable_jumpIncrement_path`,
  `markedProgressivelyMeasurable_jumpIncrement_path`, `lintegral_sq_jumpIncrement_path_lt_top`);
  the drift is integrable on the window almost surely (`ae_integrableOn_drift_path`) and the
  compensator-drift integrand is integrable over the marks and the window almost surely by the
  bounded-Hessian Taylor remainder and the jump energy
  (`ae_lintegral_compensatorDriftIntegrand_lt_top`). **M16 is still narrower than this axiom**
  (bounded derivatives); the axiom remains live. **M16 remains narrower than this axiom** (bounded
  derivatives; the axiom asks none), so #16 stays live: Stage 2 (removing the derivative bounds)
  is the open L-group, and the papers' own Itô applications are Epic D. `#print axioms` on the
  finite-activity identity and on M16 lists only the three standard axioms.
* **Statement audit (2026-09-11) — the axiom is under-specified, and the repair.** Lining the
  axiom up against milestone M16 shows the axiom takes an *arbitrary* filtration `ℱ` with `W`
  Brownian and `N` Poisson for it, and asserts the formula with the two integrals taken at that
  `ℱ` — while `JumpDiffusion.is_solution` only says the SDE holds at *some* filtration. Nothing
  in the axiom's statement ties the process to `ℱ`: it is not asked to be adapted to it, and it
  need not solve the equation relative to it. That is a specification defect, not a missing
  proof. The correct statement is the formula for a solution *relative to its own filtration*,
  which is what `BigJump.SdeData` packages. Classifying the eleven hypotheses M16 carries beyond
  the axiom's:
  - **specification repair** — `S : SdeData X` (the equation and the admissibility at the same
    `ℱ` used in the conclusion), and `SdeData.X_prog`, the progressive measurability of the
    path. Adaptedness is part of the literature definition of a solution (Applebaum 6.2.9,
    Ikeda–Watanabe IV) and the structure's own docstring claims it, but no field carried it; it
    is **not** derivable from the equation, since the drift term `∫_0^t μ(s, X_s) ds` is
    `ℱ t`-measurable only once the path already is. Added as a field 2026-09-11;
    `nonempty_sdeData` was deleted with it, being no longer provable from the structure alone.
  - **version convention** — the usual conditions (`[S.ℱ.IsRightContinuous]`, `hℱ0`, `hnull`).
  - **implementation bridges, now derived** — adaptedness of the path from `X_prog`; the drift's
    joint measurability, progressive measurability and window energy from `IsRegular`,
    `IsLipschitz` and `JumpDiffusion.sup_L2`; joint measurability of `γ` from `IsRegular`; the
    four derived-integrand admissibility bundles and the drift and compensator-drift
    integrability from the same. All of these were already proved as standalone lemmas and were
    being applied at the call site; `itoLevyFormula_jumpResidual_of_sdeData` moves them inside
    the theorem, so they are no longer public assumptions.
  - **path-regularity bridge, now derived (2026-09-11)** — left limits of the path at every
    sample point and every time. `JumpDiffusion.cadlag_paths` supplies them only almost surely,
    and M16 asked for them everywhere. `itoLevyFormula_jumpResidual_of_sdeData` now takes the
    càdlàg representative on a measurable full set (`cadlagRep`), which has left limits
    everywhere and carries SDE data at the same filtration (`solvesOn_of_eqn`,
    `solvesOn_cadlagRep`, `SdeData.ofSolvesOn`), and transports the four terms of the formula
    back to the original path — the two stochastic integrals through the difference isometry
    (`multidimIntegral_congr_ae`, `compensatedIntegral_congr_ae`), the two Lebesgue integrals
    pointwise on the full set. The left-limit-carrying form survives as
    `itoLevyFormula_jumpResidual_of_sdeData_of_leftLim`.
  - **traded, not derived** — the coefficient hypotheses `IsRegular` and `IsLipschitz`. The
    axiom assumes the derived-integrand admissibility bundles directly and says nothing about
    the coefficients; the repaired theorem assumes the coefficients are regular and Lipschitz
    and derives the bundles. Neither implies the other, so this is an exchange of hypotheses,
    not a discharge — it is the standing setting of the well-posedness development
    (Applebaum 6.2.9), which is where a solution comes from at all.
  - **genuine narrowing, still open** — the three derivative bounds `hK₀`, `hK₁`, `hK₂`. Only
    these separate M16 from the general statement; removing them is Stage 2 and is what closes
    this axiom. A Stage-2 theorem that kept any of the bridges as hypotheses would **not**
    close it.
* **Progress (2026-09-11, B4-L4) — locality of the compensated integral at a stopping time.**
  `Ito/CompensatedLocality.lean` proves for the compensated Poisson integral what
  `Brownian/ItoLocality.lean` proves for the Itô integral: for a stopping time `τ` of the
  filtration and two admissible marked integrands agreeing at the positive times `s ≤ τ ω`
  (`stochasticIntegral_congr_of_le`) or `s < τ ω` (`stochasticIntegral_congr_of_lt`), the two
  compensated integrals at a time `t > 0` coincide almost surely on `{t ≤ τ}`. The route: the
  integrand cut off at `τ` (`markedStopped τ φ`; jointly and progressively measurable and of
  finite energy via `stoppedSet` / `stoppedRegion`); the increment identity
  `CI(1_{(c,t]} φ)_t = CI(φ)_t − CI(φ)_c` from the martingale property — the integral of an
  integrand vanishing after `c` has the same second moment at `c` and at `t`
  (`stochasticIntegral_ae_eq_of_vanishing_gt`, `stochasticIntegral_indicator_Ioc`); the
  pull-out of the hit indicator `1_{τ = c}` through the integral over `(c, t]`
  (`hitInd_mul_stochasticIntegral_indIoc`, from `MarkedHorizonIntegrand.integral_mulLeft`);
  optional stopping for a stopping time of finite range
  (`stochasticIntegral_markedStopped_finiteRange`: the pathwise decomposition
  `markedStopped_eq_sub_sum`, `stochasticIntegral_sub`, `exists_stochasticIntegral_finsetSum`);
  and the grid approximations `gridStop τ t n ↓ τ` of `Brownian/ItoLocality.lean`, whose
  cut-offs converge to `markedStopped τ φ` in energy by dominated convergence, so that the
  difference isometry `itoIsometry_diff_compensated` squeezes the integrals
  (`stochasticIntegral_markedStopped_eq_of_le`). `#print axioms` on every declaration of the
  file lists the three standard axioms. This supplies the compensated transfer that Stage 2
  (general `u`, the L-group) needs; Stage 2 itself stays open and the axiom stays live.

* **Stage-2 status (2026-09-15) — one genuine gap in the Stage-2 route, the target restated
  with every hypothesis exposed, and the close-out re-planned.** The cut-off machinery of
  B4-L5a–h is in the tree and audited over the three standard axioms: the cut-off
  `cutoffFun₂ u (2m)` has globally bounded `∂ₜ`, `∇`, `Hess` (`Ito/CutoffGlobalBounds.lean`,
  `exists_globalBound_cutoffFun₂`), so M16 applies to it; the whole continuous side transfers on
  `boundedPathSet X T m` (`Ito/CutoffPathAgreement.lean`, `ae_continuousSide_cutoffFun₂_eq`); and
  the jump side transfers as a sum, in the left-limit reference-intensity form
  (`Ito/CutoffJumpTransfer.lean`, `ae_jumpSide_cutoffFun₂_eq`, on `Ito/AtomJumpRelation.lean`,
  `Ito/JumpSideCompensator.lean`). The exit-time overshoot question does not arise: the transfer
  is at the fixed time `T` on the event that the path stays in the closed ball of radius `m` over
  `[0, T]`, on which `T ≤ openExitTime` (`boundedPathSet_subset_le_openExitTime`), and almost
  every path lies in one such event (`ae_exists_mem_boundedPathSet`); nothing is stopped at the
  exit.
  - **Gap G (found 2026-09-14).** `ae_jumpSide_cutoffFun₂_eq` takes `hsplit`: at every level `j`
    of `spanningSets ν`, `X = V + jumpSumLeftAt coeffs N X (spanningSets ν j)` a.s. with `V` a.s.
    continuous. It was taken expecting the splitting lemma
    `ae_forall_eq_add_jumpSumLeftAt_of_path` (`Ito/JumpSplittingPath.lean`) to discharge it. It
    cannot: that lemma needs `γ` supported in the mark set (`hsupp`), so it applies to the
    truncated path with coefficient `markCut A γ` — which is how Stage 1 used it — and not to
    `X`, whose remainder `X − J_A` still carries the jumps outside `A` and is not continuous.
    What `hsplit` buys is the jump relation at the atoms of a finite-intensity mark set,
    `X_θ = X_{θ−} + γ(θ, X_{θ−}, ε)` a.s. at every atom `(θ, ε)` with `ε ∈ spanningSets ν j`
    (`ae_exists_atomEnum_jump_eq_gamma`, `ae_setIntegral_jumpIncrement_sub_eq_zero`). For a
    solution of the SDE this is standard — the compensated small-jump integral has a càdlàg
    version whose jump at a big-jump atom is zero — but it is **not in the tree**: it needs the
    càdlàg modification of the small-jump compensated integral
    (`Poisson/CompensatedCadlagMod.lean`) and Doob's `L²` maximal inequality
    (`Probability/DoobContinuous.lean`) to control the small-jump remainder uniformly in time
    along the truncation `markCut (spanningSets ν k)ᶜ γ`, `k → ∞`. The note of 2026-09-13
    (`../Dissertation/WORK_BREAKDOWN.md`, "no missing mathematics is known") was wrong. Every
    lemma conditioned on `hsplit` compiles over the three standard axioms and **none of them is
    a proof of the jump relation for `X`**; they are conditional until `hsplit` is proved and
    removed from their statements.
  - **The target (the statement that closes this entry; nothing narrower does).** For
    `X : JumpDiffusion W N coeffs x₀` with SDE data `S : SdeData X` (the equation, the
    coefficient bundles and `X_prog` at one filtration `S.ℱ` — corrections 3 and 8), the usual
    conditions on `S.ℱ` (`[S.ℱ.IsRightContinuous]`, `hℱ0`, `hnull` — a version convention), the
    mark space countably generated with measurable singletons (correction 1), the coefficients
    jointly Borel measurable (corrections 5 and 6: `Measurable (uncurry μ)`,
    `Measurable (uncurry σ)`, `Measurable fun q => γ q.1 q.2.1 q.2.2`), the drift of finite
    window energy along the path (correction 5, `hμq`), `u` jointly `C²`, `T > 0`, and the
    three admissibility inputs this axiom itself assumes — `h_sigmaGrad_sq`, `h_jumpInt_sq`
    (finite window energy of `(∇u)ᵀσ(s, X_s)` and of `u(s, X_s + γ) − u(s, X_s)`) and
    `h_compDrift_int` — the conclusion is this axiom's four-term identity with both stochastic
    integrals at `S.ℱ`, their joint and progressive measurability derived
    (`measurable_diffusionIntegrand_path`, `progressivelyMeasurable_diffusionIntegrand_path`,
    `measurable_jumpIncrement_path`, `markedProgressivelyMeasurable_jumpIncrement_path`) and the
    drift's window integrability derived from `hμq`. **No** global bound on `∂ₜu`, `∇u`,
    `Hess u`; **no** bound on the jump sizes `‖γ‖` (correction 7 is withdrawn from the target;
    it is not the cited theorem's hypothesis); **no** `IsLipschitz` and **no** growth bound on
    the coefficients (of `IsRegular` only the three measurability conjuncts survive); **no**
    moment assumption beyond `JumpDiffusion.sup_L2` and the energies above. A theorem carrying
    any of those is a milestone, not the closure.
  - **Distance from the current milestone.** `itoLevyFormula_jumpResidual_of_sdeData` differs
    from the target in the three derivative bounds *and* in `hReg`/`hLip`, which it uses only to
    derive the window energies of `μ`, `σ`, `γ` along the path
    (`lintegral_sq_mu_lt_top_of_energy` and siblings) and inside `solvesOn_cadlagRep`; those
    energies are `SdeData.σ_sq`/`γ_sq` and `hμq` directly, so this is a hypothesis trade (M2),
    not new mathematics. The 2026-09-13 report that only the three bounds separated M16 from
    the axiom understated this.
  - **Close-out order (decision 2026-09-15).** *Z1a, next:* delete the axiom now — it cannot be
    proved as stated, its `ℱ` being unrelated to the solution's — and replace its two consumers
    and the Dissertation forwarder by the bounded-derivative theorem under a name that says so,
    with the `SdeData` hypotheses and the three bounds exposed; empty
    `tools/axiom_allowlist.txt`; re-head this entry as **open** (neither a live axiom nor
    proved) until the target is a theorem. Deleting an unprovable axiom is clean-up, not the
    closure. *M1:* the jump relation at the atoms for a solution, then `hsplit` deleted from
    `ae_jumpSide_cutoffFun₂_eq` and its dependents. *M2:* the trade above, and the point-value ↔
    left-limit and iterated ↔ reference-intensity transfers of the `u`-hypotheses
    (`Ito/JumpIntegrandLeftLim.lean`, `integral_window_eq_and_integrableOn`). *M3:* the assembly
    — M16 at the cut-off, the two transfers, the conventions, exhaustion in `m`
    (`ae_exists_mem_boundedPathSet`). *M4 = B4-Z1b/Z2:* delete the seven-`sorry`
    `Ito/JumpFormulaAssembled.lean`, re-point `itoLevyFormula` and Cu03 at the target, ledger
    and Dissertation close-out. Progress reports name the obligation discharged, not line or
    commit counts.

* **Z1a (2026-09-15) — the axiom is deleted; the entry stays open.** `Ito/JumpFormula.lean` no
  longer declares `itoLevyFormula_jumpResidual_canonical_axiom`, nor the two theorems derived
  from it (`itoLevyFormula_jumpResidual_axiom`, `itoLevyFormula`), whose statements were the
  axiom's — at an arbitrary filtration `ℱ` unrelated to the solution's (correction 8) and with
  no adaptedness of the path to it (correction 3) — and so were unprovable with it. The module
  keeps the integrand vocabulary. The four-term formula the dissertation forwards is now
  `itoLevyFormula_of_boundedDerivs` (`Ito/ItoLevyBoundedDerivsSolution.lean`): the conclusion of
  `itoLevyFormula_jumpResidual_of_sdeData` rearranged, so it carries that theorem's hypotheses —
  SDE data at one filtration with the usual conditions, regular Lipschitz coefficients, and the
  three derivative bounds — and lists only the three standard axioms under `#print axioms`.
  `tools/axiom_allowlist.txt` is empty and `tools/import_contract.md` row 67 points at the new
  theorem (module 13). The deletion is its own dependency check: with the axiom and its two
  derived forms removed, both repositories build, so no remaining declaration depended on it;
  the only consumer outside this library was the dissertation forwarder
  `Dissertation.Continuous.itoLevyFormula` (no dissertation proof applied it), restated as the
  forwarder of the bounded-derivative theorem. No proved result lost support. **This does not close #16**: the target
  statement above is unproved, and the entry stays open until M1–M4 deliver it.

* **M1 (2026-09-15) — gap G is closed: the jump relation at the arrival times is a theorem for
  a solution, and `hsplit` is gone.** `Ito/JumpSplittingRemainder.lean`. A path satisfying the
  equation is, at every nonnegative time, the vector Itô process with drift
  `continuousDriftLeftAt`, plus the left-limit jump sum over a mark set of finite intensity, plus
  the compensated integral of the left-limit jump coefficient cut to the complement of that set —
  the *remainder* (`eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path`,
  `ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path`): no support restriction on `γ`; the
  remainder carries the jumps outside the set and is càdlàg, being a compensated integral. Across
  an arrival time the path jumps by the jump coefficient at its left limit plus the jump of the
  remainder (`ae_exists_atomEnum_jump_eq_gamma_add_remainder`). Along a subsequence of the
  spanning sets of `ν`, the remainders of a finite family of integrands are almost surely
  eventually smaller than any bound at every time of `[0, T]`
  (`ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt`): Doob's `L²`
  maximal inequality for the càdlàg martingale (`Probability/DoobContinuous.lean`) against the
  Itô–Lévy isometry, whose right side is the energy of the cut integrand and tends to zero by the
  small-jump limit of `Ito/StochasticIntegralLimit.lean`. Hence, for a jump diffusion with SDE
  data under the usual conditions whose drift and left-limit jump coefficient are admissible with
  marked predictable zero extension, the increment across each arrival time carrying a mark of a
  spanning set is exactly the jump coefficient at the left limit
  (`ae_exists_atomEnum_jump_eq_gamma_of_sdeData`): an arrival of the smaller set is an arrival of
  every larger one, the relation with remainder holds at every level of the subsequence, and the
  remainder's jump is bounded by twice its uniform bound, so the discrepancy lies below every
  positive number. `ae_setIntegral_jumpIncrement_cutoffFun₂_eq`,
  `ae_setIntegral_jumpIncrement_sub_eq_zero` and `ae_jumpSide_cutoffFun₂_eq` now take that
  arrival-time relation as hypothesis in place of `hsplit`; nothing in the Stage-2 chain assumes a
  continuous remainder any more. `#print axioms` lists the three standard axioms for all six
  declarations. **Still open**: M2 (the hypothesis trade and the convention transfers) and M3
  (the assembly); this entry stays open.

* **M2, first half (2026-09-15) — the Lipschitz and growth conditions are gone from the
  bounded-derivative chain.** `Ito/ItoLevyBoundedDerivsSolution.lean`:
  `itoLevyFormula_jumpResidual_of_sdeData_of_leftLim` and `itoLevyFormula_jumpResidual_of_sdeData`
  now take the joint measurability of `μ`, `σ`, `γ` and the window energy of `μ` along the path
  (`hμmeas`, `hσmeas`, `hγmeas`, `hμq`) in place of `IsRegular` and `IsLipschitz`; the energies of
  `σ` and `γ` along the path are the `SdeData` fields, and along the càdlàg representative they are
  the same numbers (`lintegral_sq_comp_cadlagRep`, `lintegral_sq_marked_comp_cadlagRep`), so
  `solvesOn_cadlagRep` takes the energies along the original path instead of deriving them from
  a growth bound. `itoLevyFormula_of_boundedDerivs`, the four-term form the dissertation forwards,
  keeps its signature (`IsRegular`, `IsLipschitz`) as a corollary: those hypotheses are now consumed
  only to produce the drift energy. What separates the traded theorem from the target is the three
  derivative bounds alone. The second half of M2 — the point-value/left-limit and
  iterated/reference-intensity transfers of the `u`-hypotheses — is done inside M3.

* **M3 and M4 (2026-09-15) — the general Itô–Lévy formula is a theorem; the entry is resolved.**
  `Ito/ItoLevyFormulaGeneral.lean`. `itoLevyFormula_general` states, for a jump diffusion `X`
  carrying `SdeData` at a right-continuous filtration `ℱ` whose time-zero σ-algebra contains the
  null sets, jointly measurable `μ`, `σ`, `γ`, the window energy of `μ` along the path, a jointly
  `C²` state function `u`, a horizon `T > 0`, and the three admissibility inputs of the target —
  the window energies of `(∇u)ᵀσ` and of `u(x + γ) − u(x)` along the path, and the almost-sure
  integrability of the compensator-drift integrand over `[0, T] × E` — that
  `u(T, X_T) − u(0, X_0) = drift + Brownian + compensated + compensator-drift` almost surely,
  both stochastic integrals taken at `ℱ`. No bound on `∂ₜu`, `∇u`, `Hess u`; no Lipschitz or
  growth condition on the coefficients; no jump-size bound. This is the target recorded under
  "Stage-2 status" above, hypothesis for hypothesis. Proof: the bounded-derivative formula
  (`itoLevyFormula_jumpResidual_of_sdeData_of_leftLim`, after M2) at the cut-off
  `cutoffFun₂ u (2m)`, whose derivatives are globally bounded (`Ito/CutoffGlobalBounds.lean`);
  on the event `boundedPathSet X T m` that the path stays in the closed ball of radius `m` over
  `[0, T]`, the endpoints, the drift integral and the Brownian integral of the cut-off agree
  with those of `u` (`ae_continuousSide_cutoffFun₂_eq`), and the compensated integral plus the
  compensator drift of the cut-off agree with those of `u` as a sum
  (`ae_jumpSide_cutoffFun₂_eq`, through the arrival-time jump relation of M1 and the locality of
  the compensated integral at the exit time); the point-value and left-limit conventions of the
  jump terms agree because a càdlàg path has countably many jumps
  (`compensatedIntegral_congr_of_countable_ne`, `setIntegral_congr_of_countable_ne`), and the
  iterated and reference-intensity forms of the compensator drift agree by Fubini
  (`integral_window_eq_and_integrableOn`); almost every path stays in some ball of radius
  exceeding the horizon (`ae_exists_mem_boundedPathSet`), which exhausts `m`. Along a solution
  with càdlàg paths at every sample point this is
  `itoLevyFormula_jumpResidual_of_sdeData_general_of_leftLim`; for a general jump diffusion the
  identity is transported through the càdlàg representative `cadlagRep`
  (`itoLevyFormula_jumpResidual_of_sdeData_general`), the admissibility inputs being the same
  numbers along the representative (`lintegral_sq_comp_cadlagRep` and its marked sibling).
  `#print axioms` on all three lists `{propext, Classical.choice, Quot.sound}`; no `sorryAx`.
  Close-out (M4): `Ito/JumpFormulaAssembled.lean` (the seven-`sorry` canonical assembly) is
  deleted and `tools/sorry_baseline.txt` is empty; `tools/import_contract.md` row 67 and the
  dissertation forwarder Cu03 (`Dissertation.Continuous.itoLevyFormula`) point at
  `itoLevyFormula_general` with the hypotheses above and no derivative bound;
  `itoLevyFormula_of_boundedDerivs` stays in the tree as the milestone the proof is built on.
  What the theorem does not do: it takes the admissibility of the derived integrands as
  hypotheses (as the deleted axiom did) rather than deriving them from growth conditions on `u`
  and the coefficients — a growth-condition corollary would be a separate statement — and it is
  stated at the solution's `SdeData` filtration, not at an arbitrary one (correction 8).

### Resolved #17: `LevyStochCalc.Brownian.Ito.itoIsometry_diff_brownian` (proved axiom→theorem 2026-06-17)

* **Statement**: For two jointly-measurable, progressively-measurable, square-integrable integrands `H₁, H₂ : Ω → ℝ → ℝ`, the L² norm of the difference of their Brownian Itô integrals at any `T > 0` equals the L² norm of the integrand difference: `𝔼 |∫_0^T H₁ dW − ∫_0^T H₂ dW|² = 𝔼 ∫_0^T |H₁(s) − H₂(s)|² ds`.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 3.2.6** + §3.2.B.
* **Status**: No longer an axiom — proved as a `theorem` in `Ito/Picard.lean`, forwarding to `isometry_diff_stochasticIntegralBrownian` (`Brownian/ItoL2Completion.lean`). This was unblocked by making `stochasticIntegral := stochasticIntegralBrownian` a genuine `L²`-limit construction (rather than `Classical.choose` on #5): both the integral difference and the integrand difference are realized as `L²`-limits of the same simple-integral difference sequence (`masterApprox_cross_diff_isometry`), and `tendsto_nhds_unique` equates the two limits. The consumer `picardStep_diffusion_diff_lipschitz_sq_componentwise` (`Ito/Picard.lean`) is unchanged.
* **Integrand-class caveat (2026-09-06) — resolved the same day (X2-1)**: the original `h_progMeas` hypothesis admitted only integrands a.s. constant in `ω` for each time (see "Integrand-class audit" below). The theorem is now stated for `Probability.ProgressivelyMeasurable ℱ H` (genuine progressive measurability, equivalent to Mathlib's `IsStronglyProgressive`) with respect to any filtration `ℱ` for which `W` is a Brownian motion (`IsBrownianFiltration W ℱ`), and `stochasticIntegral` takes `(ℱ, hℱ)` as arguments; the proof was re-run over that class without any change to the analytic argument. `#print axioms` still lists only the three standard axioms.

### Resolved #18: `LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated` (proved axiom→theorem 2026-09-06; added 2026-05-23, documented 2026-05-27)

* **Statement**: For two jointly-measurable, progressively-measurable, square-integrable integrands `φ₁, φ₂ : Ω → ℝ → E → ℝ`, the L² norm of the difference of their compensated-Poisson Itô-Lévy integrals at any `T > 0` equals the L² norm of the integrand difference: `𝔼 |∫_0^T ∫_E φ₁ Ñ − ∫_0^T ∫_E φ₂ Ñ|² = 𝔼 ∫_0^T ∫_E |φ₁(s, e) − φ₂(s, e)|² ν(de) ds`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.2.3** step (II) (the L²-Itô-Lévy integral is a linear isometry from the predictable `H²` space `L²(Ω × [0, T] × E, dP ⊗ ds ⊗ dν)` to `L²(Ω, ℱ_T, P)`; the per-difference identity is the linear-isometry property applied to `(φ₁ − φ₂)`); Ikeda–Watanabe **Section II.3** for the same construction.
* **Status**: No longer an axiom — proved as a `theorem` in `Poisson/Compensated.lean`, statement unchanged, forwarding to `process_sub_lintegral_sq` (`Poisson/CompensatedDiff.lean`): the stage approximants of the two integrands are refined to a common dyadic grid (`MarkStep.integral_dyadicRefine`: a refined adapted integrand has a.e. the same integral at every time, by the martingale property from the common horizon), where the same-grid difference isometry `MarkStep.lintegral_integral_sub_sq_at` holds at every time; both sides pass to the limit in `L²` (`tendsto_lintegral_nnnorm_sq_of_eLpNorm`) and `tendsto_nhds_unique` equates the limits; the integrals are modifications of the processes (`stochasticIntegral_ae_eq_process`). `#print axioms` lists only the three standard axioms. The per-difference isometry is used downstream by the γ-side Picard contraction estimate (`picardStep_jump_diff_lipschitz_sq_componentwise` in `Ito/Picard.lean`) and by the `ε → 0` limit in the Itô-Lévy formula jump residual axiom (Tier 1 #16).
* **Mathlib status (May 2026)**: blocked on Mathlib gaining a compensated-Poisson L²-integral (waits on a PRM construction; in-tree, #2 is a theorem since 2026-09-06). No current Mathlib activity in this direction.
* **Replacement plan**: `theorem itoIsometry_diff_compensated := <linearity ∘ isometry>` when Mathlib gains a compensated-Poisson L²-integral as a continuous linear map.
* **Integrand-class caveat (2026-09-06) — resolved the same day (X2-2)**: the original `h_progMeas` hypothesis admitted only integrands a.s. constant in `ω` for each time (see "Integrand-class audit" below). The theorem is now stated for `Probability.MarkedProgressivelyMeasurable ℱ φ` (genuine progressive measurability of the marked integrand) with respect to any filtration `ℱ` for which `N` is a Poisson random measure (`IsPoissonFiltration N ℱ`), and `stochasticIntegral` takes `(ℱ, hℱ)` as arguments; the proof was re-run over that class without any change to the analytic argument. `#print axioms` still lists only the three standard axioms.

### Retired #12: `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` (DEMOTED axiom→theorem 2026-05-26)

* **Statement**: Under Lipschitz hypothesis on `(μ, σ, γ)`, the jump-diffusion SDE `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)` with `X_0 = x_0` admits a strong solution (with càdlàg paths, L²-sup-bounded on every bounded interval) that is a.s. unique.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 6.2.9**; Ikeda-Watanabe, *Stochastic Differential Equations and Diffusion Processes*, North-Holland 1989, Chapter IV.
* **2026-05-23 refactor + axiomatization (COMPLETED)**: the theorem moved out of `Ito/Setting.lean` and into `Ito/PicardFixedPoint.lean`, where it forwards through a SINGLE intermediate `picardFixedPoint_jumpDiffusion_exists_unique` (the SDE-specialised Banach fixed-point output). That intermediate was previously a `theorem` with a `sorry` body; it was converted on 2026-05-23 to a thin forwarder over the (then-)Tier-1 axiom `picardFixedPoint_jumpDiffusion_exists_unique_axiom`. On 2026-05-26 the axiom was further demoted to a theorem (forwarding through the wrap-up `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` in `PicardSpace.lean`, which carries a single explicit baseline `sorry`). Consequently `JumpDiffusion.exists_unique` is sorryAx-baselined (via the wrap-up) — its transitive axiom dependency now surfaces `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`'s sorry rather than a standalone axiom. The qualified name `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` is preserved by re-opening the namespace in `PicardFixedPoint.lean`.
* **Signature strength**: requires `JumpDiffusionCoeffs.IsLipschitz coeffs ν L` (Tanaka's `|X|^α` counterexample for α < 1/2 rules out uniqueness without this).
* **Mathlib status (May 2026)**: No SDE-with-jumps strong existence/uniqueness in Mathlib. Continuous-SDE strong existence is partially formalized but the jump-SDE case waits on the multidim Brownian + compensated-Poisson integral infrastructure.
* **CLOSED 2026-09-07**: the chain is proved end to end. Picard iteration on the Bielecki-weighted process space gives a fixed point on each window (`exists_solvesOn`); the contraction gives uniqueness on a window (`ae_eq_of_solvesOn`); right-continuity upgrades per-time agreement to whole-path agreement, so the window solutions glue along `⌈t⌉₊` into a solution on `[0, ∞)` (`exists_globalSolution`); that solution populates every field of `JumpDiffusion` (`jumpDiffusionOfSolvesOn`). `#print axioms LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` = `[propext, Classical.choice, Quot.sound]`.
* **Statement audit (2026-09-07), two items.**
  1. *Filtration scope.* Uniqueness is now asserted against competitors satisfying the equation relative to the SAME filtration (`Ito.Picard.SolvesOn`), and the usual conditions on `ℱ` (right-continuity, `ℱ 0 ≤ ℱ t` for `t ≤ 0`, null sets in `ℱ 0`) are hypotheses. `JumpDiffusion.is_solution` quantifies the filtration existentially, so two `JumpDiffusion`s can carry incomparable Brownian filtrations; the `L²` Itô isometry that powers the Gronwall step exists only within one filtration, and a join of two Brownian filtrations need not be Brownian (take `U` a fair coin independent of `W` and `V = U · sign(W_1)`: each of `σ(U)`, `σ(V)` is independent of `W`, but `σ(U, V)` determines `sign(W_1)`). Applebaum 6.2.9 and Ikeda–Watanabe IV fix the filtered space; the existential form of uniqueness is outside both the literature scope and the method.
  2. *Parse bug in `is_solution`, fixed.* The drift term was written `+ ∫ s in Set.Icc 0 t, coeffs.μ s (X s ω) i` with the two stochastic integrals on the following lines. Mathlib's `∫ x in s, ·` notation parses its body at level 60 and `+` sits at 65, so the body swallowed both stochastic integrals: the field asserted `X t = x₀ + ∫₀ᵗ (μ(s, X_s) + ∫σ dW + ∫γ dÑ) ds`, i.e. `x₀ + ∫μ + t·(∫σ dW + ∫γ dÑ)`, not the SDE. The drift integral is now parenthesised. Nothing depended on the old form (the only producer of a `JumpDiffusion` was the sorry-bodied theorem), so no downstream result changes. A repo-wide scan found no other occurrence.

### Retired #13: `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom` (DEMOTED axiom→theorem 2026-05-26)

**Deleted 2026-09-06 (`7dad5c2`)** together with #13a, on which the derived theorem was built;
what follows is the record of the 2026-05-26 decomposition.

On 2026-05-26 this axiom was demoted to a Lean `theorem` derived from a
DECOMPOSITION into two strictly narrower Tier 1 sub-axioms (#13a + #13b
below). The downstream-facing `jacodYor_representation` theorem is
unchanged (still a thin forwarder; now over the derived theorem rather
than over the previously-monolithic axiom).

**Why the demotion**: the previous single axiom #13 conflated two
independent classical results — the deep PRP content of Jacod 1976 and
the standard classical bridge from L² random variables to càdlàg L²
martingales. Splitting them surfaces where the actual mathematical
difficulty lies (#13a) and pulls the bridge (#13b) into a narrower
form that bottoms out in three independent Mathlib targets (Doob L²
càdlàg regularization, Blumenthal 0-1 for the joint (W, N) filtration,
condExp reproducibility — the last is already in Mathlib).

**Original statement** (recoverable from git history prior to commit
demoting #13): every L²-integrable `((⨆ i, naturalFiltration W_i) ⊔
naturalFiltration N).rightCont.seq T`-measurable random variable
`ξ : Ω → ℝ` admits a representation `ξ = E[ξ] + ∫_0^T Z_s · dW_s +
∫_0^T ∫_E U_s(e) Ñ(ds, de)` a.s., with progressively-measurable
square-integrable integrands `Z, U`, where the Brownian and
compensated-Poisson integrals are pinned to
`MultidimBrownianMotion.stochasticIntegral W Z ...` and
`Compensated.stochasticIntegral N U ...` respectively.

**Reference (original)**: Jacod, J. "Multivariate point processes:
predictable projection, Radon-Nikodym derivatives, representation of
martingales", Z. Wahrsch. Verw. Gebiete 31(3), 1975, pp 235-253;
Jacod-Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed.,
Springer 2003, **Theorem III.4.34**.

### Retired #13a: `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_PRP_martingale_axiom` (RETIRED 2026-09-06 — statement refutable; DELETED)

* **Statement audit (2026-09-06)**: the martingale `M` was one of the joint filtration `((⨆ i, ℱ^{W^i}) ⊔ ℱ^N).rightCont`, but the representing integrands were required to be progressively measurable for the natural filtration of a *single* driver (`Z i` for `ℱ^{W^i}`, `U` for `ℱ^N`) — the only class the library's `L²` integrals accept. Refutation (`d = 1`, `0 < ν(A) < ∞`, `W ⟂ N` as in the product construction): `M_t = W_t · Ñ_t([0, t] × A)` is a càdlàg `L²` martingale of the joint filtration; if `M_T = I_W(Z)_T + I_N(U)_T` with `Z` `ℱ^W`-adapted and `U` `ℱ^N`-adapted, then `I_W(Z)_T` is `σ(W)`-measurable and `I_N(U)_T` is `σ(N)`-measurable, so `𝔼[M_T I_W(Z)_T] = 𝔼[W_T I_W(Z)_T] 𝔼[Ñ_T] = 0` and likewise `𝔼[M_T I_N(U)_T] = 0`, whence `𝔼[M_T²] = 0`, contradicting `𝔼[M_T²] = T · Tν(A) > 0`. (For `d ≥ 2` and no jumps, `M = W¹ W²` refutes it likewise.) The axiom and the derived `jacodYor_representation_axiom` / `jacodYor_representation` were deleted. The cited theorem (Jacod–Shiryaev III.4.34) is for integrands adapted to the joint filtration of an independent pair `(W, N)`; it returns with work package X2. Note also that no statement of this file assumed `W ⟂ N`; the corrected statements will take the pair as a Lévy driver bundle.

* **Statement**: For every L²-bounded càdlàg martingale `M` on the joint right-continuous filtration `ℱ = ((⨆ i, σ(W_i)) ⊔ σ(N)).rightCont`, there exist progressively-measurable square-integrable integrands `Z, U` such that `M_t = M_0 + ∫_0^t Z_s · dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)` a.s. at every `t ∈ [0, T]`. Both stochastic integrals are pinned to `MultidimBrownianMotion.stochasticIntegral` and `Compensated.stochasticIntegral` (canonical forms).
* **Reference**: Jacod, J. (1975/76) Z. Wahrsch. Verw. Gebiete 31(3); Jacod-Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer 2003, **Theorem III.4.34** (stated in EXACTLY the martingale-input form of this sub-axiom — the conditional-expectation construction for a generic L² random variable is handled separately by #13b below).
* **Narrowness**: this is the LITERAL content of Jacod-Shiryaev III.4.34. It is the deep mathematical content of the two-source martingale representation theorem. No conditional-expectation / Doob-regularization step appears — those are factored out into #13b.
* **Mathlib status (May 2026)**: No predictable projection / chaos decomposition in Mathlib for general (W, N) filtrations. Continuous-Brownian-only chaos decomposition is partially in `Mathlib.Probability.Process.WienerChaos` (early-stage at time of writing).
* **Replacement plan**: `theorem jacodYor_PRP_martingale_axiom := <predictable projection + chaos decomposition>` when (a) Tier 1 #5 + #6 are theorems, (b) the projection / decomposition apparatus is built.

### Resolved #13b: `LevyStochCalc.BSDEJ.MartingaleRepresentation.condExp_to_PRP_martingale_form` (proved axiom→theorem 2026-09-06)

* **Statement**: For every L² random variable `ξ : Ω → ℝ` that is `ℱ_T`-measurable on the joint right-continuous (W, N) filtration, there exists a càdlàg L²-bounded `ℱ`-martingale `M` with `M_0 = ∫ ξ ∂P` a.s. (the deterministic expectation) and `M_T = ξ` a.s.
* **Reference**: Karatzas-Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem I.3.13** (Doob L² càdlàg regularization for right-continuous filtrations); Karatzas-Shreve **Theorem 2.7.17** (Blumenthal 0-1 for the Brownian factor, giving `𝔼[ξ | ℱ_0] = ∫ ξ ∂P` a.s.); Applebaum **Theorem 2.3.7** (analog Blumenthal-style 0-1 for Poisson random measures); Mathlib's `MeasureTheory.condExp_of_stronglyMeasurable` (condExp reproducibility, `𝔼[ξ | ℱ_T] = ξ` a.s.).
* **Narrowness**: this is a STANDARD CLASSICAL BUNDLE of three independent results: (1) Doob L² càdlàg modification on a right-continuous filtration, (2) Blumenthal 0-1 for the joint (W, N) filtration, (3) conditional-expectation reproducibility. Each has independent Mathlib activity / formalization roadmap. The bundle is strictly narrower than the original #13 because it does NOT require any chaos decomposition / predictable projection machinery — only classical martingale + filtration analysis.
* **Mathlib status (May 2026)**: Doob L² càdlàg regularization is NOT yet in Mathlib but is on the roadmap (independent of BM construction; requires only `MeasureTheory.Martingale` + `Filtration.IsRightContinuous`). Blumenthal-for-BM waits on the BM construction (Tier 1 #1). `MeasureTheory.condExp_of_stronglyMeasurable` is already in Mathlib.
* **Replacement plan (executed)**: `theorem condExp_to_PRP_martingale_form := <Doob L² càdlàg modification ∘ Blumenthal 0-1 ∘ condExp_of_stronglyMeasurable>`; the three pieces were built in-house rather than waited for.
* **Status**: No longer an axiom — proved as a `theorem` in `BSDEJ/MartingaleRepresentation.lean`, statement unchanged (the `_axiom` suffix is dropped). `#print axioms` lists only `propext, Classical.choice, Quot.sound`. The witness is `LevyDriver.cadlagCondExp` (`Driver/CadlagMartingale.lean`): the `ℝ≥0`-indexed right-continuous modification of `t ↦ 𝔼[ξ | ℱ₊ t]`, extended by the constant `𝔼 ξ` before time `0`. The three pieces:
  1. **Doob `L²` càdlàg regularisation.** `Probability/CondExpModification.lean` builds the modification through `ProbabilityTheory.rightContModif` of the `BrownianMotion` dependency. Its hypothesis `IsRealQuasimartingale` is supplied by `Probability/Quasimartingale.lean` (`isRealQuasimartingale_of_martingale`, variation bound `0`) because the dependency's own `Martingale.isRealQuasimartingale` is a `sorry`; its other hypothesis, convergence in measure from the right, comes from the downward `L²` convergence of conditional expectations along a decreasing chain of σ-algebras (`Probability/ProjectionLimit.lean`, `Probability/AEMeasurableInf.lean`, `Probability/CondExpInf.lean`, `Probability/CondExpRightContinuous.lean`) — a statement Mathlib has only in the upward direction. `rightContModif`, not `cadlagModif`, is used: the latter needs a complete filtration, which `jointFiltration D` is not.
  2. **Blumenthal 0-1 for the joint filtration.** `Driver/GermIndep.lean`,
     `isTrivialSigma_rightCont_zero`. The chain is `Driver/VectorIncrement.lean` (the whole mixed
     increment tuple of one interval against `ℱ_s`, which does *not* follow from the per-coordinate
     `IsBrownianFiltration`), `Driver/GridIncrement.lean` (the grid induction),
     `Driver/ValueSigma.lean` (the limit `s ↓ 0`), and the finite-subfamily assembly. The Poisson
     half needed the two-sided region independence of `Poisson/RegionIndependence.lean` and
     `Poisson/RegionPartition.lean`. Not the cited Karatzas–Shreve/Applebaum statements, which are
     for a single driver: the joint version is a theorem of `Driver/GermIndep.lean`.
  3. **Conditional-expectation reproducibility.** Mathlib's `condExp_of_stronglyMeasurable`, as planned.
* **Statement audit (2026-09-06)**: not refuted. The càdlàg modification along rational right limits is measurable for the right-continuous joint filtration without completion, so adaptedness holds as stated; the `M_0 = 𝔼 ξ` clause is the 0-1 law of `ℱ_{0+}` for the *joint* filtration, which is the cited fact only when `W` and `N` are independent — a hypothesis this file never states (`W` and `N` are separate structures on one probability space). **X2-3 (2026-09-06) — fixed**: the axiom now takes a `LevyDriver D` (`Driver/Joint.lean`), whose `indep` field is exactly `σ(W) ⟂ σ(N)`, and is stated over `jointFiltration D = D.filtration.rightCont`; the coordinates of `D.W` are Brownian and `D.N` Poisson for that filtration (`LevyDriver.isBrownianFiltration`, `.isPoissonFiltration`, lifted by `.rightCont`).

### Retired #14: `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom` (DELETED 2026-09-07)

* **CLOSED 2026-09-07 (`ba5e214`)**: the Picard chain is proved end to end, so the wrap-up's
  `sorry` is gone and both intermediates (`..._axiom` and `..._via_aeQuot`) were deleted as
  redundant. What survives is `Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique`
  (`Ito/PicardFixedPoint.lean`) over `Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn`
  (`Ito/PicardWellPosed.lean`), on the three standard axioms. Everything below this bullet is
  the record of the 2026-05-26 to 2026-09-07 interval, when the chain still carried a `sorry`;
  its present-tense claims about `tools/sorry_baseline.txt` describe that interval, not the
  current tree. The statement audits in it (C0/C0a/C0b/C0c-ii, and the A6-1 filtration
  narrowing) do describe the current statement and are the reason to read the entry.

On 2026-05-26 this axiom was demoted to a Lean `theorem` forwarding through
the wrap-up `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` in
`LevyStochCalc/Ito/PicardSpace.lean`. The wrap-up theorem
carries a SINGLE explicit `sorry` collecting the entire literature Picard
chain (Applebaum 6.2.9 / Ikeda-Watanabe IV); the per-step status is in
that file's section note "Status of the fixed-point programme".

**Statement audit (survey C0, 2026-09-06) — the wrap-up statement is refutable, so the `sorry` cannot be discharged as it stands.** `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` asks, from `JumpDiffusionCoeffs.IsLipschitz coeffs ν L` alone, for a `JumpDiffusion W N coeffs x₀`. `IsLipschitz` constrains `(μ, σ, γ)` only in the state variable `x`; it says nothing about their dependence on `s`, or, for `γ`, on `e`. But the `is_solution` field of `JumpDiffusion` existentially bundles joint measurability, progressive measurability and the `L²` bounds of `(s, ω) ↦ σ(s, X_s ω)` and `(ω, s, e) ↦ γ(s, X_s ω, e)`, since the two stochastic integrals need them to be well-typed. Two coefficient families satisfy `IsLipschitz` with `L = 0` and admit no `JumpDiffusion` at all: (i) `n = d = 1`, `μ = γ = 0`, `σ s x = 1 / s` — every Lipschitz clause reads `0 ≤ 0`, but `∫⁻ s in Icc 0 T', ‖1/s‖₊² = ∞` for every `T' > 0`, so `h_σ_sq` fails for every path map; (ii) the same with `σ s x = 1_A s` for a non-measurable `A ⊆ ℝ` — the preimage `Set.univ ×ˢ A` has `ω`-sections `A`, so `h_σ_meas` fails for every path map. The whole forwarder chain down to `JumpDiffusion.exists_unique` inherits the defect. The correction is to add (a) joint measurability of `(s, x) ↦ μ s x`, `(s, x) ↦ σ s x`, `(s, x, e) ↦ γ s x e`, and (b) local square integrability in `s` at one state, `∫⁻ s in Icc 0 T', ‖σ s 0‖₊² < ∞` and `∫⁻ s in Icc 0 T', ∫⁻ e, ‖γ s 0 e‖₊² ∂ν < ∞`; with the Lipschitz clauses these give the `L²` bounds along any `L²`-bounded path. Applebaum 6.2.9 assumes measurable coefficients of linear growth; the Lean statement dropped that. **Corrected 2026-09-06 (C0a)**: `JumpDiffusionCoeffs.IsRegular coeffs ν` was added to `Ito/Setting.lean` and threaded through the wrap-up theorem and all three forwarders, so the statement is no longer refutable. Deriving the `is_solution` integrand hypotheses *from* it — which is what makes `picardStepOnS2` a total self-map — is the next leaf. **Third gap, closed 2026-09-06 (C0b)**: the space had no adaptedness field, only joint measurability, so `(s, ω) ↦ σ(s, X_s ω)` was progressively measurable for no filtration and the Brownian integral in the Picard step was not well-typed for a general member. `SBoundedProcess` is now parameterised by a filtration `ℱ` and carries `ProgressivelyMeasurable ℱ (fun ω s => X s ω i)` per coordinate; the Picard-step lemmas in `Ito/Picard.lean` take and return it. A second gap found by the same survey: `bieleckiNorm` is the weighted *sup-of-`L²`* norm, whereas `JumpDiffusion.sup_L2` is the strictly stronger `L²`-of-sup bound, so the fixed point does not by itself populate that field. **Fourth gap, closed 2026-09-07 (C0c-ii)**: the `γ` clause of `JumpDiffusionCoeffs.IsLipschitz` was stated as `(∫⁻ e, ‖γ s x₁ e - γ s x₂ e‖₊² ∂ν).toReal ≤ L² ‖x₁ - x₂‖²`. Since `(⊤ : ℝ≥0∞).toReal = 0`, that inequality is satisfied vacuously whenever the jump energy is infinite, so it constrains nothing in exactly the case the `h_γ_sq` hypothesis of `picardStep` needs constrained — no finiteness can be derived from it. It has been restated in `ℝ≥0∞`, `∫⁻ e, ‖γ s x₁ e - γ s x₂ e‖₊² ∂ν ≤ ENNReal.ofReal (L² ‖x₁ - x₂‖²)`, which is the statement Applebaum 6.2.9 assumes and is strictly stronger (it implies the `toReal` form and adds the finiteness). No declaration consumed the old clause — `hL` was only forwarded — so the change is a statement correction, not a re-proof. The forwarder `picardFixedPoint_jumpDiffusion_exists_unique_axiom`
was then listed in the "Honest derivative theorems" table below; until 2026-09-07 the
single baseline-`sorry` entry in `tools/sorry_baseline.txt` was
`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`.

**Why the demotion**: the Bielecki AE-quotient infrastructure landed in
`PicardSpace.lean` (Agent 3 integration commit 2c64e97) plus
the wrap-up bridge in `PicardSpace.lean` (this session).
Together they expose the literature `S²([0, T]; ℝⁿ)` Banach space and
the descended Picard contraction map at the type level, so the
existence-uniqueness conclusion of Applebaum 6.2.9 is now a real Lean
theorem statement (not a black-box axiom). The substantive analytical
content — Lp completeness for the Bielecki sup norm, càdlàg
modification descent, integrand ae-equivalence respect, AEQuot fixed
point → JumpDiffusion bridge — remains as the single sorry, to be
discharged when the corresponding Mathlib infrastructure lands or when
the project formalizes Doob regularization + Lp Bielecki sup norm
completeness directly.

**Statement audit (2026-09-06, A6-1) — narrowed, not strengthened.** As stated before this
audit, the four theorems of the chain (`…_via_aeQuot`, `…_axiom`, `…`,
`JumpDiffusion.exists_unique`) asserted a solution for an *arbitrary* pair `(W, N)` on one
probability space. Since X2-3 the `is_solution` field asks for a filtration `ℱ` for which every
coordinate of `W` is a Brownian motion and `N` a Poisson random measure, and for a dependent
pair no such `ℱ` exists: if `N` is a measurable functional of `W|[0,1]` (possible — both
σ-algebras are standard Borel and non-atomic), then `N((1, 2] × A)` is `ℱ₁`-measurable and, by
`IsPoissonFiltration`, independent of `ℱ₁`, hence a.s. constant, contradicting its Poisson law.
The claim was therefore false for such pairs and its `sorry` was undischargeable as stated. All
four now take `(ℱ, hℱW, hℱN)` — the hypothesis Applebaum 6.2.9 carries implicitly by assuming a
Lévy driver, and one that `Driver/Existence.lean` shows is satisfiable. The `sorry` is
unchanged in kind: the analytic Picard chain (A6) is still owed.

**Original statement** (recoverable from git history prior to commit
demoting #14): under Lipschitz hypothesis on `(μ, σ, γ)`, the
jump-diffusion SDE `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E
γ(t, X_{t-}, e) Ñ(dt, de)` with `X_0 = x_0` admits a `JumpDiffusion
W N coeffs x₀` solution (with càdlàg paths, L²-sup-bounded on every
bounded interval, satisfying the full SDE integral equation) that is
a.s.-pairwise-unique (any two solutions agree a.s. at every `t ≥ 0`).

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*,
2nd ed., CUP 2009, **Theorem 6.2.9**; Ikeda-Watanabe, *Stochastic
Differential Equations and Diffusion Processes*, North-Holland 1989,
**Chapter IV**.

## Honest derivative theorems (proven from cited axioms)

Results downstream of the numbered entries, and what each one forwards through. Rows whose
target has since been proved or deleted say so; only the last two rows still reach a live cited
axiom (#16). The table was expanded on 2026-05-23 (red-team P5 F4) to cover the BSDEJ-side
extractors and the then sorry-bodied Picard forwarders.

| Theorem | Forwards via |
|---|---|
| `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` | `BrownianMotion.exists` (a theorem since 2026-09-05; this row is now fully proven) |
| `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification` | `kolmogorovChentsov_modification` |
| `LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq` | derived from Kolmogorov continuity-in-probability + dyadic density (no Tier 1 axiom) |
| `LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous` | `brownian_martingale_rightCont` |
| `LevyStochCalc.Brownian.Martingale.brownian_martingale` | `brownian_martingale_rightCont` |
| `LevyStochCalc.Brownian.Martingale.brownian_quadVar` | `brownian_martingale_rightCont` (quadVar identity) |
| `LevyStochCalc.Brownian.Ito.itoIsometry` | `itoIsometry_brownian_unified_existence` (extracts conjunct 3 = isometry) |
| `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 1 = martingale) |
| `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 2 = quadVar) |
| `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | a theorem since 2026-09-06 (the Poisson recipe over `Poisson/PoissonSuperposition.lean`); fully proven |
| `LevyStochCalc.Poisson.poissonRandomMeasure_finite_exists` | deleted 2026-09-15: its unused finiteness hypothesis was removed (audit F13), which made it a verbatim restatement of `PoissonRandomMeasure.exists_of_sigmaFinite` |
| `LevyStochCalc.Poisson.Compensated.itoLevyIsometry` | `isometry_stochasticIntegral` (a theorem since 2026-09-06; this row is now fully proven) |
| `LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral` | `martingale_stochasticIntegral_rightCont` (a theorem since 2026-09-06; fully proven) |
| `LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral` | `martingale_quadVar_stochasticIntegral_rightCont` (a theorem since 2026-09-06; fully proven) |
| `LevyStochCalc.Poisson.Compensated.cadlag_modification_exists` | `stochasticIntegral_cadlag` (a theorem since 2026-09-06; fully proven) |
| `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry` | 1-line forwarder over `Compensated.itoLevyIsometry` |
| `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom` | deleted 2026-09-06 (built on the retired #13a) |
| `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` | deleted 2026-09-06 (built on the retired #13a) |
| `Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` | deleted 2026-09-07 (`ba5e214`); the ex-baseline-`sorry` wrap-up |
| `Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom` | deleted 2026-09-07 (`ba5e214`); ex-#14's forwarder over it |
| `Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique` | `exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`); 3 standard axioms |
| `Ito.Setting.JumpDiffusion.exists_unique` | `picardFixedPoint_jumpDiffusion_exists_unique`; 3 standard axioms |
| `BSDEJ.PathRegularity.bsdej_path_regularity_linear_rate` | deleted 2026-09-06 (`7dad5c2`) with the retired #10 |
| `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_axiom` | deleted 2026-09-15 with the axiom #16 it forwarded (Z1a); the formula is `itoLevyFormula_general` (`Ito/ItoLevyFormulaGeneral.lean`); 3 standard axioms |
| `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` | deleted 2026-09-15 with the axiom #16 it forwarded (Z1a); the four-term formula is `itoLevyFormula_general` (`Ito/ItoLevyFormulaGeneral.lean`); 3 standard axioms |

### Sorry baseline (count: 0)

`tools/sorry_baseline.txt` is empty, and `sorry`/`admit` occur in the `.lean` sources only as
words in docstrings and comments. The last entry was the Picard-chain wrap-up
`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`, which carried the whole literature
Picard iteration (Applebaum 6.2.9 / Ikeda–Watanabe IV) in a single explicit `sorry`. On
2026-09-07 (`ba5e214`) that chain was completed — `exists_jumpDiffusion_unique_of_solvesOn`
(`Ito/PicardWellPosed.lean`) builds the solution window by window, glues the windows along
`⌈t⌉₊` and populates every field of `JumpDiffusion` — and the wrap-up with the intermediates
`..._via_aeQuot` and `..._axiom` was deleted. `JumpDiffusion.exists_unique` now forwards through
`picardFixedPoint_jumpDiffusion_exists_unique` to that theorem.

Two statement audits landed with the closure and are recorded under entries #12 and #14:
uniqueness is asserted relative to a fixed filtration, and `is_solution`'s drift integral needed
parenthesising. Both change what the theorem says, so read those entries before citing it.

### P7 F10 qualification (red-team 2nd audit, 2026-05-23) — about the retired #9

Kept as the record of what the retired `continuousBSDEJ_exists_unique` (#9, deleted 2026-09-06)
asked of `IsBSDEJSolution`; the predicate itself is unchanged and still carries these clauses.

The previous note that `continuousBSDEJ_exists_unique` is "no longer
vacuously satisfiable" is TRUE for existence (the strengthened predicate
rules out trivial constant `Y` for generic `(f, g)`), but the uniqueness
clause is only sound under the strengthened predicate that now includes
(2026-05-23):
* `Filt` PINNED to `((⨆ i, naturalFiltration W_i) ⊔ naturalFiltration N).rightCont`
* `Adapted Filt Y`
* `IsStronglyProgressive Filt Z` (per P4 F1 fix)
* `IsStronglyProgressive Filt (fun s ω => U s ω e)` for each `e : E`
* `Y_cadlag` (càdlàg paths for the S²-leg)
* `M_W` pinned to `MultidimBrownianMotion.stochasticIntegral W Z`
* `M_N` pinned to `Compensated.stochasticIntegral N U`

Without all of these, the P12 F1 counterexample (Y₁ = 0 vs Y₂ = W_T − W_t
both satisfy the predicate for f = g = 0) would falsify the uniqueness
clause. The current closure is via Y₂'s failure of `Adapted Filt`: `W_T`
is not measurable in `Filt_t` for t < T.

## Status snapshot

Verified against the working tree on 2026-09-08:

* `tools/sorry_baseline.txt` is empty; `grep -rn '\bsorry\b\|\badmit\b' LevyStochCalc/`
  matches only prose in docstrings and module comments.
* Exactly one `axiom` declaration exists in the repository —
  `Ito/JumpFormula.lean:189`, entry #16 — and it is referenced by name only in that file, by
  `itoLevyFormula_jumpResidual_axiom` and `itoLevyFormula`.
* In `audit_output.txt` (untracked; the `#print axioms` report `tools/lint.sh` writes from
  `_audit.lean`), exactly three reports name a non-standard axiom — #16 itself and those two
  consumers — every other report is `{propext, Classical.choice, Quot.sound}`, and none names
  `sorryAx`. That is a statement about the logical trust base, not about coverage: the
  per-entry statement audits above are where the question of whether a Lean statement matches
  the result it cites is answered.
* Every `#print axioms` target in `_audit.lean` names a declaration present in the source tree
  (checked by name). The report in `audit_output.txt` predates `3119ca3` and `c9a0966`, which
  added `Poisson.natural_le_aug_windowSigma` and `Poisson.ae_eq_zero_of_integral_char_window`
  to `Poisson/WindowFiltration.lean`, so it still lists those two names as unknown; it is not a
  report on the current tree. Making the lint fail on such a mismatch is `X1b`/`X1c` in
  `../Dissertation/RELEASE_READINESS.md`.

### History (the Picard chain and the PRP decomposition)

Resolved on 2026-05-26 (formerly Tier 1 cited axiom #14):
* `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom`
  — converted from a standalone axiom to a 1-line forwarder over the
  wrap-up theorem. The literature dependency (Applebaum 6.2.9 /
  Ikeda-Watanabe IV) was from then on carried by the wrap-up's explicit
  baseline `sorry`, not by a free-standing axiom — visible to the lint
  pipeline — until the chain was proved and both were deleted on 2026-09-07.

Resolved on 2026-05-23 (formerly a baseline entry):
* `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation`
  — Jacod 1976 martingale representation theorem for `(W, Ñ)` filtrations
  (Jacod-Shiryaev Thm III.4.34). Converted to a thin forwarder over
  `jacodYor_representation_axiom` (Tier 1 #13). The integrand pinning
  to `MultidimBrownianMotion.stochasticIntegral` and
  `Compensated.stochasticIntegral` (canonical integrals) is at the
  statement level — no trivial-witness leakage.

Further on 2026-05-26:
* `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom`
  — was Tier 1 axiom #13. Demoted to a derived `theorem` forwarding
  through the strictly narrower Tier 1 sub-axiom pair #13a + #13b. The
  derivation is a 3-step composition: (1) apply #13b to build the càdlàg
  L² conditional-expectation martingale `M` with `M_0 = E[ξ]` a.s. and
  `M_T = ξ` a.s.; (2) apply #13a to extract `(Z, U)` such that
  `M_T = M_0 + ∫Z dW + ∫U dÑ` a.s.; (3) combine to get the L²-random-
  variable form. Public name `jacodYor_representation_axiom` retained
  for downstream stability — it's now in the "Honest derivative theorems"
  table rather than the Tier 1 axiom list.

### Recursive audit (2026-05-11) — internal classification

Per the user's recursive-audit standard (trivial-witness theorems = worse
than documented axioms), the 4 LevyStochCalc theorems the dissertation
forwards into were classified:

| Theorem | Classification | Action taken |
|---|---|---|
| `Poisson.L2Isometry.itoLevyIsometry` | (R) Real | Leave alone (extracts from Tier 1 unified-existence axiom with non-trivial quadVar conjunct that rules out constant witnesses) |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` | (C) Cosmetic predicate | `IsBSDEJSolution` strengthened: replaced vacuous per-`(t, ω)` existential `∃ BM jump : ℝ` with outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to Z (L²-isometry) and U (direct `=` to `Compensated.stochasticIntegral`); adaptedness layer added 2026-05-21 (closes red-team C1); `M_W` pinned to canonical multidim Brownian Itô integral 2026-05-22 (closes red-team H2). |
| `Ito.JumpFormula.itoLevyFormula` | (C) Cosmetic theorem | DEMOTED from `theorem` (trivial-witness proof) to `axiom`; all 4 terms pinned to literature integral forms 2026-05-22 (closes red-team C2) |
| `BSDEJ.PathRegularity.bsdej_path_regularity` | (C) Cosmetic predicate | Same as `continuousBSDEJ_exists_unique` — fixed by the `IsBSDEJSolution` strengthening; `Z_avg`/`U_avg` pinned to `cellTimeAverage_*` 2026-05-22 (closes red-team H3) |

### Red-team audit fix log (2026-05-20 audit, fixes through 2026-05-22)

The 12-persona red-team audit ran on commit db582f9. Per-finding fix status:

**CRITICAL (all closed):**
* **C1** (BSDEJ unsoundness): closed by `IsBSDEJSolution` adaptedness +
  `M_W` canonical-integral pinning (commits 2d9309e, 1b1f69f).
* **C2** (itoLevyFormula trivial-witness statement): closed by pinning
  all 4 terms (commits 7d232bf, 09687cf, 9675e44, 94f0155).
* **C3** (JumpDiffusion trivial-witness): closed — `is_solution` field
  strengthened from `True` to real SDE integral equation; proof now
  honestly sorry'd in baseline (commit 62e124a).
* **C4** (jacodYor trivial-witness): closed — signature strengthened to
  pin BM/jump integrals to canonical forms; proof now honestly sorry'd
  in baseline.
* **C5** (3 public sorryAx hidden from audit): closed — `kolmogorov_modification_ae_eq`
  fully proved (commit 259d2d2); `poissonRandomMeasure_finite_exists`
  forwarded to σ-finite axiom (commit 2a88b87); `simplePredictable_dense_L2`
  deleted as dead code (commit 6b25dfc).
* **C6** (Gnoatto 2025 fabrication): closed — replaced with real
  Andersson-Gnoatto-Patacca-Picarelli 2025 citation.
* **C7** (BET 2009 misattribution): closed — replaced with Bouchard-Elie
  2008 SPA 118(1).
* **C8** (518 lines untracked): closed by `git add` of all source +
  build configs.
* **C9** (lint.sh silently passing): closed — hardened to fail when audit
  output is missing/empty.

**HIGH (all closed):**
* **H1, H2** (BSDEJ adaptedness / M_W pinning): closed (see C1).
* **H3** (Z_avg/U_avg loose existential): closed by pinning to
  `cellTimeAverage_*`.
* **H4** (missing Lipschitz / L² / measurability on BSDEJ axioms): closed.
* **H5** (Compensated unified-existence asymmetric vs Brownian): closed
  by adding `h_meas` + `h_sq_int` outer hypotheses (commit 359beda).
* **H7, H8** (Le Gall citation theorem-number errors): closed (commit b065b7d).
* **H9** (Pardoux-Răşcanu continuous-case in BSDEJ citations): retained
  with explicit `(continuous case)` parenthetical to honestly mark the
  scope.
* **H10** (lake-manifest project-name + toolchain): closed.

**MEDIUM:**
* **M1** (7+ `True := trivial` lemmas): closed — all 8 stubs deleted
  (commit 638b21d).
* **M2** (4 dead-code `sorry` privates): closed by direct proof
  (`kolmogorov_modification_ae_eq`, `poissonRandomMeasure_finite_exists`)
  or deletion (`quadVar_simpleIntegral_brownian`,
  `simplePredictable_dense_L2_bounded`).
* **M3** (677-line orphan `Poisson/Martingale.lean`): closed (commit eb707a4).
* **M4** (Tier 1 #7 + #8 dead post-refactor): CLOSED 2026-05-22 — both
  dead axioms deleted along with the intertwined dead chain
  (`cauchySeq_simpleIntegralLp_compensated`, `adaptedSimple_dense_L2_
  compensated`, plus the supporting `_existence` + density chain).
  P10 F12 fix (red-team 2nd audit 2026-05-23): the previous "retained
  pending careful walk-up deletion" wording contradicted the M4 closure
  elsewhere in this file; corrected.
* **M5** (`adaptedSimple_dense_L2_compensated` docstring vs signature):
  CLOSED 2026-05-22 alongside M4 (axiom deleted).
* **M6** (this file's "No trivial-witness theorems remain" claim): closed
  by this update.
* **M8** (path-regularity constant parameterization): CLOSED 2026-05-23 —
  C polynomial-pinned to BET 2008 exponential form `K · (1+T)^p · exp(αLT)
  · (1+ξ)` (P4 F5 fix).
* **M9** (multidim Brownian primitive): CLOSED — built as
  `Brownian/MultidimIto.lean`.
* **M10** (scalar-Y BSDEJData): scope-note; not a defect, generalization
  tracked in `BSDEJData` docstring.
* **M11** (`IsBSDEJSolution` filtration trivial-constant): CLOSED
  2026-05-23 — Filt PINNED to `((⨆ i, naturalFiltration W_i) ⊔
  naturalFiltration N).rightCont` inside the existential. P10 F12 fix:
  the previous "deferred" wording was stale.
* **M12** (`integral_undef` exploit on Compensated quadVar): closed
  alongside H5.
* **M13** (Le Gall Thm 2.1 citation for BM existence): closed (commit b065b7d).

**Open / deferred:**
* **H6** (Predictable vs. Measurable hypothesis): CLOSED 2026-05-23 —
  outer h_meas + h_progMeas + h_sq_int_global hypotheses on
  `itoIsometry_compensated_unified_existence` mirror the Brownian-side
  signature exactly.

### Integrand-class audit (2026-09-06) — the `L²` integrals admit only deterministic integrands

The progressive-measurability hypothesis carried by every stochastic integral of this library
(`h_progMeas` in `Brownian/ItoL2Completion.lean`, `Brownian/MultidimIto.lean`,
`Poisson/Compensated*.lean`, and mirrored in `Ito/Setting.lean`, `Ito/JumpFormula.lean`,
`BSDEJ/Definition.lean`) reads

    ∀ t, StronglyMeasurable[ℱ t ⊗ Borel] (fun p : Ω × ℝ => H p.1 p.2)

with **no restriction to `s ≤ t`** — unlike Mathlib's `IsStronglyProgressive`, which restricts
to `Set.Iic t × Ω`. Taking `t = 0`: every section `ω ↦ H ω s` must be `ℱ 0`-measurable. For the
natural filtration of a Brownian motion, `ℱ 0 = ⨆ j ≤ 0, σ(W j)` is generated by the a.s.-zero
variables `W j` (`initial_zero`, `negative_zero`), hence P-trivial; for the natural filtration of
a Poisson random measure, `ℱ 0` is generated by the counts `N(B)`, `B ⊆ (-∞, 0] × E`, of
intensity `0`, hence P-trivial as well. An `ℱ 0`-measurable real function is a.s. constant. So
**every admissible integrand is, for each time `s`, a.s. constant in `ω`** — its class in
`L²(P ⊗ ds)` (resp. `L²(P ⊗ ds ⊗ ν)`) is that of a deterministic function of `(s)` (resp.
`(s, e)`). Consequences, recorded here so that nothing downstream over-reads the theorems:

* The proved results #5, #6, #17, #18 (isometry, martingale, quadratic variation, càdlàg
  modification, difference isometry) are true theorems, but about **Wiener integrals of
  deterministic integrands**, not about the Itô–Lévy integral of predictable processes. The
  docstrings that say "predictable square-integrable integrands" over-state the class.
* `JumpDiffusion.is_solution` admits only coefficients `σ(s, X_s)`, `γ(s, X_s, e)` that are a.s.
  constant in `ω` for each `(s, e)`; `IsBSDEJSolution` admits only deterministic `Z`, `U`;
  the corrected #16 applies only to integrands in this class (its hypotheses are otherwise
  unsatisfiable, so it is not refuted by this finding).
* The dissertation forwarder `Dissertation.Continuous.itoLevyIsometry` (I02) inherits the
  class; the one-step discrete model of Paper C never consumed these integrals.

**Remediation** is work package X2 in `Plan.md`, rescoped to rebuild the interface of the
integrals with genuine progressive measurability (Mathlib's `IsStronglyProgressive`, i.e.
`Set.Iic t × Ω`) over a common filtration, and to check every proof that silently used the
over-strong hypothesis.

**Resolution, Brownian side (X2-1, 2026-09-06).** `Probability/Progressive.lean` defines
`ProgressivelyMeasurable ℱ H` — for every `t`, `(ω, s) ↦ 1_{s ≤ t} H ω s` is
`ℱ t ⊗ Borel`-measurable — and proves it equivalent to Mathlib's `IsStronglyProgressive` in
both directions. The whole Brownian chain (`ItoSimple` … `ItoL2Completion`, `MultidimIto`) is
restated with `h_progMeas : ProgressivelyMeasurable ℱ H` for an arbitrary filtration `ℱ` with
`IsBrownianFiltration W ℱ`; no proof used the over-strong hypothesis in an essential way — the
only three places that consumed it (the `ℱ t`-measurability of the dyadic averages over
`(t_{i−1}, t_i]`, of the clipped integrand, and of the compensator `∫_0^t H²`) go through
`ProgressivelyMeasurable.stronglyMeasurable_setIntegral` and `Continuous.comp_progressivelyMeasurable`.
So #5 and #17 are theorems about the Itô integral of progressively measurable integrands, and
the consumers now pass the joint Brownian filtration `W.naturalFiltration`
(`Brownian/MultidimFiltered.lean`). 
**Resolution, Poisson side (X2-2, 2026-09-06).** The marked analogue
`MarkedProgressivelyMeasurable ℱ φ` — for every `t`, `(ω, s, e) ↦ 1_{s ≤ t} φ ω s e` is
`ℱ t ⊗ Borel ⊗ 𝓔`-measurable — carries the compensated-Poisson chain
(`CompensatedIsometry` … `Compensated`, `L2Isometry`) over an arbitrary filtration `ℱ` with
`IsPoissonFiltration N ℱ`. The three consumers of the over-strong hypothesis (the
`ℱ p_i ⊗ 𝓔`-measurability of the shifted dyadic averages, the truncation to bounded
integrands supported on a finite-measure mark set, and the `ℱ t`-measurability of the
compensator `∫_0^t ∫_E φ² dν ds`) go through `stronglyMeasurable_setIntegral_prod`,
`indicator_mark` with `Continuous.comp_markedProgressivelyMeasurable`, and
`stronglyMeasurable_setIntegral_integral`; the past-measurability and future-independence
of `N` enter only through `hℱ.measurable` and `hℱ.indep`. So #6 and #18 are theorems about
the Itô–Lévy integral of progressively measurable marked integrands.

**Resolution, common filtration (X2-3, 2026-09-06).** Both `stochasticIntegral`s take the
filtration as an argument, so a consumer can pass the *same* `ℱ` to both provided `ℱ` carries
both driver properties. `Ito/Setting.is_solution` now opens with
`∃ ℱ, (∀ j, IsBrownianFiltration (W.W j) ℱ) ∧ IsPoissonFiltration N ℱ ∧ …`, with `σ(s, X_s) i j`
progressive and `γ(s, X_s, ·) i` marked-progressive for that one `ℱ`; `Ito/JumpFormula` (#16),
`Ito/Picard*` and `BSDEJ/Definition.IsBSDEJSolution` (over `ℱ₊`) are stated the same way, and
#13b over a `LevyDriver` and its `D.filtration.rightCont`. Coupled coefficients — `σ` depending
on the jump history and `γ` on the Brownian history — are therefore in scope: the integrands
share one filtration, and nothing forces `ℱ` to be a single driver's natural filtration. What
this does *not* settle is that the conjunction is satisfiable; the witness is X2-4.

**Non-vacuity (X2-4, 2026-09-06).** `Driver/Existence.lean` constructs a `LevyDriver` on the
product of a space carrying a `d`-dimensional Brownian motion and one carrying a Poisson
random measure with the given σ-finite intensity on a standard Borel mark space: both
projections are measure preserving, so each driver transports (`Brownian/Transport.lean`,
`Poisson/Transport.lean`, over the independence transport in `Probability/Transport.lean`),
and on the product `σ(W)` factors through the first coordinate and `σ(N)` through the second,
which a product measure makes independent. `LevyDriver.filtration` then carries both driver
properties, so `exists_isBrownianFiltration_and_isPoissonFiltration` witnesses the hypothesis
above. This is satisfiability of the *filtration* hypothesis only: whether the SDE, the
Itô–Lévy formula's hypotheses or a BSDEJ have solutions is separate and still open.

### Net audit (verifiable via `tools/lint.sh` + `_audit.lean`)

* **1 Tier 1 cited axiom currently lives** (#3 proved axiom→theorem
  2026-06-16; #5 and #17 2026-06-17; #1 2026-09-05; #2, #4, #6, #18 and #13b 2026-09-06;
  #15 retired 2026-09-06 as a vacuous statement; #9, #10 and #13a retired 2026-09-06 as
  refutable statements — see their entries; the Brownian foundations #1, #3, #4, #5,
  the Poisson random measure #2, the Poisson integral #6 and the conditional-expectation
  bridge #13b are theorems): #16 (the Itô-Lévy formula's content,
  `itoLevyFormula_jumpResidual_canonical_axiom`; the previously-monolithic
  Tier 1 #11 `itoLevyFormula` is a derived theorem over it alone since the
  vacuous #15 was retired on 2026-09-06). The two
  per-difference L²-isometries #17 (`itoIsometry_diff_brownian`, 2026-06-17)
  and #18 (`itoIsometry_diff_compensated`, 2026-09-06) are theorems.
  Each axiom has paper reference + Mathlib status + replacement plan.
  History markers: M4 deleted #7 + #8 (2026-05-22); #11 retired (2026-05-24);
  #12, #13, #14 demoted axiom→theorem (2026-05-26); #17, #18 added
  to this file (2026-05-27 — 3rd-audit CRITICAL #1 closure).
* **Derivative theorems** over Lean's three standard axioms plus, for the two consumers of
  #16, that one cited axiom.
* **No `sorryAx` anywhere.** `tools/sorry_baseline.txt` is empty, the Picard wrap-up that held
  the last entry was discharged and deleted on 2026-09-07 (`ba5e214`), and no report in
  `audit_output.txt` names `sorryAx`.
* No `True := trivial` stub lemmas remain in the project.
* The dissertation forwarders surface #16 alone; `Dissertation.Continuous.itoLevyFormula` is the
  one dissertation declaration that carries it (through `itoLevyFormula`).

## Naming-suffix drift (P1 F11 acknowledgment)

The Tier 1 axiom names include redundant `_brownian` / `_compensated`
suffixes (e.g., `itoIsometry_brownian_unified_existence`,
`itoIsometry_compensated_unified_existence`) where the surrounding
namespace (`Brownian.Ito`, `Poisson.Compensated`) already
disambiguates. The Mathlib-style preferred form would be
`Brownian.Ito.itoIsometry_unified_existence` and
`Poisson.Compensated.itoIsometry_unified_existence`. The redundant
suffixes are historical accidents from the pre-2026-05-10 refactor
when the analogous axioms shared a flat namespace. Renaming would
break the Dissertation forwarders + every downstream caller, so the
historical names are preserved for stability; a future "Mathlib-PR
prep" pass can do the rename atomically with the forwarder updates.
Documented per red-team P1 F11 2nd audit, 2026-05-23.

## How to add a new Tier 1 cited axiom

P10 F13 fix (red-team 2nd audit 2026-05-23): explicit guidance for
contributors.

1. **Identify the literature theorem.** Find the textbook/paper reference
   (Karatzas-Shreve, Le Gall, Applebaum, Tang-Li, Bouchard-Elie,
   Pardoux-Răşcanu, etc.) with **specific theorem/equation number**.
   Verify the number against the actual book (P11 found 4 wrong
   theorem-number citations in the 1st audit; check the body text, not
   just the TOC).
2. **Write the axiom in the right file.**
   * Brownian foundations → `LevyStochCalc/Brownian/`
   * Poisson foundations → `LevyStochCalc/Poisson/`
   * BSDEJ → `LevyStochCalc/BSDEJ/`
   * Itô-Lévy formula → `LevyStochCalc/Ito/`
3. **Strengthen the statement per Rule 0.** The axiom MUST pin every
   existential to a literature object — no `∃ F BM_integral, ...`
   unbound existentials that admit trivial witnesses. If pinning to a
   `Classical.choose`-d object, document where the choose chain
   bottoms out.
4. **Make the signature load-bearing.** Outer hypotheses (`h_meas`,
   `h_progMeas`, `h_sq_int_global`, Lipschitz, L²-terminal) must
   appear in the signature, not gate conjuncts inside the existential.
5. **Add to `tools/cited_axioms.md`** with: name, statement (1
   sentence), reference (1 sentence with paper + thm #), Mathlib
   status, replacement plan.
6. **Add to `_audit.lean`** so `#print axioms` covers it.
7. **Build + lint must still pass.** New sorryAx-tainted theorems
   require a baseline entry in `tools/sorry_baseline.txt` AND a
   commit-message rationale; the lint script's typo-defense (P2
   HIGH-2 fix) will FAIL on baseline entries that don't match any
   theorem name.
8. **Commit message format**: include the Tier 1 number + the
   paper citation in the body. Example:
   `Add Tier 1 #12: predictable-projection theorem (Jacod-Shiryaev I.2.13)`

## Convention

* `tools/sorry_baseline.txt` — sorry-blocked theorems (currently empty: see the status
  snapshot above).
* `tools/cited_axioms.md` (this file) — Tier 1 cited axioms with citations + Mathlib status +
  replacement plans.
* `tools/lint.sh` — runs `_audit.lean` and fails on new sorryAx beyond
  the baseline.
* `_audit.lean` — `#print axioms` on every load-bearing theorem; runs as
  part of CI to verify the axiom budget.
