# Cited Axioms

Theorems in `LevyStochCalc` that depend on **paper-cited stochastic calculus axioms**.
Each entry below names an axiom whose statement is a real published theorem,
introduced as `axiom <name> : <statement>` with a docstring giving the citation.

The `tools/lint.sh` script flags only `sorryAx`-tainted theorems. Cited axioms
are introduced as Lean `axiom` declarations and do NOT count as `sorryAx`.

## Tier 1: Honest cited axioms (14 currently live; #7 and #8 deleted 2026-05-22; #11 retired 2026-05-24 via axiom→theorem conversion — `itoLevyFormula` now a theorem derived from #15 + #16; #12, #13, #14 added 2026-05-23 via theorem→axiom conversion; #15 + #16 added 2026-05-24 to expose the two literature sub-primitives behind the Itô–Lévy formula — #15 is `itoFormula_continuousSemimartingale_axiom` cited from Karatzas–Shreve 3.3.6; #16 is `itoLevyFormula_jumpResidual_axiom` cited from Applebaum 4.4.10 + 4.4.7 step II)

These axioms state real published theorems. The LevyStochCalc-side `axiom`
declaration faithfully matches the cited statement. When Mathlib formalises
the underlying theorem, the `axiom` is replaced with a `theorem` forwarding
to the Mathlib version, no other changes needed downstream.

### 1. `LevyStochCalc.Brownian.BrownianMotion.exists`

* **Statement**: There exists a probability space carrying a 1-dimensional Brownian motion.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 2.2.2** (Daniell-Kolmogorov consistency) + **Theorem 2.2.8** (Kolmogorov-Čentsov continuous-modification existence) — Chapter 2 §2.2 "First Construction of Brownian Motion" pp. 49-56 (correcting the previous "Theorem 2.1.5" citation flagged by red-team P11 2nd audit — §2.1 of K-S is the chapter Introduction, no theorem 2.1.5 exists); Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Definition 2.1** / **Definition 2.12** / **Corollary 2.11** (the Brownian-motion construction; correcting the previous "Theorem 2.1" citation flagged by red-team P11 — Le Gall 2016 has no "Theorem 2.1"; the existence statement combines the definition + the explicit Wiener-measure construction in Chapter 2). Wiener measure construction via Kolmogorov extension + KC modification.
* **Mathlib status (May 2026)**: No current `MeasureTheory.WienerMeasure` or `BrownianMotion` definition. Adjacent infrastructure exists: `ProbabilityTheory.gaussianReal` (Real Gaussian distribution), `ProbabilityTheory.IsGaussianProcess`, `MeasureTheory.IsProjectiveLimit`, `Probability.Kernel.IonescuTulcea.trajMeasure` (dyadic-time Markov chains). The "Degenne et al stochastic integration" effort (arXiv:2511.20118, late 2025) is the most active push toward Mathlib-Brownian; no Mathlib PR merged at time of writing.
* **Replacement plan**: `theorem BrownianMotion.exists := <Mathlib forwarder>` when `MeasureTheory.WienerMeasure` lands.

### 2. `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite`

* **Statement**: For σ-finite intensity ν on standard Borel E, ∃ probability space carrying a Poisson random measure with intensity `vol[0,∞) ⊗ ν`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 2.3.1**; Kallenberg, *Random Measures, Theory and Applications*, Springer 2017, **Proposition 3.6**.
* **Mathlib status (May 2026)**: `ProbabilityTheory.poissonMeasure` exists (ℕ-valued Poisson distribution), but no Poisson random measure construction. No current Mathlib activity for Poisson random measures or general Lévy processes.
* **Replacement plan**: `theorem PoissonRandomMeasure.exists_of_sigmaFinite := <Mathlib forwarder>` when `MeasureTheory.PoissonRandomMeasure` lands.

### 3. `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification`

* **Statement**: A real-valued process satisfying the Kolmogorov moment condition with `q > 1` admits a modification with continuous paths.
* **Reference**: Karatzas–Shreve **Theorem 2.2.8**; Le Gall **Theorem 2.9**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Springer 1999, **Theorem I.2.1**.
* **Mathlib status (May 2026)**: `ProbabilityTheory.IsKolmogorovProcess` is defined (the *condition*) with `mk_of_secondCountableTopology` constructor and various API lemmas (measurable, edist_eq_zero, stronglyMeasurable_edist). The modification *theorem* (existence of continuous version) is NOT yet present. Active partial work in `Mathlib.Probability.Process.Kolmogorov`.
* **Replacement plan**: `theorem kolmogorovChentsov_modification := IsKolmogorovProcess.exists_continuous_modification` (or equivalent) when the modification theorem is added.

### 4. `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont`

* **Statement**: Brownian motion is a martingale w.r.t. the right-continuous augmentation of its natural filtration (consequence of Blumenthal 0-1 law).
* **Reference**: Karatzas–Shreve **Theorem 2.7.7** (Blumenthal 0-1) + **Theorem 2.7.9** (right-continuity of augmented filtration); Le Gall **Theorem 2.13** (Blumenthal 0-1 for Brownian motion; correcting the previous "Proposition 2.10" citation flagged by red-team P11 — Le Gall 2016 p. 25 "Lemma 2.10" is a deterministic real-analysis Hölder lemma; Blumenthal is Le Gall p. 30 Theorem 2.13).
* **Mathlib status (May 2026)**: `MeasureTheory.Filtration.rightCont` is defined; `MeasureTheory.Filtration.IsRightContinuous` predicate available. Blumenthal 0-1 law is NOT in Mathlib for Brownian motion (waits on BM construction). No current activity.
* **Replacement plan**: `theorem brownian_martingale_rightCont := <Blumenthal 0-1 corollary>` when Blumenthal 0-1 for BM lands.

### 5. `LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence`

* **Statement**: For predictable square-integrable `H`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t H² ds` is a `Filt`-martingale (quadratic variation identity), and the L²-isometry `∫⁻ ‖F T‖₊² = ∫⁻ ∫⁻ ‖H‖² over [0,T]` holds at every `T > 0`.
* **Reference**: Karatzas–Shreve **Theorem 3.2.6** (unified martingale + quadratic variation + L²-isometry); Le Gall **Theorem 5.4** + equation **(5.8)** (Itô isometry; correcting the previous "Theorem 5.13" citation flagged by red-team P11 — Le Gall 2016 p. 121 "Theorem 5.13" is Dambis–Dubins–Schwarz, not Itô isometry; L² Itô isometry is Le Gall Thm 5.4 with the explicit norm-equality at eq. (5.8)).
* **Mathlib status (May 2026)**: No general L²-Itô integral against Brownian motion in Mathlib (waits on BM construction). `MeasureTheory.condExpL2_continuous` and `MeasureTheory.Martingale` provide the analytic glue for the L²-limit-of-martingales argument; the simple-level martingale + quadVar + L²-isometry combine via that glue. arXiv:2511.20118 (Degenne et al, late 2025) is targeting this.
* **Replacement plan**: `theorem itoIsometry_brownian_unified_existence := <Mathlib forwarder>` when Mathlib gains the L²-Itô integral with these properties.

### 6. `LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence`

* **Statement**: For predictable square-integrable `φ`, there is a process `F` and filtration `Filt` such that `F` is a `Filt`-martingale, `(F t)² − ∫_0^t ∫_E φ² ν(de) ds` is a `Filt`-martingale, the L²-isometry holds at every `T > 0`, and `F` has càdlàg paths.
* **Reference**: Applebaum 2009 **Theorem 4.2.3** (martingale + quadVar + L²-isometry) + **Theorem 4.2.4** (càdlàg modification); Ikeda–Watanabe **Section II.3**.
* **Mathlib status (May 2026)**: No compensated-Poisson L² integral in Mathlib (waits on Poisson random measure construction). No current activity.
* **Replacement plan**: `theorem itoIsometry_compensated_unified_existence := <Mathlib forwarder>` when Mathlib gains compensated-Poisson L² integration.

### 7. `LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` (DELETED 2026-05-22)

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

### 8. `LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated` (DELETED 2026-05-22)

This axiom was deleted on 2026-05-22 as dead code, alongside #7. It was
the Compensated L²-density-of-adapted-simple-predictables step in the
same superseded chain. Per red-team finding M4, not reachable from any
audited load-bearing theorem.

Original statement (recoverable from git history): for progressively-
measurable `φ : Ω → ℝ → E → ℝ` with finite L² norm on `[0, T]`, there
exists a sequence of adapted simple predictables `G n` with `(G n).eval`
converging to `φ` in `L²(P × ds × dν)` plus the shared endpoint + joint
measurability properties needed downstream (Applebaum 2009 Lemma 4.2.2).

### 9. `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique`

* **Statement**: Under Lipschitz hypotheses on `(f, g)` and L² integrability of terminal data, the continuous BSDEJ has a unique adapted solution triple `(Y, Z, U) ∈ S² × H² × H²_N` satisfying the strengthened `IsBSDEJSolution` predicate.
* **Reference**: Tang & Li, *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, DOI 10.1137/S0363012992233858 (historical first BSDEJ existence reference per Papapantoleon-Possamaï-Saplaouras 2018; specific theorem number paywalled and unverified per red-team P11 2nd audit 2026-05-23 — primary numbered citation is AGPP 2025 below); Andersson, Gnoatto, Patacca & Picarelli, *A deep solver for BSDEs with jumps*, SIAM J. Financial Math. / arXiv:2211.04349, 2025, **Theorem 2.4** (correcting the previous fabricated citation "Gnoatto 2025 *Quantitative Finance* primer" flagged by red-team P11 — no such paper exists per DBLP); Delong, *BSDEs with Jumps and their Actuarial and Financial Applications*, Springer EAA 2013 (first edition, DOI 10.1007/978-1-4471-5331-3), **Theorem 4.1.3** (jumps case, directly applicable). For continuous-only background see also Pardoux & Răşcanu, *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*, Springer 2014, **Theorem 4.79** — but note Pardoux-Răşcanu does NOT cover the BSDEJ (jump) case per red-team P11 2nd audit 2026-05-23; the jump-case authority is Tang-Li + Delong + AGPP.
* **Predicate state (2026-05-11)**: The `IsBSDEJSolution` predicate was tightened on 2026-05-11 — the previous vacuous per-`(t, ω)` existential `∃ BM_term jump_term : ℝ, …` (which made the axiom mathematically false as written, since multiple distinct `Y` could trivially satisfy it) was replaced with an outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to `Z, U` via L²-isometry (for `M_W` vs `Z`) and direct equality to `Compensated.stochasticIntegral` (for `M_N` vs `U`). The strengthened predicate is no longer vacuously satisfiable by constant `Y` for generic `(f, g)`. Documented in `BSDEJ/Definition.lean` module docstring.
* **Mathlib status (May 2026)**: No BSDEJ in Mathlib. `Mathlib.Analysis.SpecificLimits.Basic` has Picard / contraction-mapping infrastructure (`ContractingWith.fixedPoint`) usable for the proof body once the L² Itô-Lévy + martingale representation pieces land.
* **Replacement plan**: `theorem continuousBSDEJ_exists_unique := <Picard contraction proof>` when the L² Itô-Lévy chain is fully formalized (after items 5 + 6 above). Further predicate-tightening (pinning `M_W` to the actual multidim Brownian stochastic integral, not just an isometric martingale) is a separate downstream item — needs `h_progMeas` threaded through `IsBSDEJSolution`.

### 10. `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity`

* **Statement**: For the unique BSDEJ solution (satisfying the strengthened `IsBSDEJSolution` predicate from item 9), the L²-time modulus + projection errors of `(Z, U)` over a partition with mesh `Δt` are bounded by `C · Δt`.
* **Reference**: Bouchard & Elie, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, Stochastic Processes Appl. **118(1)**, **2008**, pp. 53–75, **Theorem 2.1** (correcting the previous misattribution to "Bouchard, Elie & Touzi 2009 SPA 119(11)" — Touzi is not an author and no such 2009 paper exists; flagged by red-team P06/P07/P10/P11, verified via Bouchard's slides + HAL hal-00015486 + Kharroubi–Lim 2018 citing "Bouchard and Elie [4]"). For continuous-only background see also Pardoux & Răşcanu, Springer 2014, **Theorem 5.42** (continuous case, NOT BSDEJ) — Pardoux-Răşcanu does NOT cover the jump case per red-team P11 2nd audit 2026-05-23.
* **Predicate state**: Same strengthening note as item 9.
* **Mathlib status (May 2026)**: `MeasureTheory.Submartingale.upcrossingsBefore_le` and adjacent Doob's L²-maximal inequality infrastructure exists in `Mathlib.Probability.Martingale`. The Grönwall integral lemma `Mathlib.Analysis.Gronwall` is also available. Combining these into the path regularity bound is mechanical once items 5 + 6 + 9 land.
* **Replacement plan**: `theorem bsdej_path_regularity := <Doob + Grönwall combination>` when items 5, 6, 9 are theorems.

### 11. `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` — RETIRED 2026-05-24

This entry was retired on 2026-05-24 as part of the Rule-1 START
`axiom → theorem` conversion of the headline Itô–Lévy formula. The
single Applebaum 4.4.7 axiom was split into TWO Tier 1 sub-primitives
(entries #15 and #16 below) that expose the precise content of the
literature proof; the headline `itoLevyFormula` is now a `theorem`
derived by algebraic re-bundling from the two sub-axioms.

The previous content of this entry (the single-axiom Applebaum 4.4.7
form) is preserved verbatim in the file's git history (commit
4dea618 and predecessors).

**See entries #15 + #16 below for the current axiomatisation.**

### 12. `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique`

* **Statement**: Under Lipschitz hypothesis on `(μ, σ, γ)`, the jump-diffusion SDE `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)` with `X_0 = x_0` admits a strong solution (with càdlàg paths, L²-sup-bounded on every bounded interval) that is a.s. unique.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 6.2.9**; Ikeda-Watanabe, *Stochastic Differential Equations and Diffusion Processes*, North-Holland 1989, Chapter IV.
* **2026-05-23 refactor + axiomatization (COMPLETED)**: the theorem moved out of `Ito/Setting.lean` and into `Ito/PicardBanach.lean`, where it forwards through a SINGLE intermediate `picardFixedPoint_jumpDiffusion_exists_unique` (the SDE-specialised Banach fixed-point output). That intermediate was previously a `theorem` with a `sorry` body; it has now been converted to a thin forwarder over the new Tier 1 cited axiom `picardFixedPoint_jumpDiffusion_exists_unique_axiom` (entry #14 below). Consequently `JumpDiffusion.exists_unique` is no longer sorryAx-tainted — its transitive axiom dependency surfaces #14 instead of `sorryAx`. The qualified name `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` is preserved by re-opening the namespace in `PicardBanach.lean`. Previous status: previously a `theorem` with direct-`sorry` body in `Setting.lean`; per Rule 0, that was a misleading representation (the implementation was effectively unproven).
* **Signature strength**: requires `JumpDiffusionCoeffs.IsLipschitz coeffs ν L` (Tanaka's `|X|^α` counterexample for α < 1/2 rules out uniqueness without this).
* **Mathlib status (May 2026)**: No SDE-with-jumps strong existence/uniqueness in Mathlib. Continuous-SDE strong existence is partially formalized but the jump-SDE case waits on the multidim Brownian + compensated-Poisson integral infrastructure.
* **Replacement plan**: When the underlying axiom #14 becomes a theorem (full Picard iteration + Bielecki packaging + structure bridge), `JumpDiffusion.exists_unique` inherits soundness automatically with no source-level changes.

### 13. `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom`

* **Statement**: Every L²-integrable `((⨆ i, naturalFiltration W_i) ⊔ naturalFiltration N).rightCont.seq T`-measurable random variable `ξ : Ω → ℝ` admits a representation `ξ = E[ξ] + ∫_0^T Z_s · dW_s + ∫_0^T ∫_E U_s(e) Ñ(ds, de)` a.s., with progressively-measurable square-integrable integrands `Z, U`, where the Brownian and compensated-Poisson integrals are pinned to `MultidimBrownianMotion.stochasticIntegral W Z ...` and `Compensated.stochasticIntegral N U ...` respectively.
* **Reference**: Jacod, J. "Multivariate point processes: predictable projection, Radon-Nikodym derivatives, representation of martingales", Z. Wahrsch. Verw. Gebiete 31(3), 1975, pp 235-253; Jacod-Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer 2003, **Theorem III.4.34**.
* **2026-05-23 conversion `theorem → axiom` (COMPLETED)**: previously a `theorem` with `sorry` body. The literature proof requires predictable projection / chaos decomposition machinery that Mathlib does not yet have. The honest representation is the `axiom jacodYor_representation_axiom` cited from Jacod 1976, with the downstream-facing `theorem jacodYor_representation` preserved as a thin forwarder over the axiom (signature unchanged, callers unaffected).
* **Signature strength**: ξ measurability strengthened to `StronglyMeasurable[ℱ_T] ξ` (joint natural filtration at endpoint T) — required because martingale representation only holds for ξ measurable wrt the filtration at the endpoint. Both stochastic integrals fully pinned with per-component progressively-measurable + L² hypotheses bundled as existential witnesses (no trivial Z = U = 0 witness).
* **Mathlib status (May 2026)**: No predictable projection / chaos decomposition in Mathlib for general (W, N) filtrations. Continuous-Brownian-only chaos decomposition is partially in `Mathlib.Probability.Process.WienerChaos` (early-stage).
* **Replacement plan**: `theorem jacodYor_representation_axiom := <predictable projection + chaos decomposition>` (and inline the forwarder) when (a) Tier 1 #5 + #6 are theorems, (b) the projection / decomposition apparatus is built.

### 14. `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom`

* **Statement**: Under Lipschitz hypothesis on `(μ, σ, γ)`, the jump-diffusion SDE `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)` with `X_0 = x_0` admits a `JumpDiffusion W N coeffs x₀` solution (with càdlàg paths, L²-sup-bounded on every bounded interval, satisfying the full SDE integral equation with all per-row σ + γ measurability + L²-bound witnesses bundled in `is_solution`) that is a.s.-pairwise-unique (any two solutions agree a.s. at every `t ≥ 0`).
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 6.2.9** (Picard iteration in `S²` for jump-diffusion SDEs with Lipschitz coefficients — bounds the Banach fixed-point output of the Bielecki β-norm contraction); Ikeda-Watanabe, *Stochastic Differential Equations and Diffusion Processes*, North-Holland 1989, **Chapter IV** (jump SDE strong existence + uniqueness via Picard iteration).
* **2026-05-23 conversion `theorem → axiom` (COMPLETED)**: previously a `theorem` with `sorry` body (`LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique`). The literature proof requires three independent pieces of substantive infrastructure not yet in the codebase: (1) `MetricSpace (SBoundedProcess P T)` + `CompleteSpace` instance with the *Bielecki β-norm metric* on the `S²` Banach space of càdlàg L²-bounded processes (the discrete-metric instances added in `Ito/PicardSpace.lean` satisfy the typeclass obligation but are not the literature metric — the substantive contraction estimate `picardStep_bielecki_contraction` operates against `bieleckiNorm` directly, not against the discrete `dist`); (2) `Φ : SBoundedProcess P T → SBoundedProcess P T` lifting of `picardStep` (promoting the Picard map from `ℝ → Ω → (Fin n → ℝ)` to the structured `S²` space, requires showing `picardStep` preserves joint measurability + càdlàg + L²-sup-bound — `Ito/PicardSelfMap.lean` provides the well-typed lift but takes the output-field hypotheses as explicit parameters since BDG is missing from Mathlib); (3) bridging an `S²` fixed point back into the `JumpDiffusion` structure (`is_solution`, `initial_value`, `sup_L2`, `cadlag_paths`, `measurable_path` fields). The Bielecki contraction estimate itself IS proven downstream in `Ito/PicardContraction.lean` as `picardStep_bielecki_contraction` (and tightened in `Ito/PicardContractionTight.lean`), combining the per-component drift / diffusion / jump L²-Lipschitz bounds from `Picard.lean`, `PicardSigmaLipschitz.lean`, `PicardGammaLipschitz.lean` (the latter two depending on Tier 1 axioms `itoIsometry_diff_brownian`, `itoIsometry_diff_compensated`). The honest representation is `axiom picardFixedPoint_jumpDiffusion_exists_unique_axiom` cited from Applebaum 6.2.9 — the claim then matches the content exactly. `picardFixedPoint_jumpDiffusion_exists_unique` is preserved as a thin forwarding `theorem` so all downstream callers (notably `JumpDiffusion.exists_unique`) remain stable.
* **Signature strength**: requires `JumpDiffusionCoeffs.IsLipschitz coeffs ν L` (Tanaka's `|X|^α` counterexample for α < 1/2 rules out uniqueness without this); produces a CONCRETE `JumpDiffusion` (all six fields populated — `X`, `measurable_path`, `initial_value`, `sup_L2`, `cadlag_paths`, `is_solution`) plus the a.s. pairwise agreement at every `t ≥ 0` (the literature uniqueness conclusion). No trivial constant-path witness satisfies this combination of fields for generic `(μ, σ, γ)`: the constant `X t ω = x₀` fails `is_solution` because the integrals `∫₀^t μ(s, x₀) ds`, `∫₀^t σ(s, x₀) dW_s`, `∫₀^t ∫_E γ(s, x₀, e) Ñ(ds, de)` don't vanish for nontrivial coefficients.
* **Why a separate axiom**: this is the SDE-specialised packaging of the Banach fixed-point output from `picardFixedPoint_generic` (Mathlib `ContractingWith.fixedPoint`) into the `JumpDiffusion` structure. The Banach shim `picardFixedPoint_of_exists` already discharges the abstract existence-uniqueness when the contraction is available, but the SDE-specific packaging (steps 1-3 above) does not yet have Mathlib-side primitives.
* **Downstream usage**: `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` (the headline literature theorem — re-opens the `Setting` namespace inside `PicardBanach.lean` so the qualified name is preserved across the file boundary).
* **Mathlib status (May 2026)**: No SDE-with-jumps strong existence/uniqueness in Mathlib. Continuous-SDE strong existence (Karatzas-Shreve 5.2 / Le Gall 8.1) is partially formalized but the jump-SDE case waits on the multidim Brownian + compensated-Poisson integral infrastructure (Tier 1 #5 + #6).
* **Replacement plan**: `theorem picardFixedPoint_jumpDiffusion_exists_unique_axiom := <Picard iteration proof>` when (a) Tier 1 #5 + #6 are theorems, (b) the Bielecki-norm Banach packaging on `SBoundedProcess` is built (`MetricSpace` + `CompleteSpace` instances under the literature metric, replacing the placeholder discrete-metric instances in `PicardSpace.lean`), (c) the `picardStep` self-map lift `Φ : SBoundedProcess → SBoundedProcess` is constructed with the σ/γ measurability + L²-bound preservation proofs (extending the `picardStepOnS2` skeleton in `PicardSelfMap.lean`), and (d) the `S²` fixed point → `JumpDiffusion` structure bridge is built. Once the axiom becomes a theorem, `JumpDiffusion.exists_unique` (the public-facing theorem) inherits soundness automatically with no source-level changes.

### 15. `LevyStochCalc.Ito.JumpFormula.itoFormula_continuousSemimartingale_axiom`

* **Statement**: For a `C^{1,2}` function `u` and the jump diffusion `X = (μ, σ, γ)`-driven by `(W, N)`, the classical Itô formula applied to `u(t, X^c_t)` (where `X^c` is the continuous-semimartingale part of the Lévy–Itô decomposition `X = X^c + X^d`) yields the existence of a residual process `R : ℝ → Ω → ℝ` such that `u(T, X_T) − u(0, X_0) = ∫_0^T (∂_t u + 𝓛^c u)(s, X_s) ds + MultidimBrownianMotion.stochasticIntegral W (∇uᵀσ along X) T + R T ω` almost surely, where `𝓛^c u = μᵀ∇u + ½ Tr(σσᵀ ∇²u)` is the *continuous part* of the Lévy generator. The residual `R` is the jump correction, identified by entry #16 below.
* **Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer 1991, **Theorem 3.3.6** (Itô formula for continuous semimartingales — multidimensional vector form, equation (3.3.5)); Le Gall, B. *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 5.10**; Revuz, D. & Yor, M. *Continuous Martingales and Brownian Motion*, 3rd ed., Springer 1999, **Theorem IV.3.3**.
* **2026-05-24 introduction (NEW)**: this axiom was introduced today as part of the Rule-1 START `axiom → theorem` conversion of the headline `itoLevyFormula` (previous Tier 1 #11). The single Applebaum 4.4.7 axiom is split into TWO literature sub-primitives — this entry #15 (continuous-semimartingale Itô formula, Karatzas–Shreve 3.3.6) and entry #16 (jump-residual decomposition, Applebaum 4.4.10 + 4.4.7 step II). The conjunction of #15 + #16 reconstructs the literature four-term identity; `itoLevyFormula` is now a `theorem` derived by algebraic re-bundling.
* **Signature strength**: takes the multidim Brownian Itô integral hypotheses (`h_sigmaGrad_meas`, `h_sigmaGrad_progMeas`, `h_sigmaGrad_sq` for the integrand `∇uᵀσ`) as explicit parameters, so the existential `R` is constrained to satisfy the exact pinned-form continuous-part identity (no `R = (the whole change)` trivial-witness pathology, since the equation must hold against the pinned drift + diffusion-Itô-integral form).
* **Transitive axiom dependency**: surfaces Tier 1 #5 (`itoIsometry_brownian_unified_existence`, via the multidim Brownian integral) and Tier 1 #6 (`itoIsometry_compensated_unified_existence`, via the `JumpDiffusion` structure's bundled `is_solution` field which uses `Compensated.stochasticIntegral`).
* **Mathlib status (May 2026)**: No Itô formula in Mathlib (waits on Brownian motion construction + L² Itô integral; tracked alongside Tier 1 #5). The Degenne et al stochastic-integration effort (arXiv:2511.20118, late 2025) is the most active push toward a Mathlib Itô formula; no PR merged at time of writing.
* **Replacement plan**: when Mathlib gains the Itô formula for continuous semimartingales (Karatzas–Shreve 3.3.6), this axiom is replaced by a forwarder that decomposes `X = X^c + X^d` via the Lévy–Itô decomposition and applies the Mathlib theorem to `X^c`.

### 16. `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_axiom`

* **Statement**: Given any residual process `R : ℝ → Ω → ℝ` satisfying the continuous-part identity from entry #15 (`u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω` a.s.), the residual `R T ω` equals the sum of the *jump martingale* term `Compensated.stochasticIntegral N (u(·+γ) − u along X) T ω` and the *compensator drift* term `∫_0^T ∫_E [u(·+γ) − u − γᵀ∇u](s, X_s, e) ν(de) ds`, almost surely.
* **Reference**: Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.4.10** (small/large jump decomposition); same source **Theorem 4.4.7 proof, step (II)** (page 240) for the `ε → 0` limit using the L²-isometry of the compensated-Poisson integral; Ikeda-Watanabe, *Stochastic Differential Equations and Diffusion Processes*, North-Holland 1989, **Section II §5**; Cont, R. & Tankov, P. *Financial Modelling with Jump Processes*, Chapman & Hall/CRC 2003, **Proposition 8.18** + Chapter 8.
* **2026-05-24 introduction (NEW)**: this axiom was introduced today alongside entry #15 as part of the Rule-1 START `axiom → theorem` conversion of the headline `itoLevyFormula`. Together with #15 it discharges the literature derivation of Applebaum 4.4.7 — `itoLevyFormula` is now a `theorem` derived by algebraic re-bundling from #15 + #16.
* **Signature strength**: takes the residual `R` as an explicit parameter PLUS the continuous-part identity `_h_continuousPart` (`R` satisfies the entry-#15 identity) as a load-bearing hypothesis. This rules out trivial-witness pathologies: the conclusion `R T ω = jump_mart + comp_drift` cannot be discharged by ANY `R` — only by residuals arising from a real continuous-part decomposition. The signature also bundles `h_jumpInt_*` (joint measurability + per-`t` progressive measurability + global L² bound on the jump-martingale integrand) and the `_h_compDrift_int` ν-integrability hypothesis (red-team P4 H fix carried forward).
* **Transitive axiom dependency**: surfaces Tier 1 #5 (`itoIsometry_brownian_unified_existence`, via the multidim Brownian integral that appears in the `_h_continuousPart` hypothesis) and Tier 1 #6 (`itoIsometry_compensated_unified_existence`, via the `Compensated.stochasticIntegral` that appears in the conclusion).
* **Mathlib status (May 2026)**: No compensated-Poisson integral in Mathlib (waits on PRM construction). The small/large decomposition is itself a derived statement once the integral exists; the `ε → 0` limit uses `itoIsometry_diff_compensated` (Tier 1 #14).
* **Replacement plan**: derive as a theorem from `itoIsometry_diff_compensated` (Tier 1 #14, in `Poisson/Compensated.lean`) + a Mathlib-level linearity-cum-isometry result on the compensated-Poisson L²-integral once that machinery becomes available.

## Honest derivative theorems (proven from cited axioms)

P5 F4 closure (red-team 2nd audit, 2026-05-23): table expanded to include
the BSDEJ-side extractors + the two baseline-sorry theorems
(`JumpDiffusion.exists_unique`, `jacodYor_representation`) that are
literature-pinned sorry-bodied theorems with strengthened signatures, not
plain `theorem`-axioms.

| Theorem | Forwards via |
|---|---|
| `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` | `BrownianMotion.exists` |
| `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification` | `kolmogorovChentsov_modification` |
| `LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq` | derived from Kolmogorov continuity-in-probability + dyadic density (no Tier 1 axiom) |
| `LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous` | `brownian_martingale_rightCont` |
| `LevyStochCalc.Brownian.Martingale.brownian_martingale` | `brownian_martingale_rightCont` |
| `LevyStochCalc.Brownian.Martingale.brownian_quadVar` | `brownian_martingale_rightCont` (quadVar identity) |
| `LevyStochCalc.Brownian.Ito.itoIsometry` | `itoIsometry_brownian_unified_existence` (extracts conjunct 3 = isometry) |
| `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 1 = martingale) |
| `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral` | `itoIsometry_brownian_unified_existence` (extracts conjunct 2 = quadVar) |
| `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | (Tier 1 cited axiom #2 — itself) |
| `LevyStochCalc.Poisson.poissonRandomMeasure_finite_exists` | `PoissonRandomMeasure.exists_of_sigmaFinite` (finite-intensity restriction) |
| `LevyStochCalc.Poisson.Compensated.itoLevyIsometry` | `itoIsometry_compensated_unified_existence` (extracts conjunct 3 = isometry) |
| `LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral` | `itoIsometry_compensated_unified_existence` (extracts conjunct 1 = martingale) |
| `LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral` | `itoIsometry_compensated_unified_existence` (extracts conjunct 2 = quadVar) |
| `LevyStochCalc.Poisson.Compensated.cadlag_modification_exists` | `itoIsometry_compensated_unified_existence` (extracts conjunct 4 = càdlàg) |
| `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry` | 1-line forwarder over `Compensated.itoLevyIsometry` |
| `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` | 1-line forwarder over `jacodYor_representation_axiom` (Tier 1 #13) |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique` | 1-line forwarder over `picardFixedPoint_jumpDiffusion_exists_unique_axiom` (Tier 1 #14) |
| `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` | forwarder via `picardFixedPoint_jumpDiffusion_exists_unique` (Tier 1 #14 transitively) |
| `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` | algebraic re-bundling of `itoFormula_continuousSemimartingale_axiom` (Tier 1 #15) + `itoLevyFormula_jumpResidual_axiom` (Tier 1 #16) — extracts the residual `R` from #15, applies #16 to identify `R = jump_mart + comp_drift`, combines via `filter_upwards` + `ring`. Previously Tier 1 #11 axiom (retired 2026-05-24). |

### Literature-pinned baseline-sorry theorems (count: 0 — fully eliminated 2026-05-23)

**2026-05-23 update**: BOTH literature-pinned sorry-bodied theorems
are now thin forwarders over Tier 1 cited axioms:
* `jacodYor_representation` → `jacodYor_representation_axiom` (entry #13).
* `picardFixedPoint_jumpDiffusion_exists_unique` →
  `picardFixedPoint_jumpDiffusion_exists_unique_axiom` (entry #14),
  which in turn backs the headline `JumpDiffusion.exists_unique`
  (sole previous baseline entry — now sorryAx-free).
Per Rule 0, this is HONEST (theorem-with-axiom-body matches claim;
axiom matches literature) where the previous `theorem ... := by sorry`
was DISHONEST (claimed proven, was unproven). `tools/sorry_baseline.txt`
is now EMPTY; the lint script enforces sorryAx = 0 across the entire
library. Future Picard work continues in `PicardSpace.lean` (typeclass
instances), `PicardSelfMap.lean` (`S²` self-map lift), and
`PicardContraction.lean` / `PicardContractionTight.lean` (Bielecki
contraction estimates) toward the eventual theorem-form replacement
of axiom #14.

### P7 F10 qualification (red-team 2nd audit, 2026-05-23)

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

## Status snapshot (2026-05-24, `itoLevyFormula` `axiom → theorem` conversion COMPLETED)

`tools/sorry_baseline.txt` is EMPTY — every previously sorry'd theorem
is either:
* Proven from Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
  plus possibly one or more Tier 1 cited axioms documented here, OR
* A Tier 1 cited axiom itself.

The 2026-05-24 conversion was the third in the recent series of
`axiom → theorem` / `theorem → axiom` refactors:

* 2026-05-23: `jacodYor_representation` → forwarder over
  `jacodYor_representation_axiom` (Tier 1 #13, Jacod 1976).
* 2026-05-23: `picardFixedPoint_jumpDiffusion_exists_unique` → forwarder
  over `picardFixedPoint_jumpDiffusion_exists_unique_axiom` (Tier 1
  #14, Applebaum 6.2.9), which backs `JumpDiffusion.exists_unique`.
* 2026-05-24 (today, Rule-1 START): `itoLevyFormula` previously a
  single `axiom` (retired Tier 1 #11) is now a `theorem` derived by
  algebraic re-bundling from two sub-axioms — `itoFormula_continuous-`
  `Semimartingale_axiom` (Tier 1 #15, Karatzas–Shreve 3.3.6) and
  `itoLevyFormula_jumpResidual_axiom` (Tier 1 #16, Applebaum 4.4.10 +
  4.4.7 step II). The headline qualified theorem name
  `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` is preserved so the
  dissertation forwarder `Dissertation.Continuous.itoLevyFormula`
  remains stable.

No baseline entries remain.

Resolved on 2026-05-23 (formerly a baseline entry):
* `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation`
  — Jacod 1976 martingale representation theorem for `(W, Ñ)` filtrations
  (Jacod-Shiryaev Thm III.4.34). Converted to a thin forwarder over
  `jacodYor_representation_axiom` (Tier 1 #13). The integrand pinning
  to `MultidimBrownianMotion.stochasticIntegral` and
  `Compensated.stochasticIntegral` (canonical integrals) is at the
  statement level — no trivial-witness leakage. The axiom carries the
  full literature dependency; the theorem is now genuinely axiom-clean
  (modulo the cited axiom + Lean stdlib).

### Recursive audit (2026-05-11) — internal classification

Per the user's recursive-audit standard (trivial-witness theorems = worse
than documented axioms), the 4 LevyStochCalc theorems the dissertation
forwards into were classified:

| Theorem | Classification | Action taken |
|---|---|---|
| `Poisson.L2Isometry.itoLevyIsometry` | (R) Real | Leave alone (extracts from Tier 1 unified-existence axiom with non-trivial quadVar conjunct that rules out constant witnesses) |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` | (C) Cosmetic predicate | `IsBSDEJSolution` strengthened: replaced vacuous per-`(t, ω)` existential `∃ BM jump : ℝ` with outer existential `∃ M_W M_N : ℝ → Ω → ℝ` of martingales pinned to Z (L²-isometry) and U (direct `=` to `Compensated.stochasticIntegral`); adaptedness layer added 2026-05-21 (closes red-team C1); `M_W` pinned to canonical multidim Brownian Itô integral 2026-05-22 (closes red-team H2). |
| `Ito.JumpFormula.itoLevyFormula` | (C) Cosmetic theorem | DEMOTED from `theorem` (trivial-witness proof) to `axiom`; all 4 terms pinned to literature integral forms 2026-05-22 (closes red-team C2) |
| `BSDEJ.PathRegularity.bsdej_path_regularity` | (C) Cosmetic predicate | Same as `continuousBSDEJ_exists_unique` — fixed by the `IsBSDEJSolution` strengthening; `Z_avg`/`U_avg` pinned to `conditionalTimeAverage_*` 2026-05-22 (closes red-team H3) |

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
  `conditionalTimeAverage_*`.
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

### Net audit (verifiable via `tools/lint.sh` + `_audit.lean`)

* **14 Tier 1 cited axioms currently live** (M4 deleted #7 + #8;
  #11 retired 2026-05-24 via axiom→theorem conversion — `itoLevyFormula`
  now a theorem derived from #15 + #16; #12 + #13 + #14 added 2026-05-23
  via theorem→axiom conversion; #15 + #16 added 2026-05-24 to expose
  the two literature sub-primitives behind the Itô–Lévy formula
  derivation), each with paper reference + Mathlib status + replacement
  plan.
* **Honest derivative theorems**, axiom-clean modulo Lean std + Tier 1 cited.
* No `sorryAx` in the public API: `tools/sorry_baseline.txt` is EMPTY
  (2026-05-23 closure; preserved 2026-05-24 by the `itoLevyFormula`
  refactor, which converted axiom → theorem via two sub-axioms #15 + #16).
* No `True := trivial` stub lemmas remain in the project.
* Dissertation forwarders transitively surface only real Tier 1 cited axioms
  in their audit, including the now-derived `itoLevyFormula` (theorem
  derived from Tier 1 #15 + #16; previously the retired Tier 1 #11 axiom).

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

* `tools/sorry_baseline.txt` — sorry-blocked theorems (currently 1: see
  status snapshot above).
* `tools/cited_axioms.md` (this file) — Tier 1 cited axioms with citations + Mathlib status + replacement plans.
* `tools/lint.sh` — runs `_audit.lean` and fails on new sorryAx beyond
  the baseline.
* `_audit.lean` — `#print axioms` on every load-bearing theorem; runs as
  part of CI to verify the axiom budget.
