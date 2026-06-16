# Cited Axioms

Theorems in `LevyStochCalc` that depend on **paper-cited stochastic calculus axioms**.
Each entry below names an axiom whose statement is a real published theorem,
introduced as `axiom <name> : <statement>` with a docstring giving the citation.

The `tools/lint.sh` script flags only `sorryAx`-tainted theorems. Cited axioms
are introduced as Lean `axiom` declarations and do NOT count as `sorryAx`.

## Tier 1: Honest cited axioms (13 currently live)

**History** (3rd audit reconciliation 2026-05-27):
* #3 (`kolmogorovChentsov_modification`) was PROVED axiom→theorem 2026-06-16: a
  from-scratch Karatzas–Shreve 2.2.8 / Le Gall 2.9 proof on the current mathlib
  pin (per-dyadic-level Markov bound → Borel–Cantelli a.s. dyadic Hölder →
  `extendFrom` continuous extension), depending only on the 3 standard axioms.
  It is now a `theorem`; its consumer `brownian_continuous_modification` is
  unchanged. Entry #3 retained below for provenance, marked RESOLVED.
* #7 and #8 deleted 2026-05-22 (dead post-refactor per M4).
* #11 retired 2026-05-24 via decomposition into the new #15 + #16
  (`itoLevyFormula` is now a derived theorem).
* #12 and #13 added 2026-05-23 via theorem→axiom conversion of the previously
  sorry-bodied `JumpDiffusion.exists_unique` and `jacodYor_representation`.
* #13 was DECOMPOSED 2026-05-26 into two strictly narrower sub-axioms #13a +
  #13b; the prior monolithic `jacodYor_representation_axiom` is now a derived
  theorem; the public `jacodYor_representation` is preserved as a thin
  forwarder.
* #14 was added 2026-05-23 then converted axiom→theorem 2026-05-26 via the
  Bielecki AE-quotient infrastructure in `PicardSpace.lean`;
  `picardFixedPoint_jumpDiffusion_exists_unique_axiom` is now a thin forwarder
  over `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`, the latter
  carrying a single explicit `sorry` baseline entry.
* #12 (`JumpDiffusion.exists_unique`) was similarly demoted axiom→theorem on
  2026-05-26 (forwards through the same Bielecki wrap-up).
* #16 was NARROWED 2026-05-26 from the previous universal-`R` form
  `itoLevyFormula_jumpResidual_axiom` to the canonical-`R` form
  `itoLevyFormula_jumpResidual_canonical_axiom`; the universal-`R` form is
  now a derived theorem.
* #17 and #18 added 2026-05-27 by the 3rd-audit reconciliation: the two
  `_diff` axioms (`itoIsometry_diff_brownian`, `itoIsometry_diff_compensated`)
  have lived in source since 2026-05-23 but were never assigned formal Tier 1
  numbers in this file (they appeared as undocumented axioms in the 3rd-audit
  CRITICAL #1 finding). They are the per-difference L²-isometries used by the
  Picard contraction estimates and the Itô-Lévy formula (#16).

Retired/deleted entries (#7, #8, #11, #12, #13, #14) and resolved-by-proof
entries (#3, proved 2026-06-16) are kept as `### Retired #N` / `### Resolved #N`
headings below for traceability; they are NOT counted in the headline "13
currently live" figure. Only `### N.` (digit-leading) headings correspond to
live axioms, so `grep -c "^### [0-9]" tools/cited_axioms.md == 13`.

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

### Resolved #3: `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification` (proved axiom→theorem 2026-06-16)

* **Statement**: A real-valued process satisfying the Kolmogorov moment condition with `q > 1` admits a modification with continuous paths.
* **Reference**: Karatzas–Shreve **Theorem 2.2.8**; Le Gall **Theorem 2.9**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, Springer 1999, **Theorem I.2.1**.
* **Status**: No longer an axiom — proved from scratch as a `theorem` (mathlib has only `IsKolmogorovProcess`, the condition; the continuity conclusion is supplied here). Proof: `kc_level_bad_measure` (per-level Markov/union bound) → `kc_ae_increment_bound` (Borel–Cantelli) → `dyadic_holder_chaining` + `kc_ae_nbhd_holder` (a.s. local Hölder) → `exists_tendsto_of_local_holder` + `continuous_extendFrom` (continuous modification) → `kolmogorov_modification_ae_eq` (modification property). `#print axioms` → `propext, Classical.choice, Quot.sound` only.

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

### 15. `LevyStochCalc.Ito.JumpFormula.itoFormula_continuousSemimartingale_axiom`

* **Statement**: For `u ∈ C^{1,2}` and a jump-diffusion `X = (μ, σ, γ)`-driven by `(W, N)`, the classical continuous-semimartingale Itô formula (Karatzas–Shreve 3.3.6) applied to `u(t, X^c_t)` (where `X^c` is the continuous-semimartingale part in the Lévy–Itô decomposition `X = X^c + X^d`) produces the drift + diff-mart identity with an existential residual `R`: there exists `R : ℝ → Ω → ℝ` such that a.s.,  `u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω`.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer 1991, **Theorem 3.3.6** (Itô formula for continuous semimartingales — multidimensional vector form, equation (3.3.5)); Le Gall, *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, **Theorem 5.10**; Revuz–Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer 1999, **Theorem IV.3.3**.
* **Mathlib status (May 2026)**: No Itô formula in Mathlib (waits on Brownian motion construction + L² Itô integral; tracked alongside Tier 1 #5). The Degenne et al stochastic-integration effort (arXiv:2511.20118, late 2025) is the most active push toward a Mathlib Itô formula; no PR merged at time of writing.
* **Replacement plan**: when Mathlib gains the Itô formula for continuous semimartingales (Karatzas–Shreve 3.3.6), this axiom is replaced by a forwarder that decomposes `X = X^c + X^d` via the Lévy–Itô decomposition and applies the Mathlib theorem to `X^c`.

### 16. `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_canonical_axiom` (NARROWED 2026-05-26 from previous monolithic #16)

* **Statement**: For the *canonical* residual `R_canonical T ω := u(T, X_T) − u(0, X_0) − drift − diff_mart` (constructed by direct subtraction from the LHS, with no quantification over arbitrary `R`s), we have `R_canonical T ω = jump_mart_T(ω) + comp_drift_T(ω)` a.s., where `jump_mart_T = Compensated.stochasticIntegral N (u(·+γ) − u along X) T` and `comp_drift_T(ω) = ∫_0^T ∫_E [u(·+γ) − u − γᵀ∇u](s, X_s, e) ν(de) ds`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.4.10** (small/large jump decomposition); same source **Theorem 4.4.7** proof **step (II)** for the `ε → 0` limit (page 240); Ikeda–Watanabe **Section II.5**; Cont–Tankov **Proposition 8.18** + Chapter 8.
* **Narrowness (2026-05-26 narrowing)**: the previous monolithic #16 (`itoLevyFormula_jumpResidual_axiom`, universal-`R` form) quantified over *any* `R` satisfying a continuous-part identity `u(T, X_T) − u(0, X_0) = drift + diff_mart + R T ω`. The 2026-05-26 narrowing eliminates that quantifier: the axiom now asserts the identity only for the canonical `R` constructed by direct subtraction. The universal-`R` form (`itoLevyFormula_jumpResidual_axiom`) is now a derived theorem forwarding over this canonical axiom by per-ω algebra (`R = R_canonical` a.s. when both satisfy the continuous-part identity). The narrower axiom captures exactly the analytical content of Applebaum 4.4.10 + 4.4.7 step II (the small/large-jump decomposition + ε→0 L²-limit + Lévy-Itô combinatorial step); the universal-`R` form adds only algebraic glue.
* **Mathlib status (May 2026)**: No compensated-Poisson integral in Mathlib (waits on PRM construction). The small/large decomposition is itself a derived statement once the integral exists; the `ε → 0` limit uses `itoIsometry_diff_compensated` (Tier 1 #18, in `Poisson/Compensated.lean`).
* **Replacement plan**: derive as a theorem from `itoIsometry_diff_compensated` + a Mathlib-level linearity result on the compensated-Poisson L²-integral once that machinery becomes available.

### 17. `LevyStochCalc.Brownian.Ito.itoIsometry_diff_brownian` (added 2026-05-23; documented 2026-05-27 per 3rd-audit reconciliation)

* **Statement**: For two jointly-measurable, progressively-measurable, square-integrable integrands `H₁, H₂ : Ω → ℝ → ℝ`, the L² norm of the difference of their Brownian Itô integrals at any `T > 0` equals the L² norm of the integrand difference: `𝔼 |∫_0^T H₁ dW − ∫_0^T H₂ dW|² = 𝔼 ∫_0^T |H₁(s) − H₂(s)|² ds`.
* **Reference**: Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem 3.2.6** + §3.2.B equation (2.20) (the L²-Itô integral is a continuous linear isometry from `L²(Ω × [0, T])` to `L²(Ω)`; the per-difference identity is the linear-isometry property applied to `(H₁ − H₂)`).
* **Why a separate axiom**: in the present axiomatization `stochasticIntegral W H` is constructed via `Classical.choose` on `itoIsometry_brownian_unified_existence` (Tier 1 #5). The choose-witness depends on the integrand, so the difference-of-choices is not syntactically the choice-of-difference; linearity is not available from Tier 1 #5 alone. The per-difference isometry is therefore stated separately and used downstream in the σ-side Picard contraction estimate (`picardStep_diffusion_diff_lipschitz_sq_componentwise` in `Ito/Picard.lean`).
* **Mathlib status (May 2026)**: same status as Tier 1 #5 — no general L²-Itô integral against Brownian motion in Mathlib (waits on BM construction). When Mathlib's L²-Itô integral lands as a continuous linear map, this axiom becomes a forwarder over its linearity + isometry.
* **Replacement plan**: `theorem itoIsometry_diff_brownian := <linearity ∘ isometry>` when Mathlib's L²-Itô integral exposes the continuous-linear-isometry structure (likely follow-up to the Degenne et al stochastic-integration effort, arXiv:2511.20118).

### 18. `LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated` (added 2026-05-23; documented 2026-05-27 per 3rd-audit reconciliation)

* **Statement**: For two jointly-measurable, progressively-measurable, square-integrable integrands `φ₁, φ₂ : Ω → ℝ → E → ℝ`, the L² norm of the difference of their compensated-Poisson Itô-Lévy integrals at any `T > 0` equals the L² norm of the integrand difference: `𝔼 |∫_0^T ∫_E φ₁ Ñ − ∫_0^T ∫_E φ₂ Ñ|² = 𝔼 ∫_0^T ∫_E |φ₁(s, e) − φ₂(s, e)|² ν(de) ds`.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 4.2.3** step (II) (the L²-Itô-Lévy integral is a linear isometry from the predictable `H²` space `L²(Ω × [0, T] × E, dP ⊗ ds ⊗ dν)` to `L²(Ω, ℱ_T, P)`; the per-difference identity is the linear-isometry property applied to `(φ₁ − φ₂)`); Ikeda–Watanabe **Section II.3** for the same construction.
* **Why a separate axiom**: same rationale as #17 — in the present axiomatization `Compensated.stochasticIntegral N φ` is constructed via `Classical.choose` on `itoIsometry_compensated_unified_existence` (Tier 1 #6), and the choose-witness depends on the integrand. The per-difference isometry is used downstream by the γ-side Picard contraction estimate (`picardStep_jump_diff_lipschitz_sq_componentwise` in `Ito/Picard.lean`) and by the `ε → 0` limit in the Itô-Lévy formula jump residual axiom (Tier 1 #16).
* **Mathlib status (May 2026)**: blocked on Mathlib gaining a compensated-Poisson L²-integral (waits on PRM construction — Tier 1 #2). No current Mathlib activity in this direction.
* **Replacement plan**: `theorem itoIsometry_diff_compensated := <linearity ∘ isometry>` when Mathlib gains a compensated-Poisson L²-integral as a continuous linear map.

### Retired #12: `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` (DEMOTED axiom→theorem 2026-05-26)

* **Statement**: Under Lipschitz hypothesis on `(μ, σ, γ)`, the jump-diffusion SDE `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)` with `X_0 = x_0` admits a strong solution (with càdlàg paths, L²-sup-bounded on every bounded interval) that is a.s. unique.
* **Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, **Theorem 6.2.9**; Ikeda-Watanabe, *Stochastic Differential Equations and Diffusion Processes*, North-Holland 1989, Chapter IV.
* **2026-05-23 refactor + axiomatization (COMPLETED)**: the theorem moved out of `Ito/Setting.lean` and into `Ito/PicardFixedPoint.lean`, where it forwards through a SINGLE intermediate `picardFixedPoint_jumpDiffusion_exists_unique` (the SDE-specialised Banach fixed-point output). That intermediate was previously a `theorem` with a `sorry` body; it was converted on 2026-05-23 to a thin forwarder over the (then-)Tier-1 axiom `picardFixedPoint_jumpDiffusion_exists_unique_axiom`. On 2026-05-26 the axiom was further demoted to a theorem (forwarding through the wrap-up `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` in `PicardSpace.lean`, which carries a single explicit baseline `sorry`). Consequently `JumpDiffusion.exists_unique` is sorryAx-baselined (via the wrap-up) — its transitive axiom dependency now surfaces `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`'s sorry rather than a standalone axiom. The qualified name `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` is preserved by re-opening the namespace in `PicardFixedPoint.lean`.
* **Signature strength**: requires `JumpDiffusionCoeffs.IsLipschitz coeffs ν L` (Tanaka's `|X|^α` counterexample for α < 1/2 rules out uniqueness without this).
* **Mathlib status (May 2026)**: No SDE-with-jumps strong existence/uniqueness in Mathlib. Continuous-SDE strong existence is partially formalized but the jump-SDE case waits on the multidim Brownian + compensated-Poisson integral infrastructure.
* **Replacement plan**: When the wrap-up theorem `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` is fully proven (Bielecki packaging + structure bridge + the descended Picard contraction chain), `JumpDiffusion.exists_unique` inherits soundness automatically with no source-level changes.

### Retired #13: `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom` (DEMOTED axiom→theorem 2026-05-26)

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

### 13a. `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_PRP_martingale_axiom`

* **Statement**: For every L²-bounded càdlàg martingale `M` on the joint right-continuous filtration `ℱ = ((⨆ i, σ(W_i)) ⊔ σ(N)).rightCont`, there exist progressively-measurable square-integrable integrands `Z, U` such that `M_t = M_0 + ∫_0^t Z_s · dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)` a.s. at every `t ∈ [0, T]`. Both stochastic integrals are pinned to `MultidimBrownianMotion.stochasticIntegral` and `Compensated.stochasticIntegral` (canonical forms).
* **Reference**: Jacod, J. (1975/76) Z. Wahrsch. Verw. Gebiete 31(3); Jacod-Shiryaev, *Limit Theorems for Stochastic Processes*, 2nd ed., Springer 2003, **Theorem III.4.34** (stated in EXACTLY the martingale-input form of this sub-axiom — the conditional-expectation construction for a generic L² random variable is handled separately by #13b below).
* **Narrowness**: this is the LITERAL content of Jacod-Shiryaev III.4.34. It is the deep mathematical content of the two-source martingale representation theorem. No conditional-expectation / Doob-regularization step appears — those are factored out into #13b.
* **Mathlib status (May 2026)**: No predictable projection / chaos decomposition in Mathlib for general (W, N) filtrations. Continuous-Brownian-only chaos decomposition is partially in `Mathlib.Probability.Process.WienerChaos` (early-stage at time of writing).
* **Replacement plan**: `theorem jacodYor_PRP_martingale_axiom := <predictable projection + chaos decomposition>` when (a) Tier 1 #5 + #6 are theorems, (b) the projection / decomposition apparatus is built.

### 13b. `LevyStochCalc.BSDEJ.MartingaleRepresentation.condExp_to_PRP_martingale_form_axiom`

* **Statement**: For every L² random variable `ξ : Ω → ℝ` that is `ℱ_T`-measurable on the joint right-continuous (W, N) filtration, there exists a càdlàg L²-bounded `ℱ`-martingale `M` with `M_0 = ∫ ξ ∂P` a.s. (the deterministic expectation) and `M_T = ξ` a.s.
* **Reference**: Karatzas-Shreve, *Brownian Motion and Stochastic Calculus*, Springer 1991, **Theorem I.3.13** (Doob L² càdlàg regularization for right-continuous filtrations); Karatzas-Shreve **Theorem 2.7.17** (Blumenthal 0-1 for the Brownian factor, giving `𝔼[ξ | ℱ_0] = ∫ ξ ∂P` a.s.); Applebaum **Theorem 2.3.7** (analog Blumenthal-style 0-1 for Poisson random measures); Mathlib's `MeasureTheory.condExp_of_stronglyMeasurable` (condExp reproducibility, `𝔼[ξ | ℱ_T] = ξ` a.s.).
* **Narrowness**: this is a STANDARD CLASSICAL BUNDLE of three independent results: (1) Doob L² càdlàg modification on a right-continuous filtration, (2) Blumenthal 0-1 for the joint (W, N) filtration, (3) conditional-expectation reproducibility. Each has independent Mathlib activity / formalization roadmap. The bundle is strictly narrower than the original #13 because it does NOT require any chaos decomposition / predictable projection machinery — only classical martingale + filtration analysis.
* **Mathlib status (May 2026)**: Doob L² càdlàg regularization is NOT yet in Mathlib but is on the roadmap (independent of BM construction; requires only `MeasureTheory.Martingale` + `Filtration.IsRightContinuous`). Blumenthal-for-BM waits on the BM construction (Tier 1 #1). `MeasureTheory.condExp_of_stronglyMeasurable` is already in Mathlib.
* **Replacement plan**: `theorem condExp_to_PRP_martingale_form_axiom := <Doob L² càdlàg modification ∘ Blumenthal 0-1 ∘ condExp_of_stronglyMeasurable>` when the three Mathlib pieces above land.

### Retired #14: `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom` (DEMOTED axiom→theorem 2026-05-26)

On 2026-05-26 this axiom was demoted to a Lean `theorem` forwarding through
the wrap-up `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` in
`LevyStochCalc/Ito/PicardSpace.lean`. The wrap-up theorem
carries a SINGLE explicit `sorry` collecting the entire literature Picard
chain (Applebaum 6.2.9 / Ikeda-Watanabe IV); the chain breakdown is in
that file's module docstring. The forwarder `picardFixedPoint_jumpDiffusion_exists_unique_axiom`
is now listed in the "Honest derivative theorems" table below; the
single baseline-sorry entry in `tools/sorry_baseline.txt` is
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
| `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom` | derived theorem combining Tier 1 sub-axioms #13a (PRP for càdlàg L² (W, N)-martingales) + #13b (condExp→PRP-martingale bridge); was Tier 1 axiom #13 prior to 2026-05-26 decomposition |
| `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` | 1-line forwarder over `jacodYor_representation_axiom` (now a derived theorem transitively over Tier 1 #13a + #13b) |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` | wrap-up theorem in `PicardSpace.lean` (single explicit baseline `sorry` for the entire Picard chain; ex-Tier-1-axiom #14 was demoted 2026-05-26 to a forwarder over this wrap-up) |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom` | 1-line forwarder over `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` (ex-Tier-1-axiom #14, demoted 2026-05-26 — name retained for downstream stability) |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique` | 1-line forwarder over `picardFixedPoint_jumpDiffusion_exists_unique_axiom` (now a theorem; transitively over `_via_aeQuot`) |
| `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` | forwarder via `picardFixedPoint_jumpDiffusion_exists_unique` (transitively over `_via_aeQuot`'s sorry) |
| `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity_linear_rate` | `bsdej_path_regularity` (Tier 1 #10; specializes the polynomial-exponential constant to a single `C : ℝ` evaluated at `(T, L, ‖ξ‖_L²)` so downstream chapters can take `ψ(h) := C · h`) |
| `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_axiom` | derived theorem (was Tier 1 axiom #16 prior to 2026-05-26 narrowing); forwards over Tier 1 #16 `itoLevyFormula_jumpResidual_canonical_axiom` by per-ω algebra (`R = R_canonical` a.s. when both satisfy the continuous-part identity) |
| `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` | derived theorem forwarding over Tier 1 #15 `itoFormula_continuousSemimartingale_axiom` + Tier 1 #16 `itoLevyFormula_jumpResidual_canonical_axiom` (transitively via the universal-`R` derived theorem `itoLevyFormula_jumpResidual_axiom`); the previous Tier 1 #11 axiom (`itoLevyFormula`) was retired 2026-05-24 |

### Literature-pinned baseline-sorry theorems (count: 1 — 2026-05-26 update)

**2026-05-26 update**: the Picard chain wrap-up
`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` is the single
baseline-sorry theorem; ex-Tier-1-axiom #14 (and via the forwarders,
`JumpDiffusion.exists_unique`) transitively depend on this single sorry.

* `jacodYor_representation` → `jacodYor_representation_axiom` (entry #13;
  still an axiom).
* `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` — single
  explicit baseline `sorry`; entire literature Picard chain
  (Applebaum 6.2.9) collected in the wrap-up theorem body (see
  `PicardSpace.lean` module docstring for breakdown).
* `picardFixedPoint_jumpDiffusion_exists_unique_axiom` (ex-#14, now
  theorem) → forwards to `_via_aeQuot`.
* `picardFixedPoint_jumpDiffusion_exists_unique` → forwards.
* `JumpDiffusion.exists_unique` → forwards.

Per Rule 0, this is HONEST: the wrap-up theorem carries an explicit
`sorry` body (visible to the lint pipeline as a baseline-tracked
sorryAx-tainted theorem) rather than being hidden behind an axiom.
`tools/sorry_baseline.txt` contains the single entry
`LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`.
Future Picard work continues in `PicardSpace.lean` / `PicardSpace.lean`
/ `PicardSpace.lean` (Banach packaging), `Picard.lean`
(`S²` self-map lift), `Picard.lean` (Bielecki
contraction estimates) toward fully discharging the wrap-up theorem's
sorry.

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

## Status snapshot (2026-05-26, axiom #14 `axiom → theorem` conversion COMPLETED)

`tools/sorry_baseline.txt` now contains **1 entry** — the Picard
iteration for the jump-diffusion SDE, now exposed as the wrap-up
theorem `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` in
`PicardSpace.lean` (single explicit `sorry`). The
chain `JumpDiffusion.exists_unique` →
`picardFixedPoint_jumpDiffusion_exists_unique` →
`picardFixedPoint_jumpDiffusion_exists_unique_axiom` (now theorem)
→ `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` (sorry)
collapses the previous "ex-Tier-1-axiom #14 → headline" route into
a single sorry-tracked theorem. Every other previously sorry'd
theorem is either:
* Proven from Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
  plus possibly one or more Tier 1 cited axioms documented here, OR
* A Tier 1 cited axiom itself.

Baseline entries (the single genuinely-deferred classical theorem):
* `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`
  — Picard iteration in `S²([0, T]; ℝⁿ)` for the jump-diffusion SDE
  (Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV). Real theorem statement
  with single explicit sorry'd proof body collecting the entire chain.

Resolved on 2026-05-26 (formerly Tier 1 cited axiom #14):
* `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom`
  — converted from a standalone axiom to a 1-line forwarder over the
  wrap-up theorem. The literature dependency (Applebaum 6.2.9 /
  Ikeda-Watanabe IV) is now carried by the wrap-up's explicit
  baseline sorry, not by a free-standing axiom — making the
  unresolved analytical content visible to the lint pipeline.

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

* **13 Tier 1 cited axioms currently live** (#3 proved axiom→theorem
  2026-06-16): #1, #2, #4, #5, #6 (Brownian + Poisson foundations; #3
  Kolmogorov–Chentsov now a theorem), #9 + #10
  (BSDEJ existence + path regularity), #13a + #13b (the two strictly
  narrower sub-axioms `jacodYor_PRP_martingale_axiom` +
  `condExp_to_PRP_martingale_form_axiom` from the 2026-05-26
  decomposition of the previously-monolithic `jacodYor_representation_axiom`,
  now demoted to a derived theorem), #15 + #16 (the two pieces of the
  decomposed Itô-Lévy formula: `itoFormula_continuousSemimartingale_axiom`
  + `itoLevyFormula_jumpResidual_canonical_axiom`, with the previously-
  monolithic Tier 1 #11 `itoLevyFormula` now a derived theorem), and #17
  + #18 (`itoIsometry_diff_brownian` + `itoIsometry_diff_compensated`,
  the per-difference L²-isometries that have lived in source since
  2026-05-23 but were first formally numbered in this file on 2026-05-27).
  Each axiom has paper reference + Mathlib status + replacement plan.
  History markers: M4 deleted #7 + #8 (2026-05-22); #11 retired (2026-05-24);
  #12, #13, #14 demoted axiom→theorem (2026-05-26); #17, #18 added
  to this file (2026-05-27 — 3rd-audit CRITICAL #1 closure).
* **Honest derivative theorems**, axiom-clean modulo Lean std + Tier 1 cited
  + the single baseline-sorry wrap-up theorem.
* `sorryAx` in the public API restricted to the 1 baseline-acknowledged entry
  (`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`); the chain
  `JumpDiffusion.exists_unique` → `_unique` → `_unique_axiom` (now theorem)
  → `_via_aeQuot` transitively surfaces this single sorry.
* No `True := trivial` stub lemmas remain in the project.
* Dissertation forwarders transitively surface only real Tier 1 cited axioms
  + the single baseline sorry, in their audit (including the
  fully-pinned #11 `itoLevyFormula`).

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
