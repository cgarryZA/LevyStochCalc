# LevyStochCalc — Status (2026-09-05)


> **Integrand-class audit (2026-09-06) — both integrals rebuilt the same day (X2-1, X2-2).**
> The `h_progMeas` hypothesis of the stochastic integrals demanded `ℱ t ⊗ Borel`-measurability
> of the whole integrand for *every* `t`, with no restriction to `s ≤ t`; since `ℱ 0` of the
> natural filtrations is P-trivial, every admissible integrand was a.s. constant in `ω` at each
> time. **The Brownian integrals (#5, #17) and the compensated-Poisson integrals (#6, #18) are
> now stated for genuinely progressively measurable integrands**
> (`Probability.ProgressivelyMeasurable ℱ H`, equivalent to Mathlib's `IsStronglyProgressive`,
> and its marked analogue `MarkedProgressivelyMeasurable ℱ φ`) **with respect to any filtration
> for which `W` is a Brownian motion, resp. `N` a Poisson random measure**
> (`IsBrownianFiltration W ℱ`, `IsPoissonFiltration N ℱ`; work packages X2-1/X2-2 in `Plan.md`).
> **X2-3 (2026-09-06)** puts both integrands on ONE filtration: `JumpDiffusion.is_solution`,
> #16, `Ito/Picard*` and `IsBSDEJSolution` are stated for a single `ℱ` carrying both driver
> properties (`∀ j, IsBrownianFiltration (W.W j) ℱ` and `IsPoissonFiltration N ℱ`), and #13b
> over a `LevyDriver` and its `ℱ₊`. Coupled `(σ, γ)` are therefore in scope. **X2-4** builds a
> `LevyDriver` on a product space (`Driver/Existence.lean`), so that filtration hypothesis is
> satisfiable — it is satisfiability of the hypothesis, not existence of SDE/BSDEJ solutions.
> Full argument: `tools/cited_axioms.md`, "Integrand-class audit".

## Headline

**Library builds clean** (`lake build`: 3286 jobs, no errors; Mathlib `81a5d257` /
Lean `v4.32.0` since decision D1, with `RemyDegenne/brownian-motion` as a lake dependency).
**Lint passes** (`bash tools/lint.sh`: PASS at baseline of the
JumpDiffusion Picard-chain wrap-up sorry — see below).

## Sorry baseline (1 mathematical entry; 4 transitive forwarders)

There is a single genuinely-deferred classical theorem; the four
`tools/sorry_baseline.txt` lines are forwarders that all bottom out in
the same wrap-up sorry:

| Theorem | Citation | Role |
|---|---|---|
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` | Applebaum 2009 Thm 6.2.9 / Ikeda-Watanabe IV | Single explicit `sorry` for the Picard iteration in `S²([0,T]; ℝⁿ)` |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom` | (transitive) | 1-line forwarder over `_via_aeQuot` |
| `LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique` | (transitive) | 1-line forwarder |
| `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` | (transitive) | 1-line forwarder |

The wrap-up theorem has an honest statement (no trivial-witness in the
conclusion): the SDE integral equation is the `JumpDiffusion W N coeffs x₀`
structure's `is_solution` field, which is the literature Itô-with-jumps
integral equation in full form.

Previously, `BSDEJ.MartingaleRepresentation.jacodYor_representation` and
`Ito.JumpFormula.itoLevyFormula` were sorry'd. Both are now derived
theorems forwarding through honest Tier 1 cited axioms (the
#13a + #13b decomposition for jacodYor; #15 + #16 for itoLevyFormula).

## Tier 1 cited axioms (2 currently live)

See `tools/cited_axioms.md` for the full inventory. Numbering history:
#7 + #8 deleted 2026-05-22 (dead post-refactor per M4); #11 retired
2026-05-24 by decomposition into #15 + #16; #12 + #13 added 2026-05-23
via theorem→axiom promotion and then demoted axiom→theorem 2026-05-26
via the #13a/#13b decomposition + Bielecki AE-quotient wrap-up; #14
added 2026-05-23 then demoted axiom→theorem 2026-05-26; #16 narrowed
2026-05-26 from universal-`R` to canonical-`R` form; #17 + #18 added
in source 2026-05-23 and formally numbered in `tools/cited_axioms.md`
on 2026-05-27 (3rd-audit CRITICAL #1 closure). **Sorry baseline now has
1 entry**: `picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`
(carries the entire literature Picard chain for Applebaum 6.2.9).

* **Brownian foundations** (0 axioms): `BrownianMotion.exists` (#1, a theorem since
  2026-09-05 via RemyDegenne/brownian-motion), `kolmogorovChentsov_modification` (#3,
  2026-06-16), `brownian_martingale_rightCont` (#4, 2026-09-06, by the right-`L¹`-continuity
  lift `Martingale/RightCont.lean`), `itoIsometry_brownian_unified_existence` (#5,
  2026-06-17).
* **Compensated-Poisson foundations** (0 axioms): `PoissonRandomMeasure.exists_of_sigmaFinite`
  (#2, a theorem since 2026-09-06 by the Poisson recipe — cells `[n, n+1) × sₘ` of a σ-finite
  decomposition, a Poisson number of iid marks per cell, superposed; see
  `Poisson/PoissonSplitting.lean`, `Poisson/PoissonSuperposition.lean`,
  `Poisson/RandomMeasure.lean`) and `itoIsometry_compensated_unified_existence` (#6,
  2026-09-06 — the càdlàg modification of the `L²`-limit of mark-step integrals, see
  `Poisson/Compensated.lean`).
* **BSDEJ** (1 axiom): `condExp_to_PRP_martingale_form_axiom` (#13b). **Retired
  2026-09-06 as refutable statements** (`tools/cited_axioms.md`): `continuousBSDEJ_exists_unique`
  (#9: arbitrary non-adapted `X`; single-driver integrand class), `bsdej_path_regularity` (#10:
  the `C·Δt` rate for merely measurable `g`, `X`), `jacodYor_PRP_martingale_axiom` (#13a:
  single-driver integrands for a joint-filtration martingale; `W·Ñ` is a counterexample) and the
  theorems derived from them (`jacodYor_representation(_axiom)`,
  `bsdej_path_regularity_linear_rate`, `bsdej_U_L2_regularity_linear_rate`). Since X2-3 the
  common filtration those corrected statements need is available; restating and proving them
  is work packages A6/A7 and B5 in `Plan.md`.
* **Itô-Lévy formula** (1 axiom): `itoLevyFormula_jumpResidual_canonical_axiom`
  (#16). The former #15 `itoFormula_continuousSemimartingale_axiom` was retired
  2026-09-06: its statement (an unconstrained existential residual) was
  trivially satisfiable; `itoLevyFormula` now forwards over #16 alone.
  **Statement audit 2026-09-06**: #16 now assumes `u ∈ C²` jointly and an
  integrable drift along the path — without them its Lean statement was
  refutable (`fderiv`/`deriv` and the Bochner integral vanish where the
  hypotheses fail). Since X2-3 both its Brownian and its Poisson integrands are
  progressively measurable for one common filtration `ℱ` carrying both driver
  properties, so `JumpDiffusion.is_solution`, #16 and `IsBSDEJSolution` cover
  coupled coefficients, and X2-4 constructs a Lévy driver whose joint filtration
  is such an `ℱ`. See `tools/cited_axioms.md` #16.
* **SDE existence/uniqueness** (0 axioms, 1 `sorry`): the Picard chain
  (`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` and its three
  forwarders). **Statement audit 2026-09-06 (A6-1)**: all four now take a
  filtration `ℱ` with both driver properties. Without it the claim was false for
  a dependent `(W, N)` — no such filtration exists there, so `JumpDiffusion` is
  uninhabited and the `sorry` was undischargeable as stated. See
  `tools/cited_axioms.md`, Retired #14.
* **Toward #13b** (0 axioms closed yet): the analytic input of the Doob regularization is in
  place — the conditional expectation is right-continuous in `L²` along a right-continuous
  filtration on `ℝ` (`Probability/CondExpRightContinuous.lean`,
  `tendsto_condExpL2_nhdsGT`), over the downward convergence along a decreasing sequence of
  σ-algebras (`Probability/CondExpInf.lean`, `tendsto_condExpL2_of_antitone`), which in turn
  rests on the Hilbert-space limit of `Probability/ProjectionLimit.lean` and the identification
  of `⨅ n, lpMeas (m n)` from `Probability/AEMeasurableInf.lean`. Mathlib has the upward
  statement (`Integrable.tendsto_eLpNorm_condExp`) but not this one.
  `Probability/Augmentation.lean` (`aug_iInf_of_antitone`, augmentation by the `μ`-null sets
  commutes with a countable antitone infimum) was the originally planned route; the `limsup`
  argument reaches the same place without it, so it is no longer on the path. Tickets `A1a`,
  `A1b`, `A1c` of `../Dissertation/WORK_BREAKDOWN.md`; `A3a`–`A3d` remain.
* **Per-difference L²-isometries** (0 axioms — used by Picard contraction
  estimates and the #16 `ε → 0` limit): `itoIsometry_diff_brownian` (#17,
  a theorem since 2026-06-17), `itoIsometry_diff_compensated` (#18, a theorem
  since 2026-09-06 via `process_sub_lintegral_sq`).

## Recent activity (2026-05-22)

Following a 12-persona red-team audit that identified 24+ findings, all
9 CRITICAL and 8 HIGH findings were closed:

* **Soundness (C1, H1, H2)**: `IsBSDEJSolution` predicate strengthened
  with adaptedness layer + canonical multidim Brownian Itô integral
  pin for `M_W`.
* **Trivial-witness (C2, C3, C4, M1)**: `itoLevyFormula` axiom statement
  pinned to literature integral forms for all 4 terms; trivial-witness
  proof bodies on `JumpDiffusion.exists_unique` /
  `jacodYor_representation` replaced with honest sorries (in baseline);
  8 `True := trivial` stub lemmas deleted.
* **Hidden sorryAx (C5)**: `kolmogorov_modification_ae_eq` fully proved
  (no longer sorryAx); `poissonRandomMeasure_finite_exists` forwarded
  to the σ-finite cited axiom; `simplePredictable_dense_L2` dead chain
  (~540 lines) deleted.
* **Citations (C6, C7, H7, H8, M13)**: Gnoatto 2025 fabrication →
  Andersson-Gnoatto-Patacca-Picarelli 2025; Bouchard-Elie-Touzi 2009
  → Bouchard-Elie 2008; 3 Le Gall theorem-number errors corrected.
* **Git hygiene (C8, C9, H10)**: previously-untracked source files +
  build configs committed; `tools/lint.sh` hardened to fail on missing
  `_audit.lean`; `lake-manifest.json` fixed.
* **Hypothesis hygiene (H4, H5)**: Lipschitz + L²-terminal hypotheses
  added to BSDEJ axioms; `itoIsometry_compensated_unified_existence`
  gained `h_meas`/`h_sq_int` outer hypotheses to close the
  `integral_undef` exploit.
* **Path regularity (H3)**: `Z_avg`/`U_avg` pinned to
  `conditionalTimeAverage_*` projections.
* **Dead-code cleanup (M2, M3)**: 677-line orphan `Poisson/Martingale.lean`
  deleted; 4 dead-code `sorry` private lemmas eliminated.
* **Documentation (M6)**: `tools/cited_axioms.md` status section
  refreshed with full per-finding fix log.

## Architecture

```
LevyStochCalc/
├── Basic.lean                                 — common imports + L² bridge lemmas
├── Brownian/
│   ├── Construction.lean                      — BrownianMotion structure
│   ├── Existence.lean                         — BrownianMotion.exists (ex-Tier-1 #1, thm)
│   ├── Continuity.lean                        — KC modification + ae_eq
│   ├── Martingale.lean                        — naturalFiltration W + Tier 1 #4 axiom
│   ├── Ito.lean                               — L² Itô integral (4000+ lines)
│   ├── SimplePredictableRefine.lean           — Tier 1 #5 axiom
│   ├── Multidim.lean                          — multidim BM structure
│   └── MultidimIto.lean                       — multidim L² Itô integral
├── Poisson/
│   ├── RandomMeasure.lean                     — PRM structure + existence (#2, a theorem)
│   ├── NaturalFiltration.lean                 — filtration definition
│   ├── Compensated.lean                       — L² Itô-Lévy integral (2900+ lines)
│   │                                            + Tier 1 auxiliary axiom
│   │                                            itoIsometry_diff_compensated
│   ├── L2Isometry.lean                        — public isometry forwarder
│   ├── IndependentScattering.lean             — σ-algebra independent scattering
│   └── MathFinBridge.lean                     — PRM bridge to formal-mathfin (#6 isometry conjunct)
├── Ito/
│   ├── Setting.lean                           — JumpDiffusion structure
│   ├── JumpFormula.lean                       — Tier 1 #15 + #16 axioms + derived
│   │                                            #11/#16 universal-R theorems
│   ├── Picard.lean                            — Picard map + Bielecki β-norm framework,
│   │                                            σ/γ L² Lipschitz bounds (auxiliary axiom
│   │                                            itoIsometry_diff_brownian), self-map and
│   │                                            Bielecki contraction
│   ├── PicardSpace.lean                       — complete metric space of bounded processes:
│   │                                            discrete metric + Bielecki β-norm AE-quotient
│   │                                            and wrap-up (single explicit baseline sorry
│   │                                            for the entire Picard chain)
│   └── PicardFixedPoint.lean                  — Banach-shim + JumpDiffusion.exists_unique
│                                                forwarder (ex-Tier-1-axiom #14, now thm)
└── BSDEJ/
    ├── Definition.lean                        — IsBSDEJSolution predicate + extractors
    ├── Existence.lean                         — Tier 1 #9 axiom (Y-only uniqueness)
    ├── PathRegularity.lean                    — Tier 1 #10 axiom + linear-rate corollary
    └── MartingaleRepresentation.lean          — Tier 1 #13a + #13b sub-axioms; #13 is now
                                                  a derived theorem forwarder
```

## Build instructions

```
cd D:/LevyStochCalc
lake build                            # 8402 jobs
bash tools/lint.sh                    # checks build + sorry baseline
bash tools/verify_import_contract.sh  # checks dissertation-import contract
                                      # (paths from tools/import_contract.md;
                                      #  added 2026-05-27, audit HIGH #6)
```

## See also

* `tools/cited_axioms.md` — full Tier 1 axiom inventory with paper references.
* `tools/sorry_baseline.txt` — currently-sorry'd theorems.
* `_audit.lean` — load-bearing axiom-budget audit.
* `redteam_findings/SUMMARY.md` — meta-summary across 12 audit personas
  (severity-ranked, deduplicated). The 12 raw persona reports and the audit
  scaffolding were collapsed into this single summary on 2026-06-15 (Plan.md
  Phase 0.2 de-clutter); they remain in git history if needed.
