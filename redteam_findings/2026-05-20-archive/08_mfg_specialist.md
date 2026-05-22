# Red Team Audit: MFG / McKean-Vlasov Specialist

**Auditor lens**: Mean-field game theorist (Lasry-Lions, Carmona-Delarue, Cardaliaguet) asking whether the existing LevyStochCalc BSDEJ apparatus could support a downstream McKean-Vlasov / MFG-BSDEJ formalisation, or whether design choices in the current substrate would force a future MFG project to redefine core types.
**Date**: 2026-05-20
**Coverage**: 8 files read in full (`tools/cited_axioms.md`, `BSDEJ/Definition.lean`, `BSDEJ/Existence.lean`, `BSDEJ/MartingaleRepresentation.lean`, `BSDEJ/PathRegularity.lean`, `Brownian/Multidim.lean`, `Ito/Setting.lean`, shared context override), 0 skimmed, the rest (Brownian path-level construction, Poisson construction, Compensated L2, Ito L2) not touched because they sit below the BSDEJ layer and have nothing to say about mean-field structure.

## Executive summary (<= 3 sentences)

LevyStochCalc has no MFG content and is correctly out-of-scope for this lens; my mandate per the override is to write a short honest report on whether the existing apparatus could *extend* to MFG-BSDEJ. The substrate is well-designed for the classical (one-agent) Tang-Li / Bouchard-Elie-Touzi setting and could in principle be reused for McKean-Vlasov extension, but two design choices in `BSDEJData` and `IsBSDEJSolution` (no law-argument in the generator/terminal, no measure-on-paths slot) would force a downstream MFG project to define a parallel `MFG_BSDEJData` rather than reusing `BSDEJData` directly. This is normal and expected for a non-MFG library; it is not a defect.

## Top findings (ranked by severity, highest first)

### Finding 1 - `BSDEJData` generator/terminal signatures hard-code the classical (non-McKean-Vlasov) shape

- **Severity**: LOW (design observation; would force a non-trivial refactor or a parallel definition for any future MFG extension, but the library is not advertised as MFG-ready)
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:78-82`
- **Evidence** (verbatim):
  ```
  structure BSDEJData (n d : ℕ) (E : Type v) where
    /-- Generator `f(t, x, y, z, u)`. -/
    f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ
    /-- Terminal condition `g(x)`. -/
    g : (Fin n → ℝ) → ℝ
  ```
- **Why this matters**: In the McKean-Vlasov / MFG-BSDEJ generalisation (Carmona-Delarue 2018 Vol II, Ch 1; Buckdahn-Li-Peng-Rainer "Mean-field SDEs", AOP 2017; Buckdahn-Djehiche-Li-Peng "Mean-field BSDEs", AAP 2009) the canonical signature is
  - `f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → P₂(ℝⁿ × ℝ) → ℝ` (generator with extra **law argument** for the joint distribution of `(X_t, Y_t)`), and
  - `g : (Fin n → ℝ) → P₂(ℝⁿ) → ℝ` (terminal with law argument).
  A downstream MFG project building on LevyStochCalc cannot reuse `BSDEJData` as-is: it would need to either (a) introduce a new structure `MFG_BSDEJData` with the law argument, or (b) refactor `BSDEJData` to take a `P₂` slot defaulted to a trivial measure for the classical case. Neither is fatal; both are normal for an extension. The current shape matches the literature it cites (Tang-Li 1994, Pardoux-Rascanu 2014, Bouchard-Elie-Touzi 2009), which are pre-mean-field, so no false advertising. Flag this as "future-extension friction" only.
- **Recommendation**: No action required for the current scope. If a follow-on MFG library is contemplated, the cleanest path is a new `MFG_BSDEJData` structure in a new namespace `LevyStochCalc.MFGBSDEJ`, plus a coercion `BSDEJData -> MFG_BSDEJData` injecting the classical case with a constant `P₂` argument. The two-month-ish proof-engineering cost is in the predicate `IsMFG_BSDEJSolution`, not in the algebraic data.

### Finding 2 - `IsBSDEJSolution` has no fixed-point / consistency slot for the law of `(X, Y)`

- **Severity**: LOW (design observation; same character as Finding 1)
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:91-133`
- **Evidence**: The signature
  ```
  def IsBSDEJSolution
      {P : Measure Ω} [IsProbabilityMeasure P]
      {ν : Measure E} [SigmaFinite ν]
      {n d : ℕ}
      (_W : ... MultidimBrownianMotion P d)
      (N : ... PoissonRandomMeasure P ν)
      (bsdej : BSDEJData n d E)
      (X : ℝ → Ω → (Fin n → ℝ))
      (Y : ℝ → Ω → ℝ)
      (Z : ℝ → Ω → (Fin d → ℝ))
      (U : ℝ → Ω → E → ℝ)
      (T : ℝ) : Prop := ...
  ```
  takes `X` as a fixed input. In an MFG-BSDEJ, `X` itself is McKean-Vlasov — its coefficients depend on the law of `(X_t, Y_t)` under `P`, and a "solution" is a pair (process tuple, consistent law). The MFG fixed point is `Law_P(X_t, Y_t) = L_t` where `L_t` is the law used to compute the coefficients.
- **Why this matters**: For a Cardaliaguet-Carmona-Delarue-Lasry-style MFG-BSDEJ extension you need an outer fixed-point structure on top of the inner `IsBSDEJSolution` predicate. The current predicate cannot express that fixed point directly — you would wrap it in an outer
  ```
  IsMFG_BSDEJSolution L X Y Z U T :=
    (∀ t, P.map (fun ω => (X t ω, Y t ω)) = L t) ∧
    IsBSDEJSolution_with_L W N bsdej_L X Y Z U T
  ```
  where `bsdej_L : BSDEJData ...` is `bsdej` partially-applied at the consistent `L`. This is mechanical but adds a layer. The contraction-mapping side (Banach on `P₂`-valued paths) is independent of the inner BSDEJ contraction and lives at a different layer.
- **Recommendation**: No action required. Note in `BSDEJ/Definition.lean` module docstring (if a future audit refactors this file) that the predicate is single-agent only; MFG extension would require an outer wrapper.

### Finding 3 - `JumpDiffusion` (forward SDE) likewise hard-codes coefficients with no law slot

- **Severity**: LOW
- **Location**: `LevyStochCalc/Ito/Setting.lean:41-45`
- **Evidence** (verbatim):
  ```
  structure JumpDiffusionCoeffs (n d : ℕ) (E : Type v) where
    μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)
    σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)
    γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)
  ```
- **Why this matters**: The forward McKean-Vlasov SDE (Carmona-Delarue Vol I, Ch 2; Sznitman 1991) has coefficients `μ(t, x, L_t)`, `σ(t, x, L_t)`, `γ(t, x, L_t, e)` where `L_t = Law(X_t)` (or `Law(X_t, Y_t)` for the controlled / FBSDEJ setting). Same observation as Findings 1-2: any MFG extension needs a `MV_JumpDiffusionCoeffs` with the extra `P₂` slot, then a `MV_JumpDiffusion` solver wrapping `JumpDiffusion.exists_unique` in the consistency fixed-point. Consistent across the library; not a defect.
- **Recommendation**: Same as Finding 1 - parallel `MV_*` structure in a future MFG module.

### Finding 4 - The L²-isometry-on-`M_W` strengthening in `IsBSDEJSolution` would carry over cleanly to the MFG layer

- **Severity**: OUT-OF-SCOPE-as-criticism, recording as a positive observation
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:111-133`
- **Evidence**: The 2026-05-11 strengthening replaced the previous vacuous per-`(t, ω)` existential with an outer `∃ M_W M_N : ℝ → Ω → ℝ` pinned by L²-isometry to `Z` and direct equality to `Compensated.stochasticIntegral` for `U`. This is precisely the form an MFG extension would want — the law-conditioning enters at the `bsdej.f` and `bsdej.g` level (Finding 1), not at the martingale-integral level. The integral primitives `Brownian.Ito.stochasticIntegral` and `Poisson.Compensated.stochasticIntegral` take per-path inputs that an MFG layer can produce from `L_t`-dependent integrands.
- **Why this matters**: A common failure mode in formalising MFG-BSDEJ is to push the law-dependence too deep into the integral apparatus (e.g., making the Itô isometry itself law-dependent). LevyStochCalc avoids this — the L²-isometries are stated against the per-path integrands, exactly the right level. An MFG extension can plug law-dependent integrands into the same isometries.
- **Recommendation**: None.

### Finding 5 - Probability-space-existential typeclass shape would not impede an MFG extension

- **Severity**: OUT-OF-SCOPE-as-criticism, recording as a positive observation
- **Location**: `BrownianMotion.exists`, `PoissonRandomMeasure.exists_of_sigmaFinite`, `MultidimBrownianMotion.exists` (Multidim.lean:209-230) all live in `∃ (Ω : Type u) (_ : MeasurableSpace Ω) ...` form
- **Evidence**: `Multidim.lean:209-211` —
  ```
  theorem MultidimBrownianMotion.exists (d : ℕ) :
      ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
        (_ : IsProbabilityMeasure P), Nonempty (MultidimBrownianMotion P d) := ...
  ```
- **Why this matters**: This is the right shape for downstream extension — the user picks a probability space, then everything else is parametrised. An MFG construction needs a *single* probability space carrying both the idiosyncratic noise `W^i, N^i` for each agent and (in the propagation-of-chaos limit) the common noise. LevyStochCalc's existential form composes cleanly: take a product of `MultidimBrownianMotion.exists`-witnesses indexed by agent, or take the product with a common-noise factor for the conditional MFG variant. No re-formalisation required.
- **Recommendation**: None.

## Per-claim verdicts on the 11 Tier 1 cited axioms + ~10 derivative theorems

Almost everything is out-of-scope for this lens. The MFG layer would be built on top of these axioms, not against them; so my "verdict" is essentially whether the axiom is **MFG-friendly** (its statement composes with a law-conditioned extension) versus **MFG-hostile** (its statement bakes in a single-agent shape that can't be lifted). I have nothing to flag as hostile.

| Axiom / theorem | Verdict | One-line note |
|---|---|---|
| `BrownianMotion.exists` | OUT-OF-SCOPE-FOR-MY-LENS | Probability-space-level; MFG-neutral |
| `PoissonRandomMeasure.exists_of_sigmaFinite` | OUT-OF-SCOPE-FOR-MY-LENS | Same |
| `kolmogorovChentsov_modification` | OUT-OF-SCOPE-FOR-MY-LENS | Path-regularity; MFG-neutral |
| `brownian_martingale_rightCont` | OUT-OF-SCOPE-FOR-MY-LENS | Filtration-level; MFG-neutral |
| `itoIsometry_brownian_unified_existence` | OUT-OF-SCOPE-FOR-MY-LENS | L² Itô; per-path integrand, MFG can plug in law-dependent `Z` |
| `itoIsometry_compensated_unified_existence` | OUT-OF-SCOPE-FOR-MY-LENS | L² Itô-Lévy; same as above for `U` |
| `cauchySeq_simpleIntegralLp_compensated` | OUT-OF-SCOPE-FOR-MY-LENS | L²-Cauchy machinery; MFG-neutral |
| `adaptedSimple_dense_L2_compensated` | OUT-OF-SCOPE-FOR-MY-LENS | Density of simple integrands; MFG-neutral |
| `continuousBSDEJ_exists_unique` | OUT-OF-SCOPE-FOR-MY-LENS | Inner-layer (one-agent) BSDEJ; an MFG layer wraps it, doesn't fight it |
| `bsdej_path_regularity` | OUT-OF-SCOPE-FOR-MY-LENS | Inner-layer too; same comment |
| `itoLevyFormula` | OUT-OF-SCOPE-FOR-MY-LENS | Itô-Lévy chain rule on a single `X`; MFG uses it per-agent or per-representative |
| `MultidimBrownianMotion.exists` | OUT-OF-SCOPE-FOR-MY-LENS | Product-of-1D BM; ready for `i`-indexed extension |
| `brownian_continuous_modification` | OUT-OF-SCOPE-FOR-MY-LENS | Path-regularity derivative; MFG-neutral |
| `brownian_filtration_rightContinuous` | OUT-OF-SCOPE-FOR-MY-LENS | Filtration-level; MFG-neutral |
| `Brownian.Ito.itoIsometry` | OUT-OF-SCOPE-FOR-MY-LENS | L²-conjunct extraction; MFG-neutral |
| `Brownian.Ito.martingale_stochasticIntegral` | OUT-OF-SCOPE-FOR-MY-LENS | Martingale-conjunct extraction; MFG-neutral |
| `Brownian.Ito.quadVar_stochasticIntegral` | OUT-OF-SCOPE-FOR-MY-LENS | Quadratic-variation conjunct; MFG-neutral |
| `Compensated.itoLevyIsometry` | OUT-OF-SCOPE-FOR-MY-LENS | L²-conjunct; MFG-neutral |
| `Compensated.martingale_stochasticIntegral` | OUT-OF-SCOPE-FOR-MY-LENS | Martingale-conjunct; MFG-neutral |
| `Compensated.quadVar_stochasticIntegral` | OUT-OF-SCOPE-FOR-MY-LENS | Quadratic-variation conjunct; MFG-neutral |
| `Compensated.cadlag_modification_exists` | OUT-OF-SCOPE-FOR-MY-LENS | Càdlàg modification; MFG-neutral |
| `Poisson.L2Isometry.itoLevyIsometry` | OUT-OF-SCOPE-FOR-MY-LENS | 1-line forwarder; MFG-neutral |
| `jacodYor_representation` | OUT-OF-SCOPE-FOR-MY-LENS | Two-source predictable representation; MFG extension would need a `Law_t`-conditioned version (Carmona-Delarue Vol II Prop 1.36), but the current statement is correct for the non-MFG layer |
| `picardMap_contraction` | OUT-OF-SCOPE-FOR-MY-LENS | Inner-layer Picard; an MFG outer-Picard would wrap this |
| `JumpDiffusion.exists_unique` | OUT-OF-SCOPE-FOR-MY-LENS | Same as `continuousBSDEJ_exists_unique` — single-agent, MFG wraps it |

## Tools and sources used

- **Lean tools called**: none — read files directly with `Read`. The audit is design-level (could this extend?), not Lean-semantics level (does this prove what it claims?), so LSP queries would not add information.
- **Web searches**: none. The relevant literature is well-known to the persona (Carmona-Delarue, Buckdahn-Li-Peng-Rainer, Sznitman, Cardaliaguet) and the question is whether the LevyStochCalc signatures could host it, not whether the literature exists.
- **Web fetches**: none.
- **Papers consulted (background, persona-resident knowledge)**:
  - Carmona, R. & Delarue, F. *Probabilistic Theory of Mean Field Games with Applications I & II*, Springer 2018. Vol I Ch 2 (McKean-Vlasov SDEs), Vol II Ch 1 (Mean-field BSDEs and master equation).
  - Buckdahn, R., Djehiche, B., Li, J. & Peng, S. *Mean-field backward stochastic differential equations: A limit approach*, Annals of Probability 37(4), 2009.
  - Buckdahn, R., Li, J., Peng, S. & Rainer, C. *Mean-field stochastic differential equations and associated PDEs*, Annals of Probability 45(2), 2017.
  - Sznitman, A.-S. *Topics in propagation of chaos*, Ecole d'Été de Probabilités de Saint-Flour XIX, LNM 1464, 1991.
  - Cardaliaguet, P. *Notes on Mean Field Games*, lecture notes, Paris-Dauphine.
  - Lasry, J.-M. & Lions, P.-L. *Mean field games*, Japanese J. Math. 2, 2007.

## What you couldn't verify

- I did not attempt to "verify" anything in LevyStochCalc against MFG, because the override is explicit that LevyStochCalc has no MFG content. I read the architecture and asked the design-question my lens supports: "if this library wanted MFG extension downstream, would it have to start over?". Answer: no.
- I did not check whether the dissertation side (out-of-scope per override) actually does build MFG on top of LevyStochCalc. The override instructs me to ignore dissertation MFG content; I have done so.
- I did not run `lake build` or `lean_verify`. The findings are at the type-signature / structure-shape level; Lean semantics are not the question my lens is set up to answer.

## Recommendations for the project (<= 5 bullets)

- No critical or high-severity action required. LevyStochCalc is honestly scoped as a one-agent Itô-Lévy + BSDEJ library, and the override confirms MFG is not in scope.
- If a follow-on MFG-BSDEJ formalisation is contemplated (e.g., for the sister dissertation's Cont-Xiong work or a future Mathlib contribution), introduce parallel `MV_BSDEJData`, `MV_JumpDiffusionCoeffs`, `MV_JumpDiffusion`, `IsMV_BSDEJSolution` structures in a new namespace `LevyStochCalc.MV` (or `LevyStochCalc.MeanField`), rather than refactoring the existing classical structures in place. Refactoring in place would force every Tier 1 axiom and derivative theorem to carry a trivial `P₂` argument they don't use — that ugliness is worse than parallel structures.
- The inner BSDEJ Picard contraction `picardMap_contraction` in `BSDEJ/Existence.lean:80-91` will be reusable inside a future MFG outer Picard, but only once it is upgraded from the current `True := trivial` placeholder. The path forward: prove the contraction body, then wrap in an outer fixed-point on `P₂`-valued path-laws.
- Consider documenting in `tools/cited_axioms.md` (or a new `tools/extension_notes.md`) the explicit fact that LevyStochCalc is single-agent only, with a one-paragraph pointer to the design choices a future MFG extension would have to make. This pre-empts any future Mathlib reviewer asking "why doesn't `BSDEJData` have a `P₂` slot?".
- No edits to source.
