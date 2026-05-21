# Red Team Audit: 05 Proof Theorist / Axiom Hygiene

**Auditor lens**: Logician with proof-assistant background; lens is dependency-closure of the axiom set plus the question "is each existential proved with real content, or with a vacuous witness?"
**Date**: 2026-05-20
**Coverage**: 14 source files read in full (the 11 modules listed in `cited_axioms.md` + `LevyStochCalc.lean` + `tools/full_audit.lean` + `tools/full_audit_output.txt`); 4 context docs read in full (`shared_context.md`, `shared_context_override.md`, `personas/05_proof_theorist.md`, `output_template.md`); `Brownian/Martingale.lean` and `Brownian/SimplePredictableRefine.lean` skimmed (>2000 lines each, read the axioms + stochasticIntegral definitions in full). No files in scope skipped.

## Executive summary (≤ 3 sentences)

**Three CRITICAL trivial-witness theorems survived the 2026-05-11 recursive audit:** (i) `JumpDiffusion.exists_unique` discharges its existential with the constant path `X t ω = x₀` against arbitrary coefficients `(μ, σ, γ)` because the `JumpDiffusion` structure carries `is_solution : True`; (ii) `jacodYor_representation` discharges the Jacod-Yor martingale-representation existential with `⟨0, 0, 0, ξ − 𝔼[ξ]⟩` — three zero processes plus the entire variance stuffed into the fourth slot, identical to the demoted-`itoLevyFormula` pattern; (iii) the just-strengthened `IsBSDEJSolution` predicate still lacks any adaptedness or progressive-measurability constraint on `(Y, Z, U)`, so a non-adapted deterministic Y (whenever the driver `f` does not depend on `(y, z, u)`) is a witness, which makes the cited axiom `continuousBSDEJ_exists_unique` mathematically false as written (uniqueness fails between the literature conditional-expectation Y and the deterministic-functional Y). Items (i) and (ii) currently sit in `tools/cited_axioms.md` under "honest derivative theorems", which is wrong — `lean_verify` shows their full axiom set is `{propext, Classical.choice, Quot.sound}` with no Tier 1 dependency, i.e., they are tautologies dressed as theorems.

## Top findings (ranked by severity, highest first)

### Finding 1 — `IsBSDEJSolution` strengthening still admits a non-literature trivial witness when `f` is `(y,z,u)`-independent, breaking the cited-axiom uniqueness claim

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean:91-133` (predicate); `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:113-126` (axiom using it)
- **Evidence** (verbatim from `LevyStochCalc/BSDEJ/Definition.lean:91-133`):

```
def IsBSDEJSolution
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (Y : ℝ → Ω → ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (U : ℝ → Ω → E → ℝ)
    (T : ℝ) : Prop :=
  Measurable (Function.uncurry Y)
    ∧ (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    ∧ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    ∧ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    ∧ (∃ M_W M_N : ℝ → Ω → ℝ, ...
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          Y t ω = bsdej.g (X T ω)
            + ∫ s in Set.Icc t T,
                bsdej.f s (X s ω) (Y s ω) (Z s ω) (U s ω)
            - (M_W T ω - M_W t ω) - (M_N T ω - M_N t ω)))
```

A grep for `Filtration|adapted|naturalFiltration|progMeas|StronglyMeasurable` against this file returns only a docstring mention on line 8 and the inner `Filt` for the M_W/M_N pair on line 125. **The predicate enforces only joint measurability (Function.uncurry Y) plus L²-norm conditions** — there is no `(naturalFiltration W N).IsAdapted Y`, no `ProgressivelyMeasurable Z`, no `Y_t` being `ℱ_t`-measurable.

**Explicit trivial witness for `(f, g)` with `f(s, x, y, z, u) := f̃(s, x)` (driver independent of `(y, z, u)`)**:

* `Y t ω := bsdej.g (X T ω) + ∫_{Icc t T} f̃ s (X s ω) ds` (deterministic functional of `ω` through `X`)
* `Z ≡ 0`, `U ≡ 0`
* `M_W ≡ 0` (which satisfies the isometry conjunct against `Z=0` because RHS is 0)
* `M_N := LevyStochCalc.Poisson.Compensated.stochasticIntegral N (fun ω' s e => 0)`, which the unified-existence axiom forces to be `0` a.s. for every `T' > 0` (because its isometry conjunct fires on the constant-zero integrand, giving `∫⁻ ‖F T'‖² = 0`); the martingale property then propagates `M_N 0 = 0` a.s. as well.
* Common filtration: the constant filtration `Filt s = ⊥`. Constant-zero is a martingale on any filtration.

Then the BSDEJ equation reduces to `Y t ω = bsdej.g(X T ω) + ∫_t^T f̃(s, X_s ω) ds − 0 − 0`, which is exactly the definition of `Y`. All four L² conjuncts hold trivially. The strengthening that the module docstring (`Definition.lean:54-58`) claims excludes constant `Y` does indeed exclude `Y ≡ 0`, but **not** non-adapted `ℱ_T`-measurable functional Y.

The literature (Tang-Li 1994) solution for `f̃`-independent driver is `Y t ω = 𝔼[g(X T) + ∫_t^T f̃ | ℱ_t](ω)` — different from my `Y`. So **two distinct solutions** exist for the strengthened predicate. The axiom `continuousBSDEJ_exists_unique` asserts uniqueness (`Existence.lean:124-126`): "for any `Y'` satisfying the predicate, `Y t ω = Y' t ω` a.s." This is mathematically false as written.

- **Why this matters**: This is exactly the failure mode the 2026-05-11 audit was supposed to fix. The previous fix replaced an inner per-`(t,ω)` existential with an outer existential over `(M_W, M_N)`, which closed off one route to trivial witnesses (the route the docstring discusses). But it left the adaptedness gap on `(Y, Z, U)` untouched, and that gap admits a different family of non-literature witnesses. The cited axiom `continuousBSDEJ_exists_unique` therefore asserts a false uniqueness statement; in classical logic this means anyone using it can derive a `Y = Y'` equality that the literature doesn't support, and ultimately `False` if the difference between the two `Y`s is exploited (e.g., a finite-dimensional projection `𝔼[(Y - Y')_t · 𝟙_A]` is nonzero on some `A` for one solution but zero for the other).
- **Recommendation**: Add explicit adaptedness conjuncts to `IsBSDEJSolution`:
  1. Take `Filt` from the filtration generated by `(W, N)` as a *parameter* of the predicate, or define it inside.
  2. Require `MeasureTheory.Adapted Filt Y` (i.e., `Y t` is `Filt t`-measurable for every `t`).
  3. Require `ProgMeasurable Filt Z` and similarly for `U`.
  4. Move `Filt` out of the inner existential (`Definition.lean:125`) and into the predicate's parameters, then require `M_W, M_N` to be martingales w.r.t. the SAME `Filt` used for adaptedness.

  Without (1)-(4), `continuousBSDEJ_exists_unique` should be DEMOTED in the same way `itoLevyFormula` was on 2026-05-11. The current state (a false-as-written axiom) is strictly worse than a stub or sorry.

---

### Finding 2 — `Ito.Setting.JumpDiffusion.exists_unique` is a trivial-witness `theorem` (constant path satisfies the SDE because the SDE constraint is `True`)

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Ito\Setting.lean:50-72` (structure) and `:85-112` (theorem)
- **Evidence**:

Structure (`Setting.lean:50-72`):
```
structure JumpDiffusion ... where
  X : ℝ → Ω → (Fin n → ℝ)
  measurable_path : Measurable (Function.uncurry X)
  initial_value : ∀ᵐ ω ∂P, X 0 ω = x₀
  sup_L2 : ∀ T : ℝ, 0 < T → ∫⁻ ω, ... < ⊤
  /-- The SDE itself: stubbed, since the integrals along `X` require Phase 3
  development. -/
  is_solution : True
```

Theorem proof (`Setting.lean:85-112`):
```
theorem JumpDiffusion.exists_unique
    ... (coeffs : JumpDiffusionCoeffs n d E) (x₀ : Fin n → ℝ) :
    Nonempty (JumpDiffusion W N coeffs x₀) := by
  -- Existence witness: the constant path X t ω = x₀. Substantive Picard solution
  -- (Applebaum 2009 Thm 6.2.9) replaces this in a future refinement.
  refine ⟨{
    X := fun _ _ => x₀
    measurable_path := measurable_const
    initial_value := Filter.Eventually.of_forall (fun _ => rfl)
    sup_L2 := ?_
    is_solution := trivial
  }⟩
  ...
```

`mcp__lean-lsp__lean_verify` confirms: `'LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique' depends on axioms: [propext, Classical.choice, Quot.sound]` — i.e., **NO Tier 1 cited axiom**. This is mathematically impossible for a real Applebaum-6.2.9 statement (which requires Brownian motion + Poisson random measure + Picard contraction). It is axiom-free because the structure field `is_solution : True` makes the SDE constraint vacuous.

- **Why this matters**: The theorem's docstring claims it states "Existence and uniqueness of the jump-diffusion SDE [...] Reference: Applebaum 2009 Thm 6.2.9", and the file's module docstring says `JumpDiffusion` is "the solution of the SDE `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`". A reader (and a downstream proof) would assume the structure encodes the SDE. It does not. The constant path `X t ω = x₀` is a `JumpDiffusion` for *any* `coeffs` whatsoever — including coefficients for which no actual solution exists. The theorem name says `exists_unique`, but the conclusion is `Nonempty`, with no uniqueness clause. This is precisely the trivial-witness pattern the user has been hunting for weeks.

  In `tools/cited_axioms.md` the line "Honest derivative theorems" lists ten entries but **does not** list `JumpDiffusion.exists_unique`; however, it does appear in `tools/full_audit.lean:69` under the comment `Layer 2: Itô-Lévy formula`. So the project knows it exists but classifies it inconsistently. The audit-output shows it with no Tier 1 dependency, which (by the project's own rule "no trivial-witness theorems remain") should have triggered a demotion.

- **Recommendation**: Either (a) demote `JumpDiffusion.exists_unique` to a cited `axiom` referencing Applebaum 2009 Thm 6.2.9, matching the `itoLevyFormula` precedent, OR (b) remove the `is_solution : True` field from the `JumpDiffusion` structure and add a real SDE-validity field that involves `Brownian.SimplePredictableRefine.stochasticIntegral W (σ ∘ X)` and `Poisson.Compensated.stochasticIntegral N (γ ∘ X)`. Until one of those happens, the file's claim that `JumpDiffusion` "is the solution of the SDE" is false. Also: the name `exists_unique` should be `exists` since no uniqueness is proved; or add uniqueness.

---

### Finding 3 — `BSDEJ.MartingaleRepresentation.jacodYor_representation` is a `theorem` with the exact `⟨0, 0, 0, ξ − 𝔼[ξ]⟩` trivial-witness pattern that got `itoLevyFormula` demoted

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\MartingaleRepresentation.lean:55-85`
- **Evidence** (proof body, lines 73-84):

```
    ∃ (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
      (BM_integral jump_integral : Ω → ℝ),
      Measurable (Function.uncurry Z) ∧
      Measurable (fun (p : ℝ × Ω × E) => U p.1 p.2.1 p.2.2) ∧
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) ∧
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) ∧
      (∀ᵐ ω ∂P, ξ ω = (∫ ω', ξ ω' ∂P) + BM_integral ω + jump_integral ω) := by
  -- Existence: take Z = 0, U = 0, BM_integral = 0, jump_integral = ξ - 𝔼[ξ].
  -- The substantive (Jacod 1976) decomposition (with Z, U from orthogonal
  -- projection) replaces these in a future refinement.
  refine ⟨0, 0, 0, fun ω => ξ ω - ∫ ω', ξ ω' ∂P, ?_, ?_, ?_, ?_, ?_⟩
```

This is **structurally identical** to the proof body of the pre-demotion `itoLevyFormula`: three zero processes (Z, U, BM_integral) plus the entire informative content (here `ξ − 𝔼[ξ]`) stuffed into the fourth witness (`jump_integral`). The existential is satisfied with no Jacod-Yor content whatsoever — anyone could write the proof without ever having heard of martingale representation.

`mcp__lean-lsp__lean_verify` confirms: `'LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation' depends on axioms: [propext, Classical.choice, Quot.sound]` — **no Tier 1 cited axiom**.

- **Why this matters**: The theorem's name and docstring (lines 45-54) claim Jacod 1976 / Jacod-Yor martingale representation, a non-trivial result. The conclusion as stated (existence of `(Z, U)` with finite L²-norm such that `ξ ω = 𝔼[ξ] + BM_integral ω + jump_integral ω`) is **vacuously true for any** `L²` random variable, because the existential doesn't constrain `BM_integral` to actually be `∫ Z dW` or `jump_integral` to be `∫∫ U Ñ` — they are unanchored `Ω → ℝ` functions, so the witness `BM_integral := 0`, `jump_integral := ξ − 𝔼[ξ]` trivially satisfies `ξ = 𝔼[ξ] + 0 + (ξ − 𝔼[ξ])` by `ring`.

  This is the textbook anti-pattern the 2026-05-11 audit caught for `itoLevyFormula`. It survived the recursive audit because the audit only checked the 4 dissertation-forwarder targets (`itoLevyIsometry`, `continuousBSDEJ_exists_unique`, `itoLevyFormula`, `bsdej_path_regularity`); `jacodYor_representation` was not on the checklist. The proof body comment (`-- Existence: take Z = 0, U = 0, BM_integral = 0, jump_integral = ξ - 𝔼[ξ]`) acknowledges the triviality, so the author was aware.

  The theorem is referenced by name in `BSDEJ/Existence.lean:108-109` ("Uses the martingale representation theorem (`jacodYor_representation`) for the Z, U extraction") in the docstring of `continuousBSDEJ_exists_unique` — i.e., the cited axiom's *standard proof outline* claims it uses this representation, which (in its current form) carries no content.

- **Recommendation**: Demote `jacodYor_representation` to a cited `axiom` with `Reference: Jacod 1976`. Alternatively, tighten the conclusion so `BM_integral` is literally `Brownian.SimplePredictableRefine.stochasticIntegral W Z T` and `jump_integral` is `Poisson.Compensated.stochasticIntegral N U T` — at which point the existential would no longer be satisfiable by `Z = U = 0` unless `ξ = 𝔼[ξ]` a.s.

---

### Finding 4 — `tools/cited_axioms.md` honest-derivative-theorems table is incomplete and misclassifies `JumpDiffusion.exists_unique` + `jacodYor_representation`

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\tools\cited_axioms.md:97-111` (the "Honest derivative theorems" table)
- **Evidence**: The table lists 11 derived theorems. `JumpDiffusion.exists_unique` and `jacodYor_representation` are NOT in this table, yet they both appear in `tools/full_audit.lean:69` and `:72` — the canonical `#print axioms` checklist. The audit's status snapshot (`cited_axioms.md:134-139`) claims "**10 honest derivative theorems**, axiom-clean modulo Lean std + Tier 1 cited" and "No trivial-witness theorems remain." Both claims fail:
  * `JumpDiffusion.exists_unique` and `jacodYor_representation` are theorems with vacuous proofs and no Tier 1 axiom.
  * `BSDEJ.Existence.picardMap_contraction` (`Existence.lean:80-91`) is a public `lemma` with conclusion `True := trivial` — listed nowhere in the inventory.

- **Why this matters**: The inventory file is the orchestrator's source of truth for what the library is hiding behind axioms vs what it has actually proved. If the inventory misses two trivial-witness theorems and one True-valued public lemma, then a downstream consumer (e.g., a Mathlib reviewer or a dissertation examiner) cannot trust the "axiom-clean modulo Tier 1" claim. The line "No trivial-witness theorems remain" in `cited_axioms.md:139` is *plainly false* given my Findings 2 and 3.
- **Recommendation**: After demoting `JumpDiffusion.exists_unique` and `jacodYor_representation` (per Findings 2, 3), update `cited_axioms.md` to (i) add their demoted axiom entries, (ii) revise the "10 honest derivative theorems" count, and (iii) retract the "No trivial-witness theorems remain" claim until Finding 1 is also addressed.

---

### Finding 5 — `Brownian/Construction.lean:142` and 6 other public `True`-valued lemmas are decorative placeholders with misleading docstrings

- **Severity**: MEDIUM
- **Location**: Multiple — full list from grep:
  * `Brownian/Construction.lean:142-146` (`brownian_dyadicTime_exists` — concludes `∃ Ω' ..., True`, witnessed by `PUnit + dirac`)
  * `Brownian/Construction.lean:156` (`brownian_extend_to_real : True := trivial`)
  * `Brownian/Continuity.lean:37-43` (`kolmogorov_dyadic_holder : ... → True := trivial`)
  * `Poisson/RandomMeasure.lean:146-148` (`poissonRandomMeasure_combine : ... → True := trivial`)
  * `Brownian/Ito.lean:1626-1629, 1638-1640, 1693-1697` (three `True`-valued private lemmas with substantive-looking statements about dyadic approximation)
  * `Poisson/Compensated.lean:1852-1855, 1859-1862` (two more `True`-valued private lemmas)
  * `BSDEJ/Existence.lean:80-91` (`picardMap_contraction : True := trivial` — **public**)
- **Evidence**: `picardMap_contraction` (Existence.lean:80-91):
```
lemma picardMap_contraction
    ... {L : ℝ} (_hL : Lipschitz bsdej ν L) :
    -- placeholder for the contraction inequality
    True := trivial
```
The docstring says "Picard contraction lemma. Under Lipschitz hypothesis with constant `L`, the Picard map `Φ` is a contraction on `S² × H² × H²_N` for sufficiently small `T`..." but the conclusion is `True`. A reader auto-completing on this name will be told it's the technical core of BSDEJ existence; the actual content is `trivial`.

- **Why this matters**: Each of these `True := trivial` lemmas has a docstring that describes a substantive mathematical fact (Kolmogorov-Hölder, Picard contraction, σ-finite Poisson combination, dyadic averaging). The names imply content; the proofs deliver `True`. A naive consumer (or an LLM) writing downstream code might believe the named lemmas are usable, when in fact they are scaffolding for proofs not yet written. This is documentation drift, not a soundness issue (none of these are used to prove any cited axiom or headline derivative). The `private` ones are less concerning than the public ones (`brownian_dyadicTime_exists`, `brownian_extend_to_real`, `kolmogorov_dyadic_holder`, `poissonRandomMeasure_combine`, `picardMap_contraction`).
- **Recommendation**: Either (a) prefix all `True := trivial` lemmas with `private` and add a `-- TODO: spec for ...` comment, OR (b) delete them (their statements convey no information). Keeping them under their current docstrings invites a reader to think the project has formalized e.g. the Picard contraction lemma; it has not.

---

### Finding 6 — `Compensated.itoIsometry_compensated_unified_existence` axiom takes no hypotheses on `φ`, making the joint conjunction trivially satisfied by `F ≡ 0` whenever `φ` is non-measurable / non-L²

- **Severity**: MEDIUM (degenerate case only, not unsound — but a hygiene issue)
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean:2748-2767`
- **Evidence** (verbatim, no hypotheses on `φ`):
```
axiom itoIsometry_compensated_unified_existence
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (φ : Ω → ℝ → E → ℝ) :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2
          - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν) Filt P ∧
      (∀ T, 0 < T → Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2) →
        ∫⁻ ω, ... < ⊤ →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ...) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ, ... càdlàg ...)
```

For non-measurable or non-`L²` `φ`, conjunct 3 (isometry) is vacuously satisfied (hypothesis fails). Conjunct 2: `∫ ... ∂ν` is 0 by Bochner convention when the integrand is non-integrable, so the inner `∫_0^t ∫_E (φ ω s e)² ∂ν ds = 0`, making conjunct 2 reduce to `(F t ω)²` being a martingale. Witness `F ≡ 0, Filt = constant ⊥`: all four conjuncts hold trivially.

Compare to the analogous Brownian-side axiom (`SimplePredictableRefine.lean:2094-2115`), which takes `h_meas`, `h_progMeas`, `h_sq_int_global` as PARAMETERS — so the conclusion is only asserted for well-behaved `H`.

- **Why this matters**: The asymmetry between Brownian and Compensated unified-existence axioms is concerning. The Compensated version asserts the conclusion *unconditionally on `φ`*, which makes the axiom's literature support weaker than claimed (Applebaum 2009 Thm 4.2.3 assumes predictable square-integrable `φ`). Downstream usage in `Compensated.stochasticIntegral N φ T` does NOT pre-check `φ` for measurability or integrability — the `Classical.choose` simply picks some `F`. For wild `φ`, the choice could be `F ≡ 0`, which means `stochasticIntegral N φ` silently equals zero, with no diagnostic. This is the "Classical.choose applied to an existential that is itself vacuous" anti-pattern from the persona brief.

  This is not a CRITICAL because downstream callers always do supply `Measurable + L²` `φ`, so in practice `F` is the "real" L²-Itô-Lévy integral. But the axiom *as stated* is weaker than Applebaum's theorem, and that asymmetry is undocumented.

- **Recommendation**: Add hypotheses `h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2)` and `h_progMeas` and `h_sq_int_global : ∀ T, 0 < T → ∫⁻ ... < ⊤` to `itoIsometry_compensated_unified_existence`, matching the Brownian version. Downstream `stochasticIntegral` will then need these hypotheses too (as the Brownian one already does). This restores the Applebaum-faithful axiom statement and removes the degenerate trivial-witness branch.

---

### Finding 7 — `Brownian.SimplePredictableRefine.stochasticIntegral`'s `Classical.choose` only constrains the chosen `F` at integer/positive-`T` time steps via isometry; the inner `Filt` is a free parameter

- **Severity**: MEDIUM (not unsound, just under-specified)
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\SimplePredictableRefine.lean:2123-2139`
- **Evidence**:
```
noncomputable def stochasticIntegral
    {P : MeasureTheory.Measure Ω} [...]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas ... h_progMeas ... h_sq_int_global ...)
    (T : ℝ) : Ω → ℝ :=
  Classical.choose
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas h_sq_int_global) T
```
Two distinct invocations with the *same* `(W, H, hypotheses)` will share the same `F` (because `Classical.choose` is deterministic per term-level encoding), but the choice across distinct `H` is independent. The resulting `F` could in principle satisfy the 3 conjuncts in multiple ways — e.g., for `H ≡ 0` we get `F ≡ 0` a.s. by isometry, but the chosen `Filt` is unspecified beyond "some filtration making `F` and `F²` martingales". This means downstream theorems that need `Filt` to be the natural filtration of `W` cannot rely on this — they must reach back into the original existence axiom to extract `Filt`, which is what `martingale_stochasticIntegral` does (extracting via `Classical.choose_spec.choose`).

- **Why this matters**: The Brownian (and compensated-Poisson) `stochasticIntegral` is a `Classical.choose`-based functional. The user explicitly flagged this pattern in the audit brief: "The Classical.choose-based definitions of stochasticIntegral (both Brownian and Compensated). The cited 'unified existence' axioms have 3-4 conjuncts; verify the joint constraint really excludes constants-in-(t,ω)." For the Brownian case, the answer is **yes**: when `H` is L²-non-trivial and progressively measurable, conjunct 3 (isometry) forces `‖F T‖₂² = ‖H‖₂²[0,T]` for every `T > 0`, which excludes `F ≡ 0` unless `H ≡ 0` a.e. So the joint conjunction does exclude constants. Same conclusion for Compensated with hypothesised `φ`. The trivial-witness risk in this primitive is therefore LOW.
- **Recommendation**: No code change. Document in the file header that `stochasticIntegral` is canonical (uniquely determined a.s. by the isometry conjunct under the supplied hypotheses), but only "canonical modulo a.s. equality" — there may be multiple `F` satisfying the axiom; `Classical.choose` picks one, and downstream theorems must thread `Classical.choose_spec` to get any property beyond the isometry.

---

### Finding 8 — `BSDEJ/Existence.lean:113` axiom `continuousBSDEJ_exists_unique` requires its `_W` parameter via `W` (not `_W`), while predicate definition only used `_W`; small naming inconsistency between axiom and predicate around the W parameter

- **Severity**: LOW
- **Location**: `Definition.lean:95` (`_W` underscored), `Existence.lean:117` (`W` not underscored)
- **Evidence**:
```
-- Definition.lean line 95
def IsBSDEJSolution
    ...
    (_W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    ...

-- Existence.lean line 117
axiom continuousBSDEJ_exists_unique
    ...
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    ...
```
The fact that `_W` is underscored in `IsBSDEJSolution` indicates it's never used in the predicate — and indeed it isn't (no W appears in the body). This means the strengthened predicate **completely ignores `W`** — the Brownian motion plays no role in the L²-isometry constraint on `M_W`. The isometry only ties `M_W` to `Z` via the integral identity, not to the actual Brownian increments. The docstring on `Definition.lean:42-47` acknowledges this: "We don't pin `M_W` to a specific functional of `Z` because the multidim Brownian stochastic integral primitive would need `h_progMeas` threaded through; the isometry constraint together with the martingale requirement is enough to exclude the trivial witnesses."

That parenthetical claim is what Finding 1 contests: "the isometry constraint together with the martingale requirement" is NOT enough to exclude non-adapted Y.

- **Why this matters**: A predicate that ignores its `W` parameter cannot meaningfully reference "Brownian motion" in its semantics. This is the structural reason behind Finding 1. The argument is decorative (carried for type-checking the relationship with the cited axiom), not load-bearing. The `_W` underscore makes this explicit at the predicate level.
- **Recommendation**: When fixing Finding 1, drop the underscore on `_W` and actually use `W` (e.g., to define the natural filtration `(W, N)`-generated, then require `Y, Z, U` adapted to it, and `M_W` to be the multidim Brownian stochastic integral of `Z` against `W`). This is essentially the literature definition.

---

## Per-claim verdicts on the headlines (the 11 Tier 1 axioms + the honest derivative theorems)

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `LevyStochCalc.Brownian.BrownianMotion.exists` | EARNED | Real cited axiom (Karatzas-Shreve), correctly transparent. |
| `LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | EARNED | Real cited axiom (Applebaum / Kallenberg), correctly transparent. |
| `LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification` | EARNED | Real cited axiom (Karatzas-Shreve / Le Gall), correctly transparent. |
| `LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont` | EARNED | Real cited axiom (Karatzas-Shreve Blumenthal corollary), correctly transparent. |
| `LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence` | EARNED | Real cited axiom with proper hypotheses; 3-conjunct conjunction rigid. |
| `LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence` | WEAK | Missing `h_meas` and `h_sq_int_global` parameters (Finding 6); axiom weaker than Applebaum 4.2.3 as stated. |
| `LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` | EARNED | Cited (Applebaum Lemma 4.2.5), substantive content. |
| `LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated` | EARNED | Cited (Applebaum Lemma 4.2.2), substantive content. |
| `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique` | **TRIVIAL** | Uniqueness clause is mathematically false as written, because `IsBSDEJSolution` lacks adaptedness — see Finding 1. |
| `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity` | WEAK | Statement is coherent but inherits the `IsBSDEJSolution` weakness from Finding 1; bound `C·Δt` is over a class of "solutions" that includes non-literature witnesses. |
| `LevyStochCalc.Ito.JumpFormula.itoLevyFormula` | EARNED | Honestly demoted to axiom on 2026-05-11; citation correct. |
| `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists` | EARNED | Genuine derivation from `BrownianMotion.exists` via `Measure.pi`. |
| `LevyStochCalc.Brownian.Continuity.brownian_continuous_modification` | EARNED | Genuine derivation from `kolmogorovChentsov_modification`. |
| `LevyStochCalc.Brownian.Martingale.brownian_martingale` | EARNED | Real proof (substantive `condExp` decomposition). |
| `LevyStochCalc.Brownian.Martingale.brownian_quadVar` | EARNED | Real proof. |
| `LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous` | EARNED | Forwarder over `brownian_martingale_rightCont`. |
| `LevyStochCalc.Brownian.Ito.itoIsometry` | EARNED | Extracts conjunct 3 from unified-existence; constraints rigid. |
| `LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral` | EARNED | Extracts conjunct 1. |
| `LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral` | EARNED | Extracts conjunct 2. |
| `LevyStochCalc.Poisson.Compensated.itoLevyIsometry` | EARNED | Extracts conjunct 3; conditional on hypotheses. |
| `LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral` | EARNED | Extracts conjunct 1. |
| `LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral` | EARNED | Extracts conjunct 2. |
| `LevyStochCalc.Poisson.Compensated.cadlag_modification_exists` | EARNED | Extracts conjunct 4. |
| `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry` | EARNED | 1-line forwarder over `Compensated.itoLevyIsometry`. |
| `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` | **TRIVIAL** | Constant-path witness against the `is_solution : True` field — Finding 2. |
| `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` | **TRIVIAL** | `⟨0, 0, 0, ξ − 𝔼[ξ]⟩` proof — Finding 3, identical to the demoted-`itoLevyFormula` pattern. |

## Tools and sources used

- **Lean tools called**:
  * `mcp__lean-lsp__lean_verify` on 7 theorems (`continuousBSDEJ_exists_unique`, `bsdej_path_regularity`, `Poisson.L2Isometry.itoLevyIsometry`, `itoLevyFormula`, `Brownian.Multidim.MultidimBrownianMotion.exists`, `JumpDiffusion.exists_unique`, `jacodYor_representation`) to confirm axiom-set drift vs `tools/full_audit_output.txt`. No drift observed.
  * `bash tools/lint.sh` confirmed build passes (8401 jobs, PASS).
- **`Grep` searches**: `axiom\s+\w+` over `LevyStochCalc/` (returned the 11 axioms exactly); `refine ⟨0|refine ⟨default|:= 0|:= fun _ =>|True\.intro|trivial` over `LevyStochCalc/` (returned the trivial-witness hits + many `True := trivial` placeholders); `JumpDiffusion.exists_unique|jacodYor_representation` over `D:\Dissertation` (confirmed forwarders exist but are flagged with `std only (axiom-clean)` in `LevyStochCalcBridge.lean:39, 41`, exactly the trivial-axiom-set pattern); `Filtration|adapted|naturalFiltration|progMeas|StronglyMeasurable` over `BSDEJ/Definition.lean` (confirmed predicate has no adaptedness clause beyond inner filtration for `M_W, M_N`).
- **Web searches / fetches**: None for this audit — the trivial-witness analysis is purely formal and the literature claims are already documented in `cited_axioms.md`.
- **Papers consulted**: Tang & Li (1994) SICON 32(5), via the citation chain in `cited_axioms.md` Tier 1 #9; Applebaum 2009 (Thm 4.2.3, 4.2.4, 4.4.7, 6.2.9), via the citation chain in `cited_axioms.md` Tier 1 #2, #6, #11; Jacod (1976), via `MartingaleRepresentation.lean:21`.

## What you couldn't verify

- I did not run `lean_verify` on the public lemma `picardMap_contraction` because it concludes `True` and the axiom check is trivial (no Tier 1 axioms can possibly be needed for `trivial`).
- I did not exhibit the trivial-witness Y from Finding 1 as an executable Lean term (would require ~30 lines of Mathlib boilerplate to wire up `Compensated.stochasticIntegral N 0`'s a.s.-zero property). The argument is straightforward but the formal exhibit would take a separate session.
- I did not check whether the dissertation-side `Continuous.lean` forwarders silently weaken the LevyStochCalc-side statements (e.g., whether the dissertation re-states `continuousBSDEJ_exists_unique` with the existence half only). That is a different persona's lens, and the override scoped my audit to the LevyStochCalc side.

## Recommendations for the project (≤ 5 bullets)

- **(Highest priority)** Fix Finding 1 immediately: add adaptedness / progressive-measurability clauses to `IsBSDEJSolution` and tie `M_W` to the actual multidim Brownian stochastic integral of `Z` against `W`. Without this fix, `continuousBSDEJ_exists_unique` asserts a false uniqueness statement. The cited axiom as written is strictly worse than a `sorry`.
- **Demote `JumpDiffusion.exists_unique`** to a Tier 1 cited axiom referencing Applebaum 2009 Thm 6.2.9, OR remove the `is_solution : True` field and add real SDE-validity content. The current state is the exact trivial-witness pattern that got `itoLevyFormula` demoted on 2026-05-11; it is inconsistent that this one survived.
- **Demote `jacodYor_representation`** to a Tier 1 cited axiom referencing Jacod 1976, OR tighten its conclusion so `BM_integral := ∫_0^T Z · dW` literally (and similarly for `jump_integral`). The current `⟨0, 0, 0, ξ−𝔼[ξ]⟩` proof is no better than the pre-demotion `itoLevyFormula`.
- **Update `tools/cited_axioms.md`**: the line "No trivial-witness theorems remain" (`:139`) is false. After demoting the two theorems above, update the "honest derivative theorems" table to 9 entries (or 11 if the two new axioms are added as Tier 1 #12, #13), and rewrite the audit-snapshot section.
- **Add `h_meas`/`h_sq_int_global` hypotheses** to `itoIsometry_compensated_unified_existence` (Finding 6), matching the Brownian-side symmetry. Currently the Compensated axiom is silently weaker than Applebaum 4.2.3 because it omits the predictability/L² hypotheses on `φ`.
