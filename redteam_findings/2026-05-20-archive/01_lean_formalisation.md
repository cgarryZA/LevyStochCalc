# Red Team Audit: Lean 4 / Mathlib formalisation expert

**Auditor lens**: Senior Mathlib contributor judging idiom, naming, build hygiene, imports, type-class hygiene, measure-theoretic primitive choice, axiom-cleanliness mechanics, and Mathlib alignment.
**Date**: 2026-05-20
**Coverage**: 21 files read in full (`LevyStochCalc.lean`, `lakefile.toml`, `lean-toolchain`, `_audit.lean`, `tools/full_audit.lean`, `tools/full_audit_output.txt`, `tools/cited_axioms.md`, `tools/lint.sh`, `tools/sorry_baseline.txt`, `LevyStochCalc/Basic.lean`, `Notation.lean`, `Brownian/{Construction,Continuity,Martingale,Multidim}.lean`, `Brownian/SimplePredictableRefine.lean` (excerpts of the 2.2k-line file), `Brownian/Ito.lean` (excerpts of the 4k-line file), `Poisson/{RandomMeasure,Compensated,L2Isometry,Martingale}.lean` (Compensated.lean read in selective excerpts of the 2.9k-line file), `Ito/{Setting,JumpFormula}.lean`, `BSDEJ/{Definition,Existence,MartingaleRepresentation,PathRegularity}.lean`); 4 files skimmed via `Grep`/file-outline (`Poisson/NaturalFiltration.lean`, `STATUS.md`, `STATUS_strong_exists.md`, the two long files); 0 files not touched (the entire `LevyStochCalc/**` tree was inspected).

## Executive summary (≤ 3 sentences)

The library builds (8401 jobs PASS) and the audit-tracked theorems are `sorryAx`-free, but the underlying chain hides four real defects: (1) `Notation.lean` is a 13-line file whose only content is `import Mathlib`, a banned Mathlib-wide pattern; (2) `BSDEJ.MartingaleRepresentation.jacodYor_representation` is a literal trivial-witness theorem of exactly the form the 2026-05-11 recursive audit was created to eliminate (`refine ⟨0, 0, 0, fun ω => ξ ω - ∫ ω', ξ ω' ∂P, …⟩`), missed by the audit because the four-zero-plus-residual pattern is now syntactically `0, 0, 0, ξ − 𝔼[ξ]`; (3) the just-demoted `Ito.JumpFormula.itoLevyFormula` axiom (item #11) is **as an `axiom` still vacuous** — its conclusion is `∃ four reals : Ω → ℝ summing to u(T,X_T)−u(0,X_0)`, with NO internal constraint pinning the four terms to the literature integrals; (4) the BSDEJ existence/uniqueness and path-regularity Tier 1 axioms (#9, #10) omit the Lipschitz hypotheses that Tang–Li 1994 and Bouchard–Elie–Touzi 2009 require, making the axiom statements stronger-than-literature (and hence mathematically false). On top of these soundness/code-hygiene issues there are 198 `lake build` warnings — 4 `declaration uses 'sorry'`, 8 deprecated Mathlib symbols still in use, 59 misuses of the `show` tactic, 29 deprecated `push_neg` invocations, 19 undocumented `set_option maxHeartbeats` lines, 18 module headers that the style linter complains about, plus 21 over-long lines.

## Top findings (ranked by severity, highest first)

### Finding 1 — `BSDEJ.MartingaleRepresentation.jacodYor_representation` is a trivial-witness theorem

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:55-84`
- **Evidence** (verbatim from source):
  ```
  theorem jacodYor_representation
      …
      (ξ : Ω → ℝ)
      … :
      ∃ (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
        (BM_integral jump_integral : Ω → ℝ),
        Measurable (Function.uncurry Z) ∧
        Measurable (fun (p : ℝ × Ω × E) => U p.1 p.2.1 p.2.2) ∧
        … L²-integrability conjuncts …
        (∀ᵐ ω ∂P, ξ ω = (∫ ω', ξ ω' ∂P) + BM_integral ω + jump_integral ω) := by
    -- Existence: take Z = 0, U = 0, BM_integral = 0, jump_integral = ξ - 𝔼[ξ].
    -- The substantive (Jacod 1976) decomposition (with Z, U from orthogonal
    -- projection) replaces these in a future refinement.
    refine ⟨0, 0, 0, fun ω => ξ ω - ∫ ω', ξ ω' ∂P, ?_, ?_, ?_, ?_, ?_⟩
    · exact measurable_const
    · exact measurable_const
    · simp
    · simp
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      show ξ ω = (∫ ω', ξ ω' ∂P) + 0 + (ξ ω - ∫ ω', ξ ω' ∂P)
      ring
  ```
- **Why this matters**: This is *exactly* the trivial-witness pattern (`⟨0, 0, 0, change⟩`) that the 2026-05-11 recursive audit demoted `itoLevyFormula` over. The `tools/full_audit_output.txt` reports `jacodYor_representation depends on axioms: [propext, Classical.choice, Quot.sound]` — i.e. no Tier 1 axiom, no `sorryAx` — but the proof body is the literal "three zeros + entire residual stuffed in the fourth slot" pattern. The theorem is named after Jacod–Yor (1976) and is supposed to provide the predictable representation `M_t = M_0 + ∫_0^t Z_s dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)`. Taking `Z = U = 0, BM_integral = 0, jump_integral = ξ − 𝔼[ξ]` makes the existential trivially provable for *any* L²-integrable `ξ`, without any martingale machinery whatsoever. The recursive audit caught `itoLevyFormula` but the same author wrote the same pattern again here.
- **Recommendation**: Demote to a Tier 1 `axiom` (mirroring the `itoLevyFormula` action) with the Jacod 1976 citation, **and** strengthen the statement: the `BM_integral` and `jump_integral` slots must be pinned (e.g. `BM_integral ω = Brownian.Ito.stochasticIntegral` for some `Z`, `jump_integral ω = Compensated.stochasticIntegral N U T ω` etc.) so that the trivial witness no longer works. Add to `tools/cited_axioms.md` as a 12th cited axiom. The current pattern is precisely what the user instructed the audit chain to hunt for.

### Finding 2 — `Ito.JumpFormula.itoLevyFormula` axiom is still vacuous after demotion

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/Ito/JumpFormula.lean:90-105`
- **Evidence** (verbatim from source):
  ```
  axiom itoLevyFormula
      …
      (u : ℝ → (Fin n → ℝ) → ℝ)
      (T : ℝ) (_hT : 0 < T) :
      -- Exists four processes giving the integral-form decomposition.
      ∃ (drift_term diff_mart jump_mart comp_drift : Ω → ℝ),
        (∀ᵐ ω ∂P,
          u T (X.X T ω) - u 0 (X.X 0 ω) =
            drift_term ω + diff_mart ω + jump_mart ω + comp_drift ω)
  ```
- **Why this matters**: The 2026-05-11 audit demoted this from `theorem` to `axiom` because the *proof* was `refine ⟨0, 0, 0, fun ω => u T (X T ω) - u 0 (X 0 ω), ?_⟩; simp`. But **the conclusion's text wasn't changed** — it still says: "there exist four processes summing to `u(T,X_T) − u(0,X_0)`." That statement is *provable in Lean's standard logic* by the same `⟨0, 0, 0, change⟩` trick. So the axiom asserts a *triviality*, not Applebaum 2009 Thm 4.4.7. The docstring acknowledges the issue ("Previous status: a `theorem` whose proof body was the trivial-witness pattern") but axiomatising a triviality and citing a real theorem after it is a documentation/code mismatch: a Mathlib reviewer reading the docstring expects the Lean statement to *capture* Applebaum 4.4.7; the Lean statement does not. This is worse than the previous form: the previous form at least surfaced as a *theorem* whose `Classical.choose` witness is one specific functional. Now `Classical.choose (itoLevyFormula …)` can pick any quadruple of functions summing to the change, with no constraint that `drift_term ω = ∫_0^T (∂_t u + 𝓛u)(s, X_{s-} ω) ds`, etc. The axiom adds zero mathematical content.
- **Recommendation**: Rewrite the axiom's conclusion so each of the four terms is pinned to its literature integral form:
  ```
  ∃ … drift_term diff_mart jump_mart comp_drift : Ω → ℝ,
    drift_term =ᵐ[P] (fun ω => ∫ s in Icc 0 T, (𝓛 u + ∂_t u)(s, X.X s ω)) ∧
    diff_mart =ᵐ[P] (Brownian.Multidim.stochasticIntegral W (fun ω' s i => …)) T ∧
    jump_mart =ᵐ[P] (Compensated.stochasticIntegral N (fun ω' s e => …)) T ∧
    comp_drift =ᵐ[P] (fun ω => ∫ s in Icc 0 T, ∫ e, [u(·+γ) − u − γᵀ ∇u] …) ∧
    (∀ᵐ ω ∂P, u T (X.X T ω) - u 0 (X.X 0 ω)
                = drift_term ω + diff_mart ω + jump_mart ω + comp_drift ω)
  ```
  Until each term is pinned, the axiom is not "Applebaum 4.4.7" — it's a tautology with a misleading citation.

### Finding 3 — `Ito.Setting.JumpDiffusion.exists_unique` is named "exists_unique" but proves only `Nonempty`, with a constant-path witness on a `True`-valued `is_solution` field

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/Ito/Setting.lean:50-112`
- **Evidence** (verbatim from source):
  ```
  structure JumpDiffusion
      … where
    X : ℝ → Ω → (Fin n → ℝ)
    measurable_path : Measurable (Function.uncurry X)
    initial_value : ∀ᵐ ω ∂P, X 0 ω = x₀
    sup_L2 : ∀ T : ℝ, 0 < T → ∫⁻ ω, … < ⊤
    /-- The SDE itself: stubbed, since the integrals along `X` require Phase 3
    development. -/
    is_solution : True

  theorem JumpDiffusion.exists_unique
      … :
      Nonempty (JumpDiffusion W N coeffs x₀) := by
    -- Existence witness: the constant path X t ω = x₀. Substantive Picard solution
    -- (Applebaum 2009 Thm 6.2.9) replaces this in a future refinement.
    refine ⟨{
      X := fun _ _ => x₀
      …
      is_solution := trivial
    }⟩
  ```
- **Why this matters**: Three problems compounded:
  1. The structure's `is_solution : True` field makes "X solves the SDE" be the proposition `True`, satisfied by *any* X. The constant path `X t ω = x₀` satisfies it trivially.
  2. The theorem is named `exists_unique` but proves *only* `Nonempty` — there is **no uniqueness statement at all**. The cited Applebaum 2009 Thm 6.2.9 is an existence-and-uniqueness theorem; this is half of that.
  3. The `tools/full_audit_output.txt` reports it as Lean-std-axiom-only — i.e. it appears clean. But it's clean because it's *vacuous*: a `Nonempty`-statement on a structure with a `True` field is trivially `Nonempty (PUnit)` modulo the L²-sup field, which the constant witness also satisfies.
  
  This is the same anti-pattern as Finding 2: a "honest derivative theorem" listed in `tools/full_audit.lean` line 69, claiming to carry Applebaum 6.2.9 content, when in fact it carries no content.
- **Recommendation**: Either (a) demote to a `Tier 1` axiom with a real SDE-validity predicate replacing `is_solution : True`, or (b) strengthen `is_solution` to assert the actual SDE identity (`X_t = x₀ + ∫_0^t μ(s,X_s) ds + ∫_0^t σ(s,X_s) dW_s + ∫_0^t ∫_E γ(s, X_{s-}, e) Ñ(ds, de)` a.s.) so the constant witness no longer satisfies it. Also add the uniqueness conjunct (`∀ X' : JumpDiffusion W N coeffs x₀, ∀ t, ∀ᵐ ω, X.X t ω = X'.X t ω`). Until then, the theorem name is misleading.

### Finding 4 — Tier 1 cited axioms #9 and #10 omit the Lipschitz hypothesis required by Tang–Li 1994 and Bouchard–Elie–Touzi 2009

- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/Existence.lean:113-126` (`continuousBSDEJ_exists_unique`); `LevyStochCalc/BSDEJ/PathRegularity.lean:111-139` (`bsdej_path_regularity`)
- **Evidence** (verbatim from source, `BSDEJ/Existence.lean:113-121`):
  ```
  axiom continuousBSDEJ_exists_unique
      {P : Measure Ω} [IsProbabilityMeasure P]
      {ν : Measure E} [SigmaFinite ν]
      {n d : ℕ}
      (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
      (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
      (X : ℝ → Ω → (Fin n → ℝ))
      (T : ℝ) (_hT : 0 < T) :
      ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
        LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T ∧ …
  ```
  And the docstring claims: "**Reference**: Tang, S. & Li, X. *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, Theorem 3.1."
- **Why this matters**: Tang–Li 1994 Thm 3.1 (and BET 2009 Thm 2.1) require Lipschitz `(f, g)` with `g(X_T) ∈ L²(F_T, P)`. The axiom takes only `bsdej : BSDEJData` and `X : ℝ → Ω → (Fin n → ℝ)` — *no* Lipschitz hypothesis, *no* L² integrability hypothesis, *no* progressive-measurability hypothesis on `X`. The `Lipschitz` predicate IS defined at `BSDEJ/Existence.lean:67-73` but is never invoked anywhere in the axiom. So if a user instantiates with `f(s, x, y, z, u) = e^y` (non-Lipschitz, possibly blow-up), the axiom asserts existence + uniqueness anyway, despite Tang–Li 1994 not applying. The axiom is therefore **mathematically false as stated** — it asserts a strictly stronger claim than the cited paper proves. A Mathlib reviewer reading the citation expects the Lean statement to be a faithful encoding; it isn't. Same applies to `bsdej_path_regularity` — BET 2009 Thm 2.1 explicitly requires Lipschitz f + L² ξ + the constant `C` depends on `T, L, ‖ξ‖_{L²}`; the Lean axiom states `∃ C, ∀ M, partition, Y, Z, U` ignoring all of this.
- **Recommendation**: Add the missing hypotheses:
  ```
  axiom continuousBSDEJ_exists_unique
      …
      {L : ℝ} (hL_pos : 0 < L)
      (h_lipschitz : LevyStochCalc.BSDEJ.Existence.Lipschitz bsdej ν L)
      (h_g_L2 : ∫⁻ ω, ((‖bsdej.g (X T ω)‖₊ : ℝ≥0∞)) ^ 2 ∂P < ⊤)
      (h_X_progMeas : Measurable (Function.uncurry X)) :
      ∃ (Y : …) (Z : …) (U : …), …
  ```
  Same fix for `bsdej_path_regularity`. Without these the axioms misrepresent the cited theorems.

### Finding 5 — `LevyStochCalc/Notation.lean` is a 13-line file containing only `import Mathlib` and an empty namespace

- **Severity**: HIGH
- **Location**: `LevyStochCalc/Notation.lean:1-13`
- **Evidence** (verbatim from source — the whole file):
  ```
  import Mathlib

  /-!
  # LevyStochCalc.Notation

  Local notation reserved for use across the project. Empty at bootstrap;
  each layer adds its own notation here as needed (e.g. `∫∫ φ Ñ` for the
  compensated-Poisson integral, `dW` for the Itô differential).
  -/

  namespace LevyStochCalc

  end LevyStochCalc
  ```
  Imported only by `LevyStochCalc.lean:3`. The Mathlib code-conventions doc explicitly forbids `import Mathlib`: see [Mathlib4 contribution guide](https://leanprover-community.github.io/contribute/index.html) (the "imports" section). Also `LevyStochCalc/Basic.lean:1` uses `import Mathlib` for similar reasons.
- **Why this matters**: `import Mathlib` pulls in the entire library (~5k transitive files). For an *empty* notation file, this is wasteful, slow to elaborate, and would be auto-rejected by `mathlib4/scripts/check_imports.lean` in any PR. It also makes `Basic.lean`'s imports impossible to audit — the lemmas there could be replaced with much narrower imports (`Mathlib.MeasureTheory.Function.LpSpace`, `Mathlib.MeasureTheory.Integral.SetIntegral`, etc.). For a library that aspires to be Mathlib-quality (the `cited_axioms.md` describes a Mathlib-merge replacement plan for every Tier 1 axiom), `import Mathlib` is a non-starter.
- **Recommendation**: Either delete `Notation.lean` entirely (it's unused) or replace its `import Mathlib` with the minimal imports actually needed for whatever notation appears there in the future. For `Basic.lean`, audit which Mathlib modules `eLpNorm_sub_eLpNorm_le_eLpNorm_sub`, `lintegral_sq_eq_eLpNorm_sq_on_prod`, `lintegral_sq_eval_tendsto_of_diff_tendsto_zero_*` actually depend on and inline only those. Likely candidates: `Mathlib.MeasureTheory.Function.LpSpace.Basic`, `Mathlib.MeasureTheory.Constructions.Prod.Basic`, `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`.

### Finding 6 — Tier 1 cited axioms #5 and #6 (unified existence) under-specify the filtration

- **Severity**: HIGH
- **Location**: `LevyStochCalc/Brownian/SimplePredictableRefine.lean:2094-2115` (`itoIsometry_brownian_unified_existence`); `LevyStochCalc/Poisson/Compensated.lean:2748-2767` (`itoIsometry_compensated_unified_existence`)
- **Evidence** (verbatim, `SimplePredictableRefine.lean:2108-2115`):
  ```
  axiom itoIsometry_brownian_unified_existence
      …
      (W : LevyStochCalc.Brownian.BrownianMotion P)
      (H : Ω → ℝ → ℝ)
      … :
      ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
        MeasureTheory.Martingale F Filt P ∧
        MeasureTheory.Martingale
          (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
        (∀ T, 0 < T → … L²-isometry …)
  ```
- **Why this matters**: Karatzas–Shreve Thm 3.2.6 (the cited reference) gives the L²-Itô integral as a martingale wrt the *natural augmented filtration of W*. The axiom existentially quantifies *some* filtration `Filt` instead of pinning it to `LevyStochCalc.Brownian.Martingale.naturalFiltration W`. This is a strict weakening: the literature's filtration is canonical; the axiom's is not. Downstream BSDEJ existence relies on `Z, U` being predictable wrt the natural filtration of `(W, N)` — if the `stochasticIntegral`'s martingale filtration is unconstrained, the predicate `IsBSDEJSolution` cannot connect `Compensated.stochasticIntegral N (fun ω' s e => U s ω' e)` to a process martingale wrt a *common* `(W, N)`-filtration. This is the same kind of cosmetic-clean-axiom-with-real-weakening the recursive audit was supposed to eliminate.
- **Recommendation**: Pin the filtration:
  ```
  axiom itoIsometry_brownian_unified_existence … :
    ∃ F : ℝ → Ω → ℝ,
      MeasureTheory.Martingale F (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P ∧
      MeasureTheory.Martingale (fun t ω => (F t ω) ^ 2 - …) (naturalFiltration W) P ∧
      …
  ```
  Same fix for the compensated version (pin to the natural filtration of `N`). This makes the axiom faithfully encode Karatzas–Shreve 3.2.6 / Applebaum 4.2.3.

### Finding 7 — Tier 1 cited axioms #7 and #8 are not transitively referenced by any audited theorem

- **Severity**: MEDIUM
- **Location**: `tools/full_audit_output.txt` (full output); `LevyStochCalc/Poisson/Compensated.lean:2271` (`cauchySeq_simpleIntegralLp_compensated`), `:2579` (`adaptedSimple_dense_L2_compensated`)
- **Evidence** (verbatim from `tools/full_audit_output.txt`):
  ```
  'LevyStochCalc.Poisson.Compensated.itoLevyIsometry' depends on axioms: [propext,
   Classical.choice,
   Quot.sound,
   LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence]
  ```
  No theorem's audit output mentions `cauchySeq_simpleIntegralLp_compensated` or `adaptedSimple_dense_L2_compensated`. They only appear as their own one-line entries in `tools/full_audit_output.txt:25-32`.
- **Why this matters**: The library declares 11 Tier 1 cited axioms in `tools/cited_axioms.md`. Two of them (#7 and #8) are not transitively pulled in by any audited theorem — the "Honest L²-completion" path documented in `Poisson/Compensated.lean:39-61` was replaced on 2026-05-10 by routing everything through the unified-existence axiom `itoIsometry_compensated_unified_existence`. The two simple-density / Cauchy-sequence axioms now serve only as internal API for the dead `itoIntegralLp_compensated_tendsto` chain (`Compensated.lean:2325-2348`) which itself is never called. They are dead axioms in the load-bearing dependency graph but still listed as Tier 1 — inflating the axiom-budget claim. From a Mathlib-review perspective, this is misleading: the library claims 11 cited axioms; the actual axiom set required to prove the 4 exposed theorems is 8 (the unified-existence axiom for compensated subsumes the role of the two density/Cauchy axioms in the load-bearing chain).
- **Recommendation**: Either (a) delete `cauchySeq_simpleIntegralLp_compensated` and `adaptedSimple_dense_L2_compensated` along with the dead `itoIntegralLp_compensated*` and `simplePredictable_dense_L2` chain (this saves ~600 lines of Compensated.lean), or (b) re-route `stochasticIntegral` through the L²-completion chain (back through `itoIntegralLp_compensated`) so axioms #7 and #8 actually carry their stated weight. The current "two parallel paths" state — unified-existence axiom for the load-bearing chain, density/Cauchy axioms for an orphan chain — is confusing and inflates the cited-axiom count.

### Finding 8 — 4 active `sorry` declarations remain in the codebase as dead lemmas

- **Severity**: MEDIUM
- **Location**: 
  - `LevyStochCalc/Brownian/Continuity.lean:184` (`kolmogorov_modification_ae_eq`)
  - `LevyStochCalc/Brownian/Ito.lean:3984` (`quadVar_simpleIntegral_brownian`)
  - `LevyStochCalc/Poisson/RandomMeasure.lean:139` (`poissonRandomMeasure_finite_exists`)
  - `LevyStochCalc/Poisson/Compensated.lean:1893` (`simplePredictable_dense_L2_bounded`)
- **Evidence**: All four declarations have proof body containing the term `sorry`. From `lake build` output:
  ```
  warning: LevyStochCalc/Brownian/Continuity.lean:176:6: declaration uses `sorry`
  warning: LevyStochCalc/Brownian/Ito.lean:3972:14: declaration uses `sorry`
  warning: LevyStochCalc/Poisson/RandomMeasure.lean:134:6: declaration uses `sorry`
  warning: LevyStochCalc/Poisson/Compensated.lean:1880:14: declaration uses `sorry`
  ```
  `Grep` confirms each is referenced 0 times from any other module (only inside the same file as a self-citation in the docstring). `tools/sorry_baseline.txt` is empty.
- **Why this matters**: The `shared_context_override.md` claims "`tools/sorry_baseline.txt` is **empty**. Every previously sorry'd theorem is either: Proven from Lean's standard axioms (...) OR a Tier 1 cited axiom itself." This is true *only because* `lint.sh` audits only `_audit.lean`'s 24 named theorems — the 4 sorry'd lemmas are NOT in that list. The orchestrator's claim "no sorries remain" is technically true for the load-bearing chain but misleading for the codebase as a whole. A Mathlib reviewer running `grep sorry -r LevyStochCalc/` finds 4 hits; the natural reading of the `STATUS.md` would not anticipate this. Three of the four (`simplePredictable_dense_L2_bounded`, `quadVar_simpleIntegral_brownian`, `poissonRandomMeasure_finite_exists`) are also "downstream-blockers" for the eventual deax of axioms #5, #6, #7, #8 — their dead-code status means the deax plan has unfilled holes that the cited_axioms.md "Replacement plan" sections don't accurately reflect.
- **Recommendation**: Either delete the four sorry'd lemmas (they're dead) or extend `tools/sorry_baseline.txt` to list them explicitly, so the build-state claim "sorry-free at baseline" can be honestly checked against the codebase. Add the four lemmas to `tools/full_audit.lean` so `#print axioms` surfaces their `sorryAx` dependency.

### Finding 9 — `import Mathlib` in `LevyStochCalc/Basic.lean:1` pulls the entire library

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Basic.lean:1`
- **Evidence**:
  ```
  import Mathlib

  /-!
  # LevyStochCalc.Basic
  …
  ```
- **Why this matters**: Mathlib-style discipline (matched by every Mathlib4 file) requires *minimal* imports. `Basic.lean` defines 5 fairly narrow lemmas about `eLpNorm` continuity and `lintegral`-via-`eLpNorm` bridges; these need at most `Mathlib.MeasureTheory.Function.LpSpace.Basic`, `Mathlib.MeasureTheory.Constructions.Prod.Basic`, and `Mathlib.MeasureTheory.Integral.Bochner.Basic`. The current `import Mathlib` pulls in ~5k transitive files including unrelated subjects (algebraic geometry, category theory, set theory, etc.). This (a) makes the file slow to elaborate, (b) makes the file's actual dependencies un-auditable, and (c) is precisely the import-pattern that mathlib4 PR review rejects. Combined with Finding 5, the entire library transitively pulls all of Mathlib via just two imports.
- **Recommendation**: Replace `import Mathlib` with the specific Mathlib subdirectories the lemmas actually depend on. Run `lake env lean Basic.lean` with a stub of just the needed Mathlib imports and add back what compilation requires.

### Finding 10 — `open Classical` (scoped form) is used instead of the recommended `open Classical in` or `classical` tactic

- **Severity**: LOW
- **Location**: `LevyStochCalc/Poisson/Compensated.lean:66`; `LevyStochCalc/Brownian/Ito.lean:40`
- **Evidence** (verbatim from `lake build` warnings):
  ```
  warning: LevyStochCalc/Poisson/Compensated.lean:66:5: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
  Instead, use `open Classical in` for definitions or instances, the `classical` tactic for proofs.
  For theorem statements, either add missing decidability assumptions or use `open Classical in`.

  warning: LevyStochCalc/Brownian/Ito.lean:40:5: please avoid 'open (scoped) Classical' statements: this can hide theorem statements which would be better stated with explicit decidability statements.
  ```
- **Why this matters**: Mathlib's `linter.style.openClassical` (which is `warn`-level in `lakefile.toml`'s `weak.linter.mathlibStandardSet = true`) catches exactly this. The pattern hides whether each `Decidable` instance comes from the project's own work or from `Classical.dec`. Mathlib reviewers will request this rewrite during PR.
- **Recommendation**: Replace `open Classical` with localized `open Classical in def …` / `open Classical in theorem …` blocks, or use the `classical` tactic inside proofs that need it.

### Finding 11 — 59 misuses of the `show` tactic (style linter warning)

- **Severity**: LOW
- **Location**: 59 different locations across `LevyStochCalc/Brownian/{Ito,Martingale,SimplePredictableRefine}.lean`, `LevyStochCalc/Poisson/Compensated.lean`, and `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean`. Examples: `Brownian/Ito.lean:1087, 1604, 1713, 1838, 1893, 1899, 1924, 1926, 1930, 1955, 1958, 1961, 1983, 1985, 1989, 2078, 2109, 2115, 2121, 2125, 2266, 2281, 2312, 2424, 2474, 2483, 2519, 2542, 2676, 2690, 2721, 2836, 2946, 3666` (sample).
- **Evidence** (sample from `lake build`):
  ```
  warning: LevyStochCalc/Brownian/Ito.lean:1087:2: The `show` tactic should only be used to indicate intermediate goal states for readability.
  However, this tactic invocation changed the goal. Please use `change` instead for these purposes.
  ```
- **Why this matters**: The `show` tactic is supposed to display the current goal for readability, not change it. When `show X` changes the goal, the correct tactic is `change X`. 59 misuses across the library is a systemic violation of the Mathlib style linter and would be flagged in every file of a hypothetical Mathlib PR. The volume here is striking — there's a habitual pattern in the author's code of using `show` to perform definitional unfolding.
- **Recommendation**: Sweep through the 59 sites and replace `show` with `change` where the tactic invocation modifies the goal. This is mechanical with a project-wide regex.

### Finding 12 — 29 uses of the deprecated `push_neg` tactic; multiple other deprecated Mathlib API calls

- **Severity**: LOW
- **Location**: 29 sites for `push_neg` (e.g. `Brownian/Ito.lean:184, 1100, 1104, 1108, 2462, 2664, 3728, 3820, 3832, 3886`; `Brownian/Martingale.lean:72, 118, 162, 499, 526, 739, 772`; `Poisson/Compensated.lean:266, 1605, 1609, 1613`); plus deprecated symbol usages:
  - `MeasureTheory.lintegral_finset_sum` (5 sites; should be `lintegral_finsetSum`)
  - `MeasureTheory.integral_finset_sum` (6 sites; should be `integral_finsetSum`)
  - `MeasureTheory.integrable_finset_sum` (6 sites; should be `integrable_finsetSum`)
  - `Fin.coe_castSucc` (4 sites; should be `Fin.val_castSucc`)
  - `mul_le_mul_left'` (4 sites; should be `mul_le_mul_right`)
  - `Nat.tendsto_pow_atTop_atTop_of_one_lt` (1 site; should be unqualified `tendsto_pow_atTop_atTop_of_one_lt`)
  - `MeasureTheory.condExp_finset_sum` (1 site; should be `condExp_finsetSum`)
- **Evidence** (sample from `lake build`):
  ```
  warning: LevyStochCalc/Brownian/Ito.lean:1100:8: `push_neg` has been deprecated. Prefer using `push Not` instead.
  warning: LevyStochCalc/Poisson/Compensated.lean:302:10: `MeasureTheory.lintegral_finset_sum` has been deprecated: Use `MeasureTheory.lintegral_finsetSum` instead
  ```
- **Why this matters**: Mathlib v4.30.0-rc2 + `lake-manifest.json` rev `0e208554a6143756c125878a8fe8b17a331d39f7` includes deprecation warnings for these — the renamed symbols are the current API. Existing deprecations cause continuous-build noise (each appears in `lake build` output) and signal staleness. Future Mathlib bumps will remove these aliases entirely and break the build.
- **Recommendation**: Project-wide find-and-replace. Each deprecation message includes the replacement; this should be mostly mechanical. For `push_neg → push Not`, see the deprecation message; for the `finset_sum → finsetSum` family, the API change is a simple rename.

### Finding 13 — 19 `set_option maxHeartbeats <large>` lines without explanatory comments

- **Severity**: LOW
- **Location**: 19 sites, e.g. `Brownian/Ito.lean:1119, 2881, 3280, 3473`; `Poisson/Compensated.lean:1896`; etc.
- **Evidence** (sample from `lake build`):
  ```
  warning: LevyStochCalc/Brownian/Ito.lean:1119:0: Please, add a comment explaining the need for modifying the maxHeartbeat limit, as in `set_option maxHeartbeats 400000 in -- comment`
  ```
  Inspection of `Compensated.lean:1895-1897`:
  ```
  -- maxHeartbeats: triangle-inequality lift through three nested lintegrals + Tonelli.
  set_option maxHeartbeats 1600000 in
  /-- **Density of simple predictable integrands in L²(dP ⊗ ds ⊗ dν).** … -/
  ```
  Here a comment IS present but at line 1895 — the linter wants the comment on the `set_option` line itself.
- **Why this matters**: Mathlib's `linter.style.maxHeartbeats` requires a comment justifying any raise above the default. Bumping heartbeats to `1600000` (~16× the default) without explanation suggests proofs that should be refactored (named sub-lemmas, lemma extraction) rather than just given more compute. From a maintainability standpoint, 19 such bumps is a warning sign — the file has at least 19 proofs that may be brittle to future Mathlib changes.
- **Recommendation**: Audit each `maxHeartbeats` site. For each one: (a) add an inline comment explaining what specific elaboration step needs the budget; (b) where the proof can be split into named sub-lemmas to reduce per-proof elaboration, do so.

### Finding 14 — `LevyStochCalc.lean:6` "Poisson.RandomMeasure" import inconsistent with sibling-file naming

- **Severity**: LOW
- **Location**: `LevyStochCalc.lean:6-8`; file `LevyStochCalc/Poisson/RandomMeasure.lean`
- **Evidence** (verbatim from `LevyStochCalc.lean:5-12`):
  ```
  -- Layer 0: Compensated Poisson
  import LevyStochCalc.Poisson.RandomMeasure
  import LevyStochCalc.Poisson.NaturalFiltration
  import LevyStochCalc.Poisson.Compensated

  -- Layer 1: Itô-Lévy isometry  → I02
  import LevyStochCalc.Poisson.L2Isometry
  ```
  But `LevyStochCalc/Poisson/Martingale.lean` (677 lines, defining `martingale_simpleIntegral_compensatedPoisson` and `itoIsometry_compensatedPoisson_general`) is **NOT** imported by the root.
- **Why this matters**: `Poisson/Martingale.lean` contains the `itoIsometry_compensatedPoisson_general` theorem (line 651) operating on a *constant-function placeholder* `itoIntegral_compensatedPoisson` (line 640) — see the next finding. Since it's not imported by the root, it's dead code from a prior project phase. Either it should be removed entirely or reincorporated. Its existence as orphaned-but-compiling code creates confusion: a user searching for `itoIntegral_compensatedPoisson` finds a `(constant in ω) · √R.toReal` placeholder that has no relation to the live `Poisson.Compensated.stochasticIntegral`.
- **Recommendation**: Delete `LevyStochCalc/Poisson/Martingale.lean` (and the parallel `Brownian/Ito.lean:4020-4060` `itoIntegral_brownian` placeholder + `itoIsometry_brownian_general` theorem). These are remnants of the pre-unified-existence-axiom design and serve no purpose post-2026-05-10 refactor. Keeping them increases the codebase by ~700 lines of misleading content.

### Finding 15 — Stale documentation: `L2Isometry.lean:33-34` and `Brownian/Ito.lean` docstrings still refer to "underlying sorry transitively"

- **Severity**: LOW
- **Location**: `LevyStochCalc/Poisson/L2Isometry.lean:30-34`; `LevyStochCalc/Brownian/Ito.lean:32-35`
- **Evidence** (verbatim from `Poisson/L2Isometry.lean:30-34`):
  ```
  ## Status

  Phase 2 spec: clean wrapper around `Compensated.itoLevyIsometry`. ENNReal-norm
  form matches the dissertation's `I02` axiom exactly. Currently inherits the
  underlying `sorry` transitively.
  -/
  ```
  But `tools/full_audit_output.txt:85-88`:
  ```
  'LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry' depends on axioms: [propext,
   Classical.choice,
   Quot.sound,
   LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence]
  ```
  — no `sorryAx`. Similarly `Brownian/Ito.lean:32-35` claims "The headline `itoIsometry` reduces to them [sorry'd named lemmas]"; the headline now reduces to the *unified-existence axiom* directly.
- **Why this matters**: A Mathlib reviewer reading these module docstrings expects to see `sorryAx` in the transitive axiom set. They won't, because the 2026-05-10 unified-existence refactor bypassed the sorry'd chain. The docstring claim is materially false (post-refactor). The user has been explicit that "cosmetic axiom-cleanliness is worse than a documented axiom" — and stale-documentation that says "transitively sorry'd" when the code is actually "transitively axiom-X'd" is exactly that kind of cosmetic mismatch.
- **Recommendation**: Update the module docstrings of `L2Isometry.lean` and `Brownian/Ito.lean` (and any other file that still references the sorry'd chain) to reflect the post-2026-05-10 state: the headline reduces to the relevant unified-existence Tier 1 cited axiom. The mismatch undermines the project's stated honesty discipline.

### Finding 16 — Three `True := trivial` "lemmas" pretending to be construction steps

- **Severity**: LOW
- **Location**: 
  - `LevyStochCalc/Brownian/Construction.lean:142-146` (`brownian_dyadicTime_exists`)
  - `LevyStochCalc/Brownian/Construction.lean:156` (`brownian_extend_to_real : True := trivial`)
  - `LevyStochCalc/Poisson/RandomMeasure.lean:146-148` (`poissonRandomMeasure_combine`)
  - `LevyStochCalc/BSDEJ/Existence.lean:80-91` (`picardMap_contraction`)
- **Evidence** (verbatim from `Brownian/Construction.lean:142-156`):
  ```
  lemma brownian_dyadicTime_exists :
      ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (P' : Measure Ω')
        (_ : IsProbabilityMeasure P'),
        True :=
    ⟨PUnit, ⊤, MeasureTheory.Measure.dirac PUnit.unit, inferInstance, trivial⟩

  /-- **Step 3: extension to all of `ℝ`.** A process defined on dyadic times
  can be extended to `[0, ∞)` by continuity (after KC modification, which is
  in `LevyStochCalc.Brownian.Continuity`). The extended process satisfies
  the Brownian increment law on all of `ℝ`.

  Spec is `True`-valued; the actual extension is delivered inline within
  `BrownianMotion.exists` using `holder_dense_extends_continuous` (proved)
  plus the KC modification result. -/
  lemma brownian_extend_to_real : True := trivial
  ```
- **Why this matters**: These are placeholder "construction steps" that present as named lemmas (giving the impression of intermediate results) but actually prove only `True` or `Nonempty PUnit`. They take docstrings of substantial mathematical content and label proofs that have none. From a code-shape standpoint, this is a classic *anti-pattern* the user has been hunting: the docstring narrates Karatzas–Shreve-level mathematics while the proof body is `trivial`. None of them is referenced by any other declaration. They're dead-code with deceptive docstrings.
- **Recommendation**: Delete all four (they're not used by `BrownianMotion.exists`, `PoissonRandomMeasure.exists_of_sigmaFinite`, or `continuousBSDEJ_exists_unique`). Replacing them with `axiom`-style "spec" declarations or just removing them entirely is preferable to having `True := trivial` stubs that look like proven content in `Grep` output.

## Per-claim verdicts on the 11 Tier 1 axioms + ~16 derived theorems

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `Brownian.BrownianMotion.exists` (Tier 1 #1) | EARNED | Honest axiom, Karatzas–Shreve 2.1.5 citation accurate, faithful statement. |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` (Tier 1 #2) | EARNED | Honest axiom, Applebaum 2.3.1 citation, faithful statement. |
| `Brownian.Continuity.kolmogorovChentsov_modification` (Tier 1 #3) | EARNED | Honest axiom, Karatzas–Shreve 2.2.8 citation, faithful statement. |
| `Brownian.Martingale.brownian_martingale_rightCont` (Tier 1 #4) | EARNED | Honest axiom; statement matches Karatzas–Shreve 2.7.7 + 2.7.9. |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` (Tier 1 #5) | **WEAK** | Filtration is existentially quantified instead of pinned to `naturalFiltration W` (Finding 6). |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` (Tier 1 #6) | **WEAK** | Same filtration-not-pinned issue (Finding 6). |
| `Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` (Tier 1 #7) | **WEAK** | Dead in load-bearing chain post-2026-05-10 refactor (Finding 7). |
| `Poisson.Compensated.adaptedSimple_dense_L2_compensated` (Tier 1 #8) | **WEAK** | Dead in load-bearing chain post-2026-05-10 refactor (Finding 7). |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` (Tier 1 #9) | **TRIVIAL/WRONG** | Missing Lipschitz + L² + progressive-measurability hypotheses required by Tang–Li 1994 (Finding 4). Predicate is non-vacuous post the 2026-05-11 strengthening but axiom statement is over-strong vs. the cited theorem. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` (Tier 1 #10) | **TRIVIAL/WRONG** | Missing Lipschitz + L² hypotheses required by Bouchard–Elie–Touzi 2009 (Finding 4). Same predicate issue as #9. |
| `Ito.JumpFormula.itoLevyFormula` (Tier 1 #11, newly DEMOTED) | **TRIVIAL** | Statement still has no internal pinning of the four terms to the literature integrals; demotion to `axiom` did not fix the vacuity (Finding 2). |
| `Brownian.Multidim.MultidimBrownianMotion.exists` (derived) | EARNED | Real Lean proof via product-measure construction. |
| `Brownian.Continuity.brownian_continuous_modification` (derived) | EARNED | Forwards through Tier 1 #3. |
| `Brownian.Martingale.brownian_martingale` (derived) | EARNED | Lean-std-only via `condExp_increment_eq_zero_aux`. |
| `Brownian.Martingale.brownian_quadVar` (derived) | EARNED | Lean-std-only. |
| `Brownian.Martingale.brownian_filtration_rightContinuous` (derived) | EARNED | Forwards through Tier 1 #4. |
| `Brownian.Ito.itoIsometry` (derived) | WEAK | Extracts conjunct 3 of Tier 1 #5; inherits the #5 weakness (Finding 6). |
| `Brownian.Ito.martingale_stochasticIntegral` (derived) | WEAK | Extracts conjunct 1 of Tier 1 #5. |
| `Brownian.Ito.quadVar_stochasticIntegral` (derived) | WEAK | Extracts conjunct 2 of Tier 1 #5. |
| `Poisson.Compensated.itoLevyIsometry` (derived) | WEAK | Extracts conjunct 3 of Tier 1 #6; inherits the #6 weakness. |
| `Poisson.Compensated.martingale_stochasticIntegral` (derived) | WEAK | Extracts conjunct 1 of Tier 1 #6. |
| `Poisson.Compensated.quadVar_stochasticIntegral` (derived) | WEAK | Extracts conjunct 2 of Tier 1 #6. |
| `Poisson.Compensated.cadlag_modification_exists` (derived) | WEAK | Extracts conjunct 4 of Tier 1 #6. |
| `Poisson.L2Isometry.itoLevyIsometry` (derived, dissertation forwarder target) | WEAK | 1-line forwarder of `Compensated.itoLevyIsometry`; same filtration weakness. |
| `Ito.Setting.JumpDiffusion.exists_unique` (derived) | **TRIVIAL** | Named "exists_unique" but proves only Nonempty; constant-path witness on a `True`-valued `is_solution` field (Finding 3). |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` (derived) | **TRIVIAL** | Literal trivial-witness proof `⟨0, 0, 0, ξ − 𝔼[ξ]⟩` (Finding 1). |

Tier 1 cited axioms #1–#4 are clean honest cited axioms. Tier 1 #5, #6 are weakened by under-specified filtrations. Tier 1 #7, #8 are dead weight. Tier 1 #9, #10 are mathematically over-strong vs. literature (missing Lipschitz). Tier 1 #11 (newly demoted) is still vacuous. Among derived theorems, `JumpDiffusion.exists_unique` and `jacodYor_representation` are trivial-witness theorems missed by the 2026-05-11 recursive audit.

## Tools and sources used

- **Lean tools called**: 
  - `lake build` (2× runs) — confirmed 8401 jobs PASS, 198 warnings; captured deprecation and style-linter output.
  - `lake env lean tools/full_audit.lean` (1× run) — confirmed transitive axiom sets for all 24 audited declarations match `tools/full_audit_output.txt`.
  - `mcp__lean-lsp__lean_diagnostic_messages` attempted once on `Brownian/Multidim.lean` — MCP connection closed mid-call; substituted with `lake build` output.
  - No `lean_verify` / `lean_hover_info` calls needed beyond what `Grep`+`Read` covered.
- **Web searches**: none required — all citations in `tools/cited_axioms.md` are well-known (Karatzas–Shreve, Le Gall, Applebaum, Tang–Li, Bouchard–Elie–Touzi); verification of citation accuracy is persona 11's lens.
- **Web fetches**: none.
- **Papers consulted**: the docstring citations in source were treated as accurate for the purpose of comparing Lean statements to claimed paper-content; the audit explicitly notes (Finding 4) where the Lean statement is strictly stronger than the docstring's cited theorem (Tang–Li 1994 Thm 3.1 requires Lipschitz; the Lean axiom doesn't take that hypothesis).

## What you couldn't verify

- Did NOT exhaustively read the 4060-line `Brownian/Ito.lean` or the 2907-line `Poisson/Compensated.lean`; instead used `Grep` for `axiom`/`theorem`/`lemma` declarations and read targeted excerpts around each. A full lemma-by-lemma audit of the auxiliary chain (~60 named lemmas in `Brownian/Ito.lean` building up to `simplePredictable_dense_Lp_brownian`) would require ~4 hours of additional reading and is out of scope for the lean-formalisation lens.
- Did NOT verify the actual mathematical content of `Compensated.simplePredictable_dense_L2_bounded`'s `sorry` — only flagged that it is a `sorry` and dead in the load-bearing chain. Whether the math would go through if attempted is persona 5/7's call.
- Did NOT verify that `convert this using 1` at `Brownian/Multidim.lean:230` closes cleanly — `lake build` reports the file compiles without errors so this is implicit, but `mcp__lean-lsp__lean_goal` would give certainty (the MCP connection dropped).
- Did NOT audit every `set_option maxHeartbeats` site to confirm whether the budget is justified — flagged the 19 sites and the missing-comment pattern but did not investigate each individually.
- The 198 build warnings include some `unused variable` warnings (e.g. `BSDEJ/Existence.lean:84-87 unused variable W/N/X`); these are minor and noted in aggregate but not enumerated individually.

## Recommendations for the project (≤ 5 bullets)

- **Run the recursive trivial-witness audit again, broader scope**: the 2026-05-11 pass demoted `itoLevyFormula` and strengthened `IsBSDEJSolution` but missed `jacodYor_representation`, `JumpDiffusion.exists_unique`, and the post-demotion vacuity of `itoLevyFormula` itself. Specifically, search for the patterns `refine ⟨0,` and `:= trivial` and `is_solution : True` across the codebase; each is a trivial-witness flag.
- **Strengthen Tier 1 #9, #10 with the missing Lipschitz + L² + measurability hypotheses**: the current statements claim Tang–Li 1994 / Bouchard–Elie–Touzi 2009 content under strictly weaker hypotheses than the cited papers, which is a misrepresentation in the docstring citation. The `Lipschitz` predicate already exists at `BSDEJ/Existence.lean:67-73`; thread it into both axioms.
- **Pin the filtration in Tier 1 #5, #6**: replace `∃ (F : ℝ → Ω → ℝ) (Filt : Filtration ℝ _), Martingale F Filt P ∧ …` with `∃ F : ℝ → Ω → ℝ, Martingale F (naturalFiltration W) P ∧ …`. This makes the unified-existence axioms faithful encodings of Karatzas–Shreve 3.2.6 / Applebaum 4.2.3 + 4.2.4 and unblocks the BSDEJ uniqueness statement's filtration coordination across `W` and `N`.
- **Delete the dead code**: `Notation.lean` (empty + `import Mathlib`); the placeholder constant-function `itoIntegral_brownian` and `itoIntegral_compensatedPoisson` and `itoIsometry_*_general` chain; the 4 sorry'd dead lemmas; the 3 `True := trivial` placeholder construction-step lemmas; the unimported `Poisson/Martingale.lean`. Estimated reduction: ~1500 lines.
- **Fix the Mathlib-style linter regressions before any external review**: 198 warnings is too many for a library claiming Mathlib-merge readiness. The 8 deprecated symbols, 59 `show → change` rewrites, 29 `push_neg → push Not` rewrites, and 19 `maxHeartbeats` comments are mostly mechanical fixes; running them clears the warnings to a baseline that wouldn't be auto-rejected on a Mathlib PR.
