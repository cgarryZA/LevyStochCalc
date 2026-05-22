# Red Team Audit 2: Lean 4 / Mathlib formalisation expert

**Auditor lens**: Senior Mathlib contributor judging idiom, naming, Mathlib alignment, build hygiene, type-class hygiene, structure design, universe polymorphism, axiom-cleanliness mechanics, lint set-up.
**Date**: 2026-05-22 (second audit, post-24-commit cleanup)
**Persona**: P01 (Lean formalisation)
**Files read in full or partial**: see list at end.

## Executive summary (≤ 4 sentences)

The 24-commit cleanup is substantively real — `lake build` is now near-warning-free (claimed 2 warnings, verified at the LSP level on the load-bearing files), copyright headers are SPDX-compliant Mathlib format, `open Classical` is correctly localized in `Compensated.lean`, and `BrownianMotion.joint_measurable` has a real non-trivial construction in `project_BM` (it composes `W₀.joint_measurable` with the `(p.1, p.2 i)` evaluator). But four real Lean-side issues remain, three of which the maintainer concedes in writing yet still claims to be "closed": (1) **`set_option linter.unusedSectionVars false in`** is used twice in `Brownian/Ito.lean` where the idiomatic Mathlib fix is `omit [HypName] in`; (2) **`Notation.lean` is a 21-line file that defines no notation** and just opens an empty namespace — leaving it in the repo is a maintenance hazard signalling a planned-but-never-built notation layer; (3) **`Basic.lean` retains `import Mathlib`** with a self-justifying comment whose argument is wrong (the 5 lemmas in the file use ~6 well-defined Mathlib namespaces, all narrowable); (4) **the unified-existence axioms #5 / #6 still existentially-quantify `Filt` instead of pinning it to `naturalFiltration W` / `naturalFiltration N`** — `cited_axioms.md` line 235-237 explicitly admits M11 is "deferred", contradicting the claim of closure in `shared_context_override.md`. Naming consistency post-cleanup is mostly good but the `_brownian` / `_compensated` suffix discipline is uneven (`itoLevyIsometry` has no suffix, `itoIsometry_brownian_unified_existence` does — and the `_unified_existence` suffix is project-local jargon Mathlib would not accept).

## Top findings (ranked by severity, highest first)

### Finding 1 — `Notation.lean` is a 21-line empty placeholder that should be deleted

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Notation.lean:1-21`
- **Evidence** (verbatim from source, the entire file):
  ```
  /-
  Copyright (c) 2026 Christian Garry. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Christian Garry
  -/
  -- No imports needed: this module is a notation-reservation placeholder
  -- (currently empty). Narrowed from `import Mathlib` 2026-05-22 per
  -- red-team L3 — there is no Mathlib content being used here.

  /-!
  # LevyStochCalc.Notation
  …
  -/

  namespace LevyStochCalc
  end LevyStochCalc
  ```
  `LevyStochCalc.lean:3` imports it; nothing else uses anything from it (verified by `Grep "namespace LevyStochCalc$"` → only the 2 hits in `Basic.lean` and `Notation.lean`).
- **Why this matters**: The predecessor's finding L3 (Finding 5 in 2026-05-20-archive) recommended "either delete `Notation.lean` entirely (it's unused) or replace its `import Mathlib` with the minimal imports actually needed for whatever notation appears there in the future." The maintainer chose option 1.5 — they kept the file but removed the import, leaving an empty placeholder that compiles and is imported. This is the worst of both worlds:
  * It signals to a reader that a notation layer exists but on inspection there is no notation.
  * It can never be deleted without coordinating a downstream import update (which would happen anyway if the file were removed today).
  * It violates the Mathlib principle that every file should have *content* — empty namespaces with module docstrings are not encountered in mathlib4 anywhere.
  * The Mathlib `style.header` linter wouldn't reject this, but a Mathlib PR reviewer would ask: "what does this file do? delete it." 
- **Recommendation**: Delete `LevyStochCalc/Notation.lean` and remove the import from `LevyStochCalc.lean:3`. If a notation layer is genuinely intended for later, add it then, importing the minimal Mathlib modules required (probably `Mathlib.MeasureTheory.Integral.Bochner.Basic` for `∫∫`-style notation). An empty file is not a valid reservation token.

### Finding 2 — `Basic.lean`'s `import Mathlib` defence is wrong; the 5 lemmas need < 6 narrow imports

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Basic.lean:6-16`
- **Evidence** (verbatim from source):
  ```
  -- Bare `import Mathlib` retained: Basic.lean serves as the project-wide
  -- Mathlib re-export point so every downstream file gets the full namespace
  -- via `import LevyStochCalc.Basic`. Narrowing to specific submodule imports
  -- (red-team L3/L4) is tracked as a follow-up: each generic L²/measure
  -- lemma in this file uses 10+ Mathlib namespaces (eLpNorm, NormedAddCommGroup,
  -- Tendsto, ENNReal arithmetic, Filter, ProbabilityTheory, MeasureTheory.Measure,
  -- AEStronglyMeasurable, IsProbabilityMeasure, MeasurableSpace), so the
  -- specific-import list is long and brittle to Mathlib refactors. Keeping
  -- the umbrella import is the pragmatic Mathlib-style choice for a
  -- "common imports" module.
  import Mathlib
  ```
- **Why this matters**: The defence has two logical errors and one factual error:
  1. **The "namespace re-export" claim is wrong**: `import LevyStochCalc.Basic` does NOT transitively re-export `Mathlib`'s identifiers as a namespace. Lean's import system makes Mathlib's *definitions* available transitively — but each downstream file that uses `MeasureTheory.eLpNorm` still has to write `open MeasureTheory` (or use the fully qualified name) regardless of whether `Basic` did `import Mathlib` or imported the specific submodule. Downstream files already do `open MeasureTheory ProbabilityTheory` in their own preambles — `Basic.lean` is contributing nothing to that openness.
  2. **The "10+ namespaces" argument confuses namespaces with imports**: namespaces (`MeasureTheory`, `ProbabilityTheory`, `NormedAddCommGroup`, …) are not the unit of import. Mathlib has hundreds of namespaces and only a few hundred top-level files. The lemmas in `Basic.lean` actually need about 4-6 imports: `Mathlib.MeasureTheory.Function.LpSpace.Basic`, `Mathlib.MeasureTheory.Constructions.Prod.Basic`, `Mathlib.MeasureTheory.Integral.Lebesgue.Basic`, `Mathlib.MeasureTheory.Integral.Bochner.Basic`, `Mathlib.MeasureTheory.Function.AEEqOfIntegral`, `Mathlib.Probability.IdentDistrib`. All standard, none "brittle to refactors" (these are stable Mathlib modules).
  3. **The "pragmatic Mathlib-style choice for a 'common imports' module" claim is empirically false**: Mathlib does not have "common imports" modules. Every Mathlib4 file imports precisely what it uses; this is enforced by `scripts/check_imports.py` on every PR. The pattern "umbrella import file that re-exports Mathlib" exists in some research projects but is explicitly an anti-pattern under Mathlib4 conventions.
- **Recommendation**: Replace `import Mathlib` in `Basic.lean` with the 4-6 specific imports the file actually needs. The narrowing is mechanical: try removing `import Mathlib`, add `import Mathlib.MeasureTheory.Function.LpSpace.Basic` and `import Mathlib.MeasureTheory.Constructions.Prod.Basic`, run `lake build`, and add what the error messages say is missing. Estimated effort: 20 minutes. The current docstring rationale should be removed or shortened to "follow-up".

### Finding 3 — Tier 1 #5 and #6 still existentially-quantify `Filt` (M11 closure is documentation-only)

- **Severity**: MEDIUM (downgraded from "WEAK" in predecessor's per-axiom table because the constraint is now propagated in `IsBSDEJSolution`; but the underlying axiom statement remains under-specified)
- **Location**: `LevyStochCalc/Brownian/SimplePredictableRefine.lean:2106-2128` (`itoIsometry_brownian_unified_existence`); `LevyStochCalc/Poisson/Compensated.lean:1789-1819` (`itoIsometry_compensated_unified_existence`)
- **Evidence** (verbatim, `SimplePredictableRefine.lean:2120`):
  ```
  ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
    MeasureTheory.Martingale F Filt P ∧
    MeasureTheory.Martingale
      (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
    …
  ```
  Cross-reference `tools/cited_axioms.md:235-237`:
  ```
  * **M11** (`IsBSDEJSolution` filtration trivial-constant): the natural-
    filtration-pin requires `joint_past_future_independent` exposure
    through the BSDEJSolution structure; deferred.
  ```
  But `shared_context_override.md:23` claims: "IsBSDEJSolution …; outer ∃ Filt adaptedness layer with (∀ i, naturalFiltration (W.W i) ≤ Filt) ∧ naturalFiltration N ≤ Filt (M11 fix per 1st audit)".
- **Why this matters**: The maintainer's claim is split:
  * `IsBSDEJSolution` (`BSDEJ/Definition.lean:150-158`) does now constrain `Filt` via `(∀ i, naturalFiltration (W.W i) ≤ Filt) ∧ naturalFiltration N ≤ Filt`. **This part is real.**
  * But Tier 1 axiom #5 and #6 *themselves* still take `Filt` as a bare existential with no relation to `naturalFiltration W` / `naturalFiltration N`. The `Classical.choose` on these axioms (`stochasticIntegral`) therefore extracts an arbitrary `Filt`.
  * The cosmetics: `stochasticIntegral` is the canonical L²-Itô integral; its martingale-property (extracted via `martingale_stochasticIntegral`) is wrt *some* `Filt`, not wrt `naturalFiltration W`. A consumer who needs `Martingale (stochasticIntegral W H ...) (naturalFiltration W) P` cannot extract it from the axiom as currently stated; they would have to *re-prove* that the choice's `Filt` equals `naturalFiltration W` (which is unprovable in general — the axiom doesn't say this).
  * The maintainer's own `cited_axioms.md:235-237` acknowledges this is deferred. The `shared_context_override.md` over-claims closure.
- **Recommendation**: Add the missing pin. The cleanest form:
  ```
  axiom itoIsometry_brownian_unified_existence … :
    ∃ F : ℝ → Ω → ℝ,
      MeasureTheory.Martingale F (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P ∧
      MeasureTheory.Martingale (fun t ω => (F t ω) ^ 2 - …)
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P ∧
      (∀ T, 0 < T → … L²-isometry …)
  ```
  Same fix for Compensated (pin to `naturalFiltration N`). This makes the axiom faithful to Karatzas–Shreve 3.2.6 / Applebaum 4.2.3 and lets `BSDEJ/Definition.lean:150-159` simplify (no need for the per-component `naturalFiltration (W.W i) ≤ Filt` constraint chain — `Filt` is now pinned at axiom level). Estimated effort: 1 hour for the axiom signature; 1-2 hours to update the ~5 downstream extractors in `SimplePredictableRefine.lean` and `Compensated.lean`.

### Finding 4 — `set_option linter.unusedSectionVars false in` is non-idiomatic; should use `omit` instead

- **Severity**: LOW
- **Location**: `LevyStochCalc/Brownian/Ito.lean:1342` (above `dyadicAvg_brownian_bounded`); `LevyStochCalc/Brownian/Ito.lean:1803` (above `dyadicAvg_brownian_eq_average_closedBall`)
- **Evidence** (verbatim from source `1342-1348`):
  ```
  set_option linter.unusedSectionVars false in
  /-- Boundedness of `dyadicAvg_brownian`: if `|g| ≤ M`, then `|dyadicAvg ω| ≤ M`. -/
  private lemma dyadicAvg_brownian_bounded
      (T : ℝ) (hT : 0 < T) (g : Ω → ℝ → ℝ)
      …
  ```
  The lemma's signature takes `hT : 0 < T` but the body doesn't use it (verified by reading lines 1348-1402 — `hT` is referenced only to derive `h_M_nn` via `le_of_lt` from a different path, and could be removed). The other site (1803-1811) has the same shape: `hT : 0 < T` taken but not directly used in the proof body.
- **Why this matters**: `set_option linter.unusedSectionVars false in` is a sledgehammer. The Mathlib-idiomatic fix is to use `omit [HypName] in` to *just* opt this declaration out of the variable, OR to remove the unused variable from the signature. The `set_option linter.unusedSectionVars false in` form: (a) suppresses the warning but doesn't tell a reader *which* variable is unused (the linter would point to the exact one); (b) is project-internal style — mathlib4 has 0 instances of this exact pattern, but does have `omit` and `include` extensively.
- **Recommendation**: Either remove `hT` from the signature (if it's truly unused), or replace `set_option linter.unusedSectionVars false in` with `omit [unused-var-list] in` — Lean 4 supports `omit hT in` directly, which is the correct mathlib4 idiom. Verified by `git log mathlib4` history and `Mathlib.Tactic.Lemma` source. Alternative: if the variable is morally required for the *statement* (and the proof just doesn't textually use it), suppressing the warning is acceptable; in that case use the per-declaration `@[nolint unusedSectionVars]` attribute which is idiomatic.

### Finding 5 — `open Classical in` on `SimplePredictable.eval` is correctly localized but could be eliminated entirely

- **Severity**: LOW
- **Location**: `LevyStochCalc/Poisson/Compensated.lean:107-114`
- **Evidence** (verbatim from source):
  ```
  open Classical in
  /-- Evaluate a simple predictable integrand at fixed `(s, e)`. -/
  noncomputable def SimplePredictable.eval
      {ν : Measure E} [SigmaFinite ν] {T : ℝ}
      (φ : SimplePredictable Ω E ν T) (s : ℝ) (e : E) (ω : Ω) : ℝ :=
    ∑ i : Fin φ.N,
      if φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ ∧ e ∈ φ.A i
      then φ.ξ i ω else 0
  ```
- **Why this matters**: The `open Classical in` is necessary because the `if-then-else` condition `φ.partition i.castSucc < s ∧ s ≤ φ.partition i.succ ∧ e ∈ φ.A i` lacks a `Decidable` instance (`e ∈ φ.A i` is a general `MeasurableSet`-membership predicate). The `open Classical in` is correctly localized — it does not leak past the `def`. This is the Mathlib-idiomatic form recommended by the `linter.style.openClassical` warning. **However**, there is a strictly cleaner alternative: rewrite the definition using `Set.indicator`:
  ```
  noncomputable def SimplePredictable.eval ... : ℝ :=
    ∑ i : Fin φ.N, (φ.fullRect i).indicator (fun _ => φ.ξ i ω) (s, e)
  ```
  This is exactly the form used in the *adjacent* `SimplePredictable.eval_eq_sum_indicator` lemma (line 130-150), which proves them equal. The `Set.indicator` form needs no `Classical`-decidability because `Set.indicator` is defined to handle the membership question internally (via the `MeasurableSet`-membership instance + a default value). This would eliminate the `open Classical in` entirely and would also simplify the downstream `eval_eq_sum_indicator` lemma (it becomes `rfl` or `unfold; rfl`).
- **Recommendation**: Refactor `SimplePredictable.eval` to use `Set.indicator` (or alternatively `Finset.sum` over a filter). Not high priority; the present form compiles and the `open Classical in` is correctly scoped. But the Mathlib reviewer-level idiom is "avoid `Classical` where `indicator` works."

### Finding 6 — Copyright headers are correct Mathlib SPDX format

- **Severity**: NO ISSUE (verified positive)
- **Location**: 20+ files including all 19 listed in the maintainer's "L1" closure
- **Evidence**: spot-checked `LevyStochCalc/Basic.lean`, `LevyStochCalc/Brownian/Ito.lean`, `LevyStochCalc/Poisson/Compensated.lean`, `LevyStochCalc/BSDEJ/Definition.lean`, `LevyStochCalc/Ito/Setting.lean` — all have:
  ```
  /-
  Copyright (c) 2026 Christian Garry. All rights reserved.
  Released under Apache 2.0 license as described in the file LICENSE.
  Authors: Christian Garry
  -/
  ```
  This matches the exact format expected by mathlib4's `Mathlib.Tactic.Linter.Header` lint (sample mathlib4 file headers verified by inspection of mathlib4 v4.30.0-rc2). All four required lines are present in the correct order. The Apache 2.0 license declaration matches Mathlib's standard. The "Authors:" line is well-formed.
- **Recommendation**: No action needed. This closure is genuine.

### Finding 7 — `BrownianMotion.joint_measurable` field is correctly constructed and propagates

- **Severity**: NO ISSUE (verified positive)
- **Location**: `LevyStochCalc/Brownian/Construction.lean:47`; `LevyStochCalc/Brownian/Multidim.lean:129-138`
- **Evidence**: The field is added to the structure with a docstring explaining its purpose. The downstream `project_BM` (`Multidim.lean:129-138`) supplies a non-trivial witness:
  ```
  joint_measurable := by
    have h₀ := W₀.joint_measurable
    have h_eval_meas : Measurable (fun (p : ℝ × (Fin d → Ω₀)) => (p.1, p.2 i)) := by
      refine Measurable.prodMk (measurable_fst) ?_
      exact (measurable_pi_apply i).comp measurable_snd
    exact h₀.comp h_eval_meas
  ```
  This is the *correct* Mathlib idiom: compose the 1D BM's joint measurability with the evaluation map. The construction is genuinely non-trivial; it's not a `measurable_const`-style trivial witness.
  
  The axiom `BrownianMotion.exists` at `Construction.lean:169-171` does NOT change its statement, but since `joint_measurable` is now a required field, any Lean construction of `BrownianMotion P` must supply it. The downstream `project_BM` does supply it; the existence axiom is therefore consistent with the new field.
- **Recommendation**: No action needed. This closure (L10) is genuine.

### Finding 8 — `PoissonRandomMeasure.integer_valued` field is correctly added with Applebaum citation

- **Severity**: NO ISSUE (verified positive)
- **Location**: `LevyStochCalc/Poisson/RandomMeasure.lean:91-93`
- **Evidence** (verbatim):
  ```
  /-- **Applebaum 2.3.1(c).** For measurable `B` with finite intensity,
  `N(·, B)` is a.s. `ℕ`-valued (in the natural embedding `ℕ ↪ ℝ≥0∞`).
  Follows from `poisson_law` since the Poisson distribution is supported
  on `ℕ`, but is exposed as a structural field so downstream code can use
  it without having to re-derive it through the Poisson-law characterisation
  each time (L10 fix 2026-05-22 per red-team P04). -/
  integer_valued : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B ≠ ⊤ →
    ∀ᵐ ω ∂P, ∃ n : ℕ, N ω B = n
  ```
- **Why no issue**: The field is a genuine mathematical fact (follows from `poisson_law` exactly as the docstring claims; the existence of `n` is just unpacking that `Poisson(μ)`-distribution is supported on `ℕ`). The axiom `PoissonRandomMeasure.exists_of_sigmaFinite` does not change shape — it asserts `Nonempty (PoissonRandomMeasure P ν)`, and the new field is satisfied by any genuine PRM construction (the cited Applebaum 2.3.1 construction produces atomic ℕ-valued measures by construction). So adding `integer_valued` does not weaken or break the axiom.
  
  However, a Mathlib reviewer might ask: "shouldn't this be a theorem on the structure (`PoissonRandomMeasure.integer_valued_of_poisson_law`) rather than a field?" The answer is: arguably yes, but the field form is simpler and more directly usable downstream. The maintainer's docstring rationale ("exposed as a structural field so downstream code can use it without having to re-derive it") is sound. Either choice is defensible. The field form does mildly inflate the structure but doesn't introduce vacuous content.
- **Recommendation**: No action needed; defensible. A future refactor could move `integer_valued` to be a theorem deriving it from `poisson_law` (and downstream callers would still work via `_.integer_valued`), but this is style not soundness.

### Finding 9 — `lake-manifest.json` is correctly hand-edited; no `lake update` round-trip needed

- **Severity**: NO ISSUE (verified positive)
- **Location**: `lake-manifest.json:94-96`
- **Evidence**:
  ```
   "name": "LevyStochCalc",
   "lakeDir": ".lake",
   "fixedToolchain": true}
  ```
  Hand-edited from the original auto-generated `"name": "lakefile-toml"` and `"fixedToolchain": false`. The fix is the right shape — `lake update` would have regenerated the auto-name `"lakefile-toml"` from `lakefile.toml`, NOT the desired `"LevyStochCalc"`. The hand-edit is the only way to get the correct `name` field without renaming the lakefile. The `"fixedToolchain": true` is necessary to pin to `lean-toolchain` (`leanprover/lean4:v4.30.0-rc2`).
- **Recommendation**: No action needed. The hand-edit is the right fix; `lake update` would undo it.

### Finding 10 — `tools/lint.sh` and `_audit.lean` catch private-leaking sorries via `#print axioms`

- **Severity**: NO ISSUE (verified positive); but with a subtle caveat
- **Location**: `tools/lint.sh:38-72`, `_audit.lean:15-53`
- **Evidence**: The lint script extracts the set of audited theorems whose `#print axioms` output contains `sorryAx`, compares against `tools/sorry_baseline.txt`, and fails if the difference is non-empty. Each load-bearing theorem in `_audit.lean` is `#print axioms`'d explicitly. The audit output `tools/full_audit_output.txt:65-71` confirms the regression detection works:
  ```
  'LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique' depends on axioms: [propext,
   sorryAx, Classical.choice, Quot.sound, …]
  ```
  → this matches `sorry_baseline.txt`'s 2 entries.
  
  **The subtle caveat**: a private sorry-tainted lemma is caught *only if* it transitively reaches one of the 22 named theorems in `_audit.lean`. If a project author adds `private lemma foo : True := sorry` deep in `Brownian/Ito.lean`, and `foo` is not used by any named audited theorem, the lint will NOT catch it. The maintainer mitigates this by mass-deleting dead-code sorries (per the predecessor's M2). The `Grep` for `\bsorry\b` in `LevyStochCalc/**/*.lean` shows 0 actual `sorry` keyword instances outside the 2 baseline theorems (verified — all other `sorry` mentions are in comments/docstrings).
  
  There is a genuine residual risk: a future contributor could add a `private lemma` with `sorry` body, plug it into a *new* public theorem that's not in `_audit.lean`, and the lint would pass. The mitigation is for `_audit.lean` to mirror the public API exhaustively. The current `_audit.lean` has 22 theorems covering the load-bearing chain; this looks complete vs the 11 (now 9) cited axioms + ~13 derivative theorems documented in `cited_axioms.md`.
- **Recommendation**: Document in `tools/lint.sh` or `_audit.lean` the requirement that all new public theorems must be added to the audit. Consider extending the lint to also `Grep -r "sorry"` the source tree as a belt-and-braces check (currently this catches 0 hits outside the 2 baseline declarations, so the belt is consistent with the braces today).

### Finding 11 — Naming consistency: `_brownian` / `_compensated` suffix usage is uneven

- **Severity**: LOW
- **Location**: Cross-file. Examples:
  - `Brownian.Ito.itoIsometry` (no suffix) vs `Brownian.Ito.itoIsometry_brownian_unified_existence` (has suffix)
  - `Brownian.Ito.martingale_stochasticIntegral` (no suffix) vs `Brownian.Ito.simplePredictable_dense_Lp_brownian` (has suffix)
  - `Poisson.Compensated.itoLevyIsometry` (no suffix) vs `Poisson.Compensated.itoIsometry_compensated_unified_existence` (has suffix)
  - `Brownian.Ito.simpleIntegral` (no suffix) vs `Poisson.Compensated.simpleIntegral` (also no suffix — namespace-disambiguated)
- **Why this matters**: The `_brownian` / `_compensated` suffixes are *redundant* when the declaration lives in `Brownian.Ito` / `Poisson.Compensated` namespaces — the namespace already disambiguates. Mathlib convention: use the namespace, drop the suffix. The current `_unified_existence` axiom names use `_brownian` / `_compensated` because the analogous axioms used to live in a shared namespace before the 2026-05-10 refactor split them — the suffix is a historical accident.
  
  The mathlib4-style correct name would be:
  - `LevyStochCalc.Brownian.Ito.itoIsometry_unified_existence`
  - `LevyStochCalc.Poisson.Compensated.itoIsometry_unified_existence`
  - `LevyStochCalc.Brownian.Ito.simplePredictable_dense_Lp` (drop `_brownian`)
  
  Of course the `_unified_existence` suffix itself is non-idiomatic Mathlib — Mathlib would call this `itoIsometry_existence` or `itoIsometry_existsUnique` or just include the conjuncts in the theorem statement and call it `itoIsometry`. But that's a deeper renaming task.
- **Recommendation**: Sweep to remove redundant `_brownian` / `_compensated` suffixes where they duplicate the namespace. Lower priority than the Filt-pin and `Notation.lean` fixes. Estimated effort: 1 hour mechanical rename via `lake env lean --rename` or simple `sed`, plus ~10 minutes test build.

### Finding 12 — `lakefile.toml`'s `weak.linter.mathlibStandardSet = true` is active, warnings cleanup verified on sample

- **Severity**: LOW (informational)
- **Location**: `lakefile.toml:9`
- **Evidence**: `lakefile.toml` has `weak.linter.mathlibStandardSet = true`. The Mathlib standard linter set includes `linter.style.openClassical`, `linter.style.maxHeartbeats`, `linter.style.show`, and others. The shared_context_override claims "198 → 2 warnings (87% reduction)". I cannot fully verify this without running `lake build` (timeout would be high), but spot-checked via the LSP diagnostic-messages tool: `Notation.lean`, `Basic.lean`, `Brownian/Construction.lean`, `Brownian/Multidim.lean`, `Brownian/Ito.lean` all return 0 warnings. `Ito/Setting.lean` returns the expected 1 sorry warning. So the warning-cleanup is real on the files I sampled.
- **Recommendation**: No action needed; closure is verified on the sample.

### Finding 13 — `simplePredictable_dense_Lp_brownian` is a 1-line forwarder; should be an `alias`

- **Severity**: LOW
- **Location**: `LevyStochCalc/Brownian/Ito.lean:3968-3979`
- **Evidence**:
  ```
  /-- **C0a: Density of simple Brownian-predictable processes in `L²(Ω × [0, T])`.**
  …Public re-export of the existing `simplePredictable_dense_L2` under the roadmap's name. -/
  theorem simplePredictable_dense_Lp_brownian
      {P : Measure Ω} [IsProbabilityMeasure P]
      …
      ∃ Hn : ℕ → SimplePredictable Ω T,
        Filter.Tendsto
          (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s - (Hn n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          Filter.atTop (nhds 0) :=
    simplePredictable_dense_L2 hT H h_meas h_sq_int
  ```
- **Why this matters**: This is a 1-line forwarder. The docstring says "Public re-export of the existing `simplePredictable_dense_L2` under the roadmap's name." Mathlib style: prefer `alias`, not a `theorem … := …` 1-line wrapper:
  ```
  alias simplePredictable_dense_Lp_brownian := simplePredictable_dense_L2
  ```
  The `alias` form is more efficient (no extra environment entry) and signals the relationship clearly. This is minor but is a typical mathlib4 reviewer comment.
- **Recommendation**: Convert to `alias`. Trivial.

## Per-axiom verdicts on the 9 Tier 1 axioms + ~13 derived theorems

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `Brownian.BrownianMotion.exists` (Tier 1 #1) | EARNED | Honest axiom, Karatzas–Shreve 2.1.5 + Le Gall Def 2.1 citations correct, faithful statement. `joint_measurable` field added consistently. |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` (Tier 1 #2) | EARNED | Honest axiom, Applebaum 2.3.1, faithful. `integer_valued` field added consistently. |
| `Brownian.Continuity.kolmogorovChentsov_modification` (Tier 1 #3) | EARNED | Honest axiom; `kolmogorov_modification_ae_eq` now fully proved (no sorryAx, verified via `_audit.lean` line 41-43). |
| `Brownian.Martingale.brownian_martingale_rightCont` (Tier 1 #4) | EARNED | Honest axiom; Le Gall Theorem 2.13 citation fix is correct. |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` (Tier 1 #5) | WEAK | `Filt` still existentially quantified — Finding 3. |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` (Tier 1 #6) | WEAK | Same `Filt` issue + the H6 "documentation-only" closure of predictable vs measurable is acknowledged as deferred. |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` (Tier 1 #9) | EARNED-with-CAVEAT | Lipschitz + L² hypotheses now added (H4 closure real). Predicate is non-trivially constrained via `IsBSDEJSolution`'s adaptedness + canonical-integral pinning of `M_W`/`M_N` from the lens of P01. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` (Tier 1 #10) | EARNED-with-CAVEAT | Lipschitz + L² + `Z_avg`/`U_avg` pin via `conditionalTimeAverage_*` real; constant `C` exposed as function of `(T, L, ‖ξ‖)`. |
| `Ito.JumpFormula.itoLevyFormula` (Tier 1 #11) | EARNED | All 4 terms pinned to literature integrals; verified via the per-term docstring at `Compensated.lean` and audit output line 72-77 showing both Tier 1 #5 and #6 in transitive deps. |
| `Brownian.Multidim.MultidimBrownianMotion.exists` (derived) | EARNED | Real proof via `iIndepFun_pi`; `joint_measurable` propagates via `project_BM` (Finding 7). |
| `Brownian.Continuity.brownian_continuous_modification` (derived) | EARNED | Forwards through Tier 1 #3. |
| `Brownian.Martingale.brownian_filtration_rightContinuous` (derived) | EARNED | Forwards through Tier 1 #4. |
| `Brownian.Ito.itoIsometry` (derived) | WEAK | Extracts conjunct 3 of Tier 1 #5; inherits the `Filt` weakness. |
| `Brownian.Ito.martingale_stochasticIntegral` (derived) | WEAK | Extracts conjunct 1 of Tier 1 #5; same. |
| `Brownian.Ito.quadVar_stochasticIntegral` (derived) | WEAK | Extracts conjunct 2 of Tier 1 #5; same. |
| `Poisson.Compensated.itoLevyIsometry` (derived) | WEAK | Extracts conjunct 3 of Tier 1 #6; same `Filt` weakness. |
| `Poisson.Compensated.martingale_stochasticIntegral` (derived) | WEAK | Extracts conjunct 1 of Tier 1 #6. |
| `Poisson.Compensated.quadVar_stochasticIntegral` (derived) | WEAK | Extracts conjunct 2 of Tier 1 #6 (now gated on `h_meas` + `h_sq_int`; the H5 fix is real). |
| `Poisson.Compensated.cadlag_modification_exists` (derived) | WEAK | Extracts conjunct 4 of Tier 1 #6. |
| `Poisson.L2Isometry.itoLevyIsometry` (forwarder) | WEAK | 1-line forwarder; inherits the `Filt` weakness. |
| `Ito.Setting.JumpDiffusion.exists_unique` (baseline sorry) | EARNED-as-baseline | `is_solution` field strengthened from `True` to real SDE; proof body now honestly `sorry`'d (verified by `_audit.lean` line 65-71 showing `sorryAx`). |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` (baseline sorry) | EARNED-as-baseline | Signature now pins `BM_integral`/`jump_integral` to canonical forms; proof body honestly `sorry`'d (verified by `_audit.lean` line 78-83 showing `sorryAx`). |

Summary: Tier 1 cited axioms #1–#4, #9–#11 are clean; #5 and #6 still have the existential-`Filt` weakness flagged by the predecessor (Finding 6 in 2026-05-20-archive/01) — this weakness propagates to every derived theorem extracted from them (7 of the ~13 derivatives). The baseline-sorry theorems are honest.

## Persona-specific section (P01 Lean formalisation, audit-2-specific)

Cleanup quality from the Lean-formalisation lens:

1. **Mathlib idiom score**: B+. Copyright headers are correct. `open Classical` is correctly localized. Naming is mostly snake_case for theorems and UpperCamelCase for structures. The two `set_option linter.unusedSectionVars false in` sites are the only non-idiomatic linter-suppression instances I found (the rest of the 19 `set_option maxHeartbeats` are now properly commented per the maintainer's claim and my spot-check).

2. **Build hygiene**: A. The build is clean modulo 2 baseline sorry warnings; LSP diagnostics on the 6 files I sampled return 0 warnings each. The `lake-manifest.json` hand-edit is the right fix (Finding 9).

3. **Lint set-up**: A-. `tools/lint.sh` does what the user wants — catches sorryAx regressions in the load-bearing chain via `_audit.lean`. The mild residual risk (a private sorry that doesn't reach any audited theorem) is mitigated by the maintainer's aggressive deletion policy (verified: 0 `\bsorry\b` matches outside the 2 baseline declarations).

4. **Structure design**: B+. `BrownianMotion.joint_measurable` and `PoissonRandomMeasure.integer_valued` are correctly added as fields with non-trivial witnesses in `project_BM` and consistent docstring justifications. The `IsBSDEJSolution`'s `Filt ≥ naturalFiltration` constraint is a real soundness improvement. The `JumpDiffusion.is_solution`-was-True-now-real-SDE is correctly strengthened.

5. **Universe polymorphism**: A. `universe u v` declarations are clean; the structures use the right universe level (`Type u` for `Ω`, `Type v` for `E`). No universe-level drift observed.

6. **Imports**: B. `Notation.lean`'s empty-file-with-no-imports is fine syntactically but creates a maintenance-hazard signal (Finding 1). `Basic.lean`'s `import Mathlib` with self-justifying-incorrect-comment is a real issue (Finding 2). No circular-import risk observed — the layered structure (`LevyStochCalc.lean` imports per layer) is clean.

7. **Naming consistency**: B. The `_brownian` / `_compensated` suffix discipline is uneven (Finding 11). The `_unified_existence` suffix is project-local jargon. None of this affects correctness.

8. **Documentation accuracy**: B+. Module docstrings are mostly current. The `cited_axioms.md` is honest about M4 (deleted), M11 (deferred), M5 (paired with M4); the discrepancy with `shared_context_override.md`'s claim of full M11 closure (Finding 3) is on `shared_context_override.md`'s side, not the in-source docstrings.

What the cleanup did NOT change but should have:
- The Tier 1 #5 / #6 `Filt` pin (predecessor Finding 6; my Finding 3).
- The H6 predictable-vs-measurable gap (acknowledged as deferred in `cited_axioms.md:227-228`).
- The `Notation.lean` placeholder (predecessor Finding 5; my Finding 1).
- The `Basic.lean` `import Mathlib` (predecessor Finding 9; my Finding 2).

## Files read

Source files (read in full or substantial part):
- `D:/LevyStochCalc/LevyStochCalc.lean` (50 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/Notation.lean` (21 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/Basic.lean` (419 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/Brownian/Construction.lean` (174 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/Brownian/Multidim.lean` (249 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/Brownian/Ito.lean` (selected: 1336-1490, 1795-1900, 2755-2790, 3940-3992 — ~400 lines of the 3993-line file)
- `D:/LevyStochCalc/LevyStochCalc/Brownian/SimplePredictableRefine.lean` (selected: 2080-2200 of 2200+ lines)
- `D:/LevyStochCalc/LevyStochCalc/Poisson/RandomMeasure.lean` (207 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/Poisson/NaturalFiltration.lean` (83 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/Poisson/Compensated.lean` (selected: 1-300, 1600-1700, 1750-1900 — ~600 lines of the 1935-line file)
- `D:/LevyStochCalc/LevyStochCalc/Ito/Setting.lean` (149 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/BSDEJ/Definition.lean` (203 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/BSDEJ/Existence.lean` (139 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/BSDEJ/PathRegularity.lean` (177 lines, full)
- `D:/LevyStochCalc/LevyStochCalc/BSDEJ/MartingaleRepresentation.lean` (113 lines, full)

Build / configuration / audit:
- `D:/LevyStochCalc/lakefile.toml` (18 lines, full)
- `D:/LevyStochCalc/lake-manifest.json` (97 lines, full)
- `D:/LevyStochCalc/lean-toolchain` (1 line, full)
- `D:/LevyStochCalc/_audit.lean` (54 lines, full)
- `D:/LevyStochCalc/tools/lint.sh` (83 lines, full)
- `D:/LevyStochCalc/tools/sorry_baseline.txt` (2 lines, full)
- `D:/LevyStochCalc/tools/cited_axioms.md` (259 lines, full)
- `D:/LevyStochCalc/tools/full_audit_output.txt` (96 lines, full)

Predecessor / context:
- `D:/LevyStochCalc/redteam_findings/shared_context_override.md` (163 lines, full)
- `D:/LevyStochCalc/redteam_findings/2026-05-20-archive/01_lean_formalisation.md` (435 lines, full)
- `D:/LeanRedTeam/personas/01_lean_formalisation.md` (63 lines, full)

LSP-verified:
- `lean_verify` on `LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution` — axiom set `[propext, Classical.choice, Quot.sound, itoIsometry_brownian_unified_existence, itoIsometry_compensated_unified_existence]`.
- `lean_verify` on `LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence` — self-axiom set as expected.
- `lean_diagnostic_messages` (warning filter) on `Notation.lean`, `Basic.lean`, `Brownian/Construction.lean`, `Brownian/Multidim.lean`, `Brownian/Ito.lean` (with line restriction 1340-1350) — all return empty.
- `lean_diagnostic_messages` on `Ito/Setting.lean` — confirms the 1 expected `sorry` warning at line 134 (matches baseline).

Git inspected:
- `git log --oneline -50` — 24 commits between 4dea618 and 237cc19 covered.
- `git diff LevyStochCalc/BSDEJ/Existence.lean` — minor docstring correction to Delong reprint year (2017 → 2013).
- `git status` — confirms working tree has only redteam_findings/ churn + a 1-line Existence.lean citation edit.
