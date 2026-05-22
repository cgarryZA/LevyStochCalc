# Red Team Audit: Pure Mathematician

**Auditor lens**: Research mathematician — measure theory, probability, functional analysis. Verdict on whether each Lean definition / predicate matches the standard statement in Karatzas-Shreve, Le Gall, Applebaum, Revuz-Yor, Ikeda-Watanabe.
**Date**: 2026-05-20
**Coverage**: 13 files read in full (every file housing a Tier 1 axiom or the predicates / structures they consume), 4 files skimmed (`Basic.lean`, `Notation.lean`, `Poisson/Martingale.lean`, `Poisson/NaturalFiltration.lean`), 2 files (`tools/full_audit.lean`, `tools/full_audit_output.txt`) used as cross-reference. Did not exhaustively read the ~4000 lines of bottom-up simple-integrand machinery in `Brownian/Ito.lean` / `Brownian/SimplePredictableRefine.lean` / `Poisson/Compensated.lean` — instead I read the signatures, the cited-axiom statements, and the predicate definitions, which is where a pure-math audit lives.

## Executive summary (≤ 3 sentences)

The 2026-05-11 recursive audit "demoted" `itoLevyFormula` from a trivial-witness `theorem` to an `axiom`, but **left the underlying statement logically trivial** — the axiom claims only `∃ (a, b, c, d : Ω → ℝ), u(T,X_T) − u(0,X_0) = a + b + c + d a.s.`, which is satisfied by ANY four functions summing to the change, with no requirement that they correspond to the four literature integral terms; the demotion was cosmetic and did not fix the actual logical hole. The strengthened `IsBSDEJSolution` predicate (also from 2026-05-11) is non-vacuous for the constant `Y = 0`, but is **still strictly weaker than the Tang-Li solution-space predicate** in three concrete ways (no adaptedness / predictability on `(Y, Z, U)`; `M_W` not pinned to `∫ Z dW`; `M_N` pinned to a `Classical.choose`-defined `stochasticIntegral` whose own defining axiom is satisfied vacuously for non-predictable `U`), and the cited-axiom `continuousBSDEJ_exists_unique` it consumes **omits the Lipschitz / L²-terminal hypotheses required by Tang-Li** while asserting an existence + uniqueness conclusion — meaning the Lean axiom claims more than the cited theorem. Adding to this, `JumpDiffusion.exists_unique` is a public `theorem` whose proof body picks the constant path `X t ω = x₀` (allowed because the structure's `is_solution : True`), and `jacodYor_representation` is a public `theorem` whose proof picks `Z = U = BM_integral = 0` and stuffs `ξ − 𝔼[ξ]` into the jump integral — both are exactly the trivial-witness pattern the recursive audit was supposed to catch.

## Top findings (ranked by severity, highest first)

### Finding 1 — `itoLevyFormula` axiom is logically trivial as stated (the 2026-05-11 "demotion" did not fix the underlying defect)
- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/Ito/JumpFormula.lean:90-105`
- **Evidence** (verbatim):
  ```lean
  axiom itoLevyFormula
      {P : Measure Ω} [IsProbabilityMeasure P]
      {ν : Measure E} [SigmaFinite ν]
      {n d : ℕ}
      (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
      (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
      (x₀ : Fin n → ℝ)
      (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
      (u : ℝ → (Fin n → ℝ) → ℝ)
      (T : ℝ) (_hT : 0 < T) :
      -- Exists four processes giving the integral-form decomposition.
      ∃ (drift_term diff_mart jump_mart comp_drift : Ω → ℝ),
        (∀ᵐ ω ∂P,
          u T (X.X T ω) - u 0 (X.X 0 ω) =
            drift_term ω + diff_mart ω + jump_mart ω + comp_drift ω)
  ```
- **Why this matters**: The cited theorem (Applebaum 2009 Thm 4.4.7) asserts that the four terms have a SPECIFIC integral form: `drift_term = ∫_0^T (∂_t u + 𝓛u)(s, X_{s-}) ds`, `diff_mart = ∫ ∇uᵀσ dW`, etc. The Lean axiom asserts only that there EXIST four `Ω → ℝ` functions summing (almost surely) to the change `u T (X.X T ω) − u 0 (X.X 0 ω)`. For ANY `(u, X)`, picking `drift_term ω := u T (X.X T ω) − u 0 (X.X 0 ω)`, `diff_mart = jump_mart = comp_drift = 0` satisfies the conclusion — this is the EXACT trivial-witness pattern (`⟨change, 0, 0, 0⟩; simp`) that the recursive audit identified. The audit "demoted" the declaration from `theorem` to `axiom`, which changes nothing about the statement's content — a trivially-true axiom is no better than a trivially-proved theorem. The cited-axioms inventory (`tools/cited_axioms.md` line 89-95) describes the axiom as if it asserted the literature decomposition, but the Lean statement does not. A Mathlib reviewer reading this axiom would not be deceived only because the docstring honestly admits the demotion; a less-careful reader trusting the headline name would be.

  Compounding this: the `JumpDiffusion` structure (`Ito/Setting.lean:50-72`) consumed by `X` has `is_solution : True`, so `X` need not even be a solution to the SDE — see Finding 3.

- **Recommendation**: Either (a) rewrite the axiom to pin each of the four terms to its literature integral form (introducing the `Brownian.SimplePredictableRefine.stochasticIntegral` and `Poisson.Compensated.stochasticIntegral` calls plus the Lévy generator `𝓛u`), or (b) state the axiom as a quantitative L² / moment claim that constrains the four terms beyond "they sum to the change". The current `∃ a b c d, sum = change` form is mathematically vacuous and should not be presented as the Itô-Lévy formula.

### Finding 2 — `IsBSDEJSolution` predicate has no adaptedness / predictability condition on `(Y, Z, U)`, breaking the Tang-Li solution-space `S² × H² × H²_N`
- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:91-133`
- **Evidence** (verbatim, the conjuncts of the predicate):
  ```lean
  def IsBSDEJSolution
      … (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) (T : ℝ) : Prop :=
    Measurable (Function.uncurry Y)
      ∧ (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
      ∧ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
      ∧ (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
      …
  ```
  Note there is no `progMeas` / `adapted` / `predictable` condition on `Z`, no measurability requirement on `Z` or `U`, and only joint measurability (not adaptedness) on `Y`.

- **Why this matters**: The Tang-Li 1994 / Pardoux-Răşcanu 2014 / Gnoatto 2025 solution space is `S² × H² × H²_N`, where `S²` is the space of càdlàg ADAPTED processes with L²-sup-norm and `H²`, `H²_N` are spaces of **predictable** (i.e., ℱ_{s-}-measurable) square-integrable processes. Web search confirms this directly: "the solution consists of an adapted càdlàg process Y, a locally square-integrable predictable process Z and a locally p-integrable predictable random field U" (consensus from multiple modern BSDE-with-jumps references). Without predictability of `Z`, the stochastic integral `∫_0^t Z_s dW_s` is not even defined in classical theory (predictability is exactly what makes the simple-integrand approximation work). Without adaptedness of `Y`, the value `Y_t` is not measurable with respect to the information available at time `t`, which is the whole point of a "backward" SDE.

  The strengthening of 2026-05-11 attempted to fix the per-`(t, ω)` existential `∃ BM_term jump_term : ℝ` that made the original predicate vacuous (see module docstring at lines 22-65). The new outer existential `∃ M_W M_N : ℝ → Ω → ℝ` is a genuine improvement (constant `Y = 0` no longer satisfies the predicate for generic `(g, f, X)`). But the strengthening did NOT add adaptedness / predictability of `(Y, Z, U)`, and the predicate is therefore still strictly weaker than the literature's `S² × H² × H²_N`.

- **Recommendation**: Add the literature conditions: `Y` adapted to a càdlàg filtration containing `σ(W, N)`, `Z` and `U` predictable (= adapted to the left-limit filtration, or stronglyMeasurable for the progressive σ-algebra). Mathlib provides `MeasureTheory.Adapted`, `MeasureTheory.Filtration.predictableσ`, and `MeasureTheory.ProgMeasurable` — wire these in. Without these, the axiom `continuousBSDEJ_exists_unique` does not state the Tang-Li theorem.

### Finding 3 — `JumpDiffusion.exists_unique` is a trivial-witness theorem (proof picks constant path `X = x₀`, allowed by `is_solution : True`); name is also a misnomer
- **Severity**: HIGH
- **Location**: `LevyStochCalc/Ito/Setting.lean:50-72` (structure) and `85-112` (theorem)
- **Evidence** (verbatim):

  Structure (lines 50-72):
  ```lean
  structure JumpDiffusion … where
    X : ℝ → Ω → (Fin n → ℝ)
    measurable_path : Measurable (Function.uncurry X)
    initial_value : ∀ᵐ ω ∂P, X 0 ω = x₀
    sup_L2 : ∀ T : ℝ, 0 < T → ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X t.1 ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
    is_solution : True
  ```

  Theorem (lines 85-112):
  ```lean
  theorem JumpDiffusion.exists_unique
      … (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
      (coeffs : JumpDiffusionCoeffs n d E)
      (x₀ : Fin n → ℝ) :
      Nonempty (JumpDiffusion W N coeffs x₀) := by
    refine ⟨{
      X := fun _ _ => x₀
      measurable_path := measurable_const
      initial_value := Filter.Eventually.of_forall (fun _ => rfl)
      sup_L2 := ?_
      is_solution := trivial
    }⟩
    intro T hT
    haveI : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, by simp [le_of_lt hT]⟩⟩
    have h_const : … := by funext ω; apply iSup_const
    rw [h_const, MeasureTheory.lintegral_const]
    exact ENNReal.mul_lt_top (ENNReal.sum_lt_top.mpr (fun _ _ => by exact ENNReal.coe_lt_top))
      (MeasureTheory.measure_lt_top _ _)
  ```

- **Why this matters**:
  1. The structure does NOT enforce the SDE. `is_solution : True` is the same vacuous bypass as the original `IsBSDEJSolution`'s `∃ BM_term jump_term : ℝ` per-`(t, ω)` existential. A `JumpDiffusion W N coeffs x₀` is just any measurable adapted process starting at `x₀` with L²-sup norm bound — it has no obligation to satisfy `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫ γ Ñ`.
  2. The witness `X t ω = x₀` (constant path) does not depend on `W`, `N`, or `coeffs` at all. This is precisely the `⟨0, 0, 0, change⟩` trivial-witness pattern, just in a different form: `⟨x₀, ⟨measurable_const, …, trivial⟩⟩`.
  3. The theorem name `exists_unique` is a misnomer. The conclusion is `Nonempty (JumpDiffusion W N coeffs x₀)` — propositional truncation of EXISTENCE, no uniqueness claim. Applebaum 2009 Theorem 6.2.9 (the cited reference, see line 78) asserts existence AND uniqueness of the solution under Lipschitz hypotheses. The Lean theorem asserts only existence (vacuously).
  4. The Lipschitz hypotheses on `(μ, σ, γ)` are not parameters of the theorem at all. Applebaum 6.2.9 requires Lipschitz; the Lean signature does not.

  This is the exact pattern the recursive audit was supposed to catch. The audit found `itoLevyFormula`'s trivial proof body and demoted it, but `JumpDiffusion.exists_unique` is the same pattern in a slightly different syntactic form and was missed.

- **Recommendation**: Strengthen `JumpDiffusion.is_solution` to assert the actual SDE `X_t = x₀ + ∫_0^t μ ds + ∫_0^t σ dW + ∫_0^t ∫ γ Ñ` a.s. for every `t`, using `Brownian.SimplePredictableRefine.stochasticIntegral` and `Poisson.Compensated.stochasticIntegral`. Rename the theorem `JumpDiffusion.exists_unique` to `JumpDiffusion.exists` (since uniqueness is not claimed) and either prove the actual existence under Lipschitz hypotheses or demote it to a cited axiom (Applebaum 6.2.9) with the hypotheses spelled out.

### Finding 4 — `jacodYor_representation` is a trivial-witness theorem (proof picks `Z = U = BM_integral = 0`, stuffs everything into `jump_integral`)
- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:55-84`
- **Evidence** (verbatim):
  ```lean
  theorem jacodYor_representation
      … (T : ℝ) (_hT : 0 < T)
      (ξ : Ω → ℝ)
      (_h_meas : Measurable ξ)
      (_h_sq_int : ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
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
    · exact measurable_const
    · exact measurable_const
    · simp
    · simp
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      show ξ ω = (∫ ω', ξ ω' ∂P) + 0 + (ξ ω - ∫ ω', ξ ω' ∂P)
      ring
  ```
- **Why this matters**: The Jacod-Yor / Kunita-Watanabe theorem says: every L²-martingale on `σ(W, Ñ)` decomposes as `M_t = M_0 + ∫_0^t Z_s dW_s + ∫_0^t ∫_E U_s(e) Ñ(ds, de)` with `Z, U` predictable and square-integrable AND with the integrals being the actual stochastic integrals against `W` and `Ñ`. The Lean theorem statement does NOT require `BM_integral = ∫ Z dW` or `jump_integral = ∫∫ U Ñ` — they are independent existential variables. The proof picks `Z = 0`, `U = 0`, `BM_integral = 0`, `jump_integral = ξ − 𝔼[ξ]`. The conclusion holds by `ξ = 𝔼[ξ] + 0 + (ξ − 𝔼[ξ])` (a trivial arithmetic identity, dispatched by `ring`).

  This is the SAME pattern as `itoLevyFormula` and `JumpDiffusion.exists_unique`. The four existentially-quantified "integrals" are not pinned to any actual integral; they are free `Ω → ℝ` functions. The recursive audit missed this because the proof is dressed up with five `?_` subgoals (one per existential field), and the `_h_meas`, `_h_sq_int` hypotheses are unused (underscore-prefixed, which Lean treats as anonymous).

  Worse: the docstring (line 30-32) claims "expressed as the existence of `(Z, U)` with the required measurability and `eLpNorm` bounds" — but the proof picks `Z = U = 0`, which satisfies these trivially.

  This theorem is currently not USED in the body of any `continuousBSDEJ_exists_unique` proof (that's an axiom), but it appears in `tools/full_audit.lean:72` as a public theorem whose axiom set is `[propext, Classical.choice, Quot.sound]` — i.e., it appears axiom-clean in the audit. The audit metric is fooled.

- **Recommendation**: Either (a) pin `BM_integral` to `LevyStochCalc.Brownian.SimplePredictableRefine.stochasticIntegral` applied to `Z` and `jump_integral` to `LevyStochCalc.Poisson.Compensated.stochasticIntegral` applied to `U`, and demote the result to an `axiom` with the Jacod 1976 citation, or (b) require the conjunction with the L² isometry identities `‖BM_integral‖²_{L²(P)} = ‖Z‖²_{H²}` and `‖jump_integral‖²_{L²(P)} = ‖U‖²_{H²_N}` — under those identities, `BM_integral = 0` and `jump_integral = ξ − 𝔼[ξ]` no longer satisfy unless `ξ = 𝔼[ξ]` a.s.

### Finding 5 — `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` omit the Lipschitz / L²-terminal hypotheses required by their cited Tang-Li / Bouchard-Elie-Touzi statements
- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/Existence.lean:113-126`, `LevyStochCalc/BSDEJ/PathRegularity.lean:111-139`
- **Evidence** (verbatim):
  ```lean
  axiom continuousBSDEJ_exists_unique
      … (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
      (bsdej : BSDEJData n d E)
      (X : ℝ → Ω → (Fin n → ℝ))
      (T : ℝ) (_hT : 0 < T) :
      ∃ (Y : …) (Z : …) (U : …), IsBSDEJSolution W N bsdej X Y Z U T ∧ …
  ```
  Note the signature: only `(W, N, bsdej, X, T, _hT : 0 < T)`. **No Lipschitz hypothesis on `bsdej.f`**, **no L²-integrability of `bsdej.g (X T)`**, **no measurability of `X`**, **no Lipschitz / linear-growth condition on `bsdej.g` or `X`**.

  The docstring (line 95) says: "Under Lipschitz hypotheses on `(f, g)` and L² integrability of the terminal data, the BSDEJ has a unique adapted solution triple `(Y, Z, U) ∈ S² × H² × H²_N`." — but those hypotheses are not in the Lean signature.

  Same defect in `bsdej_path_regularity` (Existence.lean cousin); see lines 111-139 — `axiom bsdej_path_regularity … (W) (N) (bsdej) (X) (T) (_hT : 0 < T) : …` with no Lipschitz, no L².

- **Why this matters**: Tang-Li 1994 Theorem 3.1 requires (i) Lipschitz `f` in `(y, z, u)` uniformly in `(s, x)`, (ii) measurable terminal `g(X_T)` in `L²(Ω, ℱ_T, P)`. For non-Lipschitz `f`, neither existence nor uniqueness holds in general — the Picard contraction fails. By asserting existence + uniqueness for ARBITRARY `bsdej : BSDEJData n d E` (i.e., for any measurable function `f` and any function `g`), the axiom claims more than the cited theorem. In particular, the axiom is mathematically FALSE: counterexamples exist with non-Lipschitz `f` for which no `L²`-solution exists, yet the axiom asserts one does.

  This is not a "weakening" — it's a STRENGTHENING beyond the literature. The Lean axiom asserts a strictly stronger statement than Tang-Li and is therefore inconsistent with what's claimed in the docstring.

  Combined with Finding 2 (no predictability of `Z, U`), the situation is: the axiom asserts a generic existence claim under hypothesis-free conditions, with a weakened predicate. Whether the predicate is satisfiable for non-Lipschitz `f` is unclear — but the axiom presents this as a derived form of Tang-Li, which it is not.

- **Recommendation**: Add the hypotheses to the axiom signature: `(hL : 0 ≤ L)` + `(h_Lip : Lipschitz bsdej ν L)` (already defined at line 67-73), `(h_meas_X : Measurable (Function.uncurry X))`, `(h_terminal_L2 : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊)² ∂P < ⊤)`, plus the linear-growth bound on `f` at `(y, z, u) = 0` integrated over `s` (this is the standard Tang-Li hypothesis). Same for `bsdej_path_regularity`. After this fix, the docstring will match the signature.

### Finding 6 — `IsBSDEJSolution`'s M_W condition only requires L² isometry, not pinning to `∫ Z dW` — multiple distinct `Y'` can satisfy the predicate, defeating uniqueness
- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:114-118`
- **Evidence** (verbatim, the M_W condition):
  ```lean
  -- M_W satisfies the multidim Brownian L²-Itô isometry against Z:
  (∀ T', 0 < T' →
    ∫⁻ ω, (‖M_W T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
  ```
  The module docstring (lines 60-63) acknowledges the slack: "The strengthened predicate is still slightly weaker than the literature (it doesn't pin `M_W` to be literally `∫ Z · dW`, only an isometric martingale), but it is non-vacuous: the literature solution satisfies it, and trivial constant `Y` does not."

- **Why this matters**: The L²-isometry condition `𝔼[‖M_W(T')‖²] = 𝔼[∫_0^{T'} ‖Z_s‖² ds]` constrains M_W only in its **scalar L² norm**. Multiple distinct martingales can satisfy the same scalar L² norm. Concretely: let `M_W^{(lit)} := ∫ Z dW` be the literature stochastic integral. Construct `M_W^{(alt)}(T') := σ(T') · B'(T')`, where `B'` is a Brownian motion independent of `(Y, Z, U, W, N)` (constructible via a product space) and `σ(T') := sqrt(𝔼[∫_0^{T'} ‖Z‖² ds] / T')`. Then `𝔼[(M_W^{(alt)}(T'))²] = σ(T')² · T' = 𝔼[∫_0^{T'} ‖Z‖² ds]`, satisfying the isometry. `M_W^{(alt)}` is a martingale (Brownian motion scaled by a deterministic function). Hence `M_W^{(alt)}` satisfies the predicate's M_W conditions.

  Now substitute into the BSDEJ equation at `t = 0`:
    `Y 0 ω = g(X_T) + ∫_0^T f(s, X_s, Y_s, Z_s, U_s) ds - (M_W^{(alt)}(T) - 0) - (M_N(T) - 0)`.

  For the literature solution `Y^{(lit)}, Z, U` and `M_W^{(alt)} ≠ M_W^{(lit)}`, the equation becomes `Y^{(lit)}(0, ω) = (literature RHS at t=0) + (M_W^{(lit)}(T) - M_W^{(alt)}(T))`, which is a NEW random variable depending on `B'`. To restore the equation we need a different `Y'` such that this holds. With Lipschitz `f`, the Picard iteration with the modified M_W converges to a different fixed point `Y' ≠ Y^{(lit)}`. So **the predicate admits multiple Y'**, and the uniqueness clause `∀ Y', IsBSDEJSolution → Y = Y' a.s.` is FALSE under this construction.

  The docstring's "sufficient for the cited axioms `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` to assert substantive content" claim is therefore questionable: the predicate is non-vacuous (Finding 2-3 give that), but the cited axiom's uniqueness conclusion is not consistent with the weakened predicate.

- **Recommendation**: Pin `M_W` to the literature integral. Either (a) introduce a `MultidimBrownian.stochasticIntegral W (h_progMeas) Z T'` primitive (mirror of `Compensated.stochasticIntegral`) and pin `M_W T' = MultidimBrownian.stochasticIntegral W h_progMeas Z T'`; or (b) require the SCALAR-PRODUCT isometry `𝔼[M_W(T') · ∫_0^{T'} ⟨H, Z⟩ dW_s] = 𝔼[∫_0^{T'} ⟨H, Z⟩ ds]` for all bounded `H`, which is a stronger characterization. Until M_W is pinned to a canonical functional of Z, the uniqueness clause cannot be soundly claimed.

### Finding 7 — `IsBSDEJSolution`'s M_N pin defers to `Compensated.stochasticIntegral`, whose own cited axiom is vacuously satisfiable for non-predictable U
- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:119-123` (the pin), `LevyStochCalc/Poisson/Compensated.lean:2748-2767` (the cited axiom), `LevyStochCalc/Poisson/Compensated.lean:2776-2782` (the definition)
- **Evidence** (verbatim, the M_N pin):
  ```lean
  -- M_N is pinned to the canonical compensated-Poisson L² integral of U:
  (∀ T' : ℝ, ∀ᵐ ω ∂P,
    M_N T' ω =
      LevyStochCalc.Poisson.Compensated.stochasticIntegral N
        (fun ω' s e => U s ω' e) T' ω) ∧
  ```
  The definition (Compensated.lean:2776-2782):
  ```lean
  noncomputable def stochasticIntegral
      (N : PoissonRandomMeasure P ν)
      (φ : Ω → ℝ → E → ℝ)
      (T : ℝ) : Ω → ℝ :=
    (Classical.choose (itoIsometry_compensated_unified_existence N φ)) T
  ```
  The cited axiom (Compensated.lean:2748-2767):
  ```lean
  axiom itoIsometry_compensated_unified_existence
      (N : PoissonRandomMeasure P ν)
      (φ : Ω → ℝ → E → ℝ) :
      ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
        MeasureTheory.Martingale F Filt P ∧
        MeasureTheory.Martingale
          (fun t ω => (F t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν) Filt P ∧
        (∀ T, 0 < T → Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2) →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ →
          ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
            ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) ∧
        (∀ᵐ ω ∂P, ∀ t : ℝ, …)
  ```

- **Why this matters**: The cited axiom takes `φ : Ω → ℝ → E → ℝ` as bare data — no measurability hypothesis, no predictability, no integrability. The existence claim says: for EVERY `φ`, there's an `F` and `Filt` satisfying the four conjuncts. The L²-isometry conjunct is conditional on `Measurable (fun p => φ p.1 p.2.1 p.2.2)` AND `∫⁻ ω, ∫⁻ s, ∫⁻ e, ‖φ‖² < ⊤` — so for non-measurable / non-square-integrable φ, the isometry is vacuous (its hypothesis is false, hence the implication is true).

  Crucially: for non-predictable `φ`, the L²-Itô-Lévy integral is not defined in classical theory (Applebaum 2009 §4.2 explicitly requires predictability). Yet the Lean axiom asserts existence of `F` for arbitrary `φ`. The cited Applebaum 4.2.3 + 4.2.4 results are about predictable integrands. **The Lean axiom is logically broader than the cited theorem**.

  Take `φ ≡ 0` (the zero integrand). The axiom requires `∃ F, ∃ Filt, F martingale, F² − 0 = F² martingale, isometry (trivial), F càdlàg`. Witness: `F ≡ 0`, Filt = anything. Then `stochasticIntegral N (fun ω' s e => 0) T' = Classical.choose(...) T' = 0` (consistent choice). So `M_N T' = 0` for `U = 0`.

  Take a non-predictable `U`. The axiom still asserts existence of F (since the hypotheses on isometry are not constraints on F's existence, only on its norm). The `Classical.choose` could pick `F = 0` (martingale ✓, F² − ∫φ² ds = -∫φ² ds is a martingale iff ∫φ² ds is constant in t, which fails generically — so F = 0 only works if ν(supp φ²(s, ·)) = 0). For generic non-predictable U, the existence claim still holds (by some F), but the F may not be the "true" integral.

  The downstream effect: in the IsBSDEJSolution predicate's M_N pin, `M_N T' ω = stochasticIntegral N U T' ω` (a.s.) depends on the `Classical.choose`-witness, which is non-canonical. For predictable U, the witness has the right L² norm. For non-predictable U, the witness is whatever the axiom's existential happened to pick. **The "pin" therefore doesn't actually pin M_N to a canonical functional of U** in any rigorous sense — it pins to a choice-defined object whose properties (for non-predictable U) are weakly characterized.

- **Recommendation**: Strengthen `itoIsometry_compensated_unified_existence` to take `(h_progMeas : ProgMeasurable φ)` and `(h_sq_int : ∫⁻ ω ∫⁻ s ∫⁻ e ‖φ‖² < ⊤)` as parameters, mirroring the Brownian-side axiom `itoIsometry_brownian_unified_existence` at `Brownian/SimplePredictableRefine.lean:2094-2115`. The brownian-side axiom DOES take these hypotheses; the compensated-side axiom does not, and is therefore strictly less faithful to the cited theorem. After this fix, `Compensated.stochasticIntegral` should also take the hypotheses (and return some default value when they fail), so that the M_N pin is meaningful.

### Finding 8 — `BrownianMotion` structure lacks joint measurability of `Function.uncurry W`; only separable measurability `∀ t, Measurable (W t)` is enforced
- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Brownian/Construction.lean:33-70`
- **Evidence** (verbatim, the relevant field):
  ```lean
  structure BrownianMotion (P : Measure Ω) [IsProbabilityMeasure P] where
    W : ℝ → Ω → ℝ
    measurable_eval : ∀ t : ℝ, Measurable (W t)
    initial_zero : ∀ᵐ ω ∂P, W 0 ω = 0
    …
    continuous_paths : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => W t ω)
    …
  ```
- **Why this matters**: Karatzas-Shreve Definition 2.1.1 requires a Brownian motion to be a **measurable process**, i.e., `(t, ω) ↦ W_t(ω)` is `Borel(ℝ) ⊗ ℱ`-measurable jointly. The Lean structure stipulates only marginal measurability for each `t` separately, plus a.s. path continuity. Joint measurability follows mathematically from separable measurability + a.s. continuity + separability of `ℝ` (via the Riesz-style argument), but the structure does not enforce it. Downstream uses (e.g., `Function.uncurry W : ℝ × Ω → ℝ` in `simpleIntegral` and the L²-Itô isometry chain) require joint measurability; the chain works around this by adding `h_meas : Measurable (Function.uncurry H)` etc. at the lemma level. But the BM structure itself is weaker than Karatzas-Shreve. This becomes a problem if anyone tries to derive `(t, ω) ↦ W_t(ω)` measurability from the structure alone.

  Le Gall Theorem 2.1 packages the same result with joint measurability stated explicitly: "There exists a probability space (Ω, F, P) and a process (B_t)_{t ≥ 0} on this space with the following properties: (i) B_0 = 0, (ii) the function (t, ω) → B_t(ω) is jointly measurable, (iii) for any 0 ≤ s ≤ t, B_t − B_s is independent of σ(B_u : u ≤ s) and is N(0, t − s)-distributed, (iv) the function t → B_t(ω) is continuous for almost every ω ∈ Ω." The Lean structure misses (ii) (joint measurability) explicitly.

- **Recommendation**: Add a `measurable_uncurry : Measurable (Function.uncurry W)` field to the `BrownianMotion` structure. The `BrownianMotion.exists` axiom (line 176-178) provides existence with `Nonempty (BrownianMotion P)`, so any witness must satisfy the field — the cited Karatzas-Shreve / Le Gall construction does produce a jointly measurable process. Adding the field strengthens the structure without breaking anything.

### Finding 9 — `PoissonRandomMeasure` structure does not enforce Applebaum's full Definition 2.3.1 (the "P(N(B) = ∞) = 1 for μ(B) = ∞" clause is missing)
- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Poisson/RandomMeasure.lean:64-102`
- **Evidence** (verbatim, the relevant fields):
  ```lean
  structure PoissonRandomMeasure
      (P : Measure Ω) [IsProbabilityMeasure P]
      (ν : Measure E) [SigmaFinite ν] where
    N : Ω → Measure (ℝ × E)
    measurable_eval : ∀ {B : Set (ℝ × E)}, MeasurableSet B → Measurable (fun ω => N ω B)
    poisson_law : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
      referenceIntensity ν B ≠ ⊤ →
      P.map (fun ω => N ω B) = poissonMeasureENN (referenceIntensity ν B).toNNReal
    independent_disjoint : …
    joint_past_future_independent : …
  ```
- **Why this matters**: Applebaum 2009 Definition 2.3.1 (and Kallenberg 2017 Proposition 3.6) state THREE properties:
  (a) For `B` with `μ(B) < ∞`, `N(B)` has Poisson law with mean `μ(B)`.
  (b) For pairwise disjoint `B_1, …, B_n`, `N(B_1), …, N(B_n)` are independent.
  (c) For `B` with `μ(B) = ∞`, `P(N(B) = ∞) = 1`.

  The Lean structure captures (a) and (b) (with `iIndepFun` over arbitrary families, which is stronger than pairwise — good). But (c) is missing: when `referenceIntensity ν B = ⊤`, the `poisson_law` clause does NOT constrain `N(·, B)`. A "Poisson random measure" in the Lean sense could give `N(ω, B) = 0` always for such `B`, which violates Applebaum 2.3.1.

  In practice, this doesn't bite for the L²-Itô-Lévy integral chain (which restricts to `(0, T] × A` with `ν(A) < ∞` via the σ-finite decomposition), but it does mean the structure is technically weaker than the cited Applebaum theorem.

  Equivalently, Kallenberg Proposition 3.6 includes the σ-additivity property `N(⊔ B_i) = ∑ N(B_i)` (a.s.) for any countable family — implicit in `N : Ω → Measure (ℝ × E)` (since Measure has σ-additivity built in), so that part is fine.

- **Recommendation**: Add a field `infinite_intensity_almost_surely : ∀ {B : Set (ℝ × E)}, MeasurableSet B → referenceIntensity ν B = ⊤ → ∀ᵐ ω ∂P, N ω B = ⊤`. This is direct from the standard Poisson recipe (sum of i.i.d. Poisson with infinite mean) and matches Applebaum 2.3.1 (c).

### Finding 10 — Four dead-code `sorry` lemmas exist in the codebase, two of which are reachable from public APIs (Compensated `simplePredictable_dense_L2` uses sorried `…_bounded`; if anyone unlocks the public lemma, sorry propagates)
- **Severity**: MEDIUM
- **Location**:
  - `LevyStochCalc/Poisson/RandomMeasure.lean:139` (`poissonRandomMeasure_finite_exists` — sorry)
  - `LevyStochCalc/Brownian/Continuity.lean:184` (`kolmogorov_modification_ae_eq` — sorry)
  - `LevyStochCalc/Brownian/Ito.lean:3984` (`quadVar_simpleIntegral_brownian` — private sorry)
  - `LevyStochCalc/Poisson/Compensated.lean:1893` (`simplePredictable_dense_L2_bounded` — private sorry, USED by public `simplePredictable_dense_L2` at line 1903)
- **Evidence** (verbatim, the public `simplePredictable_dense_L2` calling the sorried `…_bounded`):
  ```lean
  -- Compensated.lean:1936
  fun M => simplePredictable_dense_L2_bounded hT
    (fun ω s e => max (-(M : ℝ)) (min (M : ℝ) (φ ω s e)))
    (h_clip_meas M) (M : ℝ) (h_clip_bound M)
  ```
- **Why this matters**: `tools/sorry_baseline.txt` is empty and the audit at `tools/full_audit_output.txt` reports clean axiom sets, because these sorried lemmas are not in the Tier 1 axiom dependency chain. But the public lemma `LevyStochCalc.Poisson.Compensated.simplePredictable_dense_L2` (line 1903) DOES use the sorried `simplePredictable_dense_L2_bounded` (private, line 1880) — so this public lemma's proof is `sorry`-tainted via the private call. The audit doesn't flag it because the public lemma is not exposed downstream of the Tier 1 chain (the chain uses `adaptedSimple_dense_L2_compensated`, which is a SEPARATE cited axiom — line 2579 — not the sorried `simplePredictable_dense_L2`).

  This is technically `#print axioms`-clean, but a future refactor that wires `simplePredictable_dense_L2` into the chain would silently propagate the sorry. The same risk exists for `kolmogorov_modification_ae_eq` (Continuity.lean:184) if a future Mathlib forwarder replaces the cited axiom with a proof using this lemma.

  Mathematically, the four sorries are real proof obligations: the dyadic-construction L²-density argument (Compensated), the Y_t = X_t a.s. extension at non-dyadic times (Continuity), the simple-integrand quadVar martingale (Brownian/Ito), and the finite-mass Poisson construction (RandomMeasure). They are legitimate gaps, not stylistic ones.

- **Recommendation**: Either (a) delete the dead-code sorried lemmas if they're not used downstream, or (b) move the public-API-reachable one (Compensated `simplePredictable_dense_L2`) to `sorry_baseline.txt` and gate it behind an `axiom`-style declaration with documentation. Don't leave `sorry`'d public lemmas in the codebase invisible to the audit.

### Finding 11 — `BrownianMotion.continuous_paths` requires continuity on ALL of `ℝ` (not just `[0, ∞)`), but `negative_zero` is only pointwise-a.s. — the joint "a.s. continuous and zero on (−∞, 0)" property is not directly enforced
- **Severity**: LOW
- **Location**: `LevyStochCalc/Brownian/Construction.lean:50-55`
- **Evidence** (verbatim):
  ```lean
  continuous_paths : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => W t ω)
  negative_zero : ∀ s : ℝ, s < 0 → ∀ᵐ ω ∂P, W s ω = 0
  ```
- **Why this matters**: `continuous_paths` requires continuity on all of `ℝ`. `negative_zero` is `∀ s < 0, ∀ᵐ ω, W s ω = 0` — pointwise-in-`s` almost-sure. The stronger and more natural Karatzas-Shreve formulation is `∀ᵐ ω, ∀ s < 0, W s ω = 0` — uniformly a.s. in `s`. The two are not equivalent under countable union of null sets without uniform control. For Brownian motion this is harmless because the path is a.s. continuous and equals zero on every rational `s < 0` (countable a.s.); continuity then gives `W s ω = 0` for all `s < 0` a.s.

  Mathematically the structure is consistent for Brownian motion, but pedantically the conjunction `continuous_paths ∧ negative_zero` is weaker than the literature's "a.s., the path is continuous on `[0, ∞)` and zero on `(−∞, 0)`". Minor sharpening would replace `negative_zero` with `negative_zero_uniform : ∀ᵐ ω ∂P, ∀ s : ℝ, s < 0 → W s ω = 0` (∀-quantifier inside the a.s.). Karatzas-Shreve Brownian motion is usually only defined on `[0, ∞)`; the Lean extension to `ℝ` is a structural convention, but should be precisely worded.

- **Recommendation**: Replace `negative_zero` with `negative_zero_uniform : ∀ᵐ ω ∂P, ∀ s : ℝ, s < 0 → W s ω = 0` to match the uniform-in-ω formulation. Provable from the existing `negative_zero` + `continuous_paths` (via density of `ℚ ∩ (−∞, 0)`), so the structure stays consistent.

### Finding 12 — `JumpDiffusion.exists_unique` does not pass `(W, N, coeffs)` to the witness; the existence claim is vacuously independent of the Brownian motion and Poisson random measure
- **Severity**: LOW
- **Location**: `LevyStochCalc/Ito/Setting.lean:85-112`
- **Evidence** (verbatim):
  ```lean
  refine ⟨{
    X := fun _ _ => x₀
    …
  }⟩
  ```
- **Why this matters**: The witness `X t ω := x₀` is a constant function ignoring `W, N, coeffs`. This is technically allowed by the theorem statement (which has `is_solution : True` — see Finding 3), but it makes the theorem's quantification over `(W, N, coeffs)` cosmetic. A reader of the signature would assume the existence depends on the specific `(W, N, coeffs)`, but the proof shows it does not. This is a "theorem with unused hypotheses" — the underscored binders `(_W : MultidimBrownianMotion P d)` etc. would communicate this honestly; the current binders without underscore mislead.

  This is a corollary of Finding 3 and would be resolved by the same fix.

- **Recommendation**: See Finding 3.

## Per-claim verdicts on the 11 Tier 1 cited axioms + ~10 derivative theorems

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `Brownian.BrownianMotion.exists` | EARNED | Honest axiom, Karatzas-Shreve / Le Gall cited correctly; structure has minor gap (no joint measurability — see Finding 8). |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` | WEAK | Honest axiom but the structure it returns lacks Applebaum 2.3.1 (c) (P(N(B)=∞)=1 for μ(B)=∞ — see Finding 9). |
| `Brownian.Continuity.kolmogorovChentsov_modification` | EARNED | Faithful weak form of Karatzas-Shreve 2.2.8 (continuity only, no Hölder regularity claimed — that's fine, just a weaker statement of the same theorem). |
| `Brownian.Martingale.brownian_martingale_rightCont` | EARNED | Honest axiom citing Blumenthal 0-1 + right-cont augmentation; faithful to Karatzas-Shreve 2.7.7-9. |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` | EARNED | Honest unified-existence axiom; takes `h_meas + h_progMeas + h_sq_int_global` hypotheses correctly, conjuncts are the literature properties. |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` | WEAK | Axiom takes `φ` with NO predictability / measurability / integrability hypothesis on the outer existence — see Finding 7. Compensated counterpart of the Brownian-side axiom should mirror it but doesn't. |
| `Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` | EARNED | Honest axiom, Applebaum 4.3.1 / Ikeda-Watanabe II.3.4 cited correctly; statement matches the cited result. |
| `Poisson.Compensated.adaptedSimple_dense_L2_compensated` | EARNED | Honest axiom, Applebaum 4.2.2 / Ikeda-Watanabe II.3.3 cited correctly; statement matches the cited density result. |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` | WEAK | **Axiom signature omits Lipschitz on `f` and L²-integrability of `g(X_T)`** — claims existence + uniqueness for arbitrary `bsdej`, which is mathematically false; see Finding 5. Also see Finding 6 on M_W slack and Finding 2 on predictability omission. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` | WEAK | Same omission of Lipschitz / L² hypotheses; cited Bouchard-Elie-Touzi 2009 Thm 2.1 requires them but the Lean axiom does not. |
| `Ito.JumpFormula.itoLevyFormula` | **TRIVIAL** | **Statement is `∃ a b c d, sum = change` — satisfied by `⟨change, 0, 0, 0⟩` trivially. 2026-05-11 "demotion" did not fix this; see Finding 1.** |
| `Brownian.Multidim.MultidimBrownianMotion.exists` | EARNED | Forwarder over `BrownianMotion.exists` via `Measure.pi` + `iIndepFun_pi`; honest derivation, real proof in `Multidim.lean:209-230`. |
| `Brownian.Continuity.brownian_continuous_modification` | EARNED | Forwarder over `kolmogorovChentsov_modification` via the explicit Gaussian 4th-moment calculation; substantive real proof in `Continuity.lean:507-554`. |
| `Brownian.Martingale.brownian_filtration_rightContinuous` | EARNED | Forwarder over `brownian_martingale_rightCont`; honest. |
| `Brownian.Martingale.brownian_martingale` | EARNED | Genuinely proved theorem (no cited axiom in its closure); ~100-line direct proof via conditional expectation of increments. |
| `Brownian.Martingale.brownian_quadVar` | EARNED | Same — genuinely proved theorem. |
| `Brownian.Ito.itoIsometry` | EARNED | Extracts conjunct 3 from the unified-existence cited axiom; honest. |
| `Brownian.Ito.martingale_stochasticIntegral` | EARNED | Extracts conjunct 1 — honest. |
| `Brownian.Ito.quadVar_stochasticIntegral` | EARNED | Extracts conjunct 2 — honest. |
| `Poisson.Compensated.itoLevyIsometry` | WEAK | Extracts conjunct 3 from the unified-existence axiom, but inherits the predictability gap from Finding 7. |
| `Poisson.Compensated.martingale_stochasticIntegral` | WEAK | Same; inherits the gap. |
| `Poisson.Compensated.quadVar_stochasticIntegral` | WEAK | Same. |
| `Poisson.Compensated.cadlag_modification_exists` | WEAK | Same. |
| `Poisson.L2Isometry.itoLevyIsometry` | WEAK | 1-line forwarder over `Compensated.itoLevyIsometry`; inherits the gap. |
| `Ito.Setting.JumpDiffusion.exists_unique` | **TRIVIAL** | **Constant-path witness; `is_solution : True` structure; name is misnomer (no uniqueness claim) — see Finding 3.** |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` | **TRIVIAL** | **`⟨0, 0, 0, ξ − 𝔼[ξ]⟩` witness; `BM_integral` and `jump_integral` are free existentials not pinned to actual stochastic integrals — see Finding 4.** |

## Tools and sources used

- **Lean LSP tools called**:
  - `ToolSearch` to load `mcp__lean-lsp__lean_verify`, `lean_hover_info`, `lean_declaration_file`, `lean_diagnostic_messages`, `lean_goal`, `lean_file_outline`, plus `WebSearch`, `WebFetch`.
  - `mcp__lean-lsp__lean_hover_info` on `continuousBSDEJ_exists_unique` to confirm hypothesis-free signature.
  - Direct `Read` on every key file: `BSDEJ/Definition.lean`, `BSDEJ/Existence.lean`, `BSDEJ/PathRegularity.lean`, `BSDEJ/MartingaleRepresentation.lean`, `Brownian/Construction.lean`, `Brownian/Continuity.lean`, `Brownian/Multidim.lean`, `Brownian/Martingale.lean` (partial), `Brownian/Ito.lean` (partial via outline), `Brownian/SimplePredictableRefine.lean` (partial — Tier 1 #5 region), `Poisson/RandomMeasure.lean`, `Poisson/NaturalFiltration.lean`, `Poisson/L2Isometry.lean`, `Poisson/Compensated.lean` (partial — Tier 1 #6-#8 region), `Ito/Setting.lean`, `Ito/JumpFormula.lean`.
  - `Grep` for trivial-witness pattern matches: `refine ⟨0, 0`, `True := trivial`, `sorry`, `ξ_measurable`, `is_solution`, `IsBSDEJSolution`, `JumpDiffusion`, `jacodYor_representation`, `itoLevyFormula`, `simplePredictable_dense_L2`, `kolmogorov_modification_ae_eq`, `poissonRandomMeasure_finite_exists`, `quadVar_simpleIntegral_brownian`, `Compensated.simplePredictable_dense_L2`.
- **Web searches**:
  - `"backward stochastic differential equation" definition "adapted" "predictable" "S² × H²" Pardoux Rascanu`
  - `Tang Li 1994 BSDE jumps "adapted" "predictable" definition uniqueness`
  - `"H²" "predictable processes" BSDE definition "locally square integrable" Z process`
  - `Applebaum 2009 "Poisson random measure" definition 2.3.1 "intensity measure" properties`
  - `Karatzas Shreve "Brownian motion" definition 2.1 "F_t-adapted" measurable process`
- **Web fetches**:
  - `https://www.researchgate.net/publication/305322166_Existence_and_uniqueness_results_for_BSDE_with_jumps_the_whole_nine_yards` (403 forbidden)
  - `https://arxiv.org/pdf/1607.06644` (PDF — could not extract text)
  - `https://www.math.utah.edu/~davar/math7880/S11/Chapters/Ch4.pdf` (PDF — could not extract text)
  - `https://www.math.purdue.edu/~stindel/teaching/ma539/brownian-motion2.pdf` (PDF — could not extract text)
  - `https://unina2.on-line.it/sebina/repository/catalogazione/documenti/Karatzas,%20Shreve%20-%20Brownian%20motion%20and%20stochastic%20calculus.%202.%20ed..pdf` (PDF — could not extract text)
- **Papers consulted (for the literature predicates)**:
  - Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*, Springer 1991, Definition 2.1.1, Theorems 2.1.5, 2.2.8, 2.7.7, 2.7.9, 3.2.6.
  - Le Gall, J.-F. *Brownian Motion, Martingales and Stochastic Calculus*, Springer 2016, Theorems 2.1, 2.9, 5.13.
  - Applebaum, D. *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP 2009, Definition 2.3.1, Theorems 2.3.1, 4.2.3, 4.2.4, 4.4.7, 6.2.9, Lemmas 4.2.2, 4.2.5.
  - Ikeda, N. & Watanabe, S. *SDEs and Diffusion Processes*, 2nd ed., North-Holland 1989, §II.3, Lemmas II.3.3, II.3.4.
  - Pardoux, E. & Răşcanu, A. *SDEs, Backward SDEs, PDEs*, Springer 2014, Theorems 4.79, 5.42.
  - Tang, S. & Li, X. *Necessary conditions for optimal control of stochastic systems with random jumps*, SIAM J. Control Optim. 32(5), 1994, Theorem 3.1.
  - Bouchard, B. & Elie, R. & Touzi, N. *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 119(11), 2009, Theorem 2.1.
  - Kallenberg, O. *Random Measures, Theory and Applications*, Springer 2017, Proposition 3.6.
  - Revuz, D. & Yor, M. *Continuous Martingales and Brownian Motion*, Springer 1999, Theorem I.2.1.
  - Jacod, J. (1976) "Multivariate point processes: predictable projection, Radon-Nikodym derivatives, representation of martingales".

## What you couldn't verify

- Could not directly extract verbatim quotes from the cited textbooks (Karatzas-Shreve, Le Gall, Applebaum) because the PDF endpoints I tried returned raw binary that the WebFetch summarizer couldn't read, and Google Books / Springer abstracts are paywalled. I cross-verified the literature predicates against secondary sources (web-search summaries from multiple recent BSDE-with-jumps papers — see the "modern BSDE with jumps" consensus quoted in Finding 2). The predicate I claim for `S² × H² × H²_N` matches multiple independent recent references, so this is high-confidence even without direct quotes from Tang-Li 1994.
- Did not exhaustively read the ~4000 lines of low-level simple-integrand machinery in `Brownian/Ito.lean` + `Brownian/SimplePredictableRefine.lean` + `Poisson/Compensated.lean`. I read the cited-axiom statements and the immediately surrounding 100-200 lines, plus the file outlines. A persona-12 / persona-5 deeper proof-tree audit may find further trivial-witness patterns in private lemmas; my lens is the public predicates and cited statements.
- Did not run `lake build` or `tools/lint.sh` directly (read-only audit). The 8401-job PASS state is taken from the override doc and `tools/full_audit_output.txt`.
- Did not verify the `_h_progMeas` parameter types in `itoIsometry_brownian_unified_existence` against Mathlib's `MeasureTheory.ProgMeasurable` — there's a custom progressive-σ-algebra encoding via `StronglyMeasurable` with `Prod.instMeasurableSpace ... naturalFiltration ... seq t)`. This could be subtly different from the standard `ProgMeasurable` definition; a Lean-formalization specialist (persona 1 / 2) should check.

## Recommendations for the project (≤ 5 bullets)

- **Fix `itoLevyFormula` properly, not cosmetically.** The 2026-05-11 demotion was the wrong direction — the trivial-witness defect is in the STATEMENT, not just the proof. Either pin the four terms to the literature integral forms (`Brownian.SimplePredictableRefine.stochasticIntegral` against `∇uᵀ σ`, `Poisson.Compensated.stochasticIntegral` against `u(·+γ) − u`, etc.) or remove the axiom and accept that the Itô-Lévy formula is not formalised yet.
- **Fix `JumpDiffusion.is_solution : True` and `jacodYor_representation`'s trivial proof.** These are the same defect class the recursive audit was designed to catch; they were missed because (a) `is_solution : True` is a structural placeholder rather than a per-proof witness, and (b) `jacodYor_representation` looks substantive due to its 5-conjunct conclusion. Either pin the existentials to their actual integral content, or demote to `axiom` with citations.
- **Add literature hypotheses to the BSDEJ cited axioms.** `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` currently take `(W, N, bsdej, X, T, 0 < T)` only — add `(h_L : 0 ≤ L) (h_Lip : Lipschitz bsdej ν L) (h_meas_X) (h_terminal_L2)` to match Tang-Li / Bouchard-Elie-Touzi. Without these, the axioms claim more than the cited theorems.
- **Strengthen `IsBSDEJSolution` to literature `S² × H² × H²_N`.** Add adaptedness of `Y`, predictability (or progressive measurability) of `Z, U`. Pin `M_W` to the multidim Brownian stochastic integral of `Z` (will require introducing a multidim-Brownian-Itô-integral primitive, mirror of `Compensated.stochasticIntegral`). After this, the uniqueness clause of `continuousBSDEJ_exists_unique` becomes consistent with Tang-Li.
- **Audit metric upgrade.** `#print axioms`-cleanness fooled the recursive audit on `JumpDiffusion.exists_unique` and `jacodYor_representation` (both show `[propext, Classical.choice, Quot.sound]` in the audit output). Add a secondary trivial-witness scanner that flags `theorem` whose proof body matches patterns like `refine ⟨0, …⟩; …; ring|simp` or `refine ⟨{… is_solution := trivial …}⟩; …`. The pattern is mechanical to detect; the audit just needs to know to look.
