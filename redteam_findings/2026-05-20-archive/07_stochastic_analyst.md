# Red Team Audit: Stochastic Analyst (Itô–Lévy, BSDE, semimartingales)

**Auditor lens**: Stochastic analysis specialist; reads Applebaum (2009), Karatzas–Shreve (1991), Le Gall (2016), Tang–Li (1994), Bouchard–Elie (2008), Revuz–Yor (1999), Pardoux–Răşcanu (2014). I check whether Lean definitions are the literature predicates and whether axiom statements are the literature theorems (verbatim, not "morally").

**Date**: 2026-05-20

**Coverage**:
- Read in full (12 files): `LevyStochCalc/BSDEJ/Definition.lean`, `BSDEJ/Existence.lean`, `BSDEJ/PathRegularity.lean`, `BSDEJ/MartingaleRepresentation.lean`, `Brownian/Multidim.lean`, `Brownian/Construction.lean`, `Poisson/RandomMeasure.lean`, `Poisson/L2Isometry.lean`, `Ito/JumpFormula.lean`, `Ito/Setting.lean`, `tools/cited_axioms.md`, `tools/full_audit_output.txt`.
- Read in part (4 files): `Poisson/Compensated.lean` (focused on lines 2680–2907 around the unified-existence axiom and stochasticIntegral definition), `Brownian/SimplePredictableRefine.lean` (focused on lines 2050–2245 around `itoIsometry_brownian_unified_existence` and downstream theorems), `Brownian/Martingale.lean` (verified `brownian_martingale` is a real proof), `Dissertation/Continuous.lean` (sanity check of forwarders).
- Not touched (out of scope for this lens): `Brownian/Continuity.lean` (KC modification — well-known cited axiom), `Brownian/Ito.lean` (the older simple-integral file, superseded by `SimplePredictableRefine.lean`), `Poisson/Martingale.lean`, `Poisson/NaturalFiltration.lean`.

## Executive summary (≤ 3 sentences)

`continuousBSDEJ_exists_unique` (BSDEJ/Existence.lean:113), `bsdej_path_regularity` (PathRegularity.lean:111), `itoLevyFormula` (JumpFormula.lean:90), and `jacodYor_representation` (MartingaleRepresentation.lean:55) are **mathematically false or vacuously true as written**: the first two omit the Lipschitz / L² hypotheses on `(f, g, X)` that Tang–Li 1994 and Bouchard–Elie 2008 use, the third is the exact `∃ a b c d : Ω → ℝ, change = a + b + c + d` tautology that supposedly was "demoted" but remains additively trivial, and the fourth is proved with `⟨0, 0, 0, ξ − 𝔼ξ⟩; ring` — a textbook ring identity passed off as Jacod–Yor. The strengthened `IsBSDEJSolution` predicate is honestly weaker than the literature (the docstring admits this at lines 60–64) and its `M_W`-isometry-only constraint is **insufficient to recover uniqueness**, so the uniqueness clause of `continuousBSDEJ_exists_unique` is not implied by the predicate. Separately: the Bouchard–Elie–Touzi 2009 citation is misattributed — the real paper is **Bouchard & Elie**, SPA **118(1)**, **2008**, with **no Touzi** as third author and the wrong volume/issue/year.

## Top findings (ranked by severity, highest first)

### Finding 1 — `itoLevyFormula` is the trivial-witness tautology it was supposedly demoted from

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/Ito/JumpFormula.lean:90–105`
- **Evidence**: The axiom statement, verbatim:
  ```
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
  The axiom's payload (lines 102–105) is the existential `∃ a b c d : Ω → ℝ, ξ = a + b + c + d` over reals where `ξ := u(T, X_T) − u(0, X_0)`. This is **logically provable in ℝ** without any reference to "drift", "diff_mart", "jump_mart", or "comp_drift" — the literal trivial witness `⟨ξ, 0, 0, 0⟩` makes it true. The `cited_axioms.md` line 91–93 (and the JumpFormula.lean module docstring at lines 30–38) explicitly call this out as a "trivial-witness pattern" that was "demoted from `theorem` to `axiom`". But the AXIOM STATEMENT IS STILL THE SAME TRIVIAL CLAIM. Demoting a fake theorem to an axiom does not fix the statement — it just moves the lie from the proof body to the cited-axioms ledger.
- **Why this matters**: Applebaum 2009 Thm 4.4.7 is a specific identity:
  `u(T, X_T) − u(0, X_0) = ∫₀ᵀ (∂_t u + 𝓛u)(s, X_{s-}) ds + ∫₀ᵀ ∇u(s, X_{s-})ᵀ σ dW_s + ∫₀ᵀ∫_E [u(·+γ) − u] Ñ(ds,de) + ∫₀ᵀ∫_E [u(·+γ) − u − γᵀ∇u] ν(de) ds`.
  The four integrals are SPECIFIC functions of `(W, N, μ, σ, γ, u, X)`. The Lean axiom does not constrain `drift_term`, `diff_mart`, `jump_mart`, `comp_drift` to BE those integrals — it just requires them to sum to the change. Any downstream code that consumes this axiom can pull out arbitrary terms (e.g., `(ξ, 0, 0, 0)`) and use them as if they were the literature integrals. The axiom is mathematically false in the strong sense: it does NOT capture Applebaum 4.4.7.
- **Recommendation**: Either (a) state the axiom with explicit functional forms `drift_term ω := ∫₀ᵀ (∂_t u + 𝓛u)(s, X_{s-} ω) ds`, `diff_mart := Brownian.stochasticIntegral W ((∇u)ᵀ σ) T`, etc., binding each existential to the literature definition; or (b) keep the trivial existential but rename it honestly to `itoLevyFormula_additiveDecomposition_trivial` and stop claiming it represents Applebaum 4.4.7. Demoting from `theorem` to `axiom` is cosmetic; the statement is the problem.

### Finding 2 — `JumpDiffusion.exists_unique` is a fake existence theorem (constant-path witness, `is_solution := True`)

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/Ito/Setting.lean:50–112`
- **Evidence**: The structure (lines 50–72):
  ```
  structure JumpDiffusion ... where
    X : ℝ → Ω → (Fin n → ℝ)
    measurable_path : Measurable (Function.uncurry X)
    initial_value : ∀ᵐ ω ∂P, X 0 ω = x₀
    sup_L2 : ∀ T : ℝ, 0 < T → ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, ∑ i, (‖X t.1 ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
    is_solution : True
  ```
  Field `is_solution : True` — the SDE-satisfaction constraint is literally the proposition `True`. The "exists_unique" theorem (lines 85–112):
  ```
  theorem JumpDiffusion.exists_unique ... :
      Nonempty (JumpDiffusion W N coeffs x₀) := by
    refine ⟨{
      X := fun _ _ => x₀
      ...
      is_solution := trivial
    }⟩ ...
  ```
  Witness: `X t ω := x₀` (constant). `#print axioms` confirms it depends only on `[propext, Classical.choice, Quot.sound]` — no SDE content at all. Also, "exists_unique" is misnamed: the theorem only proves `Nonempty`, no uniqueness clause whatsoever (line 93).
- **Why this matters**: Applebaum 2009 Thm 6.2.9 (claimed reference in the inline comment, line 95) gives existence AND uniqueness of jump-SDE solutions for Lipschitz `(μ, σ, γ)` and L²-integrable initial data. The Lean structure does not encode the SDE constraint (the `is_solution` field is `True`), so any constant path inhabits the type, and the proof reduces to "constant_path measures right + has finite L²-sup". Downstream, `itoLevyFormula` (Finding 1) takes a `JumpDiffusion` instance as input — that instance can be the constant-`x₀` path, and the Itô–Lévy formula becomes "∃ four reals summing to a constant", which is a number-theory tautology in ℝ. The whole Itô–Lévy formula axiom is consumed against a non-SDE-satisfying `JumpDiffusion` and remains trivially true.
- **Recommendation**: Replace `is_solution : True` with the literature predicate `X_t = x₀ + ∫₀ᵗ μ(s, X_s) ds + ∫₀ᵗ σ(s, X_s) dW_s + ∫₀ᵗ ∫_E γ(s, X_{s-}, e) Ñ(ds, de)` a.s. (using the Brownian and compensated-Poisson stochastic-integral primitives), and rename `exists_unique` → `exists_unique_axiom` (demote to cited axiom, Applebaum 6.2.9) or `exists_constantPath_witness` (honest naming). Until that's done, every downstream use of `JumpDiffusion` lacks the SDE constraint.

### Finding 3 — `jacodYor_representation` is `theorem`-stated but proved by `⟨0, 0, 0, ξ - 𝔼ξ⟩; ring` — undocumented trivial witness, NOT in the Tier 1 cited-axioms ledger

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:55–84`
- **Evidence**: The theorem (lines 55–73) claims to give the Jacod–Yor martingale representation:
  ```
  theorem jacodYor_representation ... :
      ∃ (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
        (BM_integral jump_integral : Ω → ℝ),
        Measurable (Function.uncurry Z) ∧
        Measurable (fun (p : ℝ × Ω × E) => U p.1 p.2.1 p.2.2) ∧
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) ∧
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) ∧
        (∀ᵐ ω ∂P, ξ ω = (∫ ω', ξ ω' ∂P) + BM_integral ω + jump_integral ω)
  ```
  The proof (lines 77–84):
  ```
  refine ⟨0, 0, 0, fun ω => ξ ω - ∫ ω', ξ ω' ∂P, ?_, ?_, ?_, ?_, ?_⟩
  · exact measurable_const
  · exact measurable_const
  · simp
  · simp
  · refine Filter.Eventually.of_forall (fun ω => ?_)
    show ξ ω = (∫ ω', ξ ω' ∂P) + 0 + (ξ ω - ∫ ω', ξ ω' ∂P)
    ring
  ```
  `Z := 0`, `U := 0`, `BM_integral := 0`, `jump_integral := ξ − 𝔼ξ`. The "representation" is just the ring identity `ξ = 𝔼ξ + 0 + (ξ − 𝔼ξ)`. Verified via `mcp__lean-lsp__lean_verify`: depends only on `[propext, Classical.choice, Quot.sound]` — NO connection to any Brownian stochastic integral, no connection to any compensated Poisson stochastic integral, no actual martingale representation. **`jacodYor_representation` is NOT listed in `tools/cited_axioms.md`** — it's not in the Tier 1 inventory at all, so the user has no record that this "theorem" is a trivial-witness fake.
- **Why this matters**: Jacod's 1976 representation theorem is a non-trivial result: it says every L²-martingale on the filtration of `(W, N)` admits a UNIQUE predictable pair `(Z, U)` such that `M_t = M_0 + ∫₀ᵗ Z_s dW_s + ∫₀ᵗ ∫_E U_s(e) Ñ(ds, de)`. The Lean "theorem" claims to be this but gives no connection between `Z, U` and `BM_integral, jump_integral` — they are independently existentially quantified. The same pattern as Finding 1 (sum-of-four-things tautology). This is the EXACT pattern that supposedly was "audited out" — but it survived because `MartingaleRepresentation.lean` is not in the `cited_axioms.md` ledger.
- **Recommendation**: Either (a) rewrite as a cited axiom (with citation Jacod 1976 / Tang–Li 1994), explicitly constraining `BM_integral` and `jump_integral` to be the canonical stochastic integrals of `Z` and `U`; or (b) state honestly as `theorem jacodYor_representation_additive_tautology` and stop pretending it's Jacod–Yor. Add to `cited_axioms.md` either way so the ledger is honest.

### Finding 4 — `continuousBSDEJ_exists_unique` axiom omits Lipschitz, L², and measurability hypotheses; the Lean axiom is mathematically false (claims more than Tang–Li 1994 proves)

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/BSDEJ/Existence.lean:113–126`
- **Evidence**: The axiom statement, verbatim, with the entire hypothesis set:
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
        LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T ∧
        ∀ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
          LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y' Z' U' T →
          (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = Y' t ω)
  ```
  Hypotheses: only `0 < T`. Nothing on `bsdej.f` (Lipschitz? measurable?), nothing on `bsdej.g` (measurable? `∫ ‖g(X_T)‖² < ⊤`?), nothing on `X` (measurable? càdlàg? `𝔼[sup_t ‖X_t‖²] < ⊤`?). The `BSDEJData` structure (`Definition.lean:78–82`) has no measurability or Lipschitz fields either; `f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ`, `g : (Fin n → ℝ) → ℝ` — raw functions.
- **Why this matters**: Tang & Li 1994 SICON 32(5), Thm 3.1 (the cited reference, `Existence.lean:98–100`) requires **Lipschitz `(f, g)` in `(y, z, u)`** and **`g(X_T) ∈ L²(F_T)`**, with **`X`** a square-integrable càdlàg adapted process. Without Lipschitz `f`, BSDEJ uniqueness fails (classical Picard counterexample); without measurable `f, g`, the integral `∫ f` and `g(X_T)` are not well-defined (Bochner returns 0). The Lean axiom asserts existence + uniqueness UNCONDITIONALLY — so it claims to prove what Tang–Li would NOT claim, and what's mathematically false. Concrete counterexample: take `bsdej.f s x y z u := if y = 0 then 1 else 0`, `bsdej.g x := 0`. This `f` is non-Lipschitz and discontinuous in `y`; the BSDEJ `Y_t = ∫_t^T 1_{Y_s = 0} ds − martingales` admits no Lipschitz solution but has multiple weak solutions. The Lean axiom claims a unique `Y` exists. False. (The downstream forwarder `Dissertation.Continuous.continuousBSDEJ_exists_unique`, file `Dissertation/Continuous.lean:251–268`, also lacks hypotheses, so the falsity propagates.)
- **Recommendation**: Add hypotheses verbatim from Tang–Li 1994 Thm 3.1: `(hLip : Lipschitz bsdej ν L)` (the definition `Lipschitz` already exists on `BSDEJ/Existence.lean:67–73`!), `(hg_L2 : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊)² ∂P < ⊤)`, `(hX_meas : Measurable (Function.uncurry X))`, `(hX_sup_L2 : ∀ T' > 0, ∫⁻ ω, (⨆ t ∈ [0, T'], ‖X t ω‖₊²) ∂P < ⊤)`. With these, the axiom matches Tang–Li exactly. Right now the axiom is *strictly stronger* than the literature theorem — and false.

### Finding 5 — `bsdej_path_regularity` axiom is materially weaker than BET 2008 Thm 2.1: `Z_avg, U_avg` are existentially quantified, killing the L²-projection-error content; plus no Lipschitz hypothesis

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/BSDEJ/PathRegularity.lean:111–139`
- **Evidence**: The axiom statement (lines 111–139), key fragment from lines 131–139:
  ```
  ∃ (Z_avg : ℝ → Ω → (Fin d → ℝ)) (U_avg : ℝ → Ω → E → ℝ),
    (⨆ n : Fin M, ∫⁻ ω, ⨆ t ∈ Set.Icc (partition n.castSucc) (partition n.succ),
      (‖Y t ω - Y (partition n.castSucc) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
    + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ∑ i, (‖Z s ω i - Z_avg s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
    + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖U s ω e - U_avg s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
    ≤ ENNReal.ofReal (C * Δt)
  ```
  `Z_avg` and `U_avg` are existentially quantified inside the axiom. The intended literature meaning: `Z_avg` is the conditional time-average of `Z` over each partition interval (defined in the same file at lines 62–71 as `conditionalTimeAverage_Z`), and similarly `U_avg`. The BET 2008 Thm 2.1 statement bounds `Z − Z_avg` and `U − U_avg` for the SPECIFIC conditional projections — that's the entire L²-projection-error result. **By existentially quantifying `Z_avg, U_avg`, the Lean axiom lets the witness pick `Z_avg := Z` and `U_avg := U`** (making both projection-error terms `0`). The axiom then reduces to: "∃ C, ∀ partition, the L²-time modulus of `Y` is ≤ C·Δt" — which doesn't even need the BSDEJ structure, just an L²-bounded `Y` (and the constant from `IsBSDEJSolution`'s `∫⁻ ω (⨆_t ‖Y_t‖²) < ⊤` bounds it uniformly). The named function `conditionalTimeAverage_Z` (defined precisely at lines 62–71 for use in the axiom) is **never referenced** in the axiom statement.
- **Why this matters**: BET 2008 Thm 2.1 (Bouchard & Elie 2008 SPA 118(1), pp. 53–75) is exactly the L²-projection-error bound on `Z − E[Z | F_{t_n}]` and `U − E[U | F_{t_n}]`. That's the discrete-time approximation result that underwrites Euler-scheme convergence. With `Z_avg, U_avg` free, the axiom states a much weaker fact (`Y` is L²-càdlàg-regular) and the projection content is silently lost. Downstream numerical work that depends on this regularity result is consuming a substantially weaker statement than what the paper proves.
- **Recommendation**: Change `∃ (Z_avg) (U_avg)` to use the named definitions `let Z_avg := conditionalTimeAverage_Z partition Z; let U_avg := conditionalTimeAverage_U partition U`. Also add Lipschitz hypothesis on `f` (`Lipschitz bsdej ν L`) and L² hypothesis on terminal data, mirroring BET 2008.

### Finding 6 — `IsBSDEJSolution` is still slightly weaker than literature; uniqueness of `continuousBSDEJ_exists_unique` is not implied by the predicate

- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:91–133`, docstring at lines 60–64
- **Evidence**: The predicate (lines 111–127):
  ```
  ∃ M_W M_N : ℝ → Ω → ℝ,
      Measurable (Function.uncurry M_W) ∧
      Measurable (Function.uncurry M_N) ∧
      -- M_W satisfies the multidim Brownian L²-Itô isometry against Z:
      (∀ T', 0 < T' →
        ∫⁻ ω, (‖M_W T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) ∧
      -- M_N is pinned to the canonical compensated-Poisson L² integral of U:
      (∀ T' : ℝ, ∀ᵐ ω ∂P,
        M_N T' ω =
          LevyStochCalc.Poisson.Compensated.stochasticIntegral N
            (fun ω' s e => U s ω' e) T' ω) ∧
      ...
      (∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
        MeasureTheory.Martingale M_W Filt P ∧
        MeasureTheory.Martingale M_N Filt P) ∧
      ...
  ```
  And the docstring (lines 60–64), verbatim admission:
  > The strengthened predicate is still slightly weaker than the literature (it doesn't pin `M_W` to be literally `∫ Z · dW`, only an isometric martingale), but it is non-vacuous: the literature solution satisfies it, and trivial constant `Y` does not.
- **Why this matters**: There are MANY L²-isometric martingales — the constraint `𝔼[(M_W T')²] = 𝔼[∫₀ᵀ' ‖Z_s‖² ds]` does not pin `M_W` to be the canonical Brownian Itô integral of `Z`. For `d ≥ 2`, with `Z = (Z¹, Z²)` you can swap to `Z' := (Z², Z¹)` and the L²-isometric martingale `M'_W := ∫Z' · dW` satisfies the same isometry but `M'_W ≠ ∫Z · dW`. With orthogonality to `M_N` (independent Brownian / Poisson), additional ambiguity arises. The literature Tang–Li uniqueness uses the orthogonal-projection structure of `∫Z dW + ∫U dÑ`; the Lean predicate replaces "the canonical Brownian integral of Z" with "ANY L²-isometric martingale with the right norm". This means **the uniqueness clause of `continuousBSDEJ_exists_unique` (line 124–126) is NOT implied by the predicate** — the predicate admits non-Tang–Li witnesses. The docstring (line 64) claims "sufficient for the cited axioms `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` to assert substantive content"; my analysis disagrees with the uniqueness half. Existence is plausibly enforced because the literature solution does satisfy the predicate; uniqueness is not, because non-canonical L²-isometric martingales let you construct distinct `(Y, Z, U)` triples for the same data. (Also note: the `_W` argument to `IsBSDEJSolution` is unused — line 95 — so the predicate doesn't even refer to the specific Brownian motion, only to its dimension.)
- **Recommendation**: Pin `M_W := Brownian.SimplePredictableRefine.stochasticIntegral W Z h_meas h_progMeas h_sq_int_global` (the existing primitive on `SimplePredictableRefine.lean:2123`), threading `h_progMeas` through `IsBSDEJSolution`. That makes the predicate match Tang–Li. Until that's done, `continuousBSDEJ_exists_unique`'s uniqueness clause is not justified by the predicate — and the docstring's claim of sufficiency is wrong about uniqueness.

### Finding 7 — `itoIsometry_compensated_unified_existence` axiom takes `φ : Ω → ℝ → E → ℝ` with NO hypotheses (not even measurability); existence is asserted unconditionally; the Brownian analog DOES properly hypothesise

- **Severity**: HIGH
- **Location**: `LevyStochCalc/Poisson/Compensated.lean:2748–2767`
- **Evidence**: Compensated axiom (line 2748–2767):
  ```
  axiom itoIsometry_compensated_unified_existence
      {P : Measure Ω} [IsProbabilityMeasure P]
      {ν : Measure E} [SigmaFinite ν]
      (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
      (φ : Ω → ℝ → E → ℝ) :
      ∃ (F : ℝ → Ω → ℝ) (Filt : ...), ...
  ```
  No `h_meas`, no `h_progMeas`, no `h_sq_int`. The isometry conjunct (lines 2758–2763) embeds `Measurable + ∫⁻ < ⊤` as INTERIOR hypotheses (vacuous otherwise). Brownian axiom (`SimplePredictableRefine.lean:2094–2107`):
  ```
  axiom itoIsometry_brownian_unified_existence
      {P : Measure Ω} [IsProbabilityMeasure P]
      (W : LevyStochCalc.Brownian.BrownianMotion P)
      (H : Ω → ℝ → ℝ)
      (h_meas : Measurable (Function.uncurry H))
      (h_progMeas : ∀ t : ℝ, @MeasureTheory.StronglyMeasurable ...)
      (h_sq_int_global : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in [0, T], (‖H ω s‖₊)² < ⊤) :
      ∃ (F : ℝ → Ω → ℝ) (Filt : ...), ...
  ```
  Properly hypothesised.
- **Why this matters**: For non-measurable / non-progressively-measurable / non-L² `φ`, the existence claim is satisfied by `F = 0` (Bochner returns 0 for non-integrable `∫_0^t ∫_E φ²`, so `(F t)² − ∫₀ᵗ ∫_E φ² ∂ν ds = 0`, a martingale; isometry is vacuous because its hypothesis fails; càdlàg is `F = 0` trivially). So the axiom is trivially satisfiable for "wild" `φ`. The Compensated `stochasticIntegral` definition (Compensated.lean:2776–2782) uses `Classical.choose` on this *unconditional* existential, so for wild `φ`, the integral is undefined gibberish but type-checks. In `IsBSDEJSolution` (line 122–123), the Compensated stochastic integral is applied to `(fun ω' s e => U s ω' e)` where `U` has only `Measurable` (not progressive measurability) and only L² (not L²-finite per-T) — so the "M_N pinned to Compensated.stochasticIntegral N (... U)" pin is the trivial-choice result, not the canonical L² Itô–Lévy integral. The "pin" is hollow for the non-progressively-measurable case.
- **Recommendation**: Add `(h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))`, `(h_progMeas : <progressive measurability condition>)`, `(h_sq_int_global : ∀ T > 0, ∫⁻ ω ∫⁻ s ∫⁻ e (‖φ ω s e‖)² < ⊤)` to the Compensated axiom — mirror the Brownian-side hypotheses. Then `stochasticIntegral` (Compensated.lean:2776) becomes a function of `(N, φ, h_meas, h_progMeas, h_sq_int)`, and the `IsBSDEJSolution` M_N-pin becomes meaningful only when `U` carries those hypotheses.

### Finding 8 — Citation misattribution: "Bouchard, Elie & Touzi, SPA 119(11), 2009" is wrong on three counts (no Touzi, wrong vol/issue, wrong year)

- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/PathRegularity.lean:23–24, 92–94`, `tools/cited_axioms.md:84`
- **Evidence**: The Lean source `PathRegularity.lean:23–24`:
  ```
  * Bouchard & Elie & Touzi, "Discrete-time approximation of decoupled
    Forward-Backward SDE with jumps", SPA 119(11), 2009, Theorem 2.1.
  ```
  And lines 92–94:
  ```
  **Reference**: Bouchard, B. & Elie, R. & Touzi, N. *Discrete-time approximation
  of decoupled Forward-Backward SDE with jumps*, Stochastic Processes and their
  Applications 119(11), 2009, Theorem 2.1; ...
  ```
  `cited_axioms.md:84`:
  > Bouchard, Elie & Touzi, *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*, SPA 119(11), 2009, **Theorem 2.1**
  
  Verified via WebSearch on multiple sources (ScienceDirect, HAL archive, IDEAS/RePEc, Bouchard's own slides): the actual paper is **Bruno Bouchard & Romuald Elie**, "Discrete-time approximation of decoupled Forward–Backward SDE with jumps", *Stochastic Processes and their Applications*, **Volume 118, Issue 1**, **January 2008**, pp. 53–75. **No Touzi.**
- **Why this matters**: Misattribution of a paper title — adding an extra author, wrong volume/issue, wrong year — is a hard-to-fix problem if downstream papers/dissertations cite this Lean library as the source of authority for "BET 2009 Thm 2.1". Anyone trying to verify the cited theorem against the literature would chase a paper that doesn't exist. Mathlib reviewers would flag this on first sight. The dissertation forwarder (`Dissertation/Continuous.lean:419`) propagates the same misattribution.
- **Recommendation**: Replace all "Bouchard, Elie & Touzi 2009 SPA 119(11)" with "Bouchard & Elie 2008 SPA 118(1) pp. 53–75". Update `cited_axioms.md` Entry 10 and `Dissertation/Continuous.lean:419` accordingly.

### Finding 9 — `Compensated.itoLevyIsometry` / `L2Isometry.itoLevyIsometry` use `Measurable` hypothesis instead of "predictable"; isometry needs predictability not just product-σ measurability

- **Severity**: HIGH
- **Location**: `LevyStochCalc/Poisson/L2Isometry.lean:55–71`, `LevyStochCalc/Poisson/Compensated.lean:2794–2812`
- **Evidence**: `L2Isometry.lean` (lines 55–71), hypothesis on integrand:
  ```
  theorem itoLevyIsometry
      ...
      (φ : Ω → ℝ → E → ℝ)
      (T : ℝ) (hT : 0 < T)
      (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
      (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P < ⊤) :
      ∫⁻ ω, (‖LevyStochCalc.Poisson.Compensated.stochasticIntegral N φ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ...
  ```
  Same hypothesis structure in `Compensated.itoLevyIsometry`. Only "Measurable" (product-σ-algebra) is required, NOT "progressively measurable" or "predictable".
- **Why this matters**: Applebaum 2009 Thm 4.2.3 (the cited reference) requires `φ` to be **PREDICTABLE** — i.e., measurable for the predictable σ-algebra on `Ω × [0, T] × E`, which is strictly smaller than the product σ-algebra. The L²-isometry FAILS for non-predictable but measurable integrands (canonical example: `φ(s, ω, e) := W_{s+ε}(ω) − W_s(ω)` for `ε > 0` — measurable on the product σ-algebra, but the "integrand" depends on future, so the isometry fails because the simple-integrand approximation step doesn't apply). The Brownian analog `Brownian.SimplePredictableRefine.itoIsometry` does require `h_progMeas` (a progressive-measurability hypothesis, lines 2158–2163), so the asymmetry is across the Brownian-vs-Compensated cases. The Compensated side silently allows non-predictable integrands, which is mathematically wrong.
- **Recommendation**: Add `(h_progMeas : <some predictability constraint on φ>)` to `Compensated.itoLevyIsometry` and `L2Isometry.itoLevyIsometry`, mirroring the Brownian side. The progressive σ-algebra construction can be borrowed from `Brownian.SimplePredictableRefine`.

### Finding 10 — Module-docstring inconsistency: `BSDEJ/Definition.lean` admits "predicate slightly weaker than literature" but the audit-summary `cited_axioms.md:77` claims `continuousBSDEJ_exists_unique` is "no longer vacuously satisfiable" — the latter is true for existence but FALSE for uniqueness

- **Severity**: HIGH
- **Location**: `tools/cited_axioms.md:77`, vs `LevyStochCalc/BSDEJ/Definition.lean:60–64`
- **Evidence**: `cited_axioms.md:77`:
  > The strengthened predicate is no longer vacuously satisfiable by constant `Y` for generic `(f, g)`.
  
  vs `Definition.lean:60–64`:
  > The strengthened predicate is still slightly weaker than the literature (it doesn't pin `M_W` to be literally `∫ Z · dW`, only an isometric martingale), but it is non-vacuous: the literature solution satisfies it, and trivial constant `Y` does not.
  
  The docstring is honest about being weaker; the cited-axioms ledger is silent about the uniqueness weakness. Both are correct that trivial constant `Y` is excluded; neither says that NON-CONSTANT spurious solutions might also satisfy the predicate. (See Finding 6.)
- **Why this matters**: A downstream reviewer reading `cited_axioms.md` would infer the strengthening fully justifies the Tang–Li axiom. The actual situation is "existence is plausible; uniqueness is NOT IMPLIED by the predicate as written". This is a known issue (the docstring of `Definition.lean` admits it implicitly) but the cited-axioms ledger glosses over it.
- **Recommendation**: Update `cited_axioms.md:77` to explicitly state: "Existence is plausibly enforced; uniqueness is not fully justified by the predicate because `M_W` is constrained only by L²-isometry, not by being equal to `Brownian.stochasticIntegral W Z`. A further strengthening that threads `h_progMeas` through `IsBSDEJSolution` would pin `M_W` to the canonical Itô integral and recover uniqueness."

### Finding 11 — `MultidimBrownianMotion` structure does NOT require joint continuity of the d-dim path; components_independent uses cylinder σ-algebra independence which is correct but the structure lacks the natural d-dim filtration

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Brownian/Multidim.lean:36–47`
- **Evidence**: The structure (lines 38–47):
  ```
  structure MultidimBrownianMotion (P : Measure Ω) [IsProbabilityMeasure P]
      (d : ℕ) where
    W : Fin d → LevyStochCalc.Brownian.BrownianMotion P
    components_independent :
      ProbabilityTheory.iIndepFun
        (fun (i : Fin d) (ω : Ω) (t : ℝ) => (W i).W t ω) P
  ```
  The structure has `d` independent 1-D BMs and a path-space `iIndepFun` constraint. Each `(W i)` has `continuous_paths : ∀ᵐ ω ∂P, Continuous (W i).W t ω` (inherited from `BrownianMotion`), so each *component* path is a.s. continuous. By countable intersection, all `d` components are jointly a.s. continuous. So joint continuity DOES follow from componentwise continuity (since `Fin d` is finite). No actual missing structural constraint here.
  
  However, the structure does NOT carry a natural-filtration field for the d-dim case. Each 1-D `BrownianMotion` has `joint_increment_independent` (a σ-algebra-level independence claim, used to derive conditional-expectation identities). The d-dim `MultidimBrownianMotion` does not bundle the JOINT natural filtration of the d components, which is the right filtration for d-dim Itô integration. Downstream code (`BSDEJ/Definition.lean:125`) uses `∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›` — any filtration — instead of the natural one of `(W^1, ..., W^d, N)`.
- **Why this matters**: The literature d-dim Brownian Itô integral is defined w.r.t. the joint natural filtration. The Lean predicate `IsBSDEJSolution` lets the filtration be existentially chosen (Finding 6), which loses connection to `W`. The d-dim Brownian structure could carry the joint natural filtration as a field to avoid this; currently `MultidimBrownianMotion` is more anaemic than the 1-D `BrownianMotion`.
- **Recommendation**: Add `joint_natural_filtration : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›` and `joint_adaptedness : ∀ i, (W i).W is adapted to joint_natural_filtration` fields to `MultidimBrownianMotion`. Use this as the canonical filtration for downstream `IsBSDEJSolution` instead of existentially quantifying.

### Finding 12 — `PoissonRandomMeasure.independent_disjoint` allows any indexing type `ι : Type*` without constraint; for uncountable `ι`, `iIndepFun` may not match the standard PRM independence

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Poisson/RandomMeasure.lean:80–84`
- **Evidence**: The field (lines 80–84):
  ```
  independent_disjoint :
    ∀ {ι : Type*} (B : ι → Set (ℝ × E)),
      (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      ProbabilityTheory.iIndepFun (fun (i : ι) (ω : Ω) => N ω (B i)) P
  ```
  `ι : Type*` is unrestricted — any cardinality.
- **Why this matters**: The standard Poisson random measure independence is over PAIRWISE-DISJOINT *countable* (or finite) families. For uncountable index sets, the joint independence claim is non-standard and may or may not coincide with the σ-algebra independence one expects. Applebaum 2009 Thm 2.3.1 states the independence for finite families. Mathlib's `iIndepFun` for uncountable index sets is defined via "for every finite subfamily, the finite version holds" — so this is OK semantically, but redundant with the binary independence + closure under countable unions. Tighter to use `[Countable ι]` constraint.
- **Recommendation**: Add `[Countable ι]` to the `independent_disjoint` field hypothesis. Match Applebaum's finite/countable formulation.

### Finding 13 — `BSDEJData` structure has no measurability fields; downstream BSDEJ integral `∫ f` silently returns 0 for non-measurable `f`

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:78–82`
- **Evidence**: Structure definition:
  ```
  structure BSDEJData (n d : ℕ) (E : Type v) where
    f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ
    g : (Fin n → ℝ) → ℝ
  ```
  No `f_measurable`, no `g_measurable`, no `f_lipschitz` field.
- **Why this matters**: For pathological non-measurable `f`, the integral `∫ s in [t, T], f(s, X s ω, Y s ω, Z s ω, U s ω)` in `IsBSDEJSolution` (line 131–132) silently returns 0 (Lean's Bochner integral returns 0 for non-integrable functions). The BSDEJ equation then degrades to `Y t = g(X_T) − M_W − M_N` for any non-measurable `f`. This is a hidden inconsistency between the type signature and the mathematical content.
- **Recommendation**: Add `f_measurable : Measurable (Function.uncurry5 f)` (or whatever the right product-measurability is) and `g_measurable : Measurable g` as structure fields. Better: add Lipschitz constraint as a structure invariant. Then the axiom `continuousBSDEJ_exists_unique` would get measurability/Lipschitz for free from the type.

### Finding 14 — Internal cite "Gnoatto, *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, Theorem 2.2" is unverifiable; Gnoatto's 2022/2025 paper is on deep solvers not a primer

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/BSDEJ/Existence.lean:100–103`, `tools/cited_axioms.md:76`
- **Evidence**: From `Existence.lean:100–101`:
  > Gnoatto, A. *A primer on backward stochastic differential equations with jumps*, Quantitative Finance 25, 2025, Theorem 2.2;
  
  WebSearch finds Gnoatto's 2022/2025 paper "A deep solver for BSDEs with jumps" (arXiv:2211.04349) co-authored with Andersson, Patacca, Picarelli — published in Quantitative Finance. No paper titled "A primer on backward stochastic differential equations with jumps" by Gnoatto alone is findable. Dissertation `Continuous.lean:263` more honestly cites "Andersson-Gnoatto-Patacca-Picarelli 2025 arXiv:2211.04349 Thm 2.4".
- **Why this matters**: The Tang–Li 1994 primary citation IS verifiable; the Gnoatto "primer" secondary citation appears fabricated or misremembered. Either Gnoatto wrote a separate primer paper I can't find, or the citation should be replaced. Minor relative to the deeper finding that the AXIOM ITSELF lacks Lipschitz hypotheses.
- **Recommendation**: Replace "Gnoatto 2025 primer Thm 2.2" with "Andersson, Gnoatto, Patacca, Picarelli, 'A deep solver for BSDEs with jumps', arXiv:2211.04349, Thm 2.4" (the citation the dissertation already uses honestly) — or just drop the secondary cite and rely on Tang–Li 1994 + Pardoux–Răşcanu 2014.

### Finding 15 — Naming: `JumpDiffusion.exists_unique` does not prove uniqueness

- **Severity**: LOW
- **Location**: `LevyStochCalc/Ito/Setting.lean:85–93`
- **Evidence**: Signature `Nonempty (JumpDiffusion W N coeffs x₀)` — no uniqueness clause.
- **Why this matters**: A `_unique` suffix promises uniqueness; the theorem only delivers existence. Reader confusion + downstream code might assume uniqueness was proven and use a non-existent uniqueness lemma.
- **Recommendation**: Rename to `JumpDiffusion.exists` (drop `_unique`), or upgrade the conclusion to include uniqueness once the SDE constraint is genuinely encoded (per Finding 2).

## Per-claim verdicts on the 11 Tier 1 cited axioms + ~16 honest derivative theorems

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `BrownianMotion.exists` | EARNED | Documented cited axiom (Karatzas–Shreve Thm 2.1.5); honest existence claim. |
| `PoissonRandomMeasure.exists_of_sigmaFinite` | EARNED | Documented cited axiom (Applebaum Thm 2.3.1); minor structure-side issue on `Countable ι` (Finding 12). |
| `kolmogorovChentsov_modification` | OUT-OF-SCOPE-FOR-MY-LENS | Continuity theorem; not in BSDE/Lévy semantics path. |
| `brownian_martingale_rightCont` | OUT-OF-SCOPE-FOR-MY-LENS | Filtration augmentation; not the right lens. |
| `itoIsometry_brownian_unified_existence` | EARNED | Properly hypothesised (`h_meas`, `h_progMeas`, `h_sq_int_global`) — see SimplePredictableRefine.lean:2094. The unified 3-conjunct (martingale + quadVar + isometry) IS the canonical Karatzas–Shreve Thm 3.2.6 strong statement. |
| `itoIsometry_compensated_unified_existence` | **WEAK** | Trivial-witness-vulnerable for non-measurable / non-progressively-measurable `φ` because NO hypotheses on `φ` (Finding 7). Brownian analog has `h_meas/h_progMeas/h_sq_int`; Compensated does not. |
| `cauchySeq_simpleIntegralLp_compensated` | EARNED | Honest cited axiom; the underlying common-refinement lemma is a finite-sum calculation, this is just packaged as axiom pending mechanization. |
| `adaptedSimple_dense_L2_compensated` | EARNED | Honest cited axiom; the mark-dimension dyadic averaging is the missing piece, properly documented. |
| `continuousBSDEJ_exists_unique` | **TRIVIAL** (in strong sense — claims more than literature, mathematically false) | NO Lipschitz, NO L², NO measurability hypotheses on (f, g, X) — see Finding 4. Also, the strengthened `IsBSDEJSolution` predicate is *insufficient* for the uniqueness clause (Finding 6). |
| `bsdej_path_regularity` | **TRIVIAL** (projection-error content lost via existential `Z_avg, U_avg`) | `Z_avg`, `U_avg` existentially quantified — witness can pick them equal to `Z, U` (Finding 5). Plus citation misattribution (Finding 8). Plus no Lipschitz. |
| `itoLevyFormula` | **TRIVIAL** | The `∃ a b c d : Ω → ℝ, change = a + b + c + d` tautology (Finding 1). The "demotion" from `theorem` to `axiom` is cosmetic — statement is still the trivial pattern. |
| `MultidimBrownianMotion.exists` | WEAK | Definition is structurally correct (Finding 11 is a minor gap on bundled filtration); proof depends only on `BrownianMotion.exists`. |
| `brownian_continuous_modification` | OUT-OF-SCOPE-FOR-MY-LENS | KC modification consumer. |
| `brownian_martingale` | EARNED | Real proof in Martingale.lean:464; verified no Tier 1 axiom dependency (per audit output). |
| `brownian_quadVar` | EARNED | Real proof in Martingale.lean:696. |
| `brownian_filtration_rightContinuous` | OUT-OF-SCOPE-FOR-MY-LENS | Filtration property. |
| `Brownian.Ito.itoIsometry` | EARNED | Honest derivative of the Brownian unified-existence axiom; conjunct 3 extraction. |
| `Brownian.Ito.martingale_stochasticIntegral` | EARNED | Conjunct 1 extraction. |
| `Brownian.Ito.quadVar_stochasticIntegral` | EARNED | Conjunct 2 extraction. |
| `Compensated.itoLevyIsometry` | **WEAK** | Only `Measurable` (not predictability) hypothesis on `φ` (Finding 9). Inherits the Compensated unified-existence axiom's vulnerability (Finding 7). |
| `Compensated.martingale_stochasticIntegral` | WEAK | Same predictability gap. |
| `Compensated.quadVar_stochasticIntegral` | WEAK | Same. |
| `Compensated.cadlag_modification_exists` | WEAK | Same. |
| `L2Isometry.itoLevyIsometry` | WEAK | 1-line forwarder over `Compensated.itoLevyIsometry`; inherits all its weaknesses (Finding 9). |
| `JumpDiffusion.exists_unique` | **TRIVIAL** | `is_solution := True`; constant-path witness; no uniqueness clause; misleadingly named (Findings 2, 15). |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` | **TRIVIAL** | `⟨0, 0, 0, ξ − 𝔼ξ⟩; ring` — the exact trivial-witness pattern; NOT documented as such; NOT in `cited_axioms.md` (Finding 3). |

## Tools and sources used

- **Lean tools called**:
  - `mcp__lean-lsp__lean_verify` on `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique`, `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation`, `LevyStochCalc.Ito.JumpFormula.itoLevyFormula`, `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique`, `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity`, `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry`, `LevyStochCalc.Poisson.Compensated.itoLevyIsometry`.
  - `mcp__lean-lsp__lean_diagnostic_messages` on `Brownian/Multidim.lean`, `BSDEJ/Definition.lean` (both clean compile).
  - Grep over `Compensated.lean`, `SimplePredictableRefine.lean`, `Continuous.lean`.
  - Read on all 12 priority files in full + 4 in part (per Coverage section).
- **Web searches**:
  - "Applebaum 2009 Levy Processes Theorem 4.2.3 compensated Poisson stochastic integral isometry"
  - "Tang Li 1994 BSDE jumps necessary conditions optimal control predictable integrand"
  - "Bouchard Elie Touzi 2008 2009 discrete time approximation FBSDE jumps SPA path regularity theorem"
  - "Bouchard Elie Discrete time approximation decoupled Forward-Backward jumps 2008 SPA volume"
  - "Bruno Bouchard Romuald Elie Discrete-time approximation jumps 2008 authors"
  - "Gnoatto primer backward stochastic differential equations jumps Quantitative Finance 2025"
  - "Pardoux Rascanu Stochastic Differential Equations Backward SDEs Springer 2014 Theorem 4.79"
  - "Pardoux Rascanu 2014 BSDE chapter 5 theorem 5.42 jumps Poisson random measure"
  - "Karatzas Shreve Brownian Motion and Stochastic Calculus 1991 Theorem 3.2.6 Ito isometry martingale quadratic variation"
  - "Le Gall Brownian Motion Martingales and Stochastic Calculus 2016 Springer Theorem 5.13"
- **Web fetches**:
  - `https://epubs.siam.org/doi/abs/10.1137/S0363012992233858` (Tang & Li 1994 — confirmed title and topic).
  - `https://hal.science/hal-00015486` (blocked by Anubis security).
  - `https://link.springer.com/book/10.1007/978-3-319-05714-9` (redirected through Springer auth).
  - `https://www.sciencedirect.com/science/article/pii/S030441490700052X` (HTTP 403).
  - `http://ndl.ethernet.edu.et/.../BrownianMotionMartingalesAndSt.pdf` (binary PDF, unreadable).
  - `https://unina2.on-line.it/.../Karatzas,%20Shreve%20-%20Brownian%20motion%20and%20stochastic%20calculus.%202.%20ed..pdf` (binary PDF).
- **Papers consulted**:
  - Applebaum, D. (2009). *Lévy Processes and Stochastic Calculus*, 2nd ed., Cambridge UP. Chapters 2, 4, 6. (Cited reference for axioms 2, 6, 11; secondary background.)
  - Tang, S. & Li, X. (1994). *Necessary conditions for optimal control of stochastic systems with random jumps*. SIAM J. Control Optim. 32(5), 1447–1475. (Confirmed via web search.)
  - **Bouchard, B. & Elie, R. (2008)**. *Discrete-time approximation of decoupled Forward-Backward SDE with jumps*. SPA 118(1), 53–75. (CORRECTED reference; the Lean source says "Bouchard-Elie-Touzi 2009 SPA 119(11)" incorrectly — Finding 8.)
  - Karatzas, I. & Shreve, S. (1991). *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer. Chapter 3. (Cited reference for axioms 1, 3, 4, 5; could not verify exact theorem 3.2.6 statement from text-encoded PDF.)
  - Le Gall, J.-F. (2016). *Brownian Motion, Martingales, and Stochastic Calculus*. Springer GTM 274. (Cited reference; could not verify exact theorem 5.13 statement from PDF.)
  - Pardoux, E. & Răşcanu, A. (2014). *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*. Springer. (Cited as secondary reference; chapter contents confirmed.)

## What you couldn't verify

- Exact statement of Karatzas–Shreve Thm 3.2.6 (cited for `itoIsometry_brownian_unified_existence`): could not read the binary-encoded PDF online. Standard knowledge: §3.2 covers Itô integration; Thm 3.2.6 is plausible but I'd want to confirm the exact 3-conjunct form. Marked the axiom EARNED on the basis that the statement IS the right joint statement and the hypotheses are sound.
- Exact statement of Le Gall Thm 5.13: same PDF issue.
- Exact statement of Pardoux–Răşcanu Thm 4.79 / 5.42: Springer page redirected through authentication.
- Whether "Gnoatto, *A primer on backward SDEs with jumps*, Quantitative Finance 25, 2025, Thm 2.2" (cited at `Existence.lean:101`) is a real publication — appears fabricated or misremembered (Finding 14).
- Whether Applebaum's Thm 4.4.7 has any version weaker than the four-integral identity that could justify the additive existential form of `itoLevyFormula` — I do not believe such a weaker version exists in Applebaum, but did not directly access the 2009 book PDF beyond a Google Books preview.
- Whether the `Compensated` adapted-simple density axiom (Tier 1 #8) is robust to my predictability-vs-measurability concern (Finding 9) — the cited axiom assumes `progressively-measurable φ`, but downstream `Compensated.itoLevyIsometry` only requires `Measurable φ`, so there's a real type mismatch in the chain.

## Recommendations for the project (≤ 5 bullets)

- **Statement-level repairs (urgent)**: Fix the axiom statements of `continuousBSDEJ_exists_unique` (add Lipschitz / L² / measurability hypotheses), `bsdej_path_regularity` (replace existential `Z_avg, U_avg` with the named `conditionalTimeAverage_Z/U` from same file, add Lipschitz), and `itoLevyFormula` (constrain each existential to the literature integral form, not just to "real numbers summing to the change"). The current "fix" of demoting `itoLevyFormula` to `axiom` is cosmetic — the trivial statement remains. These are the four exposed forwarders of the dissertation; they're consumed by Mathlib reviewers and viva examiners.
- **Add `jacodYor_representation` to `cited_axioms.md` and either fix it or demote it**: it's a TRIVIAL theorem proved by `⟨0, 0, 0, ξ - 𝔼ξ⟩; ring`, not currently documented as such, not in the Tier 1 ledger. The recursive audit's standard says trivial-witness theorems are worse than documented axioms — this one slipped past.
- **Tighten the Compensated unified-existence axiom hypotheses**: add `h_meas`, `h_progMeas`, `h_sq_int` to mirror the Brownian-side axiom. Then `stochasticIntegral` becomes a 5-arg function and the `IsBSDEJSolution` M_N-pin becomes meaningful for the cases where `U` is actually progressively measurable + L²-finite.
- **Encode the SDE constraint in `JumpDiffusion.is_solution`**: replace `is_solution : True` with the literature `X_t = x₀ + ∫μ ds + ∫σ dW + ∫∫γ dÑ`. This kills the constant-path trivial inhabitant of `JumpDiffusion` and gives downstream `itoLevyFormula` something non-vacuous to apply to.
- **Citation hygiene**: fix "Bouchard, Elie & Touzi 2009 SPA 119(11)" → "Bouchard & Elie 2008 SPA 118(1)" in `PathRegularity.lean`, `cited_axioms.md`, and `Dissertation/Continuous.lean`. Verify or replace the Gnoatto 2025 "primer" citation. Confirm the Karatzas–Shreve / Le Gall theorem numbers against the actual book texts; right now they're plausible but unverifiable from web sources.
