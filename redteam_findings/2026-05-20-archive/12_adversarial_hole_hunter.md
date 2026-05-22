# Red Team Audit: Adversarial Proof-Hole Hunter (Persona 12)

**Auditor lens**: Adversarial reviewer who reads proofs the way a security researcher reads code, looking for trivial witnesses, vacuous existentials, predicate-inversion exploits, and silent conclusion weakenings that let headline theorems be discharged without doing the literature work.
**Date**: 2026-05-20
**Coverage**: 14 Lean files read in full (`LevyStochCalc.lean`, `Brownian/Construction.lean`, `Brownian/Continuity.lean`, `Brownian/Martingale.lean`, `Brownian/Multidim.lean`, `Brownian/SimplePredictableRefine.lean`, `Brownian/Ito.lean` (in chunks: lines 1–100, 1620–1710, 2770–2820, 3470–3550, 3960–4060), `Poisson/RandomMeasure.lean`, `Poisson/Compensated.lean` (in chunks: lines 1840–2120, 2240–2330, 2540–2620, 2700–2890), `Poisson/L2Isometry.lean`, `Ito/Setting.lean`, `Ito/JumpFormula.lean`, `BSDEJ/Definition.lean`, `BSDEJ/MartingaleRepresentation.lean`, `BSDEJ/Existence.lean`, `BSDEJ/PathRegularity.lean`); 4 inventory/audit files read in full (`tools/cited_axioms.md`, `tools/full_audit.lean`, `tools/full_audit_output.txt`, `Dissertation/Continuous.lean`); 4 mandatory framing files read in full.

## Executive summary (≤ 3 sentences)

The recursive audit on 2026-05-11 caught two of the headline trivial-witness defects (`itoLevyFormula` demoted, `IsBSDEJSolution` outer-existential strengthening) but **left at least six independent holes in place**: (a) `continuousBSDEJ_exists_unique` asserts uniqueness UNIVERSALLY OVER `BSDEJData` with no Lipschitz / no adaptedness on `(Y,Z,U)`, and a concrete two-distinct-solutions counterexample falsifies it for `(f=0, g=0)`; (b) `JumpDiffusion.exists_unique` is a fake `Nonempty` theorem (no uniqueness, `is_solution : True`), letting `itoLevyFormula`'s `X` parameter be the constant path with no SDE content; (c) `jacodYor_representation` is a `⟨0, 0, 0, ξ − 𝔼ξ⟩` trivial-witness `theorem` not even classified as a cited axiom; (d) the Compensated unified-existence axiom binds `φ` with no measurability hypothesis, allowing conjuncts 1+2+4 to be discharged by `F ≡ 0` whenever conjunct 3's measurability conditional is false; (e) `adaptedSimple_dense_L2_compensated`'s docstring says "progressively-measurable" but the axiom binds `φ` with only joint measurability — strictly stronger than Applebaum 4.2.2; (f) `tools/sorry_baseline.txt` is empty but `Poisson.Compensated.simplePredictable_dense_L2` (public, non-private) has `sorryAx` in its axiom set, refuting `cited_axioms.md`'s "No sorryAx anywhere in the public API" claim. The previous recursive audit's strengthening of `IsBSDEJSolution` only blocked the inner-`(t,ω)`-real existential route; the predicate is still satisfiable by non-adapted Y derived from any L² Brownian-stochastic-integral martingale, contradicting the cited axiom's uniqueness assertion.

## Top findings (ranked by severity, highest first)

### Finding 1 — `continuousBSDEJ_exists_unique` is mathematically FALSE as a Lean axiom: for `(f=0, g=0)` data, multiple distinct `IsBSDEJSolution`-satisfying triples exist, so the asserted ∀-uniqueness clause is unsatisfiable (adding the axiom postulates a false statement)

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:113-126` (axiom statement); the satisfying-but-different triples use `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean:91-133` predicate.
- **Evidence**:

The axiom statement (verbatim, `Existence.lean:113-126`):
```lean
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

**Concrete falsifier** (no Lean rewrite required — purely a mathematical counterexample showing the axiom asserts a false ∃-∀ statement):

Take `bsdej : BSDEJData n d E` with `bsdej.f := fun _ _ _ _ _ => 0` and `bsdej.g := fun _ => 0`. Take any `X` jointly measurable, `d ≥ 1` so a Brownian component `W₁ := (W.W 0)` exists. Take `T > 0`.

**Solution A** (the trivial constant): `Y_A t ω := 0`, `Z_A s ω i := 0`, `U_A s ω e := 0`. With `M_W := 0`, `M_N := 0`, `Filt := arbitrary`, every `IsBSDEJSolution` conjunct holds (zero L² norms; zero martingales; `M_N = Compensated.stochasticIntegral N 0 = 0 a.s.` because the unified-existence axiom's conjunct-3 isometry fires on the zero integrand and forces `‖F T'‖² = 0` for every `T' > 0`; BSDEJ equation reduces to `0 = 0`).

**Solution B** (BM-integral): `Y_B t ω := W₁.W T ω - W₁.W t ω`, `Z_B s ω i := if i = 0 then 1 else 0`, `U_B s ω e := 0`. Take `M_W^B := fun s ω => -(W₁.W s ω)` and `M_N^B := 0`, `Filt^B := naturalFiltration W₁`. Verify:
- L²(sup-of-Y) finite: by Doob's L² maximal, `𝔼[sup_{t∈[0,T]} (W₁_T − W₁_t)²] ≤ 4 𝔼[(W₁_T − W₁_0)²] = 4T < ∞`. ✓
- L²(Z_B) = `T < ∞`. ✓
- L²(U_B) = 0 < ∞. ✓
- L²-isometry of `M_W^B = -W₁` against `Z_B`: `𝔼[(W₁_{T'})²] = T'` (Gaussian variance) `= 𝔼[∫_0^{T'} 1 ds]`. ✓
- `M_N^B = 0 = Compensated.stochasticIntegral N 0` (a.s.). ✓
- Martingale of `-W₁` and `0` wrt `naturalFiltration W₁`: standard. ✓
- BSDEJ equation: `Y_B t ω = 0 + ∫_t^T 0 − (M_W^B T − M_W^B t) − 0 = -(-(W₁_T - W₁_t)) = W₁_T - W₁_t = Y_B t ω`. ✓

Both `Solution A` and `Solution B` satisfy `IsBSDEJSolution W N {f:=0, g:=0} X · · · T`, but `Y_A = 0 ≠ W₁_T - W₁_t = Y_B` (on a positive-measure subset of `Ω`, since `W₁` is genuine Brownian motion with positive variance).

For the axiom's `∃ Y, ∀ Y', sol Y' → Y = Y'` to hold, `Y` would have to equal both `0` and `W₁_T − W₁_t` a.s., which is impossible.

`mcp__lean-lsp__lean_verify` on `Dissertation.Continuous.continuousBSDEJ_exists_unique` confirms the axiom set includes only `propext, Classical.choice, Quot.sound, LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique` — no Lipschitz / no L² hypothesis — and the type signature shown by `#check` is exactly as above (no `Lipschitz bsdej ν L` parameter anywhere).

- **Why this matters**: Postulating a false statement as an axiom makes the project's logic inconsistent. From `continuousBSDEJ_exists_unique W N {0,0} X T hT`, one extracts a `Y` such that `∀ Y' Z' U', IsBSDEJSolution Y' Z' U' → ∀ t, ∀ᵐ ω, Y t ω = Y' t ω`. Apply this with both `Y' := 0` (giving `Y t ω = 0 a.s.`) and `Y' := fun t ω => W₁.W T ω − W₁.W t ω` (giving `Y t ω = W₁_T − W₁_t a.s.`). These force `0 = W₁_T − W₁_t a.s.`, but `(W₁_T - W₁_0)² = W₁_T²` has expectation `T > 0`, so it is NOT a.s. zero. We have derived `0 = W₁_T a.s.` which contradicts `gaussianReal 0 ⟨T, _⟩` having positive variance — i.e., contradicts `BrownianMotion.increment_gaussian`. The library is inconsistent (subject to the existence of a genuine multidim BM, which is itself axiomatised; the inconsistency is therefore a `False`-derivation **conditional on the Tier 1 axiom inventory**).
- **Recommendation**: This is the single most important fix. Three options, in order of preference:
  1. Add explicit Lipschitz + L² + adaptedness hypotheses to `continuousBSDEJ_exists_unique` matching Tang-Li 1994 (Lipschitz `f` in `(y,z,u)`, `𝔼[g(X_T)²] < ∞`, `(Y,Z,U)` adapted to `naturalFiltration (W, N)`). Strengthen `IsBSDEJSolution` to require adaptedness (P5#1, P4#2 cover this).
  2. Failing that, demote the axiom to a stub `True := trivial` lemma until the hypotheses are added, matching the `itoLevyFormula` precedent.
  3. At minimum, add a `Lipschitz bsdej ν L` hypothesis (already defined at `Existence.lean:67-73` but threaded through nothing) and an `𝔼[g(X T)²] < ⊤` hypothesis.

---

### Finding 2 — `Ito.Setting.JumpDiffusion.exists_unique` is a fake existence theorem hiding a TRIVIAL SDE constraint (`is_solution : True`), and it is the parameter that makes `itoLevyFormula` discharge against the constant path

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Ito\Setting.lean:50-72` (structure) and `:85-112` (theorem)
- **Evidence**:

Structure definition (`Setting.lean:71-72`):
```lean
  /-- The SDE itself: stubbed, since the integrals along `X` require Phase 3
  development. -/
  is_solution : True
```

Theorem (`Setting.lean:85-112`):
```lean
theorem JumpDiffusion.exists_unique ... :
    Nonempty (JumpDiffusion W N coeffs x₀) := by
  refine ⟨{
    X := fun _ _ => x₀
    measurable_path := measurable_const
    initial_value := Filter.Eventually.of_forall (fun _ => rfl)
    sup_L2 := ?_
    is_solution := trivial
  }⟩
  ...
```

`mcp__lean-lsp__lean_verify` returns `{"axioms":["propext","Classical.choice","Quot.sound"]}` — zero Tier 1 dependency, confirming the theorem is vacuous.

Three independent defects compound:
1. The conclusion is `Nonempty (...)`, **not** `∃! ...`, despite the name `exists_unique` (P5#2, P7#15, P4#3 cover this naming issue).
2. The structure's only SDE field is `is_solution : True`. The constant path `X t ω = x₀` trivially has `(X T, U)` satisfy the literal field (which says nothing).
3. **The chain to `itoLevyFormula`**: `Ito.JumpFormula.itoLevyFormula` takes `X : JumpDiffusion W N coeffs x₀` as a parameter (`JumpFormula.lean:98`). Because `JumpDiffusion` has no SDE constraint, `X` can be the constant-path witness produced by `JumpDiffusion.exists_unique`. The "Itô-Lévy formula" axiom then claims existence of `(drift, diff, jump, comp)` summing to `u(T, x₀) − u(0, x₀)` for this constant path — which is trivially `⟨u(T, x₀) − u(0, x₀), 0, 0, 0⟩`. **Neither side of the formula carries any literature content.**

- **Why this matters**: This is the same pattern the recursive audit caught in `itoLevyFormula` (proof body was `⟨0, 0, 0, change⟩; simp`) and demoted. But the demotion targeted only the **proof body**; the demoted axiom **statement** is itself satisfied by `⟨change, 0, 0, 0⟩`. The `JumpDiffusion.exists_unique` theorem is the upstream enabler: it lets downstream code feed a constant path into `itoLevyFormula` without ever engaging Applebaum 6.2.9 or any actual SDE solver. The dissertation's red-team note (`Continuous.lean:46-53`) admits this for `itoLevyFormula` and `bsdej_path_regularity` directly; it does not flag `JumpDiffusion.exists_unique` as the structural enabler.
- **Recommendation**: Either (a) replace `is_solution : True` with a real SDE predicate using `Brownian.SimplePredictableRefine.stochasticIntegral W (σ ∘ X)` + `Poisson.Compensated.stochasticIntegral N (γ ∘ X)`, and demote `JumpDiffusion.exists_unique` to a cited axiom (Applebaum 6.2.9), OR (b) keep `is_solution : True` but make `JumpDiffusion` package the SDE predicate as a separate field with proper `noncomputable def isSolution := ...` and re-prove existence. Without one of these, the entire `itoLevyFormula` axiom-with-citation chain is decorative.

---

### Finding 3 — `BSDEJ.MartingaleRepresentation.jacodYor_representation` is a `theorem` with the exact trivial-witness pattern that got `itoLevyFormula` demoted; it is NOT classified as a Tier 1 cited axiom and is silently consumed downstream

- **Severity**: CRITICAL
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\MartingaleRepresentation.lean:55-85`
- **Evidence** (proof body, lines 73-84, verbatim):
```lean
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

`mcp__lean-lsp__lean_verify` on `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` returns `{"axioms":["propext","Classical.choice","Quot.sound"]}` — confirming it is axiom-free, hence trivially provable.

This is **the identical pattern** to the demoted `itoLevyFormula`: four-existential, three zeros + one stuffed term, `ring`-discharged. The Jacod 1976 / Yor representation theorem requires `Z` to be the predictable projection of `dM/dW` and `U` to be the projection of `dM/dN`, with `BM_integral = ∫ Z dW` and `jump_integral = ∫∫ U Ñ`. The Lean statement enforces none of these — `BM_integral` and `jump_integral` are arbitrary `Ω → ℝ` functions, and the L² conditions trivially hold for the zero choices.

`jacodYor_representation` is imported by `BSDEJ/Existence.lean` (`import LevyStochCalc.BSDEJ.MartingaleRepresentation`) but the existence axiom doesn't actually call it — yet its docstring claims it "accounts for ≈ a third of Cu01's proof effort" (`MartingaleRepresentation.lean:16-17`). It is also not listed in `tools/cited_axioms.md`'s "Honest derivative theorems" table (lines 99-111), nor classified as Tier 1, nor flagged in the 2026-05-11 recursive audit's internal classification table at `cited_axioms.md:124-132`.

- **Why this matters**: This is a fake theorem with a strong-sounding name that survived the previous recursive audit because the audit only scanned the four headline forwarders (`itoLevyIsometry`, `continuousBSDEJ_exists_unique`, `itoLevyFormula`, `bsdej_path_regularity`). The classification table missed `jacodYor_representation`. The `tools/full_audit_output.txt:94-96` shows its axiom set as Lean-std only, which by the project's own rule ("no trivial-witness theorems remain") should have triggered demotion. Either (a) `jacodYor_representation` should be demoted to an `axiom` referencing Jacod 1976, OR (b) its conclusion needs to constrain `BM_integral = ∫ Z dW`, `jump_integral = ∫∫ U Ñ` (via the LevyStochCalc Brownian + Compensated stochasticIntegral primitives).
- **Recommendation**: Demote to a Tier 1 cited axiom (Jacod 1976 / Yor 1976 multivariate point process representation). Add the new entry to `tools/cited_axioms.md` and `tools/full_audit.lean`. Mirror the `itoLevyFormula` 2026-05-11 demotion pattern.

---

### Finding 4 — `Poisson.Compensated.simplePredictable_dense_L2` is a non-private public lemma with `sorryAx` in its axiom set, refuting `tools/cited_axioms.md`'s "No `sorryAx` anywhere in the public API" claim AND the empty `tools/sorry_baseline.txt`

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean:1903` (the `lemma`, public — no `private` keyword); the sorry it depends on is `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean:1893` (`private lemma simplePredictable_dense_L2_bounded`).
- **Evidence**:

`mcp__lean-lsp__lean_verify` on `LevyStochCalc.Poisson.Compensated.simplePredictable_dense_L2` returns:
```json
{"axioms":["propext","sorryAx","choice","Quot.sound"]}
```

The dependency chain:
- `simplePredictable_dense_L2` (public, `Compensated.lean:1903`) calls `simplePredictable_dense_L2_bounded` at line 1936:
  ```lean
    fun M => simplePredictable_dense_L2_bounded hT
      (fun ω s e => max (-(M : ℝ)) (min (M : ℝ) (φ ω s e)))
      (h_clip_meas M) (M : ℝ) (h_clip_bound M)
  ```
- `simplePredictable_dense_L2_bounded` (private, line 1880) has the body:
  ```lean
    -- Chain assembly per Steps 1-5. See chain documentation above.
    sorry
  ```

Three other `sorry`s exist in the source:
- `Brownian/Continuity.lean:184` (`kolmogorov_modification_ae_eq`, public lemma) — has `sorryAx`
- `Brownian/Ito.lean:3984` (`quadVar_simpleIntegral_brownian`, private lemma)
- `Poisson/RandomMeasure.lean:139` (`poissonRandomMeasure_finite_exists`, public lemma) — has `sorryAx`

`cited_axioms.md:113-115`:
> `tools/sorry_baseline.txt` is **empty**. Every previously sorry'd theorem is either:
> * Proven from Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`) plus possibly one or more Tier 1 cited axioms documented here, OR
> * A Tier 1 cited axiom itself.

This claim is FALSE for three public lemmas (`Poisson.Compensated.simplePredictable_dense_L2`, `Brownian.Continuity.kolmogorov_modification_ae_eq`, `Poisson.poissonRandomMeasure_finite_exists`), each carrying `sorryAx` directly. `tools/sorry_baseline.txt` being empty is technically vacuously true (it lists nothing), but the surrounding claim that nothing in the public API has `sorryAx` is contradicted by these three.

- **Why this matters**: A Mathlib reviewer reading `cited_axioms.md` and `tools/full_audit_output.txt` would conclude the library has zero `sorry`-tainted lemmas in its public surface. Three exist. The full_audit.lean only `#print axioms` the 21 specifically-listed theorems; it does not scan all public lemmas. The honest claim would be: "The 11 Tier 1 axioms + the ~16 honest derivative theorems listed in this file are sorry-free; other public lemmas may carry sorryAx pending future development." Better still: add the sorry'd lemmas to `tools/sorry_baseline.txt` as documented carry-overs.
- **Recommendation**: Either (a) mark the four `sorry`'d lemmas as `private`, OR (b) extend `tools/sorry_baseline.txt` to list them with citations to their literature proofs, OR (c) update `cited_axioms.md:113-115` to accurately reflect the current state. Either way, the "No sorryAx in public API" guarantee is currently misleading.

---

### Finding 5 — `itoIsometry_compensated_unified_existence` axiom binds `φ` with NO measurability/predictability hypothesis at the existential level; for arbitrary `φ`, the entire 4-conjunct conjunction can be discharged by `F ≡ 0` whenever conjunct 3's measurability conditional is false

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean:2748-2767`
- **Evidence** (verbatim):
```lean
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
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Ioi t)) (nhds (F t ω))
          ∧ ∃ L : ℝ,
              Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
```

Two structural defects:

1. **`φ` is bound with no `h_meas` / no `h_progMeas` / no `h_sq_int`**. Contrast with the Brownian analog `itoIsometry_brownian_unified_existence` (`SimplePredictableRefine.lean:2094-2107`) which binds `h_meas, h_progMeas, h_sq_int_global` at the existential level. The Compensated axiom moves `h_meas` and `h_sq_int` inside conjunct 3 as a conditional implication. For `φ` non-measurable, the conditional `Measurable (...) → ∫⁻ ‖φ‖² < ⊤ → ...` is vacuously satisfied (false hypothesis ⟹ anything), so conjunct 3 imposes NO constraint on `F`.

2. **The literature statement (Applebaum 4.2.3 + 4.2.4) is for PREDICTABLE square-integrable integrands**, NOT arbitrary `φ : Ω → ℝ → E → ℝ`. The axiom drops predictability entirely (it isn't even in the docstring as a hypothesis on the function — the docstring at line 2712 says "predictable square-integrable" but the Lean signature drops it).

**Concrete exploit construction**:
For ANY φ violating either (a) joint Ω×ℝ×E measurability, OR (b) finite triple-lintegral over [0,T] for every T, the conjunct-3 isometry implication is vacuous. The remaining conjuncts 1, 2, 4 are jointly satisfied by `F ≡ 0` paired with `Filt := constant trivial filtration` provided that `(F t ω)² − ∫_0^t ∫_E (φ ω s e)² ν(de) ds = −∫_0^t ∫_E (φ ω s e)² ν ds` is a martingale wrt the trivial filtration. If `φ` is such that `∫_E (φ ω s e)² ν(de)` defaults to `0` (e.g., φ-squared is not Bochner-integrable in `e` per Mathlib convention `MeasureTheory.integral_undef`), then `∫_0^t 0 ds = 0` and conjunct 2 reads `0 = 0`, trivially a martingale.

The Mathlib convention `MeasureTheory.integral_undef : ¬ Integrable f μ → ∫ x, f x ∂μ = 0` (verified at `mcp__lean-lsp__lean_run_code`) makes this exploit non-hypothetical. Take `φ ω s e := f(ω, s, e)` where `f²` is not Bochner-integrable in `e` against `ν` — e.g., `ν = volume` on `E = ℝ` and `f² = 1` (not L¹). Then `∫ e, (φ ω s e)² ∂ν = ∫ e, 1 ∂volume = 0` (by `integral_undef` since `1 ∉ L¹(volume)` on `ℝ`). Conjunct 2 holds with `F ≡ 0`.

For this same `φ`, the conjunct 3 isometry implication's premise `∫⁻ ω ∫⁻ s ∫⁻ e (‖φ‖₊)² ∂ν ∂volume ∂P < ⊤` is FALSE (the lintegral is `∞ · vol[0,T] · 1 = ∞`), so conjunct 3 is vacuous.

So the unified-existence axiom is satisfied by `(F ≡ 0, Filt := trivial)` for this non-L²-on-volume `φ`. Downstream, `Compensated.stochasticIntegral N φ T = Classical.choose (axiom) T ω = 0` a.s. (or undefined depending on the choose). The "canonical L²-Itô-Lévy integral" of this `φ` is then **0**, not the actual compensated integral.

- **Why this matters**: Combined with Finding 1, the BSDEJ predicate's pin `M_N = Compensated.stochasticIntegral N (fun ω' s e => U s ω' e)` allows `M_N = 0` to satisfy the predicate for **any** non-L² `U`. So Finding 1's two-solutions counterexample can be extended to non-zero `f, g` if `U` is chosen to fail L²-on-ν integrability — the predicate then admits more degenerate witnesses than even `f = g = 0` admits. The Brownian-side axiom binds `h_meas, h_progMeas, h_sq_int_global` correctly; the asymmetry is a known mismatch (P5#6, P7#7 cover the basic gap, but neither traces the downstream consequence through `Compensated.stochasticIntegral`'s Classical.choose to the BSDEJ predicate's pin).
- **Recommendation**: Bind `h_meas` and `h_sq_int` (per-`T`, like the Brownian axiom does globally) at the existential level of `itoIsometry_compensated_unified_existence`. Add a predictability hypothesis (e.g., `h_progMeas` against the natural filtration of `N`). The asymmetry with the Brownian axiom is presumably an oversight from when this axiom was lifted out of the per-`T` existential.

---

### Finding 6 — `adaptedSimple_dense_L2_compensated`'s docstring claims "progressively-measurable" but the Lean signature only requires joint measurability — strictly stronger claim than Applebaum 2009 Lemma 4.2.2 proves, hence the axiom is overstated relative to its citation

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean:2550-2606`
- **Evidence**:

Docstring (`Compensated.lean:2552-2554`):
```
For **progressively-measurable** `φ : Ω → ℝ → E → ℝ` with finite L² norm on `[0, T]`,
there exists a sequence of ADAPTED simple predictables `Hn` ...
```

Lean axiom signature (`Compensated.lean:2579-2606`):
```lean
axiom adaptedSimple_dense_L2_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    {T : ℝ} (hT : 0 < T)
    (φ : Ω → ℝ → E → ℝ)
    (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))   -- ← only joint measurability
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ G : ℕ → SimplePredictable Ω E ν T,
      ...
      (∀ n : ℕ, ∀ i : Fin (G n).N,
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic ((G n).partition i.castSucc) ×ˢ Set.univ
                                      ∧ MeasurableSet C },
            MeasurableSpace.comap (fun ω => N.N ω B) inferInstance) ((G n).ξ i)) ∧
      ...
```

The signature binds only `h_meas : Measurable (fun p => φ p.1 p.2.1 p.2.2)` — joint measurability in `Ω × ℝ × E`. This is **strictly weaker** than progressive measurability against the natural filtration of `N` (which the docstring claims and Applebaum 4.2.2 requires).

For a joint-but-not-progressively-measurable `φ` (e.g., `φ ω s e := 𝟙[s ≤ τ(ω)]` for `τ` a non-stopping time), the literature does NOT guarantee approximation by **adapted** simple predictables — only by some L² approximation. The axiom claims approximation by adapted simples for arbitrary jointly-measurable `φ`, which is mathematically false.

- **Why this matters**: This is the same docstring-vs-signature mismatch as in Finding 5. A user (or Mathlib reviewer) reading the docstring would conclude the axiom matches Applebaum 4.2.2; reading the signature, they would see the axiom claims more than Applebaum 4.2.2 proves. For non-progressive `φ`, the axiom postulates the existence of adapted approximations that the literature does not provide.
- **Recommendation**: Add a progressive measurability hypothesis to the axiom binding (matching the docstring), e.g., `(h_progMeas : ∀ t, @StronglyMeasurable (Ω × ℝ × E) ℝ _ (Prod.instMeasurableSpace (Prod.instMeasurableSpace ...)) ...)`. Without this, downstream `Compensated.stochasticIntegral` constructions inherit a falsehood about which integrands admit adapted-simple approximations.

---

### Finding 7 — `bsdej_path_regularity` axiom's `∃ Z_avg U_avg` is existentially quantified, allowing `Z_avg := Z`, `U_avg := U` (the trivial choice making the error terms zero), so the axiom's "projection error ≤ C·Δt" content is satisfiable without any approximation

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\PathRegularity.lean:111-139`
- **Evidence** (axiom body, lines 131-139):
```lean
        let Δt : ℝ := ⨆ n : Fin M,
          partition n.succ - partition n.castSucc
        ∃ (Z_avg : ℝ → Ω → (Fin d → ℝ)) (U_avg : ℝ → Ω → E → ℝ),
          (⨆ n : Fin M, ∫⁻ ω,
            ⨆ t ∈ Set.Icc (partition n.castSucc) (partition n.succ),
              (‖Y t ω - Y (partition n.castSucc) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              ∑ i, (‖Z s ω i - Z_avg s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖U s ω e - U_avg s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
          ≤ ENNReal.ofReal (C * Δt)
```

The axiom asserts `∃ Z_avg U_avg, [Y-modulus + Z-projection-error + U-projection-error] ≤ C·Δt`.

**Take `Z_avg := Z` and `U_avg := U` (the trivial choice).** Then:
- `Z s ω i − Z_avg s ω i = 0`, so the Z-projection-error term is `∫⁻ ∫⁻ 0 ds dP = 0`.
- Same for U.

The bound reduces to `[Y-modulus over partition] ≤ C · Δt`.

For `(Y, Z, U) = (0, 0, 0)` (the trivial solution of `f = g = 0`), the Y-modulus term is also 0. So the bound is `0 ≤ C · Δt`, which holds for ANY `C > 0` and `Δt > 0`. The axiom is satisfied with `C := 1`.

P7#5 caught the bare fact that `Z_avg, U_avg` are existentially quantified. The downstream consequence: the bound has NO content for the trivial solution, hence cannot detect violations of the BET 2008 / 2009 projection-error bound when applied to trivial witnesses.

The literature statement (Bouchard-Elie 2008 SPA 118(1) Thm 2.1) is that `Z_avg`, `U_avg` are the **specific conditional time-averages** (the operators `conditionalTimeAverage_Z`, `conditionalTimeAverage_U` defined in `PathRegularity.lean:62-83`), NOT existentially quantified. The Lean axiom drops the specific operator and existentially-quantifies, losing the content.

- **Why this matters**: A Mathlib reviewer or downstream user might assume the bound constrains `Z` against its conditional time-average. It does not — it constrains `Z` against ANY `Z_avg` they happen to pick. This is a silent weakening from the literature claim. Combined with Finding 1's non-uniqueness and Finding 2's trivial JumpDiffusion, the path-regularity axiom's substantive content is unrecoverable from its current form.
- **Recommendation**: Replace `∃ Z_avg U_avg, ...` with `Z_avg := conditionalTimeAverage_Z partition Z, U_avg := conditionalTimeAverage_U partition U` (the operators already defined). The bound then bites against the literature operators.

---

### Finding 8 — `IsBSDEJSolution`'s inner `∃ Filt` allows the constant trivial filtration `Filt _ := ⊤` (the full σ-algebra), under which every measurable function is trivially a martingale — so the "martingale wrt common filtration" conjunct is vacuous

- **Severity**: HIGH
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean:125-127`
- **Evidence** (verbatim, embedded inside the outer `∃ M_W M_N`):
```lean
        -- M_W and M_N are martingales w.r.t. a common filtration:
        (∃ Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
          MeasureTheory.Martingale M_W Filt P ∧
          MeasureTheory.Martingale M_N Filt P) ∧
```

The `Filt` is existentially quantified with no constraint beyond being a `Filtration ℝ ‹MeasurableSpace Ω›`. A filtration is by definition monotone and bounded by the ambient `MeasurableSpace Ω`. The constant filtration `Filt _ := ⊤` (the full σ-algebra) is a valid `Filtration`. Under this filtration:
- `𝔼[M_W t | Filt s] = M_W t` (since M_W t is `Filt s`-measurable, being measurable wrt `⊤`).
- The martingale identity `𝔼[M_W t | Filt s] = M_W s` then says `M_W t = M_W s` for s ≤ t.

So under `Filt = const ⊤`, the martingale conjunct forces `M_W` and `M_N` to be **constant in t** (a.s.). This is a very weak constraint, but it IS a constraint — it's not VACUOUS in the strict sense.

However, **the literature requires the filtration to be `(W, N)`-augmented**, i.e., the natural filtration of the driving processes. The Lean predicate has no such constraint. So `M_W` and `M_N` can be martingales wrt any filtration whatsoever — including filtrations under which the constant-Y trivial solution (Finding 1, Solution A) is a martingale.

For Solution A `(M_W = 0, M_N = 0)`, the constant filtration `Filt = const ⊤` makes both `0`-martingales trivially.

For Solution B `(M_W = -W₁, M_N = 0)`, the filtration `Filt = naturalFiltration W₁` makes `-W₁` a martingale.

Both solutions exhibit different filtrations. The predicate's inner `∃ Filt` accepts both.

This is a related-but-distinct issue from Finding 1: even adding adaptedness on `(Y, Z, U)` would not fix this, because `M_W, M_N` could use a DIFFERENT filtration than the `(Y, Z, U)` adaptedness filtration. The right structure is: a SINGLE `Filt` parameter to the predicate, with `(Y, Z, U)` adapted to `Filt`, `M_W, M_N` martingales wrt `Filt`, AND `Filt` ⊇ `naturalFiltration(W, N)` (so the BM and PRM information is in the filtration).

P5#1 recommendation point 4 is in this direction; my finding sharpens the diagnostic — it is not just that adaptedness is missing, but that the filtration is ALSO existentially quantified, doubling the freedom.

- **Why this matters**: Finding 1's non-uniqueness uses two solutions with DIFFERENT filtrations. The current predicate accepts this. The literature would require both solutions to use the same `(W, N)`-augmented filtration; under that constraint, only Solution A would be valid (Solution B's `M_W = -W₁` requires the natural filtration of `W`, which is finer than what `Solution A` uses).
- **Recommendation**: Lift `Filt` out of the inner existential into a parameter of the predicate (or fix it to `naturalFiltration W N`). Require `(Y, Z, U)` adapted to `Filt` and `M_W, M_N` martingales wrt the same `Filt`. The filtration ambiguity is independently exploitable.

---

### Finding 9 — `Lipschitz` predicate is defined in `BSDEJ/Existence.lean:67-73` but THREADED THROUGH NOTHING; `picardMap_contraction` (`Existence.lean:80-91`) takes a `_hL : Lipschitz` hypothesis but returns `True`, and `continuousBSDEJ_exists_unique` does not take `Lipschitz` as a hypothesis at all — the dead-code pattern is symptomatic of the missing Lipschitz hypothesis the axiom needs

- **Severity**: MEDIUM
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:67-73`, `:80-91`, `:113-126`
- **Evidence**:

Lipschitz definition (`Existence.lean:67-73`):
```lean
def Lipschitz {n d : ℕ}
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (ν : Measure E) (L : ℝ) : Prop :=
  ∀ s : ℝ, ∀ x : Fin n → ℝ, ∀ y₁ y₂ : ℝ, ∀ z₁ z₂ : Fin d → ℝ, ∀ u₁ u₂ : E → ℝ,
    |bsdej.f s x y₁ z₁ u₁ - bsdej.f s x y₂ z₂ u₂|
      ≤ L * (|y₁ - y₂| + ‖z₁ - z₂‖
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal.sqrt)
```

Dead-end use site (`Existence.lean:80-91`):
```lean
lemma picardMap_contraction ... (_hL : Lipschitz bsdej ν L) :
    -- placeholder for the contraction inequality
    True := trivial
```

Axiom statement (`Existence.lean:113-126`) does NOT take `Lipschitz` as a hypothesis.

A `Grep` for `Lipschitz` across the LevyStochCalc directory:
```
D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:67:def Lipschitz {n d : ℕ}
D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean:89:    {L : ℝ} (_hL : Lipschitz bsdej ν L) :
```

The `Lipschitz` predicate is defined, mentioned in one `True := trivial` lemma, and never used to constrain any axiom or theorem. This is **dead code that misrepresents the library's hypotheses**.

- **Why this matters**: A reader inspecting `Existence.lean` for the BSDEJ existence/uniqueness hypothesis surface sees `Lipschitz` defined and might assume it's threaded through. It is not. The axiom's effective hypothesis surface is just `0 < T`. Combined with Finding 1, this is the structural enabler of the uniqueness falsification.
- **Recommendation**: Either thread `Lipschitz bsdej ν L` through `continuousBSDEJ_exists_unique` as a hypothesis (closing Finding 1's hole), OR remove the dead `Lipschitz` definition + `picardMap_contraction` lemma to avoid misleading future readers. The former is correct; the latter is honest housekeeping.

---

### Finding 10 — `tools/cited_axioms.md`'s "Honest derivative theorems" table (lines 99-111) is incomplete: it omits `JumpDiffusion.exists_unique`, `jacodYor_representation`, and `brownian_martingale`/`brownian_quadVar`, and the 2026-05-11 recursive audit's internal classification table (lines 124-132) misses `JumpDiffusion.exists_unique` (a CRITICAL trivial-witness theorem) entirely

- **Severity**: MEDIUM
- **Location**: `D:\LevyStochCalc\tools\cited_axioms.md:99-111` (honest-derivative table); `cited_axioms.md:121-132` (recursive-audit classification table)
- **Evidence**:

The honest derivative theorems table (`cited_axioms.md:99-111`) lists 11 entries. `tools/full_audit.lean` runs `#print axioms` on:
- 11 Tier 1 axioms (file lines 28-39)
- 10 honest derivative theorems (lines 43-66)
- `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` (line 69, marked as "Layer 2")
- `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` (line 72, marked as "Layer 3")
- `LevyStochCalc.Brownian.Martingale.brownian_martingale` (line 50)
- `LevyStochCalc.Brownian.Martingale.brownian_quadVar` (line 51)

The latter four are tested by `full_audit.lean` but NOT listed in `cited_axioms.md`'s honest-derivative table. `JumpDiffusion.exists_unique` and `jacodYor_representation` are confirmed by `mcp__lean-lsp__lean_verify` to be Lean-std-axioms-only — which by the project's own rule ("no trivial-witness theorems remain", `cited_axioms.md:139`) should trigger demotion. Neither was demoted in the 2026-05-11 recursive audit.

The recursive-audit classification table (`cited_axioms.md:121-132`) lists only the 4 forwarder targets (`L2Isometry.itoLevyIsometry`, `continuousBSDEJ_exists_unique`, `itoLevyFormula`, `bsdej_path_regularity`). It does not look beyond those 4. `JumpDiffusion.exists_unique` and `jacodYor_representation` were untouched.

- **Why this matters**: The audit's stated invariant is "no trivial-witness theorems remain. Dissertation forwarders now transitively surface real Tier 1 cited axioms in their audit" (line 139). Findings 2, 3 show this is false. The classification table is incomplete because the scope was only the 4 named forwarders, not the broader library.
- **Recommendation**: Re-run the recursive trivial-witness audit on EVERY public theorem listed in `tools/full_audit.lean`, including the 10 derivative theorems + the 2 extra entries (`JumpDiffusion.exists_unique`, `jacodYor_representation`) + the 2 trivially-axiom-clean theorems (`brownian_martingale`, `brownian_quadVar`). Demote trivial-witness theorems found, and update `cited_axioms.md`'s tables to be exhaustive over `tools/full_audit.lean`'s contents.

---

### Finding 11 — `BSDEJData` structure has NO measurability fields on `f` and `g`; for non-measurable BSDEJ data, the Bochner integral `∫ s in [t, T], bsdej.f s ...` defaults to 0 (Mathlib convention `integral_undef`), making the BSDEJ equation trivially satisfiable

- **Severity**: MEDIUM
- **Location**: `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean:78-82` (structure)
- **Evidence**:

```lean
structure BSDEJData (n d : ℕ) (E : Type v) where
  /-- Generator `f(t, x, y, z, u)`. -/
  f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ
  /-- Terminal condition `g(x)`. -/
  g : (Fin n → ℝ) → ℝ
```

No `f_measurable`, no `g_measurable`, no `f_continuous`, no Lipschitz.

The BSDEJ equation conjunct (`Definition.lean:129-133`):
```lean
        (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
          Y t ω = bsdej.g (X T ω)
            + ∫ s in Set.Icc t T,
                bsdej.f s (X s ω) (Y s ω) (Z s ω) (U s ω)
            - (M_W T ω - M_W t ω) - (M_N T ω - M_N t ω)))
```

The `∫ s in [t, T], bsdej.f s ... ds` is the Bochner integral. By `MeasureTheory.integral_undef`, if the integrand is not Bochner-integrable in `s` (e.g., because `f` is non-measurable or has discontinuities making it non-locally-integrable), this integral evaluates to **0**.

**Concrete exploit**: take `bsdej.f := fun s _ _ _ _ => if s.IsRational then 0 else (1 : ℝ)` (or any non-measurable function via a non-Lebesgue-measurable set). The integral over `[t, T]` may default to 0 (depending on Mathlib's Bochner-integral conventions). Then the BSDEJ equation reduces to `Y t ω = g(X T ω) - M_W diff - M_N diff`, which the trivial witnesses can satisfy.

Even for MEASURABLE but non-Lipschitz `f`, the integral can be Bochner-defined but the BSDEJ uniqueness argument (which requires Picard-contraction in a Banach space) fails. The axiom asserts uniqueness regardless.

P7#13 noted the lack of measurability fields; this finding adds the `integral_undef`-default-to-0 mechanism that lets non-measurable f be silently absorbed without breaking the BSDEJ equation. The exploit is the **integral default**, not just the lack of constraints.

- **Why this matters**: `BSDEJData` is supposed to model the generator+terminal pair. Without measurability, the generator can be pathological and the BSDEJ equation collapses via `integral_undef`. The literature assumes Borel-measurability of `f` and `g` as a given. The Lean structure dropping this is silently weaker than the literature.
- **Recommendation**: Add `f_measurable : Measurable (Function.uncurry₅ f)` (joint in all five arguments) and `g_measurable : Measurable g` as structure fields of `BSDEJData`. Update downstream theorems to use these.

---

### Finding 12 — `Brownian.BrownianMotion.exists` axiom returns `∃ Ω, _, P, _, Nonempty (BrownianMotion P)` with `Ω : Type u` UNCONSTRAINED — for any non-Brownian-supporting `Ω`, the Nonempty witness is FORCED by the structure's increment_gaussian field, but no constraint propagates to downstream theorems that fix their own `Ω` via `Classical.choose`

- **Severity**: LOW
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\Construction.lean:176-178`
- **Evidence**:
```lean
axiom BrownianMotion.exists :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (BrownianMotion P)
```

`Classical.choose` extracts an `Ω : Type u`, but the choice is opaque. Two invocations of `BrownianMotion.exists` (even in the same proof) yield two different but structurally identical witnesses. If a downstream theorem assumes the Ω is "the" Brownian space and another theorem assumes "the same" Ω, the equalities don't hold by `rfl`.

This is a non-issue for the current library because each top-level theorem `Classical.choose`s its own `Ω`. But it's a future composability obstacle: when Mathlib's `MeasureTheory.WienerMeasure` arrives, the forwarder will use Mathlib's specific Ω (likely `C[0,∞)`), and any downstream `Classical.choose`-based reasoning needs to adapt.

The Multidim Brownian version (`MultidimBrownianMotion.exists`, `Multidim.lean:209-230`) uses `Fin d → Ω₀` for the same `Ω₀` from `BrownianMotion.exists`, which is one consistent choice.

- **Why this matters**: This is a minor structural issue. The axiom is correct as a postulate; the issue is documentation: a future Mathlib forwarder will fix `Ω`, breaking any downstream code that assumed `Classical.choose` was the only Ω.
- **Recommendation**: When porting to Mathlib's `WienerMeasure`, document the canonical `Ω`. No immediate fix needed.

---

### Finding 13 — `Brownian.Continuity.kolmogorov_modification_ae_eq` is a public lemma carrying `sorryAx` (sub-step of the KC modification proof) but is unused anywhere in the library — dead sorry'd lemma

- **Severity**: LOW
- **Location**: `D:\LevyStochCalc\LevyStochCalc\Brownian\Continuity.lean:176-184`
- **Evidence**:
```lean
lemma kolmogorov_modification_ae_eq
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (_hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (_Y : ℝ → Ω → ℝ)
    (_h_continuous : ∀ᵐ ω ∂P, Continuous (fun t => _Y t ω))
    (_h_dyadic_eq : ∀ s ∈ dyadicRationals, ∀ᵐ ω ∂P, _Y s ω = X s ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂P, _Y t ω = X t ω := by
  sorry
```

`Grep` for usage: 0 callers anywhere in the library. The lemma is public, named, has `sorryAx`, and is unused. The cited_axioms.md "no sorryAx anywhere in the public API" claim covers this too — see Finding 4.

- **Why this matters**: Minor — it's dead code, but the public-with-sorry signature is misleading. A reader sees a "lemma" that compiles; they might try to use it. They cannot, because it's unsound (it's `sorry`'d).
- **Recommendation**: Either complete the proof, mark `private`, or delete the lemma.

## Per-claim verdicts on the 11 Tier 1 cited axioms + 10 honest derivative theorems

| Theorem | Verdict | One-line note |
|---|---|---|
| `BrownianMotion.exists` | EARNED | Standard Wiener measure existence; structure non-trivial (increment_gaussian rules out W ≡ 0). |
| `PoissonRandomMeasure.exists_of_sigmaFinite` | EARNED | Standard PRM existence; structure non-trivial (poisson_law rules out N ≡ 0 for positive ν). |
| `kolmogorovChentsov_modification` | EARNED | Conjunct `continuous + a.s.-equals-X-at-each-t` is non-trivial (rules out X-arbitrary witnesses). |
| `brownian_martingale_rightCont` | EARNED | Standard Blumenthal 0-1 corollary; non-trivial. |
| `itoIsometry_brownian_unified_existence` | EARNED | 3-conjunct strongly constrained; properly binds `h_meas, h_progMeas, h_sq_int_global`. |
| `itoIsometry_compensated_unified_existence` | **WEAK** | Finding 5: `φ` bound without measurability/predictability; exploits via `integral_undef` convention. |
| `cauchySeq_simpleIntegralLp_compensated` | EARNED | Strongly typed Cauchy condition; non-trivial. |
| `adaptedSimple_dense_L2_compensated` | **WEAK** | Finding 6: docstring vs signature mismatch (claims progressive measurability, gets joint measurability). |
| `continuousBSDEJ_exists_unique` | **TRIVIAL** | Finding 1: false-as-stated (uniqueness fails for f=g=0; multiple Y'). |
| `bsdej_path_regularity` | **WEAK** | Finding 7: `∃ Z_avg U_avg` allows the trivial choice Z_avg=Z, U_avg=U; literature operators not pinned. |
| `itoLevyFormula` | **TRIVIAL** | Axiom statement satisfied by `⟨change, 0, 0, 0⟩`; demoted in 2026-05-11 audit but statement still vacuous (P7#1 covered; Finding 2 adds the JumpDiffusion enabler). |
| `MultidimBrownianMotion.exists` | EARNED | Real construction via `Measure.pi` + `iIndepFun_pi`. |
| `brownian_continuous_modification` | EARNED | Real derivation from `kolmogorovChentsov_modification` via 4-moment Gaussian. |
| `brownian_martingale` | EARNED | Real derivation, Lean-std axioms only. |
| `brownian_quadVar` | EARNED | Real derivation, Lean-std axioms only. |
| `brownian_filtration_rightContinuous` | EARNED | Forwards via `brownian_martingale_rightCont`. |
| `Brownian.Ito.itoIsometry` | EARNED | Extracts conjunct 3 from unified existence. |
| `Brownian.Ito.martingale_stochasticIntegral` | EARNED | Extracts conjunct 1. |
| `Brownian.Ito.quadVar_stochasticIntegral` | EARNED | Extracts conjunct 2. |
| `Compensated.itoLevyIsometry` | EARNED (modulo Finding 5) | Extracts conjunct 3; depends on unified existence's defects. |
| `Compensated.martingale_stochasticIntegral` | EARNED (modulo Finding 5) | Conjunct 1 extraction. |
| `Compensated.quadVar_stochasticIntegral` | EARNED (modulo Finding 5) | Conjunct 2 extraction. |
| `Compensated.cadlag_modification_exists` | EARNED | Conjunct 4 extraction. |
| `L2Isometry.itoLevyIsometry` | EARNED | 1-line forwarder; matches dissertation's I02 axiom statement exactly. |
| `JumpDiffusion.exists_unique` | **TRIVIAL** | Finding 2: `is_solution : True`, constant path is "the" JumpDiffusion. |
| `jacodYor_representation` | **TRIVIAL** | Finding 3: `⟨0, 0, 0, ξ - 𝔼ξ⟩; ring` proof; not even classified as a cited axiom. |

## Tools and sources used

- **Lean tools called**:
  - `mcp__lean-lsp__lean_verify` on: `continuousBSDEJ_exists_unique`, `jacodYor_representation`, `itoIsometry_compensated_unified_existence`, `Compensated.itoLevyIsometry`, `adaptedSimple_dense_L2_compensated`, `MultidimBrownianMotion.exists`, `JumpDiffusion.exists_unique`, `Brownian.Ito.simplePredictable_dense_L2`, `Poisson.Compensated.simplePredictable_dense_L2`, `Brownian.Continuity.kolmogorov_modification_ae_eq`, `Poisson.poissonRandomMeasure_finite_exists`
  - `mcp__lean-lsp__lean_run_code` for `@IsBSDEJSolution`, `@stochasticIntegral` type signatures, and the `MeasureTheory.integral_undef` Mathlib convention check
  - `mcp__lean-lsp__lean_loogle` for `MeasureTheory.lintegral` API check
- **Read**: 14 LevyStochCalc Lean files in full + relevant chunks of long files (Brownian/Ito.lean, Poisson/Compensated.lean); `tools/cited_axioms.md`, `tools/full_audit.lean`, `tools/full_audit_output.txt`; `Dissertation/Continuous.lean` (cross-repo context only).
- **Grep**: searched for `True := trivial`, `sorry`, `simplePredictable_dense_L2`, `is_solution`, `Lipschitz`, `kolmogorov_modification_ae_eq`, `jacodYor_representation` patterns across the LevyStochCalc directory.
- **Web searches**: None (P11 covered citation verification; my scope is structural/witness-level).
- **Papers consulted**: None directly (Applebaum 2009, Tang-Li 1994, Bouchard-Elie-Touzi 2009 citation correctness handled by P11; this audit takes the citations as given and audits whether the Lean statement matches what the cited theorem proves).

## What you couldn't verify

- I did not construct a fully mechanized Lean proof of inconsistency from Finding 1's two-solutions counterexample. The construction uses `(W, N)`-driven Brownian motion increments whose joint measurability is structurally assumed but not explicitly threaded through `BrownianMotion.measurable_eval`; constructing Solution B in Lean would require either (a) adding a `Measurable (Function.uncurry W.W)` field or (b) deriving joint measurability from continuity + slice-measurability. I have sketched the math; the orchestrator should decide whether mechanizing the inconsistency derivation is worth the additional Lean engineering before adding adaptedness to `IsBSDEJSolution`.
- I did not check `BrownianMotion.exists`'s `Classical.choose` semantics in detail — whether Lean's elaboration order admits a non-standard `Ω` choice that breaks downstream code. The Multidim version's `project_BM` construction (`Multidim.lean:114-201`) confirms one valid Ω; I accepted this as evidence of consistency.
- I did not exhaustively scan `Brownian/SimplePredictableRefine.lean` (2246 lines) — only the axiom region (lines 2020–2247) and structural outline. P5 #7's note about the `Filt` in the Brownian axiom being free is genuine but the conjunct-2 quadVar martingale rules out trivial F for non-zero H, so the consequence is bounded.
- I did not attempt WebFetch on Applebaum 2009 or Bouchard-Elie 2008 for citation verification — P11 handled this.

## Recommendations for the project (≤ 5 bullets)

- **Highest priority**: Fix Finding 1 by adding Lipschitz + adaptedness + L²(terminal) hypotheses to `continuousBSDEJ_exists_unique` AND strengthening `IsBSDEJSolution` per P5#1 recommendation. The current axiom is mathematically false; postulating it makes the project's logic inconsistent (the inconsistency is derivable from a working multidim BM, which the project already postulates).
- **High priority**: Demote `JumpDiffusion.exists_unique` (Finding 2) and `jacodYor_representation` (Finding 3) to Tier 1 cited axioms with citations, matching the 2026-05-11 `itoLevyFormula` precedent. Re-run the recursive trivial-witness audit over EVERY entry in `tools/full_audit.lean`, not just the 4 forwarder targets (Finding 10).
- **High priority**: Fix the `itoIsometry_compensated_unified_existence` measurability/predictability binding (Finding 5) to match the Brownian analog. Add the progressive measurability hypothesis to `adaptedSimple_dense_L2_compensated` (Finding 6) matching the docstring.
- **Medium priority**: Update `tools/cited_axioms.md:113-115` to reflect the four `sorryAx`-bearing public lemmas (Finding 4); update `cited_axioms.md`'s honest-derivative table to cover every entry in `tools/full_audit.lean`. Lift `Filt` out of `IsBSDEJSolution`'s inner existential (Finding 8). Either thread `Lipschitz` through `continuousBSDEJ_exists_unique` or delete the dead definition (Finding 9). Add measurability fields to `BSDEJData` (Finding 11).
- **Documentation hygiene**: Several `True := trivial` and `sorry`'d lemmas (`brownian_dyadicTime_exists`, `brownian_extend_to_real`, `kolmogorov_dyadic_holder`, `simpleFunc_approx_by_rectangles_*`, `rectangular_to_simplePredictable_*`, `dyadic_pointwise_tendsto_brownian`, `picardMap_contraction`, `poissonRandomMeasure_combine`, etc.) are decorative placeholders with strong-sounding names. Either mark `private`, complete the proofs, or delete them. The current state misleads any reader who scans for the substantive content.
