# Red Team Audit: Financial Mathematician (recalibrated)

**Auditor lens**: PhD-level mathematical finance reader asking "does this Lean library, as currently designed, support downstream Itô–Lévy work for jump-diffusion option pricing, Merton/Heston/CGMY pricing, mean-variance hedging, Lévy-driven BSDEJs (utility maximisation, indifference pricing, quadratic hedging)?"
**Date**: 2026-05-20
**Coverage**: 13 files read in full (`LevyStochCalc.lean`, `LevyStochCalc/BSDEJ/Definition.lean`, `LevyStochCalc/BSDEJ/Existence.lean`, `LevyStochCalc/BSDEJ/PathRegularity.lean`, `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean`, `LevyStochCalc/Ito/Setting.lean`, `LevyStochCalc/Ito/JumpFormula.lean`, `LevyStochCalc/Poisson/RandomMeasure.lean`, `LevyStochCalc/Poisson/L2Isometry.lean`, `LevyStochCalc/Brownian/Multidim.lean`, head of `LevyStochCalc/Brownian/Ito.lean`, tail of `LevyStochCalc/Brownian/SimplePredictableRefine.lean`, `tools/cited_axioms.md`); skimmed `Dissertation/Continuous.lean` for forwarder shape; not touched: `Compensated.lean` body (read targeted excerpts via grep), `Basic.lean`, `Notation.lean`, NaturalFiltration (out of finance lens). Persona is mostly out of scope per `shared_context_override.md` — short honest report.

## Executive summary

The library is a pure stochastic-calculus formalisation with zero finance content, so most of my lens does not apply. The *one* design choice that is unambiguously finance-relevant — the BSDEJ predicate and existence axiom — is currently NOT specified at literature strength (no Lipschitz hypothesis is required on the driver `f`, no L²-integrability on `g(X_T)`, no measurability/forward-SDE structure on `X`, `M_W` is not pinned to `∫Z·dW`); the axiom is honestly documented as such but its statement is mathematically false as written (asserts existence/uniqueness for arbitrary, non-Lipschitz `f`). Independently, I found that **`BSDEJ/MartingaleRepresentation.jacodYor_representation` is a `theorem` whose proof body is the exact `⟨0, 0, 0, jump_integral := ξ − 𝔼[ξ]⟩` trivial-witness pattern that caused `itoLevyFormula` to be demoted to an axiom on 2026-05-11 — the recursive audit missed it**; this is not finance-specific but is the kind of trivial-witness pattern the project has been hunting and lies on the BSDEJ→Picard chain a downstream finance user would inspect.

## Top findings (ranked by severity)

### Finding 1 — `jacodYor_representation` is a fake theorem (trivial-witness ⟨0, 0, 0, ξ−𝔼[ξ]⟩)

- **Severity**: CRITICAL
- **Location**: `LevyStochCalc/BSDEJ/MartingaleRepresentation.lean:55-84`
- **Evidence** (verbatim, lines 73-84):
  ```
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
  `lean_verify` on `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` returns `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}` — confirming this is a `theorem` closed by Lean's std axioms only, with no Tier 1 cited axiom dependency. The Brownian arguments `_W`, `_N` are unused (underscore-bound), so the proof literally does not consume any `(W, N)` structure to produce the decomposition.
- **Why this matters** (finance lens):
  Jacod–Yor martingale representation is **the** theorem that underwrites completeness, replication, and Föllmer–Schweizer quadratic hedging in Lévy-driven markets. A user reaching for this name expects "for every L²-payoff `ξ`, there exist predictable `(Z, U)` such that `ξ = 𝔼[ξ] + ∫Z·dW + ∫∫U·dÑ`". This file's `theorem` provides ZERO of that content: `Z = 0`, `U = 0`, and the entire `ξ − 𝔼[ξ]` content is dumped into an unconstrained scalar `Ω → ℝ`. `BM_integral` and `jump_integral` are not required to be Itô integrals against `(W, N)`, are not required to be martingales, and are not pinned to `(Z, U)` via L²-isometry. The exact pattern (three zero-processes plus the entire change stuffed into the fourth) is what the 2026-05-11 recursive audit caught in `itoLevyFormula` and demoted to an axiom. **The recursive audit missed this one.** The dissertation forwarder `continuousBSDEJ_exists_unique` does not currently depend on it (it forwards into the BSDEJ Tier 1 axiom directly), so soundness of the dissertation headlines is not broken — but the file is publicly listed under the same "BSDEJ" namespace a downstream finance user would inspect, and the `tools/cited_axioms.md` "honest derivative theorems" boundary is not respected here (this theorem is neither cited as a Tier 1 axiom nor derived from one).
- **Recommendation**:
  Demote `jacodYor_representation` to a Tier 1 `axiom` (Jacod 1976; Jacod & Yor; see also Tang–Li 1994 §2 for the BSDEJ-aware version). The cited-axioms register should include it as item #12. If a `theorem` form is wanted, the conclusion must be strengthened so the trivial witness fails:
    - require `BM_integral = (LevyStochCalc.Brownian.Ito.stochasticIntegral W Z) T` (or its multidim sum),
    - require `jump_integral = (LevyStochCalc.Poisson.Compensated.stochasticIntegral N U) T`,
    - require `Z`, `U` predictable / progressively-measurable w.r.t. the natural filtration of `(W, N)`.
  Even an "honest derivative" version of this would need most of the Tier 1 #5 / #6 unified-existence axioms to land first.

### Finding 2 — `continuousBSDEJ_exists_unique` asserts existence/uniqueness with NO Lipschitz hypothesis on the driver

- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/Existence.lean:113-126` (the axiom) + `:67-73` (the unused `Lipschitz` definition)
- **Evidence**: The axiom signature (verbatim, lines 113-126):
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
  No `Lipschitz bsdej ν L` hypothesis. No `L²` integrability on `bsdej.g`. The docstring at lines 93-103 says "Under Lipschitz hypotheses on `(f, g)` and L² integrability of the terminal data" — that's **only the docstring**, the formal hypotheses do not enforce this. The `Lipschitz` predicate is defined locally (lines 67-73) but is **never plugged into any axiom or theorem** in the library (verified by grep on `LevyStochCalc.BSDEJ.Existence.Lipschitz` — zero matches).
- **Why this matters** (finance lens):
  The Tang–Li 1994 / Pardoux–Răşcanu 2014 / Gnoatto 2025 cited result requires Lipschitz `f` and `g(X_T) ∈ L²(P)`. Without these, the result is **mathematically false**: drivers like `f(s,x,y,z,u) = y²` (quadratic growth) or `f(s,x,y,z,u) = e^{y}` (super-linear) admit no global L² solution in general. By stating the axiom for arbitrary `(f, g)`, the library is asserting more than the literature does — a mathematical statement that simply isn't true. Two consequences for finance:
    1. A downstream user importing this for a vanilla Lipschitz BSDEJ (Markowitz mean-variance hedging, Black–Scholes–Merton with jumps, Föllmer–Schweizer quadratic hedging) gets the correct result by accident — the literature's `f` is in fact Lipschitz, so the over-strong axiom still applies. But the user has to *know* their `f` is Lipschitz; the Lean statement does not enforce it, so a careless mis-application to a quadratic-growth driver (e.g., utility maximisation under exponential preferences, or Becherer 2006 bounded-`Y` indifference hedging) would silently use an axiom that the literature does not support.
    2. The "uniqueness" half of the axiom is also unconstrained by Lipschitz. In the literature uniqueness is a consequence of contraction; without contraction there can be multiple non-trivial solutions (e.g., quadratic BSDEs have multiple solutions distinguished by integrability class). The Lean axiom asserts a.e.-uniqueness for all `(f, g)` — false in general.
  This is the strongest single statement in the BSDEJ chain; over-claiming here propagates into any downstream finance use.
- **Recommendation**: Add `(_h_lip : Lipschitz bsdej ν L)` and `(_h_g_L2 : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞)^2 ∂P < ⊤)` and `(_h_X_meas : Measurable (Function.uncurry X))` (plus possibly a `∫⁻ ω, ∫⁻ s, |bsdej.f s (X s ω) 0 0 0|² ds ∂P < ⊤` L²-on-the-zero-section bound) as explicit hypotheses to `continuousBSDEJ_exists_unique`. Without them the axiom is over-claimed — the docstring already lists the intended hypotheses, just hoist them into the signature. Also delete or use `Lipschitz` — dead code at axiom-spec level is exactly the kind of "decorative" hypothesis the recursive audit hates.

### Finding 3 — `bsdej_path_regularity` inherits no Lipschitz hypothesis and `Z_avg, U_avg` are existentially quantified

- **Severity**: HIGH
- **Location**: `LevyStochCalc/BSDEJ/PathRegularity.lean:111-139` and unused `conditionalTimeAverage_Z`, `conditionalTimeAverage_U` (lines 62-83)
- **Evidence**: The axiom (verbatim 130-138):
  ```
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
  No Lipschitz hypothesis on `bsdej.f`. `Z_avg`, `U_avg` are existential — they are NOT required to be `conditionalTimeAverage_Z (partition) Z` and `conditionalTimeAverage_U (partition) U` (which the file defines at lines 62-83 but does not connect to the axiom).
- **Why this matters** (finance lens):
  Bouchard–Elie–Touzi 2009 Theorem 2.1 is a discretisation-error bound used to certify finite-difference / Monte-Carlo schemes for BSDEJs that arise in option pricing and dynamic hedging (Cont–Tankov 2003 §12, Gnoatto 2025 §4). The bound is on `(Z − E[Z|ℱ_{t_n}])` — i.e., the projection of `Z` onto piecewise-constant adapted approximations, which is the natural objective for numerical schemes. The Lean axiom existentially quantifies `(Z_avg, U_avg)` instead of pinning them to the conditional time-average defined in the file — this gives the axiom an escape valve (any `(Z_avg, U_avg)` will do, including `Z_avg := Z, U_avg := U`, which trivialises the second and third terms). The bound then reduces to bounding only the `‖Y_t − Y_{t_n}‖²` term, which is a much weaker statement than BET-2009.
  In addition the axiom has the same hypothesis hole as Finding 2 — no Lipschitz hypothesis. BET-2009's constant `C` depends explicitly on `T`, the Lipschitz constant `L`, and `‖(ξ, Z, U)‖_{S²×H²}` (Theorem 2.1, eq. (2.10)–(2.12)); none of these dependencies are recorded in the Lean statement.
- **Recommendation**:
  - Pin `Z_avg := conditionalTimeAverage_Z partition Z` and `U_avg := conditionalTimeAverage_U partition U` — make them definitions in the conclusion, not existentially quantified. The defined ones are already in the same file.
  - Add a Lipschitz hypothesis (same as Finding 2).
  - Optionally make the constant `C` an explicit function of `(T, L, ‖g(X_T)‖_{L²}, ‖f(·, 0, 0, 0)‖_{L²(P×dt)})` rather than an opaque existential — BET-2009 gives the explicit dependency.

### Finding 4 — `JumpDiffusion.exists_unique` is closed by the constant-path trivial witness + `is_solution := trivial`

- **Severity**: HIGH
- **Location**: `LevyStochCalc/Ito/Setting.lean:85-112` + structure at `:50-72`
- **Evidence**:
  - The `JumpDiffusion` structure has an `is_solution : True` field (line 72, with comment "stubbed, since the integrals along `X` require Phase 3 development").
  - The existence theorem proof body (verbatim lines 96-112):
    ```
      refine ⟨{
        X := fun _ _ => x₀
        measurable_path := measurable_const
        initial_value := Filter.Eventually.of_forall (fun _ => rfl)
        sup_L2 := ?_
        is_solution := trivial
      }⟩
    ```
  - `lean_verify` confirms: `{"axioms":["propext","Classical.choice","Quot.sound"],"warnings":[]}` — no Tier 1 dependency.
- **Why this matters** (finance lens):
  `JumpDiffusion` is the FORWARD process of a forward-backward SDE — in finance this is the asset-price process `S_t` (Merton 1976, Cont–Tankov 2003, Heston-with-jumps in Bates 1996). The library declares an "existence-and-uniqueness" `theorem` for the jump-SDE, but the structure's `is_solution` field is `True`, so the witness `X t ω := x₀` (constant process) trivially satisfies it. The proof contains no SDE content. For a finance user, this means:
    1. The library does NOT currently certify any non-trivial jump-diffusion model. Merton's `dS_t = μ S_t dt + σ S_t dW_t + S_{t-}(e^{J} − 1) dN_t` is not formalised; you cannot ground option-pricing arguments on top of `JumpDiffusion.exists_unique` because the structure constructed is just the constant path.
    2. The `itoLevyFormula` axiom takes a `X : JumpDiffusion W N coeffs x₀` parameter, but since `is_solution := True`, this argument carries no information about the actual SDE — making the axiom's `u(T, X_T) − u(0, X_0)` decomposition existentially vacuous against any `X.X` field (constant or not).
  The docstring at line 22-27 honestly flags this ("Phase 2 spec: structure fields wired to real Mathlib types... The full SDE-validity hypothesis... is layered on top once those integrals are defined."), but the `theorem JumpDiffusion.exists_unique` label is misleading — it should be a `def` or marked `_stub` or declared as the constant-path lift. Compare to the recursive-audit treatment of `itoLevyFormula` (downgraded from theorem-with-trivial-witness to documented axiom); the same standard should apply here.
- **Recommendation**:
  - Either (a) demote `JumpDiffusion.exists_unique` to a Tier 1 cited axiom (Applebaum 2009 Thm 6.2.9), making the existence-claim honestly axiomatised; OR (b) rename to `JumpDiffusion.exists_constant_witness` and write its substantive Picard-iteration form as a future-`sorry` named lemma.
  - Strengthen the `JumpDiffusion` structure's `is_solution` field to actually assert the SDE (using the existing Brownian + compensated-Poisson stochastic-integral primitives) — this is a Phase 3 task that the file flags but has not done.

### Finding 5 — `IsBSDEJSolution`'s `M_W` not pinned to `∫Z·dW`; hedging-strategy interpretation of `Z` is lost

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:114-118` (the L²-isometry constraint, not equality)
- **Evidence** (verbatim, with file's own docstring acknowledgement at 60-64):
  ```
        -- M_W satisfies the multidim Brownian L²-Itô isometry against Z:
          (∀ T', 0 < T' →
            ∫⁻ ω, (‖M_W T' ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
              ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
                ∑ i, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) ∧
  ```
  And docstring lines 60-64:
  > The strengthened predicate is still slightly weaker than the literature (it doesn't pin `M_W` to be literally `∫ Z · dW`, only an isometric martingale), but it is non-vacuous: the literature solution satisfies it, and trivial constant `Y` does not. Sufficient for the cited axioms `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` to assert substantive content.
- **Why this matters** (finance lens):
  In every finance application of BSDEJs — quadratic hedging (Föllmer–Schweizer 1991, Schweizer 2001, Cont–Tankov §10), mean-variance hedging (Schweizer 1995), indifference pricing (Becherer 2006) — the **`Z`-process is the hedging strategy** (the number of units of the risky asset to hold). The hedging interpretation requires `M_W_t = ∫_0^t Z_s dW_s`, NOT merely a martingale with the same L²-norm. Two martingales can share L²-norm without being equal: e.g., `M_W := ∫Z·dW + N̄` where `N̄` is any orthogonal mean-zero martingale (the L²-norm picks up an additive `‖N̄‖²` term that cancels in the isometry only if `N̄ ≡ 0`; for general orthogonal `N̄` the isometry constraint fails, but for a parametrised family of `N̄`s with norm pinned to zero — i.e., `N̄ ≡ 0` a.s. — the constraint does pin `M_W = ∫Z·dW` a.s. **on the natural filtration of `W`**). Critically, the predicate has `∃ Filt : Filtration ℝ _` (line 125) — any common filtration suffices, NOT the natural filtration of `(W, N)`. Under a larger filtration `Filt`, additional `Filt`-martingales orthogonal to `W` exist, so the isometry-only constraint genuinely does not pin `M_W` to `∫Z·dW`.
  Net effect for finance: the BSDEJ axiom certifies existence/uniqueness of `Y` (the value process — useful for pricing), but does NOT certify that the extracted `Z` is the hedging strategy. A downstream user wanting to claim "and `Z` is the delta of the option" cannot derive that from the predicate as written.
  The library's own docstring acknowledges this gap honestly (line 61: "doesn't pin `M_W` to be literally `∫ Z · dW`").
- **Recommendation**: Add an `h_progMeas` field to the BSDEJ predicate (the file's docstring at line 45-47 notes this requires "threading `h_progMeas`") and pin `M_W` to the multidim-Brownian stochastic-integral primitive analogously to how `M_N` is pinned to `Compensated.stochasticIntegral`. This makes `Z` recoverable as the literature hedging strategy. Also constrain the filtration `Filt` to be `≥ σ(W, N)` (the natural filtration of the driving noises); otherwise predictability of `Z` w.r.t. financial information cannot be claimed.

### Finding 6 — No multidim Brownian stochastic-integral primitive; finance applications must roll their own

- **Severity**: MEDIUM
- **Location**: `LevyStochCalc/Brownian/SimplePredictableRefine.lean:2117-2139` (scalar `stochasticIntegral`); no multidim counterpart
- **Evidence**: The `stochasticIntegral` definition takes `H : Ω → ℝ → ℝ` (scalar integrand). There is no `(H : Ω → ℝ → Fin d → ℝ) → Ω → ℝ` lifted version against the `MultidimBrownianMotion`. The BSDEJ predicate's `M_W` constraint at `BSDEJ/Definition.lean:114-118` reflects this — it uses L²-isometry rather than an explicit `∫Z·dW` sum because no `∑ i ∫ Z_i dW_i` primitive is exposed.
- **Why this matters** (finance lens):
  Real financial models are multidim: Heston model has 2 Brownian factors (price + vol), multivariate Black–Scholes baskets have `d` correlated factors, Hull–White interest-rate models have multiple factors. A finance user wanting to write `dS_t = ∑_{i=1}^d σ^i(t, S_t) dW^i_t` must define their own `∑_i Brownian.Ito.stochasticIntegral W_i (fun ω s => Z s ω i)` and re-derive its martingale + isometry properties. The library does the hard work for d=1 (via the unified-existence axiom) and provides `MultidimBrownianMotion` as a structure, but does not bridge them.
- **Recommendation**: Add a top-level definition
  ```
  noncomputable def Multidim.stochasticIntegral
      (W : MultidimBrownianMotion P d)
      (Z : Ω → ℝ → (Fin d → ℝ)) (h_meas, h_progMeas, h_sq) (T : ℝ) : Ω → ℝ
      := fun ω => ∑ i, Brownian.Ito.stochasticIntegral (W.W i) (fun ω' s => Z ω' s i) ... T ω
  ```
  with the obvious martingale + multidim-isometry corollaries. This is mechanical given the scalar primitive already exists; would unblock all multifactor finance applications and tighten the BSDEJ predicate (Finding 5).

### Finding 7 — `BSDEJData` does not support quadratic-growth drivers, multi-Y systems, or reflected/constrained BSDEJ

- **Severity**: LOW (out-of-scope for current claims; documents finance-relevant design omissions)
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:78-82`
- **Evidence**:
  ```
  structure BSDEJData (n d : ℕ) (E : Type v) where
    f : ℝ → (Fin n → ℝ) → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ
    g : (Fin n → ℝ) → ℝ
  ```
  `Y` is implicitly scalar (`f : … → ℝ → … → ℝ`); the driver is hard-wired to be a scalar BSDEJ.
- **Why this matters** (finance lens):
  Finance applications that the library claims to be a foundation for include:
    - **Markowitz mean-variance hedging** (Schweizer 1995, Bouleau 1991): scalar `Y`, Lipschitz `f` ✓ supported in shape.
    - **Indifference pricing under exponential utility** (Becherer 2006, Mania–Tevzadze 2003): BSDE driver has **quadratic growth** in `Z`; not Lipschitz. The library's `Lipschitz` predicate cannot express this (and isn't plugged in anywhere anyway). The library's BSDEJ existence axiom would over-claim if invoked on a non-Lipschitz driver (Finding 2).
    - **Coupled / multi-Y BSDEJ** (Cvitanić–Karatzas 1996 reflected BSDE, multi-asset American options under jumps): need `Y : Fin k → ℝ`. Not supported by the current `BSDEJData` structure.
    - **Reflected BSDEJ for American jump-diffusion options** (El Karoui et al. 1997 reflected BSDE, Hamadène–Ouknine 2003 for the jump case): need an obstacle `L_t` and `Y_t ≥ L_t` constraint with a `K` increasing-process component. Not supported.
    - **Forward-backward coupled SDE-BSDE (FBSDE) systems** (Ma–Protter–Yong 1994 for deep BSDE, Hu–Peng 1995): need `X` to solve an SDE with the same `(W, N)` AND `(Y, Z, U)` to feed back into `X`'s drift. The library's `X` is exogenous (Finding 8).
  None of these is a defect of the *current* library claims (which are scoped to scalar Lipschitz BSDEJ a la Tang–Li 1994 / Gnoatto 2025). But every one of them is a foreseeable finance extension, and the current `BSDEJData` shape forces a non-trivial restructuring of every downstream consumer.
- **Recommendation**: If finance applications are an explicit downstream target, document the scope: "supports scalar Lipschitz BSDEJ; quadratic-growth / reflected / FBSDE extensions are deferred". Otherwise this is fine for the current pure-stochastic-calculus scope.

### Finding 8 — `IsBSDEJSolution` treats `X` as exogenous (no SDE constraint); decoupled FBSDEJ not certified

- **Severity**: LOW (out-of-scope structural note)
- **Location**: `LevyStochCalc/BSDEJ/Definition.lean:97-98` (`X : ℝ → Ω → (Fin n → ℝ)` with no SDE hypothesis) + `BSDEJ/Existence.lean:120-121` (axiom inherits this)
- **Evidence**: `X` enters the BSDEJ predicate as a bare function with no requirement that it solves a forward jump-SDE driven by the same `(W, N)`. The dissertation forwarder `Continuous.itoLevyFormula` does take `X : JumpDiffusion W N coeffs x₀` (an SDE solution structure), but `continuousBSDEJ_exists_unique` does not.
- **Why this matters** (finance lens):
  Every BSDEJ application in finance is a *decoupled* FBSDEJ: `X` solves an SDE with the asset-price dynamics; `(Y, Z, U)` solves the BSDEJ where the driver `f(s, X_s, …)` depends on the forward state. The literature (Pardoux–Răşcanu 2014 §4.3, Bouchard–Elie–Touzi 2009 §2) treats `X` as the solution of a jump-SDE driven by the same `(W, N)`. Here `X` is unconstrained — a finance user could feed in a non-measurable junk function, or a function not adapted to the natural filtration of `(W, N)`. In the latter case the BSDEJ is mis-aligned with financial information flow.
- **Recommendation**: Either pass `X : JumpDiffusion W N coeffs x₀` (using the existing `JumpDiffusion` structure — once Finding 4 is fixed) or add `h_X_meas`, `h_X_adapted` hypotheses. The current free-`X` shape is fine for proving the abstract Picard contraction, but a finance-facing public API should constrain it.

### Finding 9 — No Lévy-measure condition (`∫(1 ∧ |x|²) ν(dx) < ∞`) checked or required for Lévy processes

- **Severity**: LOW (out-of-scope note on naming)
- **Location**: `LevyStochCalc/Poisson/RandomMeasure.lean:64-103` (PRM structure) + axiom at `:170-174`
- **Evidence**: The PRM definition requires only `[SigmaFinite ν]`. There is no `∫(1 ∧ |x|²) ν(dx) < ∞` integrability condition (the **Lévy measure** condition). The library is correctly named "LevyStochCalc" because the PRM + compensated integral apparatus is the building block for Lévy processes, but no Lévy-process structure is actually defined — only the underlying PRM.
- **Why this matters** (finance lens):
  In finance, the Lévy measure of a jump-diffusion model satisfies the Lévy condition `∫(1 ∧ |x|²) ν(dx) < ∞` (and stronger conditions for specific moment requirements: e.g., finite variance requires `∫ |x|² ν(dx) < ∞` on `|x| > 1`; martingale measure equivalence in Esscher / minimal-entropy pricing requires `∫ e^{θx} ν(dx) < ∞` for some `θ`). The library's PRMs are more general than Lévy measures — `ν` can be any σ-finite measure (e.g., `ν = Lebesgue` on `ℝ` is σ-finite but not a Lévy measure since `∫(1 ∧ x²) dx = ∞`). When a downstream user instantiates with their financial `ν` (Merton: discrete; CGMY: continuous with explicit density), they have to check the Lévy condition themselves — the library does not encode "this PRM corresponds to a Lévy process". This is correct for a foundational library but worth flagging because the name "LevyStochCalc" suggests Lévy-process content that isn't there yet.
- **Recommendation**: Either (a) document the gap in the top-level README / module docstring ("intensity ν is required to be σ-finite, not necessarily a Lévy measure; downstream Lévy-process applications must verify `∫(1 ∧ |x|²) ν(dx) < ∞` themselves"), or (b) add a `LevyMeasure` typeclass / predicate for downstream use. Not a defect; just a discoverability gap.

### Finding 10 — `itoLevyFormula` axiom statement still vacuous (acknowledged by the project)

- **Severity**: MEDIUM (already documented by the project; flagged here for finance lens completeness)
- **Location**: `LevyStochCalc/Ito/JumpFormula.lean:90-105`
- **Evidence**: The axiom (verbatim 90-105):
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
      ∃ (drift_term diff_mart jump_mart comp_drift : Ω → ℝ),
        (∀ᵐ ω ∂P,
          u T (X.X T ω) - u 0 (X.X 0 ω) =
            drift_term ω + diff_mart ω + jump_mart ω + comp_drift ω)
  ```
  No `C^{1,2}(u)` smoothness hypothesis. No measurability on `u`. The four terms `drift_term, diff_mart, jump_mart, comp_drift` are existentially quantified `Ω → ℝ` with NO pinning to the literature integrals (`∫(∂_t u + 𝓛u) ds`, `∫∇uᵀσ dW`, `∫∫(u(·+γ)−u) Ñ`, `∫∫(u(·+γ)−u−γᵀ∇u) ν ds`). The dissertation-side forwarder docstring (`D:/Dissertation/Dissertation/Continuous.lean:347-353`) honestly notes:
  > the LevyStochCalc theorem was demoted from a trivial-witness theorem to an axiom but the statement itself is currently still vacuous (`∃ drift mart jumpMart compDrift, u(T,X_T) − u(0,X_0) = sum` is satisfied by `drift := full change, others := 0`).
- **Why this matters** (finance lens):
  Itô–Lévy formula is the foundation of every jump-diffusion option pricing argument (PIDE derivation in Cont–Tankov 2003 §12.2, dynamic-programming HJB for stochastic-control problems in Øksendal–Sulem 2007). The axiom currently does not certify the four-term decomposition that finance applications need; it only certifies *some* additive decomposition of the change `u(T, X_T) − u(0, X_0)` into four functions. A downstream finance user wanting "and `diff_mart` is `∫∇uᵀσ dW`" gets nothing. The project acknowledges this and queues a strengthening; flagged here for finance-lens completeness.
- **Recommendation**: Strengthen the four-term existential to pin each to its literature integral. This requires landing the multidim-Brownian + compensated-Poisson stochastic integrals against jump-diffusion integrands (Phase 3 work flagged elsewhere). Independent of finance: the same recommendation persona 7 (stochastic analyst) would make.

## Per-claim verdicts on the headline theorems / cited axioms

Applied to the 11 Tier 1 cited axioms + the 10 honest derivative theorems listed in `tools/cited_axioms.md` (plus the relevant non-Tier-1 theorems I encountered).

| Theorem | Verdict | One-line note |
|---|---|---|
| `Brownian.BrownianMotion.exists` (Tier 1 #1) | OUT-OF-SCOPE-FOR-MY-LENS | Foundational; no finance angle. |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` (Tier 1 #2) | OUT-OF-SCOPE-FOR-MY-LENS | Foundational; finance-relevant note in Finding 9. |
| `Brownian.Continuity.kolmogorovChentsov_modification` (Tier 1 #3) | OUT-OF-SCOPE-FOR-MY-LENS | — |
| `Brownian.Martingale.brownian_martingale_rightCont` (Tier 1 #4) | OUT-OF-SCOPE-FOR-MY-LENS | — |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` (Tier 1 #5) | EARNED | Three non-trivial conjuncts (martingale + quadVar + isometry); witnesses are non-vacuous; matches Karatzas–Shreve 3.2.6. Critical foundation for delta-hedging. |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` (Tier 1 #6) | EARNED | Same structure with added càdlàg; matches Applebaum 4.2.3+4.2.4. Foundation for jump-hedging. |
| `Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated` (Tier 1 #7) | OUT-OF-SCOPE-FOR-MY-LENS | Pure construction step. |
| `Poisson.Compensated.adaptedSimple_dense_L2_compensated` (Tier 1 #8) | OUT-OF-SCOPE-FOR-MY-LENS | Pure construction step. |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` (Tier 1 #9) | **WEAK** | Statement over-claims: missing Lipschitz / L² / measurability hypotheses (Finding 2). Strengthened predicate (2026-05-11) blocks the constant-witness attack but `M_W` not pinned to `∫Z·dW` (Finding 5). Sufficient for the abstract "Y exists" claim; not sufficient for downstream finance use of `Z` as a hedging strategy. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` (Tier 1 #10) | **WEAK** | Same Lipschitz hole as Tier 1 #9 (Finding 3); `(Z_avg, U_avg)` existentially quantified instead of pinned to the file's `conditionalTimeAverage_*`. |
| `Ito.JumpFormula.itoLevyFormula` (Tier 1 #11) | **WEAK** | Statement still vacuous (Finding 10); project-acknowledged. |
| `Poisson.L2Isometry.itoLevyIsometry` (derived) | EARNED | Clean 1-line forwarder; finance-critical foundation for compensated-Poisson L² hedging arguments. |
| `Brownian.Multidim.MultidimBrownianMotion.exists` (derived) | EARNED | Honest construction via product measure. |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` (not on Tier 1) | **TRIVIAL** | Fake theorem: `⟨0, 0, 0, ξ−𝔼[ξ]⟩` trivial-witness pattern (Finding 1). Recursive audit missed it. |
| `Ito.Setting.JumpDiffusion.exists_unique` (not on Tier 1) | **TRIVIAL** | Constant-path witness + `is_solution : True` (Finding 4). Recursive audit missed it. |
| `BSDEJ.Existence.picardMap` / `picardMap_contraction` (lemma stubs) | OUT-OF-SCOPE-FOR-MY-LENS | Dead-code stubs (`picardMap = id`, `picardMap_contraction : True := trivial`). Already noted by persona 8. |
| Other derived theorems (`itoIsometry`, `martingale_stochasticIntegral`, `quadVar_stochasticIntegral`, etc.) | OUT-OF-SCOPE-FOR-MY-LENS | Conjunct-extractors from Tier 1 unified-existence axioms; verified earned-by-extraction. |

## Tools and sources used

- **Lean tools called**:
  - `mcp__lean-lsp__lean_verify` on `LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation` (confirmed `theorem` with std-axioms-only — bug confirmed),
  - `mcp__lean-lsp__lean_verify` on `LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` (same — bug confirmed),
  - `mcp__lean-lsp__lean_verify` on `LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique`, `LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity`, `LevyStochCalc.Ito.JumpFormula.itoLevyFormula`, `LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry` (Tier 1 dependencies confirmed).
- **Read calls**: 13 files listed in Coverage above.
- **Grep calls**: searches for `finance|hedge|option|portfolio|Markowitz|Heston|Merton`, `Lipschitz`, `M_W|M_N`, `picardMap`, `JumpDiffusion`, `stochasticIntegral`, `Lévy.*measure|integrable.*min|truncat`, `progMeas|adapted|filtration`, etc.
- **Web searches / fetches**: None — drew on background knowledge of cited literature already named in the docstrings (Tang–Li 1994, Bouchard–Elie–Touzi 2009, Applebaum 2009, Cont–Tankov 2003, Becherer 2006, Föllmer–Schweizer 1991, Schweizer 1995/2001, Pardoux–Răşcanu 2014, Karatzas–Shreve 1991, Gnoatto 2025).
- **Papers consulted (from memory / docstring cross-checks)**:
  - Tang, S. & Li, X. (1994). "Necessary conditions for optimal control of stochastic systems with random jumps." SICON 32(5).
  - Bouchard, B., Elie, R. & Touzi, N. (2009). "Discrete-time approximation of decoupled forward-backward SDE with jumps." SPA 119(11), Theorem 2.1.
  - Applebaum, D. (2009). *Lévy Processes and Stochastic Calculus*, 2nd ed., CUP. Ch 4, esp. Thm 4.2.3 (L²-isometry), Thm 4.4.7 (Itô–Lévy formula), Thm 6.2.9 (SDE existence).
  - Cont, R. & Tankov, P. (2003). *Financial Modelling with Jump Processes*, esp. §8.4 (Itô formula) and §12 (BSDE / PIDE pricing).
  - Becherer, D. (2006). "Bounded solutions to backward SDEs with jumps for utility optimization and indifference hedging." AAP 16(4).
  - Föllmer, H. & Schweizer, M. (1991). "Hedging of contingent claims under incomplete information." In *Applied Stochastic Analysis*.
  - Pardoux, E. & Răşcanu, A. (2014). *Stochastic Differential Equations, Backward SDEs, Partial Differential Equations*. Springer.
  - Gnoatto, A. (2025). "A primer on backward stochastic differential equations with jumps." Quantitative Finance 25.
  - Karatzas, I. & Shreve, S. (1991). *Brownian Motion and Stochastic Calculus*. Springer. Esp. §3.2 (Itô integral construction).

## What I couldn't verify

- I did NOT read the body of `Poisson/Compensated.lean` (2907 lines) in full — only the head (axioms, definitions of the integral primitive) plus targeted grep matches. The persona is "what finance applications does the library support", and the compensated-Poisson stochastic integral construction is several layers below where finance applications would enter; the surface API (the axioms, the `stochasticIntegral` definition, the L²-isometry forwarder) is what matters for the finance-lens audit and that's what I read in full.
- I did NOT run `lake build` — the build is reported by `shared_context_override.md` as passing at 8401 jobs and I have no reason to doubt that. My Lean verification was per-theorem (`lean_verify`).
- I did NOT verify the Tier 1 axiom statements against the original Applebaum 2009 / Tang–Li 1994 / BET 2009 papers from primary sources during this audit — verifying paper-citation faithfulness is persona 11's mandate, and the docstrings in the Lean files give enough context for the finance-lens findings here (which are about LEAN-side hypothesis omissions and predicate-strength gaps, NOT about whether the cited paper says what the axiom claims it says).
- I did NOT audit `Brownian/Continuity.lean` or `Brownian/Martingale.lean` — these are pure infrastructure and have no finance lens.

## Recommendations for the project (≤ 5 bullets)

1. **Fix `jacodYor_representation` (Finding 1)** — same recursive-audit treatment as `itoLevyFormula` got on 2026-05-11. Either demote to a Tier 1 cited axiom (Jacod 1976) or strengthen the conclusion to pin `BM_integral`, `jump_integral` to actual stochastic integrals against `(W, N)`. This is the most concrete leftover from the 2026-05-11 audit.
2. **Fix `JumpDiffusion.exists_unique` (Finding 4)** — `is_solution : True` + constant-path witness is the same anti-pattern. Either demote the theorem to a Tier 1 axiom (Applebaum 2009 Thm 6.2.9) or strengthen `JumpDiffusion`'s `is_solution` field to an actual SDE-satisfaction predicate.
3. **Hoist the Lipschitz / L² hypotheses into the BSDEJ axiom signatures (Findings 2, 3)** — both `continuousBSDEJ_exists_unique` and `bsdej_path_regularity` should take `Lipschitz bsdej ν L`, `‖bsdej.g (X T ·)‖_{L²} < ∞`, and measurability hypotheses on `X` explicitly. The `Lipschitz` predicate is already defined; it's just not plugged in. Without this the axioms over-claim against the literature.
4. **Add a multidim Brownian stochastic-integral primitive (Finding 6)** — this is the smallest concrete API gap blocking real multifactor finance applications. Should be a few lines of definition + corollaries on top of the scalar `stochasticIntegral`.
5. **Either (a) document explicitly that downstream finance applications require quadratic-growth / reflected / coupled-FBSDE extensions on top of this scalar Lipschitz library, or (b) add `LevyMeasure` / `IsLévyProcess` predicates to bridge the naming gap (Findings 7, 9)** — purely a discoverability fix.
