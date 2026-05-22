# Red Team Audit: Pure Mathematician (2nd audit)

**Auditor lens**: Research mathematician — measure theory, probability, functional analysis. Verdict on whether each Lean definition / predicate matches the standard statement in Karatzas-Shreve, Le Gall, Applebaum, Revuz-Yor, Ikeda-Watanabe, Jacod-Shiryaev, Tang-Li.
**Date**: 2026-05-22
**Coverage**: I read in full `BSDEJ/Definition.lean`, `BSDEJ/Existence.lean`, `BSDEJ/PathRegularity.lean`, `BSDEJ/MartingaleRepresentation.lean`, `Ito/Setting.lean`, `Ito/JumpFormula.lean`, `Brownian/Construction.lean`, `Brownian/Multidim.lean`, `Brownian/MultidimIto.lean`, `Poisson/RandomMeasure.lean`, plus the key axiom regions of `Brownian/SimplePredictableRefine.lean` (lines 2080-2200) and `Poisson/Compensated.lean` (lines 1750-1970). Cross-referenced against `tools/cited_axioms.md`, `shared_context_override.md`, my predecessor's archived report, and the parallel peer `05_proof_theorist.md`. Lean LSP `lean_verify` run on the four load-bearing axioms (`continuousBSDEJ_exists_unique`, `bsdej_path_regularity`, `itoLevyFormula`, `JumpDiffusion.exists_unique`) — all axiom sets clean modulo the documented Tier 1 cited axioms + Lean core + `sorryAx` for the two baseline sorries.

## Executive verdict (≤ 3 sentences)

The 24-commit cleanup is substantively real on the predicates: the 1st audit's CRITICAL counterexamples (constant-path `JumpDiffusion`, `is_solution : True`, the `⟨0,0,0,ξ−E[ξ]⟩` trivial witness in `jacodYor_representation`, and the predecessor P12's `Y₂ = W_T − W_t` counterexample to BSDEJ uniqueness) are all structurally excluded by the post-cleanup signatures, and the four-term `itoLevyFormula` now pins every term to a literature integral with no remaining existentials. The remaining literature-divergences that survive the cleanup are: (i) `IsBSDEJSolution` and `JumpDiffusion.is_solution` use `Adapted` not `ProgMeasurable` at the outer layer (literature requires predictability of `Z` and `U`); (ii) neither predicate requires càdlàg sample paths for `Y` / `X` (literature S² is càdlàg-adapted, not joint-measurable); (iii) the `Compensated.itoIsometry_compensated_unified_existence` axiom asserts the unconditional-on-φ existence of `F` plus a `Measurable`-gated isometry — strictly broader than Applebaum 4.2.3, which is for predictable φ only. These are not soundness gaps (no concrete counterexample escapes), but they are literature divergences a careful research-mathematician reader would flag.

## Top findings (ranked by severity, highest first)

### Finding 1 — `IsBSDEJSolution` and `JumpDiffusion.is_solution` use `Adapted Filt Z/U` where Tang-Li/Pardoux-Răşcanu/Bichteler require **predictable** (≡ `ProgMeasurable Filt`) `Z` and `U`

- **Severity**: HIGH (literature divergence with stated citations)
- **Location**: `BSDEJ/Definition.lean:160-162`, `Ito/Setting.lean:91-110`
- **Evidence** — the predicate uses `MeasureTheory.Adapted Filt Z` (per-time-`t` Filt-measurability, no further regularity) at the outer layer:
  ```lean
  MeasureTheory.Adapted Filt Y ∧
  MeasureTheory.Adapted Filt Z ∧
  (∀ e : E, MeasureTheory.Adapted Filt (fun s ω => U s ω e)) ∧
  ```
- **Why this matters**: Tang & Li 1994 SICON 32(5) Theorem 3.1 uses the solution space `S² × H² × H²_N` where `H²` is the L²-space of *predictable* (= `Pred(Filt)`-measurable, equivalently `ProgMeasurable Filt`) `Z`. Pardoux-Răşcanu 2014 Thm 4.79 / 5.42 is identical, as is Andersson-Gnoatto-Patacca-Picarelli 2025 arXiv:2211.04349 Thm 2.4 (the now-cited replacement for the fabricated "Gnoatto 2025 *QF*"). Bouchard-Elie 2008 SPA 118(1) Thm 2.1 (the now-cited replacement for the fabricated "BET 2009 SPA 119(11)") is also predictable-based. The Lean `Adapted` predicate is `∀ t, StronglyMeasurable[(Filt t)] (Z t)` — per-`t` measurability of the random variable `ω ↦ Z(t, ω)` only; it does NOT imply joint measurability of `(s, ω) ↦ Z(s, ω)` on the progressive σ-algebra. Mathlib's own infrastructure (Mathlib.Probability.Process.Adapted) confirms `Adapted → ProgMeasurable` requires extra hypotheses (continuous-in-time, or discrete time, or right-continuous + left-limits + separability of state space).

  Within the predicate, the M_W pin requires a separately-bundled inner existential of `h_Z_progMeas` witnesses (per-component) — so the integral `MultidimBrownianMotion.stochasticIntegral W Z h_Z_meas h_Z_progMeas h_Z_sq T'` IS well-typed. But the *outer* `Adapted Filt Z` requirement is the predicate-level honest statement of "Z is part of the BSDEJ solution"; that requirement should match the literature solution space.

  Consequence: a Z that is `Adapted Filt` but not jointly progressively measurable on the progressive σ-algebra could in principle satisfy the predicate via the bundled inner `h_Z_progMeas` witnesses (which deliver a different progressive measurability w.r.t. each per-component natural filtration `(naturalFiltration (W.W i)).seq t`, not the universal `Filt`-progressive σ-algebra). This is a subtle predicate-shape mismatch: outer adaptedness is to `Filt`, inner progressive-measurability is to a *per-component* filtration. The literature uses one uniform progressive σ-algebra everywhere.

- **Recommendation**: Either (a) replace `Adapted Filt Z` with `ProgMeasurable Filt Z` in `IsBSDEJSolution`, and similarly for the `U_e` family; (b) acknowledge in the BSDEJ docstring that the predicate uses `Adapted` not `ProgMeasurable` — analogous to the H6 documentation caveat already present in the Compensated axiom. Neither (a) nor (b) is present.

### Finding 2 — Neither `IsBSDEJSolution` nor `JumpDiffusion` requires càdlàg sample paths; `Y` and `X` need only be jointly measurable (per audit lens, this breaks `S²` per the literature definition)

- **Severity**: HIGH (literature divergence)
- **Location**: `BSDEJ/Definition.lean:137-138`, `Ito/Setting.lean:80-87`
- **Evidence**: `IsBSDEJSolution`'s `Y` field requires
  ```lean
  Measurable (Function.uncurry Y)
    ∧ (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
  ```
  — joint measurability + L²-sup-norm finite — but NO path-regularity hypothesis (no càdlàg, no right-continuity with left limits). `JumpDiffusion`'s `X` field is identical: `measurable_path : Measurable (Function.uncurry X)` + `sup_L2`.
- **Why this matters**: The literature `S²([0,T]; ℝ^m)` space is defined as **càdlàg adapted** processes with L²-sup-norm:
  * Pardoux-Răşcanu 2014 §4.5: "S² is the space of càdlàg adapted processes Y such that E[sup_t |Y_t|²] < ∞."
  * Becherer 2006 AAP 16(4) "Bounded solutions to BSDEs with jumps..." — solution space requires càdlàg `Y`.
  * Tang-Li 1994 SICON 32(5) Thm 3.1 — proof requires càdlàg `Y` to apply Itô's formula to `|Y_t|²`.
  * Bouchard-Elie 2008 SPA 118(1) Thm 2.1 — the path-regularity bound `E[sup_{t ∈ [t_n, t_{n+1}]} |Y_t − Y_{t_n}|²] ≤ C·Δt` is exactly about càdlàg regularity; it's vacuous (or worse, ill-defined) for processes that are only jointly measurable.

  Without càdlàg, `X_{s-}` (left limit) is undefined — but the literature SDE / Itô-Lévy formula uses `X_{s-}` everywhere (the jump compensator evaluates at left-limits). The Lean structure replaces `X_{s-}` with `X_s` (point evaluation). For L²-integrable processes the integrals coincide Lebesgue-a.s. in `s` because càdlàg paths have at most countably many jumps a.s., so `{s : X_s ≠ X_{s-}}` has Lebesgue measure 0. But if `Y` is not even càdlàg, the pointwise expression `Y_s ω` is not well-behaved.

  Specifically, the path-regularity axiom `bsdej_path_regularity` asserts the bound `E[sup_{t ∈ [t_n, t_{n+1}]} |Y_t − Y_{t_n}|²] ≤ C·Δt` over arbitrary partitions. Without càdlàg regularity, `sup` over an interval of a jointly measurable process is not generally measurable in `ω` (the natural domain for sup is a finite/countable subset). The Lean statement uses `⨆ t ∈ Set.Icc ... ` which is a `iSup` over an uncountable index — this can be highly pathological without continuity hypotheses. For a generic L²-bounded jointly measurable `Y`, the sup could fail to be Lebesgue-measurable in `ω` (essential sup vs pointwise sup discrepancy). The bound is therefore mathematically ill-posed without càdlàg.

  The cited Bouchard-Elie 2008 Thm 2.1 establishes the bound assuming `Y` is càdlàg adapted (which is the literature S² norm).

- **Recommendation**: Add càdlàg fields to both predicates:
  ```
  Y_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y s ω) (𝓝[Set.Ioi t] t) (𝓝 (Y t ω)) ∧
      ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (𝓝[Set.Iio t] t) (𝓝 L)
  ```
  (mirror of the `cadlag` clause already present in `itoIsometry_compensated_unified_existence` for the integral process). Similarly for `X` in `JumpDiffusion`. This brings the predicates in line with `S²` and makes the path-regularity bound mathematically well-posed.

### Finding 3 — `compensatorDriftIntegrand` integration in `itoLevyFormula` uses Bochner `∫ e, ... ∂ν` over all of E — but the literature compensator-drift integrand is only ν-integrable on `{|γ| ≤ 1}` for general Lévy measures (small/large jump split is absent)

- **Severity**: HIGH (literature divergence; potential divergence of the asserted equation)
- **Location**: `Ito/JumpFormula.lean:84-91` (definition of `compensatorDriftIntegrand`); `Ito/JumpFormula.lean:195-196` (its use in the axiom statement)
- **Evidence**:
  ```lean
  noncomputable def compensatorDriftIntegrand {n : ℕ} {E : Type v}
      (u : ℝ → (Fin n → ℝ) → ℝ)
      (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ))
      (s : ℝ) (x : Fin n → ℝ) (e : E) : ℝ :=
    u s (x + γ s x e) - u s x - ∑ i : Fin n, γ s x e i * gradient u s x i
  ```
  And in the axiom (lines 195-196):
  ```lean
  + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
      compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν
  ```
  No restriction to small jumps; no compensation/splitting between `{|γ| ≤ 1}` and `{|γ| > 1}`.

- **Why this matters**: Applebaum 2009 Thm 4.4.7 (the cited theorem) states the Itô-Lévy formula with the compensator drift only over **small jumps** (the integral over `{e : |γ(s, X_{s-}, e)| ≤ 1}` for the second-order Taylor remainder), and the large-jump contribution `∫_{|γ| > 1} [u(x+γ) − u(x)] ν(de) ds` is folded into a separate term that combines with the Lévy measure of the *uncompensated* large-jump integral. The standard small/large-jump decomposition is:
  ```
  u(T, X_T) − u(0, X_0)
    = ∫_0^T (∂_t u + ½ Tr(σσᵀ ∇²u) + μᵀ∇u) ds          [continuous drift]
    + ∫_0^T ∇uᵀσ dW                                   [diffusion martingale]
    + ∫_0^T ∫_{|γ|≤1} [u(X_{s-} + γ) − u(X_{s-})] Ñ(ds, de)   [small-jump martingale]
    + ∫_0^T ∫_{|γ|>1} [u(X_{s-} + γ) − u(X_{s-})] N(ds, de)   [large-jump uncompensated]
    + ∫_0^T ∫_{|γ|≤1} [u(X_{s-} + γ) − u(X_{s-}) − γᵀ∇u(X_{s-})] ν(de) ds  [small-jump compensator]
  ```
  For a general Lévy measure ν, `∫ |γ(e)|² ν(de) < ∞` near zero but `∫ |γ(e)| ν(de)` may diverge near zero (e.g. ν the standard α-stable Lévy measure with α ∈ (1, 2)). The Lean formula has
  ```
  jump_mart = Compensated.stochasticIntegral N [u(·+γ) − u along X] T   [all jumps compensated]
  comp_drift = ∫_0^T ∫_E [u(·+γ) − u − γᵀ∇u] ν(de) ds                  [Taylor remainder over ALL e]
  ```
  For this to match Applebaum 4.4.7 globally, we need EITHER (a) `∫_E (u(x+γ) − u(x))² ν(de) < ∞` for all `(s, x)` (square-integrability for the compensated jump integral over all of E), OR (b) the integrand `[u(·+γ) − u − γᵀ∇u]` to be ν-integrable on all of E. Neither hypothesis is in the axiom signature.

  For **bounded jumps** (ν has compact support / `γ` bounded) this is fine. For **finite-intensity** ν (`ν(E) < ∞`) this is also fine. But for general σ-finite ν with mass near zero (e.g. infinite-intensity Lévy measures like α-stable), the unrestricted-domain compensator integral is divergent.

  The Lean axiom asserts the equation holds for the given X, u, T regardless of ν's structure. If ν is e.g. the standard α-stable Lévy measure with α ∈ (1, 2) and γ has linear growth in e near zero, both the `Compensated.stochasticIntegral` (over all E) and the compensator integral may individually diverge while their formal sum converges in the literature small/large-jump decomposition — i.e., the equation as stated could fail to make sense.

  In effect: the Lean `itoLevyFormula` axiom is faithful to Applebaum 4.4.7 ONLY for the **bounded-jump / finite-intensity** case, not for the general Lévy measure. The cited Applebaum 4.4.7 (2nd edition) is itself for finite Lévy measures (or for the small-jump truncation); for infinite Lévy measures Applebaum uses the small/large-jump decomposition (Thm 4.4.10 in 2nd ed). The Lean statement matches neither version cleanly — it asserts the global form without the small/large split.

- **Recommendation**: Either (a) add the hypothesis `∀ s, x, ∫⁻ e, ‖u(s, x+γ(s,x,e)) − u(s,x) − γ(s,x,e)ᵀ ∇u(s,x)‖² ν(de) < ⊤` as a parameter of the axiom (this is the standard L² hypothesis for the compensated jump integral over all of E to make sense); or (b) restrict the cited theorem to finite Lévy measures (ν(E) < ∞), with a note that the infinite-intensity case requires the small/large-jump decomposition; or (c) refactor the axiom to use the small/large split explicitly.

### Finding 4 — `continuousBSDEJ_exists_unique` Lipschitz hypothesis is *joint* in `(y, z, u)` only via norm-of-Z and L²-of-U; it omits the standard linear-growth condition on `f` at `(0, 0, 0)`

- **Severity**: MEDIUM (over-strong claim if proof would actually be attempted; under-stated for a complete Tang-Li match)
- **Location**: `BSDEJ/Existence.lean:73-79` (Lipschitz def), `:128` (use as hypothesis)
- **Evidence**:
  ```lean
  def Lipschitz {n d : ℕ}
      (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
      (ν : Measure E) (L : ℝ) : Prop :=
    ∀ s : ℝ, ∀ x : Fin n → ℝ, ∀ y₁ y₂ : ℝ, ∀ z₁ z₂ : Fin d → ℝ, ∀ u₁ u₂ : E → ℝ,
      |bsdej.f s x y₁ z₁ u₁ - bsdej.f s x y₂ z₂ u₂|
        ≤ L * (|y₁ - y₂| + ‖z₁ - z₂‖
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal.sqrt)
  ```
  This is Lipschitz in `(y, z, u)` jointly with constant `L`, with `u`'s contribution measured in `L²(ν)`. Note it does NOT include Lipschitz-in-`(s, x)` (the literature is also uniformly Lipschitz in `s, x` — but here `(s, x)` is fixed when comparing `y, z, u`, so this is correct, the literature only needs `(y, z, u)`-Lipschitz uniformly in `(s, x)`).

- **What's missing for full Tang-Li match**: The literature also requires the **integrability-at-zero** hypothesis: `E ∫_0^T |f(s, X_s, 0, 0, 0)|² ds < ∞` — without this, the Picard iteration's starting iterate `Y^{(0)} = E[g(X_T) | Filt_t]` lands in `S²` but the next iterate `Y^{(1)} = E[g(X_T) + ∫_t^T f(s, X_s, Y^{(0)}_s, Z^{(0)}_s, U^{(0)}_s) ds | Filt_t]` is not automatically in `S²` (the `∫_t^T |f(s, X_s, 0, 0, 0)| ds` part has no a priori bound). Tang-Li 1994 Thm 3.1 hypothesis (H2) explicitly states this integrability requirement. The Lean axiom omits it.

  Crucially: without this hypothesis, the axiom claims existence and uniqueness for arbitrary `f` satisfying ONLY Lipschitz at fixed `(s, x)` — Lipschitz alone does not bound `f` itself. Pick `f(s, x, y, z, u) := φ(s, x)` for an arbitrary non-integrable φ — this is Lipschitz with `L = 0` (no dependence on `y, z, u`), but `∫_t^T f(s, X_s, 0, 0, 0) ds = ∫_t^T φ(s, X_s) ds` could be non-integrable, and the BSDEJ would have NO `L²` solution. The Lean axiom would still claim one exists.

- **Why this matters**: The Lean axiom is strictly stronger than the cited Tang-Li theorem. The missing hypothesis is easy to add (and routinely included in the literature). The omission is in line with the maintainer's pattern of including SOME but not all literature hypotheses on the axiom signature.

- **Recommendation**: Add the hypothesis
  ```
  (_h_f0_sq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖bsdej.f s (X s ω) 0 0 (fun _ => 0)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  ```
  to `continuousBSDEJ_exists_unique`. Same for `bsdej_path_regularity`.

### Finding 5 — `bsdej_path_regularity`'s polynomial-dependence parametrization `C : T → L → norm_ξ → ℝ` is too weak to capture Bouchard-Elie 2008's explicit polynomial; the literature bound has `C = K · (1 + T)^{p} · e^{αLT} · (1 + ‖ξ‖²)` form

- **Severity**: MEDIUM (literature divergence with the cited paper)
- **Location**: `BSDEJ/PathRegularity.lean:145-148`
- **Evidence**:
  ```lean
  ∃ (C : ℝ → ℝ → ℝ → ℝ),
    let norm_ξ_real : ℝ := (∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
    0 < C T L norm_ξ_real ∧
    ∀ (M : ℕ) (_hM : 0 < M) ..., (...) ≤ ENNReal.ofReal (C T L norm_ξ_real * Δt)
  ```
- **Why this matters**: The "parameterized constant" change is M8 — it moves from a flat `∃ C : ℝ` to `∃ C : T → L → norm_ξ → ℝ`. Per the docstring on line 142-144, this is supposed to capture Bouchard-Elie 2008's polynomial dependence. But the statement only asserts `C T L norm_ξ_real > 0` — it doesn't pin `C` to any specific functional form. So any positive function `C` works.

  Bouchard-Elie 2008 SPA 118(1) Thm 2.1 gives an explicit bound of the form `C = K · (T + 1) · exp(αL²T) · (1 + E[|ξ|²]^{1/2})` (the specific exponent / multiplicative form varies by edition; the key feature is **polynomial-in-T-and-norm**, **exponential-in-Lipschitz-squared-times-T**). Capturing this explicitly is necessary for downstream numerical work (Bouchard-Elie's discrete-time approximation results use the rate `C · Δt^{1/2}` for the deep-BSDE method, and the explicit form of `C` matters for stability bounds).

  The Lean axiom doesn't pin `C` to any functional form, so a witness could pick `C T L norm_ξ_real := 1` (constant in all arguments). For a partition with mesh `Δt` very large (e.g. `Δt = T`, partition just `{0, T}`), the bound `C · Δt = T` is essentially trivial. For small `Δt`, the bound is also trivial since the LHS is bounded by the L²-sup-norms of `Y`, `Z`, `U` (already required by `IsBSDEJSolution`). So the "polynomial constant" form is purely cosmetic — any positive constant works.

  More precisely: the LHS is `sup over n of E[sup over t ∈ [t_n, t_{n+1}] of |Y_t − Y_{t_n}|²] + ‖Z − Z_avg‖²_{L²} + ‖U − U_avg‖²_{L²}`. All three terms are uniformly bounded above by the L²-sup-norm of `Y` plus `4 · ‖Z‖²_{L²} + 4 · ‖U‖²_{L²}` (the Z-avg / U-avg has the same L²-norm as Z/U by Jensen). So a trivially-large `C` (e.g. `C := 10 · sup_norm(Y) + 10 · ‖Z‖² + 10 · ‖U‖²`) works regardless of `Δt`.

  In effect: the constant `C` IS allowed to depend on the L²-norms of `(Y, Z, U)`, and any "depends on T, L, norm_ξ" function can be ≥ those L²-norms for any fixed `(T, L, norm_ξ)`. So the parametrization `C : T → L → norm_ξ → ℝ` does NOT actually constrain anything beyond positivity — it just enforces that `C` is a measurable function of `(T, L, norm_ξ)`, which is automatic. The "polynomial dependence" claim is a documentation overstatement.

- **Recommendation**: Either (a) pin the functional form of `C` more tightly — e.g. require `C T L norm_ξ_real ≤ K · (T + 1) · Real.exp(α * L^2 * T) * (1 + norm_ξ_real)` for some universal `K, α` — to capture the literature polynomial; or (b) drop the parametrization claim from the docstring (M8 fix is cosmetic in its current form).

### Finding 6 — `Compensated.itoIsometry_compensated_unified_existence` (Tier 1 #6) is strictly stronger than Applebaum 4.2.3: the existence of `F` and the martingale + càdlàg conjuncts are unconditional on φ, but Applebaum's theorem requires predictable square-integrable φ

- **Severity**: HIGH (literature divergence; documented but not closed)
- **Location**: `Poisson/Compensated.lean:1789-1819`
- **Evidence**: The axiom signature is
  ```lean
  axiom itoIsometry_compensated_unified_existence
      (N : PoissonRandomMeasure P ν) (φ : Ω → ℝ → E → ℝ) :
      ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
        MeasureTheory.Martingale F Filt P ∧                                  -- unconditional
        (Measurable ... → ∫⁻ ... → MeasureTheory.Martingale (F² - ∫φ²) Filt P) ∧  -- gated
        (∀ T, 0 < T → Measurable ... → ∫⁻ ... → L²-isometry) ∧                -- gated
        (∀ᵐ ω ∂P, ∀ t, ... càdlàg ...)                                       -- unconditional
  ```
  No hypothesis of measurability, predictability, or integrability on φ for the OUTER existence + martingale + càdlàg conjuncts. The maintainer's H6 docstring (Compensated.lean:1753-1764) explicitly acknowledges this gap and admits it's a "documentation-only" closure.

- **Why this matters**: Applebaum 2009 Thm 4.2.3 is for **predictable** φ in `L²(P × ds × dν)`. The Lean axiom asserts the existence of `F` (martingale + càdlàg) for ARBITRARY `φ : Ω → ℝ → E → ℝ`. For wild φ (say, non-measurable in `ω, s, e`), the axiom asserts that some `F` exists that's a martingale w.r.t. SOME filtration. This is strictly broader than Applebaum 4.2.3 supports.

  In practice this is harmless within the audited chain (every load-bearing caller threads through `IsBSDEJSolution`'s adaptedness layer + the bundled `h_progMeas` parameters which deliver predictability). But the axiom's content, taken in isolation, is not what Applebaum 4.2.3 says.

  Counterpart on the Brownian side (`itoIsometry_brownian_unified_existence`, Tier 1 #5) does take `h_meas`, `h_progMeas`, `h_sq_int_global` as parameters; the Compensated counterpart is asymmetric.

- **Recommendation**: Tighten `itoIsometry_compensated_unified_existence` to take `(h_meas : Measurable ...)`, `(h_progMeas : ...)`, `(h_sq_int_global : ∀ T, ...)` as parameters and condition the entire existence + 4 conjuncts on them (mirror the Brownian side). This converts the H6 "documentation-only" closure into a real signature-level closure. Pending that, this is the largest live literature-divergence in the chain.

### Finding 7 — `MultidimBrownianMotion.components_independent` correctly encodes joint independence of components but does NOT separately enforce joint Gaussianity with diagonal covariance

- **Severity**: LOW (the `W : Fin d → BrownianMotion P` field's individual BMs already deliver this; the field is technically redundant but mathematically correct)
- **Location**: `Brownian/Multidim.lean:43-52`
- **Evidence**:
  ```lean
  structure MultidimBrownianMotion (P : Measure Ω) [IsProbabilityMeasure P] (d : ℕ) where
    W : Fin d → LevyStochCalc.Brownian.BrownianMotion P
    components_independent :
      ProbabilityTheory.iIndepFun
        (fun (i : Fin d) (ω : Ω) (t : ℝ) => (W i).W t ω) P
  ```
- **Why this matters**: Karatzas-Shreve §2.5 (multidim BM) requires (i) each component to be a 1D BM and (ii) the components to be **jointly Gaussian with diagonal covariance**. The Lean encoding gives (i) directly (each `W i` is a `BrownianMotion P`, satisfying all 1D properties), and gives joint INDEPENDENCE (not just joint Gaussianity with diagonal covariance) via `iIndepFun`. Independence + each-marginal-Gaussian implies joint-Gaussian-with-diagonal-covariance (standard result, since independent normals are joint normals with diagonal covariance). So the structure is mathematically equivalent to Karatzas-Shreve §2.5's "d-dim BM" — the Lean encoding is actually slightly stronger than strictly necessary (independence is stronger than diagonal-covariance joint Gaussianity in general, but for 1D Gaussian marginals they coincide).

  The encoding `iIndepFun (fun i ω t => (W i).W t ω)` treats each component as a random variable into the path space `ℝ → ℝ` (with the Pi σ-algebra), and asserts joint independence of the d component path-RVs. This is the right statement.

- **Recommendation**: No action. This is honest.

### Finding 8 — `JumpDiffusion`'s SDE equation uses `X s` (point value) where the literature SDE uses `X_{s-}` (left limit), and the structure does not require càdlàg sample paths — same issue as Finding 2 propagated

- **Severity**: MEDIUM (linked to Finding 2; the convention mismatch is harmless for L²-integrable processes with càdlàg modifications, but the structure doesn't deliver that modification)
- **Location**: `Ito/Setting.lean:104-112`
- **Evidence**: The integrals in `is_solution` use `coeffs.μ s (X s ω) i` and `coeffs.σ s (X s ω) i` and `coeffs.γ s (X s ω') e i` — all at `X_s` not `X_{s-}`. The structure has no càdlàg field.
- **Why this matters**: Applebaum 2009 Chapter 6 SDEs use `X_{s-}` throughout. Ikeda-Watanabe IV.9 same. For càdlàg `X` with at most countably many jumps a.s., `X_s = X_{s-}` for Lebesgue-a.e. `s`, so the integrals coincide a.s. Hence for L²-integrable (Brownian + compensated-Poisson) integrals, the convention difference is a.s.-harmless. But the structure does NOT require `X` to be càdlàg in the first place. A jointly measurable `X` that is highly oscillatory in `s` (e.g. a "wild" L²-bounded process) would not have well-defined left limits, and `X_s` in the SDE integrals would not correspond to any literature object.

  The cited Applebaum 6.2.9 / Ikeda-Watanabe IV existence-uniqueness is for càdlàg adapted solutions. The Lean structure's `JumpDiffusion` is for non-càdlàg solutions, so it's not actually capturing the literature object.

- **Recommendation**: Add a `cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, ...` field (mirror of Compensated's). Or alternatively, write the SDE in terms of `X_{s-}` explicitly using `essential_left_limit` once `X`'s càdlàg property is established.

### Finding 9 — `jacodYor_representation`'s `ξ : Ω → ℝ` does NOT require `ξ` to be `ℱ_T`-measurable; the predicate only requires `ξ` to be Borel-measurable in the ambient σ-algebra

- **Severity**: MEDIUM (literature divergence)
- **Location**: `BSDEJ/MartingaleRepresentation.lean:81-83`
- **Evidence**:
  ```lean
  (T : ℝ) (_hT : 0 < T)
  (ξ : Ω → ℝ)
  (_h_meas : Measurable ξ)
  (_h_sq_int : ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤)
  ```
  `_h_meas : Measurable ξ` is plain Borel-measurability w.r.t. the ambient σ-algebra on `Ω`, not w.r.t. the joint filtration `ℱ_T = σ(W, Ñ) ⊔_T`.

- **Why this matters**: Jacod 1976 / Jacod-Shiryaev III.4.34 is about L²-martingales on the filtration `(ℱ_t)` generated by `(W, Ñ)`. The representation `ξ = E[ξ] + ∫_0^T Z dW + ∫_0^T ∫ U Ñ` is valid ONLY for `ξ` that is `ℱ_T`-measurable. For arbitrary Borel-measurable `ξ` (e.g. `ξ` depending on a random variable independent of `(W, N)`), the representation generally fails.

  Example counterexample to the Lean claim if it were a theorem (it's currently `sorry`'d so the gap doesn't bite): let `Ω = Ω_1 × Ω_2` where `(W, N)` lives on `Ω_1` and `B' : Ω_2 → ℝ` is a standard Gaussian independent of `(W, N)`. Then `ξ(ω) := B'(ω_2)` is Borel-measurable, L²-bounded, but `ξ - E[ξ] = B'` is independent of `(W, N)`, so cannot be represented as a sum of stochastic integrals against `W` and `Ñ`.

  The Lean theorem (as `sorry`'d) would assert existence of such a representation — which is **false** for non-`ℱ_T`-measurable `ξ`. Strictly speaking, since the proof is `sorry`, the theorem cannot be used to derive False; but if anyone replaced the sorry with a proof, the statement is too strong to prove (would require False).

  This is the "claim more than the cited theorem" pattern. The honest signature would add `(h_ξ_FT_meas : Measurable[ℱ_T] ξ)` where `ℱ_T` is the joint filtration's value at `T`.

- **Recommendation**: Add the `ℱ_T`-measurability hypothesis. Concretely:
  ```lean
  (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
  (_hFilt_BM : ∀ i, naturalFiltration (W.W i) ≤ Filt)
  (_hFilt_PRM : LevyStochCalc.Poisson.naturalFiltration N ≤ Filt)
  (_h_ξ_FT_meas : Measurable[(Filt T : MeasurableSpace Ω)] ξ)
  ```

### Finding 10 — `BrownianMotion.continuous_paths : ∀ᵐ ω ∂P, Continuous (fun t => W t ω)` requires continuity on ALL of ℝ, including `(−∞, 0)`, where `W` is conventionally 0; this is mathematically consistent but pedantically tighter than Karatzas-Shreve

- **Severity**: LOW (pedantic; harmless)
- **Location**: `Brownian/Construction.lean:60-65`
- **Evidence**:
  ```lean
  continuous_paths : ∀ᵐ ω ∂P, Continuous (fun t : ℝ => W t ω)
  negative_zero : ∀ s : ℝ, s < 0 → ∀ᵐ ω ∂P, W s ω = 0
  ```
- **Why this matters**: Karatzas-Shreve §2.1 defines BM on `[0, ∞)` only, and the path is continuous on `[0, ∞)`. The Lean structure extends to all of ℝ by setting `W_s = 0` for `s < 0` and requiring continuity on all of ℝ. The continuity at `t = 0` requires `lim_{t → 0+} W_t = W_0 = 0` (from the right) AND `lim_{t → 0−} W_t = 0` (from the left), the latter being trivial since `W_s = 0` for `s < 0`. The construction is consistent (the Wiener-measure-based existence axiom delivers it). But note `negative_zero` is pointwise-in-`s` almost-sure, not uniformly-in-ω: `∀ s < 0, ∀ᵐ ω, W s ω = 0` rather than the stronger `∀ᵐ ω, ∀ s < 0, W s ω = 0`. The two are equivalent under countable union of null sets + continuity (rationals are countable, continuity transfers from rationals to all reals on a co-null set), so this is fine for Brownian motion. But it could be tightened.

- **Recommendation**: No action required. Pedantic.

### Finding 11 — `PoissonRandomMeasure.integer_valued` field is correct for finite-intensity B; for B with `referenceIntensity ν B = ⊤` the predicate is silent — Applebaum 2.3.1(c) requires `P(N(B) = ∞) = 1` in that case, but the Lean structure does not encode it

- **Severity**: LOW (literature divergence on a corner case rarely used downstream)
- **Location**: `Poisson/RandomMeasure.lean:91-93`
- **Evidence**:
  ```lean
  integer_valued : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B ≠ ⊤ →
    ∀ᵐ ω ∂P, ∃ n : ℕ, N ω B = n
  ```
  Only applies when `referenceIntensity ν B ≠ ⊤`. For B with infinite intensity, no constraint.

- **Why this matters**: Applebaum 2009 Definition 2.3.1(c) (and Kallenberg 3.6) include the clause: for `μ(B) = ∞`, `P(N(B) = ∞) = 1`. This is a structural property — a Poisson random measure with infinite-intensity set has infinitely many points there a.s. The Lean structure does not encode this. A pathological `N` could satisfy `poisson_law`, `independent_disjoint`, `joint_past_future_independent`, and `integer_valued` (only for finite-intensity B) while having `N(ω, B) = 0` for some infinite-intensity B — this violates Applebaum 2.3.1.

  In practice this doesn't bite the audited chain (every compensated-integral construction restricts to `[0, T] × A` with `ν(A) < ∞` via the σ-finite decomposition). But pedantically the structure is weaker than the cited definition.

  Note: my predecessor in the 1st audit (`2026-05-20-archive/04_pure_mathematician.md`) Finding 9 raised this same issue. The 2nd audit's L10 fix added `integer_valued` but did NOT add the infinite-intensity clause. So this 1st-audit finding is still open.

- **Recommendation**: Add a field
  ```lean
  infinite_intensity_almost_surely : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B = ⊤ → ∀ᵐ ω ∂P, N ω B = ⊤
  ```

## Per-axiom verdicts on the Tier 1 + key derivative theorems

| Theorem / Axiom | Verdict | One-line note |
|---|---|---|
| `Brownian.BrownianMotion.exists` (Tier 1 #1) | EARNED | Karatzas-Shreve / Le Gall cited correctly. `joint_measurable` (L10) honestly satisfiable by Wiener-measure construction. `continuous_paths` extends to all ℝ (Finding 10, pedantic). |
| `Poisson.PoissonRandomMeasure.exists_of_sigmaFinite` (Tier 1 #2) | WEAK | Applebaum 2.3.1 cited. `integer_valued` (L10) is satisfiable. But the infinite-intensity-a.s.-∞ clause of Applebaum 2.3.1(c) is still missing (Finding 11). |
| `Brownian.Continuity.kolmogorovChentsov_modification` (Tier 1 #3) | EARNED | Faithful, matches Karatzas-Shreve 2.2.8 / Le Gall 2.9. `kolmogorov_modification_ae_eq` proved. |
| `Brownian.Martingale.brownian_martingale_rightCont` (Tier 1 #4) | EARNED | Le Gall citation correction (Theorem 2.13) honored. Blumenthal 0-1 + right-continuity. |
| `Brownian.Ito.itoIsometry_brownian_unified_existence` (Tier 1 #5) | EARNED | Karatzas-Shreve 3.2.6 + Le Gall 5.4 cited; signature takes `h_meas`, `h_progMeas`, `h_sq_int_global`. Asymmetric (richer) than the Compensated counterpart but in the correct direction. |
| `Poisson.Compensated.itoIsometry_compensated_unified_existence` (Tier 1 #6) | **WEAK** | The Compensated axiom's outer existence + martingale + càdlàg conjuncts are unconditional on φ — strictly broader than Applebaum 4.2.3, which is for predictable φ only. The H6 closure is "documentation-only" — see Finding 6. |
| `BSDEJ.Existence.continuousBSDEJ_exists_unique` (Tier 1 #9) | WEAK | Tang-Li / Andersson-Gnoatto-Patacca-Picarelli / Pardoux-Răşcanu cited correctly. Lipschitz hypothesis added (H4). The `Adapted` outer layer (vs literature `ProgMeasurable` — Finding 1), no càdlàg requirement (Finding 2), and missing linear-growth-at-zero hypothesis on `f` (Finding 4) keep this WEAK rather than EARNED. |
| `BSDEJ.PathRegularity.bsdej_path_regularity` (Tier 1 #10) | WEAK | Bouchard-Elie 2008 SPA 118(1) cited correctly. `Z_avg`/`U_avg` pinned (H3). But the `C : T → L → norm_ξ → ℝ` parametrization is cosmetic — any positive `C` works (Finding 5). Same `Adapted`-vs-`ProgMeasurable` gap as #9 (Finding 1). Same missing càdlàg requirement (Finding 2). |
| `Ito.JumpFormula.itoLevyFormula` (Tier 1 #11) | EARNED-with-CAVEAT | Applebaum 4.4.7 cited. All 4 terms pinned (no remaining existentials — C2 fully closed). Helpers (`gradient`, `hessian`, `levyGenerator`, `diffusionIntegrand`, `compensatorDriftIntegrand`) are honest. BUT the compensator drift integrates over ALL of E without small/large jump truncation; for general Lévy measures this is not Applebaum 4.4.7 globally — see Finding 3. The axiom is faithful for bounded/finite Lévy measures only. |
| `Ito.Setting.JumpDiffusion.exists_unique` (baseline sorry) | EARNED-with-CAVEAT | C3 closed (no constant-path witness). Lipschitz hypotheses honestly absent from the sorry'd theorem (would need adding for a real proof). Uses `X_s` not `X_{s-}` (Finding 8); no càdlàg field (Finding 2). Sorry is honest. |
| `BSDEJ.MartingaleRepresentation.jacodYor_representation` (baseline sorry) | WEAK | C4 closed at signature level (BM_integral and jump_integral pinned to canonical integrals). But `ξ` is only required to be Borel-measurable, not ℱ_T-measurable — Jacod 1976 requires the latter (Finding 9). The current sorry'd theorem is too strong; replacing the sorry with a real proof would require False (or finding the gap). |

## Persona-specific section: what would a research mathematician flag in a referee report?

If I were refereeing this library for a Mathlib PR, the top-of-the-list points would be:

1. **`Adapted` vs `ProgMeasurable`** (Finding 1). Every stochastic-calculus referee will catch this immediately because Mathlib already has `ProgMeasurable` and the difference between the two is well-known to be subtle (joint progressive measurability on the product σ-algebra is strictly stronger than per-time-t adaptedness). The fix is a one-line change in `IsBSDEJSolution` (replace `Adapted Filt Z` with `ProgMeasurable Filt Z`).

2. **No càdlàg field on `Y` / `X`** (Finding 2). The literature `S²` space is càdlàg-adapted. Replacing it with "jointly measurable + L²-sup-norm" is a structural deviation; the `sup` over an interval of a non-càdlàg jointly-measurable process is not even guaranteed to be measurable in `ω`.

3. **General Lévy measure handling in `itoLevyFormula`** (Finding 3). The unrestricted-domain Compensated integral + compensator drift over all of E is fine for bounded-jump / finite-intensity ν, but is the wrong statement for infinite-intensity Lévy measures (where the small/large-jump split is the standard approach in Applebaum). A working mathematician reading the axiom expecting Applebaum 4.4.7 would be confused by the apparent absence of the small/large split.

4. **`Compensated.itoIsometry_compensated_unified_existence` asymmetry with the Brownian side** (Finding 6). The Brownian-side axiom takes `h_progMeas` as a parameter; the Compensated-side does not. This is unjustified — Applebaum 4.2.3 is for predictable φ, exactly like Karatzas-Shreve 3.2.6 is for predictable H. The fix is a 5-line signature change.

5. **`jacodYor_representation` ξ is not pinned to ℱ_T-measurability** (Finding 9). Jacod 1976 is about ℱ_T-measurable ξ. The Lean theorem (as `sorry`'d) would be False for non-ℱ_T-measurable ξ. This is the kind of "the statement is too strong; the proof can never succeed" pattern that's harmless when sorry'd but indicates the signature was drafted without checking the theorem hypothesis.

I would NOT flag in a referee report:

- The `joint_measurable` field on `BrownianMotion` — this is a real improvement that brings the structure in line with Le Gall §2.1.
- The `integer_valued` field on `PoissonRandomMeasure` — also a real improvement (modulo the still-missing infinite-intensity clause, Finding 11, which is a corner case).
- The constant-path witness exclusion from `JumpDiffusion` (C3 closure) — genuinely closed.
- The `⟨0,0,0,ξ−𝔼[ξ]⟩` exclusion from `jacodYor_representation` (C4 closure) — genuinely closed at the signature level.
- The four-term pinning of `itoLevyFormula` (C2 closure) — substantively closed.
- The `Filt ≥ joint natural filtration` constraint (M11 closure) — verified mathematically sound in my peer P5's Finding 3. `Filt = ⊤` is not exploitable because it forces M_W and M_N to be a.s.-constant (contradicting the M_W pin for non-zero Z).

## What I couldn't verify

- **Web access to the cited textbooks failed**: WebFetch on the Le Gall 2016 PDF returned binary content; Applebaum and Karatzas-Shreve are paywalled. I confirmed the existence of the cited papers via WebSearch (Tang-Li 1994 SICON 32(5):1447-1475 confirmed; Bouchard-Elie 2008 SPA 118(1):53-75 confirmed). For specific theorem-number content (e.g. Le Gall Thm 5.4 says "Itô isometry" vs something else) I have relied on secondary citations and my own pre-existing knowledge of the standard references — high-confidence but not first-source-verified.
- **No counterexample exhibition**: For Finding 1 (Adapted vs ProgMeasurable), Finding 3 (small/large jump split), and Finding 9 (ξ not ℱ_T-measurable), I described the issues structurally but did not construct a concrete Lean witness exhibiting the divergence. Each would take ~30-80 lines of Mathlib boilerplate. For a soundness-only audit lens, the descriptions suffice; for a "construct a Lean exploit" audit lens, this is deferred.
- **No closure verification of Pardoux-Răşcanu Theorem 4.79's hypothesis list**: I claim the linear-growth-at-zero hypothesis is part of Tang-Li 1994 Thm 3.1 hypothesis (H2). This is standard but I did not re-derive it from a first-source PDF.

## Recommendations for the project (≤ 5 bullets)

- **Replace `Adapted Filt Z/U` with `ProgMeasurable Filt Z/U`** in `IsBSDEJSolution` (`BSDEJ/Definition.lean:160-162`) and `JumpDiffusion.is_solution`. This is a one-line change per predicate that closes the largest current literature-divergence (Finding 1). It does NOT require any axiom changes — the existing inner `h_progMeas` bundles deliver the data needed.
- **Add càdlàg fields to `IsBSDEJSolution.Y` and `JumpDiffusion.X`**, mirroring the càdlàg conjunct already present in `Compensated.itoIsometry_compensated_unified_existence`. This brings the predicate in line with literature `S²` and makes the `sup` in the path-regularity bound well-posed (Finding 2).
- **Tighten `itoIsometry_compensated_unified_existence`** to take `h_meas`, `h_progMeas`, `h_sq_int_global` as parameters, mirroring the Brownian-side axiom. This converts H6's documentation-only closure into a real signature-level closure (Finding 6).
- **Either restrict `itoLevyFormula` to finite Lévy measures, or add the small/large jump split** to handle infinite-intensity Lévy measures correctly (Finding 3). Currently the axiom is faithful only for the bounded-jump case.
- **Add `ℱ_T`-measurability hypothesis to `jacodYor_representation`** (Finding 9). The current statement is too strong to ever be proved.

## Files read

- `D:\LevyStochCalc\redteam_findings\shared_context_override.md` (full)
- `D:\LevyStochCalc\redteam_findings\2026-05-20-archive\04_pure_mathematician.md` (full, predecessor's report)
- `D:\LevyStochCalc\redteam_findings\05_proof_theorist.md` (full, parallel peer report)
- `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Definition.lean` (full, 203 lines)
- `D:\LevyStochCalc\LevyStochCalc\BSDEJ\Existence.lean` (full, 138 lines)
- `D:\LevyStochCalc\LevyStochCalc\BSDEJ\PathRegularity.lean` (full, 176 lines)
- `D:\LevyStochCalc\LevyStochCalc\BSDEJ\MartingaleRepresentation.lean` (full, 112 lines)
- `D:\LevyStochCalc\LevyStochCalc\Ito\Setting.lean` (full, 148 lines)
- `D:\LevyStochCalc\LevyStochCalc\Ito\JumpFormula.lean` (full, 198 lines)
- `D:\LevyStochCalc\LevyStochCalc\Brownian\Construction.lean` (full, 173 lines)
- `D:\LevyStochCalc\LevyStochCalc\Brownian\Multidim.lean` (full, 248 lines)
- `D:\LevyStochCalc\LevyStochCalc\Brownian\MultidimIto.lean` (full, 80 lines)
- `D:\LevyStochCalc\LevyStochCalc\Poisson\RandomMeasure.lean` (full, 207 lines)
- `D:\LevyStochCalc\LevyStochCalc\Brownian\SimplePredictableRefine.lean` (lines 2080-2200, axiom + downstream definitions)
- `D:\LevyStochCalc\LevyStochCalc\Poisson\Compensated.lean` (lines 1750-1970, axiom + downstream definitions)
- `D:\LevyStochCalc\tools\cited_axioms.md` (first 200 lines, then skimmed)

## Lean LSP / web tools called

- `mcp__lean-lsp__lean_verify` on `continuousBSDEJ_exists_unique`, `bsdej_path_regularity`, `itoLevyFormula`, `JumpDiffusion.exists_unique` — all returned clean axiom sets matching `tools/full_audit_output.txt` (modulo `sorryAx` for the two baseline sorries).
- `mcp__lean-lsp__lean_leansearch` — confirmed `MeasureTheory.ProgMeasurable` vs `MeasureTheory.Adapted` are genuinely distinct Mathlib predicates with the strict-implication theorems requiring extra hypotheses (continuity-in-time or discrete-time).
- `WebSearch` — confirmed Tang-Li 1994 SICON 32(5):1447-1475 and Bouchard-Elie 2008 SPA 118(1):53-75 are real papers with the claimed titles and venues.
- `WebFetch` Le Gall 2016 PDF — returned binary content, could not extract.
