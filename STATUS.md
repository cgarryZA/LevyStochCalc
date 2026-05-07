# LevyStochCalc — Status (2026-05-03)

## Headline

**Both Itô-Lévy isometries on simple integrands are fully axiom-clean** for Brownian and compensated-Poisson stochastic integrals.

```
LevyStochCalc.Brownian.Ito.simpleIntegral_isometry              ✅ axiom-clean
LevyStochCalc.Poisson.Compensated.simpleIntegral_isometry       ✅ axiom-clean
```

Axiom set for both: `[propext, choice, Quot.sound]` (Lean's standard axioms only — no `sorryAx`, no project axioms).

## What this proves

For a partition `0 = t_0 < t_1 < ⋯ < t_N ≤ T` and adapted bounded coefficients `ξ_i : Ω → ℝ`:

**Brownian:**
```
∫⁻ ω, ‖∑ i, ξ_i ω · (W_{t_{i+1}} ω − W_{t_i} ω)‖² ∂P
  = ∫⁻ ω, ∫⁻ s in [0,T], ‖H.eval s ω‖² ds ∂P
```

**Compensated Poisson** (over `ℝ × E` with intensity `volume.restrict [0,∞) ⊗ ν`):
```
∫⁻ ω, ‖∑ i, ξ_i ω · Ñ((t_i, t_{i+1}] × A_i, ω)‖² ∂P
  = ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖φ.eval s e ω‖² ∂ν ds ∂P
```

## Foundations delivered

### Compensated Poisson (`Poisson/Compensated.lean`)

| Lemma | Result |
|---|---|
| `tsum_pow_div_factorial_mul_nat` | `∑' n, r^n/n! · n = r·exp(r)` |
| `tsum_pow_div_factorial_mul_nat_sq` | `∑' n, r^n/n! · n² = (r²+r)·exp(r)` |
| `poissonMeasure_integral_id` | `∫ n ∂Poisson(r) = r` (Poisson mean — **not in Mathlib**) |
| `poissonMeasure_integral_id_sq` | `∫ n² ∂Poisson(r) = r²+r` |
| `poissonMeasure_variance` | `Var(Poisson(r)) = r` |
| `compensated_mean_zero` | `E[Ñ(B)] = 0` |
| `compensated_second_moment` | `E[Ñ(B)²] = ν̂(B)` |
| `compensated_sq_integrable` | `Ñ(B)² ∈ L¹(P)` |
| `simpleIntegral_diagonal` | lintegral form: `∫⁻ ‖ξ_i Ñ(B_i)‖² = ν̂(B_i) · ∫⁻ ‖ξ_i‖²` |
| `simpleIntegral_offDiagonal` | for i < j: `∫ (ξ_i Ñ(B_i))(ξ_j Ñ(B_j)) = 0` |
| `simpleIntegral_diagonal_bochner` | Bochner form via `ofReal_integral_eq_lintegral_ofReal` |
| `cross_sq_integrable` | cross-product `(ξ_i Ñ_i)(ξ_j Ñ_j)` integrable via AM-GM |
| `simpleIntegral_sq_bochner_eq` | Bochner LHS: `∫(∑a_i)² = ∑ ν̂(B_i)·∫ξ_i²` |
| `simpleIntegral_sq_lintegral_eq` | LHS reduction (lintegral form) |
| **`simpleIntegral_isometry`** | **The Itô-Lévy isometry on simples** |

Plus 7 RHS-reduction helpers (`eval_eq_sum_indicator`, `fullRect_disjoint`, `referenceIntensity_fullRect`, `lintegral_indicator_fullRect`, `eval_sq_eq_sum_indicator`, `lintegral_eval_sq`, `lintegral_eval_sq_outer`).

### Brownian (`Brownian/Ito.lean`)

| Lemma | Result |
|---|---|
| `simpleIntegral_diagonal` | lintegral form: `∫⁻ ‖ξ_i ΔW_i‖² = ENNReal.ofReal(t_{i+1}-t_i) · ∫⁻ ‖ξ_i‖²` |
| `simpleIntegral_offDiagonal` | for i < j: `∫ (ξ_i ΔW_i)(ξ_j ΔW_j) = 0` |
| `brownian_increment_sq_integrable` | `(W_t − W_s)² ∈ L¹(P)` via Gaussian `MemLp 2` |
| `simpleIntegral_diagonal_bochner` | Bochner form |
| `cross_sq_integrable` | cross product integrable via AM-GM |
| `simpleIntegral_sq_bochner_eq` | Bochner LHS expansion |
| `simpleIntegral_sq_lintegral_eq` | LHS reduction |
| **`simpleIntegral_isometry`** | **The Itô isometry on simples** |

Plus 8 helpers (`SimplePredictable` structure, `eval`, `simpleIntegral_eq_sum`, partition-related lemmas, `lintegral_eval_sq_outer`, etc.).

### Structural / Probabilistic Foundations

- **`PoissonRandomMeasure`** (Poisson/RandomMeasure.lean): time-aware structure on `ℝ × E` with `referenceIntensity := volume.restrict [0,∞) ⊗ ν`, `compensated B ω := (N ω B).toReal − ν̂(B).toReal`, structural fields including `joint_past_future_independent` (σ-algebra-level past⊥future independence used in `simpleIntegral_offDiagonal`).
- **`BrownianMotion`** (Brownian/Construction.lean): structure with `increment_gaussian`, `negative_zero`, `joint_increment_independent` fields.
- `brownian_martingale`, `brownian_quadVar` (Brownian/Martingale.lean): both axiom-clean.
- `gaussianReal_fourth_moment`, `gaussianReal_second_moment` and the iterated-derivative chain for `mgf` of Gaussian: all axiom-clean.

## What's still sorry'd (`tools/sorry_baseline.txt`, 19 entries)

```
LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite
LevyStochCalc.Poisson.Compensated.itoLevyIsometry
LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral
LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral
LevyStochCalc.Poisson.Compensated.cadlag_modification_exists
LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry
LevyStochCalc.Brownian.BrownianMotion.exists
LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification
LevyStochCalc.Brownian.Continuity.brownian_continuous_modification
LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous
LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists
LevyStochCalc.Brownian.Ito.itoIsometry
LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral
LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique
LevyStochCalc.Ito.JumpFormula.itoLevyFormula
LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation
LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique
LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity
```

## Path to full I02 (`Compensated.itoLevyIsometry`)

The remaining work to close the I02 axiom completely:

1. **`simplePredictable_dense_L2`** — density of simple predictable integrands in L²(dP ⊗ ds ⊗ dν). Mathlib's `MemLp.exists_simpleFunc_eLpNorm_sub_lt` gives density via Mathlib `SimpleFunc`, but bridging to our `SimplePredictable` structure requires a refinement argument (rectangular partitions in (s, e) × ω-dependent coefficients). Estimated 5-7 days.
2. **`stochasticIntegral`** — define concretely as the L²-limit of `simpleIntegral` on density-approximating sequence. Requires #1. Standard Banach completion argument. Estimated 2-3 days.
3. **`itoLevyIsometry`** (headline) — pass-to-the-limit argument: `‖simpleIntegral(φn)‖_L² → ‖stochasticIntegral(φ)‖_L²` (continuity of L²-norm) and `‖φn‖_L² → ‖φ‖_L²` (definition of L²-convergence). Auto-derives once #1 + #2 land.
4. **`L2Isometry.itoLevyIsometry`** — 1-line wrapper (already structurally clean).

Same path closes Brownian's `itoIsometry`, `quadVar_stochasticIntegral`, `martingale_stochasticIntegral`.

## Path to other dissertation axioms (Cu01, Cu03, Cu05)

These remain genuinely hard:

- **Cu03** (`itoLevyFormula`): requires a continuous Itô formula (Mathlib doesn't have one) + jump telescoping. Multi-week.
- **Cu01** (`continuousBSDEJ_exists_unique`): requires Jacod-Yor martingale representation theorem (a stand-alone multi-week port) + Picard contraction.
- **Cu05** (`bsdej_path_regularity`): gluing layer over Cu01 + Cu03 + Doob's L²-maximal + Grönwall.

## Status of dissertation usage

The main dissertation's **Path X argument** (representation-free BSDEJ via `SatisfiesRecursion` predicate) **does not depend on `itoLevyIsometry`** as of the 2026-05-03 audit. The capstone theorem `Dissertation.ContXiong.deep_bsdej_convergence` is fully axiom-clean modulo Lean's standard axioms.

This means:
- The simples-isometry result (this milestone) is sufficient evidence that the I02 axiom would land if pushed further; the discrete chain doesn't actually require it.
- Closing the full I02 axiom replaces a "nice-to-have" axiom with a theorem, giving the dissertation a "no project axioms at all" story.
- `cx_value_satisfies_bsdej` (CX01, the Contribution C1 statement) requires Cu03 (continuous Itô-Lévy formula), so closing Cu03 is also dissertation-relevant for full C1 deax.

## Active work (2026-05-03 onwards)

**Density push committed** (PRIORITY 1.3 / 3.2). Skeleton in place with named sub-helpers:

### Compensated side (Compensated.lean)

- ✅ `truncation_pointwise_tendsto` — axiom-clean. For each `x : ℝ`, `(‖x − clip_M x‖₊)² → 0` as `M → ∞` (eventually 0 once `M ≥ ⌈|x|⌉`).
- ✅ `truncation_dominated` — axiom-clean. `(‖x − clip_M x‖₊)² ≤ (‖x‖₊)²` via case analysis.
- ⚠️ `truncation_L2_converges` — outer DCT applied (using bound = inner double integral of `(‖φ‖)²`); two sub-sorries: (a) AEMeasurable of `F_M` in ω (Tonelli; hits unification timeouts on `Ω × ℝ × E` associativity), (b) pointwise convergence of inner double integral (needs nested DCT).
- ⚠️ `simplePredictable_dense_L2_bounded` — sorry'd (constructive approximation via dyadic time × σ-finite mark partition + Bochner-integral-averaged coefficient).
- ⚠️ `simplePredictable_dense_L2` — diagonal-sequence combination, sorry'd.

### Brownian side (Brownian/Ito.lean)

Mirror skeleton in place with same three helpers (no mark dimension):
- ⚠️ `truncation_L2_converges_brownian` — sorry'd (mirror of Compensated; will inherit the same Tonelli unification issue).
- ⚠️ `simplePredictable_dense_L2_bounded_brownian` — sorry'd.
- ⚠️ `simplePredictable_dense_L2` — sorry'd.

### What's blocking each

- AEMeasurable for `F_M ω`: Tonelli requires double application of `Measurable.lintegral_prod_right'` with associativity reshaping (`Ω × ℝ × E` ↔ `(Ω × ℝ) × E`). Lean's elaborator hits `whnf`/`isDefEq` heartbeat timeouts. Likely solvable with explicit `MeasurableEquiv`-mediated reassociation, or by working in product-measure form throughout. ~1-2 days of careful type-massage.
- Pointwise inner convergence: structurally identical to outer DCT but on volume.restrict (Icc 0 T) × ν product. Same unification challenge.
- Bounded-approximation: requires constructing the approximating sequence concretely. The conditional-expectation-on-refining-σ-algebra approach (cleaner) needs L²-martingale convergence machinery. The direct dyadic-refinement approach needs Bochner integration over rectangles + Lebesgue differentiation. Either way, ~3-5 days.

Then `stochasticIntegral` concrete def via L²-completion (~2-3 days), `itoLevyIsometry` headline (~1 day glue), and `L2Isometry.itoLevyIsometry` wrapper auto-clears.

**Cu03 push (PRIORITY 4)** is the hard follow-up — continuous Itô formula + jump telescoping. Multi-week.

## Build status

```
$ bash tools/lint.sh
PASS: lake build + audit at or below baseline.
```

8400 jobs, no errors, no new sorries beyond baseline.

## C0b infrastructure landed (2026-05-07)

C0b is the partition-refinement + L²-Cauchy chain that lifts
`simpleIntegral_isometry` (already axiom-clean) to the genuine
L²-completed Itô integral. The chain closed this week, axiom-clean
end-to-end:

| Step | Lemma | What it gives |
|---|---|---|
| C0b.1 | `SimplePredictable.refine` | refine to a finer partition |
| C0b.2 | `SimplePredictable.refine_eval` | refining preserves `eval` |
| C0b.3 | `SimplePredictable.simpleIntegral_refine` | refining preserves `simpleIntegral` |
| C0b.4 | `commonRefinement_left/right` | merge two partitions to a common refinement (via `Finset.orderEmbOfFin`) |
| C0b.5 | `commonRefinement_compat` | both refinements share `N` and `partition` |
| C0b.6 | `sub_on_common` | difference SimplePredictable on the common partition |
| C0b.7 | `simpleIntegral_sub_on_common` | linearity of `simpleIntegral` |
| C0b.7-aux | `eval_sub_on_common` | linearity of `eval` |
| C0b.8 | `diff_isometry_simple` | `‖∫H₁ − ∫H₂‖² = ‖H₁.eval − H₂.eval‖²` |
| C0b.9 | `cauchy_of_L2_dense_simple` | eval-Cauchy → integral-Cauchy |
| C0b.10-pre1 | `simpleIntegral_lintegral_sq_finite_brownian` | `∫⁻ ω, ‖∫H‖² < ∞` |
| C0b.10-pre2 | `simpleIntegral_memLp_brownian` | `MemLp 2 P` witness |
| C0b.10-pre3 | `simpleIntegralLp_brownian` | lift to `Lp ℝ 2 P` |

All in `LevyStochCalc/Brownian/SimplePredictableRefine.lean`. Each
landed in its own commit, axiom set `[propext, choice, Quot.sound]`.

### Next steps

- **C0b.10**: bridge `cauchy_of_L2_dense_simple` to `CauchySeq` in
  `Lp ℝ 2 P` (using the `eLpNorm`-vs-`lintegral` translation), then
  apply `MeasureTheory.Lp.completeSpace`/`Lp.cauchy_complete_eLpNorm` to
  extract the L² limit.
- **Closing baseline**: with the L² limit in hand, close
  `stochasticIntegral_strong_exists_brownian` (currently the lone sorry
  underlying `Brownian.Ito.{itoIsometry, quadVar_stochasticIntegral,
  martingale_stochasticIntegral}` — three baseline entries).
- **Mirror for compensated Poisson**: same C0b chain with `Compensated.SimplePredictable`,
  closing `Compensated.{itoLevyIsometry, quadVar, martingale, cadlag}`
  (four baseline entries) and auto-closing `Poisson.L2Isometry.itoLevyIsometry`.
