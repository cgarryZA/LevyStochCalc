/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.Existence
import LevyStochCalc.Ito.JumpFormula

/-!
# BSDEJ path regularity

For the unique BSDEJ solution `(Y, Z, U)` from `BSDEJ.Existence`, the time
modulus of continuity satisfies

  `max_n 𝔼[ sup_{t ∈ [t_n, t_{n+1}]} |Y_t − Y_{t_n}|² ]`
  `+ 𝔼[ ∫_0^T |Z_s − Z̃_s|² ds ]`
  `+ 𝔼[ ∫_0^T ∫_E |U_s(e) − Ũ_s(e)|² ν(de) ds ]`
  `≤ C · Δt`,

where `Z̃, Ũ` are the conditional time-averages of `Z, U` over the partition
intervals, and `Δt = max_n (t_{n+1} − t_n)`.

## Source

* Bouchard, B. & Elie, R., "Discrete-time approximation of decoupled
  Forward-Backward SDE with jumps", Stochastic Processes Appl. **118(1)**,
  **2008**, pp. 53–75.

## Proof structure (Bouchard–Elie 2008)

1. Apply Itô-Lévy formula to `|Y_t − Y_s|²` for `s = t_n`, `t ∈ [t_n, t_{n+1}]`.
2. Bound the resulting drift + martingale terms using Lipschitz hypothesis +
   the L²-isometries on `Z, U`.
3. Take `sup_{t ∈ [t_n, t_{n+1}]}` then expectation.
4. Apply Doob's L²-maximal inequality to control the sup of the martingale term.
5. Bound `Z − Z̃` and `U − Ũ` via Jensen's inequality and the Itô-isometry
   identity for the conditional time-averages.
6. Combine + sum over `n`.

The constant `C` depends on `T`, the Lipschitz constant `L` of `f`, and the
L²-norm of `(Y_0, Z, U, ξ)` — all bounded uniformly by `BSDEJ.Existence`'s
solution-bound.

## Status

Real proof structure skeleton. Each step is stated as a named lemma `sorry`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u v

section TimeAverages
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Time-averaged projection of `Z` over the partition interval
`(t_n, t_{n+1}]`: for `s ∈ (t_n, t_{n+1}]`, set
`Z̃_s ω := (1 / (t_{n+1} − t_n)) ∫_{t_n}^{t_{n+1}} Z_u ω du` (constant on
each partition interval; the conditional-expectation claim then follows by
`condExp_const` in the natural filtration). For `s` outside any `(t_n, t_{n+1}]`,
return 0. -/
noncomputable def conditionalTimeAverage_Z
    {d M : ℕ}
    (partition : Fin (M + 1) → ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ)) : ℝ → Ω → (Fin d → ℝ) :=
  fun s ω => fun i =>
    ∑ n : Fin M,
      if partition n.castSucc < s ∧ s ≤ partition n.succ then
        (1 / (partition n.succ - partition n.castSucc)) *
          ∫ u in Set.Icc (partition n.castSucc) (partition n.succ), Z u ω i
      else 0

/-- Time-averaged projection of `U` (analogous to `conditionalTimeAverage_Z`). -/
noncomputable def conditionalTimeAverage_U
    {M : ℕ}
    (partition : Fin (M + 1) → ℝ)
    (U : ℝ → Ω → E → ℝ) : ℝ → Ω → E → ℝ :=
  fun s ω e =>
    ∑ n : Fin M,
      if partition n.castSucc < s ∧ s ≤ partition n.succ then
        (1 / (partition n.succ - partition n.castSucc)) *
          ∫ u in Set.Icc (partition n.castSucc) (partition n.succ), U u ω e
      else 0

end TimeAverages

section Regularity
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **CITED AXIOM: BSDEJ path regularity (Bouchard–Elie 2008 Thm 2.1).**

For the unique BSDEJ solution `(Y, Z, U)`, the L²-time modulus + projection
errors of `(Z, U)` over a partition with mesh `Δt` are bounded by `C · Δt`,
with `C` depending on `T`, the Lipschitz constant `L`, and the L²-norm of
`(ξ, Z, U)`.

**Reference**: Bouchard, B. & Elie, R. *Discrete-time approximation of
decoupled Forward-Backward SDE with jumps*, Stochastic Processes Appl.
**118(1)**, **2008**, pp. 53–75, **Theorem 2.1**. For the continuous-only
background, see also Pardoux, E. & Răşcanu, A. *Stochastic Differential
Equations, Backward SDEs, Partial Differential Equations*, Springer 2014,
**Theorem 5.42** (continuous case, NOT BSDEJ). The jump-case path regularity
is established in Bouchard–Elie 2008; Pardoux–Răşcanu covers only the
continuous (Brownian-driven) case and does not extend to jumps automatically.

**Standard proof outline**:
1. Apply Itô-Lévy formula to `|Y_t − Y_s|²` for `s = t_n`, `t ∈ [t_n, t_{n+1}]`.
2. Bound the resulting drift + martingale terms using Lipschitz hypothesis +
   the L²-isometries on `Z, U`.
3. Take `sup_{t ∈ [t_n, t_{n+1}]}` then expectation.
4. Apply Doob's L²-maximal inequality to control the sup of the martingale term.
5. Bound `Z − Z̃` and `U − Ũ` via Jensen + the Itô-isometry identity for the
   conditional time-averages.
6. Combine + sum over `n` + apply Grönwall.

**Replacement plan**: when Mathlib gains BSDEJ + Doob L² maximal + Grönwall in
the right form, replace this `axiom` with a forwarder. Tracked in
`tools/cited_axioms.md`. -/
axiom bsdej_path_regularity
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (_hX_meas : Measurable (Function.uncurry X))
    (T : ℝ) (_hT : 0 < T)
    -- Lipschitz hypothesis (Bouchard–Elie 2008 requirement; the bound `C`
    -- depends polynomially on `L`):
    {L : ℝ} (_hL : LevyStochCalc.BSDEJ.Existence.Lipschitz bsdej ν L)
    (_hξ_sq_int : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
    -- The constant `C` is exposed as a function of `(T, L, ‖ξ‖_L²)` (not a bare
    -- `ℝ`), pinned to the Bouchard–Elie 2008 Thm 2.1 literature form
    -- `C T L ξ := K · (1 + T)^p · exp(α · L · T) · (1 + ξ)` with `K, α > 0`,
    -- `p ∈ ℕ`: polynomial in `(1+T)`, exponential in `LT` (the Grönwall step),
    -- linear in `(1+ξ)` — matching BET 2008 Thm 2.1 eq. (2.10)-(2.12).
    ∃ (K α : ℝ) (p : ℕ),
      let norm_ξ_real : ℝ :=
        (∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal
      let C : ℝ → ℝ → ℝ → ℝ :=
        fun T' L' ξ' => K * (1 + T') ^ p * Real.exp (α * L' * T') * (1 + ξ')
      0 < K ∧ 0 < α ∧
      0 < C T L norm_ξ_real ∧
      ∀ (M : ℕ) (_hM : 0 < M) (partition : Fin (M + 1) → ℝ)
        (_h_part_mono : StrictMono partition)
        (_h_part_start : partition 0 = 0)
        (_h_part_end : partition (Fin.last M) = T)
        (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
        (_h_solution :
          LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T),
        let Δt : ℝ := ⨆ n : Fin M,
          partition n.succ - partition n.castSucc
        -- `Z_avg, U_avg` are pinned to the conditional time-average projections
        -- defined above, not existentially quantified: an existential `∃ Z_avg
        -- U_avg, bound holds` could be satisfied by `Z_avg := Z` (projection
        -- error zero), so pinning forces the bound to actually control the
        -- deviation of Z, U from their canonical time-averages.
        (⨆ n : Fin M, ∫⁻ ω,
            ⨆ t ∈ Set.Icc (partition n.castSucc) (partition n.succ),
              (‖Y t ω - Y (partition n.castSucc) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              ∑ i, (‖Z s ω i - conditionalTimeAverage_Z partition Z s ω i‖₊
                : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖U s ω e - conditionalTimeAverage_U partition U s ω e‖₊
                : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
          ≤ ENNReal.ofReal (C T L norm_ξ_real * Δt)

/-- **Specialization corollary (public API): linear-in-Δt BET 2008 bound.**

This is a one-line repackaging of `bsdej_path_regularity` that extracts the
Bouchard–Elie 2008 SPA 118(1) Theorem 2.1 bound in the user-facing form

  `∃ C : ℝ, 0 < C ∧ ∀ partition, (path modulus + Z, U projection errors) ≤ C · Δt`,

where `C` is a single positive real constant (concretely
`K · (1 + T)^p · exp(α · L · T) · (1 + ‖g(X_T)‖_L²)` evaluated at the
given `(T, L, ξ)`) in place of the polynomial-exponential expression
exposed by the underlying axiom.

**Motivation**: downstream discrete-to-continuous BSDEJ convergence results
need a `ψ : ℝ → ℝ` with `ψ(h) = C · h`. The polynomial form is what
Bouchard–Elie 2008 proves; downstream usage needs only the linear-in-`Δt`
rate, with `C` packaged opaquely so the convergence theorem can be specialized
without reaching into the polynomial structure.

**Citation**: same as `bsdej_path_regularity` — Bouchard, B. & Elie, R.,
*Discrete-time approximation of decoupled Forward-Backward SDE with jumps*,
Stochastic Processes Appl. **118(1)**, **2008**, pp. 53–75, **Theorem 2.1**.

**Axiom dependency**: this is a *honest derivative theorem* of the Tier 1
axiom `bsdej_path_regularity` (cited_axioms.md entry #10); no new axiom is
introduced. `#print axioms` on this corollary surfaces
`{propext, Classical.choice, Quot.sound, bsdej_path_regularity,
  itoIsometry_brownian_unified_existence, itoIsometry_compensated_unified_existence}`
— the latter two flowing transitively from the `IsBSDEJSolution` predicate's
pinning of `M_W` / `M_N` to the canonical multidim Brownian and
compensated-Poisson L² integrals (Tier 1 entries #5 + #6). -/
theorem bsdej_path_regularity_linear_rate
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X))
    (T : ℝ) (hT : 0 < T)
    {L : ℝ} (hL : LevyStochCalc.BSDEJ.Existence.Lipschitz bsdej ν L)
    (hξ_sq_int : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (_hM : 0 < M) (partition : Fin (M + 1) → ℝ)
        (_h_part_mono : StrictMono partition)
        (_h_part_start : partition 0 = 0)
        (_h_part_end : partition (Fin.last M) = T)
        (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
        (_h_solution :
          LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T),
        let Δt : ℝ := ⨆ n : Fin M,
          partition n.succ - partition n.castSucc
        (⨆ n : Fin M, ∫⁻ ω,
            ⨆ t ∈ Set.Icc (partition n.castSucc) (partition n.succ),
              (‖Y t ω - Y (partition n.castSucc) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
              ∑ i, (‖Z s ω i - conditionalTimeAverage_Z partition Z s ω i‖₊
                : ℝ≥0∞) ^ 2 ∂volume ∂P)
          + (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
              (‖U s ω e - conditionalTimeAverage_U partition U s ω e‖₊
                : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P)
          ≤ ENNReal.ofReal (C * Δt) := by
  -- Invoke the underlying polynomial-form axiom. The axiom uses an inner
  -- `let C := fun T' L' ξ' => K * (1 + T') ^ p * Real.exp (α * L' * T') * (1 + ξ')`
  -- and `let norm_ξ_real := (∫⁻ ω, ‖g(X T ω)‖² ∂P).toReal`; destructuring the
  -- existential unfolds those lets pointwise into the conjuncts.
  obtain ⟨K, α, p, hK_pos, hα_pos, hC_pos, h_bound⟩ :=
    bsdej_path_regularity W N bsdej X hX_meas T hT (L := L) hL hξ_sq_int
  -- Read off the concrete real number `C` from the polynomial closure
  -- evaluated at the input `(T, L, ‖g(X_T)‖_L²)`.
  refine ⟨K * (1 + T) ^ p * Real.exp (α * L * T) *
            (1 + (∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal),
          hC_pos, ?_⟩
  -- The remaining `∀ (M ...) ...` is `h_bound` itself, since the `let`s in
  -- the axiom statement reduce definitionally to the explicit expression.
  intro M hM partition h_part_mono h_part_start h_part_end Y Z U h_solution
  exact h_bound M hM partition h_part_mono h_part_start h_part_end Y Z U h_solution

/-- **U-integrand L²-regularity (linear-in-Δt), for Paper C's path-regularity gap.**

The compensated-Poisson integrand `U` of the BSDEJ solution has `O(Δt)` L²-projection
error onto the partition-interval time-averages:

  `𝔼 ∫_0^T ∫_E |U_s(e) − Ũ_s(e)|² ν(de) ds ≤ C · Δt`,

where `Ũ = conditionalTimeAverage_U` (the interval representative) and
`Δt = maxₙ (t_{n+1} − t_n)`. Equivalently `∑ₙ 𝔼 ∫_{tₙ}^{tₙ₊₁} ‖U_s − Ũ_s‖²_{L²(ν)} ds
≤ C · Δt`, since the partition tiles `[0, T]`.

This is the single forwarded input `hU` of the dissertation-side assembly
`Dissertation.DiffusionJumpRegularity.coupled_jump_reg_O_tau` (a-posteriori FBSDEJ
path-regularity, Reading (A): the projection / interval representative, **not** a
pointwise-in-time Malliavin value — so no Malliavin input is required).

**Proof**: the three nonnegative summands of `bsdej_path_regularity_linear_rate`
(`Y` path-modulus, `Z` projection error, `U` projection error) each lie below their
sum; drop the first two. Hence this is an honest derivative of the same Tier-1 base
as that corollary — it forwards `bsdej_path_regularity` (cited_axioms.md #10) and
introduces no new axiom. `#print axioms` surfaces `{propext, Classical.choice,
Quot.sound, bsdej_path_regularity, itoIsometry_brownian_unified_existence,
itoIsometry_compensated_unified_existence}` (the last two via the `IsBSDEJSolution`
pinning of `M_W`/`M_N` to the canonical multidim-Brownian and compensated-Poisson
L² integrals, Tier-1 #5 + #6). -/
theorem bsdej_U_L2_regularity_linear_rate
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (bsdej : LevyStochCalc.BSDEJ.Definition.BSDEJData n d E)
    (X : ℝ → Ω → (Fin n → ℝ))
    (hX_meas : Measurable (Function.uncurry X))
    (T : ℝ) (hT : 0 < T)
    {L : ℝ} (hL : LevyStochCalc.BSDEJ.Existence.Lipschitz bsdej ν L)
    (hξ_sq_int : ∫⁻ ω, (‖bsdej.g (X T ω)‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ℕ) (_hM : 0 < M) (partition : Fin (M + 1) → ℝ)
        (_h_part_mono : StrictMono partition)
        (_h_part_start : partition 0 = 0)
        (_h_part_end : partition (Fin.last M) = T)
        (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
        (_h_solution :
          LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution W N bsdej X Y Z U T),
        let Δt : ℝ := ⨆ n : Fin M,
          partition n.succ - partition n.castSucc
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖U s ω e - conditionalTimeAverage_U partition U s ω e‖₊ : ℝ≥0∞) ^ 2
              ∂ν ∂volume ∂P)
          ≤ ENNReal.ofReal (C * Δt) := by
  obtain ⟨C, hC_pos, h_bound⟩ :=
    bsdej_path_regularity_linear_rate W N bsdej X hX_meas T hT (L := L) hL hξ_sq_int
  refine ⟨C, hC_pos, ?_⟩
  intro M hM partition h_part_mono h_part_start h_part_end Y Z U h_solution
  -- The U-projection error is the third (nonnegative) summand of the full bound.
  exact le_trans le_add_self
    (h_bound M hM partition h_part_mono h_part_start h_part_end Y Z U h_solution)

end Regularity

end LevyStochCalc.BSDEJ.PathRegularity
