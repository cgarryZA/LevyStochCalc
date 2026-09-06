/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.Existence
import LevyStochCalc.Ito.JumpFormula

/-!
# Time averages of BSDEJ integrands

`conditionalTimeAverage_Z` and `conditionalTimeAverage_U` are the projections of the
integrands `Z, U` of a BSDEJ solution onto their averages over the intervals of a partition,
the interval representatives in the path-regularity estimates of Bouchard & Elie (2008).

The path-regularity bound itself is not stated here. Its previous formulation
`bsdej_path_regularity` (cited result #10) asserted the rate `C · Δt` for every measurable
terminal function `g` and every measurable forward process `X`; for `ξ = 1_{W_T > 0}` the
projection error of `Z` decays like `Δt^{1/2}` only (Geiss, Geiss & Gobet 2012), so the
statement was refutable and was retired on 2026-09-06 together with its corollaries
`bsdej_path_regularity_linear_rate` and `bsdej_U_L2_regularity_linear_rate`. It will be
restated, with the regularity hypotheses of Bouchard & Elie (a Lipschitz `g` and a jump
diffusion `X` with Lipschitz coefficients), once the `L²` integrals are built over the joint
filtration of `(W, N)` (`Plan.md`, work package X2).

## Source

* Bouchard, B. & Elie, R., "Discrete-time approximation of decoupled
  Forward-Backward SDE with jumps", Stochastic Processes Appl. **118(1)**,
  **2008**, pp. 53–75.
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

end Regularity

end LevyStochCalc.BSDEJ.PathRegularity
