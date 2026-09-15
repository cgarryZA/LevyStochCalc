/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.Existence
import LevyStochCalc.Ito.JumpFormula

/-!
# Time averages of BSDEJ integrands

`conditionalTimeAverage_Z` and `conditionalTimeAverage_U` replace the integrands `Z, U` of a
BSDEJ solution by their pathwise averages over the intervals of a partition: on each cell
`(t_n, t_{n+1}]` the value is `(1 / (t_{n+1} − t_n)) ∫_{t_n}^{t_{n+1}} Z_u(ω) du`, which is
measurable at the right end `t_{n+1}` of the cell and is the `L²(dt)`-orthogonal projection of
the path onto the cell-constant functions. They are not the `ℱ_{t_n}`-conditional projections
`E[(1/Δ) ∫ Z du | ℱ_{t_n}]` of Bouchard & Elie (2008), despite the name: the conditional
projection is the orthogonal projection onto the smaller space of adapted cell-constant
processes, so its projection error dominates the pathwise one, and a rate for it transfers
to these averages, not conversely.

The path-regularity bound itself is not stated here. The formulation `bsdej_path_regularity`,
asserting the rate `C · Δt` for every measurable terminal function `g` and every measurable
forward process `X`, is refutable: for `ξ = 1_{W_T > 0}` the projection error of `Z` decays
like `Δt^{1/2}` only (Geiss, Geiss & Gobet 2012) (`tools/cited_axioms.md`, `Retired #10`).
Restating it, with the regularity hypotheses of Bouchard & Elie (a Lipschitz `g` and a jump
diffusion `X` with Lipschitz coefficients), over the common filtration the `L²` integrals now
take is `Plan.md`'s work package A7; its proof in the literature rests on Malliavin calculus,
which this library does not have.

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

/-- The pathwise cell average of `Z` over the partition intervals: for `s ∈ (t_n, t_{n+1}]`,
`Z̃_s ω := (1 / (t_{n+1} − t_n)) ∫_{t_n}^{t_{n+1}} Z_u ω du`, constant on each interval and
measurable at its right end; `0` for `s` outside every `(t_n, t_{n+1}]`. -/
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

/-- The pathwise cell average of `U` over the partition intervals, mark by mark (the analogue
of `conditionalTimeAverage_Z`). -/
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
