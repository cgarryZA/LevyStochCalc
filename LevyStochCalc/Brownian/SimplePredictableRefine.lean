import LevyStochCalc.Brownian.Ito

/-!
# SimplePredictable refinement and diff isometry (C0b infrastructure)

This file builds the partition-refinement machinery needed to upgrade
`itoIntegral_brownian` from its provisional constant-function definition
(A3/A4) to the genuine L²-completion via `LinearIsometry.extend`.

## Roadmap

* `SimplePredictable.refine` — lift `H : SimplePredictable Ω T` from its
  partition `π` onto a finer partition `π'`. The user supplies an index
  map `idxMap : Fin M → Fin H.N` saying which old piece each new piece
  belongs to.
* `SimplePredictable.refine_eval` — `(H.refine ...).eval = H.eval`
  pointwise.
* `SimplePredictable.simpleIntegral_refine` — refining preserves
  `simpleIntegral`.
* `SimplePredictable.commonRefinement` — common refinement of two
  `SimplePredictable`s sharing the same final partition point.
* `simpleIntegral_diff_isometry_simple` — the diff isometry on simples.
* `cauchy_of_L2_dense_simple` — Cauchy property of the simple integrals
  for an L²-Cauchy approximating sequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Refine** a simple predictable to a finer partition. Given
`H : SimplePredictable Ω T` (on partition `π`) and a finer partition `π'`
of length `M + 1`, plus an index map `idxMap : Fin M → Fin H.N` and
inclusion proofs that each new piece `(π' j.castSucc, π' j.succ]` is
contained in the `idxMap j`-th old piece
`(H.partition (idxMap j).castSucc, H.partition (idxMap j).succ]`,
return the refined `SimplePredictable` on `π'` whose `ξ` agrees with `H.ξ`
under `idxMap`.

Requires `π'` to end at the same point as `H.partition` (`h_last`); the
common refinement of two `SimplePredictable`s sharing this endpoint
satisfies this naturally. -/
noncomputable def SimplePredictable.refine
    {T : ℝ} (H : SimplePredictable Ω T)
    (M : ℕ) (π' : Fin (M + 1) → ℝ)
    (h_zero : π' 0 = 0)
    (h_last : π' (Fin.last M) = H.partition (Fin.last H.N))
    (h_strictMono : StrictMono π')
    (idxMap : Fin M → Fin H.N)
    (_h_idx_le : ∀ j : Fin M,
      H.partition (idxMap j).castSucc ≤ π' j.castSucc)
    (_h_idx_ge : ∀ j : Fin M,
      π' j.succ ≤ H.partition (idxMap j).succ) :
    SimplePredictable Ω T where
  N := M
  partition := π'
  partition_zero := h_zero
  partition_le_T := h_last ▸ H.partition_le_T
  partition_strictMono := h_strictMono
  ξ := fun j ω => H.ξ (idxMap j) ω
  ξ_bounded := fun j => H.ξ_bounded (idxMap j)
  ξ_measurable := fun j => H.ξ_measurable (idxMap j)

end LevyStochCalc.Brownian.Ito
