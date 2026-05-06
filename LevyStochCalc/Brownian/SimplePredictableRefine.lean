import LevyStochCalc.Brownian.Ito

/-!
# WIP: SimplePredictable refinement and diff isometry

C0b requires a "diff isometry" on `simpleIntegral`:
  ‖simpleIntegral W H₁ T - simpleIntegral W H₂ T‖²_{L²(P)}
    = ‖H₁.eval - H₂.eval‖²_{L²(P ⊗ dt)}.

For this, we need to construct a SimplePredictable `H_diff` with
* `partition`: union of partitions of `H₁` and `H₂` (sorted, deduped),
* per-piece `ξ`: `ξ₁_refined - ξ₂_refined` (the refined values of the two
  inputs aligned to the common partition),

and prove

* `simpleIntegral W H_diff T = simpleIntegral W H₁ T - simpleIntegral W H₂ T`
  (linearity on common partition + telescoping refinement-invariance);
* `H_diff.eval = H₁.eval - H₂.eval` pointwise (refinement-invariance of `eval`);
* then apply `simpleIntegral_isometry` to `H_diff`.

The required machinery (~300 LOC):

  1. `SimplePredictable.refine`: refine to a finer partition while preserving
     `eval` and `simpleIntegral` (telescoping).
  2. `SimplePredictable.commonRefinement`: pair two SimplePredictables onto a
     common partition.
  3. `SimplePredictable.sub`: subtract on a common partition (linear over ξ).
  4. Diff isometry as a corollary of (3) + the existing
     `simpleIntegral_isometry` (B's A2).

Once that lands, C0b becomes:

  `noncomputable def itoIntegral_brownian (W) (H) (T) : Ω → ℝ :=`
    `(Lp.toFun (Cauchy-limit-in-Lp of (simpleIntegral W (Hn n) T).toLp))`

via `simplePredictable_dense_Lp_brownian` + diff isometry + `Lp.completeSpace`.

This file is intentionally empty (no declarations) — it's a documentation
placeholder marking the C0b blocker. The actual A3/A4 (provisional) and B4
(provisional) commits remain in force until C0b lands.
-/
