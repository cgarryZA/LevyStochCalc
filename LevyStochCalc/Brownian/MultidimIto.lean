/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Multidim
import LevyStochCalc.Brownian.ItoL2Completion

/-!
# Multidimensional Brownian Itô integral

The multidim L² Itô integral `∫_0^T Z_s · dW_s := ∑_i ∫_0^T Z_s^i dW_s^i`,
defined as the sum (over components `i : Fin d`) of the 1D Brownian Itô
integrals `LevyStochCalc.Brownian.SimplePredictableRefine.stochasticIntegral`
against the component Brownian motions `W.W i`.

For each component, the integrand `(s, ω) ↦ Z s ω i` must be:
* jointly measurable (`h_meas`),
* progressively measurable w.r.t. the natural filtration of `W.W i`
  (`h_progMeas`),
* L²-bounded on every `[0, T']`, `T' > 0` (`h_sq_int_global`).

These per-component hypotheses are exactly the ones the 1D primitive
requires; the multidim version just threads them through.

This file is in its own module (not in `Multidim.lean`) because the 1D
stochastic integral primitive lives in `SimplePredictableRefine.lean`,
which transitively imports `Multidim.lean` via `Brownian/Ito.lean`. Putting
the multidim integral here breaks the cycle.

## Reference

* Karatzas–Shreve §3.2 (multidim Itô integral as component sum).
* Le Gall §5.4 (Itô integral of vector-valued processes).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}

/-- The multidim Brownian Itô integral
`(∫_0^T Z_s · dW_s)(ω) = ∑_i ∫_0^T Z_s^i dW_s^i (ω)`.

`Z s ω i` is the `i`-th component of the integrand at `(s, ω)`. The result
at time `T` is the sum (over components) of the 1D Itô integrals against
the component Brownian motions `W.W i`.

Each component's 1D integral is well-defined by
`LevyStochCalc.Brownian.SimplePredictableRefine.stochasticIntegral`, which
itself extracts a process satisfying the unified-existence axiom
`itoIsometry_brownian_unified_existence`. -/
noncomputable def stochasticIntegral
    (W : MultidimBrownianMotion P d)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (h_meas : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (h_progMeas : ∀ i : Fin d, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration (W.W i)).seq t)
          inferInstance)
        (fun p : Ω × ℝ => Z p.2 p.1 i))
    (h_sq_int_global : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  fun ω => ∑ i : Fin d,
    LevyStochCalc.Brownian.Ito.stochasticIntegral
      (W.W i) (fun ω' s => Z s ω' i)
      (h_meas i) (h_progMeas i) (h_sq_int_global i) T ω

end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim
