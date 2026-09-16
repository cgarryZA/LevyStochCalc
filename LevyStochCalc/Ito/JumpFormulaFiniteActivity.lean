/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaFiniteActivityDrift
import LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion
import LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide

/-!
# Reconciling the two drifts of the finite-activity Itô–Lévy formula

Splitting a finite-activity jump diffusion into a continuous Itô part and a pathwise jump sum
replaces the drift `μ` by `μ` minus the compensator `∫_A γ dν` of the jumps, while the pathwise
jump sum contributes the intensity integral of the jump increment `u(x + γ) − u(x)`. The
Itô–Lévy formula instead carries the drift `μ` itself and the compensator-drift integrand
`u(x + γ) − u(x) − ∑ᵢ γᵢ ∂ᵢu`. The two presentations differ by the first-order term
`∑ᵢ ∂ᵢu ∫_A γᵢ dν`, which the compensator subtracted from the drift supplies exactly.

The accumulated jumps taken at the arrival times capped at the horizon are constant in the index
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms. Between consecutive arrival times inside the window that accumulation gains
exactly the jump coefficient carried by the later arrival time and the mark enumerated with it,
and strictly between them it does not move at all, so capping the arrival times themselves makes
the accumulated jumps the piecewise translation carrying the jump path.

## Module organisation

The material is split across three modules, all in the `LevyStochCalc.Ito.JumpFormula` namespace
and all re-exported here:

* `LevyStochCalc.Ito.JumpFormulaFiniteActivityDrift` — the drift reconciliation and the Itô–Lévy
  identity assembled from the split-drift and jump-sum identities.
* `LevyStochCalc.Ito.JumpFormulaFiniteActivityExhaustion` — the jumps accumulated up to the capped
  arrival times, the matching of an in-window chain with the enumerated atom times, the
  right-continuous regularisation, and the exhaustion of a path by its arrival times.
* `LevyStochCalc.Ito.JumpFormulaFiniteActivityJumpSide` — the capped arrival times as a chain of
  stopping times and the telescope's jump sum as a sum over the enumerated atoms.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.cappedJumpSum` — the jumps accumulated up to the arrival time
  capped at the horizon.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.setIntegral_compensatorDriftIntegrand_eq_sub` — the mark
  integral of the compensator-drift integrand as the jump increment's mark integral minus the
  first-order term.
* `LevyStochCalc.Ito.JumpFormula.setIntegral_firstOrder_add_compensatorDrift` — the drift
  reconciliation over a time window.
* `LevyStochCalc.Ito.JumpFormula.splitDrift_pointwise`,
  `LevyStochCalc.Ito.JumpFormula.setIntegral_splitDrift_dictionary` — the non-stochastic
  integrands of Itô's formula in the prepended coordinates, taken against the drift with the
  jump compensator subtracted, as the drift integrand minus the first-order term.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum` — the Itô–Lévy identity in
  the vocabulary of `driftIntegrand` and `compensatorDriftIntegrand`, from the split-drift
  identity and the jump-sum identity.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSum_succ_eq` — past the horizon the capped jump sum
  no longer moves.
* `LevyStochCalc.Ito.JumpFormula.ae_eq_of_ae_eq_of_le_jumpTime` — an identity holding almost
  everywhere on each event where the chain of arrival times has passed the horizon holds almost
  everywhere.
* `LevyStochCalc.Ito.JumpFormula.sum_range_ite_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.sum_range_ite_eq_sum_atomEnum_exists` — the in-window members of
  a chain of times are matched with the entries of the strictly monotone enumeration of the
  window's atom times.
* `LevyStochCalc.Ito.JumpFormula.progressivelyMeasurable_rightCont`,
  `LevyStochCalc.Ito.JumpFormula.markedProgressivelyMeasurable_rightCont`,
  `LevyStochCalc.Ito.JumpFormula.jumpTime_chain_rightCont` — the chain data and the progressive
  measurability of the integrands for the right-continuous regularisation of a filtration.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpTime` — the arrival times capped at the horizon.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpTime_chain_of_complete` — the capped arrival times
  are an increasing chain of stopping times starting at the origin.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSum_eq_cappedJumpSum`,
  `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSum_eq` — strictly between consecutive
  capped arrival times the accumulated jumps are constant, so the jump path is the continuous
  part translated by them.
* `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTerm_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTerm_eq_sum_atomEnum_of_shift`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTerm` — the telescope's jump
  sum is the sum, over the enumerated atoms, of the increments of the state function across the
  jumps, read at the left limits of the path.
* `LevyStochCalc.Ito.JumpFormula.jumpSum_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.cappedJumpSum_succ_eq_add_gamma`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_cappedJumpSum_succ` — the jump sum over a
  sub-window as the sum over the enumerated atoms it contains, and the increment of the capped
  jump sum between consecutive arrival times as the jump coefficient at the later arrival time
  and its mark.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/
