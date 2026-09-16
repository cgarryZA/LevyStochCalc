/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain
import LevyStochCalc.Ito.JumpFormulaGeneralShiftAtomSum

/-!
# The capped jump layer over a prescribed evaluation path

The pathwise sum of the jumps carried by a mark set reads the jump coefficient at a prescribed
path of states; the point values of a jump diffusion and its left limits are the two cases of
interest. Capping the arrival times at the horizon turns that sum into the piecewise translation
carrying the jump path, and the identities describing the capped sum — its value once the arrival
time has passed the horizon, its increment across an arrival time inside the window, its
constancy strictly between consecutive arrival times — are statements about the ordering of the
arrival times and the atomic structure of the random measure, so they hold for every evaluation
path. The telescope's jump sum is accordingly the sum, over the enumerated atoms of the window,
of the increments of the state function taken at the left limits of the jump path and displaced
by the jump coefficient read at the prescribed states.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.jumpSumAt` — the pathwise sum of the jumps carried by a mark set
  over a window, with the jump coefficient evaluated along a prescribed path of states.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt` — those jumps accumulated up to an arrival time
  capped at the horizon.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.jumpSumAt_path`,
  `LevyStochCalc.Ito.JumpFormula.jumpSumAt_leftLimPath` — the point-evaluated and left-limit jump
  sums as the two instances of the prescribed-path jump sum.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_of_le`,
  `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq` — past the horizon the capped jump sum
  is the jump sum over the whole window and no longer moves with the index.
* `LevyStochCalc.Ito.JumpFormula.jumpSumAt_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.jumpSumAt_eq_sum_atomEnum_horizon` — the jump sum over a
  sub-window as the sum of the jump coefficient over the enumerated atoms it contains.
* `LevyStochCalc.Ito.JumpFormula.cappedJumpSumAt_succ_eq_add_gamma` — between consecutive arrival
  times inside the window the capped jump sum gains the jump coefficient carried by the later
  arrival time and its mark.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_jumpSumAt_eq_cappedJumpSumAt`,
  `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumAt_eq` — strictly between consecutive
  capped arrival times the jump path is the continuous part translated by the capped jump sum.
* `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTermAt_eq_sum_atomEnum`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermAt` — the telescope's jump
  sum as the atom sum of the increments of the state function across the jumps.
* `LevyStochCalc.Ito.JumpFormula.add_shift_eq_of_ae_forall_at_of_path`,
  `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumAt_eq_of_path` — the same piecewise
  translation for any path that splits into a continuous part and that jump sum.
* `LevyStochCalc.Ito.JumpFormula.sum_range_jumpTermAt_eq_sum_atomEnum_of_path`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermAt_of_path` — the same
  identification of the telescope's jump sum, the base points being the left limits of the
  translated path and the jump coefficient still being read along the prescribed path of states.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumLeft_eq`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermLeft` — the same two
  conclusions for the jump sum evaluated along the left limits of the path, whose jump
  coefficient is read at the same state as the base point of each increment.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumLeft_eq_of_path`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermLeft_of_path` — those two
  conclusions for a translated path carrying the left-limit jump sum, whose base points are the
  left limits of that path.
* `LevyStochCalc.Ito.JumpFormula.ae_forall_add_cappedJumpSumPoint_eq`,
  `LevyStochCalc.Ito.JumpFormula.ae_exists_atomEnum_sum_range_jumpTermPoint` — the same two
  conclusions for the point-evaluated jump sum.

## Parts

* `LevyStochCalc.Ito.JumpFormulaGeneralShiftCappedChain` — the prescribed-path jump sum and its
  capped chain: the identities past the horizon, the jump sum against an atom enumeration, the
  increment across an arrival time inside the window, and the piecewise translation strictly
  between consecutive capped arrival times.
* `LevyStochCalc.Ito.JumpFormulaGeneralShiftAtomSum` — the telescope's jump sum as the atom sum
  of the increments of the state function across the jumps, almost surely and for a translated
  path, together with the point-evaluated and left-limit instances.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/
