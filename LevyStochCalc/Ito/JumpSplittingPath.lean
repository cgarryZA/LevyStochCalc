/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSplittingPathSums
import LevyStochCalc.Ito.JumpSplittingPathDecomposition

/-!
# Finite-activity splitting along the left limits of a prescribed path

A pathwise jump sum is an integral against the random measure of a jump coefficient read along
the left limits of a path, so it is determined by a coefficient bundle, a random measure and a
path; no relation between the bundle and the path enters. Indexing the left-limit jump sum, the
left limits themselves and the drift carrying the left-limit compensator on that triple rather
than on a jump-diffusion solution therefore loses nothing, and lets the coefficient bundle be
changed — to the bundle cut down to a mark set, say — with the path held fixed.

The splitting of a path into a vector Itô process and a left-limit jump sum likewise separates
into what is read along the evaluation path, namely the coefficients and the jump sum, and what
is asked of the split path, namely the integral equation and right continuity on the nonnegative
half-line. The two paths are therefore free of one another.

## Parts

* `LevyStochCalc.Ito.JumpSplittingPathSums` — the left limits, the left-limit jump sum and the
  compensator drift indexed on a bundle, a random measure and a path, and their regularity.
* `LevyStochCalc.Ito.JumpSplittingPathDecomposition` — the splitting of a path satisfying the
  integral equation, at a fixed time and at all nonnegative times, and along a jump diffusion.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.leftLimPathAt` — the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt` — the pathwise sum of the jumps carried by a
  mark set, with the jump coefficient of a bundle evaluated at the left limits of a path.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt` — the drift of a bundle along a path
  with the compensator of its left-limit jump coefficient subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt_path`,
  `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt_path` — the jump-diffusion-indexed jump
  sum and drift as the instances of these at the path of the jump diffusion.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt_congr_of_eqOn` — two bundles whose jump
  coefficients agree on a mark set have the same jump sum over it.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt_congr_of_eqOn` — two bundles with the
  same drift whose jump coefficients agree on a mark set have the same compensator drift.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeftAt_zeroExtPos`,
  `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeftAt_zeroExtPos` — the jump sum and the
  compensator drift at a positive time are unchanged by the zero extension of the left-limit
  jump integrand.
* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeftAt_of_path` — the splitting
  at a fixed nonnegative time, for a path satisfying the integral equation.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_of_path` — the same identity
  almost surely at all nonnegative times simultaneously, for a right-continuous such path.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft_of_path`,
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion` — the case of
  the coefficients read along the path of a jump diffusion, and of its own path.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_integrableOn_windowLeft`,
  `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeft`,
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft` — the same three statements
  indexed on a jump diffusion rather than on a coefficient bundle and a path.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/
