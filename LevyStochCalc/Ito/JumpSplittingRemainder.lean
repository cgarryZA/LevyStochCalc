/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSplittingRemainderDecomposition
import LevyStochCalc.Ito.JumpSplittingRemainderVanishing

/-!
# The jump of a solution across an arrival time

A path satisfying the jump-diffusion integral equation is, at every nonnegative time, the sum of
a vector Itô process, the pathwise sum of the jumps carried by a mark set of finite intensity and
the compensated integral of the jump coefficient cut to the complement of that set — the
*remainder*. No support restriction on the jump coefficient enters: the remainder carries the
jumps outside the mark set.

Across an arrival time carrying a mark of the set, the path therefore jumps by the jump
coefficient read at its left limit plus the jump of the remainder. Along an exhausting sequence
of mark sets the remainders vanish uniformly on every bounded window, by Doob's `L²` maximal
inequality against the Itô–Lévy isometry, so the jump of the path at such an arrival time is
exactly the jump coefficient.

## Parts

* `LevyStochCalc.Ito.JumpSplittingRemainderDecomposition` — the splitting of a path with
  remainder, at a fixed time and at all nonnegative times, and the jump across an arrival time
  up to the jump of the remainder.
* `LevyStochCalc.Ito.JumpSplittingRemainderVanishing` — the uniform vanishing of the remainders
  along a subsequence of the spanning sets and the jump of a solution across an arrival time.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path`
  — the splitting with remainder at a fixed nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path` — the
  same identity almost surely at all nonnegative times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/
