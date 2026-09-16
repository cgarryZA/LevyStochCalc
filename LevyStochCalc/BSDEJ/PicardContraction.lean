/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardContractionNorm
import LevyStochCalc.BSDEJ.PicardContractionBounds
import LevyStochCalc.BSDEJ.PicardContractionContraction

/-!
# The exponentially weighted norm of a triple and the Picard contraction

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.wNorm` — the exponentially weighted norm of a triple.
* `LevyStochCalc.BSDEJ.Solves.density` — the pointwise energy density of a triple.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput_of_two_le` — the weighted norm of
  the difference of two Picard outputs is at most `6 L² / β` times that of the difference of
  the inputs, at every Young weight `β ≥ 2`.
* `LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput` — the same with the factor `1/4`,
  at the Young weight `β = max 2 (24 L²)`.

## Parts

* `LevyStochCalc.BSDEJ.PicardContractionNorm` — the weighted norm and the pointwise energy
  density of a triple.
* `LevyStochCalc.BSDEJ.PicardContractionBounds` — energies on a horizon, the pointwise Young
  bound and the real-variable core of the contraction.
* `LevyStochCalc.BSDEJ.PicardContractionContraction` — the contraction of the weighted norm by
  one Picard step.
-/
