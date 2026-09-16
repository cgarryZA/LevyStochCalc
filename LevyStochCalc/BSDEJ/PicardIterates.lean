/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardIteratesStep
import LevyStochCalc.BSDEJ.PicardIteratesCauchy

/-!
# The Picard iterates of a backward equation with jumps

An admissible triple carries the measurability, progressive measurability and square
integrability the Picard step consumes, and the output of a step along an admissible triple is
again admissible, so the step iterates from any admissible starting triple. On the sequence of
iterates the one-step contraction of the exponentially weighted norm `wNorm` at the Young weight
`β = max 2 (24 L²)` gives a geometric bound on the weighted norm of consecutive differences, and
hence a Cauchy estimate for the iterates in `wNorm` and in the unweighted energies.

## Parts

* `LevyStochCalc.BSDEJ.PicardIteratesStep` — admissible triples, the drift and the Picard step
  along them, and the sequence of Picard iterates.
* `LevyStochCalc.BSDEJ.PicardIteratesCauchy` — subadditivity and lower bounds for the weighted
  norm, and the geometric Cauchy estimate along the iterates.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.Admissible` — the triples on which the Picard step is defined.
* `LevyStochCalc.BSDEJ.Solves.IsStep` — an output triple of the Picard step, together with the
  drift along the input triple.
* `LevyStochCalc.BSDEJ.Solves.picardSeq` — the sequence of Picard iterates from an admissible
  starting triple.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.Admissible.exists_drift` — the generator frozen along an
  admissible triple has a progressively measurable version of finite energy.
* `LevyStochCalc.BSDEJ.Solves.Admissible.exists_step` — the Picard step along an admissible
  triple has an admissible output triple.
* `LevyStochCalc.BSDEJ.Solves.wNorm_picardSeq_geom` — the weighted norm of consecutive
  iterates decays geometrically with ratio `1/4`.
* `LevyStochCalc.BSDEJ.Solves.wNorm_picardSeq_cauchy` — the iterates are Cauchy for the
  weighted norm.
* `LevyStochCalc.BSDEJ.Solves.energy_picardSeq_cauchy` — the value processes of the iterates
  are Cauchy for the energy on the horizon.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/
