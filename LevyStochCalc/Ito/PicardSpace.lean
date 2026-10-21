/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.PicardSpaceDiscrete
import LevyStochCalc.Ito.PicardSpaceBieleckiEDist
import LevyStochCalc.Ito.PicardSpaceBieleckiQuotient

/-!
# The complete metric space of bounded processes

This file equips the space `LevyStochCalc.Ito.Picard.SBoundedProcess` of L²-sup-bounded adapted
processes (from `LevyStochCalc.Ito.PicardBieleckiNorm`) with the metric structure needed to apply
Banach's fixed-point theorem to the Picard map.

## Contents

* A discrete metric and the resulting `MetricSpace` / `CompleteSpace`
  instances on `LevyStochCalc.Ito.Picard.SBoundedProcess`.
* `bieleckiEDist`, `LevyStochCalc.Ito.Picard.SBoundedProcess.WithBielecki` — the
  Bielecki-weighted extended pseudometric and its carrier type, and the almost-everywhere
  quotient `LevyStochCalc.Ito.Picard.SBoundedProcess.AEQuot` on which it becomes a genuine
  `EMetricSpace`.

The existence/uniqueness statement itself is
`LevyStochCalc.Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn` in
`Ito/PicardWellPosed.lean`. The section note "The `IsRegular` hypothesis and the `S²` norm" of
`LevyStochCalc.Ito.PicardSpaceBieleckiQuotient` records why that theorem takes
`LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs.IsRegular`, why the Bielecki norm is not the `S²`
norm, and where each step of the Picard chain lives.

The Banach fixed-point conclusion is in `LevyStochCalc.Ito.PicardFixedPoint`.

## Parts

* `LevyStochCalc.Ito.PicardSpaceDiscrete` — the constant-zero witness, the discrete distance and
  the `MetricSpace` / `CompleteSpace` instances on `LevyStochCalc.Ito.Picard.SBoundedProcess`.
* `LevyStochCalc.Ito.PicardSpaceBieleckiEDist` — Euclidean Minkowski on `Fin n → ℝ`,
  subadditivity of `bieleckiNorm`, and the pseudo-edist `bieleckiEDist` with its diagonal and
  symmetry laws.
* `LevyStochCalc.Ito.PicardSpaceBieleckiQuotient` —
  `LevyStochCalc.Ito.Picard.SBoundedProcess.WithBielecki`, the triangle inequality and the
  `PseudoEMetricSpace` instance, the separation quotient
  `LevyStochCalc.Ito.Picard.SBoundedProcess.AEQuot`, and nonemptiness of both.
-/
