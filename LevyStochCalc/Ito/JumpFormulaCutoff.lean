/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaCutoffIntegrands
import LevyStochCalc.Ito.JumpFormulaCutoffLocalise

/-!
# Cutting a function of time and space off outside a box

Multiplying a function of time and space by the product of a one-dimensional smooth cutoff in
time with a box cutoff in space leaves it, together with its time derivative and its first two
space derivatives, unchanged on a box around the origin, and gives it compact support. Along a
path that stays in a ball over a bounded window the two functions therefore give the same
Itô–Lévy integrands, except at the shifted state `x + γ(s, x, e)` reached by a jump, which needs
its own bound. A càdlàg path is bounded on a compact interval, so the events on which a path
stays in a ball over the window exhaust the sample space; the same exhaustion carries the
increment formula for a translated path from functions with globally bounded derivatives to
functions with none, with no bound on the translation.

## Parts

* `LevyStochCalc.Ito.JumpFormulaCutoffIntegrands` — the time–space cutoff, the derivatives and
  Itô–Lévy integrands it leaves unchanged inside the window, and the exhausting families.
* `LevyStochCalc.Ito.JumpFormulaCutoffLocalise` — the increment formula for a translated path
  with no bound on the derivatives and none on the translation.

## Main definitions

* `LevyStochCalc.Ito.JumpFormulaCutoff.timeBoxCut` — the time–space cutoff.
* `LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂` — a function of time and space multiplied by
  it.
* `LevyStochCalc.Ito.JumpFormulaCutoff.boundedJumpSet` — the sample points whose jump coefficient
  along the path is bounded over the window, uniformly in the mark.

## Main statements

* `LevyStochCalc.Ito.JumpFormulaCutoff.ae_exists_bound_norm` — almost every path of a jump
  diffusion is bounded over a bounded window.
* `LevyStochCalc.Ito.JumpFormulaCutoff.integrands_cutoffFun₂_eq_of_mem` — on the members of the
  two exhausting families the cutoff carries the same drift, diffusion, compensator-drift and
  jump integrands as the function itself.
* `LevyStochCalc.Ito.JumpFormulaCutoff.itoFormula_between_shift_localise` — Itô's formula for the
  increment of a translated path between two ordered stopping times, for a twice continuously
  differentiable function, with no bound on the derivatives and none on the translation.
* `LevyStochCalc.Ito.JumpFormulaCutoff.stochasticIntegralBrownian_stopped_sub_congr_of_mem` — the
  matching of the stochastic terms that theorem takes as input, from a stopping time below which
  the two integrands agree.
-/
