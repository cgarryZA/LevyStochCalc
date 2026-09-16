/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands
import LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits

/-!
# Steps of the Itô–Lévy formula at bounded derivatives

The admissibility, transport and limit steps for the small-jump truncation of the Itô–Lévy
formula along a jump diffusion, assembled from its two parts.

## Parts

* `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsIntegrands` — joint and progressive measurability
  and the window energy of the mixed integrands, the transport of the two stochastic integrals
  to the right-continuous regularisation of the filtration of the SDE data, and the
  componentwise measurability of the endpoint terms.
* `LevyStochCalc.Ito.ItoLevyBoundedDerivsStepsLimits` — the convergence of the four term
  families along a family of paths converging to the solution, and the dominated convergence
  lemma for a mark integral over a shrinking family of cuts that it rests on.
-/
