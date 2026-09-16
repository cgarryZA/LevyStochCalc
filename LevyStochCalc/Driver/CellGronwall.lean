/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CellGronwallPairing
import LevyStochCalc.Driver.CellGronwallIdentity

/-!
# The pairing of a weight with the cell character

The mixed cell lemma runs a Grönwall argument on the pairing of a square-integrable weight and a
bounded factor with the product of the Brownian cell character `e^{i l X_s}` and the Poisson cell
character. That complex pairing is the combination of four real pairings, one for each of the
cosine and sine against the real and imaginary parts of the Poisson character.

This module collects the development, which is spread over the following parts.

* `LevyStochCalc.Driver.CellGronwallPairing` — the real pairings and the complex halves, their
  integrability and bounds, and the cell identity for a real pairing in reduced form.
* `LevyStochCalc.Driver.CellGronwallIdentity` — the cell identity for a half and for the complex
  pairing, the Grönwall bound, and the vanishing of the pairing on the cell.
-/
