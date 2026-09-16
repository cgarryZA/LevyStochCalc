/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaSimpleShiftCells
import LevyStochCalc.Ito.ItoFormulaSimpleShiftIntegral

/-!
# Itô's formula for an increment translated by a simple random vector

A random vector taking finitely many values and known at a stopping time `σ` that itself takes
finitely many values below a horizon decomposes the sample space into the finitely many cells on
which both the value of `σ` and the value of the vector are constant. On such a cell the
translation is by a fixed vector, so Itô's formula for the increment between `σ` and a later
stopping time applies with a constant shift, and the cell indicator — bounded and known at the
deterministic time carried by the cell — passes inside the Itô integral of the increment.

## Parts

* `LevyStochCalc.Ito.ItoFormulaSimpleShiftCells` — the cell decomposition attached to a stopping
  time and a simple random mark, and the progressive measurability of the cell integrands.
* `LevyStochCalc.Ito.ItoFormulaSimpleShiftIntegral` — the splitting of the Itô integral over the
  cells and Itô's formula for a function translated by a simple random vector.
-/
