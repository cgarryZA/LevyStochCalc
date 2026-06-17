/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

-- Substrate
import LevyStochCalc.Basic
-- LevyStochCalc.Notation was a 21-line empty placeholder (no content, only
-- a copyright header + namespace declaration); deleted per red-team P1 F1
-- 2nd audit 2026-05-23. If notation needs to be reserved across the project
-- in the future, recreate the file with the specific notation declarations.

-- Layer 0: Compensated Poisson
import LevyStochCalc.Poisson.RandomMeasure
import LevyStochCalc.Poisson.NaturalFiltration
import LevyStochCalc.Poisson.CompensatedSimple
import LevyStochCalc.Poisson.CompensatedIsometry
import LevyStochCalc.Poisson.CompensatedMartingale
import LevyStochCalc.Poisson.CompensatedDensity
import LevyStochCalc.Poisson.Compensated

-- Layer 1: Itô-Lévy isometry  → I02
import LevyStochCalc.Poisson.L2Isometry

-- Layer 1.5: Brownian motion (in-project, no external dep)
import LevyStochCalc.Brownian.Construction
import LevyStochCalc.Brownian.Continuity
import LevyStochCalc.Brownian.Martingale
import LevyStochCalc.Brownian.Multidim
import LevyStochCalc.Brownian.ItoSimple
import LevyStochCalc.Brownian.ItoDensity
import LevyStochCalc.Brownian.ItoMartingale
import LevyStochCalc.Brownian.SimplePredictableRefine
import LevyStochCalc.Brownian.ItoL2Completion
import LevyStochCalc.Brownian.MultidimIto

-- Layer 2: Itô-Lévy formula  → Cu03
import LevyStochCalc.Ito.Setting
import LevyStochCalc.Ito.Picard
import LevyStochCalc.Ito.PicardSpace
import LevyStochCalc.Ito.PicardFixedPoint
import LevyStochCalc.Ito.JumpFormula

-- Layer 3 (+ 3a): BSDEJ existence  → Cu01
import LevyStochCalc.BSDEJ.Definition
import LevyStochCalc.BSDEJ.MartingaleRepresentation
import LevyStochCalc.BSDEJ.Existence

-- Layer 4: BSDEJ path regularity  → Cu05
import LevyStochCalc.BSDEJ.PathRegularity

/-!
# LevyStochCalc — root aggregator

Bottom-up continuous-time Lévy / jump stochastic calculus formalisation, written
to discharge the four cited continuous-time axioms of the main dissertation
(`D:/Dissertation/Dissertation/Continuous.lean`):

* `I02`  — Itô-Lévy L² isometry (Applebaum 2009 Thm 4.2.3)
* `Cu01` — Continuous BSDEJ existence/uniqueness (Tang-Li 1994)
* `Cu03` — Itô-Lévy formula for jump diffusions (Applebaum 2009 Thm 4.4.7)
* `Cu05` — BSDEJ path regularity (Bouchard-Elie 2008 SPA 118(1) pp 53-75 Thm 2.1;
  correcting the previous fabricated "Bouchard-Elie-Touzi 2009 SPA 119(11)"
  citation flagged by red-team 1st audit P11 + 2nd audit P10)

Each layer below targets one axiom (or builds machinery used by the next layer).
Modules are stubs (`sorry`) at bootstrap; they fill in incrementally per the
dependency DAG documented in the plan.
-/
