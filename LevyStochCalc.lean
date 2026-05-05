-- Substrate
import LevyStochCalc.Basic
import LevyStochCalc.Notation

-- Layer 0: Compensated Poisson
import LevyStochCalc.Poisson.RandomMeasure
import LevyStochCalc.Poisson.NaturalFiltration
import LevyStochCalc.Poisson.Compensated

-- Layer 1: Itô-Lévy isometry  → I02
import LevyStochCalc.Poisson.L2Isometry

-- Layer 1.5: Brownian motion (in-project, no external dep)
import LevyStochCalc.Brownian.Construction
import LevyStochCalc.Brownian.Continuity
import LevyStochCalc.Brownian.Martingale
import LevyStochCalc.Brownian.Multidim
import LevyStochCalc.Brownian.Ito

-- Layer 2: Itô-Lévy formula  → Cu03
import LevyStochCalc.Ito.Setting
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
* `Cu05` — BSDEJ path regularity (Bouchard-Elie-Touzi 2009 Thm 2.1)

Each layer below targets one axiom (or builds machinery used by the next layer).
Modules are stubs (`sorry`) at bootstrap; they fill in incrementally per the
dependency DAG documented in the plan.
-/
