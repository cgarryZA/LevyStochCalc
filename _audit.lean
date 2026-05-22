/-
Master audit script. Imports every active LevyStochCalc module, then prints
axiom sets for every load-bearing theorem.

Run via:  lake env lean _audit.lean 2>&1 | tee audit_output.txt

Generates ground-truth axiom info that bypasses the LSP cache. Used by
`tools/lint.sh` and the project's sorry-baseline tracking.

Mirrors `D:/Dissertation/_audit.lean`.
-/

import LevyStochCalc

-- ===== Layer 0: Compensated Poisson =====
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite
#print axioms LevyStochCalc.Poisson.poissonRandomMeasure_finite_exists
#print axioms LevyStochCalc.Poisson.Compensated.itoLevyIsometry
#print axioms LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.cadlag_modification_exists

-- ===== Layer 1: Itô-Lévy isometry (→ deaxiomatises I02) =====
#print axioms LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry

-- ===== Layer 1.5: Brownian motion sub-tree =====
-- 1.5a: construction
#print axioms LevyStochCalc.Brownian.BrownianMotion.exists
-- 1.5b: Kolmogorov-Chentsov continuous modification
#print axioms LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification
#print axioms LevyStochCalc.Brownian.Continuity.brownian_continuous_modification
#print axioms LevyStochCalc.Brownian.Continuity.kolmogorov_modification_ae_eq
-- 1.5c: martingale property + quadratic variation
#print axioms LevyStochCalc.Brownian.Martingale.brownian_martingale
#print axioms LevyStochCalc.Brownian.Martingale.brownian_quadVar
#print axioms LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous
-- 1.5d: multi-dimensional Brownian motion
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists
-- 1.5e: L² Itô integral against W
#print axioms LevyStochCalc.Brownian.Ito.itoIsometry
#print axioms LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral
#print axioms LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral

-- ===== Layer 2: Itô-Lévy formula (→ deaxiomatises Cu03) =====
#print axioms LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique
#print axioms LevyStochCalc.Ito.JumpFormula.itoLevyFormula

-- ===== Layer 3 (+ 3a): BSDEJ existence (→ deaxiomatises Cu01) =====
#print axioms LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation
#print axioms LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique

-- ===== Layer 4: BSDEJ path regularity (→ deaxiomatises Cu05) =====
#print axioms LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity
