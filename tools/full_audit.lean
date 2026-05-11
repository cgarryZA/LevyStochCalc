/-
Full project axiom audit. Imports every active LevyStochCalc module, then prints
axiom sets for every public theorem + cited axiom.

Run via:  lake env lean tools/full_audit.lean 2>&1 | tee tools/full_audit_output.txt

Every theorem listed should have axiom set ⊆ {propext, Classical.choice, Quot.sound}
∪ {the 10 Tier 1 cited axioms documented in tools/cited_axioms.md}.

No `sorryAx` should appear anywhere.

The 10 Tier 1 cited axioms:
1.  LevyStochCalc.Brownian.BrownianMotion.exists
2.  LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite
3.  LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification
4.  LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont
5.  LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence
6.  LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence
7.  LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated
8.  LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated
9.  LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique
10. LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity
-/

import LevyStochCalc

-- ===== Tier 1 cited axioms (verify they show themselves in their own axiom set) =====
#print axioms LevyStochCalc.Brownian.BrownianMotion.exists
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite
#print axioms LevyStochCalc.Brownian.Continuity.kolmogorovChentsov_modification
#print axioms LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont
#print axioms LevyStochCalc.Brownian.Ito.itoIsometry_brownian_unified_existence
#print axioms LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence
#print axioms LevyStochCalc.Poisson.Compensated.cauchySeq_simpleIntegralLp_compensated
#print axioms LevyStochCalc.Poisson.Compensated.adaptedSimple_dense_L2_compensated
#print axioms LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique
#print axioms LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity

-- ===== Honest derivative theorems (axiom set should be std + Tier 1) =====

-- Layer 1.5a/d: Brownian construction + multidim
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists

-- Layer 1.5b: Continuity / modification
#print axioms LevyStochCalc.Brownian.Continuity.brownian_continuous_modification

-- Layer 1.5c: Martingale + quadVar (Brownian motion itself, already axiom-clean — Lean std only)
#print axioms LevyStochCalc.Brownian.Martingale.brownian_martingale
#print axioms LevyStochCalc.Brownian.Martingale.brownian_quadVar
#print axioms LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous

-- Layer 1.5e: L² Itô integral against W
#print axioms LevyStochCalc.Brownian.Ito.itoIsometry
#print axioms LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
#print axioms LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral

-- Layer 0: Compensated Poisson L²-Itô-Lévy
#print axioms LevyStochCalc.Poisson.Compensated.itoLevyIsometry
#print axioms LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.cadlag_modification_exists

-- Layer 1: I02 forwarder
#print axioms LevyStochCalc.Poisson.L2Isometry.itoLevyIsometry

-- Layer 2: Itô-Lévy formula
#print axioms LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique
#print axioms LevyStochCalc.Ito.JumpFormula.itoLevyFormula

-- Layer 3: BSDEJ
#print axioms LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation
