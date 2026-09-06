/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry

Master audit script. Imports every active LevyStochCalc module, then prints
axiom sets for every load-bearing theorem.

Run via:  lake env lean _audit.lean 2>&1 | tee audit_output.txt

Generates ground-truth axiom info that bypasses the LSP cache. Used by
`tools/lint.sh` and the project's sorry-baseline tracking.

Mirrors `D:/Dissertation/_audit.lean`.
-/

import LevyStochCalc

-- ===== Layer -1: drivers with respect to a filtration (X2-0, 2026-09-06) =====
#print axioms LevyStochCalc.Probability.indep_comap_of_tendsto_ae
#print axioms LevyStochCalc.Probability.indep_sup_left_of_indep
#print axioms LevyStochCalc.Brownian.isBrownianFiltration_natural
#print axioms LevyStochCalc.Brownian.IsBrownianFiltration.rightCont
#print axioms LevyStochCalc.Poisson.isPoissonFiltration_natural
#print axioms LevyStochCalc.Poisson.IsPoissonFiltration.rightCont
#print axioms LevyStochCalc.Driver.LevyDriver.isBrownianFiltration
#print axioms LevyStochCalc.Driver.LevyDriver.isPoissonFiltration
-- X2-4 (2026-09-06): a Lévy driver exists, so the common-filtration hypothesis carried by
-- `JumpDiffusion.is_solution`, #16, the Picard iteration and `IsBSDEJSolution` is satisfiable.
#print axioms LevyStochCalc.Probability.indep_comap_of_measurePreserving
#print axioms LevyStochCalc.Probability.iIndepFun_comp_of_measurePreserving
#print axioms LevyStochCalc.Brownian.BrownianMotion.comap
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.comap
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.comap
#print axioms LevyStochCalc.Driver.LevyDriver.exists
#print axioms LevyStochCalc.Driver.exists_isBrownianFiltration_and_isPoissonFiltration
-- A1b-ii (2026-09-06): augmentation by the null sets commutes with a countable antitone
-- infimum of sub-σ-algebras — the gate of the downward `L²` convergence that #13b needs.
#print axioms LevyStochCalc.Probability.aug_eq_sup_nullSigma
#print axioms LevyStochCalc.Probability.measurableSet_aug_of_ae_eq
#print axioms LevyStochCalc.Probability.aug_iInf_of_antitone
-- A1a (2026-09-06): the Hilbert-space half — projections along a decreasing sequence of closed
-- subspaces converge to the projection onto the intersection.
#print axioms LevyStochCalc.Probability.starProjection_starProjection_of_le
#print axioms LevyStochCalc.Probability.norm_sq_starProjection_of_le
#print axioms LevyStochCalc.Probability.tendsto_starProjection_of_antitone
#print axioms LevyStochCalc.Probability.aestronglyMeasurable_iInf_of_antitone
#print axioms LevyStochCalc.Probability.lpMeas_iInf_of_antitone
#print axioms LevyStochCalc.Probability.tendsto_condExpL2_of_antitone
-- A1c (2026-09-06): right continuity in `L²` of the conditional expectation along a
-- right-continuous filtration on `ℝ`.
#print axioms LevyStochCalc.Probability.norm_starProjection_sub_le_of_le
#print axioms LevyStochCalc.Probability.iInf_filtration_add_one_div
#print axioms LevyStochCalc.Probability.iInf_filtration_add_one_div_of_isRightContinuous
#print axioms LevyStochCalc.Probability.tendsto_condExpL2_nhdsGT
-- A2c (2026-09-06): the σ-algebra of a tuple, and the grid induction that upgrades pairwise
-- independence of increments to joint independence.
#print axioms LevyStochCalc.Probability.comap_pi_eq_iSup
#print axioms LevyStochCalc.Probability.comap_prod_eq_sup
#print axioms LevyStochCalc.Probability.indep_iSup_lt_of_indep
#print axioms LevyStochCalc.Probability.indep_iSup_of_finset
-- A2e-i (2026-09-06): the whole Brownian increment vector of a Lévy driver against the joint
-- filtration and its right-continuous version.
#print axioms LevyStochCalc.Driver.LevyDriver.indep_restSigma
#print axioms LevyStochCalc.Driver.LevyDriver.indep_incrementSigma_rest
#print axioms LevyStochCalc.Driver.LevyDriver.indep_iSup_incrementSigma
#print axioms LevyStochCalc.Driver.LevyDriver.indep_iSup_incrementSigma_rightCont
-- A2e-ii, A2e-iii (2026-09-06): the Poisson counts of a finite family of regions, and the mixed
-- Brownian/Poisson increment tuple over one interval.
#print axioms LevyStochCalc.Poisson.indep_iSup_comap_of_disjoint_families
#print axioms LevyStochCalc.Poisson.indep_of_disjoint_region_families
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.indep_of_disjoint_region_pair
#print axioms LevyStochCalc.Driver.LevyDriver.indep_iSup_regionSigma
#print axioms LevyStochCalc.Driver.LevyDriver.indep_stepSigma
#print axioms LevyStochCalc.Driver.LevyDriver.indep_stepSigma_rightCont
-- A2f (2026-09-06): the grid induction — successive increment tuples, and tuples measured from
-- the start of the grid, against the right-continuous filtration at its left endpoint.
#print axioms LevyStochCalc.Probability.comap_add_le
#print axioms LevyStochCalc.Driver.LevyDriver.indep_iSup_stepSigma
#print axioms LevyStochCalc.Driver.LevyDriver.indep_iSup_stepSigma_start
-- A2g-ii support (2026-09-06): trivial σ-algebras, and regions of zero intensity.
#print axioms LevyStochCalc.Probability.IsTrivialSigma.indep
#print axioms LevyStochCalc.Probability.isTrivialSigma_comap_of_ae_const
#print axioms LevyStochCalc.Probability.IsTrivialSigma.indep_sup
#print axioms LevyStochCalc.Poisson.ae_count_eq_zero_of_intensity_eq_zero
#print axioms LevyStochCalc.Poisson.ae_count_Iic_zero_eq_zero
-- A2g-i (2026-09-06): the driver's data at finitely many positive times against `ℱ₊ 0`.
#print axioms LevyStochCalc.Driver.LevyDriver.indep_iSup_valueSigma
-- A2g-ii, A2d (2026-09-06): Blumenthal's 0-1 law for the driver's joint filtration, and the
-- conditional expectation on the germ field.
#print axioms LevyStochCalc.Probability.trivialSigma
#print axioms LevyStochCalc.Driver.LevyDriver.indep_valueTuple
#print axioms LevyStochCalc.Driver.LevyDriver.indep_rightCont_zero_filtration
#print axioms LevyStochCalc.Driver.LevyDriver.isTrivialSigma_rightCont_zero
#print axioms LevyStochCalc.Driver.LevyDriver.indep_rightCont_zero_sigma
#print axioms LevyStochCalc.Driver.LevyDriver.condExp_rightCont_zero
#print axioms LevyStochCalc.Driver.LevyDriver.condExp_rightCont_nonpos
-- A3g, A3d (2026-09-06): the càdlàg conditional-expectation martingale indexed by `ℝ`, and
-- cited result #13b as a theorem.
#print axioms LevyStochCalc.Driver.LevyDriver.martingale_cadlagCondExp
#print axioms LevyStochCalc.Driver.LevyDriver.tendsto_cadlagCondExp_nhdsGT
#print axioms LevyStochCalc.Driver.LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT
#print axioms LevyStochCalc.Driver.LevyDriver.cadlagCondExp_zero_ae_eq
#print axioms LevyStochCalc.Driver.LevyDriver.cadlagCondExp_terminal_ae_eq
-- A3e (2026-09-06): a martingale is a real quasimartingale, the hypothesis every clean lemma
-- of the upstream càdlàg-modification API takes.
#print axioms LevyStochCalc.Probability.integral_indicator_martingale_eq_zero
#print axioms LevyStochCalc.Probability.isRealQuasimartingale_of_martingale
-- A3f, A3b, A3c (2026-09-06): the `ℝ≥0` reindexing, convergence in measure from the right, and
-- the right-continuous modification of the conditional-expectation martingale.
#print axioms LevyStochCalc.Probability.restrictNNReal.instIsRightContinuous
#print axioms LevyStochCalc.Probability.tendstoInMeasure_condExp_nhdsGT
#print axioms LevyStochCalc.Probability.condExpModif_ae_eq
#print axioms LevyStochCalc.Probability.martingale_condExpModif
#print axioms LevyStochCalc.Probability.continuousWithinAt_condExpModif
#print axioms LevyStochCalc.Probability.ae_exists_tendsto_condExpModif_nhdsLT
-- X2-1 (2026-09-06): progressive measurability, Brownian filtrations, the joint natural
-- filtration of a multidimensional Brownian motion.
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.isStronglyProgressive
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.of_isStronglyProgressive
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.stronglyMeasurable_setIntegral
#print axioms LevyStochCalc.Brownian.IsBrownianFiltration.condExp_eq
#print axioms LevyStochCalc.Brownian.IsBrownianFiltration.of_le_sup
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isBrownianFiltration_natural
-- X2-2 (2026-09-06): marked progressive measurability for the compensated-Poisson chain.
#print axioms LevyStochCalc.Probability.MarkedProgressivelyMeasurable.indicator_mark
#print axioms
  LevyStochCalc.Probability.MarkedProgressivelyMeasurable.stronglyMeasurable_setIntegral_prod
#print axioms
  LevyStochCalc.Probability.MarkedProgressivelyMeasurable.stronglyMeasurable_setIntegral_integral
-- ===== Layer 0: Compensated Poisson =====
-- Poisson splitting (toward #2): counts of a Poisson number of iid marks on
-- disjoint sets are independent Poisson variables.
#print axioms LevyStochCalc.Poisson.map_markCount_eq_pi
#print axioms LevyStochCalc.Poisson.hasLaw_markCount_real
#print axioms LevyStochCalc.Poisson.map_markCount_ennreal
#print axioms LevyStochCalc.Poisson.iIndepFun_markCount_ennreal
-- Superposition of independent Poisson pieces (the Poisson recipe behind #2).
#print axioms LevyStochCalc.Probability.iIndepFun_fiber
#print axioms LevyStochCalc.Poisson.map_superposition
#print axioms LevyStochCalc.Poisson.ae_exists_nat_superposition
#print axioms LevyStochCalc.Poisson.ae_eq_top_superposition
#print axioms LevyStochCalc.Poisson.iIndepFun_superposition
#print axioms LevyStochCalc.Poisson.lintegral_superposition
#print axioms LevyStochCalc.Poisson.indep_of_disjoint_region_of_indep
-- Cited result #2 (Applebaum 2.3.1 / Kallenberg 3.6): a theorem since 2026-09-06.
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.exists_of_sigmaFinite
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.indep_iSup_comap_of_disjoint
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.indep_of_disjoint_region
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.toMathFin
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.itoLevyIntegralL2_norm
#print axioms LevyStochCalc.Poisson.poissonRandomMeasure_finite_exists
#print axioms LevyStochCalc.Poisson.Compensated.itoLevyIsometry
#print axioms LevyStochCalc.Poisson.Compensated.quadVar_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.cadlag_modification_exists
#print axioms LevyStochCalc.Poisson.Compensated.exists_cadlag_modification
#print axioms LevyStochCalc.Poisson.Compensated.martingale_stochasticIntegral_rightCont
#print axioms LevyStochCalc.Poisson.Compensated.martingale_quadVar_stochasticIntegral_rightCont
#print axioms LevyStochCalc.Poisson.Compensated.isometry_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_cadlag
#print axioms LevyStochCalc.Poisson.Compensated.itoIsometry_compensated_unified_existence
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_dyadicRefine
#print axioms LevyStochCalc.Poisson.Compensated.process_sub_lintegral_sq
#print axioms LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated

-- ===== Layer 0.25: mark-step integrands (toward #6) =====
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.martingale_integral
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_sq_at
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.lintegral_integral_sq_at
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.lintegral_integral_sub_sq_at
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_increment_sq
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.full_dyadicRefine
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.full_dyadicRestrict
#print axioms LevyStochCalc.Poisson.Compensated.exists_markStep_close
#print axioms LevyStochCalc.Poisson.Compensated.master_err
#print axioms LevyStochCalc.Poisson.Compensated.master_adapted
#print axioms LevyStochCalc.Poisson.Compensated.stageIntegral_sub_sq_le
#print axioms LevyStochCalc.Poisson.Compensated.martingale_process
#print axioms LevyStochCalc.Poisson.Compensated.martingale_rightCont_process
#print axioms LevyStochCalc.Poisson.Compensated.process_lintegral_sq'
#print axioms LevyStochCalc.Poisson.Compensated.process_eLpNorm_two_right_tendsto
#print axioms LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_zero_sq
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_weight_incr_sq
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.setIntegral_increment_sq_eq
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.martingale_sq_sub_compensator
#print axioms LevyStochCalc.Poisson.Compensated.compensator_stronglyAdapted
#print axioms LevyStochCalc.Poisson.Compensated.stage_compensator_tendsto_L1
#print axioms LevyStochCalc.Poisson.Compensated.martingale_quadVar_process
#print axioms LevyStochCalc.Poisson.Compensated.martingale_rightCont_quadVar_process

-- ===== Layer 0.5: martingale path regularity =====
#print axioms LevyStochCalc.Martingale.isRealQuasimartingale
#print axioms LevyStochCalc.Martingale.exists_adapted_ae_isCadlag_nnreal
#print axioms LevyStochCalc.Martingale.exists_adapted_ae_cadlag
#print axioms LevyStochCalc.Martingale.exists_adapted_ae_cadlag_of_eLpNorm
#print axioms LevyStochCalc.Martingale.martingale_sq_sub_of_setIntegral

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
#print axioms LevyStochCalc.Brownian.Martingale.brownian_martingale_natural
#print axioms LevyStochCalc.Brownian.Martingale.brownian_martingale_rightCont
#print axioms LevyStochCalc.Brownian.Martingale.brownian_filtration_rightContinuous
#print axioms LevyStochCalc.Martingale.martingale_rightCont_of_tendsto_eLpNorm_one
-- 1.5d: multi-dimensional Brownian motion
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists
#print axioms
  LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.joint_increment_gaussian_diagonal
-- 1.5e: L² Itô integral against W
#print axioms LevyStochCalc.Brownian.Ito.itoIsometry
#print axioms LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral
#print axioms LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral
-- B1a-1 (2026-09-06): the algebra of the `L²` Brownian integral — a simple integrand inside
-- the integral, and associativity against a simple integrand.
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.progressivelyMeasurable_eval
#print axioms LevyStochCalc.Brownian.Ito.simpleIntegral_diff_isometry_of_adapted
#print axioms LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_eval_simple
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.eval_mul_on_common
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.sum_xi_mul_simpleIntegral_sub
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.exists_mul_simple
#print axioms LevyStochCalc.Brownian.Ito.isometry_simple_sub_stochasticIntegralBrownian
#print axioms LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_integralAgainst
#print axioms LevyStochCalc.Brownian.Ito.stepIoc_eval
#print axioms LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indicator_Ioc
-- B1a-2a (2026-09-06): moments of a Brownian increment, toward the fourth-moment bound.
#print axioms LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_zero
#print axioms LevyStochCalc.Brownian.Ito.integral_pow_gaussianReal_odd
#print axioms LevyStochCalc.Brownian.Ito.integral_increment_sq
#print axioms LevyStochCalc.Brownian.Ito.integral_increment_pow_four
#print axioms LevyStochCalc.Brownian.Ito.integral_mul_increment_pow
#print axioms LevyStochCalc.Brownian.Ito.memLp_mul_increment

-- ===== Layer 2: Itô-Lévy formula (→ deaxiomatises Cu03) =====
#print axioms LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique
-- Picard framework lemmas (active construction toward JumpDiffusion proof):
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_diff
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_diff_vec
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_diff_componentwise_norm_bound
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_diff_lipschitz_componentwise
#print axioms LevyStochCalc.Ito.Picard.integral_sq_le_mul_integral_sq_on_Icc
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_diff_lipschitz_sq_componentwise
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_diff_sum_sq_bound
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_diff_lintegral_sq_bound
#print axioms LevyStochCalc.Ito.Picard.integral_exp_two_beta_Icc
#print axioms LevyStochCalc.Ito.Picard.bielecki_weight_bound
#print axioms LevyStochCalc.Ito.Picard.bielecki_weighted_integral_bound
#print axioms LevyStochCalc.Ito.Picard.bielecki_drift_contraction_factor
#print axioms LevyStochCalc.Ito.Picard.bielecki_contraction_rate_lt_one
#print axioms LevyStochCalc.Ito.Picard.sigma_along_X_measurable
#print axioms LevyStochCalc.Ito.Picard.gamma_along_X_measurable
-- Banach fixed-point shim (Mathlib `ContractingWith.fixedPoint` wrapper):
#print axioms LevyStochCalc.Ito.Picard.picardFixedPoint_generic
#print axioms LevyStochCalc.Ito.Picard.picardFixedPoint
#print axioms LevyStochCalc.Ito.Picard.picardFixedPoint_of_exists
-- Ex-Tier-1-axiom #14 chain (axiom→theorem 2026-05-26; wrap-up carries the
-- single explicit baseline `sorry` for the entire Picard chain):
#print axioms LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot
#print axioms LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique_axiom
#print axioms LevyStochCalc.Ito.Picard.picardFixedPoint_jumpDiffusion_exists_unique
-- σ-side L² Lipschitz bound (Ito/Picard.lean; depends on
-- Tier 1 axiom itoIsometry_diff_brownian for stochastic-integral linearity):
#print axioms LevyStochCalc.Ito.Picard.picardStep_diffusion_diff_lipschitz_sq_componentwise
#print axioms LevyStochCalc.Brownian.Ito.itoIsometry_diff_brownian
-- γ-side L² Lipschitz bound (Ito/Picard.lean; depends on
-- Tier 1 axiom itoIsometry_diff_compensated for compensated-Poisson
-- stochastic-integral linearity):
#print axioms LevyStochCalc.Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise
#print axioms LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated
-- Bielecki β-norm contraction assembly (Ito/Picard.lean):
#print axioms LevyStochCalc.Ito.Picard.sq_add_three_le
#print axioms LevyStochCalc.Ito.Picard.sum_sq_add_three_le
#print axioms LevyStochCalc.Ito.Picard.picardStep_diff_sum_sq_le
#print axioms LevyStochCalc.Ito.Picard.picardStep_diff_lintegral_sum_sq_le
#print axioms LevyStochCalc.Ito.Picard.picardStep_bielecki_contraction
#print axioms LevyStochCalc.Ito.Picard.picardStep_bielecki_contraction_rate_lt_one
-- Itô-Lévy formula axioms + derived theorems:
-- 2026-05-26: Tier 1 #16 narrowed to the canonical-`R` form
-- (`itoLevyFormula_jumpResidual_canonical_axiom`); the previous
-- universal-`R` form (`itoLevyFormula_jumpResidual_axiom`) is now a
-- derived THEOREM forwarding over the narrower axiom by per-ω algebra.
#print axioms LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_canonical_axiom
#print axioms LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_axiom
#print axioms LevyStochCalc.Ito.JumpFormula.itoLevyFormula

-- ===== Layer 3 (+ 3a): BSDEJ =====
-- 2026-09-06: the cited results #9 (`continuousBSDEJ_exists_unique`), #10
-- (`bsdej_path_regularity`) and #13a (`jacodYor_PRP_martingale_axiom`) were retired as
-- refutable statements (see `tools/cited_axioms.md`); only #13b remains.
#print axioms LevyStochCalc.BSDEJ.MartingaleRepresentation.condExp_to_PRP_martingale_form
#print axioms LevyStochCalc.BSDEJ.Definition.IsBSDEJSolution
#print axioms LevyStochCalc.BSDEJ.Existence.picardMap
#print axioms LevyStochCalc.BSDEJ.PathRegularity.conditionalTimeAverage_Z

