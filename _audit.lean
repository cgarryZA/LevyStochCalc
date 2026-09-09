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
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.partialSum_card
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_sq_le
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.integral_simpleIntegral_pow_four_le_horizon
#print axioms LevyStochCalc.Brownian.Ito.abs_clamp_sub_le
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.truncate_eval
#print axioms LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le
-- B1a-2b/2c (2026-09-06): the per-tile variance budget and the increment bound.
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_mono
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_sq_le_varClock
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.integral_partialSum_pow_four_le_varClock
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.integral_simpleIntegral_pow_four_le_varClock
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.eval_of_mem_Ioc
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.abs_eval_le
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.varClock_le_Ioc
#print axioms LevyStochCalc.Brownian.Ito.stepIocGen_eval
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.simpleIntegral_eq_of_support
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_of_time
#print axioms LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_pow_four_le_Ioc
#print axioms LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_pow_four_le
-- B1a-2d (2026-09-06): orthogonality of martingale differences.
#print axioms LevyStochCalc.Probability.integral_sum_mul_of_condExp_eq_zero
#print axioms LevyStochCalc.Probability.integral_sq_sum_of_condExp_eq_zero
#print axioms LevyStochCalc.Brownian.Ito.condExp_quadVarIncrement
#print axioms LevyStochCalc.Brownian.Ito.compensator_sub_bounds
#print axioms LevyStochCalc.Brownian.Ito.memLp_two_quadVarIncrement
#print axioms LevyStochCalc.Brownian.Ito.integral_sq_quadVarIncrement_le
#print axioms LevyStochCalc.Brownian.Ito.stronglyMeasurable_quadVarIncrement
#print axioms LevyStochCalc.Brownian.Ito.integral_sq_weighted_quadVarSum_le
-- B1a-2f (2026-09-06): continuous modification of the Ito integral by Kolmogorov-Chentsov.
#print axioms LevyStochCalc.Brownian.Ito.exists_continuous_modification_stochasticIntegralBrownian
-- B1a-2e (2026-09-06): the deterministic Riemann-sum error bound.
#print axioms LevyStochCalc.abs_riemann_weighted_sub_integral_le
-- B1a-3b (2026-09-06): second and third moments of an increment.
#print axioms LevyStochCalc.Brownian.Ito.lintegral_stochasticIntegralBrownian_sub_sq_le
#print axioms LevyStochCalc.Brownian.Ito.integral_sub_sq_le
#print axioms LevyStochCalc.Brownian.Ito.integral_sub_pow_four_le
#print axioms LevyStochCalc.Brownian.Ito.integral_abs_sub_pow_three_le
-- B1a-3a (2026-09-06): Riemann sums of the Ito integral against a step weight.
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.integralAgainst_eq_sum
#print axioms LevyStochCalc.Brownian.Ito.sum_xi_mul_stochasticIntegral_sub_ae
#print axioms LevyStochCalc.Brownian.Ito.lintegral_sq_stochasticIntegral_mul_sub_le
-- B1a-3c (2026-09-06): the second-order Taylor remainder bound.
#print axioms LevyStochCalc.abs_sub_taylor_one_le
#print axioms LevyStochCalc.abs_sub_taylor_two_le
#print axioms LevyStochCalc.abs_sub_sum_taylor_two_le
-- B1a-3d (2026-09-06): the uniform grid and the third-moment remainder sum.
#print axioms LevyStochCalc.Brownian.Ito.unifGrid_succ_sub
#print axioms LevyStochCalc.Brownian.Ito.sum_integral_abs_sub_pow_three_le
#print axioms LevyStochCalc.Brownian.Ito.SimplePredictable.ofUnifGrid_eval
#print axioms LevyStochCalc.Brownian.Ito.sum_unifGrid_mul_sub_ae
#print axioms LevyStochCalc.Brownian.Ito.lintegral_sq_sum_unifGrid_sub_le
-- B1a-3d (2026-09-06): drift-side increments of an Ito process.
#print axioms LevyStochCalc.setIntegral_Icc_sub_Icc
#print axioms LevyStochCalc.abs_setIntegral_Ioc_le
#print axioms LevyStochCalc.measurable_setIntegral_Ioc
#print axioms LevyStochCalc.Brownian.Ito.integral_abs_add_pow_three_le
#print axioms LevyStochCalc.Brownian.Ito.sum_integral_abs_itoIncrement_pow_three_le
#print axioms LevyStochCalc.Brownian.Ito.tendsto_riemann_weighted_unifGrid
#print axioms LevyStochCalc.Brownian.Ito.exists_unifGrid_cell
#print axioms LevyStochCalc.Brownian.Ito.abs_ofUnifGrid_eval_sub_le
#print axioms LevyStochCalc.Brownian.Ito.lintegral_sq_sub_le_of_bound
-- B1a-3e (2026-09-07): the Ito process and its L^1 Taylor remainder.
#print axioms LevyStochCalc.measurable_setIntegral
#print axioms LevyStochCalc.abs_taylorRemainder_le
#print axioms LevyStochCalc.Brownian.Ito.integrable_abs_drift_pow_three
#print axioms LevyStochCalc.Brownian.Ito.integrable_abs_itoIncrement_pow_three
#print axioms LevyStochCalc.integral_abs_le_sqrt_of_integral_sq_le
#print axioms LevyStochCalc.Brownian.Ito.integral_sq_itoProcess_sub_le
#print axioms LevyStochCalc.Brownian.Ito.integral_abs_itoProcess_sub_le
#print axioms LevyStochCalc.Brownian.Ito.measurable_itoProcess
#print axioms LevyStochCalc.Brownian.Ito.itoProcess_sub
#print axioms LevyStochCalc.Brownian.Ito.integral_abs_taylorRemainder_le
-- B1a-3g (2026-09-07): continuous versions and their window moments.
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.measurable_uncurry
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.progressivelyMeasurable_comp
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sub_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_sq_sub_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_abs_sub_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_window_sq_sub_le
#print axioms LevyStochCalc.Brownian.Ito.sum_setIntegral_unifGrid
#print axioms LevyStochCalc.Brownian.Ito.unifGrid_iUnion_Ioc
#print axioms LevyStochCalc.Brownian.Ito.lintegral_Icc_eq_sum_unifGrid
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_frozenRiemann_sub_le
#print axioms LevyStochCalc.Brownian.Ito.lintegral_sq_bounded_mul_lt_top
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_frozen_sub_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.lintegral_sq_martingaleRiemann_sub_le
#print axioms LevyStochCalc.integral_abs_le_of_bounded
#print axioms LevyStochCalc.integral_abs_add_four_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_drift_sq_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_cross_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_sum_quadVar_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.sq_sub_ae
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_quadVarRiemann_sub_le
-- B1a (2026-09-07): Ito's formula for a continuous version of a scalar Ito process.
#print axioms LevyStochCalc.Brownian.Ito.abs_sub_le_of_hasDerivAt_bound
#print axioms LevyStochCalc.Brownian.Ito.integral_abs_le_sqrt_of_lintegral_sq_le
#print axioms LevyStochCalc.Brownian.Ito.tendsto_itoGridError
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.integral_abs_itoFormula_le
#print axioms LevyStochCalc.Brownian.Ito.IsItoVersion.itoFormula
-- B1a-4 (2026-09-07): existence of a continuous adapted version.
#print axioms LevyStochCalc.abs_setIntegral_Icc_sub_le
#print axioms LevyStochCalc.continuous_setIntegral_Icc
#print axioms LevyStochCalc.Brownian.Ito.measurable_of_ae_eq_of_null_mem
#print axioms LevyStochCalc.Brownian.Ito.exists_measurable_null_of_ae
#print axioms LevyStochCalc.Brownian.Ito.exists_isItoVersion
-- B1a-5 (2026-09-07): the augmented filtration satisfies the usual conditions.
#print axioms LevyStochCalc.Brownian.Ito.tendsto_dyadicApprox
#print axioms LevyStochCalc.Probability.indep_aug
#print axioms LevyStochCalc.Brownian.isBrownianFiltration_augFiltration
#print axioms LevyStochCalc.Brownian.Ito.exists_isItoVersion_aug

-- ===== Layer 2: Itô-Lévy formula (→ deaxiomatises Cu03) =====
#print axioms LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique
-- Picard framework lemmas (active construction toward JumpDiffusion proof):
-- C0c-i (2026-09-07): the deterministic-time freeze.
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.minTime
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_min
#print axioms LevyStochCalc.Ito.Picard.SBoundedProcess.stop
#print axioms LevyStochCalc.Ito.Picard.SBoundedProcess.stop_eq_of_le
#print axioms LevyStochCalc.Ito.Picard.SBoundedProcess.stop_apply
#print axioms LevyStochCalc.Ito.Picard.SBoundedProcess.lintegral_sq_le_bieleckiNorm_sq
#print axioms LevyStochCalc.Ito.Picard.SBoundedProcess.lintegral_sq_stop_le
#print axioms LevyStochCalc.Ito.Picard.sq_coe_nnnorm
#print axioms LevyStochCalc.Ito.Picard.sq_coe_nnnorm_real
#print axioms LevyStochCalc.Ito.Picard.sq_norm_le_sum_sq
#print axioms LevyStochCalc.Ito.Picard.sq_sigma_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stop_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sigma_stop_lt_top
#print axioms LevyStochCalc.Ito.Picard.ofReal_sq_norm_le_sum
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_gamma_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_gamma_stop_lt_top
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_comp_state
#print axioms LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_comp_state
#print axioms LevyStochCalc.Ito.Picard.measurable_sigma_comp_state
#print axioms LevyStochCalc.Ito.Picard.measurable_gamma_comp_state
#print axioms LevyStochCalc.Ito.Picard.measurable_sigma_stop
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_stop
#print axioms LevyStochCalc.Ito.Picard.measurable_gamma_stop
#print axioms LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_stop
#print axioms LevyStochCalc.Ito.Picard.picardStepOnStop
#print axioms LevyStochCalc.Ito.Picard.sq_mu_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_mu_stop_lt_top
#print axioms LevyStochCalc.Ito.Picard.sq_nnnorm_sum_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_diffusion_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_jump_eq
#print axioms LevyStochCalc.Ito.Picard.enorm_sq_eq
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_setIntegral_le
#print axioms LevyStochCalc.Ito.Picard.sq_nnnorm_add_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_drift_le
#print axioms LevyStochCalc.Ito.Picard.itoIsometry_of_nonneg
#print axioms LevyStochCalc.Ito.Picard.compensatedIsometry_of_nonneg
#print axioms LevyStochCalc.Ito.Picard.measurable_setIntegral_slice
#print axioms LevyStochCalc.Ito.Picard.sq_nnnorm_add3_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_lintegral_Icc_mono
#print axioms LevyStochCalc.Ito.Picard.measurable_picardStep_drift
#print axioms LevyStochCalc.Ito.Picard.measurable_picardStep_diffusion
#print axioms LevyStochCalc.Ito.Picard.measurable_picardStep_jump
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_le
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardStep_lt_top
#print axioms LevyStochCalc.Ito.Picard.exists_cadlag_modification_itoIntegral
#print axioms LevyStochCalc.Probability.tendsto_nhdsGE_of_nhdsGT
#print axioms LevyStochCalc.Probability.dyadicCeil
#print axioms LevyStochCalc.Probability.dyadicCeil_le
#print axioms LevyStochCalc.Probability.le_dyadicCeil
#print axioms LevyStochCalc.Probability.measurable_dyadicCeil
#print axioms LevyStochCalc.Probability.tendsto_dyadicCeil
#print axioms LevyStochCalc.Probability.progressivelyMeasurable_of_rightContinuous
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_uncurry
#print axioms LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous
#print axioms LevyStochCalc.Probability.exists_everywhere_cadlag_modification
#print axioms LevyStochCalc.Ito.Picard.continuous_setIntegral_Icc_of_integrableOn
#print axioms LevyStochCalc.Ito.Picard.memLp_two_of_lintegral_sq_lt_top
#print axioms LevyStochCalc.Ito.Picard.integrableOn_of_lintegral_sq_lt_top
#print axioms LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
#print axioms LevyStochCalc.Ito.Picard.ae_memLp_two_of_lintegral_sq
#print axioms LevyStochCalc.Ito.Picard.ae_drift_diff_sq_bound
#print axioms LevyStochCalc.Ito.Picard.drift_diff_lintegral_sq_bound
#print axioms LevyStochCalc.Ito.Picard.diffusion_diff_lintegral_sq_bound
#print axioms LevyStochCalc.Ito.Picard.gamma_lip_componentwise
#print axioms LevyStochCalc.Ito.Picard.jump_diff_lintegral_sq_bound
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sum3_le
#print axioms LevyStochCalc.Ito.Picard.mu_lip_componentwise
#print axioms LevyStochCalc.Ito.Picard.lintegral_ofReal_sum_sq_eq
#print axioms LevyStochCalc.Ito.Picard.picardStep_apply_eq
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_picardStep_diff_le
#print axioms LevyStochCalc.Ito.Picard.ae_picardStep_zero
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardStep_diff_le
#print axioms LevyStochCalc.Ito.Picard.ae_continuous_picardStep_drift
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.measurable_setIntegral_Icc
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae
#print axioms LevyStochCalc.Ito.Picard.sigmaMod
#print axioms LevyStochCalc.Ito.Picard.sigmaMod_adapted
#print axioms LevyStochCalc.Ito.Picard.sigmaMod_ae_eq
#print axioms LevyStochCalc.Ito.Picard.sigmaMod_cadlag
#print axioms LevyStochCalc.Ito.Picard.picardStepMod
#print axioms LevyStochCalc.Ito.Picard.picardStepMod_ae_eq
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepMod
#print axioms LevyStochCalc.Ito.Picard.picardStepMod_adapted
#print axioms LevyStochCalc.Ito.Picard.picardStepMod_cadlag
#print axioms LevyStochCalc.Ito.Picard.exists_sBoundedProcess_picardStep
#print axioms LevyStochCalc.Ito.Picard.measurable_mu_comp_state
#print axioms LevyStochCalc.Ito.Picard.measurable_mu_stop
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_mu_stop
#print axioms LevyStochCalc.Ito.Picard.picardSelfMap
#print axioms LevyStochCalc.Ito.Picard.picardSelfMap_ae_eq
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_le_bieleckiNorm_sq_weighted
#print axioms LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_le_bieleckiNorm_sq
#print axioms LevyStochCalc.Ito.Picard.ofReal_setIntegral_le_lintegral
#print axioms LevyStochCalc.Ito.Picard.lintegral_window_norm_le_sum
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_le_of_perTime
#print axioms LevyStochCalc.Ito.Picard.sq_coe_nnnorm_le_sum
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_le_of_perTime_sup
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_le_of_perTime_bochner
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
-- Ex-Tier-1-axiom #14 chain (axiom→theorem 2026-05-26; the Picard chain closes through
-- `Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn`, 2026-09-07, with no `sorry`):
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

-- ===== Bielecki limits (C1b, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.limsup
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_le_of_perTime_rpow
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_rpow_le_of_bieleckiNorm
#print axioms LevyStochCalc.Ito.Picard.bieleckiLimit
#print axioms LevyStochCalc.Ito.Picard.measurable_bieleckiLimit
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_bieleckiLimit
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_sub_le_sum_Ico
#print axioms LevyStochCalc.Ito.Picard.lintegral_rpow_half_le
#print axioms LevyStochCalc.Ito.Picard.ae_tsum_ne_top
#print axioms LevyStochCalc.Ito.Picard.ae_summable_steps
#print axioms LevyStochCalc.Ito.Picard.ae_tendsto_bieleckiLimit
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sub_bieleckiLimit_rpow_le
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_sub_bieleckiLimit_le

-- ===== The Picard self-map is a Bielecki contraction (C2 bridge, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.sq_nnnorm_sub_le
#print axioms LevyStochCalc.Ito.Picard.measurable_uncurry_stop_sub
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_stop_sub_lt_top
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_stop_sub
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_diff_le
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardSelfMap_diff_le
#print axioms LevyStochCalc.Ito.Picard.tsum_geometric_shift
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_sub_bieleckiLimit_geometric
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_le_bieleckiNorm_zero
#print axioms LevyStochCalc.Ito.Picard.picardIter
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardIter_step_le
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardIter_sub_bieleckiLimit_le
#print axioms LevyStochCalc.Ito.Picard.exists_bieleckiWeight_rate_lt_one
-- ===== Integrand bounds along a raw state process of finite energy (C3 prep, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_energy
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_energy
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_mu_lt_top_of_energy
-- ===== The Picard step along a raw state process (C3 prep, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_le_bieleckiNorm_sq_raw
#print axioms LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_stopOf_le
#print axioms LevyStochCalc.Ito.Picard.measurable_sigma_rawStop
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_rawStop
#print axioms LevyStochCalc.Ito.Picard.measurable_gamma_rawStop
#print axioms LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_rawStop
#print axioms LevyStochCalc.Ito.Picard.measurable_mu_rawStop
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_mu_rawStop
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_rawStop_lt_top
#print axioms LevyStochCalc.Ito.Picard.picardStepOnRawStop
#print axioms LevyStochCalc.Ito.Picard.measurable_picardStep_slice
-- ===== The Picard fixed point (C2/C3a, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sub_lt_top_of_energy
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_sub_comm
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_zero_le_mul
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_approx
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnStop_sub_rawStop_le
#print axioms LevyStochCalc.Ito.Picard.picardLimit
#print axioms LevyStochCalc.Ito.Picard.measurable_picardLimit
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_picardLimit
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardLimit_lt_top
#print axioms LevyStochCalc.Ito.Picard.measurable_picardStepOnRawStop_slice
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_picardLimit_eq_zero
#print axioms LevyStochCalc.Ito.Picard.ae_eq_zero_of_bieleckiNorm_eq_zero
-- ===== Doob's L2 maximal inequality in continuous time (E1b, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.Filtration.compMono
#print axioms LevyStochCalc.Probability.martingale_compMono
#print axioms LevyStochCalc.Probability.dyadicTime
#print axioms LevyStochCalc.Probability.dyadicTime_succ_two_mul
#print axioms LevyStochCalc.Probability.dyadicRunMax
#print axioms LevyStochCalc.Probability.enorm_dyadicRunMax
#print axioms LevyStochCalc.Probability.enorm_dyadicRunMax_mono
#print axioms LevyStochCalc.Probability.tendsto_dyadicTime_dyadicIndex
#print axioms LevyStochCalc.Probability.iSup_enorm_eq_iSup_dyadicRunMax
#print axioms LevyStochCalc.Probability.iSup_sq_of_monotone
#print axioms LevyStochCalc.Probability.eLpNorm_two_eq
#print axioms LevyStochCalc.Probability.lintegral_sq_dyadicRunMax_le
#print axioms LevyStochCalc.Probability.lintegral_iSup_sq_le_of_martingale
#print axioms LevyStochCalc.Ito.Picard.picardSelfMapRaw
#print axioms LevyStochCalc.Ito.Picard.picardSelfMapRaw_ae_eq
#print axioms LevyStochCalc.Ito.Picard.picardSelfMapRaw_picardLimit_ae_eq
-- ===== The step respects a.e. equality of its input (C1c, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_picardStepOnRawStop_diff_le
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_eq_zero_of_ae
#print axioms LevyStochCalc.Ito.Picard.picardStepOnRawStop_congr_ae
-- ===== The fixed point solves its own Picard equation (C3a, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.picardSelfMapRaw_isFixedPoint
#print axioms LevyStochCalc.Probability.lintegral_iSup_dyadicRunMax_sq_le
#print axioms LevyStochCalc.Probability.enorm_dyadicRunMax_add_le
#print axioms LevyStochCalc.Probability.iSup_dyadicRunMax_add_le
#print axioms LevyStochCalc.Probability.iSup_dyadicRunMax_le_of_bound
#print axioms LevyStochCalc.Probability.iSup_sum_sq_le
#print axioms LevyStochCalc.Probability.sq_sum_le_card_sq_mul
#print axioms LevyStochCalc.Probability.enorm_dyadicRunMax_sum_le
#print axioms LevyStochCalc.Probability.iSup_dyadicRunMax_sum_le
-- ===== The S2 bound for the Picard step (C3a, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.sq_add_le_four_mul
#print axioms LevyStochCalc.Ito.Picard.sq_add3_le_sixteen_mul
#print axioms LevyStochCalc.Ito.Picard.iSup_dyadicRunMax_drift_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_drift_bound_lt_top
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_iSup_jump_le
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_iSup_brownian_coord_le
#print axioms LevyStochCalc.Ito.Picard.measurable_brownianIntegral_slice
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_iSup_diffusion_lt_top
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardStep_lt_top
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_iSup_picardSelfMapRaw_lt_top
-- ===== Locality of the Picard step (C3-global scaffolding, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.measurable_itoIntegral_slice
#print axioms LevyStochCalc.Ito.Picard.measurable_compensatedIntegral_slice
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sub_eq_zero_of_ae
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sub_mark_eq_zero_of_ae
#print axioms LevyStochCalc.Ito.Picard.itoIntegral_congr_ae
#print axioms LevyStochCalc.Ito.Picard.compensatedIntegral_congr_ae
#print axioms LevyStochCalc.Ito.Picard.picardStep_drift_congr_ae
#print axioms LevyStochCalc.Ito.Picard.picardStep_diffusion_congr_ae
#print axioms LevyStochCalc.Ito.Picard.picardStep_jump_congr_ae
#print axioms LevyStochCalc.Ito.Picard.picardStep_congr_ae
-- ===== Solutions on a window: existence and uniqueness (C3a/C4, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.lintegral_lintegral_sq_lt_top_of_supL2
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_congr_ae_on
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_lt_top_of_supL2
#print axioms LevyStochCalc.Ito.Picard.bieleckiNorm_sub_lt_top_of_lt_top
#print axioms LevyStochCalc.Ito.Picard.eq_zero_of_le_mul_self
#print axioms LevyStochCalc.Ito.Picard.SolvesOn
#print axioms LevyStochCalc.Ito.Picard.SolvesOn.mono
#print axioms LevyStochCalc.Ito.Picard.ae_eq_of_solvesOn
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_sigma_comp_state
#print axioms LevyStochCalc.Ito.Picard.markedProgressivelyMeasurable_gamma_comp_state
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_sigma_lt_top_of_supL2
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_gamma_lt_top_of_supL2
#print axioms LevyStochCalc.Ito.Picard.picardStep_rawStop_congr_ae
#print axioms LevyStochCalc.Ito.Picard.solvesOn_of_isFixedPoint
#print axioms LevyStochCalc.Ito.Picard.exists_solvesOn
-- ===== Gluing window solutions into a solution on [0, ∞) (C3-global, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont
#print axioms LevyStochCalc.Ito.Picard.globalPatch
#print axioms LevyStochCalc.Ito.Picard.measurable_globalPatch
#print axioms LevyStochCalc.Ito.Picard.progressivelyMeasurable_globalPatch
#print axioms LevyStochCalc.Ito.Picard.ae_all_windows_agree
#print axioms LevyStochCalc.Ito.Picard.ae_globalPatch_eq
#print axioms LevyStochCalc.Ito.Picard.lintegral_sq_iSup_globalPatch_lt_top
#print axioms LevyStochCalc.Ito.Picard.cadlag_globalPatch
#print axioms LevyStochCalc.Ito.Picard.solvesOn_globalPatch
#print axioms LevyStochCalc.Ito.Picard.ae_eq_initial_of_solvesOn
#print axioms LevyStochCalc.Ito.Picard.exists_globalSolution
-- ===== Well-posedness of the jump-diffusion SDE (C5, 2026-09-07) =====
#print axioms LevyStochCalc.Ito.Picard.eqn_sum_form
#print axioms LevyStochCalc.Ito.Picard.jumpDiffusionOfSolvesOn
#print axioms LevyStochCalc.Ito.Picard.solvesOn_of_eqn
#print axioms LevyStochCalc.Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn
-- ===== The predictable sigma-algebra over an R-indexed filtration (A5a, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.predictableSigma
#print axioms LevyStochCalc.Probability.measurableSet_predictableSigma_Iic_prod
#print axioms LevyStochCalc.Probability.measurableSet_predictableSigma_Ioi_prod
#print axioms LevyStochCalc.Probability.measurable_inclusion_predictableSigma
#print axioms LevyStochCalc.Probability.Predictable
#print axioms LevyStochCalc.Probability.Predictable.progressivelyMeasurable
-- ===== Characters are total in L2 of a finite measure (A4b-i-1, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.charFun_withDensity_ofReal
#print axioms LevyStochCalc.Probability.integrable_char_smul
#print axioms LevyStochCalc.Probability.integrable_char_mul
#print axioms LevyStochCalc.Probability.integrable_conj
#print axioms LevyStochCalc.Probability.integrable_toNNReal_coe
#print axioms LevyStochCalc.Probability.ae_eq_zero_of_integral_char_smul_eq_zero
#print axioms LevyStochCalc.Probability.char_neg
#print axioms LevyStochCalc.Probability.ae_eq_zero_of_integral_char_mul_eq_zero
#print axioms LevyStochCalc.Probability.memLp_char
#print axioms LevyStochCalc.Probability.charLp
#print axioms LevyStochCalc.Probability.topologicalClosure_span_charLp
#print axioms LevyStochCalc.Probability.ae_eq_zero_of_integral_char_comp_eq_zero
-- ===== Set integrals over the sigma-algebra a random vector generates (A4b-i-3, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.integrable_charComp_smul
#print axioms LevyStochCalc.Probability.charFun_map_withDensity_ofReal
#print axioms LevyStochCalc.Probability.map_withDensity_eq_of_integral_char_comp_smul_eq_zero
#print axioms LevyStochCalc.Probability.integral_smul_re_im_eq_zero
#print axioms LevyStochCalc.Probability.setIntegral_eq_zero_of_integral_char_comp_smul_eq_zero
#print axioms LevyStochCalc.Probability.setIntegral_eq_zero_of_integral_char_comp_mul_eq_zero
-- ===== Vanishing set integrals over a pi-system / directed family (A4b-i-3, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.setIntegral_eq_zero_of_isPiSystem
#print axioms LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_isPiSystem
#print axioms LevyStochCalc.Probability.ae_eq_zero_of_forall_setIntegral_eq_zero_directed
-- ===== Cylinder characters determine a.e. vanishing (A4b-i-3, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.ae_eq_zero_of_integral_char_comp_directed
#print axioms LevyStochCalc.Probability.finDimVector
#print axioms LevyStochCalc.Probability.measurable_finDimVector
#print axioms LevyStochCalc.Probability.comap_finDimVector
#print axioms LevyStochCalc.Probability.directed_comap_finDimVector
#print axioms LevyStochCalc.Probability.iSup_comap_finDimVector
#print axioms LevyStochCalc.Probability.ae_eq_zero_of_integral_char_cylinder_eq_zero
-- ===== Cylinder characters of a Brownian motion (A4b-i, 2026-09-07) =====
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_eq_iSup_comap
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.ae_eq_zero_of_integral_char_cylinder
-- ===== Gronwall in integral form (A4b-ii-1, 2026-09-07) =====
#print axioms LevyStochCalc.Analysis.le_mul_pow_div_factorial_of_le_mul_setIntegral
#print axioms LevyStochCalc.Analysis.eq_zero_of_le_mul_setIntegral
-- ===== Fubini for a pairing against a time integral (A4b-ii-4, 2026-09-07) =====
#print axioms LevyStochCalc.Probability.integral_mul_setIntegral_Ioc
-- ===== Ito integral of an indicator is a Brownian increment (A4b-ii-2, 2026-09-07) =====
#print axioms LevyStochCalc.Brownian.Ito.indIoc
#print axioms LevyStochCalc.Brownian.Ito.indIoc_le_one
#print axioms LevyStochCalc.Brownian.Ito.measurable_uncurry_indIoc
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indIoc₀
#print axioms LevyStochCalc.Brownian.Ito.lintegral_sq_indIoc_lt_top
#print axioms LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_indIoc
-- ===== The scaled cosine and sine (A4b-ii-5, 2026-09-07) =====
#print axioms LevyStochCalc.Analysis.hasDerivAt_cos_scaled
#print axioms LevyStochCalc.Analysis.hasDerivAt_sin_scaled
#print axioms LevyStochCalc.Analysis.hasDerivAt_neg_sin_scaled
#print axioms LevyStochCalc.Analysis.hasDerivAt_cos_scaled_mul
#print axioms LevyStochCalc.Analysis.lipschitz_neg_sq_mul_cos_scaled
#print axioms LevyStochCalc.Analysis.lipschitz_neg_sq_mul_sin_scaled
-- ===== Ito's formula for the scaled trig functions (A4b-ii-5, 2026-09-07) =====
#print axioms LevyStochCalc.Brownian.Ito.lintegral_sq_lt_top_of_bounded
#print axioms LevyStochCalc.Brownian.Ito.measurable_trig_integrand
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_trig_integrand
#print axioms LevyStochCalc.Brownian.Ito.lintegral_sq_trig_integrand_lt_top
#print axioms LevyStochCalc.Brownian.Ito.itoFormula_cos_scaled
#print axioms LevyStochCalc.Brownian.Ito.itoFormula_sin_scaled
-- ===== A past weight passes inside an Ito integral over a window (A4b-ii-3, 2026-09-07) =====
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul₀
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul_eval
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul₀_eval
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul_adapt
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul₀_adapt
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul_integralAgainst
#print axioms LevyStochCalc.Brownian.Ito.stepIocMul₀_integralAgainst
#print axioms LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_indIoc
-- ===== Pairing against a trigonometric increment (A4b-iii, 2026-09-07) =====
#print axioms LevyStochCalc.Brownian.Ito.indIoc_sq
#print axioms LevyStochCalc.Brownian.Ito.integrable_mul_of_bounded
#print axioms LevyStochCalc.Brownian.Ito.PerpItoIntegrals
#print axioms LevyStochCalc.Brownian.Ito.measurable_pairing
#print axioms LevyStochCalc.Brownian.Ito.ae_eq_zero_of_isItoVersion_indIoc
#print axioms LevyStochCalc.Brownian.Ito.ae_eq_increment_of_isItoVersion_indIoc
#print axioms LevyStochCalc.Brownian.Ito.trigDrift
#print axioms LevyStochCalc.Brownian.Ito.trigDrift_eq
#print axioms LevyStochCalc.Brownian.Ito.norm_pairing_le_setIntegral_norm
#print axioms LevyStochCalc.Brownian.Ito.pairing_zero_time
#print axioms LevyStochCalc.Brownian.Ito.pairing_eq_zero_of_norm_le
-- ===== The dW term pairs to zero (A4b-iii, 2026-09-07) =====
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_mul_indIoc
#print axioms LevyStochCalc.Brownian.Ito.memLp_ofReal
#print axioms LevyStochCalc.Brownian.Ito.pairing_ito_eq_zero
-- ===== One window of the Brownian PRP (A4b-iii, 2026-09-07) =====
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_zero
#print axioms LevyStochCalc.Brownian.Ito.pairing_cell_eq_zero
-- ===== The PRP over a grid (A4b-iii-2, A4b-iii-3, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.gridCharacter
#print axioms LevyStochCalc.Brownian.Ito.norm_gridCharacter
#print axioms LevyStochCalc.Brownian.Ito.measurable_gridCharacter
#print axioms LevyStochCalc.Brownian.Ito.pairing_gridCharacter_eq_zero
#print axioms LevyStochCalc.Brownian.Ito.gridCharacter_eq_exp
#print axioms LevyStochCalc.Brownian.Ito.sum_tail_mul_sub
#print axioms LevyStochCalc.Brownian.Ito.pairing_value_character_eq_zero
-- ===== Independence of two joins from blockwise independence (A4b-iii-4a, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.indepSets_piiUnionInter_of_blocks
#print axioms LevyStochCalc.Probability.indep_iSup_of_indep_blocks
-- ===== Sum of independent centred Gaussians (A4b-iii-4a, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.map_finsetSum_gaussianReal
-- ===== A unit linear combination is a Brownian motion (A4b-iii-4a/4b, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combine
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.measurable_combine
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.measurable_uncurry_combine
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combine_sub
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.iIndepFun_scaled_increment
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.map_combine_sub
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.comap_combine_le
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.comap_combine_sub_le
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.indep_naturalFiltration_combine_sub
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.indep_combine
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.combineBM
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isBrownianFiltration_combineBM
-- ===== Linearity of the Ito integral in the driver (A4b-iii-4c, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.simpleIntegral_combineBM
#print axioms LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_eLpNorm
#print axioms LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_combineBM
-- ===== One window, multidimensional (A4b-iii-4d, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.perpItoIntegrals_combineBM
#print axioms LevyStochCalc.Brownian.Ito.pairing_cell_multidim_eq_zero
-- ===== The multidimensional grid induction (A4b-iii-5, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.gridCharacterMultidim
#print axioms LevyStochCalc.Brownian.Ito.norm_gridCharacterMultidim
#print axioms LevyStochCalc.Brownian.Ito.measurable_gridCharacterMultidim
#print axioms LevyStochCalc.Brownian.Ito.pairing_gridCharacterMultidim_eq_zero
#print axioms LevyStochCalc.Brownian.Ito.gridCharacterMultidim_eq_exp
#print axioms LevyStochCalc.Brownian.Ito.pairing_value_characterMultidim_eq_zero
-- ===== Sorting a weighted family of times into a grid (A4b-iii-5b, 2026-09-08) =====
#print axioms LevyStochCalc.Analysis.sortedGrid
#print axioms LevyStochCalc.Analysis.sortedGrid_zero
#print axioms LevyStochCalc.Analysis.sortedGrid_succ_of_lt
#print axioms LevyStochCalc.Analysis.sortedGrid_succ_mem
#print axioms LevyStochCalc.Analysis.sortedGrid_lt_succ
#print axioms LevyStochCalc.Analysis.sum_Ico_sortedGrid
#print axioms LevyStochCalc.Analysis.posTimes
#print axioms LevyStochCalc.Analysis.pos_of_mem_posTimes
#print axioms LevyStochCalc.Analysis.mem_posTimes
#print axioms LevyStochCalc.Analysis.weightAt
#print axioms LevyStochCalc.Analysis.sum_weightAt_mul
#print axioms LevyStochCalc.Analysis.sum_weight_eq_sum_grid
-- ===== The orthogonal complement of the Brownian Ito integrals (A4b-iii-5c, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.ae_forall_eq_zero_of_nonpos
#print axioms LevyStochCalc.Brownian.Ito.pairing_char_cylinder_eq_zero
#print axioms LevyStochCalc.Brownian.Ito.ae_eq_zero_of_perpItoIntegrals
-- ===== Measurability for a sub-sigma-algebra and its augmentation (A4b-iii-5d, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.convSet
#print axioms LevyStochCalc.Probability.mem_convSet
#print axioms LevyStochCalc.Probability.limitOn
#print axioms LevyStochCalc.Probability.tendsto_indicator_limitOn
#print axioms LevyStochCalc.Probability.stronglyMeasurable_limitOn
#print axioms LevyStochCalc.Probability.aestronglyMeasurable_of_tendsto_ae_sub
#print axioms LevyStochCalc.Probability.aestronglyMeasurable_indicator_aug
#print axioms LevyStochCalc.Probability.aestronglyMeasurable_simpleFunc_aug
#print axioms LevyStochCalc.Probability.aestronglyMeasurable_of_stronglyMeasurable_aug
#print axioms LevyStochCalc.Brownian.Ito.ae_eq_zero_of_perpItoIntegrals_augFiltration
-- ===== Linearity of the L2 Ito integral in the integrand (A4b-iii-6a, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.add
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.sub
#print axioms LevyStochCalc.Brownian.Ito.sq_nnnorm_eq_ofReal_sq
#print axioms LevyStochCalc.Brownian.Ito.integral_sq_eq_toReal
#print axioms LevyStochCalc.Brownian.Ito.integrable_sq_of_memLp
#print axioms LevyStochCalc.Brownian.Ito.measurable_energyDensity
#print axioms LevyStochCalc.Brownian.Ito.lintegral_energy_parallelogram
#print axioms LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound
#print axioms LevyStochCalc.Brownian.Ito.lintegral_energy_const_mul
#print axioms LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul
#print axioms LevyStochCalc.Brownian.Ito.sq_nnnorm_add_le_two_mul
#print axioms LevyStochCalc.Brownian.Ito.ae_eq_add_of_sq_distances
#print axioms LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_add
#print axioms LevyStochCalc.Brownian.Ito.ae_eq_const_mul_of_sq_distances
#print axioms LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_const_mul
-- ===== Completeness of the admissible integrands (A4b-iii-6b, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.energyMeasure
#print axioms LevyStochCalc.Brownian.Ito.energy
#print axioms LevyStochCalc.Brownian.Ito.eLpNorm_sq_eq_lintegral
#print axioms LevyStochCalc.Brownian.Ito.energy_eq_eLpNorm_sq
#print axioms LevyStochCalc.Brownian.Ito.memLp_of_energy_ne_top
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_indicator_Icc
#print axioms LevyStochCalc.Brownian.Ito.energy_le_of_vanishing
#print axioms LevyStochCalc.Brownian.Ito.exists_energy_limit
#print axioms LevyStochCalc.Brownian.Ito.limsupIntegrand
#print axioms LevyStochCalc.Brownian.Ito.exists_progressive_energy_limit
-- ===== The closed range of the Ito integral and the representation (A4b-iii-6c/6d, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_const
#print axioms LevyStochCalc.Brownian.Ito.energy_ne_top_of_bound
#print axioms LevyStochCalc.Brownian.Ito.energy_add_ne_top
#print axioms LevyStochCalc.Brownian.Ito.energy_const_mul_ne_top
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.sq_int_global
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.integral
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.zero
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.add
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.smul
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.memLp
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.lintegral_sq_integral_sub
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.integral_zero
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.integral_add
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.integral_smul
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.integral_mean_zero
#print axioms LevyStochCalc.Brownian.Ito.itoRange
#print axioms LevyStochCalc.Brownian.Ito.energy_eq_edist_sq
#print axioms LevyStochCalc.Brownian.Ito.isClosed_itoRange
#print axioms LevyStochCalc.Brownian.Ito.HorizonIntegrand.aestronglyMeasurable
#print axioms LevyStochCalc.Brownian.Ito.exists_horizonIntegrand_of_mean_zero
-- ===== Driver increments against the right-continuous filtration (A2b, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.LevyDriver.isBrownianFiltration_rightCont
#print axioms LevyStochCalc.Driver.LevyDriver.isPoissonFiltration_rightCont
#print axioms LevyStochCalc.Driver.LevyDriver.indep_increment_rightCont
#print axioms LevyStochCalc.Driver.LevyDriver.indep_count_rightCont
-- ===== Second-order Taylor on a normed space (B1b-1, 2026-09-08) =====
#print axioms LevyStochCalc.abs_sub_taylor_two_le_normed
-- ===== Stopping a progressively measurable process (B1d-1, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.stopped
#print axioms LevyStochCalc.Probability.abs_stopped_le
#print axioms LevyStochCalc.Probability.stoppedRegion
#print axioms LevyStochCalc.Probability.mem_stoppedRegion
#print axioms LevyStochCalc.Probability.measurableSet_stoppedRegion
#print axioms LevyStochCalc.Probability.ProgressivelyMeasurable.stopped
-- ===== Restricting a Poisson random measure to a mark set (B2a-1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.referenceIntensity_restrict
#print axioms LevyStochCalc.Poisson.referenceIntensity_restrict_apply
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.restrict
#print axioms LevyStochCalc.Poisson.PoissonRandomMeasure.restrict_apply
-- ===== Second-order Taylor in time and space (B1c-1, 2026-09-08) =====
#print axioms LevyStochCalc.clm_apply_prod
#print axioms LevyStochCalc.clm_apply_prod₂
#print axioms LevyStochCalc.norm_prod_le_add
#print axioms LevyStochCalc.abs_sub_taylor_two_time_le
-- ===== Doob's L2 bound for the stochastic integrals (E1c/E1d, 2026-09-08) =====
#print axioms LevyStochCalc.Martingale.lintegral_iSup_sq_le_energy_brownian
#print axioms LevyStochCalc.Martingale.lintegral_iSup_sq_le_energy_compensated
#print axioms LevyStochCalc.Martingale.sq_enorm_add_le
#print axioms LevyStochCalc.Martingale.lintegral_iSup_sq_sum_le
-- ===== Taylor against a modulus of continuity (B1e-1, 2026-09-08) =====
#print axioms LevyStochCalc.abs_sub_taylor_one_le_modulus
#print axioms LevyStochCalc.abs_sub_taylor_two_le_modulus
#print axioms LevyStochCalc.abs_sub_taylor_two_le_modulus_normed
-- ===== Finite activity on a mark set of finite intensity (B2b-1a, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.referenceIntensity_Ioc_prod
#print axioms LevyStochCalc.Poisson.exists_nat_count_Ioc
#print axioms LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top
#print axioms LevyStochCalc.Poisson.count_Ioc_ne_top
-- ===== Exit times of a continuous adapted process (B1d-3, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.exitSet
#print axioms LevyStochCalc.Probability.exitTime
#print axioms LevyStochCalc.Probability.gridPt
#print axioms LevyStochCalc.Probability.bddBelow_exitSet
#print axioms LevyStochCalc.Probability.isClosed_exitSet
#print axioms LevyStochCalc.Probability.csInf_exitSet_mem
#print axioms LevyStochCalc.Probability.coe_zero_le_exitTime
#print axioms LevyStochCalc.Probability.exitTime_le_iff
#print axioms LevyStochCalc.Probability.gridPt_mem_Icc
#print axioms LevyStochCalc.Probability.abs_clamp_sub_le
#print axioms LevyStochCalc.Probability.exists_gridPt_near
#print axioms LevyStochCalc.Probability.exitTime_le_iff_forall
#print axioms LevyStochCalc.Probability.measurable_norm_of_adapted
#print axioms LevyStochCalc.Probability.measurableSet_exitTime_le
#print axioms LevyStochCalc.Probability.isStoppingTime_exitTime
#print axioms LevyStochCalc.Probability.exitTime_mono
#print axioms LevyStochCalc.Probability.exists_lt_exitTime
-- ===== Orthogonality across Brownian coordinates (A4b-iii-7, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.crossFiltration
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.crossFiltration_apply
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isBrownianFiltration_crossFiltration
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_le_crossFiltration
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.measurable_increment_crossFiltration
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero_of_le
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_cross_increment_eq_zero
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.min_eq_or_lt_min
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_increment_sq
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_cross_term
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integrable_and_integral_cross_clamped
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_simpleIntegral_mul_eq_zero
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_simpleIntegral
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.inner_toLp_eq_integral_mul
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_mul_eq_zero_of_tendsto_eLpNorm
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero
-- ===== The closed range of the multidim Ito integral (A4b-iii-8, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isClosed_iSup_of_orthogonalFamily
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.orthogonalFamily_itoRange
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isClosed_iSup_itoRange
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.vectorIntegral
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.memLp_vectorIntegral
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.integral_vectorIntegral_eq_zero
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.aestronglyMeasurable_vectorIntegral
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_vectorIntegral_of_mean_zero
-- ===== The cross witness and the augmented filtration (A4b-iii-9a, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.CrossWitness
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.crossWitnessNatural
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.CrossWitness.aug
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.crossWitnessAugNatural
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isBrownianFiltration_augNatural
-- ===== The perp bridge and the multidim Brownian PRP (A4b-iii-9b, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.clipHorizonIntegrand
#print axioms LevyStochCalc.Brownian.Ito.integral_clipHorizonIntegrand
#print axioms LevyStochCalc.Brownian.Ito.integrable_mul_of_memLp_two
#print axioms LevyStochCalc.Brownian.Ito.integral_mul_increment_eq_zero
#print axioms LevyStochCalc.Brownian.Ito.integral_mul_stochasticIntegral_eq_zero
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_vectorIntegral_augFiltration
-- ===== Cylinder characters of a Poisson random measure (A4c-i, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.encodeEquiv
#print axioms LevyStochCalc.Poisson.encode
#print axioms LevyStochCalc.Poisson.measurableEmbedding_encode
#print axioms LevyStochCalc.Poisson.comap_encode
#print axioms LevyStochCalc.Poisson.PastSet
#print axioms LevyStochCalc.Poisson.naturalFiltration_eq_iSup_comap
#print axioms LevyStochCalc.Poisson.ae_eq_zero_of_integral_char_cylinder
-- ===== Completeness of the marked integrands (A4c-iii-a1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergyMeasure
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_eq_eLpNorm_sq
#print axioms LevyStochCalc.Poisson.Compensated.memLp_of_markedEnergy_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_le_of_vanishing
#print axioms LevyStochCalc.Poisson.Compensated.exists_markedEnergy_limit
#print axioms LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_limsup
#print axioms LevyStochCalc.Poisson.Compensated.limsupMarkedIntegrand
#print axioms LevyStochCalc.Poisson.Compensated.exists_marked_progressive_energy_limit
-- ===== Linearity of the compensated Poisson integral (A4c-iii-a2-i, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.markedDensity
#print axioms LevyStochCalc.Poisson.Compensated.measurable_markedDensity
#print axioms LevyStochCalc.Poisson.Compensated.measurable_markSlice
#print axioms LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_parallelogram
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_le_two_mul_add
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_lt_top_of_bound
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_ne_top_of_bound
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_add_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_memLp
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_add
#print axioms LevyStochCalc.Poisson.Compensated.lintegral_markedEnergy_const_mul
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_const_mul
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_const_mul_ne_top
-- ===== The closed range of the compensated integral and the representation (A4c-iii-a2-ii, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_zero
#print axioms LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_add
#print axioms LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_const_mul
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.sq_int_global
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.zero
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.add
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.smul
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.memLp
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.lintegral_sq_integral_sub
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_zero
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_add
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_smul
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mean_zero
#print axioms LevyStochCalc.Poisson.Compensated.compensatedRange
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_eq_edist_sq
#print axioms LevyStochCalc.Poisson.Compensated.isClosed_compensatedRange
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.aestronglyMeasurable
#print axioms LevyStochCalc.Poisson.Compensated.exists_markedHorizonIntegrand_of_mean_zero
-- ===== Integer-valued finite measures (B2b-1b-i/ii, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.IsIntegerValued
#print axioms LevyStochCalc.Probability.isIntegerValued_of_isPiSystem
#print axioms LevyStochCalc.Probability.finInters
#print axioms LevyStochCalc.Probability.mem_finInters_iff
#print axioms LevyStochCalc.Probability.countable_finInters
#print axioms LevyStochCalc.Probability.isPiSystem_finInters
#print axioms LevyStochCalc.Probability.measurableSet_of_mem_finInters
#print axioms LevyStochCalc.Probability.generateFrom_finInters
#print axioms LevyStochCalc.Probability.exists_one_le_measure_singleton
#print axioms LevyStochCalc.Probability.exists_finset_ae_mem
#print axioms LevyStochCalc.Probability.exists_eq_sum_dirac
-- ===== Atomicity on a finite-activity window (B2b-1b-iii, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.markPiSystem
#print axioms LevyStochCalc.Poisson.generateFrom_markPiSystem
#print axioms LevyStochCalc.Poisson.isPiSystem_markPiSystem
#print axioms LevyStochCalc.Poisson.ae_isIntegerValued_restrict
#print axioms LevyStochCalc.Poisson.ae_exists_eq_sum_dirac
#print axioms LevyStochCalc.Poisson.ae_exists_finset_support
#print axioms LevyStochCalc.Poisson.ae_exists_eq_sum_dirac_Ioc
#print axioms LevyStochCalc.Poisson.ae_exists_finset_support_Ioc
-- ===== The pathwise jump sum (B2b-2, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.lintegral_of_eq_sum_dirac
#print axioms LevyStochCalc.Poisson.integral_of_eq_sum_dirac
#print axioms LevyStochCalc.Poisson.exists_strictMono_enum
#print axioms LevyStochCalc.Poisson.jumpTimes
#print axioms LevyStochCalc.Poisson.ae_exists_finset_integral_eq_sum
#print axioms LevyStochCalc.Poisson.ae_exists_finset_integral_eq_sum_Ioc
-- ===== The pathwise elementary compensated integral (B2b-3a, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.measurableSet_fullRect
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.referenceIntensity_fullRect_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.timeRect_horizon
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.markSet
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.measurableSet_markSet
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.measure_markSet_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.fullRect_subset
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.eval_eq_zero_of_notMem
#print axioms LevyStochCalc.Poisson.Compensated.SimplePredictable.integral_eval_eq_sum
#print axioms LevyStochCalc.Poisson.Compensated.simpleIntegral_eq_sub_integral
#print axioms LevyStochCalc.Poisson.Compensated.ae_count_fullRect_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.ae_simpleIntegral_eq_sub_integral
#print axioms LevyStochCalc.Poisson.Compensated.ae_exists_finset_simpleIntegral_eq
-- ===== The marked predictable sigma-algebra (B2b-3b-i, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.markedPredictableRect
#print axioms LevyStochCalc.Probability.isPiSystem_markedPredictableRect
#print axioms LevyStochCalc.Probability.markedPredictableSigma
#print axioms LevyStochCalc.Probability.MarkedPredictable
#print axioms LevyStochCalc.Probability.measurableSet_timeIic
#print axioms LevyStochCalc.Probability.measurableSet_inter_timeIic
#print axioms LevyStochCalc.Probability.markedPredictableSigma_le
#print axioms LevyStochCalc.Probability.measurableSet_slice
#print axioms LevyStochCalc.Probability.MarkedPredictable.markedProgressivelyMeasurable
-- ===== The reference intensity as compensator (B2b-3b-i, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.lintegral_count_eq_referenceIntensity
#print axioms LevyStochCalc.Poisson.referenceIntensity_Ioc_prod_ne_top'
#print axioms LevyStochCalc.Poisson.setLIntegral_count_eq
#print axioms LevyStochCalc.Poisson.sliceCount
#print axioms LevyStochCalc.Poisson.sliceIntensity
#print axioms LevyStochCalc.Poisson.aemeasurable_and_lintegral_slice_eq
#print axioms LevyStochCalc.Poisson.aemeasurable_and_lintegral_lintegral_slice_eq
#print axioms LevyStochCalc.Poisson.lintegral_lintegral_slice_eq
-- ===== Mark-step approximants are pathwise and predictable (B2b-3b-ii, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.eval_eq_sum_indicator
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_eval_eq_sum
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.full_eq_sub_integral
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.ae_count_rect_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.ae_full_eq_sub_integral
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.markedPredictable_eval
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.Ioc_inter_Iic
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.fullRect_inter_Iic
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.evalTo_eq_sum_indicator
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_evalTo_eq_sum
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.integral_eq_sub_integral
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.markedPredictable_evalTo
-- ===== From energy to the mean pathwise integral (B2b-3b-ii, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.lintegral_enorm_le_energy
#print axioms LevyStochCalc.Poisson.lintegral_enorm_count_eq
#print axioms LevyStochCalc.Poisson.lintegral_enorm_pathwise_le
#print axioms LevyStochCalc.Poisson.tendsto_lintegral_enorm_pathwise
#print axioms LevyStochCalc.Poisson.lintegral_referenceIntensity_window
#print axioms LevyStochCalc.Poisson.ae_integrableOn_window
#print axioms LevyStochCalc.Poisson.pathwise_sub
-- ===== Mark-restricted approximants (B2b-3b-ii-c1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.restrictMarks
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.restrictMarks_B_subset
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.restrictMarks_adapted
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.eval_restrictMarks_of_mem
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.eval_restrictMarks_of_notMem
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.abs_sub_eval_restrictMarks_le
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.lintegral_sq_sub_eval_restrictMarks_le
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.lintegral_integral_sub_restrictMarks_le
-- ===== The predictable compensated integral is pathwise (B2b-3b-ii-c, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.ae_count_clamped_rect_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.MarkStep.eval_eq_zero_of_nonpos
#print axioms LevyStochCalc.Poisson.lintegral_enorm_le_eLpNorm_two
#print axioms LevyStochCalc.Poisson.eLpNorm_two_eq_rpow
#print axioms LevyStochCalc.Poisson.ae_eq_of_tendsto_lintegral_enorm
#print axioms LevyStochCalc.Poisson.tendsto_lintegral_enorm_of_eLpNorm
#print axioms LevyStochCalc.Poisson.aestronglyMeasurable_pathwise_count
#print axioms LevyStochCalc.Poisson.stronglyMeasurable_pathwise_intensity
#print axioms LevyStochCalc.Poisson.Compensated.restrictedStage
#print axioms LevyStochCalc.Poisson.Compensated.restrictedStage_adapted
#print axioms LevyStochCalc.Poisson.Compensated.evalTo_restrictedStage_eq_zero
#print axioms LevyStochCalc.Poisson.Compensated.ae_restrictedStage_integral_eq
#print axioms LevyStochCalc.Poisson.Compensated.window_energy_le_stageErr
#print axioms LevyStochCalc.Poisson.Compensated.tendsto_stageErr
#print axioms LevyStochCalc.Poisson.Compensated.stageDefect
#print axioms LevyStochCalc.Poisson.Compensated.markedPredictable_stageDefect
#print axioms LevyStochCalc.Poisson.Compensated.measurable_stageDefect
#print axioms LevyStochCalc.Poisson.Compensated.window_energy_stageDefect_le
#print axioms LevyStochCalc.Poisson.Compensated.window_energy_stageDefect_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.window_energy_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.tendsto_lintegral_process_sub_restrictedStage
#print axioms LevyStochCalc.Poisson.Compensated.tendsto_lintegral_restrictedStage_sub_pathwise
#print axioms LevyStochCalc.Poisson.Compensated.process_ae_eq_pathwise
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise
-- ===== Time-simplicity on a finite-intensity set (A4c-ii-a, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.poissonMeasure_two_le_le
#print axioms LevyStochCalc.Poisson.measure_two_le_count_le
#print axioms LevyStochCalc.Poisson.timeSlab
#print axioms LevyStochCalc.Poisson.measurableSet_timeSlab
#print axioms LevyStochCalc.Poisson.volume_timeSlab
#print axioms LevyStochCalc.Poisson.pairwiseDisjoint_timeSlab
#print axioms LevyStochCalc.Poisson.iUnion_timeSlab
#print axioms LevyStochCalc.Poisson.exists_iSup_setLIntegral_timeSlab_le
#print axioms LevyStochCalc.Poisson.sectionDensity
#print axioms LevyStochCalc.Poisson.measurable_sectionDensity
#print axioms LevyStochCalc.Poisson.referenceIntensity_inter_time
#print axioms LevyStochCalc.Poisson.lintegral_sectionDensity
#print axioms LevyStochCalc.Poisson.ae_exists_forall_count_timeSlab_le_one
#print axioms LevyStochCalc.Poisson.ae_count_time_singleton_le_one
-- ===== The jump chain rule (A4c-ii-b, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.prod_sub_one_eq_sum
#print axioms LevyStochCalc.Poisson.integral_of_eq_sum_dirac'
#print axioms LevyStochCalc.Poisson.windowSum
#print axioms LevyStochCalc.Poisson.windowSumStrict
#print axioms LevyStochCalc.Poisson.ae_exp_windowSum_sub_one
-- ===== Deterministic factors are predictable (A4c-ii-c1, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.measurableSet_univ_prod_window_self
#print axioms LevyStochCalc.Probability.measurableSet_univ_prod_timeInter
#print axioms LevyStochCalc.Probability.measurableSet_univ_prod_window
#print axioms LevyStochCalc.Probability.markedPredictable_of_measurable_window
#print axioms LevyStochCalc.Probability.markedPredictable_rectIndicator
-- ===== The strictly-past count is predictable (A4c-ii-c1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.dyadicLeft
#print axioms LevyStochCalc.Poisson.one_le_ceil_mul_pow
#print axioms LevyStochCalc.Poisson.cast_ceil_pred
#print axioms LevyStochCalc.Poisson.dyadicLeft_lt
#print axioms LevyStochCalc.Poisson.sub_le_dyadicLeft
#print axioms LevyStochCalc.Poisson.dyadicLeft_le_succ
#print axioms LevyStochCalc.Poisson.dyadicLeft_mono
#print axioms LevyStochCalc.Poisson.iUnion_Ioc_dyadicLeft
#print axioms LevyStochCalc.Poisson.mem_timeSlab_dyadic
#print axioms LevyStochCalc.Poisson.cast_ceil_pred_div
#print axioms LevyStochCalc.Poisson.stepCount
#print axioms LevyStochCalc.Poisson.strictCount
#print axioms LevyStochCalc.Poisson.markedPredictable_stepCount
#print axioms LevyStochCalc.Poisson.markedPredictable_strictCount
#print axioms LevyStochCalc.Poisson.stepCount_eq
#print axioms LevyStochCalc.Poisson.strictCount_eq
-- ===== Simple integrands and their window sums (A4c-ii-c1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.simpleMark
#print axioms LevyStochCalc.Poisson.measurable_simpleMark
#print axioms LevyStochCalc.Poisson.simpleMark_eq_zero
#print axioms LevyStochCalc.Poisson.ae_setIntegral_simpleMark
#print axioms LevyStochCalc.Poisson.ae_windowSum_simple
#print axioms LevyStochCalc.Poisson.predStrict
#print axioms LevyStochCalc.Poisson.markedPredictable_predStrict
#print axioms LevyStochCalc.Poisson.predStrict_eq
-- ===== The predictable character integrand (A4c-ii-c1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.charIntegrand
#print axioms LevyStochCalc.Poisson.charRe
#print axioms LevyStochCalc.Poisson.charIm
#print axioms LevyStochCalc.Poisson.markedPredictable_charIntegrand
#print axioms LevyStochCalc.Poisson.markedPredictable_charRe
#print axioms LevyStochCalc.Poisson.markedPredictable_charIm
#print axioms LevyStochCalc.Poisson.charIntegrand_eq_zero
#print axioms LevyStochCalc.Poisson.norm_charIntegrand_le
#print axioms LevyStochCalc.Poisson.charRe_eq_zero
#print axioms LevyStochCalc.Poisson.charIm_eq_zero
#print axioms LevyStochCalc.Poisson.lintegral_sq_of_bounded
#print axioms LevyStochCalc.Poisson.sq_charRe
#print axioms LevyStochCalc.Poisson.sq_charIm
#print axioms LevyStochCalc.Poisson.ae_char_sub_one_eq_setIntegral
#print axioms LevyStochCalc.Poisson.measurable_charRe
#print axioms LevyStochCalc.Poisson.measurable_charIm
#print axioms LevyStochCalc.Poisson.setIntegral_complex_split
#print axioms LevyStochCalc.Poisson.integrableOn_charIntegrand
#print axioms LevyStochCalc.Poisson.charIntegrand_re
#print axioms LevyStochCalc.Poisson.charIntegrand_im
#print axioms LevyStochCalc.Poisson.ae_char_sub_one_eq_compensated
-- ===== The window sigma-algebra generates the natural filtration (A4c-ii-d1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.WindowSet
#print axioms LevyStochCalc.Poisson.WindowSet.measurableSet
#print axioms LevyStochCalc.Poisson.WindowSet.subset_Iic
#print axioms LevyStochCalc.Poisson.WindowSet.intensity_ne_top
#print axioms LevyStochCalc.Poisson.windowSigma
#print axioms LevyStochCalc.Poisson.measurable_windowCount
#print axioms LevyStochCalc.Poisson.windowSigma_le_natural
#print axioms LevyStochCalc.Poisson.comap_le_aug_of_ae_eq
#print axioms LevyStochCalc.Poisson.ae_count_ne_top
#print axioms LevyStochCalc.Poisson.windowTrace
#print axioms LevyStochCalc.Poisson.windowTrace_coe
#print axioms LevyStochCalc.Poisson.monotone_windowTrace
#print axioms LevyStochCalc.Poisson.iUnion_windowTrace
#print axioms LevyStochCalc.Poisson.measurable_windowSigma_count
#print axioms LevyStochCalc.Poisson.natural_le_aug_windowSigma
#print axioms LevyStochCalc.Probability.aug_le_of_le_aug
#print axioms LevyStochCalc.Poisson.ae_eq_zero_of_integral_char_windowSigma
#print axioms LevyStochCalc.Poisson.ae_eq_zero_of_integral_char_window
-- ===== Gronwall by iteration (A4c-iii-b1-iv, 2026-09-08) =====
#print axioms LevyStochCalc.Analysis.norm_le_pow_div_factorial_of_norm_le_integral
#print axioms LevyStochCalc.Analysis.eq_zero_of_norm_le_integral
-- ===== The character at an intermediate time (A4c-iii-b1-i, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.truncFam
#print axioms LevyStochCalc.Poisson.measurableSet_truncFam
#print axioms LevyStochCalc.Poisson.truncFam_subset
#print axioms LevyStochCalc.Poisson.truncFam_inter_Ioc
#print axioms LevyStochCalc.Poisson.truncFam_inter_Ioo
#print axioms LevyStochCalc.Poisson.iUnion_truncFam
#print axioms LevyStochCalc.Poisson.simpleMark_truncFam
#print axioms LevyStochCalc.Poisson.predStrict_truncFam
#print axioms LevyStochCalc.Poisson.charAt
#print axioms LevyStochCalc.Poisson.ae_windowSum_truncFam
#print axioms LevyStochCalc.Poisson.ae_charAt_sub_one_eq_integral
-- ===== Orthogonality removes the compensated halves (A4c-iii-b1-ii, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.charCompensator
#print axioms LevyStochCalc.Poisson.norm_charAt_sub_one_le
#print axioms LevyStochCalc.Poisson.measurable_charAt
#print axioms LevyStochCalc.Poisson.integral_mul_charAt_sub_one
-- ===== The character and the strict-past character agree a.s. (A4c-iii-b1-iii-a, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.referenceIntensity_inter_singleton
#print axioms LevyStochCalc.Poisson.ae_count_time_singleton_eq_zero
#print axioms LevyStochCalc.Poisson.inter_Ioc_prod_eq_union
#print axioms LevyStochCalc.Poisson.ae_count_Ioc_eq_count_Ioo
#print axioms LevyStochCalc.Poisson.charStrict
#print axioms LevyStochCalc.Poisson.ae_charAt_eq_charStrict
#print axioms LevyStochCalc.Poisson.exp_predStrict_truncFam
#print axioms LevyStochCalc.Poisson.integral_mul_exp_predStrict
-- ===== Fubini for the compensator (A4c-iii-b1-iii-b, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.charMark
#print axioms LevyStochCalc.Poisson.charIntegrand_truncFam_eq
#print axioms LevyStochCalc.Poisson.norm_charMark_le
#print axioms LevyStochCalc.Poisson.charMark_eq_zero
#print axioms LevyStochCalc.Poisson.integral_mul_charCompensator
-- ===== The character integrand as a horizon integrand (A4c-iii-b, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.charReIntegrand
#print axioms LevyStochCalc.Poisson.charImIntegrand
#print axioms LevyStochCalc.Poisson.charReIntegrand_integral
#print axioms LevyStochCalc.Poisson.charImIntegrand_integral
-- ===== The Grönwall inequality for the pairing (A4c-iii-b1-iii-c, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.charPairing
#print axioms LevyStochCalc.Poisson.integrable_mul_charAt
#print axioms LevyStochCalc.Poisson.norm_charPairing_le
#print axioms LevyStochCalc.Poisson.aestronglyMeasurable_pairing_exp
#print axioms LevyStochCalc.Poisson.aestronglyMeasurable_of_pairing_exp
#print axioms LevyStochCalc.Poisson.aestronglyMeasurable_charPairing
#print axioms LevyStochCalc.Poisson.integrableOn_norm_charPairing
#print axioms LevyStochCalc.Poisson.charPairing_eq_window_integral
#print axioms LevyStochCalc.Poisson.integrableOn_prod_of_time
#print axioms LevyStochCalc.Poisson.setIntegral_prod_of_time
#print axioms LevyStochCalc.Poisson.norm_charPairing_le_integral
-- ===== The pairing with the characters vanishes (A4c-iii-b1-v, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.charPairing_of_forall_eq_empty
#print axioms LevyStochCalc.Poisson.charPairing_eq_zero
-- ===== The predictable representation property of a Poisson random measure (A4c-iii-b2, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.exists_window_of_finset
#print axioms LevyStochCalc.Poisson.ae_eq_zero_of_integral_mul_compensated_eq_zero
#print axioms LevyStochCalc.Poisson.exists_markedHorizonIntegrand_of_le_aug
#print axioms LevyStochCalc.Poisson.exists_markedHorizonIntegrand_natural
#print axioms LevyStochCalc.Poisson.isPoissonFiltration_augFiltration
#print axioms LevyStochCalc.Poisson.exists_markedHorizonIntegrand_augFiltration
-- ===== Product characters of a Lévy driver separate (A4d-i, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.extendZero
#print axioms LevyStochCalc.Driver.extendZero_coe
#print axioms LevyStochCalc.Driver.Finset.sum_toLeft_add_sum_toRight
#print axioms LevyStochCalc.Driver.LevyDriver.jointFamily
#print axioms LevyStochCalc.Driver.LevyDriver.measurable_jointFamily
#print axioms LevyStochCalc.Driver.LevyDriver.jointWindowSigma
#print axioms LevyStochCalc.Driver.LevyDriver.jointWindowSigma_eq_iSup_comap
#print axioms LevyStochCalc.Driver.LevyDriver.jointWindowSigma_le
#print axioms LevyStochCalc.Driver.LevyDriver.filtration_le_aug_jointWindowSigma
#print axioms LevyStochCalc.Driver.LevyDriver.sum_jointFamily_eq
#print axioms LevyStochCalc.Driver.LevyDriver.ae_eq_zero_of_integral_char_jointWindowSigma
#print axioms LevyStochCalc.Driver.LevyDriver.ae_eq_zero_of_integral_char_joint
-- ===== Pulling a past weight inside a compensated integral (A4d-ii-a, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.integrable_mul_of_memLp_two
#print axioms LevyStochCalc.Poisson.Compensated.compensator_eq_zero_of_vanishing
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_vanishing
#print axioms LevyStochCalc.Poisson.Compensated.integral_mul_sq_stochasticIntegral
#print axioms LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_mul_of_vanishing
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_mul_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.mulLeft
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_congr_toFun
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.compensator_mulLeft
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mul_sq_integral
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_mulLeft
-- ===== Freezing at the left endpoints of a dyadic grid (A4d-ii-c, 2026-09-08) =====
#print axioms LevyStochCalc.Analysis.dyadicPartition
#print axioms LevyStochCalc.Analysis.dyadicPartition_strictMono
#print axioms LevyStochCalc.Analysis.leftPt
#print axioms LevyStochCalc.Analysis.leftPt_lt
#print axioms LevyStochCalc.Analysis.le_leftPt_add
#print axioms LevyStochCalc.Analysis.tendsto_leftPt
#print axioms LevyStochCalc.Brownian.Ito.leftFreeze
#print axioms LevyStochCalc.Brownian.Ito.leftFreeze_adapt
#print axioms LevyStochCalc.Brownian.Ito.leftFreeze_eval
#print axioms LevyStochCalc.Brownian.Ito.abs_leftFreeze_eval_le
#print axioms LevyStochCalc.Brownian.Ito.leftFreeze_integralAgainst
#print axioms LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_sub_leftFreeze
-- ===== Sums of finitely many jumps along a dyadic grid (A4d-ii-c, 2026-09-08) =====
#print axioms LevyStochCalc.Analysis.jumpSum
#print axioms LevyStochCalc.Analysis.jumpSumStrict
#print axioms LevyStochCalc.Analysis.jumpSum_sub
#print axioms LevyStochCalc.Analysis.eventually_jumpSum_leftPt
#print axioms LevyStochCalc.Analysis.sum_mul_jumpSum_sub
#print axioms LevyStochCalc.Analysis.tendsto_sum_mul_jumpSum_sub
#print axioms LevyStochCalc.Analysis.setIntegral_Ioc_of_eq_sum_dirac
#print axioms LevyStochCalc.Analysis.setIntegral_Ioo_of_eq_sum_dirac
-- ===== The product rule for a continuous Itô process and a pure-jump process (A4d-ii-d, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.telescope_dyadic
#print axioms LevyStochCalc.Driver.sum_mul_setIntegral_eq_integral_leftFreeze
#print axioms LevyStochCalc.Driver.tendsto_integral_leftFreeze_mul
#print axioms LevyStochCalc.Driver.product_rule_core
#print axioms LevyStochCalc.Driver.setIntegral_Ioc_eq_jumpSum
#print axioms LevyStochCalc.Driver.setIntegral_Ioo_eq_jumpSumStrict
#print axioms LevyStochCalc.Driver.tendsto_eLpNorm_two_of_tendsto_lintegral_sq
#print axioms LevyStochCalc.Driver.product_rule
-- ===== The jump chain rule at all times simultaneously (A4d-ii-b, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.exp_windowSum_sub_one_of_repr
#print axioms LevyStochCalc.Poisson.restrict_eq_sum_dirac_of_subset
#print axioms LevyStochCalc.Poisson.ae_forall_exp_windowSum_sub_one
-- ===== Trigonometric functions of a Brownian increment are Itô processes (A4d-ii-b, 2026-09-08) =====
#print axioms LevyStochCalc.Brownian.Ito.trigDriftCell
#print axioms LevyStochCalc.Brownian.Ito.abs_trigDriftCell_le
#print axioms LevyStochCalc.Brownian.Ito.measurable_trigDriftCell
#print axioms LevyStochCalc.Brownian.Ito.progressivelyMeasurable_trigDriftCell
#print axioms LevyStochCalc.Brownian.Ito.isItoVersion_trig
-- ===== The character of a window family as a pure-jump process (A4d-ii-e-1, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.charJump
#print axioms LevyStochCalc.Poisson.norm_charJump_le
#print axioms LevyStochCalc.Poisson.stronglyMeasurable_charAt
#print axioms LevyStochCalc.Poisson.ae_forall_charAt_sub
-- ===== A continuous adapted process is marked predictable on a window (A4d-ii-e-2, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.stepEval
#print axioms LevyStochCalc.Probability.markedPredictable_stepEval
#print axioms LevyStochCalc.Probability.stepEval_eq
#print axioms LevyStochCalc.Probability.stepEvalCut
#print axioms LevyStochCalc.Probability.markedPredictable_stepEvalCut
#print axioms LevyStochCalc.Probability.markedPredictable_of_continuous_adapted
-- ===== A continuous adapted factor in a marked integrand (A4d-ii-e-3, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.Compensated.cutWindow
#print axioms LevyStochCalc.Poisson.Compensated.cutWindow_eq
#print axioms LevyStochCalc.Poisson.Compensated.abs_cutWindow_le
#print axioms LevyStochCalc.Poisson.Compensated.measurable_uncurry_cutWindow
#print axioms LevyStochCalc.Poisson.Compensated.markedEnergy_bddMul_ne_top
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.markedPredictable_cutMul
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.cutMul
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.setIntegral_count_eq_integral_add
-- ===== The predictable weight of the character's jumps (A4d-ii-e-4-a, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.ae_forall_charStrict_sub
#print axioms LevyStochCalc.Poisson.ae_forall_setIntegral_charJump_eq
#print axioms LevyStochCalc.Poisson.ae_forall_charAt_sub_pred
#print axioms LevyStochCalc.Poisson.ae_forall_charStrict_sub_pred
#print axioms LevyStochCalc.Poisson.charAt_zero
#print axioms LevyStochCalc.Poisson.charStrict_zero
#print axioms LevyStochCalc.Poisson.norm_charAt
#print axioms LevyStochCalc.Poisson.norm_charStrict
#print axioms LevyStochCalc.Poisson.abs_charAt_re_le
#print axioms LevyStochCalc.Poisson.abs_charAt_im_le
#print axioms LevyStochCalc.Poisson.abs_charStrict_re_le
#print axioms LevyStochCalc.Poisson.abs_charStrict_im_le
#print axioms LevyStochCalc.Poisson.ae_forall_charAt_re_im_sub
#print axioms LevyStochCalc.Poisson.ae_forall_charStrict_re_im_sub
-- ===== The strict-past character as a progressive process (A4d-ii-e-4-a, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.progressivelyMeasurable_eval_mark
#print axioms LevyStochCalc.Poisson.progressivelyMeasurable_comp_min
#print axioms LevyStochCalc.Poisson.charStrictPred
#print axioms LevyStochCalc.Poisson.predStrict_of_nonpos
#print axioms LevyStochCalc.Poisson.charStrictPred_eq
#print axioms LevyStochCalc.Poisson.norm_charStrictPred
#print axioms LevyStochCalc.Poisson.abs_charStrictPred_re_le
#print axioms LevyStochCalc.Poisson.abs_charStrictPred_im_le
#print axioms LevyStochCalc.Poisson.measurable_uncurry_charStrictPred
#print axioms LevyStochCalc.Poisson.exp_I_mul_ofReal_re
#print axioms LevyStochCalc.Poisson.exp_I_mul_ofReal_im
#print axioms LevyStochCalc.Poisson.progressivelyMeasurable_const'
#print axioms LevyStochCalc.Poisson.progressivelyMeasurable_charStrictPred_re
#print axioms LevyStochCalc.Poisson.progressivelyMeasurable_charStrictPred_im
-- ===== Pairing the terms of the product rule (A4d-ii-e-4-b, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.integrable_mul_bdd_mul
#print axioms LevyStochCalc.Driver.integral_mul_setIntegral_count
#print axioms LevyStochCalc.Driver.integral_mul_stochasticIntegralBrownian_eq_zero
#print axioms LevyStochCalc.Driver.pairing_of_product_rule
#print axioms LevyStochCalc.Poisson.Compensated.cutWindow_eq_zero
#print axioms LevyStochCalc.Poisson.Compensated.setIntegral_eq_of_vanishing
-- ===== Pairing the product rule on a cell (A4d-ii-e-4-b/c, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.window_inter_Ioc
#print axioms LevyStochCalc.Driver.hid_cell
#print axioms LevyStochCalc.Driver.paired_cell_char
#print axioms LevyStochCalc.Poisson.charIntegrand_eq_zero_of_notMem
#print axioms LevyStochCalc.Poisson.charRe_eq_zero_of_le
#print axioms LevyStochCalc.Poisson.charIm_eq_zero_of_le
#print axioms LevyStochCalc.Poisson.abs_charRe_le
#print axioms LevyStochCalc.Poisson.abs_charIm_le
#print axioms LevyStochCalc.Driver.paired_cell_re
#print axioms LevyStochCalc.Driver.paired_cell_im
-- ===== Fubini on the surviving terms of the cell identity (A4d-ii-e-4-c-2, 2026-09-08) =====
#print axioms LevyStochCalc.Poisson.markFactor
#print axioms LevyStochCalc.Poisson.charIntegrand_eq_markFactor_mul
#print axioms LevyStochCalc.Poisson.norm_markFactor_le
#print axioms LevyStochCalc.Poisson.measurable_markFactor
#print axioms LevyStochCalc.Poisson.ae_exp_predStrict_eq_charAt
#print axioms LevyStochCalc.Poisson.ae_charStrictPred_eq_charAt
#print axioms LevyStochCalc.Poisson.integral_mul_charIntegrand
#print axioms LevyStochCalc.Probability.integral_mul_setIntegral_swap
#print axioms LevyStochCalc.Driver.integral_mul_setIntegral_drift
#print axioms LevyStochCalc.Driver.integral_mul_setIntegral_jump
#print axioms LevyStochCalc.Driver.integral_mul_trigDriftCell
-- ===== The complex pairing with the cell character (A4d-ii-e-4-c-3-a, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.memLp_two_of_bound
#print axioms LevyStochCalc.Driver.cellPart
#print axioms LevyStochCalc.Driver.integrable_cellPart
#print axioms LevyStochCalc.Driver.cellPairing
#print axioms LevyStochCalc.Driver.cellPairing_eq_parts
-- ===== The cell identity in the recombination's form (A4d-ii-e-4-c-3-b, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.cellDrift
#print axioms LevyStochCalc.Driver.abs_cellDrift_le
#print axioms LevyStochCalc.Driver.cellPart_of_paired
#print axioms LevyStochCalc.Driver.cellPart_identity_re
#print axioms LevyStochCalc.Driver.cellPart_identity_im
-- ===== The complex combination of the cell identity (A4d-ii-e-4-c-3-c, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.cellHalf
#print axioms LevyStochCalc.Driver.integrable_weight
#print axioms LevyStochCalc.Driver.cellPart_eq_cellHalf_re
#print axioms LevyStochCalc.Driver.cellPart_eq_cellHalf_im
#print axioms LevyStochCalc.Driver.cellPairing_eq_halves
#print axioms LevyStochCalc.Driver.integral_mul_charRe_eq
#print axioms LevyStochCalc.Driver.integral_mul_charIm_eq
#print axioms LevyStochCalc.Driver.norm_cellHalf_le
#print axioms LevyStochCalc.Driver.aestronglyMeasurable_cellHalf
#print axioms LevyStochCalc.Driver.integrableOn_cellHalf
#print axioms LevyStochCalc.Driver.integrableOn_prod_of_time_complex
#print axioms LevyStochCalc.Driver.cellHalf_identity
#print axioms LevyStochCalc.Driver.cellPairing_identity
-- ===== The Gronwall bound for the cell pairing (A4d-ii-e-4-c-3-d, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.norm_cellPairing_le
-- ===== The mixed cell lemma (A4d-ii-f, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.cellPairing_zero
#print axioms LevyStochCalc.Driver.norm_cellPairing_bound
#print axioms LevyStochCalc.Driver.cellPairing_eq_zero
-- ===== The cell lemma for a complex factor (A4d-iii-a, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.cellPairingC
#print axioms LevyStochCalc.Driver.norm_cellFactor
#print axioms LevyStochCalc.Driver.integrable_cellFactor
#print axioms LevyStochCalc.Driver.cellPairingC_eq_parts
#print axioms LevyStochCalc.Driver.integral_re_im_eq_zero
#print axioms LevyStochCalc.Driver.cellPairingC_eq_zero
#print axioms LevyStochCalc.Driver.pairing_cell_joint_eq_zero
-- ===== The joint character of a grid of cells (A4d-iii-b, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.cellFam
#print axioms LevyStochCalc.Driver.measurableSet_cellFam
#print axioms LevyStochCalc.Driver.cellFam_subset
#print axioms LevyStochCalc.Driver.cellFam_inter_Ioc
#print axioms LevyStochCalc.Driver.count_inter_Ioc_sum
#print axioms LevyStochCalc.Driver.grid_nonneg
#print axioms LevyStochCalc.Driver.ae_charAt_eq_prod_cellFam
#print axioms LevyStochCalc.Driver.jointGridCharacter
#print axioms LevyStochCalc.Driver.norm_jointGridCharacter
#print axioms LevyStochCalc.Driver.measurable_jointGridCharacter
-- ===== The joint grid induction (A4d-iii-c, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.pairing_jointGridCharacter_eq_zero
#print axioms LevyStochCalc.Driver.pairing_joint_value_character_eq_zero
-- ===== The joint filtration and its augmentation (A4d-iv-a, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.LevyDriver.isBrownianFiltration_combineBM
#print axioms LevyStochCalc.Driver.LevyDriver.isBrownianFiltration_aug
#print axioms LevyStochCalc.Driver.LevyDriver.isBrownianFiltration_combineBM_aug
#print axioms LevyStochCalc.Driver.LevyDriver.isPoissonFiltration_aug
#print axioms LevyStochCalc.Driver.LevyDriver.augFiltration_le_of_nonpos
#print axioms LevyStochCalc.Driver.LevyDriver.measurableSet_augFiltration_of_null
-- ===== The multidimensional joint cell lemma (A4d-iv-b-1, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.pairing_cell_multidim_joint_eq_zero
-- ===== The multidimensional joint grid (A4d-iv-b-2, 2026-09-08) =====
#print axioms LevyStochCalc.Driver.jointGridCharacterMultidim
#print axioms LevyStochCalc.Driver.norm_jointGridCharacterMultidim
#print axioms LevyStochCalc.Driver.measurable_jointGridCharacterMultidim
#print axioms LevyStochCalc.Driver.pairing_jointGridCharacterMultidim_eq_zero
#print axioms LevyStochCalc.Driver.pairing_joint_value_characterMultidim_eq_zero
-- ===== Grids over a superset of the cylinder times (A4d-iv-b-3-a, 2026-09-08) =====
#print axioms LevyStochCalc.Analysis.sum_weight_eq_sum_grid
#print axioms LevyStochCalc.Analysis.le_sortedGrid_card
-- ===== The marked perp bridge (A4d-iv-b-3-a2, 2026-09-08) =====
#print axioms LevyStochCalc.Probability.MarkedProgressivelyMeasurable.indicator_time
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_congr
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.clip
#print axioms LevyStochCalc.Poisson.Compensated.MarkedHorizonIntegrand.integral_clip
#print axioms LevyStochCalc.Poisson.Compensated.integral_mul_increment_eq_zero
#print axioms LevyStochCalc.Poisson.Compensated.integral_mul_integral_eq_zero
-- ===== The joint cylinder characters and the complement (A4d-iv-b-3-b, 2026-09-09) =====
#print axioms LevyStochCalc.Analysis.le_of_mem_posTimes
#print axioms LevyStochCalc.Analysis.sortedGrid_card_mem
#print axioms LevyStochCalc.Driver.markSet
#print axioms LevyStochCalc.Driver.measurableSet_markSet
#print axioms LevyStochCalc.Driver.markSet_ne_top
#print axioms LevyStochCalc.Driver.subset_markSet
#print axioms LevyStochCalc.Driver.markUnion
#print axioms LevyStochCalc.Driver.measurableSet_markUnion
#print axioms LevyStochCalc.Driver.markUnion_ne_top
#print axioms LevyStochCalc.Driver.markSet_subset_markUnion
#print axioms LevyStochCalc.Driver.mem_markUnion
#print axioms LevyStochCalc.Driver.pairing_char_joint_eq_zero
#print axioms LevyStochCalc.Driver.ae_eq_zero_of_perp_joint
-- ===== Cross orthogonality of the two ranges (A4d-v-a, 2026-09-09) =====
#print axioms LevyStochCalc.Driver.LevyDriver.crossPoissonFiltration
#print axioms LevyStochCalc.Driver.LevyDriver.crossPoissonFiltration_apply
#print axioms LevyStochCalc.Driver.LevyDriver.filtration_le_crossPoisson
#print axioms LevyStochCalc.Driver.LevyDriver.isPoissonFiltration_crossPoisson
#print axioms LevyStochCalc.Driver.LevyDriver.measurable_increment_crossPoisson
#print axioms LevyStochCalc.Driver.LevyDriver.crossBrownianFiltration
#print axioms LevyStochCalc.Driver.LevyDriver.crossBrownianFiltration_apply
#print axioms LevyStochCalc.Driver.LevyDriver.filtration_le_crossBrownian
#print axioms LevyStochCalc.Driver.LevyDriver.isBrownianFiltration_crossBrownian
#print axioms LevyStochCalc.Driver.LevyDriver.stronglyMeasurable_compensated_crossBrownian
#print axioms LevyStochCalc.Driver.LevyDriver.CrossWitness
#print axioms LevyStochCalc.Driver.LevyDriver.crossWitness
#print axioms LevyStochCalc.Driver.LevyDriver.CrossWitness.aug
#print axioms LevyStochCalc.Driver.LevyDriver.integral_cross_term_eq_zero_of_le
#print axioms LevyStochCalc.Driver.LevyDriver.integral_cross_term_eq_zero_of_ge
#print axioms LevyStochCalc.Driver.LevyDriver.integral_cross_term_eq_zero
#print axioms LevyStochCalc.Driver.LevyDriver.integrable_cross_term
#print axioms LevyStochCalc.Driver.LevyDriver.integrable_and_integral_cross_clamped
#print axioms LevyStochCalc.Driver.LevyDriver.integral_simpleIntegral_mul_markStep_eq_zero
#print axioms LevyStochCalc.Driver.LevyDriver.integral_stochasticIntegral_mul_compensated_eq_zero
-- ===== The joint range and its decomposition (A4d-v-b, 2026-09-09) =====
#print axioms LevyStochCalc.Driver.LevyDriver.coordCrossFiltration
#print axioms LevyStochCalc.Driver.LevyDriver.crossFiltration_le_iSup_sigmaBrownian
#print axioms LevyStochCalc.Driver.LevyDriver.isBrownianFiltration_coordCross
#print axioms LevyStochCalc.Driver.LevyDriver.coordCrossWitness
#print axioms LevyStochCalc.Driver.LevyDriver.jointRange
#print axioms LevyStochCalc.Driver.LevyDriver.inner_itoRange_compensatedRange
#print axioms LevyStochCalc.Driver.LevyDriver.orthogonalFamily_jointRange
#print axioms LevyStochCalc.Driver.LevyDriver.isClosed_iSup_jointRange
#print axioms LevyStochCalc.Driver.LevyDriver.jointIntegral
#print axioms LevyStochCalc.Driver.LevyDriver.memLp_jointIntegral
#print axioms LevyStochCalc.Driver.LevyDriver.integral_jointIntegral_eq_zero
#print axioms LevyStochCalc.Driver.LevyDriver.aestronglyMeasurable_jointIntegral
#print axioms LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_of_mean_zero
-- ===== The predictable representation property of a Levy driver (A4d-vi, 2026-09-09) =====
#print axioms LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration
-- ===== The degenerate cases of the joint representation (A4d-vii, 2026-09-09) =====
#print axioms LevyStochCalc.Driver.LevyDriver.naturalFiltration_poisson_eq_bot
#print axioms LevyStochCalc.Driver.LevyDriver.naturalFiltration_brownian_eq_bot
#print axioms LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration_of_dim_zero
#print axioms LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration_of_isEmpty
#print axioms LevyStochCalc.Driver.LevyDriver.exists_jointIntegral_augFiltration_of_mean_zero
-- ===== Predictable representatives of progressive integrands (A5b, 2026-09-09) =====
#print axioms LevyStochCalc.Probability.measurableSet_predictableSigma_Iic_univ
#print axioms LevyStochCalc.Probability.measurableSet_predictableSigma_Ioc_prod
#print axioms LevyStochCalc.Probability.measurableSet_predictableSigma_compl_Ioc
#print axioms LevyStochCalc.Probability.measurable_predictableSigma_cell
#print axioms LevyStochCalc.Probability.predictable_simpleEval
#print axioms LevyStochCalc.Probability.Predictable.limsup
#print axioms LevyStochCalc.Probability.limsupSimpleEval
#print axioms LevyStochCalc.Probability.exists_predictable_ae_eq
#print axioms LevyStochCalc.Probability.exists_predictable_ae_eq_horizonIntegrand
-- ===== Predictable representatives of marked integrands (A5b, marked half, 2026-09-09) =====
#print axioms LevyStochCalc.Probability.markedPredictable_markStepEval
#print axioms LevyStochCalc.Probability.MarkedPredictable.limsup
#print axioms LevyStochCalc.Probability.limsupMarkStepEval
#print axioms LevyStochCalc.Probability.exists_markedPredictable_ae_eq
#print axioms LevyStochCalc.Probability.exists_markedPredictable_ae_eq_markedHorizonIntegrand
-- ===== Admissible integrands have predictable versions (A5b capstone, 2026-09-09) =====
#print axioms LevyStochCalc.Brownian.Ito.predictableSigma_le
#print axioms LevyStochCalc.Brownian.Ito.measurable_uncurry_of_predictable
#print axioms LevyStochCalc.Brownian.Ito.predictable_indicator_Ioc
#print axioms LevyStochCalc.Brownian.Ito.ae_mem_Ioc_energyMeasure
#print axioms LevyStochCalc.Brownian.Ito.exists_predictable_horizonIntegrand
#print axioms LevyStochCalc.Poisson.Compensated.measurableSet_markedPredictable_strip
#print axioms LevyStochCalc.Poisson.Compensated.markedPredictable_indicator_Ioc
#print axioms LevyStochCalc.Poisson.Compensated.ae_mem_Ioc_markedEnergyMeasure
#print axioms LevyStochCalc.Poisson.Compensated.exists_markedPredictable_markedHorizonIntegrand
-- ===== The joint representation with predictable integrands (A5c input, 2026-09-09) =====
#print axioms LevyStochCalc.Driver.LevyDriver.exists_predictable_jointIntegral
-- ===== The X_{s-} convention: class identification and cadlag jumps (B0b, 2026-09-09) =====
#print axioms LevyStochCalc.Poisson.Compensated.stochasticIntegral_congr_ae
#print axioms LevyStochCalc.Analysis.abs_leftLim_sub_le
#print axioms LevyStochCalc.Analysis.exists_isolating_radius
#print axioms LevyStochCalc.Analysis.countable_setOf_ne_leftLim
#print axioms LevyStochCalc.Analysis.ae_eq_leftLim_of_cadlag
-- ===== The Ito-Levy process interface (B0a, 2026-09-09) =====
#print axioms LevyStochCalc.Ito.Setting.IsItoLevyProcess
#print axioms LevyStochCalc.Ito.Setting.JumpDiffusion.exists_isItoLevyProcess
