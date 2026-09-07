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
-- Ex-Tier-1-axiom #14 chain (axiom→theorem 2026-05-26; wrap-up carries the
-- single explicit baseline `sorry` for the entire Picard chain):
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
