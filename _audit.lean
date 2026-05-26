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
#print axioms LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.joint_increment_gaussian_diagonal
-- 1.5e: L² Itô integral against W
#print axioms LevyStochCalc.Brownian.Ito.itoIsometry
#print axioms LevyStochCalc.Brownian.Ito.quadVar_stochasticIntegral
#print axioms LevyStochCalc.Brownian.Ito.martingale_stochasticIntegral

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
-- σ-side L² Lipschitz bound (Agent 1, PicardSigmaLipschitz.lean; depends on
-- new Tier 1 axiom itoIsometry_diff_brownian for stochastic-integral linearity):
#print axioms LevyStochCalc.Ito.Picard.picardStep_diffusion_diff_lipschitz_sq_componentwise
#print axioms LevyStochCalc.Brownian.Ito.itoIsometry_diff_brownian
-- γ-side L² Lipschitz bound (Agent 2, PicardGammaLipschitz.lean; depends on
-- new Tier 1 axiom itoIsometry_diff_compensated for compensated-Poisson
-- stochastic-integral linearity — added 2026-05-23 to drop bundled `h_lin`):
#print axioms LevyStochCalc.Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise
#print axioms LevyStochCalc.Poisson.Compensated.itoIsometry_diff_compensated
-- Bielecki β-norm contraction assembly (Agent 3, PicardContraction.lean):
#print axioms LevyStochCalc.Ito.Picard.sq_add_three_le
#print axioms LevyStochCalc.Ito.Picard.sum_sq_add_three_le
#print axioms LevyStochCalc.Ito.Picard.picardStep_diff_sum_sq_le
#print axioms LevyStochCalc.Ito.Picard.picardStep_diff_lintegral_sum_sq_le
#print axioms LevyStochCalc.Ito.Picard.picardStep_bielecki_contraction
#print axioms LevyStochCalc.Ito.Picard.picardStep_bielecki_contraction_rate_lt_one
#print axioms LevyStochCalc.Ito.JumpFormula.itoLevyFormula

-- ===== Layer 3 (+ 3a): BSDEJ existence (→ deaxiomatises Cu01) =====
-- 2026-05-26: axiom #13 decomposed into two narrower Tier 1 sub-axioms
-- (#13a = PRP for càdlàg L² (W, N)-martingales; #13b = condExp-to-PRP bridge).
-- The previously-monolithic `jacodYor_representation_axiom` is now a derived
-- THEOREM forwarding through the pair; the public `jacodYor_representation`
-- thin-forwarder is unchanged.
#print axioms LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_PRP_martingale_axiom
#print axioms LevyStochCalc.BSDEJ.MartingaleRepresentation.condExp_to_PRP_martingale_form_axiom
#print axioms LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation_axiom
#print axioms LevyStochCalc.BSDEJ.MartingaleRepresentation.jacodYor_representation
#print axioms LevyStochCalc.BSDEJ.Existence.continuousBSDEJ_exists_unique

-- ===== Layer 4: BSDEJ path regularity (→ deaxiomatises Cu05) =====
#print axioms LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity
-- Public-API specialization (linear-in-Δt rate; added 2026-05-24) — extracts
-- the BET 2008 bound in the user-facing form `∃ C : ℝ, 0 < C ∧ bound ≤ C · Δt`.
-- Used by downstream chapters that need `ψ(h) := C · h`, notably the parked
-- `Dissertation/BSDE/Discrete/DiscretizationConvergence.lean`.
#print axioms LevyStochCalc.BSDEJ.PathRegularity.bsdej_path_regularity_linear_rate
