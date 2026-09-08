/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.Joint
import LevyStochCalc.Brownian.LinearCombination
import LevyStochCalc.Brownian.AugmentedFiltration
import LevyStochCalc.Poisson.PredictableRepresentation

/-!
# The joint filtration of a Lévy driver, and its augmentation

Every unit combination of the driver's Brownian coordinates is a Brownian motion for the joint
filtration, and the `0`-clamped augmentation of that filtration carries all of the driver at
once: every coordinate, every unit combination, and the Poisson random measure.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν]

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Multidim

/-- **Every unit combination is a Brownian motion for the joint filtration.** -/
theorem isBrownianFiltration_combineBM {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1) :
    Brownian.IsBrownianFiltration (MultidimBrownianMotion.combineBM D.W hc) D.filtration :=
  (MultidimBrownianMotion.isBrownianFiltration_combineBM D.W hc).of_le_sup
    (fun t => ((MultidimBrownianMotion.isBrownianFiltration_combineBM D.W hc).measurable t).mono
      (D.naturalFiltration_brownian_le t) le_rfl)
    (m := fun s => Poisson.naturalFiltration D.N s) (fun s => (Poisson.naturalFiltration D.N).le s)
    (fun s => (D.filtration_apply s).le)
    (fun s t _ _ => indep_of_indep_of_le_right
      (indep_of_indep_of_le_left D.indep.symm (naturalFiltration_le_sigmaPoisson _ s))
      (sup_le (D.W.naturalFiltration_le_iSup_sigmaBrownian s)
        ((MultidimBrownianMotion.comap_combine_sub_le D.W c s t).trans
          (iSup_le fun i => (Brownian.comap_increment_le_sigmaBrownian (D.W.W i) s t).trans
            (le_iSup (fun j => Brownian.sigmaBrownian (D.W.W j)) i)))))

/-- Every coordinate is a Brownian motion for the augmented joint filtration. -/
theorem isBrownianFiltration_aug (j : Fin d) :
    Brownian.IsBrownianFiltration (D.W.W j) (Brownian.augFiltration D.filtration P) :=
  Brownian.isBrownianFiltration_augFiltration (D.isBrownianFiltration j)

/-- Every unit combination is a Brownian motion for the augmented joint filtration. -/
theorem isBrownianFiltration_combineBM_aug {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1) :
    Brownian.IsBrownianFiltration (MultidimBrownianMotion.combineBM D.W hc)
      (Brownian.augFiltration D.filtration P) :=
  Brownian.isBrownianFiltration_augFiltration (D.isBrownianFiltration_combineBM hc)

/-- The Poisson random measure is one for the augmented joint filtration. -/
theorem isPoissonFiltration_aug :
    Poisson.IsPoissonFiltration D.N (Brownian.augFiltration D.filtration P) :=
  Poisson.isPoissonFiltration_augFiltration D.isPoissonFiltration

/-- The augmented joint filtration is constant on the nonpositive times. -/
theorem augFiltration_le_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    Brownian.augFiltration D.filtration P 0 ≤ Brownian.augFiltration D.filtration P t :=
  le_of_eq (Brownian.augFiltration_of_nonpos D.filtration P ht).symm

/-- The augmented joint filtration contains the null sets at time `0`. -/
theorem measurableSet_augFiltration_of_null {s : Set Ω} (hs : MeasurableSet s) (h0 : P s = 0) :
    MeasurableSet[Brownian.augFiltration D.filtration P 0] s :=
  Brownian.measurableSet_augFiltration_of_null D.filtration P hs h0

end LevyDriver

end LevyStochCalc.Driver
