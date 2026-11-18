/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.AugmentedFiltration
import LevyStochCalc.Brownian.MultidimFiltered

/-!
# The Brownian filtration with initial information

For a multidimensional Brownian motion `W` and a σ-algebra `𝒢₀`, the filtration
`𝒢₀ ⊔ σ(W_s : s ≤ t)` reveals `𝒢₀` at time `0` and then the path of `W`. If `𝒢₀` is independent of
the whole natural filtration of `W`, every coordinate of `W` is a Brownian motion for this
filtration and for its augmentation by the null sets, the filtration of a Brownian motion started
from random initial data.

## Main definitions

* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.initialFiltration`: the filtration
  `t ↦ 𝒢₀ ⊔ ℱ^W_t`.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.augInitialFiltration`: its
  augmentation by the null sets.

## Main statements

* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.isBrownianFiltration_initialFiltration`
  and `isBrownianFiltration_augInitial`: each coordinate is a Brownian motion for it and for its
  augmentation.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

universe u

-- `𝒢₀` precedes the ambient instance so that instance resolution keeps finding the ambient one.
variable {Ω : Type u} (𝒢₀ : MeasurableSpace Ω) [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {d : ℕ}

/-- The natural filtration of `W` joined at every time with the σ-algebra `𝒢₀`. -/
noncomputable def initialFiltration (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) : Filtration ℝ ‹MeasurableSpace Ω› where
  seq s := 𝒢₀ ⊔ W.naturalFiltration s
  mono' _ _ hst := sup_le_sup_left (W.naturalFiltration.mono hst) _
  le' s := sup_le h𝒢₀ (W.naturalFiltration.le s)

/-- The augmentation by the `P`-null sets of `𝒢₀ ⊔ ℱ^W`, frozen before time `0`. -/
noncomputable abbrev augInitialFiltration (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) : Filtration ℝ ‹MeasurableSpace Ω› :=
  augFiltration (W.initialFiltration 𝒢₀ h𝒢₀) P

variable {𝒢₀} (W : MultidimBrownianMotion P d) (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›)

theorem initialFiltration_apply (s : ℝ) :
    W.initialFiltration 𝒢₀ h𝒢₀ s = 𝒢₀ ⊔ W.naturalFiltration s := rfl

/-- At a time `t ≥ 0` the augmented filtration is the augmentation of `𝒢₀ ⊔ ℱ^W_t`. -/
theorem augFiltration_initialFiltration_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    augFiltration (W.initialFiltration 𝒢₀ h𝒢₀) P t
      = Probability.aug (𝒢₀ ⊔ W.naturalFiltration t) ‹MeasurableSpace Ω› P := by
  change Probability.aug (W.initialFiltration 𝒢₀ h𝒢₀ (max t 0)) ‹MeasurableSpace Ω› P = _
  rw [max_eq_left ht, initialFiltration_apply]

/-- `𝒢₀` is revealed at time `0`. -/
theorem le_augFiltration_initialFiltration (t : ℝ) :
    𝒢₀ ≤ augFiltration (W.initialFiltration 𝒢₀ h𝒢₀) P t :=
  le_sup_left.trans (le_augFiltration (W.initialFiltration 𝒢₀ h𝒢₀) P t)

/-- The augmented natural filtration sits below the augmented filtration with initial
information. -/
theorem augFiltration_natural_le_initial (t : ℝ) :
    augFiltration W.naturalFiltration P t ≤ augFiltration (W.initialFiltration 𝒢₀ h𝒢₀) P t :=
  Probability.aug_mono (le_sup_right (a := 𝒢₀))

/-- **The coordinates stay Brownian under independent initial information.** If `𝒢₀` is
independent of the natural filtration of `W`, every coordinate of `W` is a Brownian motion for
`𝒢₀ ⊔ ℱ^W`. -/
theorem isBrownianFiltration_initialFiltration
    (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P) (j : Fin d) :
    IsBrownianFiltration (W.W j) (W.initialFiltration 𝒢₀ h𝒢₀) := by
  have hB := W.isBrownianFiltration_natural j
  refine hB.of_le_sup (fun t => (hB.measurable t).mono le_sup_right le_rfl)
    (m := fun _ => 𝒢₀) (fun _ => h𝒢₀) (fun s => (sup_comm _ _).le) ?_
  intro s _
  refine indep_of_indep_of_le_right hind (sup_le (le_iSup (fun t => W.naturalFiltration t) s)
    (iSup₂_le fun t hst => ?_))
  have hmeas : Measurable[W.naturalFiltration t] fun ω => (W.W j).W t ω - (W.W j).W s ω :=
    (hB.measurable t).sub ((hB.measurable s).mono (W.naturalFiltration.mono
      (le_of_lt (Set.mem_Ioi.mp hst))) le_rfl)
  exact hmeas.comap_le.trans (le_iSup (fun t => W.naturalFiltration t) t)

/-- Every coordinate of `W` is a Brownian motion for the augmentation of `𝒢₀ ⊔ ℱ^W`. -/
theorem isBrownianFiltration_augInitial (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P)
    (j : Fin d) :
    IsBrownianFiltration (W.W j) (W.augInitialFiltration 𝒢₀ h𝒢₀) :=
  isBrownianFiltration_augFiltration (W.isBrownianFiltration_initialFiltration h𝒢₀ hind j)

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
