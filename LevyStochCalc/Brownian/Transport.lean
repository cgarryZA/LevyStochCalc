/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Multidim
import LevyStochCalc.Probability.Transport

/-!
# Brownian motion along a measure-preserving map

If `h : Ω' → Ω` is measure preserving from `P'` to `P` and `W` is a Brownian motion on
`(Ω, P)`, then `(t, ω') ↦ W_t (h ω')` is a Brownian motion on `(Ω', P')`, and likewise
for a `d`-dimensional Brownian motion. The two projections of a product probability
space are measure preserving, so this is how a Brownian motion and an independent
Poisson random measure are put on one space (`LevyStochCalc/Driver/Existence.lean`).
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {Ω' : Type u} [MeasurableSpace Ω']
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {d : ℕ}

/-- The Brownian motion `(t, ω') ↦ W_t (h ω')` obtained by pulling `W` back along a
measure-preserving map `h`. -/
noncomputable def BrownianMotion.comap (W : BrownianMotion P) {h : Ω' → Ω}
    (hmp : MeasurePreserving h P' P) : BrownianMotion P' where
  W := fun t ω' => W.W t (h ω')
  measurable_eval t := (W.measurable_eval t).comp hmp.measurable
  joint_measurable :=
    W.joint_measurable.comp (measurable_fst.prodMk (hmp.measurable.comp measurable_snd))
  initial_zero := hmp.quasiMeasurePreserving.ae W.initial_zero
  increment_gaussian := by
    intro s t hs hst
    have hmeas : Measurable (fun ω => W.W t ω - W.W s ω) :=
      (W.measurable_eval t).sub (W.measurable_eval s)
    rw [show (fun ω' => W.W t (h ω') - W.W s (h ω'))
        = (fun ω => W.W t ω - W.W s ω) ∘ h from rfl,
      ← Measure.map_map hmeas hmp.measurable, hmp.map_eq]
    exact W.increment_gaussian hs hst
  increment_independent := by
    intro u s t hu hus hst
    exact Probability.indepFun_comp_of_measurePreserving (W.measurable_eval u)
      ((W.measurable_eval t).sub (W.measurable_eval s))
      (W.increment_independent hu hus hst) hmp
  continuous_paths := hmp.quasiMeasurePreserving.ae W.continuous_paths
  negative_zero s hs := hmp.quasiMeasurePreserving.ae (W.negative_zero s hs)
  joint_increment_independent := by
    intro s t hs hst
    have key := Probability.indep_comap_of_measurePreserving hmp
      (m₁ := ⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W.W j) inferInstance)
      (m₂ := MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance)
      (iSup₂_le fun j _ => (W.measurable_eval j).comap_le)
      ((W.measurable_eval t).sub (W.measurable_eval s)).comap_le
      (W.joint_increment_independent hs hst)
    simpa only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]
      using key

@[simp]
lemma BrownianMotion.comap_apply (W : BrownianMotion P) {h : Ω' → Ω}
    (hmp : MeasurePreserving h P' P) (t : ℝ) (ω' : Ω') :
    (W.comap hmp).W t ω' = W.W t (h ω') := rfl

/-- The `d`-dimensional Brownian motion obtained by pulling `W` back along a
measure-preserving map, coordinatewise. -/
noncomputable def Multidim.MultidimBrownianMotion.comap
    (W : Multidim.MultidimBrownianMotion P d) {h : Ω' → Ω}
    (hmp : MeasurePreserving h P' P) : Multidim.MultidimBrownianMotion P' d where
  W := fun i => (W.W i).comap hmp
  components_independent :=
    Probability.iIndepFun_comp_of_measurePreserving
      (fun i => measurable_pi_lambda _ fun t => (W.W i).measurable_eval t)
      W.components_independent hmp
  joint_continuous_paths := hmp.quasiMeasurePreserving.ae W.joint_continuous_paths

@[simp]
lemma Multidim.MultidimBrownianMotion.comap_apply
    (W : Multidim.MultidimBrownianMotion P d) {h : Ω' → Ω}
    (hmp : MeasurePreserving h P' P) (i : Fin d) (t : ℝ) (ω' : Ω') :
    ((W.comap hmp).W i).W t ω' = (W.W i).W t (h ω') := rfl

end LevyStochCalc.Brownian
