/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Martingale
import LevyStochCalc.Probability.IndepJoin
import LevyStochCalc.Probability.IndepLimit

/-!
# Brownian motion with respect to a filtration

`IsBrownianFiltration W ℱ` says that the Brownian motion `W` is adapted to the filtration `ℱ`
and that its increments after time `s` are independent of `ℱ s`. The natural filtration of
`W` is an instance, a smaller filtration to which `W` is adapted is one, and so is the
right-continuous version `ℱ₊`, since independence of `W_t − W_r` from `ℱ r ⊇ ℱ₊ s` for
`r ↓ s` passes to the limit `W_t − W_s` along the continuous paths.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- `W` is a Brownian motion for the filtration `ℱ`: it is adapted, and its increments after
time `s ≥ 0` are independent of `ℱ s`. -/
structure IsBrownianFiltration (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Prop where
  measurable : ∀ t, Measurable[ℱ t] (W.W t)
  indep : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s < t →
    Indep (ℱ s) (MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance) P

/-- A Brownian motion is a Brownian motion for its natural filtration. -/
theorem isBrownianFiltration_natural (W : BrownianMotion P) :
    IsBrownianFiltration W (Martingale.naturalFiltration W) where
  measurable t := by
    refine Measurable.of_comap_le ?_
    change MeasurableSpace.comap (W.W t) inferInstance
      ≤ ⨆ j ≤ t, MeasurableSpace.comap (W.W j) inferInstance
    exact le_iSup₂_of_le t le_rfl le_rfl
  indep _ _ hs hst := Martingale.increment_indep_naturalFiltration_aux W hs hst

/-- A Brownian motion for `ℱ` is one for any smaller filtration to which it is adapted. -/
theorem IsBrownianFiltration.of_le {W : BrownianMotion P} {ℱ 𝒢 : Filtration ℝ ‹MeasurableSpace Ω›}
    (h : IsBrownianFiltration W ℱ) (hle : 𝒢 ≤ ℱ) (hadapted : ∀ t, Measurable[𝒢 t] (W.W t)) :
    IsBrownianFiltration W 𝒢 where
  measurable := hadapted
  indep _ _ hs hst := indep_of_indep_of_le_left (h.indep hs hst) (hle _)

/-- A Brownian motion for `ℱ` is one for the right-continuous filtration `ℱ₊`. -/
theorem IsBrownianFiltration.rightCont {W : BrownianMotion P} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (h : IsBrownianFiltration W ℱ) : IsBrownianFiltration W ℱ.rightCont where
  measurable t := (h.measurable t).mono (ℱ.le_rightCont t) le_rfl
  indep := by
    intro s t hs hst
    obtain ⟨r, -, hr_mem, hr_tend⟩ := exists_seq_strictAnti_tendsto' hst
    have hle : ∀ n, ℱ.rightCont s ≤ ℱ (r n) := fun n => by
      rw [Filtration.rightCont_eq_of_neBot_nhdsGT ℱ s]
      exact iInf₂_le (r n) (hr_mem n).1
    refine Probability.indep_comap_of_tendsto_ae (ℱ.rightCont.le s)
      (X := fun n ω => W.W t ω - W.W (r n) ω) (Y := fun ω => W.W t ω - W.W s ω)
      (fun n => (W.measurable_eval t).sub (W.measurable_eval _))
      ((W.measurable_eval t).sub (W.measurable_eval s))
      (fun n => indep_of_indep_of_le_left (h.indep (hs.trans (hr_mem n).1.le) (hr_mem n).2)
        (hle n)) ?_
    filter_upwards [W.continuous_paths] with ω hω
    exact tendsto_const_nhds.sub ((hω.tendsto s).comp hr_tend)

namespace IsBrownianFiltration

variable {W : BrownianMotion P} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- `W_t` is `ℱ t`-strongly measurable. -/
theorem stronglyMeasurable (h : IsBrownianFiltration W ℱ) (t : ℝ) :
    StronglyMeasurable[ℱ t] (W.W t) :=
  (h.measurable t).stronglyMeasurable

/-- The conditional expectation of the increment `W_t − W_s`, `0 ≤ s < t`, given `ℱ s`
vanishes. -/
theorem condExp_increment_eq_zero (h : IsBrownianFiltration W ℱ) {s t : ℝ} (hs : 0 ≤ s)
    (hst : s < t) : P[(fun ω => W.W t ω - W.W s ω) | ℱ s] =ᵐ[P] fun _ => 0 :=
  Martingale.condExp_increment_eq_zero_of_indep W ℱ hs hst (h.indep hs hst)

/-- The martingale identity `E[W_t | ℱ s] = W_s` for `0 ≤ s ≤ t`. -/
theorem condExp_eq (h : IsBrownianFiltration W ℱ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    P[W.W t | ℱ s] =ᵐ[P] W.W s := by
  have h_int_s := Martingale.brownianMotion_integrable W s
  rcases hst.eq_or_lt with rfl | hlt
  · rw [condExp_of_stronglyMeasurable (ℱ.le s) (h.stronglyMeasurable s) h_int_s]
  · have h_int_t := Martingale.brownianMotion_integrable W t
    have h_decomp : (W.W t : Ω → ℝ) = W.W s + (W.W t - W.W s) := by
      funext ω; simp
    rw [h_decomp]
    filter_upwards [condExp_add h_int_s (h_int_t.sub h_int_s) (ℱ s),
      h.condExp_increment_eq_zero hs hlt] with ω h_add h_zero
    rw [h_add, Pi.add_apply,
      condExp_of_stronglyMeasurable (ℱ.le s) (h.stronglyMeasurable s) h_int_s]
    change W.W s ω + P[(fun ω => W.W t ω - W.W s ω) | ℱ s] ω = W.W s ω
    rw [h_zero, add_zero]

/-- If `W` is a Brownian motion for `ℱ`, it is one for every filtration `𝒢` to which it is adapted
and with `𝒢 s ≤ ℱ s ⊔ m s` for σ-algebras `m s` independent of `ℱ s ⊔ σ(W_t − W_s)`. -/
theorem of_le_sup (h : IsBrownianFiltration W ℱ) {𝒢 : Filtration ℝ ‹MeasurableSpace Ω›}
    (hadapted : ∀ t, Measurable[𝒢 t] (W.W t)) {m : ℝ → MeasurableSpace Ω}
    (hm : ∀ s, m s ≤ ‹MeasurableSpace Ω›) (hle : ∀ s, 𝒢 s ≤ ℱ s ⊔ m s)
    (hind : ∀ ⦃s t : ℝ⦄, 0 ≤ s → s < t → Indep (m s)
      (ℱ s ⊔ MeasurableSpace.comap (fun ω => W.W t ω - W.W s ω) inferInstance) P) :
    IsBrownianFiltration W 𝒢 where
  measurable := hadapted
  indep s t hs hst := indep_of_indep_of_le_left
    (Probability.indep_sup_left_of_indep (ℱ.le s) (hm s)
      ((W.measurable_eval t).sub (W.measurable_eval s)).comap_le (h.indep hs hst) (hind hs hst))
    (hle s)

end IsBrownianFiltration

end LevyStochCalc.Brownian
