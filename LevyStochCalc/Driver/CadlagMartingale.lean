/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.GermIndep
import LevyStochCalc.Probability.CondExpModification

/-!
# The càdlàg conditional-expectation martingale of a Lévy driver

`Probability/CondExpModification.lean` builds a right-continuous modification of
`t ↦ 𝔼[ξ | ℱ₊ t]` indexed by `ℝ≥0`, the index type the càdlàg machinery needs. Reindexing by `ℝ`
means saying what happens before time `0`, where the constant `𝔼 ξ` is the right answer: it is
`𝔼[ξ | ℱ₊ t]` there by Blumenthal's 0-1 law (`Driver/GermIndep.lean`), and being constant it is
measurable for every σ-algebra, which the modification's value at `0` is not.

## Main statements

* `LevyDriver.cadlagCondExp` — the reindexed process.
* `LevyDriver.martingale_cadlagCondExp` — it is a martingale for `ℱ₊`.
* `LevyDriver.cadlagCondExp_ae_eq` — it agrees with `𝔼[ξ | ℱ₊ t]` at every fixed `t`.
* `LevyDriver.tendsto_cadlagCondExp_nhdsGT`, `LevyDriver.ae_exists_tendsto_cadlagCondExp_nhdsLT`
  — right continuity of every path, and left limits almost surely.
-/

open Filter MeasureTheory ProbabilityTheory Topology
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν) (ξ : Ω → ℝ)

/-- The càdlàg conditional-expectation martingale of `ξ`, indexed by `ℝ`: the `ℝ≥0`-indexed
modification before time `0` replaced by the constant `𝔼 ξ`. -/
noncomputable def cadlagCondExp : ℝ → Ω → ℝ := fun t ω =>
  if 0 ≤ t then Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal t) ω
  else ∫ ω', ξ ω' ∂P

variable {D ξ}

theorem cadlagCondExp_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    D.cadlagCondExp ξ t
      = Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal t) := by
  funext ω; simp only [cadlagCondExp, if_pos ht]

theorem cadlagCondExp_of_neg {t : ℝ} (ht : t < 0) :
    D.cadlagCondExp ξ t = fun _ => ∫ ω', ξ ω' ∂P := by
  funext ω; simp only [cadlagCondExp, if_neg (not_le.2 ht)]

/-- At every fixed time the process agrees with the conditional expectation. -/
theorem cadlagCondExp_ae_eq (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) (t : ℝ) :
    D.cadlagCondExp ξ t =ᵐ[P] P[ξ | D.filtration.rightCont t] := by
  rcases le_or_gt 0 t with ht | ht
  · rw [cadlagCondExp_of_nonneg ht]
    have h := Probability.condExpModif_ae_eq (ℱ := D.filtration.rightCont) hξ (Real.toNNReal t)
    rwa [Real.coe_toNNReal t ht] at h
  · rw [cadlagCondExp_of_neg ht]
    exact (D.condExp_rightCont_nonpos hSM ht.le).symm

theorem stronglyMeasurable_cadlagCondExp (t : ℝ) :
    StronglyMeasurable[D.filtration.rightCont t] (D.cadlagCondExp ξ t) := by
  rcases le_or_gt 0 t with ht | ht
  · rw [cadlagCondExp_of_nonneg ht]
    have h := Probability.adapted_condExpModif (μ := P) (ℱ := D.filtration.rightCont) (ξ := ξ)
      (Real.toNNReal t)
    rw [Probability.restrictNNReal_apply, Real.coe_toNNReal t ht] at h
    exact h.stronglyMeasurable
  · rw [cadlagCondExp_of_neg ht]
    exact stronglyMeasurable_const

/-- **The reindexed process is a martingale for the right-continuous joint filtration.** -/
theorem martingale_cadlagCondExp (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) :
    Martingale (D.cadlagCondExp ξ) D.filtration.rightCont P := by
  refine ⟨fun t => stronglyMeasurable_cadlagCondExp t, fun s t hst => ?_⟩
  calc P[D.cadlagCondExp ξ t | D.filtration.rightCont s]
      =ᵐ[P] P[P[ξ | D.filtration.rightCont t] | D.filtration.rightCont s] :=
        condExp_congr_ae (cadlagCondExp_ae_eq hξ hSM t)
    _ =ᵐ[P] P[ξ | D.filtration.rightCont s] :=
        condExp_condExp_of_le (D.filtration.rightCont.mono hst) (D.filtration.rightCont.le t)
    _ =ᵐ[P] D.cadlagCondExp ξ s := (cadlagCondExp_ae_eq hξ hSM s).symm

/-- Every path of the reindexed process is right-continuous. -/
theorem tendsto_cadlagCondExp_nhdsGT (t : ℝ) (ω : Ω) :
    Tendsto (fun s => D.cadlagCondExp ξ s ω) (𝓝[>] t) (𝓝 (D.cadlagCondExp ξ t ω)) := by
  rcases lt_or_ge t 0 with ht | ht
  · have hev : (fun _ : ℝ => ∫ ω', ξ ω' ∂P) =ᶠ[𝓝[>] t] fun s => D.cadlagCondExp ξ s ω := by
      filter_upwards [Ioo_mem_nhdsGT ht] with s hs
      rw [cadlagCondExp_of_neg hs.2]
    rw [cadlagCondExp_of_neg ht]
    exact Tendsto.congr' hev tendsto_const_nhds
  · have hmaps : Set.MapsTo Real.toNNReal (Set.Ioi t) (Set.Ioi (Real.toNNReal t)) := by
      intro s hs
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg ht).2 hs
    have hcomp : ContinuousWithinAt
        (fun s : ℝ => Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal s) ω)
        (Set.Ioi t) t :=
      (Probability.continuousWithinAt_condExpModif (ℱ := D.filtration.rightCont) (ξ := ξ)
        (Real.toNNReal t) ω).comp continuous_real_toNNReal.continuousWithinAt hmaps
    have hev : (fun s : ℝ =>
          Probability.condExpModif P D.filtration.rightCont ξ (Real.toNNReal s) ω)
        =ᶠ[𝓝[>] t] fun s => D.cadlagCondExp ξ s ω := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      rw [cadlagCondExp_of_nonneg (ht.trans (le_of_lt hs))]
    rw [cadlagCondExp_of_nonneg ht]
    exact Tendsto.congr' hev hcomp

/-- Almost every path of the reindexed process has left limits everywhere. -/
theorem ae_exists_tendsto_cadlagCondExp_nhdsLT :
    ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ L : ℝ,
      Tendsto (fun s => D.cadlagCondExp ξ s ω) (𝓝[<] t) (𝓝 L) := by
  filter_upwards [Probability.ae_exists_tendsto_condExpModif_nhdsLT
    (μ := P) (ℱ := D.filtration.rightCont) (ξ := ξ)] with ω hω t
  rcases le_or_gt t 0 with ht | ht
  · refine ⟨∫ ω', ξ ω' ∂P, Tendsto.congr' ?_ tendsto_const_nhds⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [cadlagCondExp_of_neg (lt_of_lt_of_le hs ht)]
  · obtain ⟨L, hL⟩ := hω (Real.toNNReal t)
    have hmap : Tendsto Real.toNNReal (𝓝[<] t) (𝓝[<] (Real.toNNReal t)) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((continuous_real_toNNReal.tendsto t).mono_left nhdsWithin_le_nhds) ?_
      filter_upwards [Ioo_mem_nhdsLT ht] with s hs
      exact (Real.toNNReal_lt_toNNReal_iff_of_nonneg hs.1.le).2 hs.2
    refine ⟨L, Tendsto.congr' ?_ (hL.comp hmap)⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    rw [Function.comp_apply, cadlagCondExp_of_nonneg hs.1.le]

/-- At time `0` the process is the mean, by Blumenthal's 0-1 law. -/
theorem cadlagCondExp_zero_ae_eq (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) :
    D.cadlagCondExp ξ 0 =ᵐ[P] fun _ => ∫ ω', ξ ω' ∂P :=
  (cadlagCondExp_ae_eq hξ hSM 0).trans (D.condExp_rightCont_zero hSM)

/-- At a terminal time for which `ξ` is measurable the process is `ξ`. -/
theorem cadlagCondExp_terminal_ae_eq (hξ : MemLp ξ 2 P) (hSM : StronglyMeasurable ξ) {T : ℝ}
    (h_meas : StronglyMeasurable[D.filtration.rightCont T] ξ) :
    D.cadlagCondExp ξ T =ᵐ[P] ξ := by
  refine (cadlagCondExp_ae_eq hξ hSM T).trans ?_
  rw [condExp_of_stronglyMeasurable (D.filtration.rightCont.le T) h_meas
    (hξ.integrable one_le_two)]

end LevyDriver

end LevyStochCalc.Driver
