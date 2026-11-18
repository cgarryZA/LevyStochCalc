/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.FiniteHorizonDrift

/-!
# Square-integrable Itô processes on a finite horizon

A process `X` with values in a complete real inner product space `E` is a square-integrable Itô
process on `[0, T]` for a filtration `ℱ`, with initial value `X₀`, drift `a` and martingale part
`M`, when for every `t ∈ [0, T]`, almost surely,

`X_t = X₀ + ∫_0^t a_s ds + M_t`,

where `X₀` is square integrable and `ℱ_0`-measurable up to a null set, the drift is square
integrable for `P ⊗ ds` on `[0, T]` and `a_s` is `ℱ_s`-measurable up to a null set at almost every
time, and `M` has orthogonal increments on `[0, T]`. Nothing is assumed of the driving noise:
the martingale part is any process with orthogonal increments, for instance an `L²` stochastic
integral on `[0, T]`.

The drift may be changed on a `P ⊗ ds`-null set (`IsL2ItoProcessOn.congr_drift`), so every drift
can be replaced by a jointly strongly measurable one (`IsL2ItoProcessOn.exists_stronglyMeasurable`),
and the image of an Itô process under a continuous linear map is one
(`IsL2ItoProcessOn.map`).
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

variable {Ω E E' : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']

/-- `X` is a square-integrable Itô process on `[0, T]` for `ℱ`, with initial value `X₀`, drift
`a` and martingale part `M`: for every `t ∈ [0, T]`, almost surely,
`X_t = X₀ + ∫_0^t a_s ds + M_t`. -/
structure IsL2ItoProcessOn (ℱ : Filtration ℝ m0) (P : Measure Ω) (T : ℝ)
    (X : ℝ → Ω → E) (X₀ : Ω → E) (a : ℝ → Ω → E) (M : ℝ → Ω → E) : Prop where
  initial_aestronglyMeasurable : AEStronglyMeasurable[ℱ 0] X₀ P
  initial_memLp : MemLp X₀ 2 P
  drift_memLp :
    MemLp (fun p : Ω × ℝ => a p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
  drift_adapted :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), AEStronglyMeasurable[ℱ s] (a s) P
  martingale : HasOrthogonalIncrementsOn ℱ P T M
  decomposition : ∀ t, 0 ≤ t → t ≤ T →
    X t =ᵐ[P] fun ω => X₀ ω + (∫ s in Set.Icc (0 : ℝ) t, a s ω) + M t ω

section ProductAE

variable [IsFiniteMeasure P] {ν : Measure ℝ} [IsFiniteMeasure ν]

/-- An almost-everywhere equality for a product measure holds along almost every time slice. -/
theorem ae_ae_eq_slice_of_ae_eq_prod {β : Type*} {F F' : Ω × ℝ → β} (h : F =ᵐ[P.prod ν] F') :
    ∀ᵐ s ∂ν, (fun ω => F (ω, s)) =ᵐ[P] fun ω => F' (ω, s) := by
  have h' : F =ᵐ[(ν.prod P).map Prod.swap] F' := by rwa [Measure.prod_swap]
  have hc : F ∘ Prod.swap =ᵐ[ν.prod P] F' ∘ Prod.swap :=
    ae_eq_comp measurable_swap.aemeasurable h'
  exact Measure.ae_ae_of_ae_prod hc

/-- A function square integrable for a product measure is square integrable along almost every
time slice. -/
theorem ae_memLp_slice {G : Type*} [NormedAddCommGroup G] {F : Ω × ℝ → G}
    (hF : MemLp F 2 (P.prod ν)) :
    ∀ᵐ s ∂ν, MemLp (fun ω => F (ω, s)) 2 P := by
  have hsq : Integrable (fun p : ℝ × Ω => ‖F p.swap‖ ^ 2) (ν.prod P) :=
    ((memLp_two_iff_integrable_sq_norm hF.1).1 hF).swap
  have hm : AEStronglyMeasurable (fun p : ℝ × Ω => F p.swap) (ν.prod P) :=
    hF.1.comp_quasiMeasurePreserving (Measure.measurePreserving_swap).quasiMeasurePreserving
  filter_upwards [hsq.prod_right_ae, hm.prodMk_left] with s hs hms
  exact (memLp_two_iff_integrable_sq_norm hms).2 hs

end ProductAE

namespace IsL2ItoProcessOn

variable {ℱ : Filtration ℝ m0} {T : ℝ} {X : ℝ → Ω → E} {X₀ : Ω → E} {a : ℝ → Ω → E}
  {M : ℝ → Ω → E}

omit [CompleteSpace E] in
/-- At almost every time of the window the drift is square integrable. -/
theorem ae_memLp_drift [IsFiniteMeasure P] (h : IsL2ItoProcessOn ℱ P T X X₀ a M) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), MemLp (a s) 2 P :=
  ae_memLp_slice h.drift_memLp

omit [CompleteSpace E] in
/-- **Almost-everywhere invariance in the drift.** An Itô process on `[0, T]` stays one, with
the same process, initial value and martingale part, when its drift is changed on a
`P ⊗ ds`-null subset of `Ω × [0, T]`. -/
theorem congr_drift [IsFiniteMeasure P] (h : IsL2ItoProcessOn ℱ P T X X₀ a M)
    {a' : ℝ → Ω → E}
    (hae : (fun p : Ω × ℝ => a p.2 p.1)
      =ᵐ[P.prod (volume.restrict (Set.Icc (0 : ℝ) T))] fun p => a' p.2 p.1) :
    IsL2ItoProcessOn ℱ P T X X₀ a' M where
  initial_aestronglyMeasurable := h.initial_aestronglyMeasurable
  initial_memLp := h.initial_memLp
  drift_memLp := h.drift_memLp.ae_eq hae
  drift_adapted := by
    filter_upwards [h.drift_adapted, ae_ae_eq_slice_of_ae_eq_prod hae] with s hs hs'
    exact hs.congr hs'
  martingale := h.martingale
  decomposition t ht0 htT := by
    filter_upwards [h.decomposition t ht0 htT, Measure.ae_ae_of_ae_prod hae] with ω hω hω'
    rw [hω]
    have e : ∫ s in Set.Icc (0 : ℝ) t, a s ω = ∫ s in Set.Icc (0 : ℝ) t, a' s ω :=
      integral_congr_ae (ae_restrict_of_ae_restrict_of_subset
        (Set.Icc_subset_Icc le_rfl htT) hω')
    rw [e]

omit [CompleteSpace E] in
/-- Every Itô process on `[0, T]` has a drift that is jointly strongly measurable and agrees with
the given one `P ⊗ ds`-almost everywhere on `Ω × [0, T]`. -/
theorem exists_stronglyMeasurable [IsFiniteMeasure P] (h : IsL2ItoProcessOn ℱ P T X X₀ a M) :
    ∃ a' : ℝ → Ω → E, StronglyMeasurable (fun p : Ω × ℝ => a' p.2 p.1) ∧
      (fun p : Ω × ℝ => a p.2 p.1)
        =ᵐ[P.prod (volume.restrict (Set.Icc (0 : ℝ) T))] (fun p => a' p.2 p.1) ∧
      IsL2ItoProcessOn ℱ P T X X₀ a' M := by
  refine ⟨fun s ω => h.drift_memLp.1.mk _ (ω, s), h.drift_memLp.1.stronglyMeasurable_mk, ?_, ?_⟩
  · exact h.drift_memLp.1.ae_eq_mk
  · exact h.congr_drift h.drift_memLp.1.ae_eq_mk

omit [CompleteSpace E] in
/-- An Itô process on `[0, T]` is square integrable at every time of the window. -/
theorem memLp [IsFiniteMeasure P] (h : IsL2ItoProcessOn ℱ P T X X₀ a M) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) : MemLp (X t) 2 P := by
  obtain ⟨a', ha', -, h'⟩ := h.exists_stronglyMeasurable
  have hA : MemLp (fun ω => ∫ s in Set.Icc (0 : ℝ) t, a' s ω) 2 P :=
    memLp_setIntegral ha' (memLp_prod_Icc_mono htT h'.drift_memLp) ht0
  exact ((h'.initial_memLp.add hA).add (h'.martingale.memLp t ht0 htT)).ae_eq
    (h'.decomposition t ht0 htT).symm

/-- **The image of an Itô process under a continuous linear map.** If
`X = X₀ + ∫ a ds + M` on `[0, T]` and `G : E →L[ℝ] E'`, then
`G X = G X₀ + ∫ G a ds + G M` on `[0, T]`. -/
theorem map [IsFiniteMeasure P] (h : IsL2ItoProcessOn ℱ P T X X₀ a M) (G : E →L[ℝ] E') :
    IsL2ItoProcessOn ℱ P T (fun t ω => G (X t ω)) (fun ω => G (X₀ ω)) (fun s ω => G (a s ω))
      (fun t ω => G (M t ω)) where
  initial_aestronglyMeasurable := G.continuous.comp_aestronglyMeasurable
    h.initial_aestronglyMeasurable
  initial_memLp := G.comp_memLp' h.initial_memLp
  drift_memLp := G.comp_memLp' h.drift_memLp
  drift_adapted := by
    filter_upwards [h.drift_adapted] with s hs
    exact G.continuous.comp_aestronglyMeasurable hs
  martingale := h.martingale.map G
  decomposition t ht0 htT := by
    filter_upwards [h.decomposition t ht0 htT,
      ae_integrableOn_of_memLp (memLp_prod_Icc_mono htT h.drift_memLp)] with ω hω hω'
    rw [hω, map_add, map_add, ← G.integral_comp_comm hω']

end IsL2ItoProcessOn

end LevyStochCalc.Ito.FiniteHorizon
