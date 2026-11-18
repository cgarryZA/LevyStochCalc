/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Process.Filtration

/-!
# Square-integrable processes with orthogonal increments on a finite horizon

A process `M` with values in a real inner product space has orthogonal increments on `[0, T]` for
a filtration `ℱ` when every `M_t`, `t ∈ [0, T]`, is square integrable, `M_0 = 0` almost surely,
and for `0 ≤ s ≤ t ≤ T` the increment `M_t - M_s` is orthogonal in `L²` to every
square-integrable variable that is `ℱ_s`-measurable up to a null set:
`𝔼⟪ξ, M_t⟫ = 𝔼⟪ξ, M_s⟫`.

This is the only property of a stochastic integral that the expected product identity of two Itô
processes uses besides the polarised isometry. A square-integrable martingale on `[0, T]` in the
sense of conditional expectations has it (`HasOrthogonalIncrementsOn.of_condExp`); the property is
kept under almost-sure changes of each `M_t` and under continuous linear maps.

## Main definitions

* `LevyStochCalc.Ito.FiniteHorizon.HasOrthogonalIncrementsOn`

## Main statements

* `HasOrthogonalIncrementsOn.of_condExp`, `HasOrthogonalIncrementsOn.congr`,
  `HasOrthogonalIncrementsOn.map`
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

variable {Ω E E' : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E']

/-- The pairing of two square-integrable functions is integrable. -/
theorem integrable_inner_of_memLp {f g : Ω → E} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => ⟪f ω, g ω⟫) P :=
  Integrable.mono' (hf.norm.integrable_mul hg.norm)
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
    (Eventually.of_forall fun ω => norm_inner_le_norm (f ω) (g ω))

/-- A process `M` on `[0, T]` is square integrable, vanishes at time zero, and its increments over
windows `[s, t] ⊆ [0, T]` are orthogonal in `L²` to the square-integrable variables that are
`ℱ_s`-measurable up to a null set. -/
structure HasOrthogonalIncrementsOn (ℱ : Filtration ℝ m0) (P : Measure Ω) (T : ℝ)
    (M : ℝ → Ω → E) : Prop where
  memLp : ∀ t, 0 ≤ t → t ≤ T → MemLp (M t) 2 P
  ae_zero : M 0 =ᵐ[P] 0
  integral_inner_eq : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → ∀ ξ : Ω → E,
    AEStronglyMeasurable[ℱ s] ξ P → MemLp ξ 2 P →
      ∫ ω, ⟪ξ ω, M t ω⟫ ∂P = ∫ ω, ⟪ξ ω, M s ω⟫ ∂P

namespace HasOrthogonalIncrementsOn

variable {ℱ : Filtration ℝ m0} {T : ℝ} {M : ℝ → Ω → E}

/-- A process with orthogonal increments is orthogonal to the square-integrable variables
measurable at time zero. -/
theorem integral_inner_eq_zero (hM : HasOrthogonalIncrementsOn ℱ P T M) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {ξ : Ω → E} (hξ : AEStronglyMeasurable[ℱ 0] ξ P) (hξ2 : MemLp ξ 2 P) :
    ∫ ω, ⟪ξ ω, M t ω⟫ ∂P = 0 := by
  rw [hM.integral_inner_eq 0 t le_rfl ht0 htT ξ hξ hξ2]
  have h0 : (fun ω => ⟪ξ ω, M 0 ω⟫) =ᵐ[P] fun _ => (0 : ℝ) := by
    filter_upwards [hM.ae_zero] with ω hω
    rw [hω, Pi.zero_apply, inner_zero_right]
  rw [integral_congr_ae h0, integral_zero]

/-- The orthogonality to the variables measurable at time zero, with the pairing reversed. -/
theorem integral_inner_eq_zero' (hM : HasOrthogonalIncrementsOn ℱ P T M) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) {ξ : Ω → E} (hξ : AEStronglyMeasurable[ℱ 0] ξ P) (hξ2 : MemLp ξ 2 P) :
    ∫ ω, ⟪M t ω, ξ ω⟫ ∂P = 0 := by
  rw [← hM.integral_inner_eq_zero ht0 htT hξ hξ2]
  exact integral_congr_ae (Eventually.of_forall fun ω => real_inner_comm _ _)

/-- Orthogonal increments are kept under an almost-sure change of the process at each time. -/
theorem congr (hM : HasOrthogonalIncrementsOn ℱ P T M) {M' : ℝ → Ω → E}
    (h : ∀ t, 0 ≤ t → t ≤ T → M t =ᵐ[P] M' t) (h0 : M 0 =ᵐ[P] M' 0) :
    HasOrthogonalIncrementsOn ℱ P T M' where
  memLp t ht0 htT := (hM.memLp t ht0 htT).ae_eq (h t ht0 htT)
  ae_zero := h0.symm.trans hM.ae_zero
  integral_inner_eq s t hs hst htT ξ hξ hξ2 := by
    have e : ∀ r, 0 ≤ r → r ≤ T → ∫ ω, ⟪ξ ω, M' r ω⟫ ∂P = ∫ ω, ⟪ξ ω, M r ω⟫ ∂P := by
      intro r hr hrT
      refine integral_congr_ae ?_
      filter_upwards [h r hr hrT] with ω hω
      rw [hω]
    rw [e t (hs.trans hst) htT, e s hs (hst.trans htT)]
    exact hM.integral_inner_eq s t hs hst htT ξ hξ hξ2

/-- The image of a process with orthogonal increments under a continuous linear map between
complete real inner product spaces has orthogonal increments. -/
theorem map [CompleteSpace E] [CompleteSpace E'] (hM : HasOrthogonalIncrementsOn ℱ P T M)
    (G : E →L[ℝ] E') : HasOrthogonalIncrementsOn ℱ P T fun t ω => G (M t ω) where
  memLp t ht0 htT := G.comp_memLp' (hM.memLp t ht0 htT)
  ae_zero := by
    filter_upwards [hM.ae_zero] with ω hω
    rw [hω, Pi.zero_apply, map_zero, Pi.zero_apply]
  integral_inner_eq s t hs hst htT ξ hξ hξ2 := by
    have e : ∀ r, ∫ ω, ⟪ξ ω, G (M r ω)⟫ ∂P
        = ∫ ω, ⟪(ContinuousLinearMap.adjoint G) (ξ ω), M r ω⟫ ∂P := fun r =>
      integral_congr_ae (Eventually.of_forall fun ω =>
        (ContinuousLinearMap.adjoint_inner_left G (M r ω) (ξ ω)).symm)
    rw [e t, e s]
    exact hM.integral_inner_eq s t hs hst htT _
      ((ContinuousLinearMap.adjoint G).continuous.comp_aestronglyMeasurable hξ)
      ((ContinuousLinearMap.adjoint G).comp_memLp' hξ2)

/-- **Martingales on a finite horizon have orthogonal increments.** A process on `[0, T]` which is
square integrable, vanishes at time zero and satisfies `𝔼[M_t | ℱ_s] = M_s` for
`0 ≤ s ≤ t ≤ T` has orthogonal increments on `[0, T]`. -/
theorem of_condExp [IsFiniteMeasure P] [CompleteSpace E]
    (hL2 : ∀ t, 0 ≤ t → t ≤ T → MemLp (M t) 2 P) (h0 : M 0 =ᵐ[P] 0)
    (hce : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → P[M t | ℱ s] =ᵐ[P] M s) :
    HasOrthogonalIncrementsOn ℱ P T M where
  memLp := hL2
  ae_zero := h0
  integral_inner_eq s t hs hst htT ξ hξ hξ2 := by
    haveI : SigmaFinite (P.trim (ℱ.le s)) := (isFiniteMeasure_trim (ℱ.le s)).toSigmaFinite
    have hMt := hL2 t (hs.trans hst) htT
    have hint : Integrable (fun ω => ⟪ξ ω, M t ω⟫) P := integrable_inner_of_memLp hξ2 hMt
    have hpull : P[fun ω => (innerSL ℝ (ξ ω) : E →L[ℝ] ℝ) (M t ω) | ℱ s]
        =ᵐ[P] fun ω => (innerSL ℝ (ξ ω) : E →L[ℝ] ℝ) ((P[M t | ℱ s]) ω) :=
      condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) hξ (by simpa using hint)
        (hMt.integrable one_le_two)
    rw [← integral_condExp (ℱ.le s)]
    refine integral_congr_ae ?_
    filter_upwards [hpull, hce s t hs hst htT] with ω hω hω'
    simpa [hω'] using hω

end HasOrthogonalIncrementsOn

end LevyStochCalc.Ito.FiniteHorizon
