/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.SecondMoment
import LevyStochCalc.Ito.CompensatedLocality
import LevyStochCalc.Brownian.ItoFinsetSum
import LevyStochCalc.Brownian.ItoLinear

/-!
# Weighted stability estimates for Itô–Lévy processes

The difference of two Itô–Lévy processes over the same Lévy driver and filtration is again an
Itô–Lévy process, with the differenced data (`isItoLevyProcess_sub`). Feeding it to the
exponentially weighted second-moment identity turns a bound on the rate

`2 𝔼[ΔX_s Δb_s] + ∑_j 𝔼[|Δσ_j(s)|²] + 𝔼 ∫_E |Δγ(s, e)|² ν(de) ≤ c 𝔼[|ΔX_s|²]`

into the stability estimate `𝔼[|ΔX_T|²] ≤ e^{cT} 𝔼[|ΔX₀|²]`, with no Grönwall lemma: the
exponential weight does the work. A drift, diffusion and jump coefficient Lipschitz in the state
gives such a rate bound with `c = 2L + 2L²`, and equal initial values then force the two
processes to agree at the horizon.

## Main statements

* `integral_mul_self_le_of_rate_le` — the weighted identity as a bound: a rate bounded by
  `c 𝔼[X_s²]` at almost every time of the window gives `𝔼[X_T²] ≤ e^{cT} 𝔼[X₀²]`.
* `isItoLevyProcess_sub` — the difference of two Itô–Lévy processes over the same driver is an
  Itô–Lévy process with the differenced initial value, drift, diffusion and jump coefficient.
* `integral_sub_mul_self_le_of_rate_le` — the stability estimate under a rate bound on the
  difference.
* `integral_sub_mul_self_le_of_lipschitz` — the stability estimate under pointwise Lipschitz
  bounds on the differences of the coefficients, with `c = 2L + 2L²`.
* `ae_eq_of_lipschitz_of_ae_eq_initial` — two Itô–Lévy processes with Lipschitz-close
  coefficients and almost surely equal initial values agree almost surely at every horizon.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.Stability

open LevyStochCalc.Ito.SecondMoment

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section RateBound

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X : ℝ → Ω → ℝ} {X₀ : Ω → ℝ} {b : ℝ → Ω → ℝ} {σ : ℝ → Ω → Fin d → ℝ} {γ : Ω → ℝ → E → ℝ}

/-- **The weighted second-moment identity as a bound.** If at almost every time of the window
the rate `2 𝔼[X_s b_s] + ∑_j 𝔼[σ_j(s)²] + 𝔼 ∫_E γ(s, e)² ν(de)` is at most `c 𝔼[X_s²]`, then
`𝔼[X_T²] ≤ e^{cT} 𝔼[X₀²]`. -/
theorem integral_mul_self_le_of_rate_le
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (𝒲 : D.CrossWitness ℱ) (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {c T : ℝ} (hT : 0 < T)
    (hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      2 * ∫ ω, X s ω * b s ω ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        ≤ c * ∫ ω, X s ω * X s ω ∂P) :
    ∫ ω, X T ω * X T ω ∂P ≤ Real.exp (c * T) * ∫ ω, X₀ ω * X₀ ω ∂P := by
  have key := integral_exp_mul_self_eq_of_isItoLevyProcess h 𝒲 hX₀ hX₀2 hbm hbp hbq (-c) hT
  have hneg : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (-c * s)
      * (-c * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b s ω ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) ≤ 0 := by
    refine setIntegral_nonpos_of_ae_restrict ?_
    filter_upwards [hrate] with s hs
    have hle : -c * ∫ ω, X s ω * X s ω ∂P + 2 * ∫ ω, X s ω * b s ω ∂P
        + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
        + (∫⁻ ω, ∫⁻ e, (‖γ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal ≤ 0 := by linarith
    simpa using mul_le_mul_of_nonneg_left hle (Real.exp_nonneg (-c * s))
  have hmain : Real.exp (-c * T) * ∫ ω, X T ω * X T ω ∂P ≤ ∫ ω, X₀ ω * X₀ ω ∂P := by
    rw [key]
    linarith
  have hexp : Real.exp (c * T) * Real.exp (-c * T) = 1 := by
    rw [← Real.exp_add, show c * T + -c * T = 0 by ring, Real.exp_zero]
  calc ∫ ω, X T ω * X T ω ∂P
      = Real.exp (c * T) * (Real.exp (-c * T) * ∫ ω, X T ω * X T ω ∂P) := by
        rw [← mul_assoc, hexp, one_mul]
    _ ≤ Real.exp (c * T) * ∫ ω, X₀ ω * X₀ ω ∂P :=
        mul_le_mul_of_nonneg_left hmain (Real.exp_pos _).le

end RateBound

section Difference

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

omit [IsProbabilityMeasure P] in
/-- The window energy of a difference of marked integrands is finite when both are. -/
theorem lintegral_sq_sub_marked_lt_top [SFinite P] {φ ψ : Ω → ℝ → E → ℝ}
    (hφ : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
    (hψ : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2) {T : ℝ}
    (hφq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hψq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e - ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  rw [← lintegral_prod_marked (P := P) (ν := ν) (hφ.sub hψ) T]
  rw [← lintegral_prod_marked (P := P) (ν := ν) hφ T] at hφq
  rw [← lintegral_prod_marked (P := P) (ν := ν) hψ T] at hψq
  have hmφ : Measurable fun p : Ω × ℝ × E => (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    hφ.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hmψ : Measurable fun p : Ω × ℝ × E => (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    hψ.nnnorm.coe_nnreal_ennreal.pow_const 2
  calc ∫⁻ p, (‖φ p.1 p.2.1 p.2.2 - ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
        ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
      ≤ ∫⁻ p, 2 * ((‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 + (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2)
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) :=
        lintegral_mono fun p => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _
    _ = 2 * ((∫⁻ p, (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)))
        + ∫⁻ p, (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2
          ∂(P.prod ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))) := by
        have hmsum : Measurable fun p : Ω × ℝ × E =>
            (‖φ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 + (‖ψ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
          hmφ.add hmψ
        rw [lintegral_const_mul _ hmsum]
        congr 1
        exact lintegral_add_left hmφ _
    _ < ⊤ := ENNReal.mul_lt_top (by simp) (ENNReal.add_lt_top.mpr ⟨hφq, hψq⟩)

variable {d : ℕ} {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

/-- **The difference of two Itô–Lévy processes over the same driver is an Itô–Lévy process**,
with the differenced initial value, drift, diffusion vector and jump coefficient. -/
theorem isItoLevyProcess_sub
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN
      (fun t ω => X t ω - Y t ω) (fun ω => X₀ ω - Y₀ ω) (fun s ω => b s ω - b' s ω)
      (fun s ω j => σ s ω j - σ' s ω j) (fun ω s e => γ ω s e - γ' ω s e) := by
  classical
  -- the admissibility of the differenced data, in the shape the integrals expect
  have hσm : ∀ j : Fin d, Measurable (Function.uncurry fun ω s => σ s ω j - σ' s ω j) :=
    fun j => (h.σ_meas j).sub (h'.σ_meas j)
  have hσp : ∀ j : Fin d, LevyStochCalc.Probability.ProgressivelyMeasurable ℱ
      fun ω s => σ s ω j - σ' s ω j := fun j => (h.σ_prog j).sub (h'.σ_prog j)
  have hσq : ∀ (j : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun j =>
    LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _)
      (h.σ_meas j) (h'.σ_meas j) (h.σ_sq j) (h'.σ_sq j)
  have hγm : Measurable fun p : Ω × ℝ × E => γ p.1 p.2.1 p.2.2 - γ' p.1 p.2.1 p.2.2 :=
    h.γ_meas.sub h'.γ_meas
  have hγp : LevyStochCalc.Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => γ ω s e - γ' ω s e :=
    LevyStochCalc.Poisson.Compensated.markedProgressivelyMeasurable_sub h.γ_prog h'.γ_prog
  have hγq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := fun T hT =>
    lintegral_sq_sub_marked_lt_top h.γ_meas h'.γ_meas (h.γ_sq T hT) (h'.γ_sq T hT)
  refine
    { measurable_path := h.measurable_path.sub h'.measurable_path
      σ_meas := hσm
      σ_prog := hσp
      σ_sq := hσq
      γ_meas := hγm
      γ_prog := hγp
      γ_sq := hγq
      decomposition := ?_ }
  intro t ht
  -- the Brownian coordinates subtract
  have hB : ∀ j : Fin d, ∀ᵐ ω ∂P,
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j)
          (fun ω s => σ s ω j - σ' s ω j) (hσm j) (hσp j) (hσq j) t ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j)
            (fun ω s => σ s ω j) (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) t ω
          - LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ (hℱW j)
              (fun ω s => σ' s ω j) (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) t ω := by
    intro j
    rcases eq_or_lt_of_le ht with h0 | hpos
    · have ht0 : t ≤ 0 := le_of_eq h0.symm
      filter_upwards [LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos
          (D.W.W j) ℱ (hℱW j) (fun ω s => σ s ω j - σ' s ω j) (hσm j) (hσp j) (hσq j) ht0,
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos
          (D.W.W j) ℱ (hℱW j) _ (h.σ_meas j) (h.σ_prog j) (h.σ_sq j) ht0,
        LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_ae_zero_of_nonpos
          (D.W.W j) ℱ (hℱW j) _ (h'.σ_meas j) (h'.σ_prog j) (h'.σ_sq j) ht0] with ω e0 e1 e2
      simp only [Pi.zero_apply] at e0 e1 e2
      rw [e0, e1, e2]
      ring
    · exact LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sub (D.W.W j) ℱ (hℱW j)
        (h.σ_meas j) (h'.σ_meas j) (h.σ_prog j) (h'.σ_prog j) (h.σ_sq j) (h'.σ_sq j)
        (hσm j) (hσp j) (hσq j) hpos
  -- the compensated integrals subtract
  have hC : ∀ᵐ ω ∂P,
      LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN
          (fun ω s e => γ ω s e - γ' ω s e) hγm hγp hγq t ω
        = LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ h.γ_meas h.γ_prog
            h.γ_sq t ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N ℱ hℱN γ' h'.γ_meas
              h'.γ_prog h'.γ_sq t ω := by
    rcases eq_or_lt_of_le ht with h0 | hpos
    · have ht0 : t ≤ 0 := le_of_eq h0.symm
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
          D.N hℱN hγm hγp hγq ht0,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos D.N hℱN
          h.γ_meas h.γ_prog h.γ_sq ht0,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos D.N hℱN
          h'.γ_meas h'.γ_prog h'.γ_sq ht0] with ω e0 e1 e2
      simp only [Pi.zero_apply] at e0 e1 e2
      rw [e0, e1, e2]
      ring
    · exact LevyStochCalc.Poisson.Compensated.stochasticIntegral_sub D.N hℱN h.γ_meas
        h'.γ_meas h.γ_prog h'.γ_prog h.γ_sq h'.γ_sq hγm hγp hγq hpos
  -- the drift integrals subtract
  have hb : ∀ᵐ ω ∂P, ∫ s in Set.Icc (0 : ℝ) t, (b s ω - b' s ω)
      = (∫ s in Set.Icc (0 : ℝ) t, b s ω) - ∫ s in Set.Icc (0 : ℝ) t, b' s ω := by
    filter_upwards [LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b s ω) hbm hbq,
      LevyStochCalc.Ito.Picard.ae_integrableOn_of_lintegral_sq
        (f := fun ω s => b' s ω) hb'm hb'q] with ω hω hω'
    exact integral_sub (hω t) (hω' t)
  filter_upwards [h.decomposition t ht, h'.decomposition t ht, hC, hb,
    (ae_all_iff.mpr hB)] with ω e1 e2 e3 e4 e5
  simp only [LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
    LevyStochCalc.Brownian.Ito.stochasticIntegral] at e1 e2 ⊢
  rw [e1, e2, e3, e4, Finset.sum_congr rfl fun j _ => e5 j, Finset.sum_sub_distrib]
  ring

end Difference

section Stability

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (D.W.W j) ℱ}
  {hℱN : LevyStochCalc.Poisson.IsPoissonFiltration D.N ℱ}
  {X Y : ℝ → Ω → ℝ} {X₀ Y₀ : Ω → ℝ} {b b' : ℝ → Ω → ℝ} {σ σ' : ℝ → Ω → Fin d → ℝ}
  {γ γ' : Ω → ℝ → E → ℝ}

omit [IsProbabilityMeasure P] in
/-- A lintegral dominated by the `ℝ≥0∞` image of an integrable nonnegative function is finite,
and its real value is at most that function's integral. -/
theorem toReal_lintegral_le_of_le {f : Ω → ℝ≥0∞} {g : Ω → ℝ} (hgi : Integrable g P)
    (hg0 : ∀ ω, 0 ≤ g ω) (hle : ∀ ω, f ω ≤ ENNReal.ofReal (g ω)) :
    (∫⁻ ω, f ω ∂P).toReal ≤ ∫ ω, g ω ∂P ∧ ∫⁻ ω, f ω ∂P ≠ ⊤ := by
  have hkey : ∫⁻ ω, f ω ∂P ≤ ENNReal.ofReal (∫ ω, g ω ∂P) := by
    calc ∫⁻ ω, f ω ∂P
        ≤ ∫⁻ ω, ENNReal.ofReal (g ω) ∂P := lintegral_mono hle
      _ = ENNReal.ofReal (∫ ω, g ω ∂P) :=
          (ofReal_integral_eq_lintegral_ofReal hgi (Eventually.of_forall hg0)).symm
  refine ⟨?_, ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkey⟩
  calc (∫⁻ ω, f ω ∂P).toReal
      ≤ (ENNReal.ofReal (∫ ω, g ω ∂P)).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hkey
    _ = ∫ ω, g ω ∂P := ENNReal.toReal_ofReal (integral_nonneg hg0)

/-- **The stability estimate for two Itô–Lévy processes under a rate bound.** If at almost every
time of the window the rate of the difference is at most `c` times its second moment, the second
moment of the difference at the horizon is at most `e^{cT}` times its initial value. -/
theorem integral_sub_mul_self_le_of_rate_le
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[ℱ 0] Y₀) (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {c T : ℝ} (hT : 0 < T)
    (hrate : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      2 * ∫ ω, (X s ω - Y s ω) * (b s ω - b' s ω) ∂P
          + (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal
        ≤ c * ∫ ω, (X s ω - Y s ω) * (X s ω - Y s ω) ∂P) :
    ∫ ω, (X T ω - Y T ω) * (X T ω - Y T ω) ∂P
      ≤ Real.exp (c * T) * ∫ ω, (X₀ ω - Y₀ ω) * (X₀ ω - Y₀ ω) ∂P := by
  have hΔbm : Measurable (Function.uncurry fun ω s => b s ω - b' s ω) := hbm.sub hb'm
  have hΔbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω - b' s ω :=
    hbp.sub hb'p
  have hΔbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω - b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hbm hb'm hbq hb'q
  exact integral_mul_self_le_of_rate_le (isItoLevyProcess_sub h h' hbm hb'm hbq hb'q) 𝒲
    (hX₀.sub hY₀) (hX₀2.sub hY₀2) hΔbm hΔbp hΔbq hT hrate

/-- **The stability estimate under one-sided Lipschitz coefficients.** A drift satisfying the
monotonicity bound `Δx Δb ≤ L |Δx|²` and a diffusion and jump coefficient satisfying
`∑_j |Δσ_j|² ≤ L² |Δx|²` and `∫_E |Δγ|² dν ≤ L² |Δx|²` pointwise give the rate bound with
`c = 2L + 2L²`, hence `𝔼[|ΔX_T|²] ≤ e^{(2L + 2L²)T} 𝔼[|ΔX₀|²]`. -/
theorem integral_sub_mul_self_le_of_lipschitz
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[ℱ 0] Y₀) (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {L : ℝ}
    (hbLip : ∀ s ω, (X s ω - Y s ω) * (b s ω - b' s ω)
      ≤ L * ((X s ω - Y s ω) * (X s ω - Y s ω)))
    (hσLip : ∀ s ω, (∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    (hγLip : ∀ s ω, (∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    {T : ℝ} (hT : 0 < T) :
    ∫ ω, (X T ω - Y T ω) * (X T ω - Y T ω) ∂P
      ≤ Real.exp ((2 * L + 2 * L ^ 2) * T)
        * ∫ ω, (X₀ ω - Y₀ ω) * (X₀ ω - Y₀ ω) ∂P := by
  classical
  have hΔ := isItoLevyProcess_sub h h' hbm hb'm hbq hb'q
  have hΔbm : Measurable (Function.uncurry fun ω s => b s ω - b' s ω) := hbm.sub hb'm
  have hΔbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω - b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hbm hb'm hbq hb'q
  -- the `L²` facts of the difference, at every time of the window
  have hΔ2 : ∀ s : ℝ, 0 ≤ s → MemLp (fun ω => X s ω - Y s ω) 2 P := fun s hs =>
    memLp_two_of_isItoLevyProcess hΔ (hX₀2.sub hY₀2) hΔbm hΔbq hs
  have hsw : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), s ∈ Set.Icc (0 : ℝ) T :=
    ae_restrict_mem measurableSet_Icc
  have hΔbs : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      MemLp (fun ω => b s ω - b' s ω) 2 P :=
    ae_memLp_two_eval (f := fun ω s => b s ω - b' s ω) hΔbm (hΔbq T hT)
  refine integral_sub_mul_self_le_of_rate_le h h' 𝒲 hX₀ hX₀2 hbm hbp hbq hY₀ hY₀2 hb'm hb'p
    hb'q hT ?_
  filter_upwards [hsw, hΔbs] with s hs hΔbs2
  set Q : ℝ := ∫ ω, (X s ω - Y s ω) * (X s ω - Y s ω) ∂P with hQdef
  have hQi : Integrable (fun ω => (X s ω - Y s ω) * (X s ω - Y s ω)) P :=
    (hΔ2 s hs.1).integrable_mul (hΔ2 s hs.1)
  have hQ0 : 0 ≤ Q := integral_nonneg fun ω => mul_self_nonneg _
  -- the drift pairing
  have hdrift : 2 * ∫ ω, (X s ω - Y s ω) * (b s ω - b' s ω) ∂P ≤ 2 * (L * Q) := by
    have h1 : ∫ ω, (X s ω - Y s ω) * (b s ω - b' s ω) ∂P
        ≤ ∫ ω, L * ((X s ω - Y s ω) * (X s ω - Y s ω)) ∂P :=
      integral_mono ((hΔ2 s hs.1).integrable_mul hΔbs2) (hQi.const_mul L) fun ω => hbLip s ω
    rw [integral_const_mul] at h1
    linarith
  -- the diffusion energy
  have hLQ0 : ∀ ω, 0 ≤ L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω)) := fun ω =>
    mul_nonneg (sq_nonneg L) (mul_self_nonneg _)
  have hLQi : Integrable (fun ω => L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))) P :=
    hQi.const_mul _
  have hσmeas : ∀ j : Fin d, Measurable fun ω => (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 := by
    intro j
    have hu : Measurable (Function.uncurry fun ω s => σ s ω j - σ' s ω j) :=
      (h.σ_meas j).sub (h'.σ_meas j)
    have hslice : Measurable fun ω => σ s ω j - σ' s ω j :=
      hu.comp measurable_prodMk_right
    exact hslice.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hsumeq : ∑ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, ∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    (lintegral_finsetSum _ fun j _ => hσmeas j).symm
  obtain ⟨hσle, hσfin⟩ := toReal_lintegral_le_of_le (P := P)
    (f := fun ω => ∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2) hLQi hLQ0 fun ω => hσLip s ω
  have hσeach : ∀ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ := fun j =>
    ne_top_of_le_ne_top hσfin (lintegral_mono fun ω =>
      Finset.single_le_sum (f := fun k : Fin d => (‖σ s ω k - σ' s ω k‖₊ : ℝ≥0∞) ^ 2)
        (fun k _ => by simp) (Finset.mem_univ j))
  have hdiff : (∑ j : Fin d, (∫⁻ ω, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
      ≤ L ^ 2 * Q := by
    rw [← ENNReal.toReal_sum fun j _ => hσeach j, hsumeq]
    rw [hQdef, ← integral_const_mul]
    exact hσle
  -- the jump energy
  obtain ⟨hγle, -⟩ := toReal_lintegral_le_of_le (P := P)
    (f := fun ω => ∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) hLQi hLQ0 fun ω => hγLip s ω
  have hjump : (∫⁻ ω, ∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal ≤ L ^ 2 * Q := by
    rw [hQdef, ← integral_const_mul]
    exact hγle
  linarith

/-- **Uniqueness from the stability estimate.** Two Itô–Lévy processes over the same driver whose
coefficients satisfy the one-sided Lipschitz bounds and whose initial values agree almost surely
agree almost surely at every horizon. -/
theorem ae_eq_of_lipschitz_of_ae_eq_initial
    (h : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN X X₀ b σ γ)
    (h' : LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N ℱ hℱW hℱN Y Y₀ b' σ' γ')
    (𝒲 : D.CrossWitness ℱ)
    (hX₀ : StronglyMeasurable[ℱ 0] X₀) (hX₀2 : MemLp X₀ 2 P)
    (hbm : Measurable (Function.uncurry fun ω s => b s ω))
    (hbp : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b s ω)
    (hbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hY₀ : StronglyMeasurable[ℱ 0] Y₀) (hY₀2 : MemLp Y₀ 2 P)
    (hb'm : Measurable (Function.uncurry fun ω s => b' s ω))
    (hb'p : LevyStochCalc.Probability.ProgressivelyMeasurable ℱ fun ω s => b' s ω)
    (hb'q : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {L : ℝ}
    (hbLip : ∀ s ω, (X s ω - Y s ω) * (b s ω - b' s ω)
      ≤ L * ((X s ω - Y s ω) * (X s ω - Y s ω)))
    (hσLip : ∀ s ω, (∑ j : Fin d, (‖σ s ω j - σ' s ω j‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    (hγLip : ∀ s ω, (∫⁻ e, (‖γ ω s e - γ' ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ≤ ENNReal.ofReal (L ^ 2 * ((X s ω - Y s ω) * (X s ω - Y s ω))))
    (hinit : X₀ =ᵐ[P] Y₀) {T : ℝ} (hT : 0 < T) :
    X T =ᵐ[P] Y T := by
  have hbound := integral_sub_mul_self_le_of_lipschitz h h' 𝒲 hX₀ hX₀2 hbm hbp hbq hY₀ hY₀2
    hb'm hb'p hb'q hbLip hσLip hγLip hT
  have hzero : ∫ ω, (X₀ ω - Y₀ ω) * (X₀ ω - Y₀ ω) ∂P = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hinit] with ω hω
    simp [hω]
  rw [hzero, mul_zero] at hbound
  have hΔ := isItoLevyProcess_sub h h' hbm hb'm hbq hb'q
  have hΔbm : Measurable (Function.uncurry fun ω s => b s ω - b' s ω) := hbm.sub hb'm
  have hΔbq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b s ω - b' s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    LevyStochCalc.Brownian.Ito.lintegral_energy_lt_top_of_bound
      (fun ω s => LevyStochCalc.Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hbm hb'm hbq hb'q
  have hT2 : MemLp (fun ω => X T ω - Y T ω) 2 P :=
    memLp_two_of_isItoLevyProcess hΔ (hX₀2.sub hY₀2) hΔbm hΔbq hT.le
  have hTi : Integrable (fun ω => (X T ω - Y T ω) * (X T ω - Y T ω)) P :=
    hT2.integrable_mul hT2
  have hTnn : 0 ≤ᵐ[P] fun ω => (X T ω - Y T ω) * (X T ω - Y T ω) :=
    Eventually.of_forall fun ω => mul_self_nonneg _
  have hTz : ∫ ω, (X T ω - Y T ω) * (X T ω - Y T ω) ∂P = 0 :=
    le_antisymm hbound (integral_nonneg fun ω => mul_self_nonneg _)
  have := (integral_eq_zero_iff_of_nonneg_ae hTnn hTi).mp hTz
  filter_upwards [this] with ω hω
  have : (X T ω - Y T ω) * (X T ω - Y T ω) = 0 := hω
  have hz : X T ω - Y T ω = 0 := by
    exact mul_self_eq_zero.mp this
  linarith

end Stability

end LevyStochCalc.Ito.Stability
