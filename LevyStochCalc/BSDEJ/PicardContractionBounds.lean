/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardContractionNorm
import LevyStochCalc.BSDEJ.YoungLipschitz
import LevyStochCalc.Ito.StabilityEstimate

/-!
# Energy and pointwise bounds behind the Picard contraction

The energy of a process on a horizon is at most the length of the horizon times its `S²`
seminorm, the energy of a difference of two processes is finite when both energies are, and
freezing a process at the horizon leaves its energy there unchanged. At almost every time of the
horizon, twice the pairing of a process against the difference of two evaluations of a Lipschitz
generator is at most `β / 2` times the second moment of the process plus `6 L² / β` times the
sample energy density of the differenced arguments, and the real-variable core turns a weighted
energy dominated by such a pairing into a contraction by the factor `6 L² / β`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}

/-- The energy of a process on a horizon is at most the length of the horizon times its `S²`
seminorm. -/
theorem energy_le_of_biSup {Y : ℝ → Ω → ℝ} :
    Brownian.Ito.energy P T (fun ω s => Y s ω)
      ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  have hb : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T,
          (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) s hs
  refine hb.trans ?_
  rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  exact le_of_eq (mul_comm _ _)

/-- The energy of a difference of two processes is finite when both energies are. -/
theorem energy_sub_ne_top {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂)) (h₁ : Brownian.Ito.energy P T H₁ ≠ ⊤)
    (h₂ : Brownian.Ito.energy P T H₂ ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) ≠ ⊤ := by
  have hA : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    hm₁.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hB : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    hm₂.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hA' : ∀ ω : Ω, Measurable fun s : ℝ => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    hA.comp (measurable_const.prodMk measurable_id)
  have hstep : Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s)
      ≤ 2 * (Brownian.Ito.energy P T H₁ + Brownian.Ito.energy P T H₂) := by
    have hpt : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
      lintegral_mono fun ω => lintegral_mono fun s =>
        Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _
    refine hpt.trans (le_of_eq ?_)
    have hin : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume
        = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
      intro ω
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hA' ω)]
    have hoA : Measurable fun ω : Ω =>
        ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := hA.lintegral_prod_right'
    rw [lintegral_congr hin, lintegral_const_mul' _ _ (by norm_num),
      lintegral_add_left hoA]
    rfl
  exact ne_top_of_le_ne_top (by finiteness) hstep

/-- A drift vanishing off a horizon on which it has finite energy is square integrable on every
horizon. -/
theorem drift_sq_int_global {b : Ω → ℝ → ℝ}
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (Brownian.Ito.energy_le_of_vanishing hbz T') (lt_top_iff_ne_top.mpr hbq)

/-- The negative of a drift vanishing off a horizon of finite energy is square integrable on
every horizon. -/
theorem neg_drift_sq_int_global {b : Ω → ℝ → ℝ}
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖-b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  simpa only [nnnorm_neg] using drift_sq_int_global hbz hbq T'

/-- Freezing a process at the horizon does not change its energy there. -/
theorem energy_clampT {Y : ℝ → Ω → ℝ} :
    Brownian.Ito.energy P T (fun ω s => clampT T Y s ω)
      = Brownian.Ito.energy P T (fun ω s => Y s ω) :=
  lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    simp only [clampT_apply, min_eq_left hs.2]

end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

/-- At almost every time of the horizon, twice the pairing of a process against the difference
of two evaluations of a Lipschitz generator is at most `β / 2` times the second moment of the
process plus `6 L² / β` times the sample energy density of the differenced arguments. -/
theorem ae_two_mul_integral_mul_sub_le
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hβ : 0 < β) {X : ℝ → Ω → ℝ} {b₁ b₂ : Ω → ℝ → ℝ}
    {Y'₁ Y'₂ : ℝ → Ω → ℝ} {Z'₁ Z'₂ : ℝ → Ω → (Fin d → ℝ)} {U'₁ U'₂ : ℝ → Ω → E → ℝ}
    {ΔY : ℝ → Ω → ℝ} {ΔZ : ℝ → Ω → (Fin d → ℝ)} {ΔU : ℝ → Ω → E → ℝ}
    (hΔY : ∀ s ω, ΔY s ω = Y'₁ s ω - Y'₂ s ω)
    (hΔZ : ∀ s ω j, ΔZ s ω j = Z'₁ s ω j - Z'₂ s ω j)
    (hΔU : ∀ s ω e, ΔU s ω e = U'₁ s ω e - U'₂ s ω e)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁m : Measurable (Function.uncurry b₁)) (hb₂m : Measurable (Function.uncurry b₂))
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ ω s - b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    (hΔYm : Measurable (Function.uncurry fun ω s => ΔY s ω))
    (hΔZm : ∀ j, Measurable (Function.uncurry fun ω s => ΔZ s ω j))
    (hΔUm : Measurable fun p : Ω × ℝ × E => ΔU p.2.1 p.1 p.2.2)
    (hin : wNorm P ν β T ΔY ΔZ ΔU ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      2 * ∫ ω, X s ω * (b₁ ω s - b₂ ω s) ∂P
        ≤ β / 2 * (∫ ω, X s ω * X s ω ∂P)
          + 6 * L ^ 2 / β * (∫⁻ ω, density ν ΔY ΔZ ΔU ω s ∂P).toReal := by
  classical
  have hg₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      b₁ ω s = f s (Y'₁ s ω) (Z'₁ s ω) (U'₁ s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc (0 : ℝ) T))
        (ν := P)).quasiMeasurePreserving.ae hb₁)
  have hg₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      b₂ ω s = f s (Y'₂ s ω) (Z'₂ s ω) (U'₂ s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc (0 : ℝ) T))
        (ν := P)).quasiMeasurePreserving.ae hb₂)
  have hdens := ae_lintegral_density_ne_top hβ.le hΔYm hΔZm hΔUm hin
  have hX2 := Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => X s ω) hXm hXq
  have hb2 := Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b₁ ω s - b₂ ω s)
    (hb₁m.sub hb₂m) hbq
  filter_upwards [hg₁, hg₂, hdens, hX2, hb2] with s hs₁ hs₂ hdf hXs hbs
  have hdm := measurable_density_slice (ν := ν) hΔYm hΔZm hΔUm s
  have hdω := ae_lt_top hdm hdf
  have hJ : ∀ᵐ ω ∂P, (∫⁻ e, (‖ΔU s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ≠ ⊤ := by
    filter_upwards [hdω] with ω hω
    simp only [density] at hω
    exact (ENNReal.add_ne_top.mp hω.ne).2
  have hptw : ∀ᵐ ω ∂P, 2 * (X s ω * (b₁ ω s - b₂ ω s))
      ≤ β / 2 * (X s ω * X s ω) + 6 * L ^ 2 / β * (density ν ΔY ΔZ ΔU ω s).toReal := by
    filter_upwards [hs₁, hs₂, hJ] with ω h1 h2 hJω
    have hueq : (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        = ∫⁻ e, (‖ΔU s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
      lintegral_congr fun e => by rw [hΔU s ω e]
    have hu : (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ≠ ⊤ := by
      rw [hueq]; exact hJω
    have key := Contraction.two_mul_mul_generator_sub_le hβ hL hlip s (Y'₁ s ω) (Y'₂ s ω)
      (Z'₁ s ω) (Z'₂ s ω) (U'₁ s ω) (U'₂ s ω) hu (X s ω)
    have hsq2 : X s ω ^ 2 = X s ω * X s ω := pow_two _
    have hdens_eq : (density ν ΔY ΔZ ΔU ω s).toReal
        = (Y'₁ s ω - Y'₂ s ω) ^ 2 + (∑ j, (Z'₁ s ω j - Z'₂ s ω j) ^ 2)
          + (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal := by
      rw [toReal_density_apply hJω]
      simp only [hΔY, hΔZ, hΔU]
    rw [h1, h2, hdens_eq]
    linarith [key]
  have hint1 : Integrable (fun ω => 2 * (X s ω * (b₁ ω s - b₂ ω s))) P :=
    (hXs.integrable_mul hbs).const_mul 2
  have hintA : Integrable (fun ω => β / 2 * (X s ω * X s ω)) P :=
    (hXs.integrable_mul hXs).const_mul _
  have hintB : Integrable
      (fun ω => 6 * L ^ 2 / β * (density ν ΔY ΔZ ΔU ω s).toReal) P :=
    (integrable_toReal_of_lintegral_ne_top hdm.aemeasurable hdf).const_mul _
  have hmono := integral_mono_ae hint1 (hintA.add hintB) hptw
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul, integral_add hintA hintB, integral_const_mul, integral_const_mul,
    integral_toReal hdm.aemeasurable hdω] at hmono
  exact hmono

end Pointwise

section RealCore

/-- The real-variable core of the Picard contraction: a weighted energy dominated by the
weighted pairing, itself dominated by the Young combination, contracts by the factor `c`. -/
theorem contraction_real_core {A Gout Gin V : ℝ → ℝ} {β c T : ℝ} (hβ : 2 ≤ β)
    (hA0 : ∀ s, 0 ≤ A s)
    (hAint : IntegrableOn (fun s => Real.exp (β * s) * A s) (Set.Icc (0 : ℝ) T))
    (hGoutint : IntegrableOn (fun s => Real.exp (β * s) * Gout s) (Set.Icc (0 : ℝ) T))
    (hGinint : IntegrableOn (fun s => Real.exp (β * s) * Gin s) (Set.Icc (0 : ℝ) T))
    (hVint : IntegrableOn (fun s => Real.exp (β * s) * V s) (Set.Icc (0 : ℝ) T))
    (hL : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (Gout s + (β - 1) * A s)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * V s)
    (hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), V s ≤ β / 2 * A s + c * Gin s) :
    ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gout s
      ≤ c * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gin s := by
  have hM0 : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s :=
    setIntegral_nonneg measurableSet_Icc fun s _ => mul_nonneg (Real.exp_nonneg _) (hA0 s)
  have h1 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (Gout s + (β - 1) * A s)
      = (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gout s)
        + (β - 1) * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s := by
    have hc1 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Real.exp (β * s) * (Gout s + (β - 1) * A s)
          = Real.exp (β * s) * Gout s + (β - 1) * (Real.exp (β * s) * A s) :=
      Eventually.of_forall fun s => by ring
    rw [integral_congr_ae hc1, integral_add hGoutint (hAint.const_mul (β - 1)),
      integral_const_mul]
  have hRHSint : IntegrableOn
      (fun s => Real.exp (β * s) * (β / 2 * A s + c * Gin s)) (Set.Icc (0 : ℝ) T) := by
    refine Integrable.congr ((hAint.const_mul (β / 2)).add (hGinint.const_mul c)) ?_
    filter_upwards with s
    simp only [Pi.add_apply]
    ring
  have h2 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * V s
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β / 2 * A s + c * Gin s) := by
    refine integral_mono_ae hVint hRHSint ?_
    filter_upwards [hpt] with s hs
    exact mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
  have h3 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β / 2 * A s + c * Gin s)
      = β / 2 * (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s)
        + c * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gin s := by
    have hc3 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Real.exp (β * s) * (β / 2 * A s + c * Gin s)
          = β / 2 * (Real.exp (β * s) * A s) + c * (Real.exp (β * s) * Gin s) :=
      Eventually.of_forall fun s => by ring
    rw [integral_congr_ae hc3, integral_add (hAint.const_mul (β / 2)) (hGinint.const_mul c),
      integral_const_mul, integral_const_mul]
  rw [h1] at hL
  have hfin := hL.trans (h2.trans_eq h3)
  nlinarith [hfin, mul_nonneg (by linarith : (0 : ℝ) ≤ β - 2) hM0]

end RealCore

end LevyStochCalc.BSDEJ.Solves
