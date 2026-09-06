/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedProcessQuadVar

/-!
# The difference isometry of the compensated integral process

For two integrands `φ₁, φ₂`, the `L²` integral processes satisfy
`∫⁻ ‖F₁(t) − F₂(t)‖² = ∫⁻∫⁻_{[0,t]}∫⁻ ‖φ₁ − φ₂‖²`: the stage approximants of the two
integrands are refined to a common dyadic grid, where the difference isometry of mark-step
integrands holds at every time, and both sides pass to the limit in `L²`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]
variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : PoissonRandomMeasure P ν) (φ₁ φ₂ : Ω → ℝ → E → ℝ)
  (h_meas₁ : Measurable (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2))
  (h_meas₂ : Measurable (fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2))
  (h_progMeas₁ : ∀ t : ℝ,
    @StronglyMeasurable (Ω × ℝ × E) ℝ _
      (@Prod.instMeasurableSpace Ω (ℝ × E) ((naturalFiltration N).seq t) inferInstance)
      (fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2))
  (h_progMeas₂ : ∀ t : ℝ,
    @StronglyMeasurable (Ω × ℝ × E) ℝ _
      (@Prod.instMeasurableSpace Ω (ℝ × E) ((naturalFiltration N).seq t) inferInstance)
      (fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2))
  (h_sq₁ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (h_sq₂ : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

/-- The difference isometry of the stage approximants of two integrands at every time. -/
lemma stageIntegral_sub_lintegral_sq {t : ℝ} (ht : 0 ≤ t) (n : ℕ) :
    ∫⁻ ω, (‖stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ p, (‖stageEval N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
          - stageEval N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p‖₊ : ℝ≥0∞) ^ 2
          ∂(horizonMeasure ν P t) := by
  have hA₁ := master_adapted N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n
  have hA₂ := master_adapted N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n
  have h₁ := le_max_left (master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).1
    (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).1
  have h₂ := le_max_right (master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).1
    (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).1
  have hiso := ((master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.dyadicRefine
    h₁).lintegral_integral_sub_sq_at N
    ((master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.dyadicRefine h₂) (hA₁.dyadicRefine h₁)
    (hA₂.dyadicRefine h₂) ht
  have hm : Measurable (fun p : Ω × ℝ × E =>
      (‖(master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval p.2.1 p.2.2 p.1
        - (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval p.2.1 p.2.2 p.1‖₊ : ℝ≥0∞) ^ 2) :=
    (ENNReal.continuous_coe.measurable.comp
      ((master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval_measurable.sub
        (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval_measurable).nnnorm).pow_const 2
  have hL : ∫⁻ ω, (‖stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖((master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.dyadicRefine h₁).integral N t ω
        - ((master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.dyadicRefine h₂).integral N t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [(master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.integral_dyadicRefine N h₁ hA₁ t,
      (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.integral_dyadicRefine N h₂ hA₂ t]
      with ω hω₁ hω₂
    simp only [stageIntegral]
    rw [hω₁, hω₂]
  rw [hL, hiso]
  unfold stageEval
  rw [lintegral_horizonMeasure t (fun ω s e =>
    (‖(master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval s e ω
      - (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm]
  refine lintegral_congr fun ω => ?_
  rw [← lintegral_swap_es (fun ω s e =>
    (‖(master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval s e ω
      - (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval s e ω‖₊ : ℝ≥0∞) ^ 2) hm ω]
  refine lintegral_congr fun e => setLIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  rw [(master N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).2.eval_dyadicRefine h₁,
    (master N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).2.eval_dyadicRefine h₂]

/-- The difference isometry of the `L²` integral processes of two integrands. -/
theorem process_sub_lintegral_sq {t : ℝ} (ht : 0 < t) :
    ∫⁻ ω, (‖process N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
        - process N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, ∫⁻ e,
          (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  have hI : Tendsto (fun n => eLpNorm
      ((fun ω => stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
        - stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
      - fun ω => process N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
        - process N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P) atTop (𝓝 0) := by
    have h₁ := stageIntegral_tendsto_process N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t
    have h₂ := stageIntegral_tendsto_process N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using h₁.add h₂) (Eventually.of_forall fun n => bot_le)
      (Eventually.of_forall fun n => ?_)
    calc eLpNorm ((fun ω => stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
            - stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
          - fun ω => process N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
            - process N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P
        = eLpNorm ((fun ω => stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
            - process N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω)
          - fun ω => stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω
            - process N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω) 2 P := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun ω => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le
          ((memLp_stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t).sub
            (process_memLp N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t)).aestronglyMeasurable
          ((memLp_stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t).sub
            (process_memLp N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).aestronglyMeasurable (by norm_num)
  have hL := LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (gₙ := fun n ω => stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t ω
      - stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t ω)
    (g := fun ω => process N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t ω
      - process N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t ω)
    (fun n => ((memLp_stageIntegral N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n t).sub
      (memLp_stageIntegral N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n t)).aestronglyMeasurable)
    ((process_memLp N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t).sub
      (process_memLp N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).aestronglyMeasurable
    ((process_memLp N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t).sub
      (process_memLp N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t)).eLpNorm_ne_top hI
  have hE : Tendsto (fun n => eLpNorm
      ((fun p => stageEval N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
        - stageEval N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
      - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2) 2 (horizonMeasure ν P t))
      atTop (𝓝 0) := by
    have h₁ := stageEval_tendsto N φ₁ h_meas₁ h_progMeas₁ h_sq₁ t
    have h₂ := stageEval_tendsto N φ₂ h_meas₂ h_progMeas₂ h_sq₂ t
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa using h₁.add h₂) (Eventually.of_forall fun n => bot_le)
      (Eventually.of_forall fun n => ?_)
    calc eLpNorm ((fun p => stageEval N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
            - stageEval N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
          - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2) 2
          (horizonMeasure ν P t)
        = eLpNorm ((stageEval N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n
            - fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2)
          - (stageEval N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n
            - fun p : Ω × ℝ × E => φ₂ p.1 p.2.1 p.2.2)) 2 (horizonMeasure ν P t) := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun p => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le
          ((measurable_stageEval N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
            h_meas₁).aestronglyMeasurable
          ((measurable_stageEval N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n).sub
            h_meas₂).aestronglyMeasurable (by norm_num)
  have hR := LevyStochCalc.Brownian.Ito.tendsto_lintegral_nnnorm_sq_of_eLpNorm
    (gₙ := fun n p => stageEval N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n p
      - stageEval N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n p)
    (g := fun p : Ω × ℝ × E => φ₁ p.1 p.2.1 p.2.2 - φ₂ p.1 p.2.1 p.2.2)
    (fun n => ((measurable_stageEval N φ₁ h_meas₁ h_progMeas₁ h_sq₁ n).sub
      (measurable_stageEval N φ₂ h_meas₂ h_progMeas₂ h_sq₂ n)).aestronglyMeasurable)
    (h_meas₁.sub h_meas₂).aestronglyMeasurable
    ((memLp_phi_horizon φ₁ h_meas₁ h_sq₁ ht).sub
      (memLp_phi_horizon φ₂ h_meas₂ h_sq₂ ht)).eLpNorm_ne_top hE
  simp_rw [stageIntegral_sub_lintegral_sq N φ₁ φ₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂ h_sq₁
    h_sq₂ ht.le] at hL
  rw [tendsto_nhds_unique hL hR]
  exact lintegral_horizonMeasure t (fun ω s e => (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2)
    ((ENNReal.continuous_coe.measurable.comp (h_meas₁.sub h_meas₂).nnnorm).pow_const 2)

end LevyStochCalc.Poisson.Compensated
