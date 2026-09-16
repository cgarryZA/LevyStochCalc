/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.TruncatedContinuousPart
import LevyStochCalc.Ito.AtomJumpRelation

/-!
# The splitting of a path with remainder

A path satisfying the jump-diffusion integral equation is, at every nonnegative time, the sum of
a vector Itô process with diffusion `σ` and drift `continuousDriftLeftAt`, the pathwise sum of
the jumps carried by a mark set of finite intensity and the compensated integral of the
left-limit jump coefficient cut to the complement of that set — the *remainder* — so that across
an arrival time carrying a mark of the set the path jumps by the jump coefficient read at its
left limit plus the jump of the remainder.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path`
  — the splitting with remainder at a fixed nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path` — the
  same identity almost surely at all nonnegative times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, step (II).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Poisson.Compensated

universe u v

section Remainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  (coeffs : Setting.JumpDiffusionCoeffs n d E)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
  (x₀ : Fin n → ℝ) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (Xp s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (Xp s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (Xp s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (Xp p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (Xp s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
    coeffs.γ p.2.1 (leftLimPathAt Xp p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable ℱ
    fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt Xp s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hγmL hγpL hγqL in
/-- **The splitting of a path satisfying the integral equation, with remainder, at a fixed
time.** At every nonnegative time a right-continuous-with-left-limits path satisfying the
equation is almost surely the sum of the vector Itô process with diffusion `σ` and drift
`continuousDriftLeftAt`, the left-limit jump sum over a mark set of finite intensity, and the
compensated integral of the left-limit jump coefficient cut to the complement of that set. -/
theorem eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hXpcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeftAt coeffs ν Xp A) t ω i
          + jumpSumLeftAt coeffs N Xp A t ω i
          + stochasticIntegral N ℱ hℱN
              (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
              (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
              (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') t ω := by
  classical
  have hzeroCI : ∀ (ψ : Ω → ℝ → E → ℝ)
      (h1 : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      (h2 : Probability.MarkedProgressivelyMeasurable ℱ ψ)
      (h3 : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      ∀ᵐ ω ∂P, stochasticIntegral N ℱ hℱN ψ h1 h2 h3 0 ω = 0 := fun ψ h1 h2 h3 => by
    filter_upwards [stochasticIntegral_ae_eq_process N ℱ hℱN ψ h1 h2 h3 0,
      process_ae_zero_of_nonpos N ℱ hℱN ψ h1 h2 h3 (le_refl (0 : ℝ))] with ω h1 h2
    rw [h1, h2]
    rfl
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    filter_upwards [hSDE 0 le_rfl,
      MeasureTheory.ae_all_iff.mpr fun i => hzeroCI _ (hγm i) (hγp i) (hγq i),
      MeasureTheory.ae_all_iff.mpr fun i => hzeroCI _ (measurable_markCut (hγmL i) hA.compl)
        ((hγpL i).indicator_mark hA.compl) (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT')]
      with ω hω hz hzR
    intro i
    rw [hω i, hz i, hzR i,
      multidimIntegral_eq_vectorItoMartingaleAt coeffs Xp ℱ hℱW hσm hσp hσq i 0 ω]
    simp [LevyStochCalc.Brownian.Ito.vectorItoProcess, jumpSumLeftAt_zero]
  · have hcong : ∀ i : Fin n, ∀ᵐ ω ∂P,
        stochasticIntegral N ℱ hℱN (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = stochasticIntegral N ℱ hℱN (fun ω s e => coeffs.γ s (Xp s ω) e i)
            (hγm i) (hγp i) (hγq i) t ω := fun i =>
      compensatedIntegral_congr_of_countable_ne N hℱN (fun s x e => coeffs.γ s x e i)
        (ae_countable_setOf_pos_ne_leftLimPathAt Xp hXpcadlag) (hγmL i) (hγm i) (hγpL i)
        (hγp i) (hγqL i) (hγq i) hpos
    have hsplitCI : ∀ i : Fin n, ∀ᵐ ω ∂P,
        stochasticIntegral N ℱ hℱN (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = stochasticIntegral N ℱ hℱN
              (markCut A fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
              (measurable_markCut (hγmL i) hA) ((hγpL i).indicator_mark hA)
              (fun T' hT' => sq_markCut (hγqL i) A T' hT') t ω
            + stochasticIntegral N ℱ hℱN
              (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
              (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
              (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') t ω := fun i =>
      LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl N ℱ hℱN _ (hγmL i)
        (hγpL i) (hγqL i) hA t
    have hpathA : ∀ i : Fin n, ∀ᵐ ω ∂P,
        stochasticIntegral N ℱ hℱN
            (markCut A fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (measurable_markCut (hγmL i) hA) ((hγpL i).indicator_mark hA)
            (fun T' hT' => sq_markCut (hγqL i) A T' hT') t ω
          = jumpSumLeftAt coeffs N Xp A t ω i
            - ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i
                ∂(LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [JumpFormula.stochasticIntegral_ae_eq_pathwise_of_zeroExtPos N ℱ hℱN
        (markCut A fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
        (measurable_markCut (hγmL i) hA) ((hγpL i).indicator_mark hA)
        (fun T' hT' => sq_markCut (hγqL i) A T' hT') hA
        (JumpFormula.markedPredictable_zeroExtPos_markCut (hpredL i) hA) hAν
        (fun ω s e he => by simp [markCut, he]) hpos] with ω hω
      rw [hω]
      have h1 : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          markCut A (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) ω q.1 q.2 ∂(N.N ω)
          = jumpSumLeftAt coeffs N Xp A t ω i :=
        setIntegral_congr_fun (measurableSet_Ioc.prod hA) fun q hq => by
          simp [markCut, hq.2]
      have h2 : ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
          markCut A (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) ω q.1 q.2
            ∂(LevyStochCalc.Poisson.referenceIntensity ν)
          = ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i
              ∂(LevyStochCalc.Poisson.referenceIntensity ν) :=
        setIntegral_congr_fun (measurableSet_Ioc.prod hA) fun q hq => by
          simp [markCut, hq.2]
      rw [h1, h2]
    have hwinL : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2 i)
          (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [JumpFormula.ae_integrableOn_window_of_zeroExtPos N hℱN hA hAν t (hpredL i)
        (hγmL i) (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
          (fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) (hγmL i) (hγqL i)
          (A := A) hpos)] with ω hω
      exact hω.2
    have hμint : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun s => coeffs.μ s (Xp s ω) i) (Set.Icc (0 : ℝ) t) volume := by
      intro i
      have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        ((ENNReal.continuous_coe.measurable.comp (hμm i).nnnorm).pow_const
          2).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      filter_upwards [ae_lt_top' hmeas.aemeasurable (hμq i t hpos).ne] with ω hω
      exact integrableOn_Icc_of_lintegral_sq_lt_top
        ((hμm i).comp measurable_prodMk_left).aestronglyMeasurable hω
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [hSDE t ht, hcong i, hsplitCI i, hpathA i, hwinL i, hμint i]
      with ω hω hc hs hp hw hm
    obtain ⟨heq, hcint⟩ :=
      integral_window_eq_and_integrableOn
        (fun s e => coeffs.γ s (leftLimPathAt Xp s ω) e i) hw
    have hd : ∫ s in Set.Icc (0 : ℝ) t, continuousDriftLeftAt coeffs ν Xp A i ω s ∂volume
        = (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t,
              (∫ e in A, coeffs.γ s (leftLimPathAt Xp s ω) e i ∂ν) ∂volume :=
      integral_sub hm hcint
    rw [hω i, ← hc, hs, hp,
      multidimIntegral_eq_vectorItoMartingaleAt coeffs Xp ℱ hℱW hσm hσp hσq i t ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    rw [hd, heq]
    ring

include hγmL hγpL hγqL in
/-- **The splitting with remainder at all nonnegative times.** For a right-continuous path
satisfying the equation and a right-continuous modification `V` of the vector Itô process with
diffusion `σ` and drift `continuousDriftLeftAt`, almost surely the path is at every nonnegative
time the sum of `V`, the left-limit jump sum over the mark set and the remainder. -/
theorem ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hXpcadlag : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Xp s ω) (𝓝[>] t) (𝓝 (Xp t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L))
    (hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (Xp s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (Xp s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (Xp s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i))
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Xp s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (Xp s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (Xp s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeftAt coeffs ν Xp A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i
        + stochasticIntegral N ℱ hℱN
            (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
            (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') t ω := by
  have hwin := ae_forall_integrableOn_windowLeftAt coeffs N Xp ℱ hℱN hA hAν hpredL hγmL hγqL
  have hRcad : ∀ i : Fin n, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Tendsto (fun s => stochasticIntegral N ℱ hℱN
          (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
          (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
          (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') s ω) (𝓝[>] t)
        (𝓝 (stochasticIntegral N ℱ hℱN
          (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
          (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
          (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') t ω)) := by
    intro i
    filter_upwards [stochasticIntegral_cadlag N ℱ hℱN
      (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
      (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
      (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT')] with ω hω t
    exact (hω t).1
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      Z t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i
        + stochasticIntegral N ℱ hℱN
            (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
            (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') t ω := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine ae_forall_eq_of_ae_rat (P := P) (Y := fun s ω => Z s ω i)
      (Z := fun s ω => V s ω i + jumpSumLeftAt coeffs N Xp A s ω i
        + stochasticIntegral N ℱ hℱN
            (markCut Aᶜ fun ω s e => coeffs.γ s (leftLimPathAt Xp s ω) e i)
            (measurable_markCut (hγmL i) hA.compl) ((hγpL i).indicator_mark hA.compl)
            (fun T' hT' => sq_markCut (hγqL i) Aᶜ T' hT') s ω) ?_ ?_ ?_
    · intro q hq
      filter_upwards [eq_vectorItoProcess_add_jumpSumLeftAt_add_remainder_of_path coeffs N Xp x₀
        ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL hγqL Z hXpcadlag hSDE hA hAν hpredL hμm hμq
        hq, hVae (q : ℝ) hq] with ω h1 h2
      rw [h1 i, h2 i]
    · filter_upwards [hZright] with ω hω t ht
      exact ((continuous_apply i).tendsto (Z t ω)).comp (hω t ht)
    · filter_upwards [hVright, hwin, hRcad i] with ω hVω hwω hRω t ht
      exact ((hVω t ht i).add (tendsto_jumpSumLeftAt_nhdsWithin_Ioi coeffs N Xp hA (hγmL i)
        (fun T => hwω T i) t)).add (hRω t)
  filter_upwards [key] with ω hω t ht i
  exact hω i t ht

end Remainder

section JumpWithRemainder

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

/-- **The jump of a path across an arrival time, with remainder.** If a path is, at every
nonnegative time, the sum of a continuous process, the left-limit jump sum over a mark set of
finite intensity and a family of processes with left limits, then almost surely its increment
across each arrival time in the window is the jump coefficient read at the left limit there, for
the mark carried at that time, plus the jump of the third summand. -/
theorem ae_exists_atomEnum_jump_eq_gamma_add_remainder
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (Xp : ℝ → Ω → Fin n → ℝ) (A : Set E) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    (V : ℝ → Ω → Fin n → ℝ) (hVc : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (R : Fin n → ℝ → Ω → ℝ)
    (hRl : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), ∃ L : ℝ, Tendsto (fun s => R i s ω) (𝓝[<] t) (𝓝 L))
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Xp t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i + R i t ω) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A) ∧
      (∀ g : ℝ × E → ℝ,
        ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ (j : Fin K) (i : Fin n),
        Xp (θ j) ω i
          = leftLimPathAt Xp (θ j) ω i + coeffs.γ (θ j) (leftLimPathAt Xp (θ j) ω) (ε j) i
            + (R i (θ j) ω - Function.leftLim (fun s => R i s ω) (θ j)) := by
  classical
  filter_upwards [ae_exists_atomEnum_jumpSumLeftAt_eq_sum coeffs N Xp A hA hAν T, hVc, hRl,
    hsplit] with ω hstep hVω hRω hsp
  obtain ⟨K, θ, ε, hmono, hmem, hg, hsum⟩ := hstep
  refine ⟨K, θ, ε, hmono, hmem, hg, fun j i => ?_⟩
  -- each remainder converges to its left limit
  have hRlim : ∀ i' : Fin n, Tendsto (fun s => R i' s ω) (𝓝[<] (θ j))
      (𝓝 (Function.leftLim (fun s => R i' s ω) (θ j))) := by
    intro i'
    obtain ⟨L, hL⟩ := hRω i' (θ j)
    rw [leftLim_eq_of_tendsto hL]
    exact hL
  -- the left limit of the path at the arrival time
  have hlim : ∀ i' : Fin n, Tendsto (fun t => Xp t ω i') (𝓝[<] (θ j))
      (𝓝 (V (θ j) ω i' + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
        coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i'
        + Function.leftLim (fun s => R i' s ω) (θ j))) := by
    intro i'
    have hVlim : Tendsto (fun t => V t ω i') (𝓝[<] (θ j)) (𝓝 (V (θ j) ω i')) :=
      (((continuous_apply i').comp hVω).tendsto (θ j)).mono_left nhdsWithin_le_nhds
    have hstepl := tendsto_nhdsLT_sum_filter_le θ
      (fun k => coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i') (θ j)
    refine ((hVlim.add hstepl).add (hRlim i')).congr' ?_
    filter_upwards [Ioo_mem_nhdsLT (hmem j).1.1] with t ht
    rw [hsp t ht.1.le i', hsum t (le_trans ht.2.le (hmem j).1.2) i']
  have hleft : leftLimPathAt Xp (θ j) ω
      = fun i' => V (θ j) ω i' + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
          coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i'
          + Function.leftLim (fun s => R i' s ω) (θ j) :=
    leftLimPathAt_eq_of_tendsto hlim
  have hsplitj : (Finset.univ.filter fun k => θ k ≤ θ j)
      = insert j (Finset.univ.filter fun k => θ k < θ j) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      hmono.le_iff_le, hmono.lt_iff_lt]
    exact le_iff_eq_or_lt
  have hnotmem : j ∉ Finset.univ.filter fun k => θ k < θ j := by simp
  have hleft_i : leftLimPathAt Xp (θ j) ω i
      = V (θ j) ω i + ∑ k ∈ Finset.univ.filter fun k => θ k < θ j,
          coeffs.γ (θ k) (leftLimPathAt Xp (θ k) ω) (ε k) i
          + Function.leftLim (fun s => R i s ω) (θ j) := by
    rw [hleft]
  rw [hsp (θ j) (hmem j).1.1.le i, hsum (θ j) (hmem j).1.2 i, hsplitj,
    Finset.sum_insert hnotmem, hleft_i]
  ring

end JumpWithRemainder

end LevyStochCalc.Ito.JumpSplitting
