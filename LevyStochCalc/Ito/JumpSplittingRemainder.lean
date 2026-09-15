/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.TruncatedContinuousPart
import LevyStochCalc.Ito.AtomJumpRelation
import LevyStochCalc.Ito.StochasticIntegralLimit

/-!
# The jump of a solution across an arrival time

A path satisfying the jump-diffusion integral equation is, at every nonnegative time, the sum of
a vector Itô process, the pathwise sum of the jumps carried by a mark set of finite intensity and
the compensated integral of the jump coefficient cut to the complement of that set — the
*remainder*. No support restriction on the jump coefficient enters: the remainder carries the
jumps outside the mark set.

Across an arrival time carrying a mark of the set, the path therefore jumps by the jump
coefficient read at its left limit plus the jump of the remainder. Along an exhausting sequence
of mark sets the remainders vanish uniformly on every bounded window, by Doob's `L²` maximal
inequality against the Itô–Lévy isometry, so the jump of the path at such an arrival time is
exactly the jump coefficient.

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

section Uniform

open LevyStochCalc.Probability

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- The second moment at the horizon of the compensated integral of an integrand cut to the
complement of a spanning set of the intensity tends to zero along the spanning sequence. -/
theorem tendsto_lintegral_sq_stochasticIntegral_markCut_spanningSets_compl {T : ℝ}
    (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (spanningSets ν m)ᶜ φ)
        (measurable_markCut h_meas (measurableSet_spanningSets ν m).compl)
        (h_progMeas.indicator_mark (measurableSet_spanningSets ν m).compl)
        (fun T' hT' => sq_markCut h_sq (spanningSets ν m)ᶜ T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hanti : Antitone fun m => (spanningSets ν m)ᶜ :=
    fun a b hab => Set.compl_subset_compl.mpr (monotone_spanningSets ν hab)
  have hnull : ν (⋂ m, (spanningSets ν m)ᶜ) = 0 := by
    rw [← Set.compl_iUnion, iUnion_spanningSets, Set.compl_univ, measure_empty]
  have h := LevyStochCalc.Ito.IntegralLimit.tendsto_lintegral_sq_stochasticIntegral_markCut_compl_of_antitone
    N ℱ hℱ φ h_meas h_progMeas h_sq (fun m => (spanningSets ν m)ᶜ)
    (fun m => (measurableSet_spanningSets ν m).compl) hanti hnull hT
  refine h.congr fun m => lintegral_congr_ae ?_
  filter_upwards [LevyStochCalc.Ito.BigJump.stochasticIntegral_markCut_add_compl N ℱ hℱ φ h_meas
    h_progMeas h_sq (measurableSet_spanningSets ν m) T] with ω hω
  have hcc : markCut (spanningSets ν m)ᶜᶜ φ = markCut (spanningSets ν m) φ := by
    rw [compl_compl]
  rw [LevyStochCalc.Ito.BigJump.stochasticIntegral_congr_fun N ℱ hℱ _ _ _
    (measurable_markCut h_meas (measurableSet_spanningSets ν m))
    (h_progMeas.indicator_mark (measurableSet_spanningSets ν m))
    (fun T' hT' => sq_markCut h_sq (spanningSets ν m) T' hT') hcc T, hω, sub_add_cancel_left,
    nnnorm_neg]

omit h_meas h_progMeas h_sq in
/-- **The small-jump remainders of a finite family vanish uniformly on a window along a common
subsequence.** Along a subsequence of the spanning sets of the intensity, the compensated
integrals of each integrand of the family cut to their complements are almost surely eventually
smaller than any given bound at every time of `[0, T]`. -/
theorem ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt
    {ι : Type*} [Fintype ι] (φ : ι → Ω → ℝ → E → ℝ)
    (hm : ∀ i, Measurable fun p : Ω × ℝ × E => φ i p.1 p.2.1 p.2.2)
    (hp : ∀ i, Probability.MarkedProgressivelyMeasurable ℱ (φ i))
    (hq : ∀ i, ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ i ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∃ ks : ℕ → ℕ, (∀ m, m ≤ ks m) ∧ ∀ᵐ ω ∂P, ∀ δ : ℝ, 0 < δ → ∀ᶠ m in atTop,
      ∀ i, ∀ t ∈ Set.Icc (0 : ℝ) T,
        |stochasticIntegral N ℱ hℱ (markCut (spanningSets ν (ks m))ᶜ (φ i))
          (measurable_markCut (hm i) (measurableSet_spanningSets ν (ks m)).compl)
          ((hp i).indicator_mark (measurableSet_spanningSets ν (ks m)).compl)
          (fun T' hT' => sq_markCut (hq i) (spanningSets ν (ks m))ᶜ T' hT') t ω| < δ := by
  classical
  set R : ℕ → ι → ℝ → Ω → ℝ := fun m i t ω =>
    stochasticIntegral N ℱ hℱ (markCut (spanningSets ν m)ᶜ (φ i))
      (measurable_markCut (hm i) (measurableSet_spanningSets ν m).compl)
      ((hp i).indicator_mark (measurableSet_spanningSets ν m).compl)
      (fun T' hT' => sq_markCut (hq i) (spanningSets ν m)ᶜ T' hT') t ω with hRdef
  have hMart : ∀ m i, Martingale (R m i) ℱ.rightCont P := fun m i =>
    martingale_stochasticIntegral_rightCont N ℱ hℱ _ _ _ _
  have hRm : ∀ m i t, Measurable (R m i t) := fun m i t =>
    (((hMart m i).1 t).mono (ℱ.rightCont.le t)).measurable
  set D : ℕ → ι → Ω → ℝ≥0∞ := fun m i ω => ⨆ k, (‖dyadicRunMax (R m i) T k ω‖₊ : ℝ≥0∞)
    with hDdef
  have hDm : ∀ m i, Measurable (D m i) := fun m i =>
    Measurable.iSup fun k => measurable_enorm_dyadicRunMax (hRm m i) T k
  have hDoob : ∀ m i, ∫⁻ ω, (D m i ω) ^ 2 ∂P ≤ 4 * ∫⁻ ω, (‖R m i T ω‖₊ : ℝ≥0∞) ^ 2 ∂P :=
    fun m i => lintegral_iSup_dyadicRunMax_sq_le (hMart m i) hT.le
  have hD0 : ∀ i, Tendsto (fun m => ∫⁻ ω, (D m i ω) ^ 2 ∂P) atTop (𝓝 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun _ => zero_le)
      (hDoob · i)
    simpa using ENNReal.Tendsto.const_mul
      (tendsto_lintegral_sq_stochasticIntegral_markCut_spanningSets_compl N ℱ hℱ (φ i) (hm i)
        (hp i) (hq i) hT) (Or.inr (by norm_num))
  have hconv : ∀ i, Tendsto (fun m => ∫⁻ ω, (‖(D m i ω).toReal - (0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
    intro i
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hD0 i)
      (fun _ => zero_le) fun m => lintegral_mono fun ω => ?_
    rw [sub_zero, Real.nnnorm_of_nonneg ENNReal.toReal_nonneg]
    exact pow_le_pow_left' ENNReal.coe_toNNReal_le_self 2
  obtain ⟨ks, hks, hae⟩ := LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral
    (μ := P) (ι := ι) (u := fun m i ω => (D m i ω).toReal) (v := fun _ _ => (0 : ℝ))
    (fun m i => (hDm m i).ennreal_toReal) (fun _ => measurable_const) hconv
  refine ⟨ks, hks, ?_⟩
  have hfin : ∀ m i, ∀ᵐ ω ∂P, D m i ω ≠ ⊤ := fun m i => by
    have hlt : ∫⁻ ω, (D m i ω) ^ 2 ∂P < ⊤ := by
      refine lt_of_le_of_lt (hDoob m i) (ENNReal.mul_lt_top (by norm_num) ?_)
      rw [hRdef]
      dsimp only
      rw [isometry_stochasticIntegral N ℱ hℱ _ _ _ _ T hT]
      exact sq_markCut (hq i) _ T hT
    filter_upwards [ae_lt_top ((hDm m i).pow_const 2) hlt.ne] with ω hω
    intro h
    rw [h] at hω
    simp at hω
  have hcad : ∀ m i, ∀ᵐ ω ∂P, ∀ t : ℝ, Tendsto (fun s => R m i s ω) (𝓝[>] t) (𝓝 (R m i t ω)) :=
    fun m i => by
      filter_upwards [stochasticIntegral_cadlag N ℱ hℱ (markCut (spanningSets ν m)ᶜ (φ i))
        (measurable_markCut (hm i) (measurableSet_spanningSets ν m).compl)
        ((hp i).indicator_mark (measurableSet_spanningSets ν m).compl)
        (fun T' hT' => sq_markCut (hq i) (spanningSets ν m)ᶜ T' hT')] with ω hω t
      exact (hω t).1
  filter_upwards [hae, MeasureTheory.ae_all_iff.mpr fun m => MeasureTheory.ae_all_iff.mpr
    fun i => hfin (ks m) i, MeasureTheory.ae_all_iff.mpr fun m => MeasureTheory.ae_all_iff.mpr
    fun i => hcad (ks m) i] with ω hω hfω hcω
  intro δ hδ
  have hlim : ∀ i, Tendsto (fun m => (D (ks m) i ω).toReal) atTop (𝓝 0) := hω
  have hev : ∀ᶠ m in atTop, ∀ i, (D (ks m) i ω).toReal < δ :=
    Filter.eventually_all.mpr fun i => (hlim i).eventually (gt_mem_nhds hδ)
  filter_upwards [hev] with m hm i t ht
  have hle : (‖R (ks m) i t ω‖₊ : ℝ≥0∞) ≤ D (ks m) i ω := by
    rw [hDdef]
    dsimp only
    rw [← iSup_enorm_eq_iSup_dyadicRunMax hT.le (hcω m i)]
    exact le_iSup (fun t : Set.Icc (0 : ℝ) T => (‖R (ks m) i (t : ℝ) ω‖₊ : ℝ≥0∞)) ⟨t, ht⟩
  calc |R (ks m) i t ω| = ((‖R (ks m) i t ω‖₊ : ℝ≥0∞)).toReal := by simp
    _ ≤ (D (ks m) i ω).toReal := ENNReal.toReal_mono (hfω m i) hle
    _ < δ := hm i

end Uniform

section Solution

open LevyStochCalc.Brownian.Ito

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ} {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}
  {X : Setting.JumpDiffusion W N coeffs x₀}

/-- **The jump of a solution across an arrival time.** Along the path of a jump diffusion with
SDE data at a filtration satisfying the usual conditions, whose drift and left-limit jump
coefficient are admissible and whose zero-extended left-limit jump coefficient is marked
predictable, almost surely the increment across each arrival time in a window carrying a mark
of a spanning set of the intensity is the jump coefficient read at the left limit there, for
that mark. -/
theorem ae_exists_atomEnum_jump_eq_gamma_of_sdeData (S : BigJump.SdeData X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → S.ℱ 0 ≤ S.ℱ t)
    (hnull0 : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[S.ℱ 0] s)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμp : ∀ i : Fin n,
      Probability.ProgressivelyMeasurable S.ℱ fun ω s => coeffs.μ s (X.X s ω) i)
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγmL : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E =>
      coeffs.γ p.2.1 (leftLimPathAt X.X p.2.1 p.1) p.2.2 i)
    (hγpL : ∀ i : Fin n, Probability.MarkedProgressivelyMeasurable S.ℱ
      fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPathAt X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable S.ℱ ν
      (JumpFormula.zeroExtPos fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i))
    (j₀ : ℕ) {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ spanningSets ν j₀) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j₀, g p ∂(N.N ω)
        = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ j : Fin K,
        X.X (θ j) ω
          = leftLimPathAt X.X (θ j) ω + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) := by
  classical
  -- the continuous part at every level of the spanning sequence
  have hVex : ∀ k : ℕ, ∃ V : ℝ → Ω → Fin n → ℝ,
      IsVectorItoVersion W S.ℱ S.isBrownian (fun i j ω s => coeffs.σ s (X.X s ω) i j)
        S.σ_meas S.σ_prog S.σ_sq (fun _ => x₀)
        (continuousDriftLeftAt coeffs ν X.X (spanningSets ν k)) V :=
    fun k => exists_continuousPart S (measure_spanningSets_lt_top ν k).ne hℱ0 hnull0 hμm hμp
      hμq hγmL hγpL hγqL
  choose V hV using hVex
  have hXcad := X.cadlag_paths
  have hXright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X.X s ω) (𝓝[>] t) (𝓝 (X.X t ω)) := by
    filter_upwards [hXcad] with ω hω t ht
    exact (hω t ht).1
  -- the remainders
  set R : ℕ → Fin n → ℝ → Ω → ℝ := fun k i t ω =>
    stochasticIntegral N S.ℱ S.isPoisson
      (markCut (spanningSets ν k)ᶜ fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
      (measurable_markCut (hγmL i) (measurableSet_spanningSets ν k).compl)
      ((hγpL i).indicator_mark (measurableSet_spanningSets ν k).compl)
      (fun T' hT' => sq_markCut (hγqL i) (spanningSets ν k)ᶜ T' hT') t ω with hRdef
  have hRl : ∀ k i, ∀ᵐ ω ∂P, ∀ t : ℝ, ∃ L : ℝ,
      Tendsto (fun s => R k i s ω) (𝓝[<] t) (𝓝 L) := fun k i => by
    filter_upwards [stochasticIntegral_cadlag N S.ℱ S.isPoisson
      (markCut (spanningSets ν k)ᶜ fun ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i)
      (measurable_markCut (hγmL i) (measurableSet_spanningSets ν k).compl)
      ((hγpL i).indicator_mark (measurableSet_spanningSets ν k).compl)
      (fun T' hT' => sq_markCut (hγqL i) (spanningSets ν k)ᶜ T' hT')] with ω hω t
    exact (hω t).2
  -- the jump relation with remainder at every level
  have hjumpk : ∀ k : ℕ, ∀ᵐ ω ∂P, ∃ (K : ℕ) (θ : Fin K → ℝ) (ε : Fin K → E), StrictMono θ ∧
      (∀ j, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ spanningSets ν k) ∧
      (∀ g : ℝ × E → ℝ, ∫ p in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν k, g p ∂(N.N ω)
        = ∑ j : Fin K, g (θ j, ε j)) ∧
      ∀ (j : Fin K) (i : Fin n),
        X.X (θ j) ω i
          = leftLimPathAt X.X (θ j) ω i + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) i
            + (R k i (θ j) ω - Function.leftLim (fun s => R k i s ω) (θ j)) := by
    intro k
    refine ae_exists_atomEnum_jump_eq_gamma_add_remainder coeffs N X.X (spanningSets ν k)
      (measurableSet_spanningSets ν k) (measure_spanningSets_lt_top ν k).ne T (V k)
      (Eventually.of_forall (hV k).continuous_path) (R k) ?_ ?_
    · exact MeasureTheory.ae_all_iff.mpr fun i => hRl k i
    · refine ae_forall_eq_add_jumpSumLeftAt_add_remainder_of_path coeffs N X.X x₀ S.ℱ
        S.isBrownian S.σ_meas S.σ_prog S.σ_sq S.isPoisson S.γ_meas S.γ_prog S.γ_sq hγmL hγpL
        hγqL X.X hXcad hXright S.sde (measurableSet_spanningSets ν k)
        (measure_spanningSets_lt_top ν k).ne hpredL hμm hμq (V k) ?_ ?_
      · intro t ht
        filter_upwards [(hV k).ae_eq t ht] with ω hω i
        exact congrFun hω i
      · refine Eventually.of_forall fun ω t _ i => ?_
        exact (((continuous_apply i).comp ((hV k).continuous_path ω)).tendsto t).mono_left
          nhdsWithin_le_nhds
  -- the remainders vanish uniformly along a subsequence
  obtain ⟨ks, hks, hunif⟩ :=
    ae_exists_seq_forall_abs_stochasticIntegral_markCut_spanningSets_compl_lt N S.ℱ
      S.isPoisson (fun i ω s e => coeffs.γ s (leftLimPathAt X.X s ω) e i) hγmL hγpL hγqL hT
  filter_upwards [ae_exists_atomEnum_jumpSumLeftAt_eq_sum coeffs N X.X (spanningSets ν j₀)
    (measurableSet_spanningSets ν j₀) (measure_spanningSets_lt_top ν j₀).ne T,
    MeasureTheory.ae_all_iff.mpr fun m => hjumpk (ks m), hunif,
    MeasureTheory.ae_all_iff.mpr fun m => MeasureTheory.ae_all_iff.mpr fun i => hRl (ks m) i]
    with ω hA hjω hu hRω
  obtain ⟨K, θ, ε, hmono, hmem, hg, -⟩ := hA
  refine ⟨K, θ, ε, hmono, hmem, hg, fun j => ?_⟩
  funext i
  simp only [Pi.add_apply]
  -- the discrepancy is bounded by twice any positive bound
  have hkey : ∀ δ : ℝ, 0 < δ →
      |X.X (θ j) ω i - (leftLimPathAt X.X (θ j) ω i
        + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) i)| ≤ 2 * δ := by
    intro δ hδ
    obtain ⟨m, hmδ, hmj⟩ := ((hu δ hδ).and (eventually_ge_atTop j₀)).exists
    have hsub : spanningSets ν j₀ ⊆ spanningSets ν (ks m) :=
      monotone_spanningSets ν (hmj.trans (hks m))
    obtain ⟨K', θ', ε', -, hmem', hg', hrel⟩ := hjω m
    -- the arrival is among the arrivals of the larger set
    obtain ⟨j', hj'⟩ : ∃ j' : Fin K', (θ' j', ε' j') = (θ j, ε j) := by
      set g : ℝ × E → ℝ := fun q => if q = (θ j, ε j) then 1 else 0 with hgdef
      have h1 : ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν (ks m), g q ∂(N.N ω)
          = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ spanningSets ν j₀, g q ∂(N.N ω) := by
        refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
          (measurableSet_Ioc.prod (measurableSet_spanningSets ν _))
          (Set.prod_mono_right hsub) fun q hq => ?_
        have hne : q ≠ (θ j, ε j) := fun h => hq.2 (h ▸ ⟨(hmem j).1, (hmem j).2⟩)
        simp [hgdef, hne]
      have h2 : ∑ j' : Fin K', g (θ' j', ε' j') = ∑ j'' : Fin K, g (θ j'', ε j'') := by
        rw [← hg', ← hg, h1]
      have hpos : (0 : ℝ) < ∑ j'' : Fin K, g (θ j'', ε j'') := by
        refine lt_of_lt_of_le zero_lt_one ?_
        have hgj : g (θ j, ε j) = 1 := by simp [hgdef]
        calc (1 : ℝ) = g (θ j, ε j) := hgj.symm
          _ ≤ ∑ j'' : Fin K, g (θ j'', ε j'') :=
            Finset.single_le_sum (f := fun j'' => g (θ j'', ε j''))
              (fun j'' _ => by
                simp only [hgdef]
                split_ifs <;> norm_num) (Finset.mem_univ j)
      rw [← h2] at hpos
      obtain ⟨j', -, hj'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
      refine ⟨j', ?_⟩
      by_contra hne
      simp [hgdef, hne] at hj'
    have hθ : θ' j' = θ j := congrArg Prod.fst hj'
    have hε : ε' j' = ε j := congrArg Prod.snd hj'
    have hrel' := hrel j' i
    rw [hθ, hε] at hrel'
    have hbR : |R (ks m) i (θ j) ω| < δ :=
      hmδ i (θ j) ⟨(hmem j).1.1.le, (hmem j).1.2⟩
    have hbL : |Function.leftLim (fun s => R (ks m) i s ω) (θ j)| ≤ δ := by
      obtain ⟨L, hL⟩ := hRω m i (θ j)
      rw [leftLim_eq_of_tendsto hL]
      refine le_of_tendsto hL.abs ?_
      filter_upwards [Ioo_mem_nhdsLT (hmem j).1.1] with s hs
      exact (hmδ i s ⟨hs.1.le, hs.2.le.trans (hmem j).1.2⟩).le
    rw [hrel']
    calc |leftLimPathAt X.X (θ j) ω i + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) i
          + (R (ks m) i (θ j) ω - Function.leftLim (fun s => R (ks m) i s ω) (θ j))
          - (leftLimPathAt X.X (θ j) ω i
            + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) i)|
        = |R (ks m) i (θ j) ω - Function.leftLim (fun s => R (ks m) i s ω) (θ j)| := by
          congr 1
          ring
      _ ≤ |R (ks m) i (θ j) ω| + |Function.leftLim (fun s => R (ks m) i s ω) (θ j)| :=
          abs_sub _ _
      _ ≤ δ + δ := add_le_add hbR.le hbL
      _ = 2 * δ := by ring
  have hc : |X.X (θ j) ω i - (leftLimPathAt X.X (θ j) ω i
      + coeffs.γ (θ j) (leftLimPathAt X.X (θ j) ω) (ε j) i)| ≤ 0 := by
    refine le_of_forall_pos_lt_add fun δ hδ => ?_
    calc _ ≤ 2 * (δ / 4) := hkey (δ / 4) (by positivity)
      _ < 0 + δ := by linarith
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hc (abs_nonneg _)))

end Solution

end LevyStochCalc.Ito.JumpSplitting
