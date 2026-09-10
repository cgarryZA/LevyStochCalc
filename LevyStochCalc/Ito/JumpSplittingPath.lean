/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSplittingLeftLim

/-!
# Finite-activity splitting of a path carrying the left-limit jump sum

The finite-activity splitting along the left limits of a path does not need the split path to be
the jump diffusion itself. What the argument uses of the left-hand side is that it satisfies the
integral equation and that it is right-continuous on the nonnegative half-line; the jump
coefficient, the drift and the diffusion are read along the path of the jump diffusion
throughout, and so is the jump sum. Freeing the left-hand side therefore splits any path
satisfying that equation into the vector Itô process with the left-limit compensator subtracted
from the drift, and the jump sum of the jump diffusion over the mark set.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeft_of_path` — the splitting at
  a fixed nonnegative time, for a path satisfying the integral equation.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft_of_path` — the same identity
  almost surely at all nonnegative times simultaneously, for a right-continuous such path.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion` — the case of
  the jump diffusion's own path.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

section Splitting

variable (X : Setting.JumpDiffusion W N coeffs x₀) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hσm : ∀ (i : Fin n) (j : Fin d),
    Measurable (Function.uncurry fun ω s => coeffs.σ s (X.X s ω) i j))
  (hσp : ∀ (i : Fin n) (j : Fin d),
    Probability.ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (X.X s ω) i j)
  (hσq : ∀ (i : Fin n) (j : Fin d) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖coeffs.σ s (X.X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (hγm : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
  (hγp : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (X.X s ω) e i)
  (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hγmL : ∀ i : Fin n,
    Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
  (hγpL : ∀ i : Fin n,
    Probability.MarkedProgressivelyMeasurable ℱ
      fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
  (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s (leftLimPath X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation.** If the jump
coefficient is carried by a mark set of finite intensity and its left-limit integrand along the
path of the jump diffusion is predictable, then at every nonnegative time a path satisfying that
equation is almost surely the sum of the vector Itô process with diffusion `σ` and drift
`continuousDriftLeft`, and the left-limit jump sum over that mark set. -/
theorem eq_vectorItoProcess_add_jumpSumLeft_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
            (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
            (continuousDriftLeft X A) t ω i
          + jumpSumLeft X A t ω i := by
  have hsupp' : ∀ (i : Fin n) (ω : Ω) (s : ℝ) (e : E), e ∉ A →
      coeffs.γ s (leftLimPath X s ω) e i = 0 := by
    intro i ω s e he
    simp [hsupp s (leftLimPath X s ω) e he]
  rcases eq_or_lt_of_le ht with h0 | hpos
  · subst h0
    have hCzero : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) 0 ω = 0 := by
      intro i
      filter_upwards [LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_process N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) 0,
        LevyStochCalc.Poisson.Compensated.process_ae_zero_of_nonpos N ℱ hℱN
          (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i)
          (le_refl (0 : ℝ))] with ω h1 h2
      rw [h1, h2]
      rfl
    have hz0 : ∀ g : ℝ → ℝ, ∫ s in Set.Icc (0 : ℝ) 0, g s ∂volume = 0 :=
      fun g => setIntegral_measure_zero g (by simp)
    filter_upwards [hSDE 0 le_rfl, MeasureTheory.ae_all_iff.mpr hCzero] with ω hω hz
    intro i
    rw [hω i, hz i, multidimIntegral_eq_vectorItoMartingale X ℱ hℱW hσm hσp hσq i 0 ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess, hz0, jumpSumLeft_zero]
  · have hcong : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω := fun i =>
      compensatedIntegral_congr_of_countable_ne N hℱN (fun s x e => coeffs.γ s x e i)
        (ae_countable_setOf_pos_ne_leftLimPath X) (hγmL i) (hγm i) (hγpL i) (hγp i)
        (hγqL i) (hγq i) hpos
    have hpathL : ∀ i : Fin n, ∀ᵐ ω ∂P,
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
            (hγmL i) (hγpL i) (hγqL i) t ω
          = jumpSumLeft X A t ω i
            - ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i
                ∂(LevyStochCalc.Poisson.referenceIntensity ν) := fun i =>
      LevyStochCalc.Poisson.Compensated.stochasticIntegral_ae_eq_pathwise N ℱ hℱN
        (fun ω s e => coeffs.γ s (leftLimPath X s ω) e i) (hγmL i) (hγpL i) (hγqL i) hA
        (hpredL i) hAν (hsupp' i) hpos
    have hwinL : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i)
          (Set.Ioc (0 : ℝ) t ×ˢ A) (LevyStochCalc.Poisson.referenceIntensity ν) := by
      intro i
      filter_upwards [LevyStochCalc.Poisson.ae_integrableOn_window N hℱN hA hAν t (hpredL i)
        (hγmL i) (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
          (fun ω s e => coeffs.γ s (leftLimPath X s ω) e i) (hγmL i) (hγqL i)
          (A := A) hpos)] with ω hω
      exact hω.2
    have hμint : ∀ i : Fin n, ∀ᵐ ω ∂P,
        IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) t) volume := by
      intro i
      have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
        ((ENNReal.continuous_coe.measurable.comp (hμm i).nnnorm).pow_const
          2).lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
      filter_upwards [ae_lt_top' hmeas.aemeasurable (hμq i t hpos).ne] with ω hω
      exact integrableOn_Icc_of_lintegral_sq_lt_top
        ((hμm i).comp measurable_prodMk_left).aestronglyMeasurable hω
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    filter_upwards [hSDE t ht, hcong i, hpathL i, hwinL i, hμint i] with ω hω hc hp hw hm
    obtain ⟨heq, hcint⟩ :=
      integral_window_eq_and_integrableOn (fun s e => coeffs.γ s (leftLimPath X s ω) e i) hw
    have hd : ∫ s in Set.Icc (0 : ℝ) t, continuousDriftLeft X A i ω s ∂volume
        = (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i ∂volume)
          - ∫ s in Set.Icc (0 : ℝ) t,
              (∫ e in A, coeffs.γ s (leftLimPath X s ω) e i ∂ν) ∂volume :=
      integral_sub hm hcint
    rw [hω i, ← hc, hp, multidimIntegral_eq_vectorItoMartingale X ℱ hℱW hσm hσp hσq i t ω]
    simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
    rw [hd, heq]
    ring

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a path satisfying the integral equation, at all
nonnegative times.** If the jump coefficient is carried by a mark set of finite intensity, its
left-limit integrand along the path of the jump diffusion is predictable, `V` is a modification of
the vector Itô process with diffusion `σ` and drift `continuousDriftLeft` whose paths are
right-continuous, and `Z` is a right-continuous path satisfying that equation, then almost surely
`Z` is, at every nonnegative time, the sum of `V` and the left-limit jump sum over that mark
set. -/
theorem ae_forall_eq_add_jumpSumLeft_of_path (Z : ℝ → Ω → Fin n → ℝ)
    (hZright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      Z t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Z t ω i = V t ω i + jumpSumLeft X A t ω i := by
  have hwin := ae_forall_integrableOn_windowLeft X ℱ hℱN hA hAν hpredL hγmL hγqL
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      Z t ω i = V t ω i + jumpSumLeft X A t ω i := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine ae_forall_eq_of_ae_rat (P := P) (Y := fun s ω => Z s ω i)
      (Z := fun s ω => V s ω i + jumpSumLeft X A s ω i) ?_ ?_ ?_
    · intro q hq
      filter_upwards [eq_vectorItoProcess_add_jumpSumLeft_of_path X ℱ hℱW hσm hσp hσq hℱN
        hγm hγp hγq hγmL hγpL hγqL Z hSDE hA hAν hsupp hpredL hμm hμq hq,
        hVae (q : ℝ) hq] with ω h1 h2
      show Z (q : ℝ) ω i = V (q : ℝ) ω i + jumpSumLeft X A (q : ℝ) ω i
      rw [h1 i, h2 i]
    · filter_upwards [hZright] with ω hω t ht
      exact ((continuous_apply i).tendsto (Z t ω)).comp (hω t ht)
    · filter_upwards [hVright, hwin] with ω hVω hwω t ht
      exact (hVω t ht i).add
        (tendsto_jumpSumLeft_nhdsWithin_Ioi X hA (hγmL i) (fun T => hwω T i) t)
  filter_upwards [key] with ω hω
  intro t ht i
  exact hω i t ht

include hγmL hγpL hγqL in
/-- **The finite-activity splitting along the left limits at all nonnegative times.** The case of
the jump diffusion's own path, whose right continuity is carried by the càdlàg field. -/
theorem ae_forall_eq_add_jumpSumLeft_of_jumpDiffusion
    (hSDE : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X.X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
            (fun s ω => coeffs.σ s (X.X s ω) i) (fun j => hσm i j) (fun j => hσp i j)
            (fun j => hσq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγp i) (hγq i) t ω)
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hsupp : ∀ (s : ℝ) (x : Fin n → ℝ) (e : E), e ∉ A → coeffs.γ s x e = 0)
    (hpredL : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDriftLeft X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Tendsto (fun s => V s ω i) (𝓝[>] t) (𝓝 (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSumLeft X A t ω i :=
  ae_forall_eq_add_jumpSumLeft_of_path X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq hγmL hγpL hγqL
    X.X (by filter_upwards [X.cadlag_paths] with ω hω t ht using (hω t ht).1)
    hSDE hA hAν hsupp hpredL hμm hμq V hVae hVright

end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting
