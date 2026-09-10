/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpIntegrandLeftLim
import LevyStochCalc.Ito.JumpSplittingAllTimes

/-!
# Finite-activity splitting along the left limits of the path

The jump coefficient of a jump diffusion can be evaluated along the left limits of the path
instead of along the path itself. The two integrands agree off a countable set of times, so they
have the same compensated integral, while the pathwise integral against the random measure and
the compensator against the reference intensity are both taken with the left-limit integrand.
The splitting of the path into a vector Itô process and a pathwise jump sum therefore holds in
this form as well, with the left-limit compensator subtracted from the drift.

## Main definitions

* `LevyStochCalc.Ito.JumpSplitting.leftLimPath` — the left limits of the path of a jump diffusion.
* `LevyStochCalc.Ito.JumpSplitting.jumpSumLeft` — the pathwise sum of the jumps carried by a mark
  set over a time window, with the jump coefficient evaluated at the left limits of the path.
* `LevyStochCalc.Ito.JumpSplitting.continuousDriftLeft` — the drift of a jump diffusion with the
  compensator of the left-limit jump coefficient subtracted.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.eq_vectorItoProcess_add_jumpSumLeft` — at every nonnegative
  time a jump diffusion is almost surely the sum of the vector Itô process with diffusion `σ` and
  drift `continuousDriftLeft`, and the left-limit jump sum.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSumLeft` — the same identity almost
  surely at all nonnegative times simultaneously.
* `LevyStochCalc.Ito.JumpSplitting.ae_ae_restrict_continuousDriftLeft_eq` and
  `LevyStochCalc.Ito.JumpSplitting.ae_forall_vectorItoProcess_continuousDriftLeft_eq` — the two
  drifts agree at almost every time of every horizon, hence build the same vector Itô process.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section WindowContinuity

variable {E : Type v} [MeasurableSpace E]

/-- The integral over a left-open time window times a mark set is right-continuous in the right
endpoint of the window, for an integrand integrable over every such window. -/
theorem tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi {κ : Measure (ℝ × E)} {A : Set E}
    (hA : MeasurableSet A) {f : ℝ × E → ℝ} (hf : Measurable f)
    (hint : ∀ T : ℝ, IntegrableOn f (Set.Ioc (0 : ℝ) T ×ˢ A) κ) (t : ℝ) :
    Tendsto (fun s => ∫ q in Set.Ioc (0 : ℝ) s ×ˢ A, f q ∂κ) (𝓝[>] t)
      (𝓝 (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, f q ∂κ)) := by
  have hrw : ∀ s : ℝ, (∫ q in Set.Ioc (0 : ℝ) s ×ˢ A, f q ∂κ)
      = ∫ q, (Set.Ioc (0 : ℝ) s ×ˢ A).indicator f q ∂κ :=
    fun s => (integral_indicator (measurableSet_Ioc.prod hA)).symm
  simp only [hrw]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    ((Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator fun q : ℝ × E => ‖f q‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun s =>
      (hf.indicator (measurableSet_Ioc.prod hA)).aestronglyMeasurable
  · filter_upwards [(ge_mem_nhds (lt_add_one t)).filter_mono nhdsWithin_le_nhds] with s hs
    refine Filter.Eventually.of_forall fun q => ?_
    by_cases hq : q ∈ Set.Ioc (0 : ℝ) s ×ˢ A
    · have hq' : q ∈ Set.Ioc (0 : ℝ) (t + 1) ×ˢ A := ⟨⟨hq.1.1, hq.1.2.trans hs⟩, hq.2⟩
      simp [Set.indicator_of_mem hq, Set.indicator_of_mem hq']
    · have hnn : (0 : ℝ) ≤ (Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator
          (fun q : ℝ × E => ‖f q‖) q :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) q
      rw [Set.indicator_of_notMem hq]
      simpa using hnn
  · exact (MeasureTheory.integrable_indicator_iff (measurableSet_Ioc.prod hA)).mpr
      (hint (t + 1)).norm
  · refine Filter.Eventually.of_forall fun q => ?_
    have key : ∀ᶠ s in 𝓝[>] t,
        (Set.Ioc (0 : ℝ) t ×ˢ A).indicator f q = (Set.Ioc (0 : ℝ) s ×ˢ A).indicator f q := by
      by_cases hqA : q.2 ∈ A
      · by_cases hq0 : 0 < q.1
        · by_cases hqt : q.1 ≤ t
          · filter_upwards [eventually_mem_nhdsWithin] with s hs
            have h1 : q ∈ Set.Ioc (0 : ℝ) s ×ˢ A := ⟨⟨hq0, hqt.trans (le_of_lt hs)⟩, hqA⟩
            have h2 : q ∈ Set.Ioc (0 : ℝ) t ×ˢ A := ⟨⟨hq0, hqt⟩, hqA⟩
            rw [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          · have ht' : t < q.1 := not_le.mp hqt
            filter_upwards [(gt_mem_nhds ht').filter_mono nhdsWithin_le_nhds] with s hs
            have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => absurd hmem.1.2 (not_le.mpr hs)
            have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => absurd hmem.1.2 (not_le.mpr ht')
            rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
        · refine Filter.Eventually.of_forall fun s => ?_
          have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => hq0 hmem.1.1
          have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => hq0 hmem.1.1
          rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
      · refine Filter.Eventually.of_forall fun s => ?_
        have h1 : q ∉ Set.Ioc (0 : ℝ) s ×ˢ A := fun hmem => hqA hmem.2
        have h2 : q ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hmem => hqA hmem.2
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    exact Filter.Tendsto.congr' key tendsto_const_nhds

end WindowContinuity

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The left limits of the path of a jump diffusion. -/
noncomputable def leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) (s : ℝ) (ω : Ω) :
    Fin n → ℝ :=
  Function.leftLim (fun r => X.X r ω) s

/-- The pathwise sum of the jumps carried by the mark set `A` over the window `(0, t]`, with the
jump coefficient evaluated at the left limits of the path. -/
noncomputable def jumpSumLeft (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (t : ℝ)
    (ω : Ω) (i : Fin n) : ℝ :=
  ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A, coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i ∂(N.N ω)

/-- The drift of a jump diffusion with the compensator of the jumps carried by `A` subtracted,
the jump coefficient being evaluated at the left limits of the path. -/
noncomputable def continuousDriftLeft (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E)
    (i : Fin n) (ω : Ω) (s : ℝ) : ℝ :=
  coeffs.μ s (X.X s ω) i - ∫ e in A, coeffs.γ s (leftLimPath X s ω) e i ∂ν

/-- The left-limit jump sum over the degenerate window vanishes. -/
theorem jumpSumLeft_zero (X : Setting.JumpDiffusion W N coeffs x₀) (A : Set E) (ω : Ω)
    (i : Fin n) : jumpSumLeft X A 0 ω i = 0 := by
  simp [jumpSumLeft]

section Cadlag

/-- A path converging in each coordinate along the filter of times strictly below a given time
has that limit as its left limit there. -/
theorem leftLimPath_eq_of_tendsto {X : Setting.JumpDiffusion W N coeffs x₀} {ω : Ω} {t : ℝ}
    {L : Fin n → ℝ} (hL : ∀ i : Fin n, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 (L i))) :
    leftLimPath X t ω = L := by
  show Function.leftLim (fun r => X.X r ω) t = L
  exact leftLim_eq_of_tendsto (tendsto_pi_nhds.mpr hL)

/-- A path with left limits in each coordinate at a given time converges there to its left
limits. -/
theorem tendsto_nhdsLT_leftLimPath {X : Setting.JumpDiffusion W N coeffs x₀} {ω : Ω} {t : ℝ}
    (h : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L)) (i : Fin n) :
    Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 (leftLimPath X t ω i)) := by
  classical
  choose L hL using h
  rw [leftLimPath_eq_of_tendsto hL]
  exact hL i

/-- The path of a jump diffusion almost surely meets its left limits at all but countably many
positive times. -/
theorem ae_countable_setOf_pos_ne_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀) :
    ∀ᵐ ω ∂P, {s : ℝ | 0 < s ∧ leftLimPath X s ω ≠ X.X s ω}.Countable := by
  filter_upwards [X.cadlag_paths] with ω hω
  refine Set.Countable.mono ?_ (countable_setOf_pos_ne_of_cadlag
    (f := fun s => X.X s ω) (g := fun s => leftLimPath X s ω)
    (fun t ht => (hω t ht).1) (fun t ht i => tendsto_nhdsLT_leftLimPath (hω t ht.le).2 i))
  intro s hs
  exact ⟨hs.1, fun h => hs.2 h.symm⟩

/-- The drift carrying the left-limit compensator meets the drift carrying the point-evaluated
compensator at almost every time of every horizon. -/
theorem ae_ae_restrict_continuousDriftLeft_eq (X : Setting.JumpDiffusion W N coeffs x₀)
    (A : Set E) (i : Fin n) :
    ∀ᵐ ω ∂P, ∀ T : ℝ, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      continuousDriftLeft X A i ω s = continuousDrift X A i ω s := by
  filter_upwards [ae_countable_setOf_pos_ne_leftLimPath X] with ω hω T
  filter_upwards [ae_restrict_eq_of_countable_ne hω T] with s hs
  simp only [continuousDriftLeft, continuousDrift, hs]

end Cadlag

section Window

/-- The left-limit jump sum over `(0, ·]` is right-continuous in time along a path whose
left-limit jump coefficient is integrable over every bounded window. -/
theorem tendsto_jumpSumLeft_nhdsWithin_Ioi (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {i : Fin n}
    (hγmL : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
    {ω : Ω}
    (hint : ∀ T : ℝ, IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)) (t : ℝ) :
    Tendsto (fun s => jumpSumLeft X A s ω i) (𝓝[>] t) (𝓝 (jumpSumLeft X A t ω i)) := by
  have hfm : Measurable fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i :=
    hγmL.comp measurable_prodMk_left
  exact tendsto_setIntegral_Ioc_prod_nhdsWithin_Ioi hA hfm hint t

/-- The left-limit jump coefficient along the path of a jump diffusion is almost surely
integrable against the random measure over every bounded window of the mark set. -/
theorem ae_forall_integrableOn_windowLeft (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpredL : ∀ i : Fin n, Probability.MarkedPredictable ℱ ν
      fun ω s e => coeffs.γ s (leftLimPath X s ω) e i)
    (hγmL : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (leftLimPath X p.2.1 p.1) p.2.2 i)
    (hγqL : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (leftLimPath X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (i : Fin n),
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω) := by
  have hstep : ∀ (m : ℕ) (i : Fin n), ∀ᵐ ω ∂P,
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (leftLimPath X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) ((m : ℝ) + 1) ×ˢ A) (N.N ω) := by
    intro m i
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    filter_upwards [LevyStochCalc.Poisson.ae_integrableOn_window N hℱN hA hAν ((m : ℝ) + 1)
      (hpredL i) (hγmL i)
      (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
        (fun ω s e => coeffs.γ s (leftLimPath X s ω) e i) (hγmL i) (hγqL i)
        (A := A) hpos)] with ω hω
    exact hω.1
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun m : ℕ =>
    MeasureTheory.ae_all_iff.mpr fun i : Fin n => hstep m i] with ω hω
  intro T i
  obtain ⟨m, hm⟩ := exists_nat_ge T
  refine (hω m i).mono_set (Set.prod_mono (Set.Ioc_subset_Ioc_right ?_) (subset_refl A))
  linarith

end Window

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

/-- The vector Itô processes built from the two drifts agree at every nonnegative time. -/
theorem ae_forall_vectorItoProcess_continuousDriftLeft_eq (A : Set E) :
    ∀ᵐ ω ∂P, ∀ (t : ℝ) (i : Fin n),
      LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
          (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
          (continuousDriftLeft X A) t ω i
        = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
          (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
          (continuousDrift X A) t ω i := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin n =>
    ae_ae_restrict_continuousDriftLeft_eq X A i] with ω hω
  intro t i
  simp only [LevyStochCalc.Brownian.Ito.vectorItoProcess]
  rw [integral_congr_ae (hω i t)]

include hγmL hγpL hγqL in
/-- **The finite-activity splitting of a jump diffusion along the left limits of its path.** If
the jump coefficient is carried by a mark set of finite intensity and its left-limit integrand
along the path is predictable, then at every nonnegative time the path is almost surely the sum
of the vector Itô process with diffusion `σ` and drift `continuousDriftLeft`, and the left-limit
jump sum over that mark set. -/
theorem eq_vectorItoProcess_add_jumpSumLeft
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
    {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ ω ∂P, ∀ i : Fin n,
      X.X t ω i
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
/-- **The finite-activity splitting along the left limits at all nonnegative times.** If the jump
coefficient is carried by a mark set of finite intensity, its left-limit integrand along the path
is predictable and `V` is a modification of the vector Itô process with diffusion `σ` and drift
`continuousDriftLeft` whose paths are right-continuous, then almost surely the path is, at every
nonnegative time, the sum of `V` and the left-limit jump sum over that mark set. -/
theorem ae_forall_eq_add_jumpSumLeft
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
      X.X t ω i = V t ω i + jumpSumLeft X A t ω i := by
  have hwin := ae_forall_integrableOn_windowLeft X ℱ hℱN hA hAν hpredL hγmL hγqL
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      X.X t ω i = V t ω i + jumpSumLeft X A t ω i := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine ae_forall_eq_of_ae_rat (P := P) (Y := fun s ω => X.X s ω i)
      (Z := fun s ω => V s ω i + jumpSumLeft X A s ω i) ?_ ?_ ?_
    · intro q hq
      filter_upwards [eq_vectorItoProcess_add_jumpSumLeft X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq
        hγmL hγpL hγqL hSDE hA hAν hsupp hpredL hμm hμq hq, hVae (q : ℝ) hq] with ω h1 h2
      show X.X (q : ℝ) ω i = V (q : ℝ) ω i + jumpSumLeft X A (q : ℝ) ω i
      rw [h1 i, h2 i]
    · filter_upwards [X.cadlag_paths] with ω hω t ht
      exact ((continuous_apply i).tendsto (X.X t ω)).comp (hω t ht).1
    · filter_upwards [hVright, hwin] with ω hVω hwω t ht
      exact (hVω t ht i).add
        (tendsto_jumpSumLeft_nhdsWithin_Ioi X hA (hγmL i) (fun T => hwω T i) t)
  filter_upwards [key] with ω hω
  intro t ht i
  exact hω i t ht

end Splitting

end Setup

end LevyStochCalc.Ito.JumpSplitting
