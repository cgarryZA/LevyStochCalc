/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpSplitting

/-!
# The finite-activity splitting at all nonnegative times

The finite-activity splitting of a jump diffusion is an identity between the path, a vector Itô
process and a pathwise jump sum, valid almost surely at each fixed nonnegative time. The jump sum
over `(0, t]` is right-continuous in `t` on a window carrying an integrable jump coefficient and a
jump diffusion has almost surely càdlàg paths, so the identity extends from the nonnegative
rationals to all of `[0, ∞)` on a single set of full measure, for any modification of the vector
Itô process whose paths are right-continuous.

## Main statements

* `LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi` — right-continuity in time of
  the pathwise jump sum.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat` — two almost surely right-continuous
  processes agreeing almost surely at each nonnegative rational time agree almost surely at every
  nonnegative time.
* `LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSum` — the finite-activity splitting,
  almost surely at all nonnegative times simultaneously.
* `LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_of_measure_zero` — the jump sum is constant across a
  window carrying no mass of the random measure.
* `LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall` — the splitting written as a path
  translated by a shift held fixed strictly between consecutive members of a chain of times.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpSplitting

universe u v

section Rationals

/-- A sequence of rationals strictly to the right of a real number and converging to it. -/
theorem exists_seq_rat_gt (t : ℝ) :
    ∃ u : ℕ → ℚ, (∀ m, t < (u m : ℝ)) ∧
      Filter.Tendsto (fun m => ((u m : ℚ) : ℝ)) Filter.atTop (nhds t) := by
  have hlt : ∀ m : ℕ, t < t + 1 / ((m : ℝ) + 1) := by
    intro m
    have h : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    linarith
  choose u hu1 hu2 using fun m : ℕ => exists_rat_btwn (hlt m)
  refine ⟨u, hu1, ?_⟩
  have h0 : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / ((m : ℝ) + 1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hc : Filter.Tendsto (fun _ : ℕ => t) Filter.atTop (nhds t) := tendsto_const_nhds
  have hb : Filter.Tendsto (fun m : ℕ => t + 1 / ((m : ℝ) + 1)) Filter.atTop (nhds t) := by
    simpa using hc.add h0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hc hb (fun m => (hu1 m).le)
    (fun m => (hu2 m).le)

end Rationals

section Upgrade

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two processes with almost surely right-continuous paths that agree almost surely at each
nonnegative rational time agree almost surely at every nonnegative time. -/
theorem ae_forall_eq_of_ae_rat {Y Z : ℝ → Ω → ℝ}
    (hrat : ∀ q : ℚ, 0 ≤ (q : ℝ) → ∀ᵐ ω ∂P, Y (q : ℝ) ω = Z (q : ℝ) ω)
    (hY : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)))
    (hZ : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => Z s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Z t ω))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Y t ω = Z t ω := by
  have hall : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ (q : ℝ) → Y (q : ℝ) ω = Z (q : ℝ) ω := by
    refine MeasureTheory.ae_all_iff.mpr fun q => ?_
    by_cases hq : 0 ≤ (q : ℝ)
    · filter_upwards [hrat q hq] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hq
  filter_upwards [hall, hY, hZ] with ω hω hYω hZω
  intro t ht
  obtain ⟨u, hgt, hu⟩ := exists_seq_rat_gt t
  have hin : Filter.Tendsto (fun m => ((u m : ℚ) : ℝ)) Filter.atTop
      (nhdsWithin t (Set.Ioi t)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hu
      (Filter.Eventually.of_forall hgt)
  refine tendsto_nhds_unique (Filter.Tendsto.congr ?_ ((hYω t ht).comp hin))
    ((hZω t ht).comp hin)
  intro m
  exact hω (u m) (le_trans ht (hgt m).le)

end Upgrade

section Setup

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The jump sum over a window is the integral of the jump coefficient cut off by that window. -/
theorem jumpSum_eq_integral_indicator (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) (t : ℝ) (ω : Ω) (i : Fin n) :
    jumpSum X A t ω i
      = ∫ q, (Set.Ioc (0 : ℝ) t ×ˢ A).indicator
          (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i) q ∂(N.N ω) := by
  simp only [jumpSum]
  rw [integral_indicator (measurableSet_Ioc.prod hA)]

/-- The pathwise jump sum over `(0, ·]` is right-continuous in time along a path whose jump
coefficient is integrable over every bounded window. -/
theorem tendsto_jumpSum_nhdsWithin_Ioi (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {i : Fin n}
    (hγm : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i) {ω : Ω}
    (hint : ∀ T : ℝ, IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω)) (t : ℝ) :
    Filter.Tendsto (fun s => jumpSum X A s ω i) (nhdsWithin t (Set.Ioi t))
      (nhds (jumpSum X A t ω i)) := by
  have hfm : Measurable fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i :=
    hγm.comp measurable_prodMk_left
  simp only [jumpSum_eq_integral_indicator X hA]
  refine MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    ((Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator
      fun q : ℝ × E => ‖coeffs.γ q.1 (X.X q.1 ω) q.2 i‖) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun s =>
      (hfm.indicator (measurableSet_Ioc.prod hA)).aestronglyMeasurable
  · filter_upwards [(ge_mem_nhds (lt_add_one t)).filter_mono nhdsWithin_le_nhds] with s hs
    refine Filter.Eventually.of_forall fun q => ?_
    by_cases hq : q ∈ Set.Ioc (0 : ℝ) s ×ˢ A
    · have hq' : q ∈ Set.Ioc (0 : ℝ) (t + 1) ×ˢ A := ⟨⟨hq.1.1, hq.1.2.trans hs⟩, hq.2⟩
      simp [Set.indicator_of_mem hq, Set.indicator_of_mem hq']
    · have hnn : (0 : ℝ) ≤ (Set.Ioc (0 : ℝ) (t + 1) ×ˢ A).indicator
          (fun q : ℝ × E => ‖coeffs.γ q.1 (X.X q.1 ω) q.2 i‖) q :=
        Set.indicator_nonneg (fun _ _ => norm_nonneg _) q
      rw [Set.indicator_of_notMem hq]
      simpa using hnn
  · exact (MeasureTheory.integrable_indicator_iff (measurableSet_Ioc.prod hA)).mpr
      (hint (t + 1)).norm
  · refine Filter.Eventually.of_forall fun q => ?_
    have key : ∀ᶠ s in nhdsWithin t (Set.Ioi t),
        (Set.Ioc (0 : ℝ) t ×ˢ A).indicator
            (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i) q
          = (Set.Ioc (0 : ℝ) s ×ˢ A).indicator
            (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i) q := by
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

/-- The jump coefficient along the path of a jump diffusion is almost surely integrable against
the random measure over every bounded window of the mark set. -/
theorem ae_forall_integrableOn_window (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) {A : Set E}
    (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (hpred : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (X.X s ω) e i)
    (hγm : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X.X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖coeffs.γ s (X.X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ) (i : Fin n),
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) T ×ˢ A) (N.N ω) := by
  have hstep : ∀ (m : ℕ) (i : Fin n), ∀ᵐ ω ∂P,
      IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
        (Set.Ioc (0 : ℝ) ((m : ℝ) + 1) ×ˢ A) (N.N ω) := by
    intro m i
    have hpos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    filter_upwards [LevyStochCalc.Poisson.ae_integrableOn_window N hℱN hA hAν ((m : ℝ) + 1)
      (hpred i) (hγm i)
      (LevyStochCalc.Poisson.Compensated.window_energy_ne_top
        (fun ω s e => coeffs.γ s (X.X s ω) e i) (hγm i) (hγq i) (A := A) hpos)] with ω hω
    exact hω.1
  filter_upwards [MeasureTheory.ae_all_iff.mpr fun m : ℕ =>
    MeasureTheory.ae_all_iff.mpr fun i : Fin n => hstep m i] with ω hω
  intro T i
  obtain ⟨m, hm⟩ := exists_nat_ge T
  refine (hω m i).mono_set (Set.prod_mono (Set.Ioc_subset_Ioc_right ?_) (subset_refl A))
  linarith

/-- The jump sums over two nested windows differ by the jump sum over the window between them. -/
theorem jumpSum_sub_jumpSum (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {ω : Ω} {i : Fin n}
    (hint : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) b ×ˢ A) (N.N ω)) :
    jumpSum X A b ω i - jumpSum X A a ω i
      = ∫ q in Set.Ioc a b ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i ∂(N.N ω) := by
  have hunion : Set.Ioc (0 : ℝ) b ×ˢ A = Set.Ioc (0 : ℝ) a ×ˢ A ∪ Set.Ioc a b ×ˢ A := by
    rw [← Set.union_prod, Set.Ioc_union_Ioc_eq_Ioc ha hab]
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) a ×ˢ A) (Set.Ioc a b ×ˢ A) :=
    Set.disjoint_left.mpr fun q hq hq' => absurd hq.1.2 (not_le.mpr hq'.1.1)
  have h1 : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) a ×ˢ A) (N.N ω) :=
    hint.mono_set (by rw [hunion]; exact Set.subset_union_left)
  have h2 : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc a b ×ˢ A) (N.N ω) :=
    hint.mono_set (by rw [hunion]; exact Set.subset_union_right)
  have hsplit : jumpSum X A b ω i
      = jumpSum X A a ω i
        + ∫ q in Set.Ioc a b ×ˢ A, coeffs.γ q.1 (X.X q.1 ω) q.2 i ∂(N.N ω) := by
    simp only [jumpSum]
    rw [hunion, setIntegral_union hdisj (measurableSet_Ioc.prod hA) h1 h2]
  rw [hsplit]
  ring

/-- The jump sum is unchanged across a window on which the random measure carries no mass of the
mark set. -/
theorem jumpSum_eq_of_measure_zero (X : Setting.JumpDiffusion W N coeffs x₀) {A : Set E}
    (hA : MeasurableSet A) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {ω : Ω} {i : Fin n}
    (hint : IntegrableOn (fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
      (Set.Ioc (0 : ℝ) b ×ˢ A) (N.N ω))
    (hzero : (N.N ω) (Set.Ioc a b ×ˢ A) = 0) :
    jumpSum X A b ω i = jumpSum X A a ω i := by
  have h := jumpSum_sub_jumpSum X hA ha hab hint
  rw [setIntegral_measure_zero _ hzero] at h
  linarith

section AllTimes

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

/-- **The finite-activity splitting at all nonnegative times.** If the jump coefficient is carried
by a mark set of finite intensity, its integrand along the path is predictable and `V` is a
modification of the vector Itô process with diffusion `σ` and drift `continuousDrift` whose paths
are right-continuous, then almost surely the path is, at every nonnegative time, the sum of `V`
and the pathwise jump sum over that mark set. -/
theorem ae_forall_eq_add_jumpSum
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
    (hpred : ∀ i : Fin n,
      Probability.MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (X.X s ω) e i)
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T : ℝ), 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (V : ℝ → Ω → Fin n → ℝ)
    (hVae : ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      V t ω i = LevyStochCalc.Brownian.Ito.vectorItoProcess W ℱ hℱW
        (fun i j ω s => coeffs.σ s (X.X s ω) i j) hσm hσp hσq (fun _ => x₀)
        (continuousDrift X A) t ω i)
    (hVright : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Filter.Tendsto (fun s => V s ω i) (nhdsWithin t (Set.Ioi t)) (nhds (V t ω i))) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSum X A t ω i := by
  have hwin := ae_forall_integrableOn_window X ℱ hℱN hA hAν hpred hγm hγq
  have key : ∀ᵐ ω ∂P, ∀ (i : Fin n) (t : ℝ), 0 ≤ t →
      X.X t ω i = V t ω i + jumpSum X A t ω i := by
    refine MeasureTheory.ae_all_iff.mpr fun i => ?_
    refine ae_forall_eq_of_ae_rat (P := P) (Y := fun s ω => X.X s ω i)
      (Z := fun s ω => V s ω i + jumpSum X A s ω i) ?_ ?_ ?_
    · intro q hq
      filter_upwards [eq_vectorItoProcess_add_jumpSum X ℱ hℱW hσm hσp hσq hℱN hγm hγp hγq
        hSDE hA hAν hsupp hpred hμm hμq hq, hVae (q : ℝ) hq] with ω h1 h2
      show X.X (q : ℝ) ω i = V (q : ℝ) ω i + jumpSum X A (q : ℝ) ω i
      rw [h1 i, h2 i]
    · filter_upwards [X.cadlag_paths] with ω hω t ht
      exact ((continuous_apply i).tendsto (X.X t ω)).comp (hω t ht).1
    · filter_upwards [hVright, hwin] with ω hVω hwω t ht
      exact (hVω t ht i).add
        (tendsto_jumpSum_nhdsWithin_Ioi X hA (hγm i) (fun T => hwω T i) t)
  filter_upwards [key] with ω hω
  intro t ht i
  exact hω i t ht

end AllTimes

/-- Strictly between consecutive members of a chain of times starting at `0`, a path that splits
at all nonnegative times agrees with the vector Itô part translated by the value of the jump sum
on that interval. -/
theorem add_shift_eq_of_ae_forall {X : Setting.JumpDiffusion W N coeffs x₀} {A : Set E}
    {V : ℝ → Ω → Fin n → ℝ}
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      X.X t ω i = V t ω i + jumpSum X A t ω i)
    {σ : ℕ → Ω → WithTop ℝ} {c : ℕ → Ω → Fin n → ℝ}
    (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hc : ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → ∀ i : Fin n, jumpSum X A s ω i = c k ω i) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < σ (k + 1) ω → V s ω + c k ω = X.X s ω := by
  have hnn : ∀ (k : ℕ) (ω : Ω), ((0 : ℝ) : WithTop ℝ) ≤ σ k ω := by
    intro k ω
    induction k with
    | zero => exact le_of_eq (h0 ω).symm
    | succ k ih => exact ih.trans (hmono k ω)
  filter_upwards [hsplit, hc] with ω hs hcω
  intro k s h1 h2
  have hlt : ((0 : ℝ) : WithTop ℝ) < ((s : ℝ) : WithTop ℝ) := lt_of_le_of_lt (hnn k ω) h1
  have hs0 : (0 : ℝ) ≤ s := le_of_lt (by exact_mod_cast hlt)
  funext i
  simp only [Pi.add_apply]
  rw [hs s hs0 i, hcω k s h1 h2 i]

end Setup

end LevyStochCalc.Ito.JumpSplitting

#print axioms LevyStochCalc.Ito.JumpSplitting.exists_seq_rat_gt
#print axioms LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_of_ae_rat
#print axioms LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_integral_indicator
#print axioms LevyStochCalc.Ito.JumpSplitting.tendsto_jumpSum_nhdsWithin_Ioi
#print axioms LevyStochCalc.Ito.JumpSplitting.ae_forall_integrableOn_window
#print axioms LevyStochCalc.Ito.JumpSplitting.jumpSum_sub_jumpSum
#print axioms LevyStochCalc.Ito.JumpSplitting.jumpSum_eq_of_measure_zero
#print axioms LevyStochCalc.Ito.JumpSplitting.ae_forall_eq_add_jumpSum
#print axioms LevyStochCalc.Ito.JumpSplitting.add_shift_eq_of_ae_forall
