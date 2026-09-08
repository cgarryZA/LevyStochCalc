/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.StrictCount

/-!
# A continuous adapted process, cut to a window, is marked predictable

Freezing a continuous adapted process at the left endpoints of the level-`n` dyadic slabs gives a
step process whose coefficients are known at those endpoints, hence a marked predictable process
for every level. The endpoints increase to the time from strictly below, so on a window of finite
mark measure the frozen processes converge pointwise to the process itself, which is therefore
marked predictable there.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {ν : Measure E} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

open LevyStochCalc.Poisson (dyadicLeft dyadicLeft_lt sub_le_dyadicLeft)

/-- A continuous adapted process frozen at the left endpoints of the level-`n` dyadic slabs of a
window. -/
noncomputable def stepEval (X : ℝ → Ω → ℝ) (A : Set E) (T : ℝ) (n : ℕ) (ω : Ω) (s : ℝ)
    (e : E) : ℝ :=
  ∑ i ∈ Finset.range ⌈T * 2 ^ n⌉₊,
    (Set.Ioc ((i : ℝ) / 2 ^ n) (((i : ℝ) + 1) / 2 ^ n) ×ˢ A).indicator
      (fun _ : ℝ × E => X ((i : ℝ) / 2 ^ n) ω) (s, e)

theorem markedPredictable_stepEval {X : ℝ → Ω → ℝ}
    (hX : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t)) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) (n : ℕ) :
    MarkedPredictable ℱ ν (stepEval X A T n) := by
  change Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    ∑ i ∈ Finset.range ⌈T * 2 ^ n⌉₊,
      (Set.Ioc ((i : ℝ) / 2 ^ n) (((i : ℝ) + 1) / 2 ^ n) ×ˢ A).indicator
        (fun _ : ℝ × E => X ((i : ℝ) / 2 ^ n) p.1) (p.2.1, p.2.2)
  refine Finset.measurable_sum _ fun i _ => ?_
  exact markedPredictable_rectIndicator (by positivity) hA hAν
    ((hX ((i : ℝ) / 2 ^ n)).measurable)

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- On a window the frozen process at a time–mark point is the process at the left endpoint of
the slab. -/
theorem stepEval_eq {X : ℝ → Ω → ℝ} {A : Set E} {T s : ℝ} (hs : 0 < s) (hsT : s ≤ T) {e : E}
    (he : e ∈ A) (ω : Ω) (n : ℕ) :
    stepEval X A T n ω s e = X (dyadicLeft n s) ω := by
  classical
  have hpow : (0 : ℝ) < 2 ^ n := by positivity
  have hmem : ⌈s * 2 ^ n⌉₊ - 1 ∈ Finset.range ⌈T * 2 ^ n⌉₊ := by
    rw [Finset.mem_range]
    have h1 : 1 ≤ ⌈s * 2 ^ n⌉₊ := LevyStochCalc.Poisson.one_le_ceil_mul_pow hs n
    have h2 : ⌈s * 2 ^ n⌉₊ ≤ ⌈T * 2 ^ n⌉₊ := Nat.ceil_le_ceil (by nlinarith)
    omega
  have hcast : ((⌈s * 2 ^ n⌉₊ - 1 : ℕ) : ℝ) = (⌈s * 2 ^ n⌉₊ : ℝ) - 1 :=
    LevyStochCalc.Poisson.cast_ceil_pred hs n
  have hin : (s, e) ∈ Set.Ioc (((⌈s * 2 ^ n⌉₊ - 1 : ℕ) : ℝ) / 2 ^ n)
      (((((⌈s * 2 ^ n⌉₊ - 1 : ℕ) : ℝ)) + 1) / 2 ^ n) ×ˢ A := by
    refine ⟨⟨?_, ?_⟩, he⟩
    · rw [hcast]
      exact dyadicLeft_lt hs n
    · rw [hcast]
      have hle := Nat.le_ceil (s * 2 ^ n)
      rw [le_div_iff₀ hpow]
      linarith
  have hzero : ∀ b ∈ Finset.range ⌈T * 2 ^ n⌉₊, b ≠ ⌈s * 2 ^ n⌉₊ - 1 →
      (Set.Ioc ((b : ℝ) / 2 ^ n) (((b : ℝ) + 1) / 2 ^ n) ×ˢ A).indicator
        (fun _ : ℝ × E => X ((b : ℝ) / 2 ^ n) ω) (s, e) = 0 := by
    intro b _ hb
    refine Set.indicator_of_notMem (fun hmemb => hb ?_) _
    obtain ⟨⟨hb1, hb2⟩, -⟩ := hmemb
    rw [div_lt_iff₀ hpow] at hb1
    rw [le_div_iff₀ hpow] at hb2
    have h1 : (b : ℝ) < s * 2 ^ n := hb1
    have h2 : s * 2 ^ n ≤ (b : ℝ) + 1 := hb2
    have hceil : ⌈s * 2 ^ n⌉₊ = b + 1 := by
      refine Nat.ceil_eq_iff (by omega) |>.mpr ⟨?_, ?_⟩
      · push_cast; linarith
      · push_cast; linarith
    omega
  rw [stepEval, Finset.sum_eq_single (⌈s * 2 ^ n⌉₊ - 1) hzero (fun h => absurd hmem h),
    Set.indicator_of_mem hin, hcast]
  rfl

/-- The frozen process cut to the window. -/
noncomputable def stepEvalCut (X : ℝ → Ω → ℝ) (A : Set E) (T : ℝ) (n : ℕ) (ω : Ω) (s : ℝ)
    (e : E) : ℝ :=
  (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => (1 : ℝ)) (s, e)
    * stepEval X A T n ω s e

theorem markedPredictable_stepEvalCut {X : ℝ → Ω → ℝ}
    (hX : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t)) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) (T : ℝ) (n : ℕ) :
    MarkedPredictable ℱ ν (stepEvalCut X A T n) := by
  have hwin : MarkedPredictable ℱ ν fun (_ : Ω) (s : ℝ) (e : E) =>
      (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => (1 : ℝ)) (s, e) :=
    markedPredictable_of_measurable_window hA hAν
      (measurable_const.indicator (measurableSet_Ioc.prod hA))
      (fun p hp => Set.indicator_of_notMem hp _)
  exact hwin.mul (markedPredictable_stepEval hX hA hAν T n)

/-- **A continuous adapted process is marked predictable on a window.** The process cut to
`(0, T] × A` by an indicator is predictable for the marked predictable σ-algebra. -/
theorem markedPredictable_of_continuous_adapted {X : ℝ → Ω → ℝ}
    (hXc : ∀ ω, Continuous fun t => X t ω) (hX : ∀ t : ℝ, StronglyMeasurable[ℱ t] (X t))
    {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    MarkedPredictable ℱ ν fun ω s e =>
      (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => X s ω) (s, e) := by
  have hstep : ∀ n : ℕ, Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
      stepEvalCut X A T n p.1 p.2.1 p.2.2 := fun n =>
    markedPredictable_stepEvalCut hX hA hAν T n
  change Measurable[markedPredictableSigma ℱ ν] fun p : Ω × ℝ × E =>
    (Set.Ioc (0 : ℝ) T ×ˢ A).indicator (fun _ : ℝ × E => X p.2.1 p.1) (p.2.1, p.2.2)
  refine @measurable_of_tendsto_metrizable' _ _ (markedPredictableSigma ℱ ν) _ _ _ _ ℕ
    (fun n p => stepEvalCut X A T n p.1 p.2.1 p.2.2) _ atTop _ _ hstep ?_
  refine tendsto_pi_nhds.mpr fun p => ?_
  by_cases hp : (p.2.1, p.2.2) ∈ Set.Ioc (0 : ℝ) T ×ˢ A
  · obtain ⟨⟨hs0, hsT⟩, he⟩ := hp
    have hmem : (p.2.1, p.2.2) ∈ Set.Ioc (0 : ℝ) T ×ˢ A := ⟨⟨hs0, hsT⟩, he⟩
    rw [Set.indicator_of_mem hmem]
    have heq : ∀ n : ℕ, stepEvalCut X A T n p.1 p.2.1 p.2.2 = X (dyadicLeft n p.2.1) p.1 := by
      intro n
      rw [stepEvalCut, Set.indicator_of_mem hmem, one_mul, stepEval_eq hs0 hsT he p.1 n]
    simp only [heq]
    refine ((hXc p.1).tendsto (p.2.1)).comp ?_
    have hlo : ∀ n : ℕ, p.2.1 - (1 / 2 : ℝ) ^ n ≤ dyadicLeft n p.2.1 := fun n =>
      sub_le_dyadicLeft n
    have hhi : ∀ n : ℕ, dyadicLeft n p.2.1 ≤ p.2.1 := fun n => (dyadicLeft_lt hs0 n).le
    have hlim : Tendsto (fun n : ℕ => p.2.1 - (1 / 2 : ℝ) ^ n) atTop (𝓝 p.2.1) := by
      have := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
        (by norm_num)
      simpa using (tendsto_const_nhds (x := p.2.1)).sub this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlo hhi
  · rw [Set.indicator_of_notMem hp]
    have hzero : ∀ n : ℕ, stepEvalCut X A T n p.1 p.2.1 p.2.2 = 0 := by
      intro n
      rw [stepEvalCut, Set.indicator_of_notMem hp, zero_mul]
    simp only [hzero]
    exact tendsto_const_nhds

end LevyStochCalc.Probability
