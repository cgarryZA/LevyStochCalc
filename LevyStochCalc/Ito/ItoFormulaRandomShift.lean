/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaIncrement
import LevyStochCalc.Brownian.ItoCutoff

/-!
# Passing to the limit in a shifted Itô formula

A shift of the argument of a `C²` function by a random vector is approximated by shifts along a
sequence of random vectors converging to it pointwise. Each term of the resulting identity
converges: the boundary term by continuity of the function, the two Lebesgue terms by dominated
convergence along the path, and the stochastic term in `L²` by the difference isometry, hence
almost surely along a subsequence. An identity holding for every member of the sequence therefore
holds in the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.stopped_sub` — cutting off at a stopping time is linear.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_comp_shift` — the energy of the difference of
  two shifted integrands vanishes along a pointwise-convergent sequence of shifts.
* `LevyStochCalc.Brownian.Ito.tendsto_setIntegral_stopped_sub_shift` — the Lebesgue terms
  converge along the path.
* `LevyStochCalc.Brownian.Ito.ae_eq_of_tendsto_of_forall_ae_eq` — an almost-everywhere identity
  survives an almost-everywhere limit on both sides.
* `LevyStochCalc.Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy` — a vanishing
  energy distance between integrands gives a vanishing `L²` distance between their Itô integrals.
* `LevyStochCalc.Brownian.Ito.exists_seq_ae_tendsto_stochInt_of_tendsto_energy` — the same over
  finitely many Brownian channels, almost surely along a common subsequence.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {α : Type*}

section StoppedAlgebra

variable {Ω : Type*}

/-- Cutting off at a stopping time commutes with subtraction of integrands. -/
theorem stopped_sub (τ : Ω → WithTop ℝ) (A B : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    Probability.stopped τ (fun ω s => A ω s - B ω s) ω s
      = Probability.stopped τ A ω s - Probability.stopped τ B ω s := by
  unfold LevyStochCalc.Probability.stopped
  split_ifs <;> ring

/-- The increment of a cut-off integrand between two stopping times is linear in the integrand. -/
theorem stopped_sub_stopped_sub (σ τ : Ω → WithTop ℝ) (A B : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    (Probability.stopped τ A ω s - Probability.stopped σ A ω s)
        - (Probability.stopped τ B ω s - Probability.stopped σ B ω s)
      = Probability.stopped τ (fun ω s => A ω s - B ω s) ω s
        - Probability.stopped σ (fun ω s => A ω s - B ω s) ω s := by
  rw [stopped_sub τ A B, stopped_sub σ A B]
  ring

/-- The increment of a cut-off integrand between two stopping times is bounded by twice the
integrand. -/
theorem abs_stopped_sub_stopped_le (σ τ : Ω → WithTop ℝ) (A : Ω → ℝ → ℝ) (ω : Ω) (s : ℝ) :
    |Probability.stopped τ A ω s - Probability.stopped σ A ω s| ≤ 2 * |A ω s| := by
  calc |Probability.stopped τ A ω s - Probability.stopped σ A ω s|
      ≤ |Probability.stopped τ A ω s| + |Probability.stopped σ A ω s| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ |A ω s| + |A ω s| :=
        add_le_add (Probability.abs_stopped_le τ A ω s) (Probability.abs_stopped_le σ A ω s)
    _ = 2 * |A ω s| := by ring

end StoppedAlgebra

section LimitTransfer

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- An identity holding almost everywhere for every member of a sequence holds for the limits, when
both sides converge almost everywhere. -/
theorem ae_eq_of_tendsto_of_forall_ae_eq {L R : ℕ → Ω → ℝ} {Lim Rlim : Ω → ℝ}
    (heq : ∀ m, L m =ᵐ[P] R m)
    (hL : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => L m ω) Filter.atTop (nhds (Lim ω)))
    (hR : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => R m ω) Filter.atTop (nhds (Rlim ω))) :
    Lim =ᵐ[P] Rlim := by
  have hall : ∀ᵐ ω ∂P, ∀ m, L m ω = R m ω := (MeasureTheory.ae_all_iff).2 heq
  filter_upwards [hall, hL, hR] with ω hω hLω hRω
  have : Filter.Tendsto (fun m => L m ω) Filter.atTop (nhds (Rlim ω)) := by
    simpa [funext fun m => hω m] using hRω
  exact tendsto_nhds_unique hLω this

/-- The same transfer along a subsequence, which is all the `L²` limit of a stochastic term
supplies. -/
theorem ae_eq_of_tendsto_comp_of_forall_ae_eq {L R : ℕ → Ω → ℝ} {Lim Rlim : Ω → ℝ}
    (ms : ℕ → ℕ) (heq : ∀ m, L m =ᵐ[P] R m)
    (hL : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => L (ms m) ω) Filter.atTop (nhds (Lim ω)))
    (hR : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => R (ms m) ω) Filter.atTop (nhds (Rlim ω))) :
    Lim =ᵐ[P] Rlim :=
  ae_eq_of_tendsto_of_forall_ae_eq (L := fun m => L (ms m)) (R := fun m => R (ms m))
    (fun m => heq (ms m)) hL hR

end LimitTransfer

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Two values of a bounded function differ by at most twice the bound. -/
theorem abs_sub_le_two_mul_of_abs_le {g : α → ℝ} {K : ℝ} (hK : ∀ z, |g z| ≤ K) (u v : α) :
    |g u - g v| ≤ 2 * K := by
  calc |g u - g v| ≤ |g u| + |g v| := by
        rw [sub_eq_add_neg]
        exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    _ ≤ K + K := add_le_add (hK u) (hK v)
    _ = 2 * K := by ring

/-- The energy of the difference between a bounded function of a shifted process times an
integrand and the same expression at the limiting shift vanishes along a pointwise-convergent
sequence of shifts. -/
theorem tendsto_lintegral_sq_comp_shift {n : ℕ} {X : ℝ → Ω → Fin n → ℝ}
    {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g) {K : ℝ} (hK : ∀ z, |g z| ≤ K)
    {H : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    {c : Ω → Fin n → ℝ} {cm : ℕ → Ω → Fin n → ℝ}
    (hcm : ∀ m, Measurable (cm m)) (hc : Measurable c)
    (hlim : ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (nhds (c ω)))
    {T : ℝ} (hHq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  have h2K0 : (0 : ℝ) ≤ 2 * K := by linarith
  set C : ℝ≥0∞ := ENNReal.ofReal ((2 * K) ^ 2) with hC
  -- the integrand is dominated by a constant multiple of the energy density
  have hdom : ∀ (m : ℕ) (ω : Ω) (s : ℝ),
      (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2
        ≤ C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro m ω s
    refine sq_enorm_le_of_abs_le h2K0 ?_
    rw [← sub_mul, abs_mul]
    exact mul_le_mul_of_nonneg_right
      (abs_sub_le_two_mul_of_abs_le hK _ _) (abs_nonneg _)
  -- measurability of each stage and of the dominating density
  have hXcm : ∀ m : ℕ, Measurable (Function.uncurry fun ω s => X s ω + cm m ω) := by
    intro m
    exact hXm.add ((hcm m).comp measurable_fst)
  have hXc : Measurable (Function.uncurry fun ω s => X s ω + c ω) :=
    hXm.add (hc.comp measurable_fst)
  have hFm : ∀ m : ℕ, Measurable (Function.uncurry fun ω s =>
      (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2) := by
    intro m
    exact ((((hgc.measurable.comp (hXcm m)).mul hHm).sub
      ((hgc.measurable.comp hXc).mul hHm)).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hBm : Measurable (Function.uncurry fun ω s => C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_const.mul (hHm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  -- the dominating density has finite total mass
  have hBfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ := by
    have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        = C * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ (by simp [hC] : C ≠ ⊤)]
      exact MeasureTheory.lintegral_congr fun ω => by
        rw [MeasureTheory.lintegral_const_mul' _ _ (by simp [hC] : C ≠ ⊤)]
    rw [hswap]
    exact ENNReal.mul_ne_top (by simp [hC]) hHq
  -- pointwise convergence of the integrand
  have hptw : ∀ (ω : Ω) (s : ℝ), Filter.Tendsto
      (fun m => (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2)
      Filter.atTop (nhds 0) := by
    intro ω s
    have h1 : Filter.Tendsto (fun m => g (X s ω + cm m ω) * H ω s
        - g (X s ω + c ω) * H ω s) Filter.atTop (nhds 0) := by
      have h2 : Filter.Tendsto (fun m => g (X s ω + cm m ω)) Filter.atTop
          (nhds (g (X s ω + c ω))) :=
        (hgc.tendsto _).comp (Filter.Tendsto.const_add _ (hlim ω))
      simpa using (h2.mul_const (H ω s)).sub_const (g (X s ω + c ω) * H ω s)
    have h3 : Filter.Tendsto (fun m => (‖g (X s ω + cm m ω) * H ω s
        - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0)) Filter.atTop (nhds 0) := by
      simpa using h1.nnnorm
    have h5 : Filter.Tendsto (fun m => (‖g (X s ω + cm m ω) * H ω s
        - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0) ^ 2) Filter.atTop (nhds 0) := by
      simpa using h3.pow 2
    have h6 := ENNReal.tendsto_coe.2 h5
    simpa [ENNReal.coe_pow] using h6
  -- dominated convergence, first in the time variable and then in the sample point
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto
      (fun m => ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖g (X s ω + cm m ω) * H ω s - g (X s ω + c ω) * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      Filter.atTop (nhds 0) := by
    have hfin : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T,
        C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤ :=
      MeasureTheory.ae_lt_top hBm.lintegral_prod_right' hBfin
    filter_upwards [hfin] with ω hω
    rw [show (0 : ℝ≥0∞) = ∫⁻ _ : ℝ, (0 : ℝ≥0∞)
      ∂(volume.restrict (Set.Icc (0 : ℝ) T)) from by simp]
    refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (bound := fun s => C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2) ?_ ?_ hω.ne ?_
    · exact fun m => (Measurable.of_uncurry_left (hFm m)).aemeasurable
    · exact fun m => Filter.Eventually.of_forall fun s => hdom m ω s
    · exact Filter.Eventually.of_forall fun s => hptw ω s
  rw [show (0 : ℝ≥0∞) = ∫⁻ _ : Ω, (0 : ℝ≥0∞) ∂P from by simp]
  refine MeasureTheory.tendsto_lintegral_of_dominated_convergence'
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T,
      C * (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) ?_ ?_ hBfin hinner
  · exact fun m => (hFm m).lintegral_prod_right'.aemeasurable
  · exact fun m => Filter.Eventually.of_forall fun ω =>
      MeasureTheory.lintegral_mono fun s => hdom m ω s

end Energy

section PathIntegral

variable {Ω : Type u}

/-- Along a pointwise-convergent sequence of shifts the increment between two stopping times of a
bounded continuous function of a shifted process against an integrable coefficient converges. -/
theorem tendsto_setIntegral_stopped_sub_shift {n : ℕ} {X : ℝ → Ω → Fin n → ℝ}
    {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g) {K : ℝ} (hK : ∀ z, |g z| ≤ K)
    {D : Ω → ℝ → ℝ} {σ τ : Ω → WithTop ℝ} {T : ℝ} {ω : Ω}
    {c : Ω → Fin n → ℝ} {cm : ℕ → Ω → Fin n → ℝ}
    (hlim : Filter.Tendsto (fun m => cm m ω) Filter.atTop (nhds (c ω)))
    (hint : IntegrableOn (fun s => D ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hmeas : ∀ m : ℕ, AEStronglyMeasurable (fun s =>
        Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s)
      (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s) ∂volume)
      Filter.atTop (nhds (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + c ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + c ω) * D ω s) ω s) ∂volume)) := by
  have hK0 : (0 : ℝ) ≤ K := le_trans (abs_nonneg _) (hK 0)
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => 2 * (K * |D ω s|)) hmeas ((hint.abs.const_mul K).const_mul 2) ?_ ?_
  · -- the increment is dominated by twice the bound times the coefficient
    intro m
    refine Filter.Eventually.of_forall fun s => ?_
    refine le_trans (abs_stopped_sub_stopped_le σ τ
      (fun ω s => g (X s ω + cm m ω) * D ω s) ω s) ?_
    have : |g (X s ω + cm m ω) * D ω s| ≤ K * |D ω s| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hK _) (abs_nonneg _)
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  · -- the increment converges pointwise in the time variable
    refine Filter.Eventually.of_forall fun s => ?_
    have hg : Filter.Tendsto (fun m => g (X s ω + cm m ω) * D ω s) Filter.atTop
        (nhds (g (X s ω + c ω) * D ω s)) :=
      Filter.Tendsto.mul_const _ ((hgc.tendsto _).comp (Filter.Tendsto.const_add _ hlim))
    have hstop : ∀ (υ : Ω → WithTop ℝ), Filter.Tendsto
        (fun m => Probability.stopped υ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s)
        Filter.atTop
        (nhds (Probability.stopped υ (fun ω s => g (X s ω + c ω) * D ω s) ω s)) := by
      intro υ
      unfold LevyStochCalc.Probability.stopped
      by_cases hs : ((s : ℝ) : WithTop ℝ) ≤ υ ω
      · simpa [hs] using hg
      · simp [hs]
    exact (hstop τ).sub (hstop σ)

/-- The variant of `tendsto_setIntegral_stopped_sub_shift` in which the state function is bounded
only against the coefficient: it suffices that `|g z| · |D ω s| ≤ K · |D ω s|`. -/
theorem tendsto_setIntegral_stopped_sub_shift_of_mul {n : ℕ} {X : ℝ → Ω → Fin n → ℝ}
    {g : (Fin n → ℝ) → ℝ} (hgc : Continuous g) {D : Ω → ℝ → ℝ} {ω : Ω} {K : ℝ}
    (hK : ∀ (z : Fin n → ℝ) (s : ℝ), |g z| * |D ω s| ≤ K * |D ω s|)
    {σ τ : Ω → WithTop ℝ} {T : ℝ}
    {c : Ω → Fin n → ℝ} {cm : ℕ → Ω → Fin n → ℝ}
    (hlim : Filter.Tendsto (fun m => cm m ω) Filter.atTop (nhds (c ω)))
    (hint : IntegrableOn (fun s => D ω s) (Set.Ioc (0 : ℝ) T) volume)
    (hmeas : ∀ m : ℕ, AEStronglyMeasurable (fun s =>
        Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s)
      (volume.restrict (Set.Ioc (0 : ℝ) T))) :
    Filter.Tendsto (fun m => ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s) ∂volume)
      Filter.atTop (nhds (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => g (X s ω + c ω) * D ω s) ω s
          - Probability.stopped σ (fun ω s => g (X s ω + c ω) * D ω s) ω s) ∂volume)) := by
  refine MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun s => 2 * (K * |D ω s|)) hmeas ((hint.abs.const_mul K).const_mul 2) ?_ ?_
  · intro m
    refine Filter.Eventually.of_forall fun s => ?_
    refine le_trans (abs_stopped_sub_stopped_le σ τ
      (fun ω s => g (X s ω + cm m ω) * D ω s) ω s) ?_
    have : |g (X s ω + cm m ω) * D ω s| ≤ K * |D ω s| := by
      rw [abs_mul]
      exact hK _ s
    exact mul_le_mul_of_nonneg_left this (by norm_num)
  · refine Filter.Eventually.of_forall fun s => ?_
    have hg : Filter.Tendsto (fun m => g (X s ω + cm m ω) * D ω s) Filter.atTop
        (nhds (g (X s ω + c ω) * D ω s)) :=
      Filter.Tendsto.mul_const _ ((hgc.tendsto _).comp (Filter.Tendsto.const_add _ hlim))
    have hstop : ∀ (υ : Ω → WithTop ℝ), Filter.Tendsto
        (fun m => Probability.stopped υ (fun ω s => g (X s ω + cm m ω) * D ω s) ω s)
        Filter.atTop
        (nhds (Probability.stopped υ (fun ω s => g (X s ω + c ω) * D ω s) ω s)) := by
      intro υ
      unfold LevyStochCalc.Probability.stopped
      by_cases hs : ((s : ℝ) : WithTop ℝ) ≤ υ ω
      · simpa [hs] using hg
      · simp [hs]
    exact (hstop τ).sub (hstop σ)

end PathIntegral

section StochasticTerm

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- A vanishing energy distance between integrands gives a vanishing `L²` distance between their
Itô integrals. -/
theorem tendsto_lintegral_sq_stochInt_of_tendsto_energy
    (G : ℕ → Ω → ℝ → ℝ) (G₀ : Ω → ℝ → ℝ)
    (hmG : ∀ m, Measurable (Function.uncurry (G m)))
    (hpG : ∀ m, Probability.ProgressivelyMeasurable ℱ (G m))
    (hqG : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmG₀ : Measurable (Function.uncurry G₀))
    (hpG₀ : Probability.ProgressivelyMeasurable ℱ G₀)
    (hqG₀ : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hE : Filter.Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G m ω s - G₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun m => ∫⁻ ω,
        (‖stochasticIntegralBrownian W ℱ hℱ (G m) (hmG m) (hpG m) (hqG m) T ω
          - stochasticIntegralBrownian W ℱ hℱ G₀ hmG₀ hpG₀ hqG₀ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) :=
  hE.congr fun m => (isometry_diff_stochasticIntegralBrownian W ℱ hℱ (G m) G₀
    (hmG m) hmG₀ (hpG m) hpG₀ (hqG m) hqG₀ hT).symm

end StochasticTerm

section MultiChannel

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- Along a family of integrands indexed by finitely many Brownian channels whose energy distance
to a limiting family vanishes, the Itô integrals converge almost surely along a common
subsequence. -/
theorem exists_seq_ae_tendsto_stochInt_of_tendsto_energy {ι : Type*} [Fintype ι]
    (W : ι → LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : ∀ i, IsBrownianFiltration (W i) ℱ)
    (G : ℕ → ι → Ω → ℝ → ℝ) (G₀ : ι → Ω → ℝ → ℝ)
    (hmG : ∀ m i, Measurable (Function.uncurry (G m i)))
    (hpG : ∀ m i, Probability.ProgressivelyMeasurable ℱ (G m i))
    (hqG : ∀ (m : ℕ) (i : ι) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G m i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmG₀ : ∀ i, Measurable (Function.uncurry (G₀ i)))
    (hpG₀ : ∀ i, Probability.ProgressivelyMeasurable ℱ (G₀ i))
    (hqG₀ : ∀ (i : ι) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖G₀ i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hE : ∀ i, Filter.Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖G m i ω s - G₀ i ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (nhds 0)) :
    ∃ ms : ℕ → ℕ, (∀ m : ℕ, m ≤ ms m) ∧ ∀ᵐ ω ∂P, ∀ i : ι, Filter.Tendsto
      (fun m => stochasticIntegralBrownian (W i) ℱ (hℱ i) (G (ms m) i)
        (hmG (ms m) i) (hpG (ms m) i) (hqG (ms m) i) T ω)
      Filter.atTop (nhds (stochasticIntegralBrownian (W i) ℱ (hℱ i) (G₀ i)
        (hmG₀ i) (hpG₀ i) (hqG₀ i) T ω)) := by
  refine exists_seq_ae_tendsto_of_tendsto_lintegral (μ := P) (ι := ι)
    (u := fun m i ω => stochasticIntegralBrownian (W i) ℱ (hℱ i) (G m i)
      (hmG m i) (hpG m i) (hqG m i) T ω)
    (v := fun i ω => stochasticIntegralBrownian (W i) ℱ (hℱ i) (G₀ i)
      (hmG₀ i) (hpG₀ i) (hqG₀ i) T ω)
    (fun m i => ((stochasticIntegralBrownian_stronglyAdapted (W i) ℱ (hℱ i) _
      (hmG m i) (hpG m i) (hqG m i) T).mono (ℱ.le T)).measurable)
    (fun i => ((stochasticIntegralBrownian_stronglyAdapted (W i) ℱ (hℱ i) _
      (hmG₀ i) (hpG₀ i) (hqG₀ i) T).mono (ℱ.le T)).measurable)
    fun i => tendsto_lintegral_sq_stochInt_of_tendsto_energy (W i) ℱ (hℱ i)
      (fun m => G m i) (G₀ i) (fun m => hmG m i) (fun m => hpG m i) (fun m => hqG m i)
      (hmG₀ i) (hpG₀ i) (hqG₀ i) hT (hE i)

end MultiChannel

end LevyStochCalc.Brownian.Ito
