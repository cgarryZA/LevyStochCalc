/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoLocality

/-!
# Almost-everywhere dependence of the Itô integral on its integrand

Two integrands that agree for `P ⊗ ds`-almost every sample point and time of a window have the
same Itô integral at the end of that window: the `L²`-isometry for the difference of two Itô
integrals turns the vanishing of the energy of the difference of the integrands into the almost
sure vanishing of the difference of the integrals. Agreement off a countable set of times for
each sample point is a special case, because a countable set of reals is Lebesgue null. It is the
case met by a path translated by a vector that tracks a second path only strictly between two
stopping times: the increments of the two cut-off integrands can part at the later of the two
times and nowhere else.

## Main statements

* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_ae` — integrands agreeing almost
  everywhere on a window have the same Itô integral at the end of the window.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_countable` — the same for
  integrands agreeing off a countable set of times at each sample point.
* `LevyStochCalc.Brownian.Ito.stopped_sub_congr_of_lt` — the increment of a cut-off integrand
  between two times depends on the integrand only at the times strictly between them, away from
  the later time.
* `LevyStochCalc.Brownian.Ito.integral_stopped_sub_shift_of_lt` — the Lebesgue integral of the
  increment of the cut-off integrand of a translated path agreeing with a second path strictly
  between the two times.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_sub_shift_congr_of_lt` — the
  corresponding identity for the Itô integral.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section CountableTimes

/-- The times carried to a given value of `WithTop ℝ` form a countable set. -/
theorem countable_setOf_coe_eq (c : WithTop ℝ) :
    {s : ℝ | ((s : ℝ) : WithTop ℝ) = c}.Countable := by
  refine Set.Subsingleton.countable ?_
  intro a ha b hb
  have h : ((a : ℝ) : WithTop ℝ) = ((b : ℝ) : WithTop ℝ) := ha.trans hb.symm
  exact_mod_cast h

/-- Almost every time is carried to a value of `WithTop ℝ` other than a given one. -/
theorem ae_coe_ne (c : WithTop ℝ) : ∀ᵐ s : ℝ ∂volume, ((s : ℝ) : WithTop ℝ) ≠ c := by
  have h : {s : ℝ | ¬ ((s : ℝ) : WithTop ℝ) ≠ c} = {s : ℝ | ((s : ℝ) : WithTop ℝ) = c} := by
    ext s
    simp
  rw [MeasureTheory.ae_iff, h]
  exact (countable_setOf_coe_eq c).measure_zero volume

end CountableTimes

section AeCongr

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **Two integrands agreeing almost everywhere on a window have the same Itô integral at the end
of that window.** -/
theorem stochasticIntegralBrownian_congr_ae
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂volume.restrict (Set.Icc (0 : ℝ) T), H₁ ω s = H₂ ω s) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by
  have hinner : ∀ᵐ ω ∂P, (∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) = 0 := by
    filter_upwards [hae] with ω hω
    have hz : (fun s => (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2)
        =ᵐ[volume.restrict (Set.Icc (0 : ℝ) T)] fun _ => 0 := by
      filter_upwards [hω] with s hs
      simp [hs]
    rw [MeasureTheory.lintegral_congr_ae hz, MeasureTheory.lintegral_zero]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P = 0 := by
    have h := MeasureTheory.lintegral_congr_ae (μ := P) hinner
    simpa using h
  have hiso := isometry_diff_stochasticIntegralBrownian W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hT
  have hL : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞) ^ 2 ∂P = 0 :=
    hiso.trans hR
  have h1 : Measurable (stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H₁ hm₁ hp₁ hq₁ T).mono
      (ℱ.le T)).measurable
  have h2 : Measurable (stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H₂ hm₂ hp₂ hq₂ T).mono
      (ℱ.le T)).measurable
  have hmeas : Measurable fun ω => (‖stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞) ^ 2 :=
    (((h1.sub h2).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hzero := (MeasureTheory.lintegral_eq_zero_iff hmeas).mp hL
  filter_upwards [hzero] with ω hω
  have h0 : ((‖stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ : ℝ≥0∞)) = 0 := by
    simpa [pow_eq_zero_iff] using hω
  have hnn : ‖stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω‖₊ = 0 := by
    exact_mod_cast h0
  have hsub : stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T ω = 0 := by
    simpa using hnn
  linarith [hsub]

include hℱ in
/-- **Two integrands agreeing off a countable set of times at each sample point have the same Itô
integral.** -/
theorem stochasticIntegralBrownian_congr_of_countable
    {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry H₂))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {D : Ω → Set ℝ} (hD : ∀ ω, (D ω).Countable)
    (hagree : ∀ (ω : Ω) (s : ℝ), s ∉ D ω → H₁ ω s = H₂ ω s)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ T := by
  refine stochasticIntegralBrownian_congr_ae W ℱ hℱ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hT ?_
  refine Filter.Eventually.of_forall fun ω => MeasureTheory.ae_restrict_of_ae ?_
  have hsub : {s : ℝ | ¬ H₁ ω s = H₂ ω s} ⊆ D ω := by
    intro s hs
    by_contra hsD
    exact hs (hagree ω s hsD)
  rw [MeasureTheory.ae_iff]
  exact MeasureTheory.measure_mono_null hsub ((hD ω).measure_zero volume)

end AeCongr

section StoppedSupport

variable {Ω : Type*}

/-- The increment of a cut-off integrand between two times depends on the integrand only at the
times strictly between them, away from the later of the two. -/
theorem stopped_sub_congr_of_lt {K L : Ω → ℝ → ℝ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω)
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) < τ₁ ω →
      K ω s = L ω s)
    {s : ℝ} (hs : ((s : ℝ) : WithTop ℝ) ≠ τ₁ ω) :
    Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s
      = Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s := by
  by_cases h₀ : ((s : ℝ) : WithTop ℝ) ≤ τ₀ ω
  · have h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω := h₀.trans hmono
    simp [Probability.stopped, h₀, h₁]
  · have hlt : τ₀ ω < ((s : ℝ) : WithTop ℝ) := not_le.mp h₀
    by_cases h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω
    · simp [Probability.stopped, h₀, h₁, hagree s hlt (lt_of_le_of_ne h₁ hs)]
    · simp [Probability.stopped, h₀, h₁]

/-- Strictly between two times on which a translated path agrees with a second path, and away
from the later of the two, the increment of the cut-off integrand built from the translated path
is the increment of the one built from the second path. -/
theorem stopped_sub_shift_apply_of_lt {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω) (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ)
    {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) < τ₁ ω →
      V s ω + b ω = X s ω)
    {s : ℝ} (hs : ((s : ℝ) : WithTop ℝ) ≠ τ₁ ω) :
    Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
      = Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s :=
  stopped_sub_congr_of_lt hmono (fun s h₁ h₂ => by rw [hagree s h₁ h₂]) hs

/-- The Lebesgue integral of the increment of the cut-off integrand of a path translated by a
vector agreeing with a second path strictly between two times is the integral of the increment of
the integrand built from that second path. -/
theorem integral_stopped_sub_shift_of_lt {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω) (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ)
    {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) < τ₁ ω →
      V s ω + b ω = X s ω) (A : Set ℝ) :
    (∫ s in A, (Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s) ∂volume)
      = ∫ s in A, (Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s) ∂volume := by
  refine MeasureTheory.integral_congr_ae (MeasureTheory.ae_restrict_of_ae ?_)
  filter_upwards [ae_coe_ne (τ₁ ω)] with s hs
  exact stopped_sub_shift_apply_of_lt hmono Φ g hagree hs

end StoppedSupport

section StoppedIto

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **The Itô integrals of the increments of two cut-off integrands agreeing strictly between the
two times agree almost surely.** -/
theorem stochasticIntegralBrownian_stopped_sub_congr_of_lt
    {K L : Ω → ℝ → ℝ} {τ₀ τ₁ : Ω → WithTop ℝ} (hmono : ∀ ω, τ₀ ω ≤ τ₁ ω)
    (hagree : ∀ (ω : Ω) (s : ℝ), τ₀ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < τ₁ ω → K ω s = L ω s)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s)
        hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s)
        hm₂ hp₂ hq₂ T := by
  refine stochasticIntegralBrownian_congr_of_countable W ℱ hℱ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂
    (D := fun ω => {s : ℝ | ((s : ℝ) : WithTop ℝ) = τ₁ ω})
    (fun ω => countable_setOf_coe_eq (τ₁ ω)) ?_ hT
  intro ω s hs
  exact stopped_sub_congr_of_lt (hmono ω) (hagree ω) hs

include hℱ in
/-- **The Itô integral of the increment of the cut-off integrand of a path translated by a vector
agreeing with a second path strictly between two times is the Itô integral of the increment of
the integrand built from that second path.** -/
theorem stochasticIntegralBrownian_stopped_sub_shift_congr_of_lt
    {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} (hmono : ∀ ω, τ₀ ω ≤ τ₁ ω)
    (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ)
    {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ (ω : Ω) (s : ℝ), τ₀ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) < τ₁ ω → V s ω + b ω = X s ω)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s)
    (hq₁ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s)
    (hq₂ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s)
        hm₁ hp₁ hq₁ T
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s)
        hm₂ hp₂ hq₂ T :=
  stochasticIntegralBrownian_stopped_sub_congr_of_lt W ℱ hℱ hmono
    (fun ω s h₁ h₂ => by rw [hagree ω s h₁ h₂]) hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hT

end StoppedIto

end LevyStochCalc.Brownian.Ito
