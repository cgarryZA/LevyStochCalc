/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpTelescope
import LevyStochCalc.Ito.ItoFormulaIncrement

/-!
# Itô's formula along a chain of stopping times

A path that evolves continuously between the members of a chain of times and is translated by a
vector held fixed on each of the intervals they cut out satisfies, after composition with a
function of the state, a telescoping identity: the increment over the whole window is the sum of
the increments with the translation frozen on each interval plus the sum of the increments of the
translation at the right endpoints. Where the translated path agrees with a second path, the
integrands of the per-interval Itô formulas coincide with the integrands built from that second
path, so the per-interval Lebesgue and Itô integrals collapse into single integrals over the
window.

## Main statements

* `LevyStochCalc.Brownian.Ito.sum_range_shift_telescope` — the pathwise telescoping identity.
* `LevyStochCalc.Brownian.Ito.stopped_sub_congr` — the increment of a cut-off integrand between
  two times depends on the integrand only between them.
* `LevyStochCalc.Brownian.Ito.stopped_sub_shift_funext` — the increment of the cut-off integrand
  of a translated path is the increment of the cut-off integrand of the path it agrees with.
* `LevyStochCalc.Brownian.Ito.sum_range_integral_stopped_sub_of_chain` — the Lebesgue integrals
  of the increments along a chain covering `(0, T]` sum to the integral over that window.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_sum_range_stopped_sub_of_chain` — the
  Itô integrals of those increments sum to the Itô integral over that window.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain` — Itô's formula over the window for a path
  translated piecewise along a chain, with the per-interval increments as a hypothesis.
* `LevyStochCalc.Brownian.Ito.itoFormula_chain_path` — the same with the two endpoints
  identified with the values of the path the translations agree with.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal

universe u

section Pathwise

variable {Ω : Type*}

/-- The increment of a function of a path translated piecewise along a family of times splits
into the increments with the translation frozen on each interval and the increments of the
translation at the right endpoints. -/
theorem sum_range_shift_telescope {n : ℕ} (f : (Fin n → ℝ) → ℝ) (V : ℝ → Ω → Fin n → ℝ)
    (c : ℕ → Ω → Fin n → ℝ) (θ : ℕ → Ω → ℝ) (m : ℕ) (ω : Ω) :
    f (V (θ m ω) ω + c m ω) - f (V (θ 0 ω) ω + c 0 ω)
      = (∑ k ∈ Finset.range m,
            (f (V (θ (k + 1) ω) ω + c k ω) - f (V (θ k ω) ω + c k ω)))
        + ∑ k ∈ Finset.range m,
            (f (V (θ (k + 1) ω) ω + c (k + 1) ω) - f (V (θ (k + 1) ω) ω + c k ω)) := by
  have hsum : ∑ k ∈ Finset.range m,
        ((f (V (θ (k + 1) ω) ω + c k ω) - f (V (θ k ω) ω + c k ω))
          + (f (V (θ (k + 1) ω) ω + c (k + 1) ω) - f (V (θ (k + 1) ω) ω + c k ω)))
      = ∑ k ∈ Finset.range m,
          (f (V (θ (k + 1) ω) ω + c (k + 1) ω) - f (V (θ k ω) ω + c k ω)) :=
    Finset.sum_congr rfl fun k _ => by ring
  rw [← Finset.sum_add_distrib, hsum]
  exact (Finset.sum_range_sub (fun i => f (V (θ i ω) ω + c i ω)) m).symm

/-- The horizon clipped at a time equal to `0` is `0`. -/
theorem clipTime_eq_zero {τ : Ω → WithTop ℝ} {T : ℝ} {ω : Ω} (hT : 0 ≤ T)
    (h : τ ω = ((0 : ℝ) : WithTop ℝ)) : clipTime τ T ω = 0 := by
  rw [clipTime_eq_min h, min_eq_right hT]

/-- The horizon clipped at a time squeezed between `0` and `0` is `0`. -/
theorem clipTime_eq_zero_of_le_zero {τ : Ω → WithTop ℝ} {T : ℝ} {ω : Ω} (hT : 0 ≤ T)
    (hle : ((0 : ℝ) : WithTop ℝ) ≤ τ ω) (hge : τ ω ≤ ((0 : ℝ) : WithTop ℝ)) :
    clipTime τ T ω = 0 :=
  clipTime_eq_zero hT (le_antisymm hge hle)

end Pathwise

section Support

variable {Ω : Type*}

/-- The increment of a cut-off integrand between two times depends on the integrand only at the
times strictly beyond the first and at or before the second. -/
theorem stopped_sub_congr {K L : Ω → ℝ → ℝ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω}
    (hmono : τ₀ ω ≤ τ₁ ω)
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω →
      K ω s = L ω s) (s : ℝ) :
    Probability.stopped τ₁ K ω s - Probability.stopped τ₀ K ω s
      = Probability.stopped τ₁ L ω s - Probability.stopped τ₀ L ω s := by
  by_cases h₀ : ((s : ℝ) : WithTop ℝ) ≤ τ₀ ω
  · have h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω := h₀.trans hmono
    simp [Probability.stopped, h₀, h₁]
  · have hlt : τ₀ ω < ((s : ℝ) : WithTop ℝ) := not_le.mp h₀
    by_cases h₁ : ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω
    · simp [Probability.stopped, h₀, h₁, hagree s hlt h₁]
    · simp [Probability.stopped, h₀, h₁]

/-- Between two times on which a translated path agrees with a second path, the increment of the
cut-off integrand built from the translated path is the increment of the one built from the
second path. -/
theorem stopped_sub_shift_apply {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} {ω : Ω} (hmono : τ₀ ω ≤ τ₁ ω)
    (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ) {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ s : ℝ, τ₀ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω →
      V s ω + b ω = X s ω) (s : ℝ) :
    Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
      = Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
        - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s :=
  stopped_sub_congr hmono (fun s h₁ h₂ => by rw [hagree s h₁ h₂]) s

/-- The two integrands of `stopped_sub_shift_apply` agree as functions of the sample point and
the time. -/
theorem stopped_sub_shift_funext {n : ℕ} {τ₀ τ₁ : Ω → WithTop ℝ} (hmono : ∀ ω, τ₀ ω ≤ τ₁ ω)
    (Φ : (Fin n → ℝ) → ℝ) (g : Ω → ℝ → ℝ) {V X : ℝ → Ω → Fin n → ℝ} {b : Ω → Fin n → ℝ}
    (hagree : ∀ (ω : Ω) (s : ℝ), τ₀ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) ≤ τ₁ ω → V s ω + b ω = X s ω) :
    (fun (ω : Ω) (s : ℝ) =>
        Probability.stopped τ₁ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (V s ω + b ω) * g ω s) ω s)
      = fun ω s => Probability.stopped τ₁ (fun ω s => Φ (X s ω) * g ω s) ω s
          - Probability.stopped τ₀ (fun ω s => Φ (X s ω) * g ω s) ω s :=
  funext fun ω => funext fun s => stopped_sub_shift_apply (hmono ω) Φ g (hagree ω) s

end Support

section Collapse

variable {Ω : Type*}

/-- Along a chain of times covering `(0, T]` the integrals of the increments of a cut-off
integrand sum to the integral of the integrand over that window. -/
theorem sum_range_integral_stopped_sub_of_chain (σ : ℕ → Ω → WithTop ℝ) (K : Ω → ℝ → ℝ)
    {m : ℕ} {T : ℝ} {ω : Ω} (h0 : σ 0 ω ≤ ((0 : ℝ) : WithTop ℝ))
    (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m ω)
    (hint : ∀ k, MeasureTheory.IntegrableOn
      (Probability.stopped (σ k) K ω) (Set.Ioc (0 : ℝ) T) volume) :
    ∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s) ∂volume
      = ∫ s in Set.Ioc (0 : ℝ) T, K ω s ∂volume := by
  have hsum : (∫ s in Set.Ioc (0 : ℝ) T, (∑ k ∈ Finset.range m,
          (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s)) ∂volume)
      = ∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s) ∂volume :=
    MeasureTheory.integral_finsetSum _ fun k _ => (hint (k + 1)).sub (hint k)
  rw [← hsum]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs =>
    sum_range_stopped_eq_of_chain σ K h0 hm hs

end Collapse

section ItoCollapse

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- Along a chain of times covering `(0, T]` the Itô integrals of the increments of a cut-off
integrand sum to the Itô integral of the integrand at `T`. -/
theorem stochasticIntegralBrownian_sum_range_stopped_sub_of_chain
    (σ : ℕ → Ω → WithTop ℝ) (hσ : ∀ k, MeasureTheory.IsStoppingTime ℱ (σ k))
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {m : ℕ} {T : ℝ} (h0 : ∀ ω, σ 0 ω ≤ ((0 : ℝ) : WithTop ℝ))
    (hm : ∀ ω, ((T : ℝ) : WithTop ℝ) ≤ σ m ω) (hT : 0 < T) :
    (fun ω => ∑ k ∈ Finset.range m, stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s)
        (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) hmK)
        (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) hpK)
        (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) hmK hqK) T ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK T := by
  classical
  obtain ⟨hms, hps, hqs, hae⟩ := exists_stochasticIntegralBrownian_finsetSum W ℱ hℱ
    (fun k ω s => Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s)
    (fun k => measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) hmK)
    (fun k => progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) hpK)
    (fun k => energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) hmK hqK) (Finset.range m) hT
  have hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ σ m ω →
      (∑ k ∈ Finset.range m,
          (Probability.stopped (σ (k + 1)) K ω s - Probability.stopped (σ k) K ω s))
        = K ω s := by
    intro ω s hs hsm
    rw [sum_range_stopped_sub, stopped_eq_zero_of_le_zero K (h0 ω) hs, sub_zero]
    simp [Probability.stopped, hsm]
  have hcongr := stochasticIntegralBrownian_congr_of_le (σ m) W ℱ hℱ (hσ m)
    hms hps hqs hmK hpK hqK hagree hT
  filter_upwards [hae, hcongr] with ω h1 h2
  exact h1.symm.trans (h2 (hm ω))

end ItoCollapse

section Algebra

/-- A sum over a range of the three terms of an Itô formula collapses termwise. -/
theorem sum_range_itoTerms {n d m : ℕ} {a : ℕ → Fin n → ℝ} {b : ℕ → Fin n → Fin d → ℝ}
    {e : ℕ → Fin n → Fin n → ℝ} {A : Fin n → ℝ} {B : Fin n → Fin d → ℝ}
    {E : Fin n → Fin n → ℝ} (ha : ∀ p, ∑ k ∈ Finset.range m, a k p = A p)
    (hb : ∀ p j, ∑ k ∈ Finset.range m, b k p j = B p j)
    (he : ∀ p q, ∑ k ∈ Finset.range m, e k p q = E p q) :
    ∑ k ∈ Finset.range m,
        ((∑ p : Fin n, a k p) + (∑ p : Fin n, ∑ j : Fin d, b k p j)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, e k p q)
      = (∑ p : Fin n, A p) + (∑ p : Fin n, ∑ j : Fin d, B p j)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, E p q := by
  have h1 : ∑ k ∈ Finset.range m, ∑ p : Fin n, a k p = ∑ p : Fin n, A p := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun p _ => ha p
  have h2 : ∑ k ∈ Finset.range m, ∑ p : Fin n, ∑ j : Fin d, b k p j
      = ∑ p : Fin n, ∑ j : Fin d, B p j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => hb p j
  have h3 : ∑ k ∈ Finset.range m, ∑ p : Fin n, ∑ q : Fin n, e k p q
      = ∑ p : Fin n, ∑ q : Fin n, E p q := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => he p q
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3]

end Algebra


section Assembly

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Finitely many almost-everywhere identities hold simultaneously almost everywhere. -/
theorem ae_forall_lt {F G : ℕ → Ω → ℝ} {m : ℕ} (h : ∀ k < m, F k =ᵐ[P] G k) :
    ∀ᵐ ω ∂P, ∀ k < m, F k ω = G k ω := by
  rw [MeasureTheory.ae_all_iff]
  intro k
  by_cases hk : k < m
  · filter_upwards [h k hk] with ω hω
    exact fun _ => hω
  · exact Filter.Eventually.of_forall fun _ hk' => absurd hk' hk

variable {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ j : Fin d, IsBrownianFiltration (W.W j) ℱ')

include hcoord in
/-- **Itô's formula over `(0, T]` for a path translated by a vector held fixed between the
members of a chain of stopping times.** The increment of the composition is a drift integral, an
Itô integral and a quadratic integral of the integrands built from the path the translated path
agrees with, plus the increments of the composition across the translations. -/
theorem itoFormula_chain
    {H : Fin n → Fin d → Ω → ℝ → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
    {V X : ℝ → Ω → Fin n → ℝ} {c : ℕ → Ω → Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    {σ : ℕ → Ω → WithTop ℝ} (hσ : ∀ k, MeasureTheory.IsStoppingTime ℱ' (σ k))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hmG : ∀ (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s))
    (hpG : ∀ (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
    (hqG : ∀ (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s))
    (hqD : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s))
    (hqQ : ∀ (p q : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s))
    (hpV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s)
    (hqV : ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (V s ω + c k ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmT : ∀ ω, ((T : ℝ) : WithTop ℝ) ≤ σ m ω)
    (hshift : ∀ (k : ℕ) (ω : Ω) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) ≤ σ (k + 1) ω → V s ω + c k ω = X s ω)
    (hcont : ∀ k < m, (fun ω : Ω => f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
          - f (V (clipTime (σ k) T ω) ω + c k ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (σ (k + 1))
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
              - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => Probability.stopped (σ (k + 1))
                  (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
                - Probability.stopped (σ k)
                    (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
              (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmV k p j))
              (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpV k p j))
              (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmV k p j) (hqV k p j)) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (σ (k + 1)) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
                - Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                    * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume) :
    (fun ω : Ω => f (V T ω + c m ω) - f (V 0 ω + c 0 ω)) =ᵐ[P] fun ω : Ω =>
      ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
              (hmG p j) (hpG p j) (hqG p j) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * (∑ j : Fin d, H p j ω s * H q j ω s) ∂volume)
        + ∑ k ∈ Finset.range m, (f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
            - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)) := by
  classical
  have hBfun : ∀ (k : ℕ) (p : Fin n) (j : Fin d),
      stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => Probability.stopped (σ (k + 1))
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
          (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmV k p j))
          (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpV k p j))
          (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmV k p j) (hqV k p j)) T
        = stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => Probability.stopped (σ (k + 1))
              (fun ω s => coordDeriv f' p (X s ω) * H p j ω s) ω s
            - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (X s ω) * H p j ω s) ω s)
          (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmG p j))
          (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpG p j))
          (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmG p j) (hqG p j)) T := by
    intro k p j
    exact stochasticIntegralBrownian_congr_fun (W.W j) ℱ' (hcoord j)
      (stopped_sub_shift_funext (fun ω => hmono k ω) (coordDeriv f' p) (H p j)
        (fun ω s h₁ h₂ => hshift k ω s h₁ h₂)) _ _ _ _ _ _ T
  have hDint : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : ℕ), MeasureTheory.IntegrableOn
      (Probability.stopped (σ k) (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω)
      (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact ae_integrableOn_stopped_Ioc (hσ k) (hmD p) (hqD p) hT
  have hQint : ∀ᵐ ω ∂P, ∀ (p q : Fin n) (k : ℕ), MeasureTheory.IntegrableOn
      (Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (X s ω)
        * ∑ j : Fin d, H p j ω s * H q j ω s) ω) (Set.Ioc (0 : ℝ) T) volume := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro q
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact ae_integrableOn_stopped_Ioc (hσ k) (hmQ p q) (hqQ p q) hT
  have hBcol : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d),
      (∑ k ∈ Finset.range m, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => Probability.stopped (σ (k + 1))
              (fun ω s => coordDeriv f' p (X s ω) * H p j ω s) ω s
            - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (X s ω) * H p j ω s) ω s)
          (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmG p j))
          (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpG p j))
          (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmG p j) (hqG p j)) T ω)
        = stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmG p j) (hpG p j) (hqG p j) T ω := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro j
    exact stochasticIntegralBrownian_sum_range_stopped_sub_of_chain (W.W j) ℱ' (hcoord j)
      σ hσ (hmG p j) (hpG p j) (hqG p j) (fun ω => le_of_eq (h0 ω)) hmT hT
  have hcontAll := ae_forall_lt hcont
  filter_upwards [hcontAll, hBcol, hDint, hQint] with ω hcω hBω hDω hQω
  have hAk : ∀ (k : ℕ) (p : Fin n), (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1))
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
          - Probability.stopped (σ k)
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1))
            (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s
          - Probability.stopped (σ k)
              (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s) ∂volume :=
    fun k p => MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s =>
      stopped_sub_shift_apply (hmono k ω) (coordDeriv f' p) (bdrift p) (hshift k ω) s)
  have hQk : ∀ (k : ℕ) (p q : Fin n), (∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1)) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
            * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
          - Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1)) (fun ω s => coordDeriv₂ f'' p q (X s ω)
            * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
          - Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume :=
    fun k p q => MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun s =>
      stopped_sub_shift_apply (hmono k ω) (coordDeriv₂ f'' p q)
        (fun ω s => ∑ j : Fin d, H p j ω s * H q j ω s) (hshift k ω) s)
  have hA : ∀ p : Fin n, (∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1))
            (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
          - Probability.stopped (σ k)
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T, coordDeriv f' p (X s ω) * bdrift p ω s ∂volume := by
    intro p
    have hstep := Finset.sum_congr (s₂ := Finset.range m) rfl
      fun k (_ : k ∈ Finset.range m) => hAk k p
    rw [hstep]
    exact sum_range_integral_stopped_sub_of_chain σ
      (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s)
      (le_of_eq (h0 ω)) (hmT ω) fun k => hDω p k
  have hC : ∀ p q : Fin n, (∑ k ∈ Finset.range m, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped (σ (k + 1)) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
            * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
          - Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume)
      = ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (X s ω) * (∑ j : Fin d, H p j ω s * H q j ω s) ∂volume := by
    intro p q
    have hstep := Finset.sum_congr (s₂ := Finset.range m) rfl
      fun k (_ : k ∈ Finset.range m) => hQk k p q
    rw [hstep]
    exact sum_range_integral_stopped_sub_of_chain σ
      (fun ω s => coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s)
      (le_of_eq (h0 ω)) (hmT ω) fun k => hQω p q k
  have hB : ∀ (p : Fin n) (j : Fin d), (∑ k ∈ Finset.range m,
        stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => Probability.stopped (σ (k + 1))
              (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
            - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
          (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmV k p j))
          (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpV k p j))
          (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmV k p j) (hqV k p j)) T ω)
      = stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
          (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
          (hmG p j) (hpG p j) (hqG p j) T ω := by
    intro p j
    have hstep := Finset.sum_congr (s₂ := Finset.range m) rfl
      fun k (_ : k ∈ Finset.range m) => congrFun (hBfun k p j) ω
    rw [hstep]
    exact hBω p j
  have htel : f (V (clipTime (σ m) T ω) ω + c m ω) - f (V (clipTime (σ 0) T ω) ω + c 0 ω)
      = (∑ k ∈ Finset.range m, (f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
            - f (V (clipTime (σ k) T ω) ω + c k ω)))
        + ∑ k ∈ Finset.range m, (f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
            - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)) :=
    sum_range_shift_telescope f V c (fun k ω => clipTime (σ k) T ω) m ω
  rw [clipTime_of_le (hmT ω), clipTime_eq_zero hT.le (h0 ω)] at htel
  have hsub := Finset.sum_congr (s₂ := Finset.range m) rfl
    fun k (hk : k ∈ Finset.range m) => hcω k (Finset.mem_range.mp hk)
  rw [htel, hsub, sum_range_itoTerms hA hB hC]

include hcoord in
/-- **Itô's formula over `(0, T]` for a jump path split into a piecewise translated path.**
The increment of the composition with the path itself is the drift, Itô and quadratic
integrals over the window plus the increments of the composition across the translations. -/
theorem itoFormula_chain_path
    {H : Fin n → Fin d → Ω → ℝ → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ}
    {V X : ℝ → Ω → Fin n → ℝ} {c : ℕ → Ω → Fin n → ℝ}
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    {σ : ℕ → Ω → WithTop ℝ} (hσ : ∀ k, MeasureTheory.IsStoppingTime ℱ' (σ k))
    (hmono : ∀ (k : ℕ) (ω : Ω), σ k ω ≤ σ (k + 1) ω)
    (hmG : ∀ (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s))
    (hpG : ∀ (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
    (hqG : ∀ (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmD : ∀ p : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s))
    (hqD : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmQ : ∀ p q : Fin n, Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s))
    (hqQ : ∀ (p q : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hmV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s))
    (hpV : ∀ (k : ℕ) (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s)
    (hqV : ∀ (k : ℕ) (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (V s ω + c k ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) {m : ℕ} (h0 : ∀ ω, σ 0 ω = ((0 : ℝ) : WithTop ℝ))
    (hmT : ∀ ω, ((T : ℝ) : WithTop ℝ) ≤ σ m ω)
    (hshift : ∀ (k : ℕ) (ω : Ω) (s : ℝ), σ k ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) ≤ σ (k + 1) ω → V s ω + c k ω = X s ω)
    (hcont : ∀ k < m, (fun ω : Ω => f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)
          - f (V (clipTime (σ k) T ω) ω + c k ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped (σ (k + 1))
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s
              - Probability.stopped (σ k)
                (fun ω s => coordDeriv f' p (V s ω + c k ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => Probability.stopped (σ (k + 1))
                  (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s
                - Probability.stopped (σ k)
                    (fun ω s => coordDeriv f' p (V s ω + c k ω) * H p j ω s) ω s)
              (measurable_uncurry_stopped_sub (hσ k) (hσ (k + 1)) (hmV k p j))
              (progressivelyMeasurable_stopped_sub (hσ k) (hσ (k + 1)) (hpV k p j))
              (energy_stopped_sub_lt_top (hσ k) (hσ (k + 1)) (hmV k p j) (hqV k p j)) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped (σ (k + 1)) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s) ω s
                - Probability.stopped (σ k) (fun ω s => coordDeriv₂ f'' p q (V s ω + c k ω)
                    * ∑ j : Fin d, H p j ω s * H q j ω s) ω s) ∂volume)
    (hV0 : ∀ ω, V 0 ω + c 0 ω = X 0 ω) (hVT : ∀ ω, V T ω + c m ω = X T ω) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      ((∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ' (hcoord j)
              (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
              (hmG p j) (hpG p j) (hqG p j) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ f'' p q (X s ω) * (∑ j : Fin d, H p j ω s * H q j ω s) ∂volume)
        + ∑ k ∈ Finset.range m, (f (V (clipTime (σ (k + 1)) T ω) ω + c (k + 1) ω)
            - f (V (clipTime (σ (k + 1)) T ω) ω + c k ω)) := by
  filter_upwards [itoFormula_chain W ℱ' hcoord hσ hmono hmG hpG hqG hmD hqD hmQ hqQ hmV
    hpV hqV hT h0 hmT hshift hcont] with ω hω
  rw [hVT ω, hV0 ω] at hω
  exact hω

end Assembly

end LevyStochCalc.Brownian.Ito
