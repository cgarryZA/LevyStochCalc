/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CrossElementary
import LevyStochCalc.Brownian.CrossOrthogonality

/-!
# Elementary integrals against the two drivers are orthogonal

An elementary Brownian integral and the compensated integral of a mark-step integrand expand
into finite sums of cross terms, one for each pair of cells. Clamping a cell to a running time
either collapses it, killing the term, or leaves its left endpoint alone, where the coefficient
is measurable; so every term has zero mean and the pairing vanishes at any pair of times.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open Brownian.Multidim.MultidimBrownianMotion (min_eq_or_lt_min)

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

/-- A Brownian increment and a compensated mass, both with bounded coefficients, have an
integrable product. -/
theorem integrable_cross_term (D : LevyDriver.{u, v, w} P d ν) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    {ξ η : Ω → ℝ} (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    Integrable (fun ω => (ξ ω * ((D.W.W i).W q ω - (D.W.W i).W p ω))
      * (η ω * D.N.compensated (Set.Ioc r v ×ˢ A) ω)) P :=
  Poisson.Compensated.integrable_mul_of_memLp_two
    (Brownian.Ito.memLp_mul_increment (D.W.W i) hp hpq 2 (by simp) hξm hξb)
    (Poisson.Compensated.memLp_bdd_mul hηm hηb
      (Poisson.Compensated.compensated_memLp D.N (measurableSet_Ioc.prod hA)
        (Poisson.Compensated.referenceIntensity_Ioc_prod_ne_top hAν)))

/-- A single clamped cross term is integrable and has zero mean. -/
theorem integrable_and_integral_cross_clamped (𝒲 : CrossWitness D ℱ) {i : Fin d} {p q r v : ℝ}
    (hp : 0 ≤ p) (hpq : p < q) (hr : 0 ≤ r) (hrv : r < v) {A : Set E} (hA : MeasurableSet A)
    (hAν : ν A ≠ ⊤) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ) (hξm : Measurable ξ)
    {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
    Integrable (fun ω => (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
        * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω)) P
      ∧ ∫ ω, (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
        * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω) ∂P = 0 := by
  rcases min_eq_or_lt_min hpq t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
        * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω))
        = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
  · rcases min_eq_or_lt_min hrv t' with hc' | ⟨hre, hrlt⟩
    · have hz : (fun ω => (ξ ω * ((D.W.W i).W (min q t) ω - (D.W.W i).W (min p t) ω))
          * (η ω * D.N.compensated (Set.Ioc (min r t') (min v t') ×ˢ A) ω))
          = fun _ => (0 : ℝ) := by
        funext ω
        rw [hc', Poisson.Compensated.MarkStep.compensated_Ioc_self D.N (min v t') A ω]
        ring
      rw [hz]
      exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
    · rw [hpe, hre]
      exact ⟨integrable_cross_term D hp hplt hA hAν hξm hξb hηm hηb,
        integral_cross_term_eq_zero 𝒲 hp hplt hr hrlt hA hAν hξ hξm hξb hη hηm hηb⟩

/-- **Orthogonality on elementary integrands.** An elementary Brownian integral and the
compensated integral of a mark-step integrand have zero pairing, at any pair of times. -/
theorem integral_simpleIntegral_mul_markStep_eq_zero (𝒲 : CrossWitness D ℱ) {i : Fin d}
    {TH : ℝ} (H : Brownian.Ito.SimplePredictable Ω TH)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    {g : Poisson.Compensated.TimeGrid} (G : Poisson.Compensated.MarkStep Ω E ν g) (hG : G.Adapted ℱ) (t t' : ℝ) :
    ∫ ω, Brownian.Ito.simpleIntegral (D.W.W i) H t ω * G.integral D.N t' ω ∂P = 0 := by
  have hHnn : ∀ a : Fin H.N, 0 ≤ H.partition a.castSucc := fun a => by
    have h := H.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [H.partition_zero] at h
  have hHlt : ∀ a : Fin H.N, H.partition a.castSucc < H.partition a.succ := fun a =>
    H.partition_strictMono Fin.castSucc_lt_succ
  have key : ∀ (a : Fin H.N) (j : ℕ), j < g.N₀ → ∀ k : Fin G.K,
      Integrable (fun ω => (H.ξ a ω * ((D.W.W i).W (min (H.partition a.succ) t) ω
            - (D.W.W i).W (min (H.partition a.castSucc) t) ω))
          * (G.ξ j k ω * D.N.compensated
            (Set.Ioc (min (g.p j) t') (min (g.p (j + 1)) t') ×ˢ G.B k) ω)) P
        ∧ ∫ ω, (H.ξ a ω * ((D.W.W i).W (min (H.partition a.succ) t) ω
            - (D.W.W i).W (min (H.partition a.castSucc) t) ω))
          * (G.ξ j k ω * D.N.compensated
            (Set.Ioc (min (g.p j) t') (min (g.p (j + 1)) t') ×ˢ G.B k) ω) ∂P = 0 := by
    intro a j hj k
    obtain ⟨Mξ, hMξ⟩ := H.ξ_bounded a
    obtain ⟨Mη, hMη⟩ := G.ξ_bounded j k
    exact integrable_and_integral_cross_clamped 𝒲 (hHnn a) (hHlt a) (g.p_nonneg hj.le)
      (g.p_lt j hj) (G.B_measurable k) (G.B_finite k) (hH a) (H.ξ_measurable a) hMξ
      (hG j hj k) (G.ξ_measurable j k) hMη t t'
  have hexp : (fun ω => Brownian.Ito.simpleIntegral (D.W.W i) H t ω * G.integral D.N t' ω)
      = fun ω => ∑ a : Fin H.N, ∑ j ∈ Finset.range g.N₀, ∑ k,
        (H.ξ a ω * ((D.W.W i).W (min (H.partition a.succ) t) ω
            - (D.W.W i).W (min (H.partition a.castSucc) t) ω))
          * (G.ξ j k ω * D.N.compensated
            (Set.Ioc (min (g.p j) t') (min (g.p (j + 1)) t') ×ˢ G.B k) ω) := by
    funext ω
    rw [Brownian.Ito.simpleIntegral, Poisson.Compensated.MarkStep.integral,
      Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ =>
      Finset.mul_sum _ _ _
  rw [hexp, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun j hj =>
    integrable_finsetSum _ fun k _ => (key a j (Finset.mem_range.mp hj) k).1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun j hj => integrable_finsetSum _ fun k _ =>
    (key a j (Finset.mem_range.mp hj) k).1]
  refine Finset.sum_eq_zero fun j hj => ?_
  rw [integral_finsetSum _ fun k _ => (key a j (Finset.mem_range.mp hj) k).1]
  exact Finset.sum_eq_zero fun k _ => (key a j (Finset.mem_range.mp hj) k).2

end LevyDriver

end LevyStochCalc.Driver
