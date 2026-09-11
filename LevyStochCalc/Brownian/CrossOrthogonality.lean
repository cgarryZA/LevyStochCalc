/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.MultidimFiltered
import LevyStochCalc.Brownian.AugmentedFiltration
import LevyStochCalc.Brownian.ItoFourthMoment

/-!
# Orthogonality of Itô integrals against distinct Brownian coordinates

For a `d`-dimensional Brownian motion `W` whose coordinates are all Brownian motions for one
filtration `ℱ`, and distinct coordinates `i ≠ j`, integrals against `Wⁱ` and against `Wʲ` are
orthogonal in `L²`. The mechanism is the identity `E[Z (Wⁱ_b - Wⁱ_a)(Wʲ_b - Wʲ_a)] = 0` for a
bounded `ℱ_a`-measurable weight `Z`: along a uniform grid of `[a, b]`, the product of the two
increments telescopes into cell-wise terms, the terms with a past factor are killed by
conditioning, and the sum of the cell-wise cross products has second moment `(b - a)² / m` by
the independence of the two coordinates. Cross terms over intervals in any relative position
reduce to this identity by splitting at the later left endpoint.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

namespace Multidim.MultidimBrownianMotion

/-- Every coordinate is a Brownian motion for the augmented joint natural filtration. -/
theorem isBrownianFiltration_augNatural (W : MultidimBrownianMotion P d) (j : Fin d) :
    IsBrownianFiltration (W.W j) (augFiltration W.naturalFiltration P) :=
  isBrownianFiltration_augFiltration (W.isBrownianFiltration_natural j)

section DirectCross

/-- Borel functionals of the paths of two distinct coordinates are independent. -/
lemma indepFun_comp_coord (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {φ ψ : (ℝ → ℝ) → ℝ} (hφ : Measurable φ) (hψ : Measurable ψ) :
    IndepFun (fun ω => φ fun t => (W.W i).W t ω) (fun ω => ψ fun t => (W.W j).W t ω) P :=
  (W.components_independent.indepFun hij).comp hφ hψ

/-- An increment of a Brownian motion over a possibly degenerate interval is square-integrable. -/
lemma memLp_two_increment_of_le (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    MemLp (fun ω => V.W q ω - V.W p ω) 2 P := by
  rcases eq_or_lt_of_le hpq with h | h
  · subst h
    simp only [sub_self]
    exact memLp_const 0
  · exact Ito.memLp_increment V hp h 2 (by simp)

/-- Increments of a Brownian motion over two intervals, the second starting after the first
ends, are uncorrelated. -/
lemma integral_increment_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {p q r v : ℝ}
    (hpr : p ≤ r) (hqr : q ≤ r) (hr : 0 ≤ r) (hrv : r < v) :
    ∫ ω, (V.W q ω - V.W p ω) * (V.W v ω - V.W r ω) ∂P = 0 := by
  have hY : StronglyMeasurable[ℱ r] fun ω => V.W q ω - V.W p ω :=
    (((hV.measurable q).mono (ℱ.mono hqr) le_rfl).sub
      ((hV.measurable p).mono (ℱ.mono hpr) le_rfl)).stronglyMeasurable
  have hYm : Measurable fun ω => V.W q ω - V.W p ω :=
    (V.measurable_eval q).sub (V.measurable_eval p)
  have h := Ito.integral_mul_increment_pow V ℱ hV hr hrv hY hYm 1
  rw [Ito.integral_increment_pow_odd V hr hrv odd_one, mul_zero] at h
  simpa only [pow_one] using h

/-- The uniform grid `a, a + h, a + 2h, …`. -/
noncomputable def affineGrid (a h : ℝ) (k : ℕ) : ℝ := a + k * h

lemma affineGrid_zero (a h : ℝ) : affineGrid a h 0 = a := by simp [affineGrid]

lemma affineGrid_succ_sub (a h : ℝ) (k : ℕ) : affineGrid a h (k + 1) - affineGrid a h k = h := by
  simp only [affineGrid, Nat.cast_succ]; ring

lemma affineGrid_mono {a h : ℝ} (hh : 0 ≤ h) {k l : ℕ} (hkl : k ≤ l) :
    affineGrid a h k ≤ affineGrid a h l := by
  simp only [affineGrid]
  have hkl' : (k : ℝ) ≤ l := Nat.cast_le.2 hkl
  nlinarith

lemma affineGrid_lt_succ {a h : ℝ} (hh : 0 < h) (k : ℕ) :
    affineGrid a h k < affineGrid a h (k + 1) := by
  have := affineGrid_succ_sub a h k
  linarith

lemma le_affineGrid {a h : ℝ} (hh : 0 ≤ h) (k : ℕ) : a ≤ affineGrid a h k := by
  simpa [affineGrid_zero] using affineGrid_mono (a := a) hh (Nat.zero_le k)

lemma affineGrid_nonneg {a h : ℝ} (ha : 0 ≤ a) (hh : 0 ≤ h) (k : ℕ) : 0 ≤ affineGrid a h k :=
  ha.trans (le_affineGrid hh k)

/-- The second moment of the sum of cross products of the increments of two distinct
coordinates over the cells of a uniform grid. -/
lemma integral_crossSum_sq (W : MultidimBrownianMotion P d) {i j : Fin d} (hij : i ≠ j)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) :
    Integrable (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2) P
    ∧ ∫ ω, (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2 ∂P
      = m * h ^ 2 := by
  have hg0 : ∀ k : ℕ, 0 ≤ affineGrid a h k := affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, affineGrid a h k < affineGrid a h (k + 1) := affineGrid_lt_succ hh
  -- the functional on path space picking out the product of two increments
  have hφ : ∀ k l : ℕ, Measurable fun path : ℝ → ℝ =>
      (path (affineGrid a h (k + 1)) - path (affineGrid a h k))
        * (path (affineGrid a h (l + 1)) - path (affineGrid a h l)) := fun k l => by
    fun_prop
  have hind : ∀ k l : ℕ, IndepFun
      (fun ω => ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
        * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
      (fun ω => ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
        * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) P :=
    fun k l => indepFun_comp_coord W hij (hφ k l) (hφ k l)
  have hint2 : ∀ (V : BrownianMotion P) (k l : ℕ), Integrable
      (fun ω => (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
        * (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω)) P := fun V k l =>
    MemLp.integrable_mul (memLp_two_increment_of_le V (hg0 k) (hglt k).le)
      (memLp_two_increment_of_le V (hg0 l) (hglt l).le)
  have hcov : ∀ (V : BrownianMotion P), IsBrownianFiltration V ℱ → ∀ k l : ℕ,
      ∫ ω, (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
        * (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω) ∂P
        = if k = l then h else 0 := by
    intro V hV k l
    rcases lt_trichotomy k l with hkl | rfl | hlk
    · rw [if_neg hkl.ne]
      exact integral_increment_mul_increment_eq_zero V hV
        (affineGrid_mono hh.le hkl.le) (affineGrid_mono hh.le hkl) (hg0 l) (hglt l)
    · have hsq := Ito.integral_increment_sq V (hg0 k) (hglt k)
      rw [affineGrid_succ_sub] at hsq
      have hsq' : ∫ ω, (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
          * (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω) ∂P
          = ∫ ω, (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω) ^ 2 ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq _).symm)
      rw [if_pos rfl, hsq', hsq]
    · rw [if_neg hlk.ne']
      rw [show (fun ω => (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω)
          * (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω))
          = fun ω => (V.W (affineGrid a h (l + 1)) ω - V.W (affineGrid a h l) ω)
            * (V.W (affineGrid a h (k + 1)) ω - V.W (affineGrid a h k) ω) from
        funext fun ω => mul_comm _ _]
      exact integral_increment_mul_increment_eq_zero V hV
        (affineGrid_mono hh.le hlk.le) (affineGrid_mono hh.le hlk) (hg0 k) (hglt k)
  have hterm : ∀ k l : ℕ,
      ∫ ω, (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) ∂P
        = if k = l then h ^ 2 else 0 := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
        * (((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    have hmul := (hind k l).integral_mul_eq_mul_integral
      (hint2 (W.W i) k l).1 (hint2 (W.W j) k l).1
    rw [show ∫ ω, (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
        * (((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) ∂P
        = (∫ ω, ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω) ∂P)
        * ∫ ω, ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω) ∂P from hmul,
      hcov (W.W i) (hcoord i) k l, hcov (W.W j) (hcoord j) k l]
    by_cases hkl : k = l
    · simp [hkl, sq]
    · simp [hkl]
  have hint : ∀ k l : ℕ, Integrable
      (fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω))) P := by
    intro k l
    have hrw : (fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)))
        = fun ω => (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω))
        * (((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) := by
      funext ω; ring
    rw [hrw]
    exact (hind k l).integrable_mul (hint2 (W.W i) k l) (hint2 (W.W j) k l)
  have hexp : (fun ω => (∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω)) ^ 2)
      = fun ω => ∑ k ∈ Finset.range m, ∑ l ∈ Finset.range m,
        (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        * (((W.W i).W (affineGrid a h (l + 1)) ω - (W.W i).W (affineGrid a h l) ω)
          * ((W.W j).W (affineGrid a h (l + 1)) ω - (W.W j).W (affineGrid a h l) ω)) := by
    funext ω
    rw [sq, Finset.sum_mul_sum]
  rw [hexp]
  refine ⟨integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l, ?_⟩
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  simp_rw [integral_finsetSum _ fun l _ => hint _ l, hterm, Finset.sum_ite_eq]
  rw [Finset.sum_congr rfl fun x hx => if_pos hx, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul]

/-- A coefficient measurable at the start of an interval is orthogonal to the Brownian increment
over it. -/
lemma integral_mul_increment_eq_zero (V : BrownianMotion P)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (hV : IsBrownianFiltration V ℱ) {s u : ℝ}
    (hs : 0 ≤ s) (hsu : s < u) {Y : Ω → ℝ} (hY : StronglyMeasurable[ℱ s] Y) (hYm : Measurable Y) :
    ∫ ω, Y ω * (V.W u ω - V.W s ω) ∂P = 0 := by
  have h := Ito.integral_mul_increment_pow V ℱ hV hs hsu hY hYm 1
  rw [Ito.integral_increment_pow_odd V hs hsu odd_one, mul_zero] at h
  simpa only [pow_one] using h

/-- Against a bounded coefficient measurable at the start of a uniform grid, the product of the
increments of two coordinates over the whole grid pairs like the sum of the cell-wise cross
products. -/
lemma integral_mul_increment_mul_increment_eq_crossSum (W : MultidimBrownianMotion P d)
    (i j : Fin d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {a h : ℝ} (ha : 0 ≤ a) (hh : 0 < h) (m : ℕ) {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z)
    (hZm : Measurable Z) {C : ℝ} (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W (affineGrid a h m) ω - (W.W i).W a ω)
      * ((W.W j).W (affineGrid a h m) ω - (W.W j).W a ω)) ∂P
      = ∫ ω, Z ω * ∑ k ∈ Finset.range m,
        ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω) ∂P := by
  have hg0 : ∀ k : ℕ, 0 ≤ affineGrid a h k := affineGrid_nonneg ha hh.le
  have hglt : ∀ k : ℕ, affineGrid a h k < affineGrid a h (k + 1) := affineGrid_lt_succ hh
  have hag : ∀ k : ℕ, a ≤ affineGrid a h k := le_affineGrid hh.le
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| := Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact (hZb ω).trans (le_abs_self C)
  have hAm : ∀ (V : BrownianMotion P) (k : ℕ),
      Measurable fun ω => V.W (affineGrid a h k) ω - V.W a ω :=
    fun V k => (V.measurable_eval _).sub (V.measurable_eval _)
  -- a bounded coefficient times a past increment is killed by a fresh increment
  have hzero : ∀ (V V' : BrownianMotion P), IsBrownianFiltration V ℱ →
      IsBrownianFiltration V' ℱ → ∀ k : ℕ,
      ∫ ω, Z ω * ((V.W (affineGrid a h k) ω - V.W a ω)
        * (V'.W (affineGrid a h (k + 1)) ω - V'.W (affineGrid a h k) ω)) ∂P = 0 := by
    intro V V' hV hV' k
    have hY : StronglyMeasurable[ℱ (affineGrid a h k)] fun ω =>
        Z ω * (V.W (affineGrid a h k) ω - V.W a ω) :=
      (hZ.mono (ℱ.mono (hag k))).mul
        ((hV.measurable _).sub ((hV.measurable a).mono (ℱ.mono (hag k)) le_rfl)).stronglyMeasurable
    have h := integral_mul_increment_eq_zero V' hV' (hg0 k) (hglt k) hY (hZm.mul (hAm V k))
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (mul_assoc _ _ _).symm)
  have hintA : ∀ (V V' : BrownianMotion P) (k : ℕ), Integrable (fun ω =>
      Z ω * ((V.W (affineGrid a h k) ω - V.W a ω)
        * (V'.W (affineGrid a h (k + 1)) ω - V'.W (affineGrid a h k) ω))) P := fun V V' k =>
    Integrable.bdd_mul (MemLp.integrable_mul (memLp_two_increment_of_le V ha (hag k))
      (memLp_two_increment_of_le V' (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have hintΔ : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
        * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))) P := fun k =>
    Integrable.bdd_mul (MemLp.integrable_mul (memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
      (memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)) hZm.aestronglyMeasurable hCabs
  have htel : ∀ ω, Z ω * (((W.W i).W (affineGrid a h m) ω - (W.W i).W a ω)
        * ((W.W j).W (affineGrid a h m) ω - (W.W j).W a ω))
      = ∑ k ∈ Finset.range m,
        (Z ω * (((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
            * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
          + Z ω * (((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)
            * ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω))
          + Z ω * (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
            * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))) := by
    intro ω
    have h0 := Finset.sum_range_sub (fun k => ((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
      * ((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)) m
    simp only [affineGrid_zero, sub_self, mul_zero, sub_zero] at h0
    rw [← h0, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint3 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        + Z ω * (((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω))
        + Z ω * (((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))) P :=
    fun k => ((hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)).add (hintΔ k)
  have hint12 : ∀ k : ℕ, Integrable (fun ω =>
      Z ω * (((W.W i).W (affineGrid a h k) ω - (W.W i).W a ω)
          * ((W.W j).W (affineGrid a h (k + 1)) ω - (W.W j).W (affineGrid a h k) ω))
        + Z ω * (((W.W j).W (affineGrid a h k) ω - (W.W j).W a ω)
          * ((W.W i).W (affineGrid a h (k + 1)) ω - (W.W i).W (affineGrid a h k) ω))) P :=
    fun k => (hintA (W.W i) (W.W j) k).add (hintA (W.W j) (W.W i) k)
  rw [integral_congr_ae (Filter.Eventually.of_forall htel), integral_finsetSum _ fun k _ => hint3 k]
  simp_rw [integral_add (hint12 _) (hintΔ _),
    integral_add (hintA (W.W i) (W.W j) _) (hintA (W.W j) (W.W i) _),
    hzero (W.W i) (W.W j) (hcoord i) (hcoord j), hzero (W.W j) (W.W i) (hcoord j) (hcoord i),
    add_zero, zero_add]
  rw [← integral_finsetSum _ fun k _ => hintΔ k]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (Finset.mul_sum _ _ _).symm)

/-- **The cross term over a common interval vanishes.** For distinct coordinates, the product of
the two increments over one interval is orthogonal to every bounded coefficient measurable at its
start. -/
theorem integral_mul_increment_mul_increment_eq_zero (W : MultidimBrownianMotion P d) {i j : Fin d}
    (hij : i ≠ j) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℝ} (hZ : StronglyMeasurable[ℱ a] Z) (hZm : Measurable Z) {C : ℝ}
    (hZb : ∀ ω, |Z ω| ≤ C) :
    ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P = 0 := by
  set I := ∫ ω, Z ω * (((W.W i).W b ω - (W.W i).W a ω) * ((W.W j).W b ω - (W.W j).W a ω)) ∂P
    with hI
  have hC : ∀ ω, |Z ω| ≤ |C| := fun ω => (hZb ω).trans (le_abs_self C)
  have hCabs : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ |C| :=
    Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC ω
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ,
      |I| ≤ |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
    intro ε hε m
    have hnpos : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hh : 0 < (b - a) / (m + 1 : ℕ) := div_pos (by linarith) hnpos
    have hgm : affineGrid a ((b - a) / (m + 1 : ℕ)) (m + 1) = b := by
      simp only [affineGrid]
      field_simp
      ring
    obtain ⟨hQ2int, hQ2⟩ := integral_crossSum_sq W hij hcoord ha hh (m + 1)
    have hI' := integral_mul_increment_mul_increment_eq_crossSum W i j hcoord ha hh (m + 1) hZ
      hZm hZb
    rw [hgm] at hI'
    rw [hI, hI']
    have hg0 : ∀ k : ℕ, 0 ≤ affineGrid a ((b - a) / (m + 1 : ℕ)) k := affineGrid_nonneg ha hh.le
    have hglt : ∀ k : ℕ, affineGrid a ((b - a) / (m + 1 : ℕ)) k
        < affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1) := affineGrid_lt_succ hh
    have hQint : Integrable (fun ω => ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) P :=
      integrable_finsetSum _ fun k _ => MemLp.integrable_mul
        (memLp_two_increment_of_le (W.W i) (hg0 k) (hglt k).le)
        (memLp_two_increment_of_le (W.W j) (hg0 k) (hglt k).le)
    have hZQ := Integrable.bdd_mul hQint hZm.aestronglyMeasurable hCabs
    -- the arithmetic-geometric bound
    have hpt : ∀ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)|
        ≤ |C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2 := by
      intro ω
      generalize (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) = Q
      have hQ : |Q| ≤ ε / 2 + Q ^ 2 / (2 * ε) := by
        rw [div_add_div _ _ two_ne_zero (by positivity), le_div_iff₀ (by positivity)]
        nlinarith [sq_nonneg (ε - |Q|), sq_abs Q]
      calc |Z ω * Q| = |Z ω| * |Q| := abs_mul _ _
        _ ≤ |C| * (ε / 2 + Q ^ 2 / (2 * ε)) :=
          mul_le_mul (hC ω) hQ (abs_nonneg _) (abs_nonneg _)
        _ = |C| * ε / 2 + |C| / (2 * ε) * Q ^ 2 := by ring
    calc |∫ ω, Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω) ∂P|
        ≤ ∫ ω, |Z ω * ∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)| ∂P :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ ω, (|C| * ε / 2 + |C| / (2 * ε) * (∑ k ∈ Finset.range (m + 1),
        ((W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W i).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)
          * ((W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) (k + 1)) ω
            - (W.W j).W (affineGrid a ((b - a) / (m + 1 : ℕ)) k) ω)) ^ 2) ∂P :=
          integral_mono hZQ.abs ((integrable_const _).add (hQ2int.const_mul _)) hpt
      _ = |C| * ε / 2 + |C| / (2 * ε) * ((m + 1 : ℕ) * ((b - a) / (m + 1 : ℕ)) ^ 2) := by
          rw [integral_add (integrable_const _) (hQ2int.const_mul _), integral_const,
            integral_const_mul, hQ2]
          simp
      _ = |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1)) := by
          have hn : ((m : ℝ) + 1) ≠ 0 := by positivity
          push_cast
          rw [div_pow, mul_div_assoc', sq ((m : ℝ) + 1), mul_div_mul_left _ _ hn]
          ring
  have hlim : ∀ ε : ℝ, 0 < ε → |I| ≤ |C| * ε / 2 := by
    intro ε hε
    have ht : Filter.Tendsto (fun m : ℕ =>
        |C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * (1 / ((m : ℝ) + 1))) Filter.atTop
        (nhds (|C| * ε / 2 + |C| * (b - a) ^ 2 / (2 * ε) * 0)) :=
      tendsto_const_nhds.add (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul _)
    rw [mul_zero, add_zero] at ht
    exact ge_of_tendsto' ht (hbound ε hε)
  have hI0 : |I| ≤ 0 := by
    by_contra hpos
    push Not at hpos
    have h1 := hlim (|I| / (|C| + 1)) (by positivity)
    have h2 : |C| * (|I| / (|C| + 1)) ≤ |I| := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith [abs_nonneg C, abs_nonneg I]
    linarith
  exact abs_nonpos_iff.mp hI0

end DirectCross

section SimpleIntegrands

open LevyStochCalc.Brownian.Ito

variable {W : MultidimBrownianMotion P d}

/-- Clamping an interval to `(-∞, t]` either collapses it or leaves its left endpoint alone. -/
lemma min_eq_or_lt_min {p q : ℝ} (h : p < q) (t : ℝ) :
    min p t = min q t ∨ (min p t = p ∧ p < min q t) := by
  rcases lt_or_ge t q with htq | hqt
  · rcases lt_or_ge p t with hpt | htp
    · exact Or.inr ⟨min_eq_left hpt.le, by rw [min_eq_right htq.le]; exact hpt⟩
    · exact Or.inl (by rw [min_eq_right htp, min_eq_right htq.le])
  · exact Or.inr ⟨min_eq_left (h.le.trans hqt), by rw [min_eq_left hqt]; exact h⟩

/-- The square of a Brownian increment over a possibly degenerate interval is integrable. -/
lemma integrable_increment_sq (V : BrownianMotion P) {p q : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q) :
    Integrable (fun ω => (V.W q ω - V.W p ω) ^ 2) P := by
  rcases eq_or_lt_of_le hpq with h | h
  · have hz : (fun ω => (V.W q ω - V.W p ω) ^ 2) = fun _ => (0 : ℝ) := by
      funext ω; rw [← h]; simp
    rw [hz]
    exact integrable_zero Ω ℝ P
  · exact brownian_increment_sq_integrable V hp h

/-- A product of two bounded coefficients and two Brownian increments is integrable. -/
lemma integrable_cross_term (V₁ V₂ : BrownianMotion P) {p q r v : ℝ} (hp : 0 ≤ p) (hpq : p ≤ q)
    (hr : 0 ≤ r) (hrv : r ≤ v) {ξ η : Ω → ℝ} (hξm : Measurable ξ) (hηm : Measurable η)
    {Mξ Mη : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hηb : ∀ ω, |η ω| ≤ Mη) :
    Integrable (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω))
      * (η ω * (V₂.W v ω - V₂.W r ω))) P := by
  have hm1 : Measurable fun ω => V₁.W q ω - V₁.W p ω :=
    (V₁.measurable_eval q).sub (V₁.measurable_eval p)
  have hm2 : Measurable fun ω => V₂.W v ω - V₂.W r ω :=
    (V₂.measurable_eval v).sub (V₂.measurable_eval r)
  have hprod : Integrable (fun ω => (V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) P := by
    have hdom : Integrable (fun ω => 1 / 2 * (V₁.W q ω - V₁.W p ω) ^ 2
        + 1 / 2 * (V₂.W v ω - V₂.W r ω) ^ 2) P :=
      ((integrable_increment_sq V₁ hp hpq).const_mul (1 / 2 : ℝ)).add
        ((integrable_increment_sq V₂ hr hrv).const_mul (1 / 2 : ℝ))
    refine Integrable.mono' hdom (hm1.mul hm2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_abs (V₁.W q ω - V₁.W p ω), sq_abs (V₂.W v ω - V₂.W r ω),
      sq_nonneg (|V₁.W q ω - V₁.W p ω| - |V₂.W v ω - V₂.W r ω|)]
  have heq : (fun ω => (ξ ω * (V₁.W q ω - V₁.W p ω)) * (η ω * (V₂.W v ω - V₂.W r ω)))
      = fun ω => (ξ ω * η ω) * ((V₁.W q ω - V₁.W p ω) * (V₂.W v ω - V₂.W r ω)) := by
    funext ω; ring
  rw [heq]
  refine Integrable.bdd_mul (c := |Mξ| * |Mη|) hprod (hξm.mul hηm).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

/-- **The cross term vanishes, when the `Wʲ` interval starts last.** -/
theorem integral_cross_increment_eq_zero_of_le (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpr : p ≤ r) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  have hΔ : ∀ (V : BrownianMotion P) (x y : ℝ), Measurable fun ω => V.W y ω - V.W x ω :=
    fun V x y => (V.measurable_eval y).sub (V.measurable_eval x)
  have hΔℱ : ∀ (k : Fin d) {x y s : ℝ}, x ≤ s → y ≤ s →
      Measurable[ℱ s] fun ω => (W.W k).W y ω - (W.W k).W x ω := fun k x y s hxs hys =>
    (((hcoord k).measurable y).mono (ℱ.mono hys) le_rfl).sub
      (((hcoord k).measurable x).mono (ℱ.mono hxs) le_rfl)
  have hξη : StronglyMeasurable[ℱ r] fun ω => ξ ω * η ω := (hξ.mono (ℱ.mono hpr)).mul hη
  have hξηb : ∀ ω, |ξ ω * η ω| ≤ |Mξ| * |Mη| := fun ω => by
    rw [abs_mul]
    exact mul_le_mul ((hξb ω).trans (le_abs_self _)) ((hηb ω).trans (le_abs_self _))
      (abs_nonneg _) (abs_nonneg _)
  rcases le_or_gt q r with hqr | hrq
  · -- the `Wⁱ` increment is already known at time `r`
    have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W p ω) * η ω :=
      ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr hqr).stronglyMeasurable).mul hη
    have h := integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
      ((hξm.mul (hΔ (W.W i) p q)).mul hηm)
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
  · -- split the `Wⁱ` increment at `r`
    have hsplit : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
          * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
        = fun ω => (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω))
          + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) := by
      funext ω; ring
    rw [hsplit,
      integral_add (integrable_cross_term (W.W i) (W.W j) hp hpr hr hrv.le hξm hηm hξb hηb)
        (integrable_cross_term (W.W i) (W.W j) hr hrq.le hr hrv.le hξm hηm hξb hηb)]
    have h1 : ∫ ω, (ξ ω * ((W.W i).W r ω - (W.W i).W p ω))
        * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
      have hY : StronglyMeasurable[ℱ r] fun ω => ξ ω * ((W.W i).W r ω - (W.W i).W p ω) * η ω :=
        ((hξ.mono (ℱ.mono hpr)).mul (hΔℱ i hpr le_rfl).stronglyMeasurable).mul hη
      have h := integral_mul_increment_eq_zero (W.W j) (hcoord j) hr hrv hY
        ((hξm.mul (hΔ (W.W i) p r)).mul hηm)
      rw [← h]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => by ring)
    rw [h1, zero_add]
    -- both increments now start at `r`
    rcases lt_trichotomy q v with hqv | rfl | hvq
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))
            + (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
                * ((W.W j).W v ω - (W.W j).W q ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω))) P := by
        have := integrable_cross_term (W.W i) (W.W j) hr hrq.le hr hrq.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          * ((W.W j).W v ω - (W.W j).W q ω)) P := by
        have := integrable_cross_term (W.W i) (W.W j) hr hrq.le (hr.trans hrq.le) hqv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        integral_mul_increment_mul_increment_eq_zero W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb,
        integral_mul_increment_eq_zero (W.W j) (hcoord j) (hr.trans hrq.le) hqv
          (Y := fun ω => ξ ω * ((W.W i).W q ω - (W.W i).W r ω) * η ω)
          (((hξ.mono (ℱ.mono (hpr.trans hrq.le))).mul
            (hΔℱ i hrq.le le_rfl).stronglyMeasurable).mul (hη.mono (ℱ.mono hrq.le)))
          ((hξm.mul (hΔ (W.W i) r q)).mul hηm), add_zero]
    · have heq : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W q ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
              * (((W.W i).W q ω - (W.W i).W r ω) * ((W.W j).W q ω - (W.W j).W r ω)) := by
        funext ω; ring
      rw [heq]
      exact integral_mul_increment_mul_increment_eq_zero W hij hcoord hr hrq hξη (hξm.mul hηm) hξηb
    · have hsplit' : (fun ω => (ξ ω * ((W.W i).W q ω - (W.W i).W r ω))
            * (η ω * ((W.W j).W v ω - (W.W j).W r ω)))
          = fun ω => (ξ ω * η ω)
                * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))
            + (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
                * ((W.W i).W q ω - (W.W i).W v ω) := by
        funext ω; ring
      have hint1 : Integrable (fun ω => (ξ ω * η ω)
          * (((W.W i).W v ω - (W.W i).W r ω) * ((W.W j).W v ω - (W.W j).W r ω))) P := by
        have := integrable_cross_term (W.W i) (W.W j) hr hrv.le hr hrv.le hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      have hint2 : Integrable (fun ω => (ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          * ((W.W i).W q ω - (W.W i).W v ω)) P := by
        have := integrable_cross_term (W.W i) (W.W j) (hr.trans hrv.le) hvq.le hr hrv.le
          hξm hηm hξb hηb
        refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
        ring
      rw [hsplit', integral_add hint1 hint2,
        integral_mul_increment_mul_increment_eq_zero W hij hcoord hr hrv hξη (hξm.mul hηm) hξηb,
        integral_mul_increment_eq_zero (W.W i) (hcoord i) (hr.trans hrv.le) hvq
          (Y := fun ω => ξ ω * η ω * ((W.W j).W v ω - (W.W j).W r ω))
          (((hξ.mono (ℱ.mono (hpr.trans hrv.le))).mul (hη.mono (ℱ.mono hrv.le))).mul
            (hΔℱ j hrv.le le_rfl).stronglyMeasurable)
          ((hξm.mul hηm).mul (hΔ (W.W j) r v)), add_zero]

/-- **The cross term vanishes.** For distinct coordinates the two increments are uncorrelated
against bounded coefficients measurable at the left endpoints, in either order. -/
theorem integral_cross_increment_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hr : 0 ≤ r) (hrv : r < v) (hpq : p < q) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ) (hη : StronglyMeasurable[ℱ r] η)
    (hηm : Measurable η) {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) :
    ∫ ω, (ξ ω * ((W.W i).W q ω - (W.W i).W p ω))
      * (η ω * ((W.W j).W v ω - (W.W j).W r ω)) ∂P = 0 := by
  rcases le_or_gt p r with hpr | hrp
  · exact integral_cross_increment_eq_zero_of_le W hij hcoord hp hr hrv hpr hξ hξm hξb hη hηm hηb
  · have h := integral_cross_increment_eq_zero_of_le W hij.symm hcoord (q := v) hr hp hpq hrp.le
      hη hηm hηb hξ hξm hξb
    rw [← h]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)

/-- A single clamped cross term is integrable and has zero mean. -/
lemma integrable_and_integral_cross_clamped (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {p q r v : ℝ} (hp : 0 ≤ p)
    (hpq : p < q)
    (hr : 0 ≤ r) (hrv : r < v) {ξ η : Ω → ℝ} (hξ : StronglyMeasurable[ℱ p] ξ)
    (hξm : Measurable ξ) {Mξ : ℝ} (hξb : ∀ ω, |ξ ω| ≤ Mξ)
    (hη : StronglyMeasurable[ℱ r] η) (hηm : Measurable η)
    {Mη : ℝ} (hηb : ∀ ω, |η ω| ≤ Mη) (t t' : ℝ) :
    Integrable (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) P
    ∧ ∫ ω, (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
      * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω)) ∂P = 0 := by
  rcases min_eq_or_lt_min hpq t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
        * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
  · rcases min_eq_or_lt_min hrv t' with hc' | ⟨hre, hrlt⟩
    · have hz : (fun ω => (ξ ω * ((W.W i).W (min q t) ω - (W.W i).W (min p t) ω))
          * (η ω * ((W.W j).W (min v t') ω - (W.W j).W (min r t') ω))) = fun _ => (0 : ℝ) := by
        funext ω; rw [hc']; ring
      rw [hz]
      exact ⟨integrable_zero Ω ℝ P, integral_zero Ω ℝ⟩
    · rw [hpe, hre]
      exact ⟨integrable_cross_term (W.W i) (W.W j) hp hplt.le hr hrlt.le hξm hηm hξb hηb,
        integral_cross_increment_eq_zero W hij hcoord hp hr hrlt hplt hξ hξm hξb hη hηm hηb⟩

/-- **Orthogonality on simple integrands.** Elementary integrals against distinct Brownian
coordinates have zero pairing, at any pair of times. -/
theorem integral_simpleIntegral_mul_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ) {TH TK : ℝ}
    (H : SimplePredictable Ω TH)
    (K : SimplePredictable Ω TK)
    (hH : ∀ a : Fin H.N, StronglyMeasurable[ℱ (H.partition a.castSucc)] (H.ξ a))
    (hK : ∀ b : Fin K.N, StronglyMeasurable[ℱ (K.partition b.castSucc)] (K.ξ b))
    (t t' : ℝ) :
    ∫ ω, simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω ∂P = 0 := by
  have hHnn : ∀ a : Fin H.N, 0 ≤ H.partition a.castSucc := fun a => by
    have h := H.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [H.partition_zero] at h
  have hKnn : ∀ b : Fin K.N, 0 ≤ K.partition b.castSucc := fun b => by
    have h := K.partition_strictMono.monotone (Fin.zero_le b.castSucc)
    rwa [K.partition_zero] at h
  have hHlt : ∀ a : Fin H.N, H.partition a.castSucc < H.partition a.succ := fun a =>
    H.partition_strictMono Fin.castSucc_lt_succ
  have hKlt : ∀ b : Fin K.N, K.partition b.castSucc < K.partition b.succ := fun b =>
    K.partition_strictMono Fin.castSucc_lt_succ
  have key : ∀ (a : Fin H.N) (b : Fin K.N),
      Integrable (fun ω => (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω))) P
      ∧ ∫ ω, (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) ∂P = 0 := by
    intro a b
    obtain ⟨Mξ, hMξ⟩ := H.ξ_bounded a
    obtain ⟨Mη, hMη⟩ := K.ξ_bounded b
    exact integrable_and_integral_cross_clamped W hij hcoord (hHnn a) (hHlt a) (hKnn b) (hKlt b)
      (hH a) (H.ξ_measurable a) hMξ (hK b) (K.ξ_measurable b) hMη t t'
  have hexp : (fun ω => simpleIntegral (W.W i) H t ω * simpleIntegral (W.W j) K t' ω)
      = fun ω => ∑ a : Fin H.N, ∑ b : Fin K.N,
        (H.ξ a ω * ((W.W i).W (min (H.partition a.succ) t) ω
          - (W.W i).W (min (H.partition a.castSucc) t) ω))
        * (K.ξ b ω * ((W.W j).W (min (K.partition b.succ) t') ω
          - (W.W j).W (min (K.partition b.castSucc) t') ω)) := by
    funext ω
    rw [simpleIntegral, simpleIntegral]
    exact Finset.sum_mul_sum _ _ _ _
  rw [hexp, integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (key a b).1]
  refine Finset.sum_eq_zero fun a _ => ?_
  rw [integral_finsetSum _ fun b _ => (key a b).1]
  exact Finset.sum_eq_zero fun b _ => (key a b).2

end SimpleIntegrands

section L2Limit

open LevyStochCalc.Brownian.Ito

/-- An elementary integral is square-integrable at every time. -/
lemma memLp_simpleIntegral (V : BrownianMotion P) {T : ℝ} (G : SimplePredictable Ω T) (t : ℝ) :
    MemLp (fun ω => simpleIntegral V G t ω) 2 P := by
  have hnn : ∀ a : Fin G.N, 0 ≤ G.partition a.castSucc := fun a => by
    have h := G.partition_strictMono.monotone (Fin.zero_le a.castSucc)
    rwa [G.partition_zero] at h
  have hlt : ∀ a : Fin G.N, G.partition a.castSucc < G.partition a.succ := fun a =>
    G.partition_strictMono Fin.castSucc_lt_succ
  have hrw : (fun ω => simpleIntegral V G t ω) = fun ω => ∑ a : Fin G.N,
      G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω) := rfl
  rw [hrw]
  refine memLp_finsetSum (f := fun (a : Fin G.N) ω => G.ξ a ω
    * (V.W (min (G.partition a.succ) t) ω - V.W (min (G.partition a.castSucc) t) ω))
    Finset.univ fun a _ => ?_
  rcases min_eq_or_lt_min (hlt a) t with hc | ⟨hpe, hplt⟩
  · have hz : (fun ω => G.ξ a ω * (V.W (min (G.partition a.succ) t) ω
        - V.W (min (G.partition a.castSucc) t) ω)) = fun _ => (0 : ℝ) := by
      funext ω; rw [hc]; ring
    rw [hz]
    exact memLp_const 0
  · obtain ⟨M, hM⟩ := G.ξ_bounded a
    rw [hpe]
    exact memLp_mul_increment V (hnn a) hplt 2 (by simp) (G.ξ_measurable a) hM

omit [IsProbabilityMeasure P] in
/-- The `L²` inner product of two `Lp` representatives is the integral of their product. -/
lemma inner_toLp_eq_integral_mul {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    (inner ℝ (hf.toLp f) (hg.toLp g) : ℝ) = ∫ ω, f ω * g ω ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with ω h1 h2
  rw [RCLike.inner_apply, h1, h2]
  simp [mul_comm]

omit [IsProbabilityMeasure P] in
/-- The `L²` pairing is continuous, so a pairing that vanishes along `L²`-convergent sequences
vanishes in the limit. -/
theorem integral_mul_eq_zero_of_tendsto_eLpNorm {u v : Ω → ℝ} {un vn : ℕ → Ω → ℝ}
    (hu : MemLp u 2 P) (hv : MemLp v 2 P)
    (hun : ∀ n, MemLp (un n) 2 P) (hvn : ∀ n, MemLp (vn n) 2 P)
    (h0 : ∀ n, ∫ ω, un n ω * vn n ω ∂P = 0)
    (hcu : Filter.Tendsto (fun n => eLpNorm (fun ω => un n ω - u ω) 2 P) Filter.atTop (nhds 0))
    (hcv : Filter.Tendsto (fun n => eLpNorm (fun ω => vn n ω - v ω) 2 P) Filter.atTop (nhds 0)) :
    ∫ ω, u ω * v ω ∂P = 0 := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hUn : Filter.Tendsto (fun n => (hun n).toLp (un n)) Filter.atTop (nhds (hu.toLp u)) := by
    rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm _ u hu]
    have heq : ∀ n, eLpNorm (⇑((hun n).toLp (un n)) - u) 2 P
        = eLpNorm (fun ω => un n ω - u ω) 2 P := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hun n).coeFn_toLp] with ω h
      simp [h]
    simp_rw [heq]
    exact hcu
  have hVn : Filter.Tendsto (fun n => (hvn n).toLp (vn n)) Filter.atTop (nhds (hv.toLp v)) := by
    rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm _ v hv]
    have heq : ∀ n, eLpNorm (⇑((hvn n).toLp (vn n)) - v) 2 P
        = eLpNorm (fun ω => vn n ω - v ω) 2 P := by
      intro n
      refine eLpNorm_congr_ae ?_
      filter_upwards [(hvn n).coeFn_toLp] with ω h
      simp [h]
    simp_rw [heq]
    exact hcv
  have hinner : Filter.Tendsto
      (fun n => (inner ℝ ((hun n).toLp (un n)) ((hvn n).toLp (vn n)) : ℝ)) Filter.atTop
      (nhds (inner ℝ (hu.toLp u) (hv.toLp v) : ℝ)) := hUn.inner hVn
  have hzero : ∀ n, (inner ℝ ((hun n).toLp (un n)) ((hvn n).toLp (vn n)) : ℝ) = 0 := fun n => by
    rw [inner_toLp_eq_integral_mul (hun n) (hvn n)]; exact h0 n
  simp_rw [hzero] at hinner
  have hlim := tendsto_nhds_unique tendsto_const_nhds hinner
  rw [inner_toLp_eq_integral_mul hu hv] at hlim
  exact hlim.symm

/-- **Orthogonality of Itô integrals against distinct Brownian coordinates.** -/
theorem integral_stochasticIntegral_mul_eq_zero (W : MultidimBrownianMotion P d)
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {i j : Fin d} (hij : i ≠ j)
    (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)
    {H K : Ω → ℝ → ℝ} (hHm : Measurable (Function.uncurry H))
    (hHp : Probability.ProgressivelyMeasurable ℱ H)
    (hHs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K)
    (hKs : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t ω
      * stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t ω ∂P = 0 := by
  have hui : MemLp (stochasticIntegral (W.W i) ℱ (hcoord i) H hHm hHp hHs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (stochasticIntegralBrownian_ae_eq (W.W i)
      ℱ (hcoord i) H hHm hHp hHs t).symm
  have huj : MemLp (stochasticIntegral (W.W j) ℱ (hcoord j) K hKm hKp hKs t) 2 P :=
    (MeasureTheory.Lp.memLp _).ae_eq (stochasticIntegralBrownian_ae_eq (W.W j)
      ℱ (hcoord j) K hKm hKp hKs t).symm
  refine integral_mul_eq_zero_of_tendsto_eLpNorm
    (un := fun n ω => simpleIntegral (W.W i) (masterApprox ℱ H hHm hHp hHs n) t ω)
    (vn := fun n ω => simpleIntegral (W.W j) (masterApprox ℱ K hKm hKp hKs n) t ω)
    hui huj (fun n => memLp_simpleIntegral _ _ t) (fun n => memLp_simpleIntegral _ _ t)
    (fun n => integral_simpleIntegral_mul_eq_zero W hij hcoord _ _
      (masterApprox_adapt ℱ H hHm hHp hHs n)
      (masterApprox_adapt ℱ K hKm hKp hKs n) t t)
    (masterApprox_tendsto_L2 (W.W i) ℱ (hcoord i) H hHm hHp hHs ht)
    (masterApprox_tendsto_L2 (W.W j) ℱ (hcoord j) K hKm hKp hKs ht)

end L2Limit

end Multidim.MultidimBrownianMotion

end LevyStochCalc.Brownian
