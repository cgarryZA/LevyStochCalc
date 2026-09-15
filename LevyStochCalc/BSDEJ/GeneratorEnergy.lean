/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.Existence
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.Poisson.CompensatedIntegrandComplete

/-!
# Energy of a BSDEJ generator along a triple of processes

A generator `f` that is Lipschitz in `(y, z, u)` for the `L²(ν)` distance of the jump variable has
linear growth: `‖f s y z u‖` is at most `‖f s 0 0 0‖ + L * (‖y‖ + ‖z‖ + ‖u‖_{L²(ν)})`, and the
square of that bound splits into four terms. Evaluated along processes `(Y, Z, U)` the splitting
dominates the energy of `s ↦ f s (Y s) (Z s) (U s)` on the horizon `[0, T]` by the energy of `Y`,
the energies of the coordinates of `Z` and the marked energy of `U`; in particular the generator
has finite energy along a triple of processes of finite energy.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Generator

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-! ### Elementary inequalities in `ℝ≥0∞` -/

/-- The square of the square root of an extended nonnegative real. -/
theorem sq_rpow_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
  rw [← ENNReal.rpow_natCast (x ^ (1 / 2 : ℝ)) 2, ← ENNReal.rpow_mul]
  norm_num

/-- The square of a sum of two extended nonnegative reals against twice the sum of the squares. -/
theorem sq_add_le (a b : ℝ≥0∞) : (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  have hsq : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => by
    rw [← ENNReal.rpow_natCast x 2]
    norm_num
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  simp only [hsq] at h
  rwa [show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] at h

/-- The square of a sum of four extended nonnegative reals against four times the sum of the
squares. -/
theorem sq_add_add_add_le (a₁ a₂ a₃ a₄ : ℝ≥0∞) :
    (a₁ + a₂ + a₃ + a₄) ^ 2 ≤ 4 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2) := by
  have hsplit : a₁ + a₂ + a₃ + a₄ = (a₁ + a₂) + (a₃ + a₄) := by ring
  rw [hsplit]
  calc ((a₁ + a₂) + (a₃ + a₄)) ^ 2 ≤ 2 * ((a₁ + a₂) ^ 2 + (a₃ + a₄) ^ 2) := sq_add_le _ _
    _ ≤ 2 * (2 * (a₁ ^ 2 + a₂ ^ 2) + 2 * (a₃ ^ 2 + a₄ ^ 2)) := by
        gcongr <;> exact sq_add_le _ _
    _ = 4 * (a₁ ^ 2 + a₂ ^ 2 + a₃ ^ 2 + a₄ ^ 2) := by ring

/-! ### Linear growth of a Lipschitz generator -/

/-- The sup norm on `Fin d → ℝ` against the sum of the norms of the coordinates, in squares. -/
theorem sq_enorm_pi_le_sum (z : Fin d → ℝ) :
    (‖z‖₊ : ℝ≥0∞) ^ 2 ≤ ∑ i : Fin d, (‖z i‖₊ : ℝ≥0∞) ^ 2 := by
  rcases (Finset.univ : Finset (Fin d)).eq_empty_or_nonempty with h | h
  · have hz : ‖z‖₊ = 0 := by
      rw [Pi.nnnorm_def, h]
      simp
    simp [hz]
  · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ h fun j => ‖z j‖₊
    have hz : ‖z‖₊ = ‖z i‖₊ := by
      rw [Pi.nnnorm_def]
      exact hi
    rw [hz]
    exact Finset.single_le_sum (f := fun j : Fin d => ((‖z j‖₊ : ℝ≥0∞) ^ 2))
      (fun j _ => zero_le) (Finset.mem_univ i)

omit [MeasurableSpace E] in
/-- Measurability in time of the generator at the origin of the state variables. -/
theorem measurable_generator_zero
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u) :
    Measurable fun s : ℝ => f s 0 0 0 := by
  have hg : Measurable fun s : ℝ => (s, ((0 : ℝ), (0 : Fin d → ℝ))) :=
    measurable_id.prodMk measurable_const
  exact (hf 0).comp hg

/-- Linear growth of a generator that is Lipschitz in the state variables. -/
theorem enorm_generator_le
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u : E → ℝ) :
    (‖f s y z u‖₊ : ℝ≥0∞) ≤ (‖f s 0 0 0‖₊ : ℝ≥0∞) + ENNReal.ofReal L *
      ((‖y‖₊ : ℝ≥0∞) + (‖z‖₊ : ℝ≥0∞) + (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) := by
  have hkey := hlip s y 0 z 0 u 0
  simp only [Pi.zero_apply, sub_zero] at hkey
  have hrw : f s y z u = (f s y z u - f s 0 0 0) + f s 0 0 0 := by ring
  calc (‖f s y z u‖₊ : ℝ≥0∞)
      = (‖(f s y z u - f s 0 0 0) + f s 0 0 0‖₊ : ℝ≥0∞) := by rw [← hrw]
    _ ≤ (‖f s y z u - f s 0 0 0‖₊ : ℝ≥0∞) + (‖f s 0 0 0‖₊ : ℝ≥0∞) := by
        rw [← ENNReal.coe_add, ENNReal.coe_le_coe]
        exact nnnorm_add_le _ _
    _ ≤ ENNReal.ofReal L * ((‖y‖₊ : ℝ≥0∞) + (‖z‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) + (‖f s 0 0 0‖₊ : ℝ≥0∞) := by
        gcongr
    _ = (‖f s 0 0 0‖₊ : ℝ≥0∞) + ENNReal.ofReal L * ((‖y‖₊ : ℝ≥0∞) + (‖z‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) := by ring

/-- The square of the linear growth bound of a Lipschitz generator, split into four terms. -/
theorem sq_enorm_generator_le
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u : E → ℝ) :
    (‖f s y z u‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * (‖y‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * (‖z‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
  have h1 := enorm_generator_le hlip s y z u
  have h2 : (‖f s y z u‖₊ : ℝ≥0∞) ≤ (‖f s 0 0 0‖₊ : ℝ≥0∞)
      + ENNReal.ofReal L * (‖y‖₊ : ℝ≥0∞) + ENNReal.ofReal L * (‖z‖₊ : ℝ≥0∞)
      + ENNReal.ofReal L * (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
    refine h1.trans_eq ?_
    ring
  calc (‖f s y z u‖₊ : ℝ≥0∞) ^ 2
      ≤ ((‖f s 0 0 0‖₊ : ℝ≥0∞) + ENNReal.ofReal L * (‖y‖₊ : ℝ≥0∞)
          + ENNReal.ofReal L * (‖z‖₊ : ℝ≥0∞)
          + ENNReal.ofReal L * (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ ≤ 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 + (ENNReal.ofReal L * (‖y‖₊ : ℝ≥0∞)) ^ 2
          + (ENNReal.ofReal L * (‖z‖₊ : ℝ≥0∞)) ^ 2
          + (ENNReal.ofReal L * (∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2) :=
        sq_add_add_add_le _ _ _ _
    _ = 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 + ENNReal.ofReal L ^ 2 * (‖y‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal L ^ 2 * (‖z‖₊ : ℝ≥0∞) ^ 2
          + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖u e‖₊ : ℝ≥0∞) ^ 2 ∂ν) := by
        rw [mul_pow, mul_pow, mul_pow, sq_rpow_half]

/-! ### Energy along a triple of processes -/

/-- The integral of `4 * (g₁ + k * g₂ + k * g₃ + k * g₄)` in terms of the integrals of the
summands. -/
theorem lintegral_four_terms {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g₁ g₂ g₃ g₄ : α → ℝ≥0∞} (h₁ : Measurable g₁) (h₂ : Measurable g₂) (h₃ : Measurable g₃)
    {k : ℝ≥0∞} (hk : k ≠ ⊤) :
    ∫⁻ x, 4 * (g₁ x + k * g₂ x + k * g₃ x + k * g₄ x) ∂μ
      = 4 * (∫⁻ x, g₁ x ∂μ + k * ∫⁻ x, g₂ x ∂μ + k * ∫⁻ x, g₃ x ∂μ + k * ∫⁻ x, g₄ x ∂μ) := by
  have m₂ : Measurable fun x => k * g₂ x := h₂.const_mul k
  have m₃ : Measurable fun x => k * g₃ x := h₃.const_mul k
  have m₁₂ : Measurable fun x => g₁ x + k * g₂ x := h₁.add m₂
  have m₁₂₃ : Measurable fun x => g₁ x + k * g₂ x + k * g₃ x := m₁₂.add m₃
  rw [lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤),
    lintegral_add_left m₁₂₃, lintegral_add_left m₁₂,
    lintegral_add_left h₁, lintegral_const_mul' _ _ hk, lintegral_const_mul' _ _ hk,
    lintegral_const_mul' _ _ hk]

/-- The energy on `[0, T]` of a Lipschitz generator evaluated along `(Y, Z, U)`, bounded by the
energy of `Y`, the energies of the coordinates of `Z` and the marked energy of `U`. -/
theorem energy_generator_along_le [IsProbabilityMeasure P] [SigmaFinite ν]
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hYm : Measurable (Function.uncurry Y))
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Brownian.Ito.energy P T (fun ω s => f s (Y s ω) (Z s ω) (U s ω))
      ≤ 4 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2)
          + ENNReal.ofReal L ^ 2 * Brownian.Ito.energy P T (fun ω s => Y s ω)
          + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i)
          + ENNReal.ofReal L ^ 2 *
              Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
  classical
  have ha : Measurable fun p : Ω × ℝ => (‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2 := by
    have h : Measurable fun p : Ω × ℝ => f p.2 0 0 0 :=
      (measurable_generator_zero hf).comp measurable_snd
    exact (h.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hb : Measurable fun p : Ω × ℝ => (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2 := by
    have h : Measurable fun p : Ω × ℝ => Y p.2 p.1 :=
      hYm.comp (measurable_snd.prodMk measurable_fst)
    exact (h.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hc : ∀ i : Fin d, Measurable fun p : Ω × ℝ => (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2 := by
    intro i
    have h : Measurable fun p : Ω × ℝ => Z p.2 p.1 i := hZm i
    exact (h.nnnorm.coe_nnreal_ennreal).pow_const 2
  have hcsum : Measurable fun p : Ω × ℝ => ∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2 :=
    Finset.measurable_sum _ fun i _ => hc i
  have hw : Measurable fun p : Ω × ℝ => ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    have h : Measurable fun q : (Ω × ℝ) × E => U q.1.2 q.1.1 q.2 :=
      hUm.comp ((measurable_fst.comp measurable_fst).prodMk
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
    exact ((h.nnnorm.coe_nnreal_ennreal).pow_const 2).lintegral_prod_right'
  have hM : Measurable fun p : Ω × ℝ => 4 * ((‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2
      + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
    (((ha.add (hb.const_mul _)).add (hcsum.const_mul _)).add (hw.const_mul _)).const_mul _
  have hprod : ∀ g : Ω × ℝ → ℝ≥0∞, Measurable g →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, g (ω, s) ∂volume ∂P
        = ∫⁻ p, g p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := fun g hg =>
    lintegral_lintegral (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      (f := fun ω s => g (ω, s)) hg.aemeasurable
  have e1 : ∫⁻ p, (‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 := by
    rw [← hprod _ ha]
    simp only [lintegral_const, measure_univ, mul_one]
  have e2 : ∫⁻ p, (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2 ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = Brownian.Ito.energy P T fun ω s => Y s ω := (hprod _ hb).symm
  have e3 : ∫⁻ p, (∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = ∑ i : Fin d, Brownian.Ito.energy P T fun ω s => Z s ω i := by
    rw [lintegral_finsetSum _ fun i _ => hc i]
    exact Finset.sum_congr rfl fun i _ => (hprod _ (hc i)).symm
  have e4 : ∫⁻ p, (∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      = Poisson.Compensated.markedEnergy P ν T fun ω s e => U s ω e := (hprod _ hw).symm
  calc Brownian.Ito.energy P T (fun ω s => f s (Y s ω) (Z s ω) (U s ω))
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * ((‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * (‖Y s ω‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P := by
        simp only [Brownian.Ito.energy]
        refine lintegral_mono fun ω => lintegral_mono fun s => ?_
        refine (sq_enorm_generator_le hlip s (Y s ω) (Z s ω) (U s ω)).trans ?_
        gcongr
        exact sq_enorm_pi_le_sum (Z s ω)
    _ = ∫⁻ p, 4 * ((‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2
            + ENNReal.ofReal L ^ 2 * ∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
          ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := hprod _ hM
    _ = 4 * ((∫⁻ p, (‖f p.2 0 0 0‖₊ : ℝ≥0∞) ^ 2
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))))
          + ENNReal.ofReal L ^ 2 * ∫⁻ p, (‖Y p.2 p.1‖₊ : ℝ≥0∞) ^ 2
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
          + ENNReal.ofReal L ^ 2 * ∫⁻ p, (∑ i : Fin d, (‖Z p.2 p.1 i‖₊ : ℝ≥0∞) ^ 2)
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
          + ENNReal.ofReal L ^ 2 * ∫⁻ p, (∫⁻ e, (‖U p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
              ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))) :=
        lintegral_four_terms ha hb hcsum (by finiteness)
    _ = 4 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2)
          + ENNReal.ofReal L ^ 2 * Brownian.Ito.energy P T (fun ω s => Y s ω)
          + ENNReal.ofReal L ^ 2 * ∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i)
          + ENNReal.ofReal L ^ 2 *
              Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
        rw [e1, e2, e3, e4]

/-- A Lipschitz generator evaluated along processes of finite energy has finite energy. -/
theorem lintegral_sq_generator_along_lt_top [IsProbabilityMeasure P] [SigmaFinite ν]
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hYm : Measurable (Function.uncurry Y))
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZ : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hU : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s => f s (Y s ω) (Z s ω) (U s ω)) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (energy_generator_along_le hlip hf hYm hZm hUm)
  have hK : ENNReal.ofReal L ^ 2 ≠ ⊤ := by finiteness
  have hsum : ∑ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤ :=
    (ENNReal.sum_lt_top.2 fun i _ => (hZ i).lt_top).ne
  refine ENNReal.mul_ne_top (by norm_num) ?_
  refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hf0.ne, ?_⟩, ?_⟩, ?_⟩
  · exact ENNReal.mul_ne_top hK hY
  · exact ENNReal.mul_ne_top hK hsum
  · exact ENNReal.mul_ne_top hK hU

/-- A Lipschitz generator evaluated along processes of finite energy and truncated to the horizon
has finite energy. -/
theorem lintegral_sq_generator_along_indicator_lt_top [IsProbabilityMeasure P] [SigmaFinite ν]
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hYm : Measurable (Function.uncurry Y))
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZm : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZ : ∀ i : Fin d, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hU : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s =>
        Set.indicator (Set.Icc (0 : ℝ) T) (fun s => f s (Y s ω) (Z s ω) (U s ω)) s) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    (lintegral_sq_generator_along_lt_top hlip hf hf0 hYm hY hZm hZ hUm hU) ?_
  simp only [Brownian.Ito.energy]
  refine lintegral_mono fun ω => lintegral_mono fun s => ?_
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [Set.indicator_of_mem hs]
  · rw [Set.indicator_of_notMem hs]
    simp

end LevyStochCalc.BSDEJ.Generator
