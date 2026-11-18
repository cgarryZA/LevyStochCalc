/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CellRegularity

/-!
# Conditional cell projections for a general filtration

For a filtration `ℱ`, a jointly measurable square-integrable process `f` and an interval
`[a, b]` of length `τ > 0`, the conditional interval average

  `c = τ⁻¹ E[∫_a^b f_s ds | ℱ_t]`

is the orthogonal projection of `f`, in `L²(dP ⊗ ds)` on `Ω × [a, b]`, onto the
`ℱ_t`-measurable processes constant in time: for every `ℱ_t`-measurable `η ∈ L²(P)`

  `E ∫_a^b |f_s − η|² ds = E ∫_a^b |f_s − c|² ds + τ E |c − η|²`.

On the uniform grid `t_i = i τ` of `[0, T]` with `τ = T / N` this gives the conditional cell
average `condCellAvg ℱ P τ Z i` of a vector process `Z` and its cell-projection error
`cellProjError ℱ P T N Z`, the left-hand side of the rate in `CellRegularity`: over the augmented
joint filtration of a Lévy driver both agree with `condCellAverage_Z` and with `rate_Z` by
definition.

## Main statements

* `lintegral_interval_sq_sub_eq` — the projection identity on an interval.
* `lintegral_interval_sq_sub_condAvg_le` — optimality of the conditional interval average.
* `lintegral_interval_sq_eq` — Pythagoras: energy = projection error + `τ E c²`.
* `condCellAvg`, `cellProjError` — the conditional cell average and the projection error.
* `condCellAverage_Z_eq_condCellAvg`, `cellRegularity_iff` — the bridge to `CellRegularity`.
* `cellProjError_le` — optimality of the conditional cell averages on the uniform grid.
* `lintegral_cell_sq_eq` — Pythagoras on a cell, and `ofReal_mul_lintegral_condCellAvg_le`
  the contraction.
* `lintegral_sum_cells` — the cells of the uniform grid tile its horizon.
-/

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

open LevyStochCalc.BSDEJ.Solves (augJoint)
open LevyStochCalc.Driver (LevyDriver)

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Scalar

/-- The squared extended norm of a real number is the extended real of its square. -/
theorem nnnorm_sq_eq_ofReal (y : ℝ) : (‖y‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (y ^ 2) := by
  rw [← sq_abs, ENNReal.ofReal_pow (abs_nonneg y), ← Real.norm_eq_abs, ofReal_norm]
  rfl

/-- For a square-integrable function on a finite measure space the energy of its difference to a
constant is the extended real of the real energy. -/
theorem lintegral_nnnorm_sub_sq_eq_ofReal {μ : Measure ℝ} {g : ℝ → ℝ} (hg : MemLp g 2 μ)
    [IsFiniteMeasure μ] (x : ℝ) :
    ∫⁻ s, (‖g s - x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (∫ s, (g s - x) ^ 2 ∂μ) := by
  have h2 : MemLp (fun s => g s - x) 2 μ := hg.sub (memLp_const x)
  rw [ofReal_integral_eq_lintegral_ofReal h2.integrable_sq
    (Filter.Eventually.of_forall fun s => sq_nonneg _)]
  exact lintegral_congr fun s => nnnorm_sq_eq_ofReal _

/-- The energy of the difference of a square-integrable function on an interval of length `τ`
to a constant `x`. -/
theorem integral_interval_sq_sub_eq {a b : ℝ} (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc a b))) (x : ℝ) :
    ∫ s in Set.Icc a b, (g s - x) ^ 2
      = (∫ s in Set.Icc a b, g s ^ 2) - 2 * x * (∫ s in Set.Icc a b, g s) + (b - a) * x ^ 2 := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hg1 : Integrable g (volume.restrict (Set.Icc a b)) := hg.integrable one_le_two
  have hg2 : Integrable (fun s => g s ^ 2) (volume.restrict (Set.Icc a b)) := hg.integrable_sq
  have hpt : (fun s => (g s - x) ^ 2) = fun s => (g s ^ 2 - 2 * x * g s) + x ^ 2 := by
    funext s; ring
  have hg3 : Integrable (fun s => g s ^ 2 - 2 * x * g s) (volume.restrict (Set.Icc a b)) :=
    hg2.sub (hg1.const_mul _)
  have hg4 : Integrable (fun s => 2 * x * g s) (volume.restrict (Set.Icc a b)) :=
    hg1.const_mul _
  rw [hpt, integral_add hg3 (integrable_const _), integral_sub hg2 hg4, integral_const_mul,
    integral_const]
  simp [Measure.real, Real.volume_Icc, hab, smul_eq_mul]

/-- For a square-integrable function the energy is the extended real of the real energy. -/
theorem lintegral_nnnorm_sq_eq_ofReal {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : α → ℝ} (hg : MemLp g 2 μ) :
    ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ = ENNReal.ofReal (∫ x, g x ^ 2 ∂μ) := by
  rw [ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
    (Filter.Eventually.of_forall fun s => sq_nonneg _)]
  exact lintegral_congr fun s => nnnorm_sq_eq_ofReal _

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (t : ℝ) {f : ℝ → Ω → ℝ} {a b : ℝ}

omit [IsProbabilityMeasure P] in
/-- Almost every path of a process of finite energy on `[a, b]` is square-integrable there. -/
theorem ae_memLp_interval (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, MemLp (fun s => f s ω) 2 (volume.restrict (Set.Icc a b)) := by
  have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  filter_upwards [ae_lt_top hmeas hfs.ne] with ω hω
  have hsl : Measurable fun s => f s ω := hf.comp measurable_prodMk_left
  refine (memLp_two_iff_integrable_sq hsl.aestronglyMeasurable).mpr
    ⟨(hsl.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (le_of_eq (lintegral_congr fun s => ?_)) hω
  rw [← ENNReal.coe_pow, ← nnnorm_pow]
  rfl

/-- The time integral over `[a, b]` of a jointly measurable process is measurable. -/
theorem measurable_integral_interval (hf : Measurable (Function.uncurry fun ω s => f s ω)) :
    Measurable fun ω => ∫ s in Set.Icc a b, f s ω :=
  (hf.stronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Icc a b))).measurable

omit [IsProbabilityMeasure P] in
/-- The pathwise energy over `[a, b]` of a process of finite energy is integrable. -/
theorem integrable_integral_interval_sq (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Integrable (fun ω => ∫ s in Set.Icc a b, f s ω ^ 2) P := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  have hmeas : Measurable fun ω => ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    (hf.nnnorm.coe_nnreal_ennreal.pow_const 2).lintegral_prod_right'
  refine (integrable_toReal_of_lintegral_ne_top hmeas.aemeasurable hfs.ne).congr ?_
  filter_upwards [ae_memLp_interval hf hfs] with ω hω
  rw [lintegral_nnnorm_sq_eq_ofReal hω, ENNReal.toReal_ofReal
    (integral_nonneg fun s => sq_nonneg _)]

omit [MeasurableSpace Ω] in
/-- **Cauchy–Schwarz on an interval.** The square of the integral of a square-integrable function
over `[a, b]` is at most `b − a` times its energy there. -/
theorem sq_integral_interval_le (hab : a < b) {g : ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (Set.Icc a b))) :
    (∫ s in Set.Icc a b, g s) ^ 2 ≤ (b - a) * ∫ s in Set.Icc a b, g s ^ 2 := by
  have hτ : 0 < b - a := sub_pos.mpr hab
  set F := ∫ s in Set.Icc a b, g s
  set A := ∫ s in Set.Icc a b, g s ^ 2
  have h0 : 0 ≤ ∫ s in Set.Icc a b, (g s - F / (b - a)) ^ 2 :=
    integral_nonneg fun s => sq_nonneg _
  rw [integral_interval_sq_sub_eq hab.le hg] at h0
  have e1 : (b - a) * (F / (b - a)) ^ 2 = F ^ 2 / (b - a) := by field_simp
  have e2 : 2 * (F / (b - a)) * F = 2 * (F ^ 2 / (b - a)) := by ring
  have h1 : F ^ 2 / (b - a) ≤ A := by
    have : 0 ≤ A - 2 * (F / (b - a)) * F + (b - a) * (F / (b - a)) ^ 2 := h0
    rw [e1, e2] at this
    linarith
  have := (div_le_iff₀ hτ).mp h1
  linarith

omit [IsProbabilityMeasure P] in
/-- The time integral over `[a, b]` of a process of finite energy is square-integrable. -/
theorem memLp_integral_interval (hab : a < b)
    (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (fun ω => ∫ s in Set.Icc a b, f s ω) 2 P := by
  have hFm := measurable_integral_interval (a := a) (b := b) hf
  refine (memLp_two_iff_integrable_sq hFm.aestronglyMeasurable).mpr
    (Integrable.mono' ((integrable_integral_interval_sq hf hfs).const_mul (b - a))
      (hFm.pow_const 2).aestronglyMeasurable ?_)
  filter_upwards [ae_memLp_interval hf hfs] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_integral_interval_le hab hω

omit [IsProbabilityMeasure P] in
/-- The energy over `[a, b]` of the difference of a process of finite energy to a
square-integrable random constant `η`, expanded: `E A − 2 E[η F] + (b − a) E η²`, with `A` the
pathwise energy and `F` the time integral; the expansion is nonnegative. -/
theorem lintegral_interval_sq_sub_eq_ofReal (hab : a < b)
    (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {η : Ω → ℝ} (hη : MemLp η 2 P) :
    0 ≤ (∫ ω, ∫ s in Set.Icc a b, f s ω ^ 2 ∂volume ∂P)
        - 2 * (∫ ω, η ω * (∫ s in Set.Icc a b, f s ω) ∂P) + (b - a) * ∫ ω, η ω ^ 2 ∂P ∧
    ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω - η ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ENNReal.ofReal ((∫ ω, ∫ s in Set.Icc a b, f s ω ^ 2 ∂volume ∂P)
        - 2 * (∫ ω, η ω * (∫ s in Set.Icc a b, f s ω) ∂P) + (b - a) * ∫ ω, η ω ^ 2 ∂P) := by
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
  set G : Ω → ℝ := fun ω => (∫ s in Set.Icc a b, f s ω ^ 2)
    - 2 * (η ω * ∫ s in Set.Icc a b, f s ω) + (b - a) * η ω ^ 2 with hG
  have hA := integrable_integral_interval_sq hf hfs
  have hF := memLp_integral_interval hab hf hfs
  have hηF : Integrable (fun ω => η ω * ∫ s in Set.Icc a b, f s ω) P := hη.integrable_mul hF
  have hη2 : Integrable (fun ω => η ω ^ 2) P := hη.integrable_sq
  have h1 : Integrable (fun ω => (∫ s in Set.Icc a b, f s ω ^ 2)
      - 2 * (η ω * ∫ s in Set.Icc a b, f s ω)) P := hA.sub (hηF.const_mul 2)
  have h2 : Integrable (fun ω => 2 * (η ω * ∫ s in Set.Icc a b, f s ω)) P := hηF.const_mul 2
  have h3 : Integrable (fun ω => (b - a) * η ω ^ 2) P := hη2.const_mul _
  have hGi : Integrable G P := h1.add h3
  have hGint : ∫ ω, G ω ∂P = (∫ ω, ∫ s in Set.Icc a b, f s ω ^ 2 ∂volume ∂P)
      - 2 * (∫ ω, η ω * (∫ s in Set.Icc a b, f s ω) ∂P) + (b - a) * ∫ ω, η ω ^ 2 ∂P := by
    rw [hG, integral_add h1 h3, integral_sub hA h2, integral_const_mul, integral_const_mul]
  have hpt : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc a b, (‖f s ω - η ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ENNReal.ofReal (G ω) ∧ 0 ≤ G ω := by
    filter_upwards [ae_memLp_interval hf hfs] with ω hω
    have e := integral_interval_sq_sub_eq hab.le hω (η ω)
    refine ⟨?_, ?_⟩
    · rw [lintegral_nnnorm_sub_sq_eq_ofReal hω, e, hG]
      congr 1
      ring
    · have : (0 : ℝ) ≤ ∫ s in Set.Icc a b, (f s ω - η ω) ^ 2 :=
        integral_nonneg fun s => sq_nonneg _
      rw [e] at this
      simp only [hG]
      linarith
  have hGnn : 0 ≤ᵐ[P] G := by filter_upwards [hpt] with ω hω using hω.2
  refine ⟨hGint ▸ integral_nonneg_of_ae hGnn, ?_⟩
  rw [← hGint, ofReal_integral_eq_lintegral_ofReal hGi hGnn]
  exact lintegral_congr_ae (by filter_upwards [hpt] with ω hω using hω.1)

/-- Pairing with the time integral over `[a, b]` against an `ℱ t`-measurable square-integrable
variable is `b − a` times the pairing with the conditional interval average. -/
theorem integral_mul_integral_interval_eq (hab : a < b)
    (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {η : Ω → ℝ} (hηm : StronglyMeasurable[ℱ t] η) (hη : MemLp η 2 P) :
    ∫ ω, η ω * (∫ s in Set.Icc a b, f s ω) ∂P
      = (b - a) * ∫ ω, η ω
        * ((b - a)⁻¹ * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω) ∂P := by
  have hτ : b - a ≠ 0 := (sub_pos.mpr hab).ne'
  have hF := memLp_integral_interval hab hf hfs
  have hηF : Integrable (η * fun ω => ∫ s in Set.Icc a b, f s ω) P := hη.integrable_mul hF
  have hce := condExp_mul_of_stronglyMeasurable_left (m := ℱ t) hηm hηF
    (hF.integrable one_le_two)
  calc ∫ ω, η ω * (∫ s in Set.Icc a b, f s ω) ∂P
      = ∫ ω, P[η * fun ω => ∫ s in Set.Icc a b, f s ω | ℱ t] ω ∂P :=
        (integral_condExp (ℱ.le t)).symm
    _ = ∫ ω, η ω * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω ∂P :=
        integral_congr_ae (by filter_upwards [hce] with ω hω using hω)
    _ = _ := by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        simp only
        field_simp

omit [IsProbabilityMeasure P] in
/-- The conditional interval average of a process of finite energy is square-integrable. -/
theorem memLp_condIntervalAvg (hab : a < b)
    (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    MemLp (fun ω => (b - a)⁻¹ * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω) 2 P :=
  ((memLp_integral_interval hab hf hfs).condExp (m := ℱ t) one_le_two).const_mul _

/-- **The projection identity on an interval.** For a process `f` of finite energy on `[a, b]`,
`a < b`, and an `ℱ t`-measurable square-integrable `η`, the energy of `f − η` on `[a, b]` is the
energy of `f − c` plus `(b − a) E |c − η|²`, where `c = (b − a)⁻¹ E[∫_a^b f | ℱ t]` is the
conditional interval average. -/
theorem lintegral_interval_sq_sub_eq (hab : a < b)
    (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {η : Ω → ℝ} (hηm : StronglyMeasurable[ℱ t] η) (hη : MemLp η 2 P) :
    ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω - η ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω - (b - a)⁻¹
          * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        + ENNReal.ofReal (b - a) * ∫⁻ ω, (‖(b - a)⁻¹
          * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω - η ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set c : Ω → ℝ := fun ω => (b - a)⁻¹ * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω
    with hc
  have hτ : 0 < b - a := sub_pos.mpr hab
  have hcm : StronglyMeasurable[ℱ t] c := stronglyMeasurable_condExp.const_mul _
  have hc2 : MemLp c 2 P := memLp_condIntervalAvg ℱ t hab hf hfs
  obtain ⟨-, hLη⟩ := lintegral_interval_sq_sub_eq_ofReal hab hf hfs hη
  obtain ⟨hnc, hLc⟩ := lintegral_interval_sq_sub_eq_ofReal hab hf hfs hc2
  have hXη : ∫ ω, η ω * (∫ s in Set.Icc a b, f s ω) ∂P = (b - a) * ∫ ω, η ω * c ω ∂P :=
    integral_mul_integral_interval_eq ℱ t hab hf hfs hηm hη
  have hXc : ∫ ω, c ω * (∫ s in Set.Icc a b, f s ω) ∂P = (b - a) * ∫ ω, c ω * c ω ∂P :=
    integral_mul_integral_interval_eq ℱ t hab hf hfs hcm hc2
  have hcη : MemLp (fun ω => c ω - η ω) 2 P := hc2.sub hη
  have hsq : ∫ ω, (c ω - η ω) ^ 2 ∂P
      = ∫ ω, c ω ^ 2 ∂P - 2 * ∫ ω, η ω * c ω ∂P + ∫ ω, η ω ^ 2 ∂P := by
    have i1 : Integrable (fun ω => c ω ^ 2 - 2 * (η ω * c ω)) P :=
      hc2.integrable_sq.sub ((hη.integrable_mul hc2).const_mul 2)
    have i2 : Integrable (fun ω => 2 * (η ω * c ω)) P := (hη.integrable_mul hc2).const_mul 2
    have hpt : (fun ω => (c ω - η ω) ^ 2) = fun ω => (c ω ^ 2 - 2 * (η ω * c ω)) + η ω ^ 2 := by
      funext ω; ring
    rw [hpt, integral_add i1 hη.integrable_sq, integral_sub hc2.integrable_sq i2,
      integral_const_mul]
  have hcc : ∫ ω, c ω * c ω ∂P = ∫ ω, c ω ^ 2 ∂P :=
    integral_congr_ae (Filter.Eventually.of_forall fun ω => (sq (c ω)).symm)
  rw [hcc] at hXc
  rw [hXc] at hnc hLc
  rw [hLη, hLc, hXη, lintegral_nnnorm_sq_eq_ofReal hcη, hsq,
    ← ENNReal.ofReal_mul hτ.le, ← ENNReal.ofReal_add hnc
      (mul_nonneg hτ.le (hsq ▸ integral_nonneg fun ω => sq_nonneg _))]
  congr 1
  ring

/-- **Optimality of the conditional interval average.** No `ℱ t`-measurable square-integrable
random constant approximates a process of finite energy on `[a, b]` better than its conditional
interval average. -/
theorem lintegral_interval_sq_sub_condAvg_le (hab : a < b)
    (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {η : Ω → ℝ} (hηm : StronglyMeasurable[ℱ t] η) (hη : MemLp η 2 P) :
    ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω - (b - a)⁻¹
          * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω - η ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [lintegral_interval_sq_sub_eq ℱ t hab hf hfs hηm hη]
  exact le_self_add

/-- **Pythagoras on an interval.** The energy of a process on `[a, b]` is the energy of its
difference to the conditional interval average `c` plus `(b − a) E c²`. -/
theorem lintegral_interval_sq_eq (hab : a < b)
    (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖f s ω - (b - a)⁻¹
          * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        + ENNReal.ofReal (b - a) * ∫⁻ ω, (‖(b - a)⁻¹
          * P[fun ω' => ∫ s in Set.Icc a b, f s ω' | ℱ t] ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  have h := lintegral_interval_sq_sub_eq ℱ t hab hf hfs (η := fun _ => 0)
    stronglyMeasurable_const (memLp_const 0)
  simpa only [sub_zero] using h

end Scalar

section Tiling

omit [MeasurableSpace Ω] in
/-- The cells `[i τ, (i + 1) τ]`, `i < N`, of the uniform grid of step `τ ≥ 0` tile `[0, N τ]`
for the Lebesgue integral. -/
theorem lintegral_sum_cells (g : ℝ → ℝ≥0∞) {τ : ℝ} (hτ : 0 ≤ τ) (N : ℕ) :
    ∑ i ∈ Finset.range N, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), g s
      = ∫⁻ s in Set.Icc 0 ((N : ℝ) * τ), g s := by
  induction N with
  | zero => simp [Set.Icc_self]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h0 : (0 : ℝ) ≤ (N : ℝ) * τ := mul_nonneg (Nat.cast_nonneg N) hτ
    have h1 : (N : ℝ) * τ ≤ ((N : ℝ) + 1) * τ := by nlinarith
    have e : (((N + 1 : ℕ) : ℝ)) * τ = ((N : ℝ) + 1) * τ := by push_cast; ring
    rw [e, setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ)) (b := (N : ℝ) * τ)).symm,
      setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume) (a := (N : ℝ) * τ)
        (b := ((N : ℝ) + 1) * τ)).symm,
      setLIntegral_congr (Ioc_ae_eq_Icc (μ := volume) (a := (0 : ℝ))
        (b := ((N : ℝ) + 1) * τ)).symm,
      ← Set.Ioc_union_Ioc_eq_Ioc h0 h1, lintegral_union measurableSet_Ioc]
    exact Set.disjoint_left.mpr fun x hx hy => absurd hx.2 (not_le.mpr hy.1)

omit [IsProbabilityMeasure P] in
/-- The cells of the uniform grid tile its horizon, for a jointly measurable family of
nonnegative integrands integrated against `P`. -/
theorem lintegral_sum_cells_lintegral {g : Ω → ℝ → ℝ≥0∞} (hg : Measurable (Function.uncurry g))
    {τ : ℝ} (hτ : 0 ≤ τ) (N : ℕ) :
    ∑ i ∈ Finset.range N,
        ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), g ω s ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc 0 ((N : ℝ) * τ), g ω s ∂volume ∂P := by
  have hm : ∀ i ∈ Finset.range N, Measurable fun ω =>
      ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), g ω s ∂volume :=
    fun i _ => hg.lintegral_prod_right'
  rw [← lintegral_finsetSum _ hm]
  exact lintegral_congr fun ω => lintegral_sum_cells (g ω) hτ N

omit [MeasurableSpace Ω] in
/-- A cell of the uniform grid of `N` cells on `[0, T]` lies in `[0, T]`. -/
theorem cell_subset_Icc {T : ℝ} (hT : 0 ≤ T) {N : ℕ} {i : ℕ} (hi : i < N) :
    Set.Icc ((i : ℝ) * (T / N)) (((i : ℝ) + 1) * (T / N)) ⊆ Set.Icc 0 T := by
  have hN : (0 : ℝ) < N := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  have hτ : 0 ≤ T / N := div_nonneg hT hN.le
  have hi' : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
  intro s hs
  refine ⟨le_trans (mul_nonneg (Nat.cast_nonneg i) hτ) hs.1, hs.2.trans ?_⟩
  calc ((i : ℝ) + 1) * (T / N) ≤ (N : ℝ) * (T / N) := mul_le_mul_of_nonneg_right hi' hτ
    _ = T := by field_simp

omit [IsProbabilityMeasure P] in
/-- The energy over a set of a finite sum of jointly measurable families is the sum of the
energies. -/
theorem lintegral_setLIntegral_finsetSum {d : ℕ} {I : Set ℝ} {g : Fin d → Ω → ℝ → ℝ≥0∞}
    (hg : ∀ k, Measurable (Function.uncurry (g k))) :
    ∫⁻ ω, ∫⁻ s in I, ∑ k, g k ω s ∂volume ∂P = ∑ k, ∫⁻ ω, ∫⁻ s in I, g k ω s ∂volume ∂P := by
  have hm : ∀ k ∈ Finset.univ, Measurable fun ω => ∫⁻ s in I, g k ω s ∂volume :=
    fun k _ => (hg k).lintegral_prod_right'
  rw [← lintegral_finsetSum _ hm]
  exact lintegral_congr fun ω =>
    lintegral_finsetSum _ fun k _ => (hg k).comp measurable_prodMk_left

end Tiling

section Grid

variable {d : ℕ}

/-- The conditional cell average of `Z` over the cell `[i τ, (i + 1) τ]` of the uniform grid of
step `τ`, for a filtration `ℱ`: the conditional expectation at the left endpoint of the integral
of `Z` over the cell, divided by `τ`, coordinate by coordinate. -/
noncomputable def condCellAvg (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) (τ : ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ)) (i : ℕ) : Ω → (Fin d → ℝ) := fun ω k =>
  τ⁻¹ * P[fun ω' => ∫ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ), Z s ω' k |
    ℱ ((i : ℝ) * τ)] ω

/-- The cell-projection error of `Z` on the uniform grid of `N` cells on `[0, T]`, for a
filtration `ℱ`: the energy of the difference of `Z` to its conditional cell averages, summed over
the cells. -/
noncomputable def cellProjError (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω) (T : ℝ)
    (N : ℕ) (Z : ℝ → Ω → (Fin d → ℝ)) : ℝ≥0∞ :=
  ∑ i ∈ Finset.range N, ∫⁻ ω,
    ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
      ∑ k : Fin d, (‖Z s ω k - condCellAvg ℱ P (T / (N : ℝ)) Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P

/-- Over the augmented joint filtration of a Lévy driver the conditional cell average is
`condCellAverage_Z`. -/
theorem condCellAverage_Z_eq_condCellAvg {E : Type v} [MeasurableSpace E] {ν : Measure E}
    [SigmaFinite ν] (D : LevyDriver P d ν) (τ : ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (i : ℕ) :
    condCellAverage_Z D τ Z i = condCellAvg (augJoint D) P τ Z i := rfl

/-- `CellRegularity` is the bound `C · T / N` on the cell-projection error over the augmented
joint filtration, together with the same bound for the marked integrals. -/
theorem cellRegularity_iff {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
    {m : ℕ} (D : LevyDriver P d ν) (T : ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
    (A : Fin m → Set E) (C : ℝ) :
    CellRegularity D T Z U A C ↔ 0 ≤ C
      ∧ (∀ N : ℕ, 0 < N → cellProjError (augJoint D) P T N Z ≤ ENNReal.ofReal (C * (T / N)))
      ∧ ∀ N : ℕ, 0 < N →
        ∑ i ∈ Finset.range N, ∫⁻ ω,
          ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
            ∑ k : Fin m,
              (‖(∫ e in A k, U s ω e ∂ν)
                - condCellAverage_U D (T / (N : ℝ)) U A i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ENNReal.ofReal (C * (T / (N : ℝ))) :=
  ⟨fun h => ⟨h.nonneg, h.rate_Z, h.rate_U⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {τ : ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}

omit [IsProbabilityMeasure P] in
/-- The coordinates of the conditional cell average are measurable at the left endpoint. -/
theorem stronglyMeasurable_condCellAvg (i : ℕ) (k : Fin d) :
    StronglyMeasurable[ℱ ((i : ℝ) * τ)] fun ω => condCellAvg ℱ P τ Z i ω k :=
  stronglyMeasurable_condExp.const_mul _

omit [IsProbabilityMeasure P] in
private theorem cell_length (i : ℕ) : ((i : ℝ) + 1) * τ - (i : ℝ) * τ = τ := by ring

omit [IsProbabilityMeasure P] in
/-- The coordinates of the conditional cell average of a process of finite energy on the cell
are square-integrable. -/
theorem memLp_condCellAvg (hτ : 0 < τ) {i : ℕ}
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (k : Fin d) :
    MemLp (fun ω => condCellAvg ℱ P τ Z i ω k) 2 P := by
  have h := memLp_condIntervalAvg ℱ ((i : ℝ) * τ) (by nlinarith) (hZm k) (hZs k)
  rw [cell_length] at h
  exact h

private theorem measurable_uncurry_sq_sub {f : ℝ → Ω → ℝ} {g : Ω → ℝ}
    (hf : Measurable (Function.uncurry fun ω s => f s ω)) (hg : Measurable g) :
    Measurable (Function.uncurry fun ω s => (‖f s ω - g ω‖₊ : ℝ≥0∞) ^ 2) :=
  ((hf.sub (hg.comp measurable_fst)).nnnorm.coe_nnreal_ennreal.pow_const 2)

/-- **Optimality on a cell.** On a cell of the uniform grid the conditional cell average
approximates a process of finite energy at least as well as any random constant whose
coordinates are square-integrable and measurable at the left endpoint. -/
theorem lintegral_cell_sq_sub_condCellAvg_le (hτ : 0 < τ) {i : ℕ}
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {η : Ω → (Fin d → ℝ)} (hηm : ∀ k, StronglyMeasurable[ℱ ((i : ℝ) * τ)] fun ω => η ω k)
    (hη : ∀ k, MemLp (fun ω => η ω k) 2 P) :
    ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k, (‖Z s ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k, (‖Z s ω k - η ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [lintegral_setLIntegral_finsetSum fun k => measurable_uncurry_sq_sub (hZm k)
      ((stronglyMeasurable_condCellAvg ℱ i k).mono (ℱ.le _)).measurable,
    lintegral_setLIntegral_finsetSum fun k => measurable_uncurry_sq_sub (hZm k)
      ((hηm k).mono (ℱ.le _)).measurable]
  refine Finset.sum_le_sum fun k _ => ?_
  have h := lintegral_interval_sq_sub_condAvg_le ℱ ((i : ℝ) * τ) (by nlinarith) (hZm k) (hZs k)
    (hηm k) (hη k)
  rw [cell_length] at h
  exact h

/-- **Pythagoras on a cell.** The energy of a process on a cell of the uniform grid is the
energy of its difference to the conditional cell average plus `τ` times the second moment of
the conditional cell average. -/
theorem lintegral_cell_sq_eq (hτ : 0 < τ) {i : ℕ}
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
          ∑ k, (‖Z s ω k - condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        + ENNReal.ofReal τ * ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  have hcm : ∀ k, Measurable fun ω => condCellAvg ℱ P τ Z i ω k := fun k =>
    ((stronglyMeasurable_condCellAvg ℱ i k).mono (ℱ.le _)).measurable
  rw [lintegral_setLIntegral_finsetSum fun k =>
      (hZm k).nnnorm.coe_nnreal_ennreal.pow_const 2,
    lintegral_setLIntegral_finsetSum fun k => measurable_uncurry_sq_sub (hZm k) (hcm k),
    lintegral_finsetSum _ fun k _ => (hcm k).nnnorm.coe_nnreal_ennreal.pow_const 2,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h := lintegral_interval_sq_eq ℱ ((i : ℝ) * τ) (by nlinarith) (hZm k) (hZs k)
  rw [cell_length] at h
  exact h

/-- **Contraction on a cell.** `τ` times the second moment of the conditional cell average is
at most the energy of the process on the cell. -/
theorem ofReal_mul_lintegral_condCellAvg_le (hτ : 0 < τ) {i : ℕ}
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ENNReal.ofReal τ * ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
        ∑ k, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rw [lintegral_cell_sq_eq ℱ hτ hZm hZs]
  exact le_add_self

/-- **Optimality on the uniform grid.** The cell-projection error of a process of finite energy
on `[0, T]` is at most the energy of its difference to any family of random constants, one per
cell, whose coordinates are square-integrable and measurable at the left endpoint of the cell. -/
theorem cellProjError_le {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {η : ℕ → Ω → (Fin d → ℝ)}
    (hηm : ∀ i < N, ∀ k, StronglyMeasurable[ℱ ((i : ℝ) * (T / N))] fun ω => η i ω k)
    (hη : ∀ i < N, ∀ k, MemLp (fun ω => η i ω k) 2 P) :
    cellProjError ℱ P T N Z
      ≤ ∑ i ∈ Finset.range N, ∫⁻ ω,
          ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
            ∑ k, (‖Z s ω k - η i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hτ : 0 < T / (N : ℝ) := div_pos hT (by exact_mod_cast hN)
  refine Finset.sum_le_sum fun i hi => ?_
  have hi' : i < N := Finset.mem_range.mp hi
  refine lintegral_cell_sq_sub_condCellAvg_le ℱ hτ hZm (fun k => ?_) (hηm i hi') (hη i hi')
  exact lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set
    (cell_subset_Icc hT.le hi')) (hZs k)

end Grid

end LevyStochCalc.BSDEJ.PathRegularity
