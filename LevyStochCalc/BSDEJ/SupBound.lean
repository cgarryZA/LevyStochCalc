/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Probability.DoobContinuous
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The `S²` norm of a sum of a constant, two martingales and a drift

The solution space `S²` of a backward equation asks for
`∫⁻ ω, ⨆ t ∈ [0, T], ‖Y t ω‖ₑ² ∂μ < ⊤`, a supremum over the window taken *inside* the square,
while Doob's `L²` maximal inequality
(`LevyStochCalc.Probability.lintegral_iSup_sq_le_of_martingale`) is stated with the square
outside a supremum over the subtype `↥(Set.Icc 0 T)`. The two shapes agree, because squaring
commutes with suprema in `ℝ≥0∞`, and the resulting bound is stable under the decomposition
`Y = c + M₁ + M₂ + A` of a Picard iterate into a constant, two stochastic integrals and a
time integral of the generator.

## Main statements

* `biSup_sq_eq_iSup_subtype_sq` — the two shapes of the squared supremum over `[0, T]` agree.
* `lintegral_biSup_sq_le_of_martingale` — Doob's `L²` maximal inequality in the `S²` shape.
* `lintegral_biSup_sq_add_le` — the `S²` seminorm is subadditive up to a factor `2`.
* `lintegral_biSup_sq_const_add_add_add_lt_top` — a sum of a constant and three processes of
  finite `S²` seminorm has finite `S²` seminorm.
* `lintegral_biSup_sq_setIntegral_le` — the `S²` seminorm of a time integral, by Cauchy–Schwarz.
* `lintegral_biSup_sq_const_mul` — the `S²` seminorm of a scalar multiple of a process.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.SupBound

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Squares and suprema in `ℝ≥0∞` -/

/-- Squaring commutes with suprema in `ℝ≥0∞`. -/
theorem iSup_sq {ι : Sort*} (f : ι → ℝ≥0∞) : (⨆ i, f i) ^ 2 = ⨆ i, f i ^ 2 := by
  refine le_antisymm ?_ (iSup_le fun i => pow_le_pow_left' (le_iSup f i) 2)
  rw [pow_two, ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  rcases le_total (f i) (f j) with h | h
  · calc f i * f j ≤ f j * f j := mul_le_mul' h le_rfl
      _ = f j ^ 2 := (pow_two (f j)).symm
      _ ≤ ⨆ k, f k ^ 2 := le_iSup (fun k => f k ^ 2) j
  · calc f i * f j ≤ f i * f i := mul_le_mul' le_rfl h
      _ = f i ^ 2 := (pow_two (f i)).symm
      _ ≤ ⨆ k, f k ^ 2 := le_iSup (fun k => f k ^ 2) i

/-- The supremum over `[0, T]` of a square is the square of the supremum over the subtype
`↥(Set.Icc 0 T)`. -/
theorem biSup_sq_eq_iSup_subtype_sq (g : ℝ → ℝ≥0∞) (T : ℝ) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, g t ^ 2 = (⨆ t : Set.Icc (0 : ℝ) T, g (t : ℝ)) ^ 2 := by
  rw [iSup_subtype'' (Set.Icc (0 : ℝ) T) g, iSup_sq]
  exact iSup_congr fun t => (iSup_sq _).symm

/-! ### Doob's `L²` maximal inequality in the `S²` shape -/

/-- **Doob's `L²` maximal inequality**, with the supremum over `[0, T]` inside the square: for a
right-continuous martingale it is at most four times the second moment of the terminal value. -/
theorem lintegral_biSup_sq_le_of_martingale [IsFiniteMeasure μ] {M : ℝ → Ω → ℝ} {T : ℝ}
    {ℱ : Filtration ℝ mΩ} (hM : Martingale M ℱ μ) (hT : 0 ≤ T)
    (hcad : ∀ᵐ ω ∂μ, ∀ t : ℝ, Filter.Tendsto (fun s => M s ω) (nhdsWithin t (Set.Ioi t))
      (nhds (M t ω))) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ 4 * ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have hcongr : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      = ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T, (‖M (t : ℝ) ω‖₊ : ℝ≥0∞)) ^ 2 ∂μ :=
    lintegral_congr fun ω => biSup_sq_eq_iSup_subtype_sq (fun t => (‖M t ω‖₊ : ℝ≥0∞)) T
  rw [hcongr]
  exact LevyStochCalc.Probability.lintegral_iSup_sq_le_of_martingale hM hT hcad

/-! ### Subadditivity of the `S²` seminorm -/

/-- The square of a sum of two reals is at most twice the sum of the squares, in `ℝ≥0∞`. -/
theorem sq_enorm_add_le (a b : ℝ) :
    (‖a + b‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by
  have hnn : ‖a + b‖₊ ^ 2 ≤ 2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 := by
    refine (pow_le_pow_left' (nnnorm_add_le a b) 2).trans ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]
  calc (‖a + b‖₊ : ℝ≥0∞) ^ 2 = ((‖a + b‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
    _ ≤ ((2 * ‖a‖₊ ^ 2 + 2 * ‖b‖₊ ^ 2 : ℝ≥0) : ℝ≥0∞) := ENNReal.coe_le_coe.mpr hnn
    _ = 2 * (‖a‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b‖₊ : ℝ≥0∞) ^ 2 := by push_cast; ring

/-- The squared supremum over `[0, T]` of a sum of two processes is at most twice the sum of the
squared suprema. -/
theorem biSup_sq_add_le (A B : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω + B t ω‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2)
        + 2 * ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2 := by
  refine iSup₂_le fun t ht => (sq_enorm_add_le (A t ω) (B t ω)).trans (add_le_add ?_ ?_)
  · exact mul_le_mul' le_rfl
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖A t ω‖₊ : ℝ≥0∞) ^ 2) t ht)
  · exact mul_le_mul' le_rfl
      (le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖B t ω‖₊ : ℝ≥0∞) ^ 2) t ht)

/-- The `S²` seminorm of a sum of two processes is at most twice the sum of the `S²` seminorms. -/
theorem lintegral_biSup_sq_add_le (A B : ℝ → Ω → ℝ) (T : ℝ)
    (hB : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) μ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω + B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
        + 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω + B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ ∫⁻ ω, (2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2)
          + 2 * ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_mono fun ω => biSup_sq_add_le A B T ω
    _ = ∫⁻ ω, 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
          + ∫⁻ ω, 2 * (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_add_right' _ (hB.const_mul 2)
    _ = 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
          + 2 * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖B t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
        rw [lintegral_const_mul' _ _ (by norm_num), lintegral_const_mul' _ _ (by norm_num)]

/-- On a finite measure a constant process has finite `S²` seminorm. -/
theorem lintegral_biSup_sq_const_lt_top [IsFiniteMeasure μ] (c : ℝ) (T : ℝ) :
    ∫⁻ _ω, (⨆ _t ∈ Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ := by
  refine lt_of_le_of_lt (lintegral_mono fun ω => iSup₂_le fun _ _ =>
    le_refl ((‖c‖₊ : ℝ≥0∞) ^ 2)) ?_
  rw [lintegral_const]
  exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) (measure_lt_top μ Set.univ)

/-- A sum of a constant and three processes of finite `S²` seminorm has finite `S²` seminorm. -/
theorem lintegral_biSup_sq_const_add_add_add_lt_top [IsFiniteMeasure μ] (c : ℝ)
    (M₁ M₂ A : ℝ → Ω → ℝ) (T : ℝ)
    (hM₁ : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₁ t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (hM₂ : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₂ t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (hA : AEMeasurable (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) μ)
    (h₁ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₁ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤)
    (h₂ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M₂ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤)
    (h₃ : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖c + M₁ t ω + M₂ t ω + A t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ := by
  have two_lt : (2 : ℝ≥0∞) < ⊤ := by norm_num
  have hc := lintegral_biSup_sq_const_lt_top (μ := μ) c T
  have hstep3 := lintegral_biSup_sq_add_le (μ := μ) (fun _ _ => c) M₁ T hM₁
  have hstep2 := lintegral_biSup_sq_add_le (μ := μ) (fun t ω => c + M₁ t ω) M₂ T hM₂
  have hstep1 := lintegral_biSup_sq_add_le (μ := μ)
    (fun t ω => c + M₁ t ω + M₂ t ω) A T hA
  have h3 : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖c + M₁ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ :=
    lt_of_le_of_lt hstep3
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top two_lt hc, ENNReal.mul_lt_top two_lt h₁⟩)
  have h2' : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      (‖c + M₁ t ω + M₂ t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ < ⊤ :=
    lt_of_le_of_lt hstep2
      (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top two_lt h3, ENNReal.mul_lt_top two_lt h₂⟩)
  exact lt_of_le_of_lt hstep1
    (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top two_lt h2', ENNReal.mul_lt_top two_lt h₃⟩)

/-! ### The drift term -/

/-- The squared supremum over `[0, T]` of a time integral is at most the square of the total
integral of the norm of the integrand. -/
theorem biSup_sq_setIntegral_le (g : Ω → ℝ → ℝ) (T : ℝ) (ω : Ω) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2
      ≤ (∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞)) ^ 2 := by
  refine iSup₂_le fun t ht => pow_le_pow_left' ?_ 2
  calc (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞)
      ≤ ∫⁻ s in Set.Icc (0 : ℝ) t, (‖g ω s‖₊ : ℝ≥0∞) :=
        enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) :=
        lintegral_mono_set (Set.Icc_subset_Icc le_rfl ht.2)

/-- Cauchy–Schwarz on `[0, T]`: the square of the integral is at most `T` times the integral of
the square. -/
theorem sq_lintegral_le_ofReal_mul_lintegral_sq (T : ℝ) {f : ℝ → ℝ≥0∞}
    (hf : AEMeasurable f (volume.restrict (Set.Icc (0 : ℝ) T))) :
    (∫⁻ s in Set.Icc (0 : ℝ) T, f s) ^ 2
      ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, f s ^ 2 := by
  have hsqr : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := by
    intro x
    rw [← ENNReal.rpow_natCast x 2]
    norm_num
  have hhalf : ∀ x : ℝ≥0∞, (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
    intro x
    rw [← ENNReal.rpow_natCast (x ^ ((1 : ℝ) / 2)) 2, ← ENNReal.rpow_mul]
    norm_num
  have huniv : (volume.restrict (Set.Icc (0 : ℝ) T)) Set.univ = ENNReal.ofReal T := by
    rw [Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Set.Icc (0 : ℝ) T))
    Real.HolderConjugate.two_two hf (aemeasurable_const (b := (1 : ℝ≥0∞)))
  simp only [Pi.mul_apply, mul_one, lintegral_const, huniv, hsqr, one_pow, one_mul] at h
  calc (∫⁻ s in Set.Icc (0 : ℝ) T, f s) ^ 2
      ≤ ((∫⁻ s in Set.Icc (0 : ℝ) T, f s ^ 2) ^ ((1 : ℝ) / 2)
          * ENNReal.ofReal T ^ ((1 : ℝ) / 2)) ^ 2 := pow_le_pow_left' h 2
    _ = ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, f s ^ 2 := by
        rw [mul_pow, hhalf, hhalf, mul_comm]

/-- The `S²` seminorm of a time integral is at most `T` times the `L²` norm of its integrand. -/
theorem lintegral_biSup_sq_setIntegral_le (g : Ω → ℝ → ℝ) (T : ℝ)
    (hg : ∀ ω, IntegrableOn (g ω) (Set.Icc (0 : ℝ) T)) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ ENNReal.ofReal T
        * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
  have key : ∀ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2)
      ≤ ENNReal.ofReal T * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    (biSup_sq_setIntegral_le g T ω).trans
      (sq_lintegral_le_ofReal_mul_lintegral_sq T (hg ω).aestronglyMeasurable.enorm)
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        (‖∫ s in Set.Icc (0 : ℝ) t, g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ
      ≤ ∫⁻ ω, (ENNReal.ofReal T
          * ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_mono key
    _ = ENNReal.ofReal T
          * ∫⁻ ω, (∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2) ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-! ### Scalar multiples -/

/-- The squared supremum over `[0, T]` of a scalar multiple of a process is the squared norm of
the scalar times the squared supremum of the process. -/
theorem biSup_sq_const_mul (c : ℝ) (M : ℝ → Ω → ℝ) (T : ℝ) (ω : Ω) :
    ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖c * M t ω‖₊ : ℝ≥0∞) ^ 2
      = (‖c‖₊ : ℝ≥0∞) ^ 2 * ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 := by
  simp only [nnnorm_mul, ENNReal.coe_mul, mul_pow, ENNReal.mul_iSup]

/-- The `S²` seminorm of a scalar multiple of a process is the squared norm of the scalar times
the `S²` seminorm of the process. -/
theorem lintegral_biSup_sq_const_mul (c : ℝ) (M : ℝ → Ω → ℝ) (T : ℝ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖c * M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ
      = (‖c‖₊ : ℝ≥0∞) ^ 2
        * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2) ∂μ := by
  rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)]
  exact lintegral_congr fun ω => biSup_sq_const_mul c M T ω

end LevyStochCalc.BSDEJ.SupBound
