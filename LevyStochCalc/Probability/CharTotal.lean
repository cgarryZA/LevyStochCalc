/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# Characters separate `L¹` densities

An integrable function on an inner-product space that integrates to zero against every character
`v ↦ exp(i⟪v, w⟫)` vanishes almost everywhere. Splitting the function into positive and negative
parts turns the hypothesis into an equality of the characteristic functions of two finite
measures, which `MeasureTheory.Measure.ext_of_charFun` reads as an equality of the measures.
-/

open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Probability

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [CompleteSpace V] [SecondCountableTopology V]


/-- The characteristic function of a density-weighted measure. -/
theorem charFun_withDensity_ofReal {μ : Measure V} {u : V → ℝ} (hu : AEMeasurable u μ) (w : V) :
    charFun (μ.withDensity fun v => ENNReal.ofReal (u v)) w
      = ∫ v, Real.toNNReal (u v) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) ∂μ := by
  rw [charFun_apply]
  exact integral_withDensity_eq_integral_smul₀ (f := fun v => Real.toNNReal (u v))
    hu.real_toNNReal _

/-- A character is bounded and continuous, so it multiplies an integrable function into an
integrable one. -/
theorem integrable_char_smul {μ : Measure V} {z : V → ℝ} (hz : Integrable z μ) (w : V) :
    Integrable (fun v => z v • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)) μ := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  refine Integrable.mono' hz.norm
    (hz.aestronglyMeasurable.smul hcont.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]

/-- A character multiplies an integrable complex function into an integrable one. -/
theorem integrable_char_mul {μ : Measure V} {g : V → ℂ} (hg : Integrable g μ) (w : V) :
    Integrable (fun v => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v) μ := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  refine Integrable.mono' hg.norm
    (hcont.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  simp [norm_mul, Complex.norm_exp_ofReal_mul_I]

/-- The complex conjugate of an integrable function is integrable. -/
theorem integrable_conj {μ : Measure V} {g : V → ℂ} (hg : Integrable g μ) :
    Integrable (fun v => (starRingEnd ℂ) (g v)) μ := by
  refine Integrable.mono' hg.norm
    (Complex.continuous_conj.comp_aestronglyMeasurable hg.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun v => ?_)
  simp

/-- The positive part of an integrable function is integrable. -/
theorem integrable_toNNReal_coe {μ : Measure V} {z : V → ℝ} (hz : Integrable z μ) :
    Integrable (fun v => ((Real.toNNReal (z v) : ℝ≥0) : ℝ)) μ := by
  refine Integrable.mono' hz.norm
    (hz.aemeasurable.real_toNNReal.coe_nnreal_real).aestronglyMeasurable
    (Filter.Eventually.of_forall fun v => ?_)
  simp only [Real.norm_eq_abs, Real.coe_toNNReal']
  rcases le_total 0 (z v) with hv | hv
  · rw [max_eq_left hv, abs_of_nonneg hv]
  · rw [max_eq_right hv]
    simpa using abs_nonneg (z v)

/-- **Characters separate integrable densities.** An integrable real function integrating to zero
against every character vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_char_smul_eq_zero {μ : Measure V} [IsFiniteMeasure μ]
    {u : V → ℝ} (hu : Integrable u μ)
    (h : ∀ w : V, ∫ v, u v • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) ∂μ = 0) :
    u =ᵐ[μ] 0 := by
  haveI hpos : IsFiniteMeasure (μ.withDensity fun v => ENNReal.ofReal (u v)) :=
    isFiniteMeasure_withDensity_ofReal hu.2
  haveI hneg : IsFiniteMeasure (μ.withDensity fun v => ENNReal.ofReal (-(u v))) :=
    isFiniteMeasure_withDensity_ofReal (f := fun v => -(u v)) hu.neg.2
  have hchar : charFun (μ.withDensity fun v => ENNReal.ofReal (u v))
      = charFun (μ.withDensity fun v => ENNReal.ofReal (-(u v))) := by
    funext w
    rw [charFun_withDensity_ofReal hu.aemeasurable w,
      charFun_withDensity_ofReal (u := fun v => -(u v)) hu.aemeasurable.neg w]
    have hsplit : ∀ v : V,
        (Real.toNNReal (u v) : ℝ) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)
          = u v • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)
            + (Real.toNNReal (-(u v)) : ℝ) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) := by
      intro v
      rw [← add_smul]
      congr 1
      simp only [Real.coe_toNNReal']
      rcases le_total 0 (u v) with hv | hv
      · rw [max_eq_left hv, max_eq_right (by linarith)]; ring
      · rw [max_eq_right hv, max_eq_left (by linarith)]; ring
    have hsmulL : ∀ v : V, (Real.toNNReal (u v) : ℝ≥0) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)
        = (Real.toNNReal (u v) : ℝ) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
      fun v => NNReal.smul_def _ _
    have hsmulR : ∀ v : V,
        (Real.toNNReal (-(u v)) : ℝ≥0) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)
          = (Real.toNNReal (-(u v)) : ℝ) • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
      fun v => NNReal.smul_def _ _
    simp only [hsmulL, hsmulR, hsplit]
    rw [integral_add (integrable_char_smul hu w)
      (integrable_char_smul (integrable_toNNReal_coe (z := fun v : V => -(u v)) hu.neg) w),
      h w, zero_add]
  have hmeas := Measure.ext_of_charFun hchar
  have hfin : ∫⁻ v, ENNReal.ofReal (u v) ∂μ ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun v => ?_) hu.2)
    calc ENNReal.ofReal (u v) ≤ ENNReal.ofReal |u v| :=
          ENNReal.ofReal_le_ofReal (le_abs_self _)
      _ = ‖u v‖ₑ := by rw [Real.enorm_eq_ofReal_abs]
  have hae : (fun v => ENNReal.ofReal (u v)) =ᵐ[μ] fun v => ENNReal.ofReal (-(u v)) :=
    (withDensity_eq_iff (ENNReal.measurable_ofReal.comp_aemeasurable hu.aemeasurable)
      (ENNReal.measurable_ofReal.comp_aemeasurable hu.aemeasurable.neg) hfin).mp hmeas
  filter_upwards [hae] with v hv
  have hz : u v = 0 := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have h1 : ENNReal.ofReal (u v) = 0 := ENNReal.ofReal_eq_zero.mpr hlt.le
      have h2 : 0 < ENNReal.ofReal (-(u v)) := ENNReal.ofReal_pos.mpr (by linarith)
      rw [h1] at hv
      exact h2.ne' hv.symm
    · have h1 : 0 < ENNReal.ofReal (u v) := ENNReal.ofReal_pos.mpr hgt
      have h2 : ENNReal.ofReal (-(u v)) = 0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
      rw [h2] at hv
      exact h1.ne' hv
  simpa using hz

omit [CompleteSpace V] [SecondCountableTopology V] in
/-- A character at `-w` is the conjugate of the character at `w`. -/
theorem char_neg (v w : V) :
    Complex.exp ((⟪v, -w⟫ : ℝ) * Complex.I)
      = (starRingEnd ℂ) (Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)) := by
  rw [← Complex.exp_conj]
  congr 1
  simp [inner_neg_right, Complex.conj_ofReal]

/-- **Characters separate integrable complex densities.** -/
theorem ae_eq_zero_of_integral_char_mul_eq_zero {μ : Measure V} [IsFiniteMeasure μ]
    {g : V → ℂ} (hg : Integrable g μ)
    (h : ∀ w : V, ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v ∂μ = 0) :
    g =ᵐ[μ] 0 := by
  -- the conjugate identity: the same integral against `conj g` also vanishes
  have hconj : ∀ w : V,
      ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (starRingEnd ℂ) (g v) ∂μ = 0 := by
    intro w
    have hthis : (starRingEnd ℂ)
        (∫ v, Complex.exp ((⟪v, -w⟫ : ℝ) * Complex.I) * g v ∂μ) = 0 := by
      rw [h (-w), map_zero]
    rw [← integral_conj] at hthis
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)) hthis
    rw [map_mul, char_neg v w]
    simp
  have hre : ∀ w : V,
      ∫ v, (g v).re • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) ∂μ = 0 := by
    intro w
    have hsum : ∀ v : V,
        (g v).re • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)
          = (2 : ℂ)⁻¹ * (Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v
              + Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (starRingEnd ℂ) (g v)) := by
      intro v
      have hc : g v + (starRingEnd ℂ) (g v) = ((2 * (g v).re : ℝ) : ℂ) := Complex.add_conj _
      rw [Complex.real_smul, ← mul_add, hc]
      push_cast
      ring
    simp only [hsum]
    rw [integral_const_mul, integral_add (integrable_char_mul hg w)
      (integrable_char_mul (integrable_conj hg) w), h w, hconj w, add_zero, mul_zero]
  have him : ∀ w : V,
      ∫ v, (g v).im • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) ∂μ = 0 := by
    intro w
    have hsum : ∀ v : V,
        (g v).im • Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)
          = (2 * Complex.I)⁻¹ * (Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * g v
              - Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (starRingEnd ℂ) (g v)) := by
      intro v
      have hc : g v - (starRingEnd ℂ) (g v) = ((2 * (g v).im : ℝ) : ℂ) * Complex.I :=
        Complex.sub_conj _
      rw [Complex.real_smul, ← mul_sub, hc]
      have hI : Complex.I ≠ 0 := Complex.I_ne_zero
      field_simp
      push_cast
      ring
    simp only [hsum]
    rw [integral_const_mul, integral_sub (integrable_char_mul hg w)
      (integrable_char_mul (integrable_conj hg) w), h w, hconj w, sub_zero, mul_zero]
  have hre0 := ae_eq_zero_of_integral_char_smul_eq_zero hg.re hre
  have him0 := ae_eq_zero_of_integral_char_smul_eq_zero hg.im him
  filter_upwards [hre0, him0] with v hv1 hv2
  simp only [Pi.zero_apply] at hv1 hv2 ⊢
  exact Complex.ext hv1 hv2

/-! ### Totality in `L²` -/

/-- A character is bounded, hence in `L²` of a finite measure. -/
theorem memLp_char (μ : Measure V) [IsFiniteMeasure μ] (w : V) :
    MemLp (fun v => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I)) 2 μ := by
  have hcont : Continuous fun v : V => Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) :=
    Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp
        (continuous_inner.comp (continuous_id.prodMk continuous_const))).mul continuous_const)
  refine MemLp.of_bound hcont.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun v => ?_)
  simp [Complex.norm_exp_ofReal_mul_I]

/-- The character at `w`, as an element of `L²`. -/
noncomputable def charLp (μ : Measure V) [IsFiniteMeasure μ] (w : V) : Lp ℂ 2 μ :=
  (memLp_char μ w).toLp _

/-- **The characters are total in `L²` of a finite measure.** -/
theorem topologicalClosure_span_charLp (μ : Measure V) [IsFiniteMeasure μ] :
    (Submodule.span ℂ (Set.range (charLp μ))).topologicalClosure = ⊤ := by
  have horth : (Submodule.span ℂ (Set.range (charLp μ)))ᗮ = ⊥ := by
   refine (Submodule.eq_bot_iff _).mpr fun g hg => ?_
   have hgint : Integrable (g : V → ℂ) μ := (Lp.memLp g).integrable one_le_two
   have hzero : ∀ w : V,
       ∫ v, Complex.exp ((⟪v, w⟫ : ℝ) * Complex.I) * (g : V → ℂ) v ∂μ = 0 := by
     intro w
     have hmem : charLp μ (-w) ∈ Submodule.span ℂ (Set.range (charLp μ)) :=
       Submodule.subset_span ⟨-w, rfl⟩
     have hinner : (inner ℂ (charLp μ (-w)) g : ℂ) = 0 :=
       (Submodule.mem_orthogonal _ _).mp hg _ hmem
     rw [L2.inner_def] at hinner
     refine Eq.trans (integral_congr_ae ?_) hinner
     filter_upwards [(memLp_char μ (-w)).coeFn_toLp] with v hv
     rw [show ((charLp μ (-w)) : V → ℂ) v = Complex.exp ((⟪v, -w⟫ : ℝ) * Complex.I) from hv,
       RCLike.inner_apply, char_neg v w]
     simp [mul_comm]
   exact (Lp.eq_zero_iff_ae_eq_zero).mpr (ae_eq_zero_of_integral_char_mul_eq_zero hgint hzero)
  exact Submodule.topologicalClosure_eq_top_iff.mpr horth

end LevyStochCalc.Probability
