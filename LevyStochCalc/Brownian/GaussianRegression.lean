/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoFourthMomentIncrements
import LevyStochCalc.Probability.IndepJoin
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-!
# Gaussian regression of a Brownian increment on a longer one

For a Brownian motion `W` with a Brownian filtration `ℱ` and times `0 ≤ t < r ≤ T`, put
`A = W_r − W_t`, `S = W_T − W_t` and `λ = (r − t) / (T − t)`. The residual `A − λ S` is a centred
Gaussian variable with zero covariance against `S`; as `(A − λ S, S)` is Gaussian the two are
independent, and as both are functions of the increments after `t` the residual is independent
of `ℱ_t ⊔ σ(S)`. Hence every square-integrable `Φ` measurable for `ℱ_t ⊔ σ(S)` satisfies

  `E[Φ A] = λ E[Φ S]`.

## Main statements

* `indep_sup_comap_residual` — the residual is independent of `ℱ_t ⊔ σ(S)`.
* `integral_mul_increment_eq_regression` — the regression identity.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Regression

variable (W : BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ)

private theorem hasGaussianLaw_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    HasGaussianLaw (fun ω => W.W b ω - W.W a ω) P := by
  haveI : IsGaussian (P.map fun ω => W.W b ω - W.W a ω) := by
    rw [W.increment_gaussian ha hab]; infer_instance
  exact IsGaussian.hasGaussianLaw

include hℱ in
/-- **Independence of the regression residual.** For `0 ≤ t < r < T` the residual
`(W_r − W_t) − λ (W_T − W_t)`, `λ = (r − t) / (T − t)`, is independent of `ℱ_t ⊔ σ(W_T − W_t)`. -/
theorem indep_sup_comap_residual {t r T : ℝ} (ht : 0 ≤ t) (htr : t < r) (hrT : r < T) :
    Indep (ℱ t ⊔ MeasurableSpace.comap (fun ω => W.W T ω - W.W t ω) inferInstance)
      (MeasurableSpace.comap (fun ω => (W.W r ω - W.W t ω)
        - (r - t) / (T - t) * (W.W T ω - W.W t ω)) inferInstance) P := by
  set A : Ω → ℝ := fun ω => W.W r ω - W.W t ω with hAdef
  set B : Ω → ℝ := fun ω => W.W T ω - W.W r ω with hBdef
  set S : Ω → ℝ := fun ω => W.W T ω - W.W t ω with hSdef
  set lam : ℝ := (r - t) / (T - t) with hlam
  set C : Ω → ℝ := fun ω => A ω - lam * S ω with hCdef
  have hr0 : 0 ≤ r := ht.trans htr.le
  have hAm : Measurable A := (W.measurable_eval r).sub (W.measurable_eval t)
  have hBm : Measurable B := (W.measurable_eval T).sub (W.measurable_eval r)
  have hSm : Measurable S := (W.measurable_eval T).sub (W.measurable_eval t)
  have hCm : Measurable C := hAm.sub (hSm.const_mul _)
  -- `A` and `B` are independent Gaussians
  have hAB : IndepFun A B P := by
    have hind := hℱ.indep hr0 hrT
    have hAr : Measurable[ℱ r] A :=
      (hℱ.measurable r).sub ((hℱ.measurable t).mono (ℱ.mono htr.le) le_rfl)
    rw [IndepFun_iff]
    intro s s' hs hs'
    rw [Indep_iff] at hind
    exact hind s s' (hAr.comap_le s hs) hs'
  have hGAB : HasGaussianLaw (fun ω => (A ω, B ω)) P :=
    IndepFun.hasGaussianLaw (hasGaussianLaw_increment W ht htr)
      (hasGaussianLaw_increment W hr0 hrT) hAB
  -- `(C, S)` is a linear image of `(A, B)`
  let L : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
    ((1 - lam) • ContinuousLinearMap.fst ℝ ℝ ℝ - lam • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
      (ContinuousLinearMap.fst ℝ ℝ ℝ + ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hCS : HasGaussianLaw (fun ω => (C ω, S ω)) P := by
    have h := hGAB.map_fun L
    refine h.congr (Eventually.of_forall fun ω => ?_)
    simp only [hCdef, hAdef, hBdef, hSdef]
    ext
    · simp [L]; ring
    · simp [L]
  -- the covariance of `C` and `S` vanishes
  have hA2 : MemLp A 2 P := Ito.memLp_increment W ht htr 2 (by norm_num)
  have hB2 : MemLp B 2 P := Ito.memLp_increment W hr0 hrT 2 (by norm_num)
  have hS2 : MemLp S 2 P := Ito.memLp_increment W ht (htr.trans hrT) 2 (by norm_num)
  have hC2 : MemLp C 2 P := hA2.sub (hS2.const_mul _)
  have hEA : ∫ ω, A ω ∂P = 0 := by
    simpa using Ito.integral_increment_pow_odd W ht htr (m := 1) odd_one
  have hEB : ∫ ω, B ω ∂P = 0 := by
    simpa using Ito.integral_increment_pow_odd W hr0 hrT (m := 1) odd_one
  have hEAA : ∫ ω, A ω ^ 2 ∂P = r - t := Ito.integral_increment_sq W ht htr
  have hEBB : ∫ ω, B ω ^ 2 ∂P = T - r := Ito.integral_increment_sq W hr0 hrT
  have hEAB : ∫ ω, A ω * B ω ∂P = 0 := by
    change ∫ ω, (A * B) ω ∂P = 0
    rw [hAB.integral_mul_eq_mul_integral hAm.aestronglyMeasurable hBm.aestronglyMeasurable,
      hEA, zero_mul]
  have hSAB : S = fun ω => A ω + B ω := by
    funext ω; simp only [hSdef, hAdef, hBdef]; ring
  have hEC : ∫ ω, C ω ∂P = 0 := by
    rw [hCdef, integral_sub (hA2.integrable one_le_two) ((hS2.integrable one_le_two).const_mul _),
      integral_const_mul, hSAB, integral_add (hA2.integrable one_le_two)
        (hB2.integrable one_le_two), hEA, hEB]
    ring
  have hcov : cov[C, S; P] = 0 := by
    rw [covariance_eq_sub hC2 hS2, hEC, zero_mul, sub_zero]
    have hpt : (C * S) = fun ω => (1 - lam) * A ω ^ 2 + (1 - 2 * lam) * (A ω * B ω)
        - lam * B ω ^ 2 := by
      funext ω; simp only [Pi.mul_apply, hCdef, hSAB]; ring
    rw [hpt, integral_sub, integral_add, integral_const_mul, integral_const_mul,
      integral_const_mul, hEAA, hEBB, hEAB]
    · rw [hlam]
      have : T - t ≠ 0 := by linarith
      field_simp
      ring
    · exact hA2.integrable_sq.const_mul _
    · exact (hA2.integrable_mul hB2).const_mul _
    · exact (hA2.integrable_sq.const_mul _).add ((hA2.integrable_mul hB2).const_mul _)
    · exact hB2.integrable_sq.const_mul _
  have hCSind : IndepFun C S P := hCS.indepFun_of_covariance_eq_zero hcov
  -- `σ(S) ⊔ σ(C)` lies in the future of `t`
  have hfut : MeasurableSpace.comap S inferInstance ⊔ MeasurableSpace.comap C inferInstance
      ≤ ⨆ u ∈ Set.Ioi t, MeasurableSpace.comap (fun ω => W.W u ω - W.W t ω) inferInstance := by
    have hS' : MeasurableSpace.comap S inferInstance
        ≤ ⨆ u ∈ Set.Ioi t, MeasurableSpace.comap (fun ω => W.W u ω - W.W t ω) inferInstance :=
      le_iSup₂_of_le T (Set.mem_Ioi.mpr (htr.trans hrT)) le_rfl
    have hA' : MeasurableSpace.comap A inferInstance
        ≤ ⨆ u ∈ Set.Ioi t, MeasurableSpace.comap (fun ω => W.W u ω - W.W t ω) inferInstance :=
      le_iSup₂_of_le r (Set.mem_Ioi.mpr htr) le_rfl
    refine sup_le hS' ?_
    have hCmeas : Measurable[MeasurableSpace.comap A inferInstance
        ⊔ MeasurableSpace.comap S inferInstance] C :=
      (comap_measurable A |>.mono le_sup_left le_rfl).sub
        ((comap_measurable S |>.mono le_sup_right le_rfl).const_mul _)
    exact hCmeas.comap_le.trans (sup_le hA' hS')
  have h2 : Indep (ℱ t) (MeasurableSpace.comap S inferInstance
      ⊔ MeasurableSpace.comap C inferInstance) P :=
    indep_of_indep_of_le_right (hℱ.indep_future ht) hfut
  have h13 : Indep (MeasurableSpace.comap S inferInstance)
      (MeasurableSpace.comap C inferInstance) P := hCSind.symm
  have := Probability.indep_sup_left_of_indep hSm.comap_le (ℱ.le t) hCm.comap_le h13 h2
  rwa [sup_comm] at this

include hℱ in
/-- **Gaussian regression.** For `0 ≤ t < r ≤ T` and a square-integrable `Φ` measurable for
`ℱ_t ⊔ σ(W_T − W_t)`, `E[Φ (W_r − W_t)] = (r − t) / (T − t) · E[Φ (W_T − W_t)]`. -/
theorem integral_mul_increment_eq_regression {t r T : ℝ} (ht : 0 ≤ t) (htr : t < r)
    (hrT : r ≤ T) {Φ : Ω → ℝ}
    (hΦm : StronglyMeasurable[ℱ t ⊔ MeasurableSpace.comap (fun ω => W.W T ω - W.W t ω)
      inferInstance] Φ) (hΦ : MemLp Φ 2 P) :
    ∫ ω, Φ ω * (W.W r ω - W.W t ω) ∂P
      = (r - t) / (T - t) * ∫ ω, Φ ω * (W.W T ω - W.W t ω) ∂P := by
  rcases eq_or_lt_of_le hrT with rfl | hrT'
  · have : r - t ≠ 0 := by linarith
    rw [div_self this, one_mul]
  set lam : ℝ := (r - t) / (T - t) with hlam
  have hA2 : MemLp (fun ω => W.W r ω - W.W t ω) 2 P := Ito.memLp_increment W ht htr 2 (by norm_num)
  have hS2 : MemLp (fun ω => W.W T ω - W.W t ω) 2 P :=
    Ito.memLp_increment W ht (htr.trans hrT') 2 (by norm_num)
  set C : Ω → ℝ := fun ω => (W.W r ω - W.W t ω) - lam * (W.W T ω - W.W t ω) with hCdef
  have hC2 : MemLp C 2 P := hA2.sub (hS2.const_mul _)
  have hind := indep_sup_comap_residual W ℱ hℱ ht htr hrT'
  have hle : ℱ t ⊔ MeasurableSpace.comap (fun ω => W.W T ω - W.W t ω) inferInstance
      ≤ ‹MeasurableSpace Ω› :=
    sup_le (ℱ.le t) ((W.measurable_eval T).sub (W.measurable_eval t)).comap_le
  have hIF : IndepFun Φ C P := by
    rw [IndepFun_iff]
    intro s s' hs hs'
    rw [Indep_iff] at hind
    exact hind s s' (hΦm.measurable.comap_le s hs) hs'
  have hEC : ∫ ω, C ω ∂P = 0 := by
    have hEA : ∫ ω, (W.W r ω - W.W t ω) ∂P = 0 := by
      simpa using Ito.integral_increment_pow_odd W ht htr (m := 1) odd_one
    have hES : ∫ ω, (W.W T ω - W.W t ω) ∂P = 0 := by
      simpa using Ito.integral_increment_pow_odd W ht (htr.trans hrT') (m := 1) odd_one
    rw [hCdef, integral_sub (hA2.integrable one_le_two) ((hS2.integrable one_le_two).const_mul _),
      integral_const_mul, hEA, hES]
    ring
  have hΦC : ∫ ω, Φ ω * C ω ∂P = 0 := by
    change ∫ ω, (Φ * C) ω ∂P = 0
    rw [hIF.integral_mul_eq_mul_integral (hΦm.mono hle).aestronglyMeasurable
      hC2.aestronglyMeasurable, hEC, mul_zero]
  have hsplit : ∫ ω, Φ ω * (W.W r ω - W.W t ω) ∂P
      = ∫ ω, Φ ω * C ω ∂P + lam * ∫ ω, Φ ω * (W.W T ω - W.W t ω) ∂P := by
    have i1 : Integrable (fun ω => Φ ω * C ω) P := hΦ.integrable_mul hC2
    have i2 : Integrable (fun ω => lam * (Φ ω * (W.W T ω - W.W t ω))) P :=
      (hΦ.integrable_mul hS2).const_mul _
    rw [← integral_const_mul, ← integral_add i1 i2]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [hCdef]
    ring
  rw [hsplit, hΦC, zero_add]

end Regression

end LevyStochCalc.Brownian
