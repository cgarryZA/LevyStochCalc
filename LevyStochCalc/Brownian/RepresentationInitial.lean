/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.RepresentationInitialSeparation

/-!
# Brownian martingale representation with initial information

Let `W` be a `d`-dimensional Brownian motion, `𝒢₀` a σ-algebra independent of `W`, and `ℱ` the
augmentation by the null sets of `𝒢₀ ⊔ σ(W_s : s ≤ t)`. On a horizon `T > 0`, every
`ξ ∈ L²(ℱ_T)` is
`ξ = 𝔼[ξ | ℱ₀] + ∑ᵢ ∫₀ᵀ Gⁱ dWⁱ`
for admissible integrands `Gⁱ` (jointly measurable, progressively measurable for `ℱ`, of finite
energy `𝔼 ∫₀ᵀ |Gⁱ|² ds`), and the decomposition is unique: an `ℱ₀`-measurable square-integrable
first term is `𝔼[ξ | ℱ₀]` almost surely and the integrands are determined `P ⊗ ds`-almost
everywhere on `Ω × [0, T]`.

The proof projects `ξ − 𝔼[ξ | ℱ₀]` onto the closed range of the multidimensional Itô integral;
the remainder integrates to zero over every set of `ℱ₀` and is orthogonal to every Itô integral,
so it vanishes by the separation theorem over the filtration with initial information.

## Main statements

* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_vectorIntegral_augInitial`:
  existence of the representation.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.unique_vectorIntegral_augInitial`:
  uniqueness of the initial term and of the integrands.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} {𝒢₀ : MeasurableSpace Ω} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {d : ℕ}

/-- **Martingale representation with initial information.** Over the augmentation of
`𝒢₀ ⊔ ℱ^W`, with `𝒢₀` independent of `W`, every square-integrable `ξ` measurable at time `T > 0`
is `𝔼[ξ | ℱ₀]` plus a sum of coordinate Itô integrals on `[0, T]`. -/
theorem exists_vectorIntegral_augInitial (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P)
    {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ} (hξ2 : MemLp ξ 2 P)
    (hξm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ T] ξ P) :
    ∃ G : ∀ _ : Fin d, HorizonIntegrand P (W.augInitialFiltration 𝒢₀ h𝒢₀) T,
      ξ =ᵐ[P] fun ω => P[ξ | W.augInitialFiltration 𝒢₀ h𝒢₀ 0] ω
        + vectorIntegral W (W.isBrownianFiltration_augInitial h𝒢₀ hind) G ω := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set ℱ := W.augInitialFiltration 𝒢₀ h𝒢₀ with hℱdef
  have hcoord := W.isBrownianFiltration_augInitial h𝒢₀ hind
  haveI : SigmaFinite (P.trim (ℱ.le 0)) := (isFiniteMeasure_trim (ℱ.le 0)).toSigmaFinite
  set c : Ω → ℝ := P[ξ | ℱ 0] with hc
  set Z : Ω → ℝ := fun ω => ξ ω - c ω with hZ
  have hc2 : MemLp c 2 P := hξ2.condExp (by norm_num)
  have hZ2 : MemLp Z 2 P := hξ2.sub hc2
  have hcm : AEStronglyMeasurable[ℱ T] c P :=
    (stronglyMeasurable_condExp.mono (ℱ.mono hT.le)).aestronglyMeasurable
  have hZm : AEStronglyMeasurable[ℱ T] Z P := hξm.sub hcm
  set V : Fin d → Submodule ℝ (Lp ℝ 2 P) := fun i => itoRange (W.W i) (hcoord i) hT with hVdef
  haveI hcl : IsClosed ((⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    isClosed_iSup_itoRange W hcoord hT
  haveI : CompleteSpace (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) := hcl.completeSpace_coe
  haveI : ∀ i : Fin d, CompleteSpace (V i) := fun i =>
    (isClosed_itoRange (W.W i) (hcoord i) hT).completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  have hproj : ∑ i, (V i).starProjection y = y :=
    (orthogonalFamily_itoRange W hcoord hT).sum_projection_of_mem_iSup y hy
  have hcomp : ∀ i : Fin d, ∃ G : HorizonIntegrand P ℱ T,
      (((V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] G.integral (W.W i) (hcoord i) :=
    fun i => (V i).starProjection_apply_mem y
  choose G hG using hcomp
  have hyfun : (y : Ω → ℝ) =ᵐ[P] vectorIntegral W hcoord G := by
    have hsumfun : ((∑ i, (V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] fun ω => ∑ i : Fin d, (((V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ) ω :=
      MeasureTheory.Lp.coeFn_fun_finsetSum _ _
    rw [← hproj]
    filter_upwards [hsumfun, Filter.eventually_all.2 (fun i : Fin d => hG i)] with ω e1 e2
    rw [e1, vectorIntegral]
    exact Finset.sum_congr rfl fun i _ => e2 i
  have hsplit : Z =ᵐ[P] fun ω => vectorIntegral W hcoord G ω + (z : Ω → ℝ) ω := by
    filter_upwards [hZ2.coeFn_toLp, Lp.coeFn_add y z, hyfun] with ω e1 e2 e3
    rw [← e1, hyz, e2, Pi.add_apply, e3]
  have hzdiff : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - vectorIntegral W hcoord G ω := by
    filter_upwards [hsplit] with ω e1
    rw [e1]; ring
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P :=
    (hZm.sub (aestronglyMeasurable_vectorIntegral W hcoord G)).congr hzdiff.symm
  have hzA : ∀ A, MeasurableSet[𝒢₀] A → ∫ ω in A, (z : Ω → ℝ) ω ∂P = 0 := by
    intro A hA
    have hA0 : MeasurableSet[ℱ 0] A := W.le_augFiltration_initialFiltration h𝒢₀ 0 A hA
    have hAm : MeasurableSet A := h𝒢₀ A hA
    have hξi : Integrable ξ P := hξ2.integrable (by norm_num)
    have hIi : ∀ i, Integrable ((G i).integral (W.W i) (hcoord i)) P := fun i =>
      (HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)).integrable (by norm_num)
    rw [setIntegral_congr_ae hAm (hzdiff.mono fun ω h _ => h),
      integral_sub (show Integrable Z P from hξi.sub integrable_condExp).integrableOn
        ((memLp_vectorIntegral W hcoord G).integrable (by norm_num)).integrableOn,
      integral_sub hξi.integrableOn integrable_condExp.integrableOn,
      setIntegral_condExp (ℱ.le 0) hξi hA0, sub_self, zero_sub, neg_eq_zero]
    change ∫ ω in A, ∑ i : Fin d, (G i).integral (W.W i) (hcoord i) ω ∂P = 0
    rw [integral_finsetSum _ fun i _ => (hIi i).integrableOn]
    exact Finset.sum_eq_zero fun i _ =>
      HorizonIntegrand.setIntegral_integral_eq_zero (W.W i) (hcoord i) hT (G i) hA0
  have hzperp : ∀ (i : Fin d) (K : HorizonIntegrand P ℱ T),
      ∫ ω, (z : Ω → ℝ) ω * K.integral (W.W i) (hcoord i) ω ∂P = 0 := by
    intro i K
    have hmem : (HorizonIntegrand.memLp (W.W i) (hcoord i) K).toLp
        (K.integral (W.W i) (hcoord i)) ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem i ⟨K, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (HorizonIntegrand.memLp (W.W i) (hcoord i) K)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzzero := ae_eq_zero_of_perp_augInitial W h𝒢₀ hind hT hzmem hzmeas hzA hzperp
  refine ⟨G, ?_⟩
  filter_upwards [hsplit, hzzero] with ω e1 e2
  have e3 : ξ ω = Z ω + c ω := by rw [hZ]; ring
  rw [e3, e1, e2, Pi.zero_apply, add_zero, add_comm]

/-- **Uniqueness of the representation.** If `η + ∑ᵢ ∫₀ᵀ Gⁱ dWⁱ = η' + ∑ᵢ ∫₀ᵀ G'ⁱ dWⁱ` almost
surely, with `η, η'` measurable for `ℱ₀`, then `η = η'` almost surely and
`Gⁱ = G'ⁱ` almost everywhere for `P ⊗ ds` on `Ω × [0, T]`. -/
theorem unique_vectorIntegral_augInitial (W : MultidimBrownianMotion P d)
    (h𝒢₀ : 𝒢₀ ≤ ‹MeasurableSpace Ω›) (hind : Indep 𝒢₀ (⨆ t, W.naturalFiltration t) P)
    {T : ℝ} (hT : 0 < T) {η η' : Ω → ℝ}
    (hηm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ 0] η P)
    (hη'm : AEStronglyMeasurable[W.augInitialFiltration 𝒢₀ h𝒢₀ 0] η' P)
    (G G' : ∀ _ : Fin d, HorizonIntegrand P (W.augInitialFiltration 𝒢₀ h𝒢₀) T)
    (h : (fun ω => η ω + vectorIntegral W (W.isBrownianFiltration_augInitial h𝒢₀ hind) G ω)
      =ᵐ[P] fun ω => η' ω + vectorIntegral W (W.isBrownianFiltration_augInitial h𝒢₀ hind) G' ω) :
    η =ᵐ[P] η' ∧ ∀ i, (fun p : Ω × ℝ => (G i).toFun p.1 p.2)
      =ᵐ[energyMeasure P T] fun p => (G' i).toFun p.1 p.2 := by
  let ℱ := W.augInitialFiltration 𝒢₀ h𝒢₀
  have hcoord := W.isBrownianFiltration_augInitial h𝒢₀ hind
  haveI : SigmaFinite (P.trim (ℱ.le 0)) := (isFiniteMeasure_trim (ℱ.le 0)).toSigmaFinite
  set D : Fin d → Ω → ℝ := fun i ω =>
    (G i).integral (W.W i) (hcoord i) ω - (G' i).integral (W.W i) (hcoord i) ω with hD
  have hD2 : ∀ i, MemLp (D i) 2 P := fun i =>
    (HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)).sub
      (HorizonIntegrand.memLp (W.W i) (hcoord i) (G' i))
  have hDint : ∀ i, Integrable (D i) P := fun i => (hD2 i).integrable (by norm_num)
  -- the sum of the differences is `ℱ₀`-measurable, hence zero
  have hsum : (fun ω => ∑ i, D i ω) =ᵐ[P] fun ω => η' ω - η ω := by
    filter_upwards [h] with ω e
    simp only [hD, Finset.sum_sub_distrib]
    change vectorIntegral W hcoord G ω - vectorIntegral W hcoord G' ω = _
    linarith
  have hsumm : AEStronglyMeasurable[ℱ 0] (fun ω => ∑ i, D i ω) P :=
    (hη'm.sub hηm).congr hsum.symm
  have hsum0 : (fun ω => ∑ i, D i ω) =ᵐ[P] 0 := by
    refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite' (ℱ.le 0)
      (fun s _ _ => (integrable_finsetSum _ fun i _ => hDint i).integrableOn)
      (fun s _ _ => integrableOn_zero) (fun A hA _ => ?_) hsumm
      (stronglyMeasurable_zero.aestronglyMeasurable)
    rw [Pi.zero_def, integral_zero, integral_finsetSum _ fun i _ => (hDint i).integrableOn]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hD, integral_sub
      ((HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)).integrable (by norm_num)).integrableOn
      ((HorizonIntegrand.memLp (W.W i) (hcoord i) (G' i)).integrable (by norm_num)).integrableOn,
      HorizonIntegrand.setIntegral_integral_eq_zero (W.W i) (hcoord i) hT (G i) hA,
      HorizonIntegrand.setIntegral_integral_eq_zero (W.W i) (hcoord i) hT (G' i) hA, sub_zero]
  refine ⟨?_, fun i => ?_⟩
  · filter_upwards [hsum, hsum0] with ω e1 e2
    rw [Pi.zero_apply] at e2
    linarith
  -- each difference is an Itô integral, and distinct coordinates are orthogonal
  set H : Fin d → HorizonIntegrand P ℱ T := fun j => (G j).add ((G' j).smul (-1)) with hH
  have hDH : ∀ j, D j =ᵐ[P] (H j).integral (W.W j) (hcoord j) := by
    intro j
    filter_upwards [HorizonIntegrand.integral_add (W.W j) (hcoord j) hT (G j) ((G' j).smul (-1)),
      HorizonIntegrand.integral_smul (W.W j) (hcoord j) hT (-1) (G' j)] with ω e1 e2
    rw [e1, e2, hD]
    ring
  have hcross : ∀ j, j ≠ i → ∫ ω, D i ω * D j ω ∂P = 0 := by
    intro j hji
    rw [show (fun ω => D i ω * D j ω) = D i * D j from rfl,
      integral_congr_ae ((hDH i).mul (hDH j))]
    exact integral_stochasticIntegral_mul_eq_zero W hji.symm hcoord (H i).measurable_uncurry
      (H i).progressive (H i).sq_int_global (H j).measurable_uncurry (H j).progressive
      (H j).sq_int_global hT.le
  have hsq : ∫ ω, D i ω ^ 2 ∂P = 0 := by
    have h1 : ∫ ω, D i ω * ∑ j, D j ω ∂P = 0 := by
      have hz : (fun ω => D i ω * ∑ j, D j ω) =ᵐ[P] fun _ => (0 : ℝ) := by
        filter_upwards [hsum0] with ω e
        simp only [Pi.zero_apply] at e
        rw [e, mul_zero]
      rw [integral_congr_ae hz, integral_zero]
    rw [integral_congr_ae (Eventually.of_forall fun ω => Finset.mul_sum _ _ _),
      integral_finsetSum (f := fun j ω => D i ω * D j ω) _
        fun j _ => (hD2 i).integrable_mul (hD2 j),
      Finset.sum_eq_single i (fun j _ hji => hcross j hji) (by simp)] at h1
    rw [← h1]
    exact integral_congr_ae (Eventually.of_forall fun ω => sq (D i ω))
  have hDi0 : D i =ᵐ[P] 0 := by
    have hnn : 0 ≤ᵐ[P] fun ω => D i ω ^ 2 := Eventually.of_forall fun ω => sq_nonneg _
    have hint : Integrable (fun ω => D i ω ^ 2) P := (hD2 i).integrable_sq
    filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hnn hint).mp hsq] with ω e
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp e
  have henergy : energy P T (fun ω s => (G i).toFun ω s - (G' i).toFun ω s) = 0 := by
    rw [← HorizonIntegrand.lintegral_sq_integral_sub (W.W i) (hcoord i) hT (G i) (G' i)]
    refine (lintegral_congr_ae (hDi0.mono fun ω e => ?_)).trans (lintegral_zero)
    change (‖D i ω‖₊ : ℝ≥0∞) ^ 2 = 0
    rw [e]
    simp
  have hm : Measurable (Function.uncurry fun ω s => (G i).toFun ω s - (G' i).toFun ω s) :=
    (G i).measurable_uncurry.sub (G' i).measurable_uncurry
  rw [energy_eq_eLpNorm_sq hm T, pow_eq_zero_iff (by norm_num),
    eLpNorm_eq_zero_iff
      (f := fun p : Ω × ℝ => (G i).toFun p.1 p.2 - (G' i).toFun p.1 p.2)
      hm.aestronglyMeasurable (by norm_num)] at henergy
  filter_upwards [henergy] with p e
  exact sub_eq_zero.mp e

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
