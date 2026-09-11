/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoRange
import LevyStochCalc.Brownian.CrossOrthogonality

/-!
# The closed range of the multidimensional Brownian Itô integral

The multidimensional Itô integral is the sum over the coordinates of the scalar integrals, so its
range in `L²` is the supremum of the scalar ranges. Those are closed, and orthogonal to one
another, so the supremum is closed: a point of its closure is the sum of its orthogonal
projections, each of which lies in the corresponding scalar range. The orthogonal decomposition
along the supremum then represents every square-integrable weight of mean zero, measurable before
the horizon, as a sum of coordinate Itô integrals, given the separation hypothesis.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion

open LevyStochCalc.Brownian.Ito

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ}

/-- A finite orthogonal family of complete submodules has closed supremum. -/
theorem isClosed_iSup_of_orthogonalFamily {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] {ι : Type*} [Finite ι] {V : ι → Submodule 𝕜 E}
    [∀ i, CompleteSpace (V i)]
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    IsClosed ((⨆ i, V i : Submodule 𝕜 E) : Set E) := by
  cases nonempty_fintype ι
  refine IsSeqClosed.isClosed fun f x hf hx => ?_
  have hsum : ∀ n, ∑ i, (V i).starProjection (f n) = f n :=
    fun n => hV.sum_projection_of_mem_iSup (f n) (hf n)
  have hlim : Tendsto (fun n => ∑ i, (V i).starProjection (f n)) atTop
      (𝓝 (∑ i, (V i).starProjection x)) :=
    tendsto_finsetSum _ fun i _ => ((V i).starProjection.continuous.tendsto x).comp hx
  have hxeq : x = ∑ i, (V i).starProjection x := by
    refine tendsto_nhds_unique ?_ hlim
    simpa only [hsum] using hx
  rw [SetLike.mem_coe, hxeq]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.mem_iSup_of_mem i ((V i).starProjection_apply_mem x)

section Range

variable (W : MultidimBrownianMotion P d) {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

/-- The `L²` ranges of the Itô integrals against distinct coordinates are orthogonal. -/
theorem orthogonalFamily_itoRange (hT : 0 < T) :
    OrthogonalFamily ℝ
      (fun i : Fin d => (itoRange (W.W i) (hcoord i) hT : Submodule ℝ (Lp ℝ 2 P)))
      (fun i => (itoRange (W.W i) (hcoord i) hT).subtypeₗᵢ) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  intro i j hij u v
  obtain ⟨G, hG⟩ := u.2
  obtain ⟨K, hK⟩ := v.2
  have hcross : ∫ ω, G.integral (W.W i) (hcoord i) ω * K.integral (W.W j) (hcoord j) ω ∂P = 0 :=
    integral_stochasticIntegral_mul_eq_zero W hij hcoord G.measurable_uncurry G.progressive
      G.sq_int_global K.measurable_uncurry K.progressive K.sq_int_global hT.le
  change (inner ℝ ((u : Lp ℝ 2 P)) ((v : Lp ℝ 2 P)) : ℝ) = 0
  rw [MeasureTheory.L2.inner_def, ← hcross]
  refine integral_congr_ae ?_
  filter_upwards [hG, hK] with ω e1 e2
  rw [RCLike.inner_apply, e1, e2]
  simp [mul_comm]

/-- The range of the multidimensional Itô integral is closed in `L²`. -/
theorem isClosed_iSup_itoRange (hT : 0 < T) :
    IsClosed ((⨆ i : Fin d, itoRange (W.W i) (hcoord i) hT :
      Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI : ∀ i : Fin d, CompleteSpace (itoRange (W.W i) (hcoord i) hT) := fun i =>
    (isClosed_itoRange (W.W i) (hcoord i) hT).completeSpace_coe
  exact isClosed_iSup_of_orthogonalFamily (orthogonalFamily_itoRange W hcoord hT)

/-- The multidimensional Itô integral of a family of admissible integrands. -/
noncomputable def vectorIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) : Ω → ℝ :=
  fun ω => ∑ i : Fin d, (G i).integral (W.W i) (hcoord i) ω

theorem memLp_vectorIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) :
    MemLp (vectorIntegral W hcoord G) 2 P :=
  memLp_finsetSum (f := fun (i : Fin d) ω => (G i).integral (W.W i) (hcoord i) ω) Finset.univ
    fun i _ => HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)

theorem integral_vectorIntegral_eq_zero (hT : 0 ≤ T)
    (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) :
    ∫ ω, vectorIntegral W hcoord G ω ∂P = 0 := by
  have hrw : vectorIntegral W hcoord G
      = fun ω => ∑ i : Fin d, (G i).integral (W.W i) (hcoord i) ω := rfl
  rw [hrw, integral_finsetSum _ fun i _ =>
    (HorizonIntegrand.memLp (W.W i) (hcoord i) (G i)).integrable (by norm_num)]
  exact Finset.sum_eq_zero fun i _ =>
    HorizonIntegrand.integral_mean_zero (W.W i) (hcoord i) hT (G i)

theorem aestronglyMeasurable_vectorIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) :
    AEStronglyMeasurable[ℱ T] (vectorIntegral W hcoord G) P := by
  set F : Fin d → Ω → ℝ := fun i => (G i).integral (W.W i) (hcoord i) with hF
  have hcomp : ∀ i : Fin d, AEStronglyMeasurable[ℱ T] (F i) P := fun i =>
    HorizonIntegrand.aestronglyMeasurable (W.W i) (hcoord i) (G i)
  have key : ∀ s : Finset (Fin d),
      AEStronglyMeasurable[ℱ T] (fun ω => ∑ i ∈ s, F i ω) P := by
    intro s
    induction s using Finset.cons_induction with
    | empty =>
      refine ⟨fun _ => 0, stronglyMeasurable_const, ?_⟩
      filter_upwards with ω
      simp
    | cons i s hi ih =>
      have hsum : (fun ω => ∑ j ∈ Finset.cons i s hi, F j ω)
          = fun ω => F i ω + ∑ j ∈ s, F j ω := by
        funext ω
        rw [Finset.sum_cons]
      rw [hsum]
      exact (hcomp i).add ih
  have hgoal : vectorIntegral W hcoord G
      = fun ω => ∑ i ∈ (Finset.univ : Finset (Fin d)), F i ω := rfl
  rw [hgoal]
  exact key Finset.univ

/-- **The representation half of the multidimensional Brownian predictable representation
property.** If the only square-integrable weight of mean zero, measurable before `T` and
orthogonal to every coordinate Itô integral, is the zero weight, then every square-integrable
weight of mean zero that is measurable before `T` is a multidimensional Itô integral. -/
theorem exists_vectorIntegral_of_mean_zero (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P →
      (∫ ω, r ω ∂P = 0) →
      (∀ (i : Fin d) (G : HorizonIntegrand P ℱ T),
        ∫ ω, r ω * G.integral (W.W i) (hcoord i) ω ∂P = 0) →
      r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[ℱ T] Z P) (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ G : ∀ _ : Fin d, HorizonIntegrand P ℱ T, Z =ᵐ[P] vectorIntegral W hcoord G := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set V : Fin d → Submodule ℝ (Lp ℝ 2 P) := fun i =>
    itoRange (W.W i) (hcoord i) hT with hVdef
  haveI hcl : IsClosed ((⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    isClosed_iSup_itoRange W hcoord hT
  haveI : CompleteSpace (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) := hcl.completeSpace_coe
  haveI : ∀ i : Fin d, CompleteSpace (V i) := fun i =>
    (isClosed_itoRange (W.W i) (hcoord i) hT).completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  -- decompose `y` along the coordinates
  have hproj : ∑ i, (V i).starProjection y = y :=
    (orthogonalFamily_itoRange W hcoord hT).sum_projection_of_mem_iSup y hy
  have hcomp : ∀ i : Fin d, ∃ G : HorizonIntegrand P ℱ T,
      (((V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] G.integral (W.W i) (hcoord i) :=
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
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P := by
    have hd : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - vectorIntegral W hcoord G ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    exact (hZm.sub (aestronglyMeasurable_vectorIntegral W hcoord G)).congr hd.symm
  have hyint : Integrable (vectorIntegral W hcoord G) P :=
    (memLp_vectorIntegral W hcoord G).integrable (by norm_num)
  have hzint : Integrable (z : Ω → ℝ) P := hzmem.integrable (by norm_num)
  have hzmean : ∫ ω, (z : Ω → ℝ) ω ∂P = 0 := by
    have hone := integral_congr_ae (μ := P) hsplit
    rw [integral_add hyint hzint, integral_vectorIntegral_eq_zero W hcoord hT.le G,
      zero_add] at hone
    rw [← hone, hZ0]
  have hzperp : ∀ (i : Fin d) (K : HorizonIntegrand P ℱ T),
      ∫ ω, (z : Ω → ℝ) ω * K.integral (W.W i) (hcoord i) ω ∂P = 0 := by
    intro i K
    have hmem : (HorizonIntegrand.memLp (W.W i) (hcoord i) K).toLp
        (K.integral (W.W i) (hcoord i))
        ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem i ⟨K, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp
      (HorizonIntegrand.memLp (W.W i) (hcoord i) K)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzzero := hsep (z : Ω → ℝ) hzmem hzmeas hzmean hzperp
  refine ⟨G, ?_⟩
  filter_upwards [hsplit, hzzero] with ω e1 e2
  rw [e1, e2]
  simp

end Range

end LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion
