/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.CrossOrthogonality
import LevyStochCalc.Brownian.PRPMultidimRange

/-!
# The joint range of a Lévy driver

The `L²` ranges of the `d` coordinate Itô integrals and of the compensated integral are pairwise
orthogonal and each closed, so their sum is closed and a square-integrable weight splits into a
part in the sum and a part orthogonal to it. The orthogonal part is a weight of mean zero,
measurable before the horizon, orthogonal to both ranges; when only the zero weight is such, the
weight is a joint integral.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open Brownian.Ito Brownian.Multidim.MultidimBrownianMotion Poisson.Compensated

section Range

variable {D : LevyDriver.{u, v, w} P d ν} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {T : ℝ}
  (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (D.W.W k) ℱ)
  (hℱN : Poisson.IsPoissonFiltration D.N ℱ)

/-- The `L²` ranges of the coordinate Itô integrals and of the compensated integral. -/
noncomputable def jointRange (hT : 0 < T) : Option (Fin d) → Submodule ℝ (Lp ℝ 2 P)
  | none => compensatedRange D.N hℱN hT
  | some i => itoRange (D.W.W i) (hcoord i) hT

/-- An Itô integral against a coordinate is orthogonal to a compensated integral in `L²`. -/
theorem inner_itoRange_compensatedRange (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T)
    (i : Fin d) (u : itoRange (D.W.W i) (hcoord i) hT) (v : compensatedRange D.N hℱN hT) :
    (inner ℝ (u : Lp ℝ 2 P) (v : Lp ℝ 2 P) : ℝ) = 0 := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  obtain ⟨G, hG⟩ := u.2
  obtain ⟨K, hK⟩ := v.2
  have hcross : ∫ ω, G.integral (D.W.W i) (hcoord i) ω * K.integral D.N hℱN ω ∂P = 0 :=
    integral_stochasticIntegral_mul_compensated_eq_zero 𝒲 hcoord hℱN G.measurable_uncurry
      G.progressive G.sq_int_global K.measurable_uncurry K.progressive K.sq_int_global hT.le
  rw [MeasureTheory.L2.inner_def, ← hcross]
  refine integral_congr_ae ?_
  filter_upwards [hG, hK] with ω e1 e2
  rw [RCLike.inner_apply, e1, e2]
  simp [mul_comm]

/-- The two ranges and the coordinate ranges form an orthogonal family. -/
theorem orthogonalFamily_jointRange (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T) :
    OrthogonalFamily ℝ (fun i => (jointRange hcoord hℱN hT i : Submodule ℝ (Lp ℝ 2 P)))
      (fun i => (jointRange hcoord hℱN hT i).subtypeₗᵢ) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  intro i j hij u v
  match i, j, u, v with
  | some i, some j, u, v =>
      exact orthogonalFamily_itoRange D.W hcoord hT (fun h => hij (by rw [h])) u v
  | some i, none, u, v => exact inner_itoRange_compensatedRange hcoord hℱN 𝒲 hT i u v
  | none, some j, u, v =>
      rw [real_inner_comm]
      exact inner_itoRange_compensatedRange hcoord hℱN 𝒲 hT j v u
  | none, none, _, _ => exact absurd rfl hij

/-- The joint range is closed in `L²`. -/
theorem isClosed_iSup_jointRange (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T) :
    IsClosed ((⨆ i : Option (Fin d), jointRange hcoord hℱN hT i :
      Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  haveI : ∀ i : Option (Fin d), CompleteSpace (jointRange hcoord hℱN hT i) := by
    intro i
    match i with
    | some i => exact (isClosed_itoRange (D.W.W i) (hcoord i) hT).completeSpace_coe
    | none => exact (isClosed_compensatedRange D.N hℱN hT).completeSpace_coe
  exact isClosed_iSup_of_orthogonalFamily (orthogonalFamily_jointRange hcoord hℱN 𝒲 hT)

/-- The joint integral of coordinate integrands and a marked integrand. -/
noncomputable def jointIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) : Ω → ℝ :=
  fun ω => vectorIntegral D.W hcoord G ω + K.integral D.N hℱN ω

theorem memLp_jointIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) : MemLp (jointIntegral hcoord hℱN G K) 2 P :=
  (memLp_vectorIntegral D.W hcoord G).add (MarkedHorizonIntegrand.memLp D.N hℱN K)

theorem integral_jointIntegral_eq_zero (hT : 0 ≤ T)
    (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) (K : MarkedHorizonIntegrand P ν ℱ T) :
    ∫ ω, jointIntegral hcoord hℱN G K ω ∂P = 0 := by
  have hrw : jointIntegral hcoord hℱN G K
      = fun ω => vectorIntegral D.W hcoord G ω + K.integral D.N hℱN ω := rfl
  rw [hrw, integral_add ((memLp_vectorIntegral D.W hcoord G).integrable (by norm_num))
      ((MarkedHorizonIntegrand.memLp D.N hℱN K).integrable (by norm_num)),
    integral_vectorIntegral_eq_zero D.W hcoord hT G,
    MarkedHorizonIntegrand.integral_mean_zero D.N hℱN hT K, add_zero]

theorem aestronglyMeasurable_jointIntegral (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T)
    (K : MarkedHorizonIntegrand P ν ℱ T) :
    AEStronglyMeasurable[ℱ T] (jointIntegral hcoord hℱN G K) P :=
  (aestronglyMeasurable_vectorIntegral D.W hcoord G).add
    (MarkedHorizonIntegrand.aestronglyMeasurable D.N hℱN K)

/-- **The representation half of the joint predictable representation property.** If the only
square-integrable weight of mean zero, measurable before `T` and orthogonal to every coordinate
Itô integral and to every compensated integral, is the zero weight, then every square-integrable
weight of mean zero that is measurable before `T` is a joint integral. -/
theorem exists_jointIntegral_of_mean_zero (𝒲 : LevyDriver.CrossWitness D ℱ) (hT : 0 < T)
    (hsep : ∀ r : Ω → ℝ, MemLp r 2 P → AEStronglyMeasurable[ℱ T] r P → (∫ ω, r ω ∂P = 0) →
      (∀ (i : Fin d) (G : HorizonIntegrand P ℱ T),
        ∫ ω, r ω * G.integral (D.W.W i) (hcoord i) ω ∂P = 0) →
      (∀ K : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, r ω * K.integral D.N hℱN ω ∂P = 0) →
      r =ᵐ[P] 0)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    ∃ (G : ∀ _ : Fin d, HorizonIntegrand P ℱ T) (K : MarkedHorizonIntegrand P ν ℱ T),
      Z =ᵐ[P] jointIntegral hcoord hℱN G K := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set V : Option (Fin d) → Submodule ℝ (Lp ℝ 2 P) := jointRange hcoord hℱN hT with hVdef
  haveI hcl : IsClosed ((⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) : Set (Lp ℝ 2 P)) :=
    isClosed_iSup_jointRange hcoord hℱN 𝒲 hT
  haveI : CompleteSpace (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) := hcl.completeSpace_coe
  haveI : ∀ i : Option (Fin d), CompleteSpace (V i) := by
    intro i
    match i with
    | some i => exact (isClosed_itoRange (D.W.W i) (hcoord i) hT).completeSpace_coe
    | none => exact (isClosed_compensatedRange D.N hℱN hT).completeSpace_coe
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)).exists_add_mem_mem_orthogonal (hZ2.toLp Z)
  have hproj : ∑ i, (V i).starProjection y = y :=
    (orthogonalFamily_jointRange hcoord hℱN 𝒲 hT).sum_projection_of_mem_iSup y hy
  have hcompB : ∀ i : Fin d, ∃ G : HorizonIntegrand P ℱ T,
      (((V (some i)).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] G.integral (D.W.W i) (hcoord i) :=
    fun i => (V (some i)).starProjection_apply_mem y
  choose G hG using hcompB
  obtain ⟨K, hK⟩ : ∃ K : MarkedHorizonIntegrand P ν ℱ T,
      (((V none).starProjection y : Lp ℝ 2 P) : Ω → ℝ) =ᵐ[P] K.integral D.N hℱN :=
    (V none).starProjection_apply_mem y
  have hyfun : (y : Ω → ℝ) =ᵐ[P] jointIntegral hcoord hℱN G K := by
    have hsumfun : ((∑ i, (V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ)
        =ᵐ[P] fun ω => ∑ i : Option (Fin d),
          (((V i).starProjection y : Lp ℝ 2 P) : Ω → ℝ) ω :=
      MeasureTheory.Lp.coeFn_fun_finsetSum _ _
    rw [← hproj]
    filter_upwards [hsumfun, hK, Filter.eventually_all.2 (fun i : Fin d => hG i)]
      with ω e1 e2 e3
    rw [e1, Fintype.sum_option, e2, jointIntegral, vectorIntegral, add_comm]
    exact congrArg (fun x => x + K.integral D.N hℱN ω) (Finset.sum_congr rfl fun i _ => e3 i)
  have hsplit : Z =ᵐ[P] fun ω => jointIntegral hcoord hℱN G K ω + (z : Ω → ℝ) ω := by
    filter_upwards [hZ2.coeFn_toLp, Lp.coeFn_add y z, hyfun] with ω e1 e2 e3
    rw [← e1, hyz, e2, Pi.add_apply, e3]
  have hzmem : MemLp (z : Ω → ℝ) 2 P := Lp.memLp z
  have hzmeas : AEStronglyMeasurable[ℱ T] (z : Ω → ℝ) P := by
    have hd : (z : Ω → ℝ) =ᵐ[P] fun ω => Z ω - jointIntegral hcoord hℱN G K ω := by
      filter_upwards [hsplit] with ω e1
      rw [e1]; ring
    exact (hZm.sub (aestronglyMeasurable_jointIntegral hcoord hℱN G K)).congr hd.symm
  have hyint : Integrable (jointIntegral hcoord hℱN G K) P :=
    (memLp_jointIntegral hcoord hℱN G K).integrable (by norm_num)
  have hzint : Integrable (z : Ω → ℝ) P := hzmem.integrable (by norm_num)
  have hzmean : ∫ ω, (z : Ω → ℝ) ω ∂P = 0 := by
    have hone := integral_congr_ae (μ := P) hsplit
    rw [integral_add hyint hzint, integral_jointIntegral_eq_zero hcoord hℱN hT.le G K,
      zero_add] at hone
    rw [← hone, hZ0]
  have hzperpB : ∀ (i : Fin d) (L : HorizonIntegrand P ℱ T),
      ∫ ω, (z : Ω → ℝ) ω * L.integral (D.W.W i) (hcoord i) ω ∂P = 0 := by
    intro i L
    have hmem : (HorizonIntegrand.memLp (D.W.W i) (hcoord i) L).toLp
        (L.integral (D.W.W i) (hcoord i)) ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem (some i) ⟨L, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp
      (HorizonIntegrand.memLp (D.W.W i) (hcoord i) L)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzperpN : ∀ L : MarkedHorizonIntegrand P ν ℱ T,
      ∫ ω, (z : Ω → ℝ) ω * L.integral D.N hℱN ω ∂P = 0 := by
    intro L
    have hmem : (MarkedHorizonIntegrand.memLp D.N hℱN L).toLp (L.integral D.N hℱN)
        ∈ (⨆ i, V i : Submodule ℝ (Lp ℝ 2 P)) :=
      Submodule.mem_iSup_of_mem none ⟨L, MemLp.coeFn_toLp _⟩
    have hinner := (Submodule.mem_orthogonal _ z).mp hz _ hmem
    rw [MeasureTheory.L2.inner_def] at hinner
    rw [← hinner]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp (MarkedHorizonIntegrand.memLp D.N hℱN L)] with ω e1
    rw [RCLike.inner_apply, e1]
    simp
  have hzzero := hsep (z : Ω → ℝ) hzmem hzmeas hzmean hzperpB hzperpN
  refine ⟨G, K, ?_⟩
  filter_upwards [hsplit, hzzero] with ω e1 e2
  rw [e1, e2]
  simp

end Range

end LevyDriver

end LevyStochCalc.Driver
