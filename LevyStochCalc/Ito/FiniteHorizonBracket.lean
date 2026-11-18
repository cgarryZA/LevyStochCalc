/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.FiniteHorizonEnergy

/-!
# The expected product of two Itô processes with their bracket

Two processes `M`, `N` on `[0, T]` with values in a real inner product space `E` satisfy the
polarised isometry with integrands `H`, `K` (values in a real inner product space `F`, for
instance matrices with the Frobenius pairing) when `H` and `K` are square integrable for
`P ⊗ ds` on `[0, T]` and `𝔼⟪M_t, N_t⟫ = 𝔼 ∫_0^t ⟪H_s, K_s⟫ ds` for `t ∈ [0, T]`
(`HasPolarisedIsometryOn`). The `L²` stochastic integrals `M = ∫ H dW`, `N = ∫ K dW` against one
Brownian motion do.

For Itô processes `X = X₀ + ∫ a ds + M`, `Y = Y₀ + ∫ b ds + N` on `[0, T]` it follows that

`𝔼⟪X_t, Y_t⟫ = 𝔼⟪X₀, Y₀⟫ + ∫_0^t 𝔼(⟪a_s, Y_s⟫ + ⟪X_s, b_s⟫) ds + 𝔼 ∫_0^t ⟪H_s, K_s⟫ ds`,

together with the forms that are short corollaries: the pairing `⟪G X, Y⟫` through a continuous
linear map `G` (a rectangular matrix), the energy identity
`𝔼‖X_t‖² = 𝔼‖X₀‖² + 2 ∫_0^t 𝔼⟪X_s, a_s⟫ ds + 𝔼 ∫_0^t ‖H_s‖² ds`, and the identity over a window
`[s, t] ⊆ [0, T]`. The polarised isometry is invariant under `P ⊗ ds`-null changes of the
integrands.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

variable {Ω E E' F : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [CompleteSpace E']
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The processes `M` and `N` satisfy the polarised isometry on `[0, T]` with the integrands `H`
and `K`: these are square integrable for `P ⊗ ds` on `[0, T]` and
`𝔼⟪M_t, N_t⟫ = 𝔼 ∫_0^t ⟪H_s, K_s⟫ ds` for every `t ∈ [0, T]`. -/
structure HasPolarisedIsometryOn (P : Measure Ω) (T : ℝ) (M N : ℝ → Ω → E)
    (H K : ℝ → Ω → F) : Prop where
  integrand_left :
    MemLp (fun p : Ω × ℝ => H p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
  integrand_right :
    MemLp (fun p : Ω × ℝ => K p.2 p.1) 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
  isometry : ∀ t, 0 ≤ t → t ≤ T →
    ∫ ω, ⟪M t ω, N t ω⟫ ∂P = ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, ⟪H s ω, K s ω⟫ ∂volume ∂P

namespace HasPolarisedIsometryOn

variable {T : ℝ} {M N : ℝ → Ω → E} {H K : ℝ → Ω → F}

omit [CompleteSpace E] in
/-- The pairing of the two integrands is integrable for `P ⊗ ds` on `[0, T]`. -/
theorem integrable_inner (h : HasPolarisedIsometryOn P T M N H K) :
    Integrable (fun p : Ω × ℝ => ⟪H p.2 p.1, K p.2 p.1⟫)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
  integrable_inner_of_memLp h.integrand_left h.integrand_right

omit [CompleteSpace E] in
/-- **Almost-everywhere invariance in the integrands.** The polarised isometry is kept when the
integrands are changed on `P ⊗ ds`-null subsets of `Ω × [0, T]`. -/
theorem congr (h : HasPolarisedIsometryOn P T M N H K) {H' K' : ℝ → Ω → F}
    (hH : (fun p : Ω × ℝ => H p.2 p.1)
      =ᵐ[P.prod (volume.restrict (Set.Icc (0 : ℝ) T))] fun p => H' p.2 p.1)
    (hK : (fun p : Ω × ℝ => K p.2 p.1)
      =ᵐ[P.prod (volume.restrict (Set.Icc (0 : ℝ) T))] fun p => K' p.2 p.1) :
    HasPolarisedIsometryOn P T M N H' K' where
  integrand_left := h.integrand_left.ae_eq hH
  integrand_right := h.integrand_right.ae_eq hK
  isometry t ht0 htT := by
    rw [h.isometry t ht0 htT]
    refine integral_congr_ae ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hH, Measure.ae_ae_of_ae_prod hK] with ω hω hω'
    refine integral_congr_ae ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl htT) hω,
      ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl htT) hω'] with s hs hs'
    rw [show H s ω = H' s ω from hs, show K s ω = K' s ω from hs']

end HasPolarisedIsometryOn

variable [IsFiniteMeasure P] {ℱ : Filtration ℝ m0} {T : ℝ} {X a M : ℝ → Ω → E}
  {X₀ : Ω → E} {H K : ℝ → Ω → F}

/-- **The expected product of two Itô processes on a finite horizon, with their bracket.** For
square-integrable Itô processes `X = X₀ + ∫ a ds + M` and `Y = Y₀ + ∫ b ds + N` on `[0, T]` for
one filtration whose martingale parts satisfy the polarised isometry with integrands `H`, `K`,
and `t ∈ [0, T]`,

`𝔼⟪X_t, Y_t⟫ = 𝔼⟪X₀, Y₀⟫ + ∫_0^t 𝔼(⟪a_s, Y_s⟫ + ⟪X_s, b_s⟫) ds + 𝔼 ∫_0^t ⟪H_s, K_s⟫ ds`. -/
theorem integral_inner_eq_add_bracket {Y b N : ℝ → Ω → E} {Y₀ : Ω → E}
    (hX : IsL2ItoProcessOn ℱ P T X X₀ a M) (hY : IsL2ItoProcessOn ℱ P T Y Y₀ b N)
    (hMN : HasPolarisedIsometryOn P T M N H K) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ ω, ⟪X t ω, Y t ω⟫ ∂P
      = ∫ ω, ⟪X₀ ω, Y₀ ω⟫ ∂P
        + (∫ s in Set.Icc (0 : ℝ) t, ∫ ω, (⟪a s ω, Y s ω⟫ + ⟪X s ω, b s ω⟫) ∂P)
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, ⟪H s ω, K s ω⟫ ∂volume ∂P := by
  rw [integral_inner_eq hX hY ht0 htT, hMN.isometry t ht0 htT]

/-- **The pairing through a continuous linear map.** For Itô processes `X` in `E` and `Y` in
`E'` on `[0, T]` for one filtration, a continuous linear map `G : E →L[ℝ] E'` (a rectangular
matrix), and martingale parts with `G M` and `N` satisfying the polarised isometry with integrands
`H`, `K`,

`𝔼⟪G X_t, Y_t⟫ = 𝔼⟪G X₀, Y₀⟫ + ∫_0^t 𝔼(⟪G a_s, Y_s⟫ + ⟪G X_s, b_s⟫) ds
  + 𝔼 ∫_0^t ⟪H_s, K_s⟫ ds`. -/
theorem integral_inner_map_eq_add_bracket (G : E →L[ℝ] E') {Y b N : ℝ → Ω → E'} {Y₀ : Ω → E'}
    (hX : IsL2ItoProcessOn ℱ P T X X₀ a M) (hY : IsL2ItoProcessOn ℱ P T Y Y₀ b N)
    (hMN : HasPolarisedIsometryOn P T (fun t ω => G (M t ω)) N H K) {t : ℝ} (ht0 : 0 ≤ t)
    (htT : t ≤ T) :
    ∫ ω, ⟪G (X t ω), Y t ω⟫ ∂P
      = ∫ ω, ⟪G (X₀ ω), Y₀ ω⟫ ∂P
        + (∫ s in Set.Icc (0 : ℝ) t, ∫ ω, (⟪G (a s ω), Y s ω⟫ + ⟪G (X s ω), b s ω⟫) ∂P)
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, ⟪H s ω, K s ω⟫ ∂volume ∂P :=
  integral_inner_eq_add_bracket (hX.map G) hY hMN ht0 htT

omit [CompleteSpace E] [IsFiniteMeasure P] in
/-- The rate of the energy of an Itô process is twice the expected pairing with the drift. -/
theorem integral_inner_add_inner_eq (s : ℝ) :
    ∫ ω, (⟪a s ω, X s ω⟫ + ⟪X s ω, a s ω⟫) ∂P = 2 * ∫ ω, ⟪X s ω, a s ω⟫ ∂P := by
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
  change ⟪a s ω, X s ω⟫ + ⟪X s ω, a s ω⟫ = 2 * ⟪X s ω, a s ω⟫
  rw [real_inner_comm (X s ω) (a s ω)]
  ring

/-- **The energy identity on a finite horizon.** For a square-integrable Itô process
`X = X₀ + ∫ a ds + M` on `[0, T]` whose martingale part satisfies the isometry
`𝔼‖M_t‖² = 𝔼 ∫_0^t ‖H_s‖² ds`, and `t ∈ [0, T]`,

`𝔼‖X_t‖² = 𝔼‖X₀‖² + 2 ∫_0^t 𝔼⟪X_s, a_s⟫ ds + 𝔼 ∫_0^t ‖H_s‖² ds`. -/
theorem integral_norm_sq_eq (hX : IsL2ItoProcessOn ℱ P T X X₀ a M)
    (hM : HasPolarisedIsometryOn P T M M H H) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ ω, ‖X t ω‖ ^ 2 ∂P
      = ∫ ω, ‖X₀ ω‖ ^ 2 ∂P + 2 * (∫ s in Set.Icc (0 : ℝ) t, ∫ ω, ⟪X s ω, a s ω⟫ ∂P)
        + ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, ‖H s ω‖ ^ 2 ∂volume ∂P := by
  have h := integral_inner_eq_add_bracket hX hX hM ht0 htT
  simp only [real_inner_self_eq_norm_sq] at h
  rw [h, integral_congr_ae (Eventually.of_forall fun s => integral_inner_add_inner_eq s),
    integral_const_mul]

/-- **The expected product over a window.** For two Itô processes on `[0, T]` whose martingale
parts satisfy the polarised isometry with integrands `H`, `K`, and `0 ≤ s ≤ t ≤ T`,

`𝔼⟪X_t, Y_t⟫ - 𝔼⟪X_s, Y_s⟫ = ∫_s^t 𝔼(⟪a_r, Y_r⟫ + ⟪X_r, b_r⟫) dr + 𝔼 ∫_s^t ⟪H_r, K_r⟫ dr`. -/
theorem integral_inner_sub_eq {Y b N : ℝ → Ω → E} {Y₀ : Ω → E}
    (hX : IsL2ItoProcessOn ℱ P T X X₀ a M) (hY : IsL2ItoProcessOn ℱ P T Y Y₀ b N)
    (hMN : HasPolarisedIsometryOn P T M N H K) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htT : t ≤ T) :
    ∫ ω, ⟪X t ω, Y t ω⟫ ∂P - ∫ ω, ⟪X s ω, Y s ω⟫ ∂P
      = (∫ r in Set.Ioc s t, ∫ ω, (⟪a r ω, Y r ω⟫ + ⟪X r ω, b r ω⟫) ∂P)
        + ∫ ω, ∫ r in Set.Ioc s t, ⟪H r ω, K r ω⟫ ∂volume ∂P := by
  have hunion : Set.Icc (0 : ℝ) s ∪ Set.Ioc s t = Set.Icc (0 : ℝ) t :=
    Set.Icc_union_Ioc_eq_Icc hs hst
  have hdisj : Disjoint (Set.Icc (0 : ℝ) s) (Set.Ioc s t) :=
    Set.disjoint_left.2 fun x h1 h2 => absurd h1.2 (not_le.2 h2.1)
  have hsub1 : Set.Icc (0 : ℝ) s ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc le_rfl (hst.trans htT)
  have hsub2 : Set.Ioc s t ⊆ Set.Icc (0 : ℝ) T := fun x hx =>
    ⟨hs.trans hx.1.le, hx.2.trans htT⟩
  -- the rate
  have hrate := integrableOn_rate hX hY (hs.trans hst) htT
  have hR : (∫ r in Set.Icc (0 : ℝ) t, ∫ ω, (⟪a r ω, Y r ω⟫ + ⟪X r ω, b r ω⟫) ∂P)
      = (∫ r in Set.Icc (0 : ℝ) s, ∫ ω, (⟪a r ω, Y r ω⟫ + ⟪X r ω, b r ω⟫) ∂P)
        + ∫ r in Set.Ioc s t, ∫ ω, (⟪a r ω, Y r ω⟫ + ⟪X r ω, b r ω⟫) ∂P := by
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioc
      (hrate.mono_set (Set.Icc_subset_Icc le_rfl hst))
      (hrate.mono_set fun x hx => ⟨hs.trans hx.1.le, hx.2⟩)
  -- the bracket
  have hint := hMN.integrable_inner
  have hint1 : Integrable (fun p : Ω × ℝ => ⟪H p.2 p.1, K p.2 p.1⟫)
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) s))) :=
    hint.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono hsub1 le_rfl))
  have hint2 : Integrable (fun p : Ω × ℝ => ⟪H p.2 p.1, K p.2 p.1⟫)
      (P.prod (volume.restrict (Set.Ioc s t))) :=
    hint.mono_measure (Measure.prod_mono le_rfl (Measure.restrict_mono hsub2 le_rfl))
  have hB : ∫ ω, ∫ r in Set.Icc (0 : ℝ) t, ⟪H r ω, K r ω⟫ ∂volume ∂P
      = ∫ ω, ∫ r in Set.Icc (0 : ℝ) s, ⟪H r ω, K r ω⟫ ∂volume ∂P
        + ∫ ω, ∫ r in Set.Ioc s t, ⟪H r ω, K r ω⟫ ∂volume ∂P := by
    rw [← integral_add hint1.integral_prod_left hint2.integral_prod_left]
    refine integral_congr_ae ?_
    filter_upwards [hint.prod_right_ae] with ω hω
    rw [← hunion]
    exact setIntegral_union hdisj measurableSet_Ioc (IntegrableOn.mono_set hω hsub1)
      (IntegrableOn.mono_set hω hsub2)
  rw [integral_inner_eq_add_bracket hX hY hMN (hs.trans hst) htT,
    integral_inner_eq_add_bracket hX hY hMN hs (hst.trans htT), hR, hB]
  ring

end LevyStochCalc.Ito.FiniteHorizon
