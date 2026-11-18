/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.FiniteHorizonBracket
import LevyStochCalc.Brownian.VectorItoProcess
import LevyStochCalc.Brownian.CrossOrthogonalityLimit

/-!
# The Brownian Itô integral of a matrix integrand on a finite horizon

For a `d`-dimensional Brownian motion `W` on a filtration `ℱ` and a matrix integrand
`H = (H^{mk})` (jointly measurable, progressive, square integrable on every window), the Itô
integral `∫_0^t H_s dW_s` is the process in `EuclideanSpace ℝ (Fin n)` whose coordinate `m` is
`∑_k ∫_0^t H^{mk}_s dW^k_s` (`euclideanItoIntegral`). Writing the integrand as a function with
values in `EuclideanSpace ℝ (Fin n × Fin d)` (`euclideanMatrix`), whose inner product is the
Frobenius pairing `⟪H, K⟫ = ∑_{m,k} H^{mk} K^{mk}`, it has

* orthogonal increments on every window `[0, T]`
  (`hasOrthogonalIncrementsOn_euclideanItoIntegral`), and
* for two integrands `H`, `K`, the polarised isometry
  `𝔼⟪∫_0^t H dW, ∫_0^t K dW⟫ = 𝔼 ∫_0^t ⟪H_s, K_s⟫ ds`
  (`hasPolarisedIsometryOn_euclideanItoIntegral`),

so it is a martingale part to which the finite-horizon expected product identities apply.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}
  (W : Multidim.MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

section Definitions

/-- The Itô integral `∫_0^t H_s dW_s` of a matrix integrand against a `d`-dimensional Brownian
motion, as a process in `EuclideanSpace ℝ (Fin n)`: its coordinate `m` is
`∑_k ∫_0^t H^{mk}_s dW^k_s`. -/
noncomputable def euclideanItoIntegral (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
    (hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k))
    (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (t : ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 fun m => vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t ω

variable {W ℱ hcoord}

/-- A matrix integrand as a function with values in `EuclideanSpace ℝ (Fin n × Fin d)`, whose
inner product is the Frobenius pairing. -/
def euclideanMatrix (H : Fin n → Fin d → Ω → ℝ → ℝ) (s : ℝ) (ω : Ω) :
    EuclideanSpace ℝ (Fin n × Fin d) :=
  WithLp.toLp 2 fun p => H p.1 p.2 ω s

omit [MeasurableSpace Ω] in
/-- The pairing of two matrix integrands is the Frobenius pairing of their entries. -/
theorem inner_euclideanMatrix (H K : Fin n → Fin d → Ω → ℝ → ℝ) (s : ℝ) (ω : Ω) :
    ⟪euclideanMatrix H s ω, euclideanMatrix K s ω⟫ = ∑ m, ∑ k, H m k ω s * K m k ω s := by
  simp only [euclideanMatrix, PiLp.inner_apply, Real.inner_apply, Fintype.sum_prod_type]

omit [IsProbabilityMeasure P] in
/-- A window energy finite on every positive horizon is finite on every window. -/
theorem energy_lt_top_of_forall_pos {f : Ω → ℝ → ℝ}
    (hf : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (lintegral_mono fun _ => lintegral_mono_set
    (Set.Icc_subset_Icc le_rfl ((le_max_left T 0).trans (le_add_of_nonneg_right zero_le_one))))
    (hf (max T 0 + 1) (by positivity))

omit [IsProbabilityMeasure P] in
/-- A matrix integrand with entries square integrable on every window is square integrable for
the product measure on every window. -/
theorem memLp_euclideanMatrix {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ m k, Measurable (Function.uncurry (H m k)))
    (hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (T : ℝ) :
    MemLp (fun p : Ω × ℝ => euclideanMatrix H p.2 p.1) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) := by
  have h : MemLp (fun p : Ω × ℝ => fun q : Fin n × Fin d => H q.1 q.2 p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) :=
    memLp_pi_iff.2 fun q => LevyStochCalc.Ito.SecondMoment.memLp_two_prod (hHm q.1 q.2)
      (energy_lt_top_of_forall_pos (hHs q.1 q.2) T)
  exact (EuclideanSpace.equiv (Fin n × Fin d) ℝ).symm.toContinuousLinearMap.comp_memLp' h

end Definitions

variable {W ℱ hcoord} {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ m k, Measurable (Function.uncurry (H m k))}
  {hHp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (H m k)}
  {hHs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}

/-- The matrix Itô integral is square integrable at every time. -/
theorem memLp_euclideanItoIntegral (t : ℝ) :
    MemLp (euclideanItoIntegral W ℱ hcoord H hHm hHp hHs t) 2 P := by
  have h : MemLp (fun ω => fun m => vectorItoMartingale W ℱ hcoord H hHm hHp hHs m t ω) 2 P :=
    memLp_pi_iff.2 fun m => memLp_finsetSum Finset.univ fun k _ =>
      stochasticIntegralBrownian_memLp (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
        (hHs m k) t
  exact (EuclideanSpace.equiv (Fin n) ℝ).symm.toContinuousLinearMap.comp_memLp' h

/-- The matrix Itô integral vanishes at time zero. -/
theorem euclideanItoIntegral_ae_zero :
    euclideanItoIntegral W ℱ hcoord H hHm hHp hHs 0 =ᵐ[P] 0 := by
  have h : ∀ᵐ ω ∂P, ∀ m k, coordItoIntegral W ℱ hcoord H hHm hHp hHs m k 0 ω = 0 := by
    rw [ae_all_iff]
    intro m
    rw [ae_all_iff]
    intro k
    exact stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hcoord k) (H m k) (hHm m k)
      (hHp m k) (hHs m k) le_rfl
  filter_upwards [h] with ω hω
  ext m
  simp [euclideanItoIntegral, vectorItoMartingale, hω]

/-- The pairing of a variable with the matrix Itô integral, entry by entry. -/
theorem integral_inner_euclideanItoIntegral {ξ : Ω → EuclideanSpace ℝ (Fin n)}
    (hξ2 : MemLp ξ 2 P) (t : ℝ) :
    ∫ ω, ⟪ξ ω, euclideanItoIntegral W ℱ hcoord H hHm hHp hHs t ω⟫ ∂P
      = ∑ m, ∑ k, ∫ ω, ξ ω m * coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t ω ∂P := by
  have hξm : ∀ m, MemLp (fun ω => ξ ω m) 2 P := fun m =>
    (EuclideanSpace.proj (𝕜 := ℝ) m).comp_memLp' hξ2
  have hS : ∀ m k, MemLp (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) 2 P := fun m k =>
    stochasticIntegralBrownian_memLp (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k) (hHs m k) t
  have hexp : (fun ω => ⟪ξ ω, euclideanItoIntegral W ℱ hcoord H hHm hHp hHs t ω⟫)
      = fun ω => ∑ m, ∑ k, ξ ω m * coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t ω := by
    funext ω
    simp only [euclideanItoIntegral, PiLp.inner_apply, Real.inner_apply, vectorItoMartingale,
      Finset.mul_sum]
  have hint : ∀ m k, Integrable
      (fun ω => ξ ω m * coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t ω) P := fun m k =>
    (hξm m).integrable_mul (hS m k)
  rw [hexp, integral_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ => hint m k]
  exact Finset.sum_congr rfl fun m _ => integral_finsetSum _ fun k _ => hint m k

/-- **The matrix Brownian Itô integral has orthogonal increments on every window.** -/
theorem hasOrthogonalIncrementsOn_euclideanItoIntegral (T : ℝ) :
    HasOrthogonalIncrementsOn ℱ P T (euclideanItoIntegral W ℱ hcoord H hHm hHp hHs) where
  memLp t _ _ := memLp_euclideanItoIntegral t
  ae_zero := euclideanItoIntegral_ae_zero
  integral_inner_eq s t _ hst _ ξ hξ hξ2 := by
    obtain ⟨ξ', hξ'm, hξξ'⟩ := hξ
    have hξ'2 : MemLp ξ' 2 P := hξ2.ae_eq hξξ'
    have e : ∀ r, ∫ ω, ⟪ξ ω, euclideanItoIntegral W ℱ hcoord H hHm hHp hHs r ω⟫ ∂P
        = ∫ ω, ⟪ξ' ω, euclideanItoIntegral W ℱ hcoord H hHm hHp hHs r ω⟫ ∂P := fun r =>
      integral_congr_ae (hξξ'.mono fun ω hω => by simp only [hω])
    rw [e t, e s, integral_inner_euclideanItoIntegral hξ'2 t,
      integral_inner_euclideanItoIntegral hξ'2 s]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    exact LevyStochCalc.Ito.SecondMoment.integral_mul_martingale_eq
      (martingale_stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
        (hHs m k)) hst
      ((EuclideanSpace.proj (𝕜 := ℝ) m).continuous.comp_stronglyMeasurable hξ'm)
      ((EuclideanSpace.proj (𝕜 := ℝ) m).comp_memLp' hξ'2)
      (stochasticIntegralBrownian_memLp (W.W k) ℱ (hcoord k) (H m k) (hHm m k) (hHp m k)
        (hHs m k) t)

/-- **The polarised isometry of the matrix Brownian Itô integral.** For two matrix integrands
`H`, `K` and every window `[0, T]`, `𝔼⟪∫_0^t H dW, ∫_0^t K dW⟫ = 𝔼 ∫_0^t ⟪H_s, K_s⟫ ds` for
`t ∈ [0, T]`, the pairing of the integrands being the Frobenius pairing. -/
theorem hasPolarisedIsometryOn_euclideanItoIntegral (T : ℝ) {K : Fin n → Fin d → Ω → ℝ → ℝ}
    {hKm : ∀ m k, Measurable (Function.uncurry (K m k))}
    {hKp : ∀ m k, Probability.ProgressivelyMeasurable ℱ (K m k)}
    {hKs : ∀ (m : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K m k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤} :
    HasPolarisedIsometryOn P T (euclideanItoIntegral W ℱ hcoord H hHm hHp hHs)
      (euclideanItoIntegral W ℱ hcoord K hKm hKp hKs) (euclideanMatrix H) (euclideanMatrix K) where
  integrand_left := memLp_euclideanMatrix hHm hHs T
  integrand_right := memLp_euclideanMatrix hKm hKs T
  isometry t ht0 _ := by
    rcases ht0.eq_or_lt with rfl | ht
    · have hL : ∫ ω, ⟪euclideanItoIntegral W ℱ hcoord H hHm hHp hHs 0 ω,
          euclideanItoIntegral W ℱ hcoord K hKm hKp hKs 0 ω⟫ ∂P = 0 := by
        rw [integral_congr_ae (euclideanItoIntegral_ae_zero.mono fun ω hω => by
          rw [hω, Pi.zero_apply, inner_zero_left])]
        exact integral_zero _ _
      have hnull : volume.restrict (Set.Icc (0 : ℝ) 0) = 0 := by simp
      rw [hL, hnull]
      simp
    · -- the left side, entry by entry
      have hS : ∀ m k, MemLp (coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t) 2 P :=
        fun m k => stochasticIntegralBrownian_memLp (W.W k) ℱ (hcoord k) (H m k) (hHm m k)
          (hHp m k) (hHs m k) t
      have hS' : ∀ m k, MemLp (coordItoIntegral W ℱ hcoord K hKm hKp hKs m k t) 2 P :=
        fun m k => stochasticIntegralBrownian_memLp (W.W k) ℱ (hcoord k) (K m k) (hKm m k)
          (hKp m k) (hKs m k) t
      have hL : ∫ ω, ⟪euclideanItoIntegral W ℱ hcoord H hHm hHp hHs t ω,
          euclideanItoIntegral W ℱ hcoord K hKm hKp hKs t ω⟫ ∂P
          = ∑ m, ∑ k, ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, H m k ω s * K m k ω s ∂volume ∂P := by
        have hexp : (fun ω => ⟪euclideanItoIntegral W ℱ hcoord H hHm hHp hHs t ω,
            euclideanItoIntegral W ℱ hcoord K hKm hKp hKs t ω⟫)
            = fun ω => ∑ m, ∑ k, ∑ l, coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t ω
                * coordItoIntegral W ℱ hcoord K hKm hKp hKs m l t ω := by
          funext ω
          simp only [euclideanItoIntegral, PiLp.inner_apply, Real.inner_apply,
            vectorItoMartingale, Finset.sum_mul_sum]
        have hint : ∀ m k l, Integrable (fun ω => coordItoIntegral W ℱ hcoord H hHm hHp hHs m k t ω
            * coordItoIntegral W ℱ hcoord K hKm hKp hKs m l t ω) P := fun m k l =>
          (hS m k).integrable_mul (hS' m l)
        rw [hexp, integral_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ =>
          integrable_finsetSum _ fun l _ => hint m k l]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint m k l]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_finsetSum _ fun l _ => hint m k l,
          Finset.sum_eq_single k (fun l _ hlk => ?_) (fun hk => absurd (Finset.mem_univ k) hk)]
        · exact LevyStochCalc.Ito.SecondMoment.integral_mul_stochasticIntegralBrownian (W.W k) ℱ
            (hcoord k) (hHm m k) (hHp m k) (hHs m k) (hKm m k) (hKp m k) (hKs m k) ht
        · exact Multidim.MultidimBrownianMotion.integral_stochasticIntegral_mul_eq_zero W
            (Ne.symm hlk) hcoord (hHm m k) (hHp m k) (hHs m k) (hKm m l) (hKp m l) (hKs m l) ht0
      -- the right side, entry by entry
      have hHK : ∀ m k, Integrable (fun p : Ω × ℝ => H m k p.1 p.2 * K m k p.1 p.2)
          (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := fun m k =>
        (LevyStochCalc.Ito.SecondMoment.memLp_two_prod (hHm m k)
          (energy_lt_top_of_forall_pos (hHs m k) t)).integrable_mul
          (LevyStochCalc.Ito.SecondMoment.memLp_two_prod (hKm m k)
            (energy_lt_top_of_forall_pos (hKs m k) t))
      have hslice : ∀ᵐ ω ∂P, ∀ m k, Integrable (fun s => H m k ω s * K m k ω s)
          (volume.restrict (Set.Icc (0 : ℝ) t)) := by
        rw [ae_all_iff]
        intro m
        rw [ae_all_iff]
        exact fun k => (hHK m k).prod_right_ae
      have hR : ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, ⟪euclideanMatrix H s ω, euclideanMatrix K s ω⟫
            ∂volume ∂P
          = ∑ m, ∑ k, ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, H m k ω s * K m k ω s ∂volume ∂P := by
        have h1 : (fun ω => ∫ s in Set.Icc (0 : ℝ) t,
              ⟪euclideanMatrix H s ω, euclideanMatrix K s ω⟫)
            =ᵐ[P] fun ω => ∑ m, ∑ k, ∫ s in Set.Icc (0 : ℝ) t, H m k ω s * K m k ω s := by
          filter_upwards [hslice] with ω hω
          simp_rw [inner_euclideanMatrix]
          rw [integral_finsetSum _ fun m _ => integrable_finsetSum _ fun k _ => hω m k]
          exact Finset.sum_congr rfl fun m _ => integral_finsetSum _ fun k _ => hω m k
        rw [integral_congr_ae h1, integral_finsetSum _ fun m _ => integrable_finsetSum _
          fun k _ => (hHK m k).integral_prod_left]
        exact Finset.sum_congr rfl fun m _ =>
          integral_finsetSum _ fun k _ => (hHK m k).integral_prod_left
      rw [hL, hR]

end LevyStochCalc.Ito.FiniteHorizon
