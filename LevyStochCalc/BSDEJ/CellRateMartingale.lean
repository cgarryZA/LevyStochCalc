/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CondCellProjection

/-!
# The cell-projection rate of a martingale plus a mean-square Lipschitz process

Let `Z = M + A` on `[0, T]`, where `M` is a square-integrable martingale for the filtration `ℱ`
and `A` is adapted, square-integrable and satisfies `E ‖A_t − A_s‖² ≤ K (t − s)`. Then the
cell-projection error of `Z` on the uniform grid of `N` cells is at most
`(2 E ‖M_T‖² + K T) T / N`.

By optimality of the conditional cell averages the error is at most the energy of
`Z − (M_{t_i} + A_{t_i})` on each cell. The martingale has orthogonal increments, so
`E ‖M_s − M_{t_i}‖² = E ‖M_s‖² − E ‖M_{t_i}‖² ≤ E ‖M_{t_{i+1}}‖² − E ‖M_{t_i}‖²` on the cell,
and the sum over the cells telescopes.

## Main statements

* `integral_sq_sub_eq_of_condExp_eq` — orthogonality of a martingale increment.
* `cellProjError_le_of_martingale_add` — the rate.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- **Orthogonality of a martingale increment.** If `m_r` is square-integrable and measurable at
`r`, `m_s` is square-integrable and `E[m_s | ℱ_r] = m_r`, then
`E (m_s − m_r)² = E m_s² − E m_r²`. -/
theorem integral_sq_sub_eq_of_condExp_eq {r : ℝ} {mr ms : Ω → ℝ}
    (hmr : StronglyMeasurable[ℱ r] mr) (hr : MemLp mr 2 P) (hs : MemLp ms 2 P)
    (hmart : P[ms | ℱ r] =ᵐ[P] mr) :
    ∫ ω, (ms ω - mr ω) ^ 2 ∂P = ∫ ω, ms ω ^ 2 ∂P - ∫ ω, mr ω ^ 2 ∂P := by
  have hcr : Integrable (mr * ms) P := hr.integrable_mul hs
  have hce := condExp_mul_of_stronglyMeasurable_left (m := ℱ r) hmr hcr (hs.integrable one_le_two)
  have hcross : ∫ ω, mr ω * ms ω ∂P = ∫ ω, mr ω ^ 2 ∂P := by
    calc ∫ ω, mr ω * ms ω ∂P = ∫ ω, P[mr * ms | ℱ r] ω ∂P := (integral_condExp (ℱ.le r)).symm
      _ = ∫ ω, mr ω * P[ms | ℱ r] ω ∂P := integral_congr_ae hce
      _ = ∫ ω, mr ω ^ 2 ∂P := integral_congr_ae (by
          filter_upwards [hmart] with ω hω
          rw [hω, sq])
  have i1 : Integrable (fun ω => ms ω ^ 2 - 2 * (mr ω * ms ω)) P :=
    hs.integrable_sq.sub ((hr.integrable_mul hs).const_mul 2)
  have i2 : Integrable (fun ω => 2 * (mr ω * ms ω)) P := (hr.integrable_mul hs).const_mul 2
  have hpt : (fun ω => (ms ω - mr ω) ^ 2) = fun ω => (ms ω ^ 2 - 2 * (mr ω * ms ω)) + mr ω ^ 2 := by
    funext ω; ring
  rw [hpt, integral_add i1 hr.integrable_sq, integral_sub hs.integrable_sq i2, integral_const_mul,
    hcross]
  ring

omit [MeasurableSpace Ω] in
private theorem integral_cell_affine {a b : ℝ} (hab : a ≤ b) (c K : ℝ) :
    ∫ s in Set.Icc a b, (c + K * (s - a)) = c * (b - a) + K * (b - a) ^ 2 / 2 := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have h1 : IntervalIntegrable (fun x : ℝ => K * (x - a)) volume a b :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const h1,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_right (fun x => x)]
  simp [integral_id]
  ring

variable {d : ℕ} {T : ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}

/-- **The cell-projection rate of a martingale plus a mean-square Lipschitz process.** Let `Z` be
a jointly measurable process of finite energy on `[0, T]`, `T > 0`, with `Z_t = M_t + A_t`
almost surely for almost every `t ∈ [0, T]`, where `M` is a square-integrable `ℱ`-martingale on
`[0, T]` with `E ‖M_T‖² ≤ B` and `A` is adapted, square-integrable and satisfies
`E ‖A_t − A_s‖² ≤ K (t − s)`. Then the cell-projection error on the uniform grid of `N ≥ 1`
cells is at most `(2 B + K T) T / N`; the norms are Euclidean. -/
theorem cellProjError_le_of_martingale_add (hT : 0 < T)
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {M A : ℝ → Ω → (Fin d → ℝ)}
    (hMa : ∀ t ∈ Set.Icc 0 T, ∀ k, StronglyMeasurable[ℱ t] fun ω => M t ω k)
    (hM2 : ∀ t ∈ Set.Icc 0 T, ∀ k, MemLp (fun ω => M t ω k) 2 P)
    (hMart : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → ∀ k,
      P[fun ω => M t ω k | ℱ s] =ᵐ[P] fun ω => M s ω k)
    {B : ℝ} (hB : ∫ ω, ∑ k, M T ω k ^ 2 ∂P ≤ B)
    (hAa : ∀ t ∈ Set.Icc 0 T, ∀ k, StronglyMeasurable[ℱ t] fun ω => A t ω k)
    (hA2 : ∀ t ∈ Set.Icc 0 T, ∀ k, MemLp (fun ω => A t ω k) 2 P)
    {K : ℝ} (hA : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      ∫ ω, ∑ k, (A t ω k - A s ω k) ^ 2 ∂P ≤ K * (t - s))
    (hZ : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), Z t =ᵐ[P] fun ω => M t ω + A t ω)
    {N : ℕ} (hN : 0 < N) :
    cellProjError ℱ P T N Z ≤ ENNReal.ofReal ((2 * B + K * T) * (T / N)) := by
  set τ : ℝ := T / N with hτdef
  have hτ : 0 < τ := div_pos hT (by exact_mod_cast hN)
  have hNτ : (N : ℝ) * τ = T := by rw [hτdef]; field_simp
  set m : ℝ → ℝ := fun t => ∫ ω, ∑ k, M t ω k ^ 2 ∂P with hmdef
  have hK : 0 ≤ K := by
    have h := hA 0 T le_rfl hT.le le_rfl
    have h0 : 0 ≤ ∫ ω, ∑ k, (A T ω k - A 0 ω k) ^ 2 ∂P :=
      integral_nonneg fun ω => Finset.sum_nonneg fun k _ => sq_nonneg _
    nlinarith
  have hinc : ∀ r s, 0 ≤ r → r ≤ s → s ≤ T →
      ∫ ω, ∑ k, (M s ω k - M r ω k) ^ 2 ∂P = m s - m r := by
    intro r s hr hrs hsT
    have hrI : r ∈ Set.Icc 0 T := ⟨hr, hrs.trans hsT⟩
    have hsI : s ∈ Set.Icc 0 T := ⟨hr.trans hrs, hsT⟩
    simp only [hmdef]
    have i1 : ∀ k ∈ Finset.univ, Integrable (fun ω => (M s ω k - M r ω k) ^ 2) P :=
      fun k _ => ((hM2 s hsI k).sub (hM2 r hrI k)).integrable_sq
    have i2 : ∀ k ∈ Finset.univ, Integrable (fun ω => M s ω k ^ 2) P :=
      fun k _ => (hM2 s hsI k).integrable_sq
    have i3 : ∀ k ∈ Finset.univ, Integrable (fun ω => M r ω k ^ 2) P :=
      fun k _ => (hM2 r hrI k).integrable_sq
    rw [integral_finsetSum _ i1, integral_finsetSum _ i2, integral_finsetSum _ i3,
      ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => integral_sq_sub_eq_of_condExp_eq ℱ (hMa r hrI k)
      (hM2 r hrI k) (hM2 s hsI k) (hMart r s hr hrs hsT k)
  have hmono : ∀ r s, 0 ≤ r → r ≤ s → s ≤ T → m r ≤ m s := by
    intro r s hr hrs hsT
    have h := hinc r s hr hrs hsT
    have h0 : 0 ≤ ∫ ω, ∑ k, (M s ω k - M r ω k) ^ 2 ∂P :=
      integral_nonneg fun ω => Finset.sum_nonneg fun k _ => sq_nonneg _
    linarith
  have hgrid : ∀ i < N, (i : ℝ) * τ ∈ Set.Icc 0 T ∧ ((i : ℝ) + 1) * τ ∈ Set.Icc 0 T := by
    intro i hi
    have hsub := cell_subset_Icc hT.le hi
    have hab : (i : ℝ) * τ ≤ ((i : ℝ) + 1) * τ := by nlinarith
    exact ⟨hsub ⟨le_rfl, hab⟩, hsub ⟨hab, le_rfl⟩⟩
  refine (cellProjError_le ℱ hT hN hZm hZs (η := fun i ω k => M ((i : ℝ) * τ) ω k
      + A ((i : ℝ) * τ) ω k)
    (fun i hi k => (hMa _ (hgrid i hi).1 k).add (hAa _ (hgrid i hi).1 k))
    (fun i hi k => (hM2 _ (hgrid i hi).1 k).add (hA2 _ (hgrid i hi).1 k))).trans ?_
  -- the bound on one cell
  have hcell : ∀ i < N, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      ∑ k, (‖Z s ω k - (M ((i : ℝ) * τ) ω k + A ((i : ℝ) * τ) ω k)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ENNReal.ofReal (2 * (m (((i : ℝ) + 1) * τ) - m ((i : ℝ) * τ)) * τ + K * τ ^ 2) := by
    intro i hi
    obtain ⟨hti, hti'⟩ := hgrid i hi
    set t := (i : ℝ) * τ with htdef
    have hlen : ((i : ℝ) + 1) * τ - t = τ := by rw [htdef]; ring
    have hsub : Set.Icc t (((i : ℝ) + 1) * τ) ⊆ Set.Icc 0 T :=
      Set.Icc_subset_Icc hti.1 hti'.2
    have hηm : ∀ k, Measurable fun ω => M t ω k + A t ω k := fun k =>
      ((hMa t hti k).mono (ℱ.le t)).measurable.add ((hAa t hti k).mono (ℱ.le t)).measurable
    have hmeas : Measurable (Function.uncurry fun ω s =>
        ∑ k, (‖Z s ω k - (M t ω k + A t ω k)‖₊ : ℝ≥0∞) ^ 2) :=
      Finset.measurable_sum _ fun k _ =>
        ((hZm k).sub ((hηm k).comp measurable_fst)).nnnorm.coe_nnreal_ennreal.pow_const 2
    rw [lintegral_lintegral_swap hmeas.aemeasurable]
    set c : ℝ := 2 * (m (((i : ℝ) + 1) * τ) - m t) with hcdef
    have hc : 0 ≤ c := by
      have := hmono t (((i : ℝ) + 1) * τ) hti.1 (by linarith) hti'.2
      rw [hcdef]; linarith
    calc ∫⁻ s in Set.Icc t (((i : ℝ) + 1) * τ), ∫⁻ ω,
          ∑ k, (‖Z s ω k - (M t ω k + A t ω k)‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ∫⁻ s in Set.Icc t (((i : ℝ) + 1) * τ), ENNReal.ofReal (c + (2 * K) * (s - t)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hZ,
            ae_restrict_mem measurableSet_Icc] with s hs hsI
          have hs0 : s ∈ Set.Icc 0 T := hsub hsI
          have hint : Integrable (fun ω => ∑ k, (2 * (M s ω k - M t ω k) ^ 2
              + 2 * (A s ω k - A t ω k) ^ 2)) P :=
            integrable_finsetSum _ fun k _ =>
              ((((hM2 s hs0 k).sub (hM2 t hti k)).integrable_sq.const_mul 2).add
                (((hA2 s hs0 k).sub (hA2 t hti k)).integrable_sq.const_mul 2))
          calc ∫⁻ ω, ∑ k, (‖Z s ω k - (M t ω k + A t ω k)‖₊ : ℝ≥0∞) ^ 2 ∂P
              ≤ ∫⁻ ω, ENNReal.ofReal (∑ k, (2 * (M s ω k - M t ω k) ^ 2
                  + 2 * (A s ω k - A t ω k) ^ 2)) ∂P := by
                refine lintegral_mono_ae ?_
                filter_upwards [hs] with ω hω
                rw [ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
                refine Finset.sum_le_sum fun k _ => ?_
                have hz : Z s ω k = M s ω k + A s ω k := by rw [hω]; rfl
                rw [hz, nnnorm_sq_eq_ofReal]
                refine ENNReal.ofReal_le_ofReal ?_
                nlinarith [sq_nonneg ((M s ω k - M t ω k) - (A s ω k - A t ω k))]
            _ = ENNReal.ofReal (∫ ω, ∑ k, (2 * (M s ω k - M t ω k) ^ 2
                  + 2 * (A s ω k - A t ω k) ^ 2) ∂P) :=
                (ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun ω =>
                  Finset.sum_nonneg fun k _ => by positivity)).symm
            _ ≤ ENNReal.ofReal (c + (2 * K) * (s - t)) := by
                refine ENNReal.ofReal_le_ofReal ?_
                have e : ∫ ω, ∑ k, (2 * (M s ω k - M t ω k) ^ 2
                    + 2 * (A s ω k - A t ω k) ^ 2) ∂P
                    = 2 * ∫ ω, ∑ k, (M s ω k - M t ω k) ^ 2 ∂P
                      + 2 * ∫ ω, ∑ k, (A s ω k - A t ω k) ^ 2 ∂P := by
                  have i1 : Integrable (fun ω => ∑ k, (M s ω k - M t ω k) ^ 2) P :=
                    integrable_finsetSum _ fun k _ =>
                      ((hM2 s hs0 k).sub (hM2 t hti k)).integrable_sq
                  have i2 : Integrable (fun ω => ∑ k, (A s ω k - A t ω k) ^ 2) P :=
                    integrable_finsetSum _ fun k _ =>
                      ((hA2 s hs0 k).sub (hA2 t hti k)).integrable_sq
                  rw [← integral_const_mul, ← integral_const_mul,
                    ← integral_add (i1.const_mul 2) (i2.const_mul 2)]
                  refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
                  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
                rw [e, hinc t s hti.1 hsI.1 hs0.2]
                have h1 := hA t s hti.1 hsI.1 hs0.2
                have h2 := hmono s (((i : ℝ) + 1) * τ) hs0.1 hsI.2 hti'.2
                rw [hcdef]
                nlinarith
      _ = ENNReal.ofReal (∫ s in Set.Icc t (((i : ℝ) + 1) * τ), (c + (2 * K) * (s - t))) := by
          refine (ofReal_integral_eq_lintegral_ofReal ?_ ?_).symm
          · exact (continuous_const.add (continuous_const.mul
              (continuous_id.sub continuous_const))).integrableOn_Icc
          · filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
            have : 0 ≤ s - t := by linarith [hs.1]
            positivity
      _ = _ := by
          rw [integral_cell_affine (by linarith) c (2 * K), hlen]
          congr 1
          ring
  refine (Finset.sum_le_sum fun i hi => hcell i (Finset.mem_range.mp hi)).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun i hi => by
    have := hmono _ _ (hgrid i (Finset.mem_range.mp hi)).1.1 (by nlinarith)
      (hgrid i (Finset.mem_range.mp hi)).2.2
    positivity]
  refine ENNReal.ofReal_le_ofReal ?_
  have htel : ∑ i ∈ Finset.range N, (m (((i : ℝ) + 1) * τ) - m ((i : ℝ) * τ))
      = m ((N : ℝ) * τ) - m 0 := by
    have := Finset.sum_range_sub (fun j : ℕ => m ((j : ℝ) * τ)) N
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, zero_mul] at this
    exact this
  have hsplit : ∑ i ∈ Finset.range N, (2 * (m (((i : ℝ) + 1) * τ) - m ((i : ℝ) * τ)) * τ
      + K * τ ^ 2) = 2 * τ * (m ((N : ℝ) * τ) - m 0) + (N : ℝ) * (K * τ ^ 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← htel,
      Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit, hNτ]
  have hm0 : 0 ≤ m 0 := integral_nonneg fun ω => Finset.sum_nonneg fun k _ => sq_nonneg _
  have hKT : (N : ℝ) * (K * τ ^ 2) = K * T * τ := by rw [← hNτ]; ring
  rw [hKT]
  nlinarith

end LevyStochCalc.BSDEJ.PathRegularity
