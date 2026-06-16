/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.SimplePredictableRefine
import LevyStochCalc.Brownian.ItoSimple
import LevyStochCalc.Brownian.ItoDensity
import LevyStochCalc.Brownian.ItoMartingale

/-!
# Brownian Itô integral via L²-completion

Lifts the simple-integrand Brownian integral to `Lp ℝ 2 P`, takes the L²-limit
along a dense approximating sequence, and proves the L²-isometry of the limit,
giving the L² Brownian Itô integral. The result is packaged as the cited
existence axiom `itoIsometry_brownian_unified_existence` (#5) and the
`stochasticIntegral` API (`itoIsometry`, `quadVar_stochasticIntegral`,
`martingale_stochasticIntegral`). Builds on the refinement machinery in
`Brownian/SimplePredictableRefine.lean`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **C0b.10-pre1: `simpleIntegral` has finite `L²(P)` norm.** For any
adapted `SimplePredictable`, the squared `lintegral` of the integral
against `P` is finite. Direct from `simpleIntegral_isometry` (giving
`= ∫⁻ ω ∫⁻ s ‖H.eval s ω‖²`) plus `lintegral_eval_sq_outer` (giving
`= ∑_i Δt_i · ∫⁻ ω ‖H.ξ i ω‖²`), each summand bounded by
`Δt_i · M_i² ≤ T · M_i² < ∞` via `ξ_bounded`.

This is the boundedness fact needed to lift `simpleIntegral W H T` to
an element of `Lp ℝ 2 P` for the `L²` extension in `C0b.10`. -/
lemma simpleIntegral_lintegral_sq_finite_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    ∫⁻ ω, (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 ∂P < ⊤ := by
  rw [simpleIntegral_isometry W hT H h_adapt]
  rw [lintegral_eval_sq_outer H]
  refine ENNReal.sum_lt_top.mpr (fun i _ => ?_)
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  obtain ⟨M, hM⟩ := H.ξ_bounded i
  have h_M_nn : 0 ≤ max M 0 := le_max_right _ _
  have h_bound : ∀ ω, |H.ξ i ω| ≤ max M 0 :=
    fun ω => le_trans (hM ω) (le_max_left _ _)
  have h_norm_le : ∀ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal (max M 0) := by
    intro ω
    rw [show (‖H.ξ i ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.ξ i ω‖
          from (ofReal_norm_eq_enorm _).symm]
    exact ENNReal.ofReal_le_ofReal
      (Real.norm_eq_abs _ ▸ h_bound ω)
  calc ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ _ω, (ENNReal.ofReal (max M 0)) ^ 2 ∂P := by
        refine MeasureTheory.lintegral_mono (fun ω => ?_)
        exact pow_le_pow_left' (h_norm_le ω) 2
    _ = (ENNReal.ofReal (max M 0)) ^ 2 * P Set.univ := by
        rw [MeasureTheory.lintegral_const]
    _ < ⊤ := by
        rw [MeasureTheory.measure_univ, mul_one]
        exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top

/-- **C0b.10-pre2: `simpleIntegral W H T` is in `L²(P)`.** Combines
the AEStronglyMeasurability of `simpleIntegral` (via `Finset.sum`
of measurable terms) with `simpleIntegral_lintegral_sq_finite_brownian`
(C0b.10-pre1) to produce a `MemLp 2 P` witness. This is the lift
of `simpleIntegral` into Mathlib's `Lp` framework, needed for the
L²-Cauchy completion in C0b.10. -/
lemma simpleIntegral_memLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H T ω) 2 P := by
  refine ⟨?_, ?_⟩
  · -- AEStronglyMeasurable: simpleIntegral W H T = ∑_i ξ_i · ΔW_i
    -- is a finite sum of products of measurable functions.
    refine Measurable.aestronglyMeasurable ?_
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    refine Measurable.mul (H.ξ_measurable i) ?_
    exact (W.measurable_eval _).sub (W.measurable_eval _)
  · -- eLpNorm < ⊤: from C0b.10-pre1 (∫⁻ ‖simpleIntegral‖² < ⊤) via
    -- eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top.
    rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    have h_two_toReal : (2 : ℝ≥0∞).toReal = 2 := by simp
    rw [h_two_toReal]
    have h_pre := simpleIntegral_lintegral_sq_finite_brownian W hT H h_adapt
    -- Bridge ‖x‖ₑ ^ (2:ℝ) vs (‖x‖₊ : ℝ≥0∞) ^ (2:ℕ)
    have h_rewrite : ∀ ω : Ω,
        (‖simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          = (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2 := by
      intro ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
      rfl
    rw [show (fun ω => (‖simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2) from
        funext h_rewrite]
    exact h_pre

/-- **C0b.10-pre3: simpleIntegral lifted to `Lp ℝ 2 P`.** Packages the
`simpleIntegral_memLp_brownian` witness via `MemLp.toLp` to give a
genuine `Lp` element. This is the function that gets fed to
`MeasureTheory.Lp.completeSpace` for the L² limit construction in
C0b.10. -/
noncomputable def simpleIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Lp ℝ 2 P :=
  (simpleIntegral_memLp_brownian W hT H h_adapt).toLp

/-- **C0b.10-pre4: `simpleIntegralLp_brownian` `coeFn` matches `simpleIntegral`.**
The coercion of `simpleIntegralLp_brownian W hT H h_adapt` back to a
function `Ω → ℝ` is a.e.-equal to `fun ω => simpleIntegral W H T ω`. -/
lemma coeFn_simpleIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    (simpleIntegralLp_brownian W hT H h_adapt : Ω → ℝ)
      =ᵐ[P] (fun ω => simpleIntegral W H T ω) :=
  MeasureTheory.MemLp.coeFn_toLp _

/-- **C0b.10-pre5: `eLpNorm` of the `simpleIntegral` difference,
rpow-form.** `eLpNorm (...)^(2:ℝ) = ∫⁻ ‖eval diff‖² over [0,T]×Ω`.

This is `diff_isometry_simple` rephrased in `eLpNorm` form using the
real-valued exponent `(2:ℝ)`, ready for use with the L²-Cauchy
completion machinery. -/
lemma eLpNorm_simpleIntegral_sub_rpow_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₂.partition i.castSucc)) (H₂.ξ i)) :
    MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := P) (p := (2 : NNReal))
    (f := fun ω => simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω)
    (by norm_num : (2 : NNReal) ≠ 0)
  -- h_pow_lemma : eLpNorm f (↑(2:NNReal)) P ^ ↑(2:NNReal)
  --              = ∫⁻ ω, ‖f ω‖ₑ ^ ↑(2:NNReal) ∂P
  -- The ↑(2:NNReal) on the LHS-base is (2:ℝ≥0∞); on exponents it's (2:ℝ).
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  -- Goal: ∫⁻ ω, ‖simpleIntegral H₁ - simpleIntegral H₂‖ₑ ^ (2:ℝ) ∂P
  --     = ∫⁻ ω, ∫⁻ s, ‖eval diff‖₊² ∂vol ∂P
  -- Convert (2:ℝ) exponent to (2:ℕ) via ENNReal.rpow_natCast,
  -- then bridge ‖.‖ₑ = (‖.‖₊ : ℝ≥0∞).
  have h_pointwise : (fun ω : Ω =>
        (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
      = (fun ω : Ω =>
        (‖simpleIntegral W H₁ T ω - simpleIntegral W H₂ T ω‖₊ : ℝ≥0∞) ^ 2) := by
    funext ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
        ENNReal.rpow_natCast]
    rfl
  rw [h_pointwise]
  exact SimplePredictable.diff_isometry_simple W hT H₁ H₂ h_eq h_adapt₁ h_adapt₂

/-- **C0b.10-pre6: `simpleIntegralLp_brownian` is a `CauchySeq` in
`Lp ℝ 2 P` whenever the eval-sequence is L²-Cauchy.**

Direct application of the eLpNorm-form diff isometry
(`eLpNorm_simpleIntegral_sub_rpow_brownian`) plus
`ENNReal.rpow_lt_rpow_iff` to convert `eLpNorm^(2:ℝ) < ε^(2:ℝ)` to
`eLpNorm < ε`. The L²-Cauchy hypothesis on evals provides the matching
`∫⁻ < ε^(2:ℝ)` bound. -/
theorem cauchySeq_simpleIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    CauchySeq (fun n => simpleIntegralLp_brownian W hT (G n) (h_adapt n)) := by
  -- Step 1: establish that edist of the Lp elements equals the eLpNorm of the
  -- raw simpleIntegral function difference (via Lp.edist_toLp_toLp).
  have h_edist_eq : ∀ m n : ℕ,
      edist (simpleIntegralLp_brownian W hT (G m) (h_adapt m))
            (simpleIntegralLp_brownian W hT (G n) (h_adapt n))
        = MeasureTheory.eLpNorm
            (fun ω => simpleIntegral W (G m) T ω - simpleIntegral W (G n) T ω) 2 P := by
    intro m n
    change edist
      ((simpleIntegral_memLp_brownian W hT (G m) (h_adapt m)).toLp)
      ((simpleIntegral_memLp_brownian W hT (G n) (h_adapt n)).toLp) = _
    exact MeasureTheory.Lp.edist_toLp_toLp _ _ _ _
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · -- ε = ⊤: edist always finite (Lp norms are < ⊤).
    obtain ⟨N, _⟩ := h_cauchy_eval 1 (by norm_num : (0 : ℝ≥0∞) < 1)
    refine ⟨N, fun m _ n _ => ?_⟩
    rw [hε_top, h_edist_eq]
    -- eLpNorm of MemLp function is finite.
    have h_memLp : MeasureTheory.MemLp
        (fun ω => simpleIntegral W (G m) T ω - simpleIntegral W (G n) T ω) 2 P :=
      (simpleIntegral_memLp_brownian W hT (G m) (h_adapt m)).sub
        (simpleIntegral_memLp_brownian W hT (G n) (h_adapt n))
    exact lt_of_le_of_ne le_top h_memLp.eLpNorm_ne_top
  · -- ε < ⊤. Pick δ = ε ^ (2:ℝ).
    set δ : ℝ≥0∞ := ε ^ (2 : ℝ) with hδ
    have hδ_pos : 0 < δ := by
      rw [hδ]
      exact ENNReal.rpow_pos hε hε_top
    obtain ⟨N, hN⟩ := h_cauchy_eval δ hδ_pos
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [h_edist_eq]
    have h_iso := eLpNorm_simpleIntegral_sub_rpow_brownian W hT (G m) (G n)
      (h_eq m n) (h_adapt m) (h_adapt n)
    have h_lt := hN m n hm hn
    rw [← h_iso] at h_lt
    rw [hδ] at h_lt
    exact (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h_lt

/-- **C0b.10: `itoIntegralLp_brownian` — the L²-limit of `simpleIntegralLp_brownian`
along a Cauchy approximating sequence.**

This is the genuine L²-extended Itô integral against Brownian motion,
defined as `Filter.limUnder Filter.atTop (simpleIntegralLp_brownian ∘ G)`
for any approximating sequence `G : ℕ → SimplePredictable` whose evals
are L²-Cauchy and which are adapted with shared endpoints.

The convergence (and unique-limit identification) follows from
`Lp.completeSpace` + `cauchySeq_simpleIntegralLp_brownian` (C0b.10-pre6)
+ `CauchySeq.tendsto_limUnder`. Properties of `itoIntegralLp_brownian`
(L² isometry, etc.) are proved in subsequent lemmas. -/
noncomputable def itoIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (_hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (_h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (_h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    MeasureTheory.Lp ℝ 2 P :=
  Filter.limUnder Filter.atTop
    (fun n => simpleIntegralLp_brownian W _hT (G n) (h_adapt n))

/-- **C0b.10-post1: `simpleIntegralLp_brownian` converges to `itoIntegralLp_brownian`
in `Lp ℝ 2 P`.** Direct from `cauchySeq_simpleIntegralLp_brownian` +
`CauchySeq.tendsto_limUnder` (using `Lp.completeSpace`). -/
theorem itoIntegralLp_brownian_tendsto
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => simpleIntegralLp_brownian W hT (G n) (h_adapt n))
      Filter.atTop
      (nhds (itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval)) :=
  (cauchySeq_simpleIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval).tendsto_limUnder

/-- **C0b.10-post2: `eLpNorm` of `simpleIntegralLp` rpow-form, the
single-function version of the diff isometry.**

`eLpNorm (simpleIntegralLp ...) 2 P ^ (2:ℝ)`
`= ∫⁻ ω ∫⁻ s ‖H.eval s ω‖₊² ∂vol ∂P`.

Direct from `simpleIntegral_isometry` (single-function version) plus
the same `eLpNorm_nnreal_pow_eq_lintegral` bridge as the diff form. -/
lemma eLpNorm_simpleIntegralLp_brownian_rpow_eq
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT H h_adapt) : Ω → ℝ) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Step 1: replace ↑↑(toLp ...) with the original simpleIntegral function (a.e.).
  have h_aeeq := coeFn_simpleIntegralLp_brownian W hT H h_adapt
  rw [MeasureTheory.eLpNorm_congr_ae h_aeeq]
  -- Goal: eLpNorm (fun ω => simpleIntegral W H T ω) 2 P ^ (2:ℝ)
  --     = ∫⁻ ω, ∫⁻ s, ‖H.eval s ω‖₊² ∂vol ∂P
  -- Step 2: eLpNorm^(2:ℝ) = ∫⁻ ‖.‖_e² via eLpNorm_nnreal_pow_eq_lintegral.
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := P) (p := (2 : NNReal))
    (f := fun ω => simpleIntegral W H T ω)
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  -- Goal: ∫⁻ ω, ‖simpleIntegral W H T ω‖_e ^ (2:ℝ) ∂P
  --     = ∫⁻ ω, ∫⁻ s, ‖H.eval s ω‖₊² ∂vol ∂P
  -- Step 3: ‖.‖_e ^ (2:ℝ) = (‖.‖₊ : ℝ≥0∞) ^ 2 (via ENNReal.rpow_natCast).
  have h_pointwise : (fun ω : Ω =>
        (‖simpleIntegral W H T ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
      = (fun ω : Ω => (‖simpleIntegral W H T ω‖₊ : ℝ≥0∞) ^ 2) := by
    funext ω
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
        ENNReal.rpow_natCast]
    rfl
  rw [h_pointwise]
  -- Goal: ∫⁻ ω, ‖simpleIntegral W H T ω‖₊² ∂P
  --     = ∫⁻ ω, ∫⁻ s, ‖H.eval s ω‖₊² ∂vol ∂P
  -- Step 4: simpleIntegral_isometry.
  exact simpleIntegral_isometry W hT H h_adapt

/-- **C0b.10-post3: ‖simpleIntegralLp_brownian (G n)‖ converges to
‖itoIntegralLp_brownian‖ in ℝ.** Direct from the convergence of
`simpleIntegralLp_brownian (G n) → itoIntegralLp_brownian` in `Lp`
plus continuity of the norm. -/
theorem norm_simpleIntegralLp_tendsto_norm_itoIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => ‖simpleIntegralLp_brownian W hT (G n) (h_adapt n)‖)
      Filter.atTop
      (nhds ‖itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval‖) :=
  (itoIntegralLp_brownian_tendsto W hT G h_eq h_adapt h_cauchy_eval).norm

/-- **C0b.10-post4: `eLpNorm (↑↑(simpleIntegralLp (G n))) 2 P` converges
to `eLpNorm (↑↑(itoIntegralLp ...)) 2 P` in `ℝ≥0∞`.** ENNReal-valued
companion to `norm_simpleIntegralLp_tendsto_norm_itoIntegralLp_brownian`,
via `Filter.Tendsto.enorm` and `Lp.enorm_def`. -/
theorem eLpNorm_simpleIntegralLp_tendsto_eLpNorm_itoIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P)
      Filter.atTop
      (nhds (MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ) 2 P)) := by
  have h_tendsto :=
    (itoIntegralLp_brownian_tendsto W hT G h_eq h_adapt h_cauchy_eval).enorm
  -- h_tendsto : Tendsto (fun n => ‖Lp_n‖ₑ) atTop (nhds ‖Lp_lim‖ₑ)
  -- Use Lp.enorm_def to convert ‖f‖ₑ = eLpNorm (↑↑f) p μ.
  simp only [MeasureTheory.Lp.enorm_def] at h_tendsto
  exact h_tendsto

/-- **C0b.10-post5: `eLpNorm (simpleIntegralLp (G n)) ^ (2:ℝ)` converges
to `eLpNorm (itoIntegralLp ...) ^ (2:ℝ)` in `ℝ≥0∞`.** Direct application
of `Filter.Tendsto.ennrpow_const` to the eLpNorm convergence (post4). -/
theorem eLpNorm_rpow_simpleIntegralLp_tendsto_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P ^ (2 : ℝ))
      Filter.atTop
      (nhds (MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ)
          2 P ^ (2 : ℝ))) :=
  (eLpNorm_simpleIntegralLp_tendsto_eLpNorm_itoIntegralLp_brownian
    W hT G h_eq h_adapt h_cauchy_eval).ennrpow_const 2

/-- **C0b.10-post6: lintegral-of-squared-eval converges to `eLpNorm²` of
`itoIntegralLp_brownian`.**

Substitutes `eLpNorm_simpleIntegralLp_brownian_rpow_eq` (post2) into
`eLpNorm_rpow_simpleIntegralLp_tendsto_brownian` (post5) to express
the convergence in pure-lintegral form. -/
theorem lintegral_sq_eval_tendsto_eLpNorm_itoIntegralLp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε) :
    Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ)
          2 P ^ (2 : ℝ))) := by
  have h_tendsto := eLpNorm_rpow_simpleIntegralLp_tendsto_brownian
    W hT G h_eq h_adapt h_cauchy_eval
  -- h_tendsto : Tendsto (fun n => eLpNorm² (simpleIntegralLp (G n))) atTop
  --              (nhds (eLpNorm² (itoIntegralLp ...)))
  -- Substitute eLpNorm² = lintegral via post2.
  have h_subst : ∀ n : ℕ,
      MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun n => eLpNorm_simpleIntegralLp_brownian_rpow_eq W hT (G n) (h_adapt n)
  -- Rewrite the function inside the Tendsto.
  have h_eqv : (fun n => MeasureTheory.eLpNorm
        (↑↑(simpleIntegralLp_brownian W hT (G n) (h_adapt n)) : Ω → ℝ) 2 P ^ (2 : ℝ))
      = (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
    funext h_subst
  rw [h_eqv] at h_tendsto
  exact h_tendsto

/-- **C0b.10-post7: L² isometry on `itoIntegralLp_brownian`.**

Conditional on the approximating sequence's `lintegral_sq` of `(G n).eval`
converging to `∫⁻ ω ∫⁻ s ‖H ω s‖₊² ∂vol ∂P`, we obtain
`eLpNorm² (itoIntegralLp ...) = ∫⁻ ω ∫⁻ s ‖H ω s‖₊² ∂vol ∂P`.

By uniqueness of limits in `ℝ≥0∞`, combining the two `Tendsto` statements
(the `(G n).eval`-form from `lintegral_sq_eval_tendsto_...` and the
hypothesised convergence to `∫⁻ ‖H‖²`) forces equality of the limits. -/
theorem itoIntegralLp_brownian_L2_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε)
    (H : Ω → ℝ → ℝ)
    (h_eval_norm_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) :
    MeasureTheory.eLpNorm
        (↑↑(itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval) : Ω → ℝ) 2 P
          ^ (2 : ℝ)
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Both Tendsto statements have the same source filter and source function;
  -- their target nhds-points must coincide by uniqueness of limits.
  have h_to_eLpNorm := lintegral_sq_eval_tendsto_eLpNorm_itoIntegralLp_brownian
    W hT G h_eq h_adapt h_cauchy_eval
  exact (tendsto_nhds_unique h_to_eLpNorm h_eval_norm_tendsto)

/-- **C0b.10-post8: `simpleIntegral W H t` is StronglyAdapted at `t`
to `naturalFiltration W`.**

For each `t : ℝ` and adapted SimplePredictable `H`, the function
`ω ↦ simpleIntegral W H t ω` is StronglyMeasurable wrt the natural
filtration's σ-algebra at `t`. Direct from
`martingale_simpleIntegral_brownian` (which establishes adaptedness as
its first conjunct). -/
lemma simpleIntegral_stronglyAdapted_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
      (fun ω => simpleIntegral W H t ω) :=
  (martingale_simpleIntegral_brownian W H h_adapt).stronglyAdapted t

/-- **C0b.10-post9: `simpleIntegral W H t` is in `Lp ℝ 1 P`** (integrable).

Direct from `Lp 2 ⊆ Lp 1` for finite measures (`MemLp.mono_exponent`)
applied to `simpleIntegral_memLp_brownian` (post2). Used in martingale
property checks where integrability (Lp¹) is required. -/
lemma simpleIntegral_integrable_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i)) :
    MeasureTheory.Integrable (fun ω => simpleIntegral W H T ω) P := by
  have h_memLp := simpleIntegral_memLp_brownian W hT H h_adapt
  -- MemLp 2 P implies MemLp 1 P (= Integrable) when measure is finite.
  exact (h_memLp.mono_exponent (by norm_num : (1 : ℝ≥0∞) ≤ 2)).integrable
    (le_refl 1)

/-- **C0b.10-post10: cond-exp identity for `simpleIntegral`.** Direct
extraction of the cond-exp clause from `martingale_simpleIntegral_brownian`
for downstream use without unpacking the Martingale structure. -/
lemma simpleIntegral_condExp_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hst : s ≤ t) :
    P[fun ω => simpleIntegral W H t ω
        | (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s]
      =ᵐ[P] (fun ω => simpleIntegral W H s ω) :=
  (martingale_simpleIntegral_brownian W H h_adapt).condExp_ae_eq hst

/-- **C0b.10-final: existence of an L²-isometric process for adapted-approximated H.**

Conditional on:
- `H` being approximated in `L²(λ⊗P)` by an adapted approximating
  sequence `(G n)` of `SimplePredictable`s sharing common endpoint, AND
- the lintegral_sq of `(G n).eval` converging to lintegral_sq of `H`,

we get an `L²(P)`-element `M` (the L²-extended Itô integral) satisfying
the L² isometry `eLpNorm² M = lintegral_sq H` over `[0,T] × Ω`.

This is the existence content extracted from the C0b chain, without
the additional martingale + quadVar conjuncts of the full strong-exists.
For closing the full strong-exists, one needs (a) extending C0b.9 to
general time `t < T`, (b) the limit-of-martingales + limit-of-quadVar
arguments for the time-parametrized version. -/
theorem exists_itoIntegralL2_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (G : ℕ → SimplePredictable Ω T)
    (h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N))
    (h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i))
    (h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε)
    (H : Ω → ℝ → ℝ)
    (h_eval_norm_tendsto : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖(G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P))) :
    ∃ M : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑M : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  ⟨itoIntegralLp_brownian W hT G h_eq h_adapt h_cauchy_eval,
   itoIntegralLp_brownian_L2_isometry W hT G h_eq h_adapt h_cauchy_eval H
     h_eval_norm_tendsto⟩

/-- **Bounded progressively-measurable existence.** For bounded progressively-measurable
`g : Ω → ℝ → ℝ` with explicit bound `M`, there exists an `Lp ℝ 2 P` element whose
squared `eLpNorm` over `P` equals the full `L²(P × ds)` norm of `g` over `[0,T]`.

Construction: feed the explicit `predictableDyadicSimple_brownian` sequence into
`exists_itoIntegralL2_brownian`. All four prerequisites are dyadic-specific lemmas
already in `Brownian.Ito`:

* `_partition_last` for `h_eq` (constant endpoint = T).
* `_adapted` for `h_adapt` (under progressive measurability).
* `L2_cauchy_of_L2_tendsto_brownian` applied to `_L2_converges` for `h_cauchy_eval`.
* `_eval_norm_tendsto_bounded` for `h_eval_norm_tendsto`. -/
theorem exists_itoIntegralL2_brownian_progMeas_bounded
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (g : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry g))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => g p.1 p.2))
    (M : ℝ) (h_bound : ∀ ω s, |g ω s| ≤ M) :
    ∃ Mlp : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set G : ℕ → SimplePredictable Ω T :=
    fun n => predictableDyadicSimple_brownian hT g h_meas M h_bound n with hG
  have h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N) := by
    intro n m
    rw [predictableDyadicSimple_brownian_partition_last hT g h_meas M h_bound n,
        predictableDyadicSimple_brownian_partition_last hT g h_meas M h_bound m]
  have h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i) :=
    fun n => predictableDyadicSimple_brownian_adapted W hT g h_meas M h_bound h_progMeas n
  have h_norm_tendsto :=
    predictableDyadicSimple_brownian_eval_norm_tendsto_bounded
      (P := P) hT g h_meas M h_bound
  -- L²-Cauchy: from L²-Tendsto via the generic helper.
  have h_L2_diff := predictableDyadicSimple_brownian_L2_converges
    (P := P) hT g h_meas M h_bound
  have h_eval_meas : ∀ n,
      Measurable (fun (p : Ω × ℝ) => (G n).eval p.2 p.1) :=
    fun n => predictableDyadicSimple_brownian_eval_jointly_measurable
      hT g h_meas M h_bound n
  have h_cauchy_eval : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ n m : ℕ,
      N ≤ n → N ≤ m →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(G n).eval s ω - (G m).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ε :=
    L2_cauchy_of_L2_tendsto_brownian (P := P) (T := T)
      G g h_eval_meas h_meas h_L2_diff
  exact exists_itoIntegralL2_brownian (P := P) W hT G h_eq h_adapt h_cauchy_eval g
    h_norm_tendsto

set_option maxHeartbeats 1600000 in
-- maxHeartbeats: typechecker budget for proof-heavy goal below.
/-- **Unbounded progressively-measurable existence.** For progressively-measurable
`H : Ω → ℝ → ℝ` in `L²(Ω × [0,T], dP ⊗ ds)` (no bound assumed), there exists an
`Lp ℝ 2 P` element whose squared `eLpNorm` over `P` equals the full `L²(P × ds)`
norm of `H` over `[0,T]`.

Construction: diagonal lift across truncations. For each `n : ℕ`, the bounded
existence applied to `clip_n H` gives an explicit dyadic SimplePredictable
sequence; pick the diagonal index `max n (N_seq n)` with `N_seq n` chosen so that
the bounded approximation is within `1/(n+1)` of `clip_n H` in L². Combine
truncation L²-convergence with the diagonal estimate via the standard
`(a+b)² ≤ 2(a²+b²)` triangle. Then apply the bounded theorem with `clip_n H`
on the diagonal sequence + `exists_itoIntegralL2_brownian`. -/
theorem exists_itoIntegralL2_brownian_progMeas
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ Mlp : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Truncation helpers (mirrored from adaptedSimple_dense_L2_brownian).
  have h_clip_bound : ∀ M : ℕ, ∀ ω s,
      |max (-(M : ℝ)) (min (M : ℝ) (H ω s))| ≤ (M : ℝ) := by
    intro M ω s
    have h_M_nn : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    rw [abs_le]
    refine ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  have h_clip_meas : ∀ M : ℕ, Measurable
      (Function.uncurry (fun (ω : Ω) (s : ℝ) =>
        max (-(M : ℝ)) (min (M : ℝ) (H ω s)))) := by
    intro M
    have h : Measurable (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by fun_prop
    exact h.comp h_meas
  have h_clip_progMeas : ∀ M : ℕ, ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => max (-(M : ℝ)) (min (M : ℝ) (H p.1 p.2))) := by
    intro M t
    have h_clip_cont : Continuous (fun x : ℝ => max (-(M : ℝ)) (min (M : ℝ) x)) := by
      fun_prop
    exact h_clip_cont.comp_stronglyMeasurable (h_progMeas t)
  -- Bounded existence on each clipped function.
  have h_bdd : ∀ M : ℕ, ∃ Mlp_M : MeasureTheory.Lp ℝ 2 P,
      MeasureTheory.eLpNorm (↑↑Mlp_M : Ω → ℝ) 2 P ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖max (-(M : ℝ)) (min (M : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
    fun M => exists_itoIntegralL2_brownian_progMeas_bounded W hT
      (fun ω s => max (-(M : ℝ)) (min (M : ℝ) (H ω s)))
      (h_clip_meas M) (h_clip_progMeas M) (M : ℝ) (h_clip_bound M)
  -- Pick N_seq for the diagonal: for each n, choose k ≥ N_seq n such that the
  -- L²-distance from clip_n H to the dyadic eval at depth k is ≤ 1/(n+1).
  have h_N : ∀ n : ℕ, ∃ N : ℕ, ∀ k ≥ N,
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s)) -
          (predictableDyadicSimple_brownian hT
            (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
            (h_clip_meas n) (n : ℝ) (h_clip_bound n) k).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    have h_eps : ((n : ℝ≥0∞) + 1)⁻¹ > 0 := by
      apply ENNReal.inv_pos.mpr
      exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top _, by simp⟩
    have h_L2 := predictableDyadicSimple_brownian_L2_converges (P := P) hT
      (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (h_clip_meas n) (n : ℝ) (h_clip_bound n)
    exact (ENNReal.tendsto_atTop_zero.mp h_L2) _ h_eps
  choose N_seq h_N_seq using h_N
  -- Diagonal sequence: G n = dyadic for clip_n H at depth (max n (N_seq n)).
  set G : ℕ → SimplePredictable Ω T := fun n =>
    predictableDyadicSimple_brownian hT
      (fun ω s => max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
      (h_clip_meas n) (n : ℝ) (h_clip_bound n) (max n (N_seq n)) with hG_def
  -- Properties of G.
  have h_eq : ∀ n m : ℕ,
      (G n).partition (Fin.last (G n).N)
        = (G m).partition (Fin.last (G m).N) := by
    intro n m
    rw [hG_def]
    rw [predictableDyadicSimple_brownian_partition_last hT _
          (h_clip_meas n) (n : ℝ) (h_clip_bound n) (max n (N_seq n)),
        predictableDyadicSimple_brownian_partition_last hT _
          (h_clip_meas m) (m : ℝ) (h_clip_bound m) (max m (N_seq m))]
  have h_adapt : ∀ n : ℕ, ∀ i : Fin (G n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((G n).partition i.castSucc)) ((G n).ξ i) := by
    intro n i
    exact predictableDyadicSimple_brownian_adapted W hT _
      (h_clip_meas n) (n : ℝ) (h_clip_bound n) (h_clip_progMeas n) (max n (N_seq n)) i
  have h_eval_meas : ∀ n,
      Measurable (fun (p : Ω × ℝ) => (G n).eval p.2 p.1) :=
    fun n => SimplePredictable.eval_jointly_measurable (G n)
  -- L²-convergence of G to H: diagonal lift.
  have h_trunc := truncation_L2_converges_brownian H h_meas h_sq_int (T := T)
  have h_L2_diff : Filter.Tendsto
      (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_atTop_zero] at h_trunc ⊢
    intro ε hε_pos
    have hε4_pos : (0 : ℝ≥0∞) < ε / 4 := by
      rw [ENNReal.div_pos_iff]
      refine ⟨hε_pos.ne', ?_⟩
      decide
    obtain ⟨N₁, hN₁⟩ := h_trunc (ε / 4) hε4_pos
    have h_inv_tendsto : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹)
        Filter.atTop (nhds 0) := by
      have h := ENNReal.tendsto_inv_nat_nhds_zero
      have hcomp :
          Filter.Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
        h.comp (Filter.tendsto_add_atTop_nat 1)
      simpa [Nat.cast_add, Nat.cast_one] using hcomp
    obtain ⟨N₂, hN₂⟩ := (ENNReal.tendsto_atTop_zero.mp h_inv_tendsto) (ε / 4) hε4_pos
    refine ⟨max N₁ N₂, ?_⟩
    intro n hn
    have hn₁ : N₁ ≤ n := le_of_max_le_left hn
    have hn₂ : N₂ ≤ n := le_of_max_le_right hn
    -- Pointwise (a + b)² ≤ 2(a² + b²) splitting:
    -- ‖H - (G n).eval‖² ≤ 2 ‖H - clip_n H‖² + 2 ‖clip_n H - (G n).eval‖².
    have h_pointwise : ∀ ω s,
        (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ≤ 2 * ((‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
              + (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                    - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2) := by
      intro ω s
      have h_sum : (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
          + (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
              - (G n).eval s ω)
          = H ω s - (G n).eval s ω := by ring
      have := sq_nnnorm_add_le_two_mul_brownian
        (H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s)))
        (max (-(n : ℝ)) (min (n : ℝ) (H ω s))
          - (G n).eval s ω)
      rw [h_sum] at this
      exact this
    set A : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        with hA
    set B : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
                      - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
    set C : Ω → ℝ → ℝ≥0∞ :=
      fun ω s => (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2 with hC
    have h_C_le : ∀ ω s, C ω s ≤ 2 * (A ω s + B ω s) := h_pointwise
    have h_s_le : ∀ ω,
        (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume) ≤
          2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
      intro ω
      calc (∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume)
          ≤ ∫⁻ s in Set.Icc (0 : ℝ) T, 2 * (A ω s + B ω s) ∂volume :=
            MeasureTheory.lintegral_mono (h_C_le ω)
        _ = 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, (A ω s + B ω s) ∂volume := by
            rw [MeasureTheory.lintegral_const_mul']
            simp
        _ = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
            + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) := by
            congr 1
            rw [MeasureTheory.lintegral_add_left']
            have h_meas_A_s : Measurable (fun s => A ω s) := by
              simp only [hA]
              have h1 : Measurable (fun s =>
                  ‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊) := by fun_prop
              exact (h1.coe_nnreal_ennreal).pow_const 2
            exact h_meas_A_s.aemeasurable
    have h_double_le :
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
        ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
      calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, C ω s ∂volume ∂P)
          ≤ ∫⁻ ω,
              2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
                + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P :=
            MeasureTheory.lintegral_mono h_s_le
        _ = 2 * ∫⁻ ω,
              ((∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume)
                + ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume) ∂P := by
            rw [MeasureTheory.lintegral_const_mul']
            simp
        _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, A ω s ∂volume ∂P)
            + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, B ω s ∂volume ∂P) := by
            congr 1
            rw [MeasureTheory.lintegral_add_left']
            have h_meas_A_pair : Measurable (fun (q : Ω × ℝ) => A q.1 q.2) := by
              simp only [hA]
              exact ((by fun_prop : Measurable (fun (q : Ω × ℝ) =>
                ‖H q.1 q.2
                  - max (-(n : ℝ))
                      (min (n : ℝ) (H q.1 q.2))‖₊)).coe_nnreal_ennreal).pow_const 2
            exact (Measurable.lintegral_prod_right'
              (ν := volume.restrict (Set.Icc (0:ℝ) T)) h_meas_A_pair).aemeasurable
    have h_first : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - max (-(n : ℝ)) (min (n : ℝ) (H ω s))‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ε / 4 := hN₁ n hn₁
    have h_second : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖max (-(n : ℝ)) (min (n : ℝ) (H ω s))
            - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P) ≤ ε / 4 := by
      have h_max_ge : N_seq n ≤ max n (N_seq n) := le_max_right _ _
      exact (h_N_seq n (max n (N_seq n)) h_max_ge).trans (hN₂ n hn₂)
    calc (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H ω s - (G n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
        ≤ 2 * (ε / 4 + ε / 4) := by
          refine h_double_le.trans ?_
          exact mul_le_mul_right (add_le_add h_first h_second) _
      _ = ε := by
          rw [← two_mul, ← mul_assoc, show (2 : ℝ≥0∞) * 2 = 4 from by norm_num]
          exact ENNReal.mul_div_cancel (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by simp)
  -- L²-Cauchy from L²-convergence.
  have h_cauchy_eval := L2_cauchy_of_L2_tendsto_brownian (P := P) (T := T)
    G H h_eval_meas h_meas h_L2_diff
  -- Norm-tendsto from the general lemma.
  have h_norm_tendsto := lintegral_sq_eval_tendsto_of_diff_tendsto_zero_brownian
    (μ := P) (T := T) H h_meas (fun n => (G n).eval) h_eval_meas h_L2_diff
  -- Apply exists_itoIntegralL2_brownian.
  exact exists_itoIntegralL2_brownian (P := P) W hT G h_eq h_adapt h_cauchy_eval H
    h_norm_tendsto

/-- **L²-Itô isometry via existence (Brownian).** For progressively-measurable
`H ∈ L²(Ω × [0,T], dP ⊗ ds)`, there is a `(stochasticInt : Ω → ℝ) ∈ L²(P)`
satisfying the Itô L² isometry on `[0,T]`:
`∫⁻ ω, ‖stochasticInt ω‖₊² = ∫⁻ ω, ∫⁻ s in Icc 0 T, ‖H ω s‖₊²`.

This is a direct extraction from `exists_itoIntegralL2_brownian_progMeas`, with
`stochasticInt` exposed as an `Ω → ℝ` function (rather than an `Lp` element) plus
the AEStronglyMeasurable + isometry conjuncts.

This is the existence form of the Itô isometry — it does **not** define a single
`stochasticIntegral : ℝ → Ω → ℝ` across all `t`. Constructing such a unified
process (with the additional martingale + quadVar properties) is the strong-exists
task; this lemma delivers conjunct 3 (isometry) at fixed `T` axiom-cleanly. -/
theorem itoIsometry_brownian_existence
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ stochasticInt : Ω → ℝ,
      MeasureTheory.AEStronglyMeasurable stochasticInt P ∧
      ∫⁻ ω, (‖stochasticInt ω‖₊ : ℝ≥0∞) ^ 2 ∂P
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  obtain ⟨Mlp, h_isometry⟩ :=
    exists_itoIntegralL2_brownian_progMeas W hT H h_meas h_progMeas h_sq_int
  refine ⟨↑↑Mlp, (MeasureTheory.Lp.aestronglyMeasurable Mlp), ?_⟩
  -- ∫⁻ ‖↑↑Mlp ω‖₊² ∂P = eLpNorm² Mlp 2 P (via eLpNorm_nnreal_pow_eq_lintegral)
  -- = ∫⁻ ‖H‖² (h_isometry).
  rw [show (∫⁻ ω, (‖(↑↑Mlp : Ω → ℝ) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = MeasureTheory.eLpNorm (↑↑Mlp : Ω → ℝ) 2 P ^ (2 : ℝ) from ?_]
  · exact h_isometry
  -- Bridge eLpNorm² to lintegral_sq.
  have h_pow_lemma := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
    (μ := P) (p := (2 : NNReal)) (f := (↑↑Mlp : Ω → ℝ))
    (by norm_num : (2 : NNReal) ≠ 0)
  have h_two_R : ((2 : NNReal) : ℝ) = (2 : ℝ) := by norm_num
  have h_two_ENNReal : ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) := by simp
  rw [h_two_ENNReal, h_two_R] at h_pow_lemma
  rw [h_pow_lemma]
  refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl

/-- **Conjunct-3 strong-exists for Brownian Itô (isometry at all T).**

For progressively-measurable `H ∈ ⋂_T L²(Ω × [0,T], dP ⊗ ds)`, there is a process
`F : ℝ → Ω → ℝ` satisfying the Itô L² isometry at every `T > 0`:
`∫⁻ ω, ‖F T ω‖₊² = ∫⁻ ω, ∫⁻ s in Icc 0 T, ‖H ω s‖₊²`.

Construction: per-`T` independent extraction from
`exists_itoIntegralL2_brownian_progMeas`. The resulting `F` does **not** carry
the martingale property (different `T`'s give independent Lp witnesses), but
delivers the isometry conjunct.

This is the **conjunct 3** of `stochasticIntegral_strong_exists_brownian` —
the isometry-only existential. Pairing with future conjunct-1/2 lemmas
(L²-limit-of-martingales + L²-limit-of-quadVar) closes the full strong-exists. -/
theorem stochasticIntegral_isometry_only_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : ℝ → Ω → ℝ,
      ∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  -- Per-T extraction: for each T, get an Ω → ℝ function with the isometry.
  refine ⟨fun T ω =>
    if hT : 0 < T then
      Classical.choose
        (itoIsometry_brownian_existence W hT H h_meas h_progMeas
          (h_sq_int_global T hT)) ω
    else 0, ?_⟩
  intro T hT
  simp only [dif_pos hT]
  exact (Classical.choose_spec
    (itoIsometry_brownian_existence W hT H h_meas h_progMeas
      (h_sq_int_global T hT))).2

/-- **General two-time diagonal (`L²` second moment of a single increment).**
For `0 ≤ a < b` and an `F_a`-measurable `ξ`,
`∫⁻ ‖ξ·(W_b − W_a)‖² = (b − a)·∫⁻ ‖ξ‖²`. Generalizes `simpleIntegral_diagonal`
from partition points to arbitrary times — the foundational piece of the
intermediate-time isometry needed for the coherent `F` (axiom #5). Proof:
`ξ ⟂ (W_b − W_a)` (independence of an `F_a`-measurable r.v. from the future
increment, `joint_increment_independent`), then the Gaussian second moment
`∫⁻ ‖W_b − W_a‖² = b − a`. -/
lemma diagonal_increment_lint
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (ξ : Ω → ℝ)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a) ξ) :
    ∫⁻ ω, (‖ξ ω * (W.W b ω - W.W a ω)‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (b - a) * ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW_def
  have h_ξ_meas : Measurable ξ :=
    (h_adapt.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a)).measurable
  have h_ΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have h_nn_meas : Measurable (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  have h_indep_F_ΔW := W.joint_increment_independent ha hab
  have h_ξ_comap_le :
      MeasurableSpace.comap ξ inferInstance ≤
        ⨆ j ∈ Set.Iic a, MeasurableSpace.comap (W.W j) inferInstance := by
    have h_ξ_F_meas : @Measurable Ω ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a) _ ξ :=
      h_adapt.measurable
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have h_naturalFilter_eq :
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a
          = ⨆ j ∈ Set.Iic a, MeasurableSpace.comap (W.W j) inferInstance := by
      show (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a = _
      unfold LevyStochCalc.Brownian.Martingale.naturalFiltration
        MeasureTheory.Filtration.natural
      rfl
    rw [← h_naturalFilter_eq]
    exact h_ξ_F_meas hv
  have h_indep_ξ_ΔW : ProbabilityTheory.IndepFun ξ ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : @MeasurableSet Ω
        (⨆ j ∈ Set.Iic a, MeasurableSpace.comap (W.W j) inferInstance) u :=
      h_ξ_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW
    exact h_indep_F_ΔW u v hu_F hv
  have h_indep_norm_sq :
      ProbabilityTheory.IndepFun
        (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) P := by
    have := h_indep_ξ_ΔW.comp h_nn_meas h_nn_meas
    simpa [Function.comp] using this
  have h_norm_mul : ∀ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2
      = (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω
    rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞)
        = (‖ξ ω‖₊ : ℝ≥0∞) * (‖ΔW ω‖₊ : ℝ≥0∞) from by
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) = ((‖ξ ω * ΔW ω‖₊ : ℝ≥0) : ℝ≥0∞) from rfl]
      rw [show (‖ξ ω * ΔW ω‖₊ : ℝ≥0) = ‖ξ ω‖₊ * ‖ΔW ω‖₊ from nnnorm_mul _ _]
      push_cast; rfl]
    ring
  rw [show (∫⁻ ω, (‖ξ ω * ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      = ∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P from
    MeasureTheory.lintegral_congr h_norm_mul]
  rw [show (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 * (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) * (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) from rfl]
  have h_ξ_norm_sq_meas : Measurable (fun ω => (‖ξ ω‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  have h_ΔW_norm_sq_meas : Measurable (fun ω => (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2) := by fun_prop
  rw [ProbabilityTheory.lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
      h_ξ_norm_sq_meas h_ΔW_norm_sq_meas h_indep_norm_sq]
  have h_ΔW_sq_int : ∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (b - a) := by
    rw [show (∫⁻ ω, (‖ΔW ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 ∂(P.map ΔW) from
      (MeasureTheory.lintegral_map h_nn_meas h_ΔW_meas).symm]
    rw [W.increment_gaussian ha hab]
    have h_int_sq : MeasureTheory.Integrable (fun x : ℝ => x ^ 2)
        (ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩) := by
      have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 2
          (ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩) :=
        ProbabilityTheory.IsGaussian.memLp_id _ 2 (by simp)
      have h := h_memLp.integrable_norm_pow (p := 2) (by norm_num)
      convert h using 1; ext x; change x ^ 2 = ‖x‖ ^ 2; rw [Real.norm_eq_abs, sq_abs]
    have h_nn_sq : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 ⟨b - a, by linarith⟩]
        fun x : ℝ => x ^ 2 := by filter_upwards with x; positivity
    have h_norm_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := by
      intro x
      rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm_eq_enorm x |>.symm]
      rw [← ENNReal.ofReal_pow (norm_nonneg _)]
      rw [show ‖x‖ ^ 2 = x ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
    rw [show (∫⁻ x, (‖x‖₊ : ℝ≥0∞) ^ 2 ∂(ProbabilityTheory.gaussianReal 0
              ⟨b - a, by linarith⟩))
        = ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂(ProbabilityTheory.gaussianReal 0
              ⟨b - a, by linarith⟩) from
      MeasureTheory.lintegral_congr (fun x => h_norm_eq x)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_sq h_nn_sq]
    rw [LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨b - a, by linarith⟩]
    rfl
  rw [h_ΔW_sq_int, mul_comm]

/-- **General off-diagonal vanishing.** For two increments with the second
strictly after the first (`a₁ < b₁ ≤ a₂ < b₂`) and `Fᵢ`-measurable coefficients,
`∫ (ξ₁·(W_{b₁}−W_{a₁}))·(ξ₂·(W_{b₂}−W_{a₂})) = 0`. Generalizes
`simpleIntegral_offDiagonal` from partition points to arbitrary times. Proof:
`f := ξ₁·ΔW₁·ξ₂` is `F_{a₂}`-measurable, `ΔW₂ ⟂ F_{a₂}` with `𝔼[ΔW₂] = 0`, so
`𝔼[f·ΔW₂] = 𝔼[f]·0 = 0`. -/
lemma offDiagonal_increment_integral_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) ξ₂) :
    ∫ ω, (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)) ∂P = 0 := by
  set ΔW₁ : Ω → ℝ := fun ω => W.W b₁ ω - W.W a₁ ω with hΔW₁_def
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a₂)).measurable
  set f : Ω → ℝ := fun ω => ξ₁ ω * ΔW₁ ω * ξ₂ ω with hf_def
  have h_factored : (fun ω => (ξ₁ ω * ΔW₁ ω) * (ξ₂ ω * ΔW₂ ω)) = fun ω => f ω * ΔW₂ ω := by
    funext ω; simp only [hf_def]; ring
  rw [show (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)))
        = fun ω => f ω * ΔW₂ ω from h_factored]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) (W.W b₁) :=
    (MeasureTheory.Filtration.stronglyAdapted_natural (u := W.W)
      (fun u => (W.measurable_eval u).stronglyMeasurable) b₁).mono
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) (W.W a₁) :=
    (MeasureTheory.Filtration.stronglyAdapted_natural (u := W.W)
      (fun u => (W.measurable_eval u).stronglyMeasurable) a₁).mono
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) ξ₁ :=
    hadapt₁.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) f :=
    (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas)).mul hadapt₂
  have h_indep_F_ΔW₂ := W.joint_increment_independent ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le :
      MeasurableSpace.comap f inferInstance ≤
        ⨆ jj ∈ Set.Iic a₂, MeasurableSpace.comap (W.W jj) inferInstance := by
    have h_f_F_measurable : @Measurable Ω ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) _ f :=
      h_f_F_meas.measurable
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have h_naturalFilter_eq :
        (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂
          = ⨆ jj ∈ Set.Iic a₂, MeasurableSpace.comap (W.W jj) inferInstance := by
      show (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂ = _
      unfold LevyStochCalc.Brownian.Martingale.naturalFiltration
        MeasureTheory.Filtration.natural
      rfl
    rw [← h_naturalFilter_eq]
    exact h_f_F_measurable hv
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    have hu_F : @MeasurableSet Ω
        (⨆ jj ∈ Set.Iic a₂, MeasurableSpace.comap (W.W jj) inferInstance) u :=
      h_f_comap_le u hu
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v hu_F hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := by
    rw [show ∫ ω, ΔW₂ ω ∂P = ∫ x, x ∂(P.map ΔW₂) from
      (MeasureTheory.integral_map h_ΔW₂_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (id : ℝ → ℝ) _)).symm]
    rw [W.increment_gaussian ha₂_nn h₂]
    exact ProbabilityTheory.integral_id_gaussianReal
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl]
  rw [h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable]
  rw [h_ΔW₂_mean, mul_zero]

/-- **Square-integrability of a Brownian increment** over `[s,t]` (general `s<t`).
A non-`private` companion of `ItoSimple`'s helper, needed below. -/
lemma increment_sq_integrable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    MeasureTheory.Integrable (fun ω => (W.W t ω - W.W s ω) ^ 2) P := by
  have h_meas : Measurable (fun ω => W.W t ω - W.W s ω) :=
    (W.measurable_eval t).sub (W.measurable_eval s)
  rw [show (fun ω => (W.W t ω - W.W s ω) ^ 2)
        = (fun x : ℝ => x ^ 2) ∘ (fun ω => W.W t ω - W.W s ω) from rfl]
  rw [(MeasureTheory.integrable_map_measure (μ := P) (f := fun ω => W.W t ω - W.W s ω)
      (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2)
        (P.map (fun ω => W.W t ω - W.W s ω))) h_meas.aemeasurable).symm]
  rw [W.increment_gaussian hs hst]
  have h := (ProbabilityTheory.IsGaussian.memLp_id
    (ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) 2 (by simp)).integrable_norm_pow
    (p := 2) (by norm_num)
  convert h using 1; ext x; change x ^ 2 = ‖x‖ ^ 2; rw [Real.norm_eq_abs, sq_abs]

/-- **General two-time diagonal, Bochner form.** `∫ (ξ·(W_b−W_a))² = (b−a)·∫ ξ²`
for `0 ≤ a < b`, `ξ` `F_a`-measurable and bounded (`|ξ| ≤ M`). Bochner companion
of `diagonal_increment_lint`, for the Bochner sum-expansion in the isometry. -/
lemma diagonal_increment_bochner
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (ξ : Ω → ℝ)
    (h_adapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a) ξ)
    (M : ℝ) (h_bound : ∀ ω, |ξ ω| ≤ M) :
    ∫ ω, (ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P = (b - a) * ∫ ω, (ξ ω) ^ 2 ∂P := by
  have hξ_meas : Measurable ξ :=
    (h_adapt.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a)).measurable
  have h_norm_sq_eq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm_eq_enorm x |>.symm]
    rw [← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [show ‖x‖ ^ 2 = x ^ 2 from by rw [Real.norm_eq_abs, sq_abs]]
  have h_lint := diagonal_increment_lint W ha hab ξ h_adapt
  rw [show (∫⁻ ω, (‖ξ ω * (W.W b ω - W.W a ω)‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((ξ ω * (W.W b ω - W.W a ω)) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  rw [show (∫⁻ ω, (‖ξ ω‖₊ : ℝ≥0∞) ^ 2 ∂P) = ∫⁻ ω, ENNReal.ofReal ((ξ ω) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq_eq _)] at h_lint
  have h_xi_sq_bound : ∀ ω, (ξ ω) ^ 2 ≤ M ^ 2 := fun ω =>
    sq_le_sq' (neg_le_of_abs_le (h_bound ω)) (le_of_abs_le (h_bound ω))
  have h_int_xi_sq : MeasureTheory.Integrable (fun ω => (ξ ω) ^ 2) P := by
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) (hξ_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h_xi_sq_bound ω
  have h_int_ΔW_sq := increment_sq_integrable W ha hab
  have h_int_aN_sq : MeasureTheory.Integrable
      (fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2) P := by
    rw [show (fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2)
            = fun ω => (ξ ω) ^ 2 * (W.W b ω - W.W a ω) ^ 2 from by funext ω; ring]
    refine MeasureTheory.Integrable.bdd_mul (c := M ^ 2) h_int_ΔW_sq
      (hξ_meas.pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact h_xi_sq_bound ω
  have h_nn_xi_sq : 0 ≤ᵐ[P] fun ω => (ξ ω) ^ 2 := by filter_upwards with ω; positivity
  have h_nn_aN_sq : 0 ≤ᵐ[P] fun ω => (ξ ω * (W.W b ω - W.W a ω)) ^ 2 := by
    filter_upwards with ω; positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_aN_sq h_nn_aN_sq] at h_lint
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int_xi_sq h_nn_xi_sq] at h_lint
  have h_dt_nn : 0 ≤ b - a := sub_nonneg.mpr (le_of_lt hab)
  rw [show ENNReal.ofReal (b - a) * ENNReal.ofReal (∫ ω, (ξ ω) ^ 2 ∂P)
          = ENNReal.ofReal ((b - a) * ∫ ω, (ξ ω) ^ 2 ∂P) from
    (ENNReal.ofReal_mul h_dt_nn).symm] at h_lint
  exact (ENNReal.ofReal_eq_ofReal_iff
    (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _))
    (mul_nonneg h_dt_nn (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)))).mp h_lint

/-- **Integrability of a cross product of two (possibly degenerate) increments.**
`(ξ₁·(W_{b₁}−W_{a₁}))·(ξ₂·(W_{b₂}−W_{a₂}))` is integrable for bounded `ξ`s and
`0 ≤ aₖ ≤ bₖ`. Degenerate (`aₖ = bₖ`) increments are `0`. Used (with clamped
endpoints) in the intermediate-time Bochner expansion. -/
lemma cross_increment_integrable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (hab₁ : a₁ ≤ b₁) (ha₂ : 0 ≤ a₂) (hab₂ : a₂ ≤ b₂)
    (ξ₁ ξ₂ : Ω → ℝ) (hξ₁meas : Measurable ξ₁) (hξ₂meas : Measurable ξ₂)
    (M₁ : ℝ) (hbd₁ : ∀ ω, |ξ₁ ω| ≤ M₁) (M₂ : ℝ) (hbd₂ : ∀ ω, |ξ₂ ω| ≤ M₂) :
    MeasureTheory.Integrable
      (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) P := by
  have h_meas₁ : Measurable (fun ω => W.W b₁ ω - W.W a₁ ω) :=
    (W.measurable_eval b₁).sub (W.measurable_eval a₁)
  have h_meas₂ : Measurable (fun ω => W.W b₂ ω - W.W a₂ ω) :=
    (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have sq_int : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
      MeasureTheory.Integrable (fun ω => (W.W b ω - W.W a ω) ^ 2) P := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h_eq | h_lt
    · rw [show (fun ω => (W.W b ω - W.W a ω) ^ 2) = fun _ => (0 : ℝ) from by
        funext ω; rw [← h_eq]; ring]
      exact MeasureTheory.integrable_const 0
    · exact increment_sq_integrable W ha h_lt
  have h_int_i_sq := sq_int ha₁ hab₁
  have h_int_j_sq := sq_int ha₂ hab₂
  have h_int_ΔW : MeasureTheory.Integrable
      (fun ω => (W.W b₁ ω - W.W a₁ ω) * (W.W b₂ ω - W.W a₂ ω)) P := by
    refine MeasureTheory.Integrable.mono'
      (MeasureTheory.Integrable.add (h_int_i_sq.const_mul (1 / 2 : ℝ))
        (h_int_j_sq.const_mul (1 / 2 : ℝ))) (h_meas₁.mul h_meas₂).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_mul]
    have h : |W.W b₁ ω - W.W a₁ ω| * |W.W b₂ ω - W.W a₂ ω|
        ≤ (1 / 2) * (W.W b₁ ω - W.W a₁ ω) ^ 2 + (1 / 2) * (W.W b₂ ω - W.W a₂ ω) ^ 2 := by
      nlinarith [sq_abs (W.W b₁ ω - W.W a₁ ω), sq_abs (W.W b₂ ω - W.W a₂ ω),
        sq_nonneg (|W.W b₁ ω - W.W a₁ ω| - |W.W b₂ ω - W.W a₂ ω|)]
    exact h
  rw [show (fun ω => (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω)))
        = fun ω => (ξ₁ ω * ξ₂ ω)
            * ((W.W b₁ ω - W.W a₁ ω) * (W.W b₂ ω - W.W a₂ ω)) from by funext ω; ring]
  refine MeasureTheory.Integrable.bdd_mul (c := |M₁| * |M₂|) h_int_ΔW
    (hξ₁meas.mul hξ₂meas).aestronglyMeasurable ?_
  filter_upwards with ω
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (le_trans (hbd₁ ω) (le_abs_self _)) (le_trans (hbd₂ ω) (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

/-- **Clamped Bochner second moment of `simpleIntegral W H t`.** For `0 ≤ t`,
`∫ (simpleIntegral W H t)² = ∑ᵢ (pᵢ₊₁∧t − pᵢ∧t)·∫ ξᵢ²`. Cross terms vanish
(`offDiagonal_increment_integral_zero`), diagonal terms give the clamped lengths
(`diagonal_increment_bochner`); degenerate clamped increments are `0`. The core
of the intermediate-time isometry for the coherent L²-Itô integral (#5). -/
lemma simpleIntegral_sq_bochner_clamped
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫ ω, (simpleIntegral W H t ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
          * ∫ ω, (H.ξ i ω) ^ 2 ∂P := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
      - W.W (min (H.partition i.castSucc) t) ω) with hterm
  have h_a_le_b : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t ≤ min (H.partition i.succ) t :=
    fun i => min_le_min_right t
      (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  have h_a_nn : ∀ i : Fin H.N, 0 ≤ min (H.partition i.castSucc) t :=
    fun i => le_min (h_part_nn i) ht_nn
  -- In the genuine case, the lower clamp equals the partition point.
  have h_acs : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t < min (H.partition i.succ) t →
        min (H.partition i.castSucc) t = H.partition i.castSucc := by
    intro i hlt
    refine min_eq_left ?_
    by_contra h
    rw [not_le] at h
    rw [min_eq_right h.le,
      min_eq_right (h.le.trans (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ)))] at hlt
    exact lt_irrefl t hlt
  -- integrability of every cross product
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => term i ω * term j ω) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    exact cross_increment_integrable W (h_a_nn i) (h_a_le_b i) (h_a_nn j) (h_a_le_b j)
      (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj
  -- off-diagonal vanishing for i < j
  have h_off : ∀ i j : Fin H.N, i < j → ∫ ω, term i ω * term j ω ∂P = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le (h_a_le_b j) with hj_eq | hj_lt
    · -- j-increment degenerate
      rw [show (fun ω => term i ω * term j ω) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hj_eq]; ring]
      exact MeasureTheory.integral_zero _ _
    · rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
      · -- i-increment degenerate
        rw [show (fun ω => term i ω * term j ω) = fun _ => (0 : ℝ) from by
          funext ω; simp only [hterm]; rw [← hi_eq]; ring]
        exact MeasureTheory.integral_zero _ _
      · -- both genuine: apply the general off-diagonal
        have hbi_le_aj : min (H.partition i.succ) t ≤ H.partition j.castSucc := by
          refine le_trans (min_le_left _ _) ?_
          exact H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij)
        have h := offDiagonal_increment_integral_zero W (h_part_nn i)
          (by rw [← h_acs i hi_lt]; exact hi_lt)
          hbi_le_aj
          (by rw [← h_acs j hj_lt]; exact hj_lt)
          (H.ξ i) (H.ξ j) (h_adapt i) (h_adapt j)
        rw [show (fun ω => term i ω * term j ω)
              = fun ω => (H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                  - W.W (H.partition i.castSucc) ω))
                * (H.ξ j ω * (W.W (min (H.partition j.succ) t) ω
                  - W.W (H.partition j.castSucc) ω)) from by
          funext ω; simp only [hterm]; rw [h_acs i hi_lt, h_acs j hj_lt]]
        exact h
  rw [show (fun ω => (simpleIntegral W H t ω) ^ 2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
    funext ω
    rw [show simpleIntegral W H t ω = ∑ i : Fin H.N, term i ω from rfl, sq,
      Finset.sum_mul_sum]]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => h_cross i j),
    Finset.sum_eq_single i]
  · -- diagonal j = i
    rw [show (fun ω => term i ω * term i ω) = fun ω => (term i ω) ^ 2 from by
      funext ω; ring]
    rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
    · rw [show (fun ω => (term i ω) ^ 2) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hi_eq]; ring, MeasureTheory.integral_zero,
        ← hi_eq]; ring
    · obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
      rw [show (fun ω => (term i ω) ^ 2)
            = fun ω => (H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
                - W.W (H.partition i.castSucc) ω)) ^ 2 from by
        funext ω; simp only [hterm]; rw [h_acs i hi_lt]]
      rw [diagonal_increment_bochner W (h_part_nn i)
        (by rw [← h_acs i hi_lt]; exact hi_lt) (H.ξ i) (h_adapt i) Mi hMi]
      rw [h_acs i hi_lt]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => term i ω * term j ω) = fun ω => term j ω * term i ω from by
        funext ω; ring]
      exact h_off j i h_lt
    · exact h_off i j h_gt
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Clamped inner integral.** Per `ω`,
`∫⁻_{[0,t]} ‖H.eval s ω‖² ds = ∑ᵢ ofReal(pᵢ₊₁∧t − pᵢ∧t)·‖ξᵢ ω‖²` (`t ≥ 0`).
Clamped companion of `lintegral_eval_sq`: each level-set contributes the length
of `(pᵢ, pᵢ₊₁] ∩ [0,t]`. -/
lemma lintegral_eval_sq_clamped {T : ℝ} (H : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∑ i : Fin H.N,
        ENNReal.ofReal (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
          * (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  rw [show (fun s => (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2)
      = (fun s => ∑ i : Fin H.N,
          (Set.Ioc (H.partition i.castSucc) (H.partition i.succ)).indicator
            (fun _ => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) s) from
    funext (eval_sq_eq_sum_indicator H · ω)]
  rw [MeasureTheory.lintegral_finsetSum _
    (fun i _ => (Measurable.indicator (by fun_prop) measurableSet_Ioc))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.lintegral_indicator measurableSet_Ioc,
    MeasureTheory.setLIntegral_const,
    MeasureTheory.Measure.restrict_apply measurableSet_Ioc]
  -- volume ((pᵢ, pᵢ₊₁] ∩ [0,t]) = ofReal (pᵢ₊₁∧t − pᵢ∧t)
  have h_inter : Set.Ioc (H.partition i.castSucc) (H.partition i.succ) ∩ Set.Icc 0 t
      = Set.Ioc (H.partition i.castSucc) (min (H.partition i.succ) t) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc, le_min_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _, h4⟩; exact ⟨h1, h2, h4⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, le_of_lt (lt_of_le_of_lt (h_part_nn i) h1), h3⟩
  rw [h_inter, Real.volume_Ioc, mul_comm]
  congr 1
  rcases le_or_gt (H.partition i.castSucc) t with h | h
  · rw [min_eq_left h]
  · have hpsucc : min (H.partition i.succ) t = t :=
      min_eq_right (h.le.trans (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ)))
    rw [hpsucc, min_eq_right h.le,
      ENNReal.ofReal_of_nonpos (by linarith : t - H.partition i.castSucc ≤ 0)]
    simp

/-- **Intermediate-time L²-isometry for the simple Brownian integral.** For
`0 ≤ t`, `∫⁻ ‖simpleIntegral W H t‖² = ∫⁻ ∫⁻_{[0,t]} ‖H.eval‖²`. The general-`t`
companion of `simpleIntegral_isometry`; combines the clamped Bochner assembly
(LHS) with the clamped inner integral (RHS) through `ENNReal.ofReal`. This is the
hinge for the coherent L²-Itô integral (axiom #5). -/
lemma simpleIntegral_intermediate_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have h_part_nn : ∀ i : Fin H.N, 0 ≤ H.partition i.castSucc := fun i => by
    have : H.partition 0 ≤ H.partition i.castSucc :=
      H.partition_strictMono.monotone (Fin.zero_le _)
    rw [H.partition_zero] at this; exact this
  have h_a_le_b : ∀ i : Fin H.N,
      min (H.partition i.castSucc) t ≤ min (H.partition i.succ) t :=
    fun i => min_le_min_right t (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from ofReal_norm_eq_enorm x |>.symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  have hξsqmeas : ∀ i : Fin H.N, Measurable (fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) :=
    fun i => (((H.ξ_measurable i).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hξ_int : ∀ i : Fin H.N, MeasureTheory.Integrable (fun ω => (H.ξ i ω) ^ 2) P := by
    intro i; obtain ⟨M, hM⟩ := H.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (g := fun _ : Ω => M ^ 2)
      (MeasureTheory.integrable_const _) ((H.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  have hξ_lint : ∀ i : Fin H.N,
      ∫⁻ ω, (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (H.ξ i ω) ^ 2 ∂P) := by
    intro i
    rw [show (fun ω => (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2) = fun ω => ENNReal.ofReal ((H.ξ i ω) ^ 2) from
      funext (fun ω => h_norm_sq _)]
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hξ_int i)
      (by filter_upwards with ω; positivity)]
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (min (H.partition i.succ) t) ω
      - W.W (min (H.partition i.castSucc) t) ω) with hterm
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => term i ω * term j ω) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    exact cross_increment_integrable W (le_min (h_part_nn i) ht_nn) (h_a_le_b i)
      (le_min (h_part_nn j) ht_nn) (h_a_le_b j)
      (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj
  have h_si_int : MeasureTheory.Integrable (fun ω => (simpleIntegral W H t ω) ^ 2) P := by
    rw [show (fun ω => (simpleIntegral W H t ω) ^ 2)
          = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
      funext ω
      rw [show simpleIntegral W H t ω = ∑ i : Fin H.N, term i ω from rfl, sq,
        Finset.sum_mul_sum]]
    exact MeasureTheory.integrable_finsetSum _
      (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))
  rw [show (∫⁻ ω, (‖simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((simpleIntegral W H t ω) ^ 2) ∂P from
    MeasureTheory.lintegral_congr (fun ω => h_norm_sq _)]
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_si_int
    (by filter_upwards with ω; positivity)]
  rw [simpleIntegral_sq_bochner_clamped W H h_adapt ht_nn]
  rw [show (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        = fun ω => ∑ i : Fin H.N,
            ENNReal.ofReal (min (H.partition i.succ) t - min (H.partition i.castSucc) t)
              * (‖H.ξ i ω‖₊ : ℝ≥0∞) ^ 2 from
    funext (fun ω => lintegral_eval_sq_clamped H ω ht_nn)]
  rw [MeasureTheory.lintegral_finsetSum _ (fun i _ => (hξsqmeas i).const_mul _)]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg
    (sub_nonneg.mpr (h_a_le_b i)) (MeasureTheory.integral_nonneg (fun ω => sq_nonneg _)))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.lintegral_const_mul _ (hξsqmeas i),
    ENNReal.ofReal_mul (sub_nonneg.mpr (h_a_le_b i)), hξ_lint i]

/-- **`simpleIntegral W H t` is in `L²(P)` at every intermediate time `t ≤ T`.**
The `AEStronglyMeasurable` part is the finite-sum argument of
`simpleIntegral_memLp_brownian`; the `eLpNorm < ⊤` part uses the intermediate-time
isometry `∫⁻‖I_t‖² = ∫⁻∫⁻_{[0,t]}‖H.eval‖²` bounded by the (finite) endpoint
`∫⁻∫⁻_{[0,T]}‖H.eval‖²` via `Set.Icc` monotonicity (`t ≤ T`). Needed to treat
`fun t => simpleIntegral W H t` as an `L²` martingale for the orthogonal-increment
Cauchy estimate. -/
lemma simpleIntegral_memLp_intermediate_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    MeasureTheory.MemLp (fun ω => simpleIntegral W H t ω) 2 P := by
  refine ⟨?_, ?_⟩
  · refine Measurable.aestronglyMeasurable ?_
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact (H.ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  · rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
        (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤)]
    rw [show (2 : ℝ≥0∞).toReal = 2 from by simp]
    have h_rewrite : (fun ω => (‖simpleIntegral W H t ω‖ₑ : ℝ≥0∞) ^ (2 : ℝ))
          = (fun ω => (‖simpleIntegral W H t ω‖₊ : ℝ≥0∞) ^ 2) := by
      funext ω
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
    rw [h_rewrite, simpleIntegral_intermediate_isometry W H h_adapt ht_nn]
    -- bound `∫⁻∫⁻_{[0,t]} ≤ ∫⁻∫⁻_{[0,T]} < ⊤`.
    have h_fin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      rw [← simpleIntegral_isometry W hT H h_adapt]
      exact simpleIntegral_lintegral_sq_finite_brownian W hT H h_adapt
    refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun ω => ?_)) h_fin
    exact lintegral_mono_set (Set.Icc_subset_Icc_right htT)

/-- **General-time difference isometry.** For adapted `H₁, H₂` sharing the endpoint
`T`, the `L²(P)`-norm² of the integral difference at *any* `t ≥ 0` equals the
`L²(λ⊗P)`-norm² of their eval difference over `[0, t]`. The `min (·) t`-clamped
analogue of `diff_isometry_simple`: rewrite the integral difference as the integral
of `sub_on_common` (`simpleIntegral_sub_on_common_intermediate`), apply the
intermediate-time isometry, and unfold `eval` of `sub_on_common`. This is the exact
isometry underlying both `L²`-Cauchy-at-each-`t` and cross-horizon consistency. -/
lemma simpleIntegral_intermediate_diff_isometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₂.partition i.castSucc)) (H₂.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hLHS : ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (H₁.sub_on_common H₂ h_eq) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [SimplePredictable.simpleIntegral_sub_on_common_intermediate W H₁ H₂ h_eq t ω]
  rw [hLHS, simpleIntegral_intermediate_isometry W (H₁.sub_on_common H₂ h_eq)
      (SimplePredictable.sub_on_common_adapt W H₁ H₂ h_eq h_adapt₁ h_adapt₂) ht_nn]
  refine lintegral_congr (fun ω => ?_)
  refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
  rw [SimplePredictable.eval_sub_on_common H₁ H₂ h_eq s ω]

/-- **L¹-limit of martingales is a martingale.** If each `M n` is an
`ℱ`-martingale and `M n t → F t` in `L¹(μ)` for every `t` (with `F` adapted and
integrable), then `F` is an `ℱ`-martingale. The conditional expectation is an
`L¹`-contraction (`eLpNorm_one_condExp_le_eLpNorm`), so the martingale identity
`μ[M n t | ℱ s] =ᵐ M n s` passes to the limit. Reusable for the L²-Itô integral
(#5) and its compensated analogue (#6). -/
lemma martingale_of_tendsto_eLpNorm_one
    {m0 : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsFiniteMeasure μ] {ℱ : MeasureTheory.Filtration ℝ m0}
    {M : ℕ → ℝ → Ω → ℝ} {F : ℝ → Ω → ℝ}
    (hM : ∀ n, MeasureTheory.Martingale (M n) ℱ μ)
    (hMint : ∀ n t, MeasureTheory.Integrable (M n t) μ)
    (hadapt : MeasureTheory.StronglyAdapted ℱ F)
    (hint : ∀ t, MeasureTheory.Integrable (F t) μ)
    (htend : ∀ t, Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ) Filter.atTop (nhds 0)) :
    MeasureTheory.Martingale F ℱ μ := by
  refine ⟨hadapt, fun s t hst => ?_⟩
  have haesmC : MeasureTheory.AEStronglyMeasurable (μ[F t | ℱ s]) μ :=
    MeasureTheory.integrable_condExp.aestronglyMeasurable
  have haesm : MeasureTheory.AEStronglyMeasurable (μ[F t | ℱ s] - F s) μ :=
    haesmC.sub (hint s).1
  -- The target seminorm is bounded by `‖Mₙt − Ft‖₁ + ‖Mₙs − Fs‖₁` for every `n`.
  have hbound : ∀ n, MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
      ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
        + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
    intro n
    have hdecomp : (μ[F t | ℱ s] - F s)
        = (μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s) := by ring
    calc MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ
        = MeasureTheory.eLpNorm
            ((μ[F t | ℱ s] - μ[M n t | ℱ s]) + (μ[M n t | ℱ s] - F s)) 1 μ := by
          rw [hdecomp]
      _ ≤ MeasureTheory.eLpNorm (μ[F t | ℱ s] - μ[M n t | ℱ s]) 1 μ
          + MeasureTheory.eLpNorm (μ[M n t | ℱ s] - F s) 1 μ :=
          MeasureTheory.eLpNorm_add_le
            (haesmC.sub MeasureTheory.integrable_condExp.aestronglyMeasurable)
            (MeasureTheory.integrable_condExp.aestronglyMeasurable.sub (hint s).1) (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ := by
          gcongr
          · have h_sub : (μ[F t | ℱ s] - μ[M n t | ℱ s]) =ᵐ[μ] μ[F t - M n t | ℱ s] :=
              (MeasureTheory.condExp_sub (hint t) (hMint n t) (ℱ s)).symm
            rw [MeasureTheory.eLpNorm_congr_ae h_sub]
            calc MeasureTheory.eLpNorm (μ[F t - M n t | ℱ s]) 1 μ
                ≤ MeasureTheory.eLpNorm (F t - M n t) 1 μ :=
                  MeasureTheory.eLpNorm_one_condExp_le_eLpNorm (F t - M n t)
              _ = MeasureTheory.eLpNorm (M n t - F t) 1 μ := by
                  rw [show F t - M n t = -(M n t - F t) from by ring,
                      MeasureTheory.eLpNorm_neg]
          · refine le_of_eq (MeasureTheory.eLpNorm_congr_ae ?_)
            exact ((hM n).condExp_ae_eq hst).sub (Filter.EventuallyEq.refl _ (F s))
  -- Send `n → ∞`: the bound tends to `0`, so the (constant) target seminorm is `0`.
  have hzero : MeasureTheory.eLpNorm (μ[F t | ℱ s] - F s) 1 μ = 0 := by
    have htend2 : Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (M n t - F t) 1 μ
          + MeasureTheory.eLpNorm (M n s - F s) 1 μ) Filter.atTop (nhds 0) := by
      simpa using (htend t).add (htend s)
    refine le_antisymm ?_ bot_le
    exact le_of_tendsto_of_tendsto tendsto_const_nhds htend2
      (Filter.Eventually.of_forall hbound)
  rw [MeasureTheory.eLpNorm_eq_zero_iff haesm (by norm_num)] at hzero
  filter_upwards [hzero] with ω hω
  simpa [Pi.sub_apply, sub_eq_zero] using hω

/-- **L²-convergence ⇒ L¹-convergence** (probability measure). The `L¹` seminorm
is dominated by the `L²` seminorm when `μ` is a probability measure, so an
`L²`-null sequence is `L¹`-null. Bridges the `L²`-Cauchy approximating sequence
(`cauchySeq_simpleIntegralLp_brownian`) to the `L¹` hypothesis of
`martingale_of_tendsto_eLpNorm_one`. -/
lemma tendsto_eLpNorm_one_of_eLpNorm_two
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ]
    {g : ℕ → Ω → ℝ} (hg : ∀ n, MeasureTheory.AEStronglyMeasurable (g n) μ)
    (h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (g n) 1 μ)
      Filter.atTop (nhds 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds h2
    (fun _ => bot_le)
    (fun n => MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le (by norm_num) (hg n))

/-- **L² Hölder product.** `‖f·g‖₁ ≤ ‖f‖₂·‖g‖₂` (Cauchy–Schwarz). The
conjunct-2 (quadratic-variation) limit needs `aₙ²→a²` in `L¹` from `aₙ→a` in
`L²`, via `aₙ²−a² = (aₙ−a)(aₙ+a)` and this bound. -/
lemma eLpNorm_one_mul_le {μ : MeasureTheory.Measure Ω} {f g : Ω → ℝ}
    (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    MeasureTheory.eLpNorm (f * g) 1 μ
      ≤ MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
  have hpq : Real.HolderConjugate 2 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
  calc ∫⁻ x, ‖(f * g) x‖ₑ ∂μ
      = ∫⁻ x, ‖f x‖ₑ * ‖g x‖ₑ ∂μ := by
        refine lintegral_congr (fun x => ?_); rw [Pi.mul_apply, enorm_mul]
    _ ≤ (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ))
        * (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) :=
        ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hf.enorm hg.enorm
    _ = MeasureTheory.eLpNorm f 2 μ * MeasureTheory.eLpNorm g 2 μ := by
        rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
            MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
        norm_num

/-- **Squares converge in L¹ from L²-convergence.** If `aₙ → b` in `L²` (with
`‖b‖₂ < ⊤`) then `aₙ² → b²` in `L¹`. The conjunct-2 (quadratic-variation) engine.
Proof: `aₙ²−b² = (aₙ−b)(aₙ+b)`, bounded by `eLpNorm_one_mul_le` and the triangle
`‖aₙ+b‖₂ ≤ ‖aₙ−b‖₂ + 2‖b‖₂`, then squeezed. -/
lemma tendsto_eLpNorm_one_sq_sub
    {μ : MeasureTheory.Measure Ω} {a : ℕ → Ω → ℝ} {b : Ω → ℝ}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
    (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
      Filter.atTop (nhds 0) := by
  have hbound : ∀ n, MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ
      ≤ MeasureTheory.eLpNorm (a n - b) 2 μ
        * (MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ) := by
    intro n
    have hfac : (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) = (a n - b) * (a n + b) := by
      funext ω; simp only [Pi.mul_apply, Pi.sub_apply, Pi.add_apply]; ring
    rw [hfac]
    refine le_trans (eLpNorm_one_mul_le ((ha n).sub hb) ((ha n).add hb)) ?_
    gcongr
    calc MeasureTheory.eLpNorm (a n + b) 2 μ
        = MeasureTheory.eLpNorm ((a n - b) + (2 : ℝ) • b) 2 μ := by
          congr 1; funext ω; simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
            smul_eq_mul]; ring
      _ ≤ MeasureTheory.eLpNorm (a n - b) 2 μ + MeasureTheory.eLpNorm ((2 : ℝ) • b) 2 μ :=
          MeasureTheory.eLpNorm_add_le ((ha n).sub hb).aestronglyMeasurable
            (hb.aestronglyMeasurable.const_smul (2 : ℝ)) (by norm_num)
      _ ≤ MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ := by
          gcongr
          refine le_trans MeasureTheory.eLpNorm_const_smul_le (le_of_eq ?_)
          rw [show ‖(2 : ℝ)‖ₑ = (2 : ℝ≥0∞) from by simp [Real.enorm_eq_ofReal_abs]]
  have htend_bound : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ
        * (MeasureTheory.eLpNorm (a n - b) 2 μ + 2 * MeasureTheory.eLpNorm b 2 μ))
      Filter.atTop (nhds 0) := by
    have h1 := htend.add (tendsto_const_nhds (x := 2 * MeasureTheory.eLpNorm b 2 μ))
    have h2C : (2 : ℝ≥0∞) * MeasureTheory.eLpNorm b 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hbfin
    have := ENNReal.Tendsto.mul htend (Or.inr (by simpa using h2C)) h1
      (Or.inr (by norm_num))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend_bound
    (fun _ => bot_le) hbound

/-- **Orthogonal-increment identity for L² martingales.** For an `ℱ`-martingale
`M` on `ℝ` with square-integrable time-slices, the increment from `s` to `t ≥ s`
is `L²`-orthogonal to `M s`, giving the Pythagoras identity
`𝔼[(M t − M s)²] = 𝔼[(M t)²] − 𝔼[(M s)²]`. Cross term: `M s` is `ℱ s`-measurable,
so `𝔼[M s · M t] = 𝔼[M s · 𝔼[M t | ℱ s]] = 𝔼[(M s)²]` by the pull-out property and
the martingale identity. This underlies the increment isometry of the L² Itô
integral and the right-`L²`-continuity of its time-slices. -/
lemma integral_sq_increment_eq_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P :=
    hMs.integrable_mul hMt
  -- cross term: `∫ M s · M t = ∫ (M s)²` via pull-out + martingale identity.
  have h_cross : ∫ ω, M s ω * M t ω ∂P = ∫ ω, (M s ω) ^ 2 ∂P := by
    have h_pull : P[(fun ω => M s ω * M t ω) | ℱ s]
        =ᵐ[P] fun ω => M s ω * P[M t | ℱ s] ω := by
      have := MeasureTheory.condExp_mul_of_stronglyMeasurable_left
        (m := ℱ s) (hmart.stronglyAdapted s)
        (by simpa [Pi.mul_apply] using hcr) (hmart.integrable t)
      simpa [Pi.mul_apply] using this
    calc ∫ ω, M s ω * M t ω ∂P
        = ∫ ω, P[(fun ω => M s ω * M t ω) | ℱ s] ω ∂P :=
          (MeasureTheory.integral_condExp hm).symm
      _ = ∫ ω, M s ω * P[M t | ℱ s] ω ∂P := integral_congr_ae h_pull
      _ = ∫ ω, M s ω * M s ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hmart.condExp_ae_eq hst] with ω hω using by rw [hω]
      _ = ∫ ω, (M s ω) ^ 2 ∂P := by simp_rw [pow_two]
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P := hMt.integrable_sq
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P := hMs.integrable_sq
  calc ∫ ω, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun ω => ?_)); ring
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - 2 * (∫ ω, M s ω * M t ω ∂P) + ∫ ω, (M s ω) ^ 2 ∂P := by
        have e1 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
            = (∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω, (M s ω) ^ 2 ∂P :=
          integral_add (hMt2.sub (hcr.const_mul 2)) hMs2
        have e2 : ∫ ω, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
            = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, 2 * (M s ω * M t ω) ∂P :=
          integral_sub hMt2 (hcr.const_mul 2)
        have e3 : ∫ ω, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω, M s ω * M t ω ∂P :=
          integral_const_mul 2 _
        rw [e1, e2, e3]
    _ = (∫ ω, (M t ω) ^ 2 ∂P) - ∫ ω, (M s ω) ^ 2 ∂P := by rw [h_cross]; ring

/-- **Monotonicity of the second moment of an L² martingale.** Immediate from the
orthogonal-increment identity: `𝔼[(M t)²] − 𝔼[(M s)²] = 𝔼[(M t − M s)²] ≥ 0`. This
gives the `L²`-Cauchy property at every intermediate time `t ≤ T` from the
endpoint (`T`) `L²`-bound, since `M t − M' t` is itself a martingale. -/
lemma integral_sq_mono_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    ∫ ω, (M s ω) ^ 2 ∂P ≤ ∫ ω, (M t ω) ^ 2 ∂P := by
  have h := integral_sq_increment_eq_of_martingale hmart hMs hMt hst
  have h_nn : 0 ≤ ∫ ω, (M t ω - M s ω) ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg _)
  linarith [h, h_nn]

/-- **Cauchy-at-each-time bound for the simple integral.** For two adapted
simple integrands sharing the endpoint `T`, the `L²(P)`-distance of their integrals
at any intermediate time `t ≤ T` is bounded by the (endpoint) `L²(λ⊗P)`-distance of
their evals over `[0, T]`. The difference process `simpleIntegral W H₁ · −
simpleIntegral W H₂ ·` is a martingale (`Martingale.sub`), so its second moment is
monotone in time (`integral_sq_mono_of_martingale`), capping the `t`-value by the
`T`-value, which is the endpoint difference isometry `diff_isometry_simple`. This
upgrades the endpoint `L²`-Cauchy hypothesis to `L²`-Cauchy at *every* `t ≤ T`
without a general-`t` refinement re-derivation. -/
lemma simpleIntegral_lintegral_sq_sub_le_endpoint_brownian
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (H₁ H₂ : SimplePredictable Ω T)
    (h_eq : H₁.partition (Fin.last H₁.N) = H₂.partition (Fin.last H₂.N))
    (h_adapt₁ : ∀ i : Fin H₁.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₁.partition i.castSucc)) (H₁.ξ i))
    (h_adapt₂ : ∀ i : Fin H₂.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H₂.partition i.castSucc)) (H₂.ξ i))
    {t : ℝ} (ht_nn : 0 ≤ t) (htT : t ≤ T) :
    ∫⁻ ω, (‖simpleIntegral W H₁ t ω - simpleIntegral W H₂ t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  set M : ℝ → Ω → ℝ :=
    fun u ω => simpleIntegral W H₁ u ω - simpleIntegral W H₂ u ω with hM
  have hmart : MeasureTheory.Martingale M
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P :=
    (martingale_simpleIntegral_brownian W H₁ h_adapt₁).sub
      (martingale_simpleIntegral_brownian W H₂ h_adapt₂)
  have hMemLp : ∀ {u : ℝ}, 0 ≤ u → u ≤ T → MeasureTheory.MemLp (M u) 2 P :=
    fun {u} hu huT =>
      (simpleIntegral_memLp_intermediate_brownian W hT H₁ h_adapt₁ hu huT).sub
        (simpleIntegral_memLp_intermediate_brownian W hT H₂ h_adapt₂ hu huT)
  -- bridge `∫⁻‖M u‖₊² = ofReal (∫ (M u)²)` for `M u ∈ L²`.
  have h_bridge : ∀ {u : ℝ}, MeasureTheory.MemLp (M u) 2 P →
      ∫⁻ ω, (‖M u ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (M u ω) ^ 2 ∂P) := by
    intro u hu
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hu.integrable_sq
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
    refine lintegral_congr (fun ω => ?_)
    rw [show (‖M u ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖M u ω‖ from (ofReal_norm_eq_enorm _).symm,
        ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
  calc ∫⁻ ω, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ENNReal.ofReal (∫ ω, (M t ω) ^ 2 ∂P) := h_bridge (hMemLp ht_nn htT)
    _ ≤ ENNReal.ofReal (∫ ω, (M T ω) ^ 2 ∂P) :=
        ENNReal.ofReal_le_ofReal (integral_sq_mono_of_martingale hmart
          (hMemLp ht_nn htT) (hMemLp (le_of_lt hT) (le_refl T)) htT)
    _ = ∫⁻ ω, (‖M T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := (h_bridge (hMemLp (le_of_lt hT) (le_refl T))).symm
    _ = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖H₁.eval s ω - H₂.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        simp only [hM]
        exact SimplePredictable.diff_isometry_simple W hT H₁ H₂ h_eq h_adapt₁ h_adapt₂

/-- **Right-continuous martingale lift.** An `ℱ`-martingale `F` on `ℝ` whose
time-slices are right-`L¹`-continuous — `eLpNorm (F r - F s) 1 P → 0` as `r ↓ s` —
is automatically a martingale wrt the right-continuous filtration `ℱ₊`.

No path-regularity or Blumenthal `0`-`1` input is needed. An `ℱ₊ s`-measurable set
`A` lies in *every* `ℱ r` with `r > s` (since `ℱ₊ s = ⨅ r > s, ℱ r ≤ ℱ r`), so the
martingale identity gives `∫_A F t = ∫_A F r` for all `r ∈ (s, t]`; the map
`r ↦ ∫_A F r` is thus constantly `∫_A F t` near `s` from the right, while
right-`L¹`-continuity sends it to `∫_A F s`. Uniqueness of limits pins
`∫_A F s = ∫_A F t` for every `A ∈ ℱ₊ s`, i.e. `P[F t | ℱ₊ s] =ᵐ F s`. -/
lemma martingale_rightCont_of_tendsto_eLpNorm_one
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {F : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale F ℱ P)
    (hrc : ∀ s : ℝ, Filter.Tendsto
      (fun r => MeasureTheory.eLpNorm (F r - F s) 1 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0)) :
    MeasureTheory.Martingale F ℱ.rightCont P := by
  refine ⟨fun i => (hmart.stronglyAdapted i).mono (ℱ.le_rightCont i), ?_⟩
  intro s t hst
  have hm : ℱ.rightCont s ≤ ‹MeasurableSpace Ω› := (ℱ.rightCont).le s
  refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm
    (hmart.integrable t) (fun A _ _ => (hmart.integrable s).integrableOn)
    ?_ ((hmart.stronglyAdapted s).mono (ℱ.le_rightCont s)).aestronglyMeasurable).symm
  intro A hA _
  -- `s = t` is trivial; for `s < t` use the constant-near-`s`/limit argument.
  rcases eq_or_lt_of_le hst with rfl | hst'
  · rfl
  -- `r ↦ ∫_A F r → ∫_A F s` from right-`L¹`-continuity.
  have htend_s : Filter.Tendsto (fun r => ∫ x in A, F r x ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds (∫ x in A, F s x ∂P)) :=
    MeasureTheory.tendsto_setIntegral_of_L1' (F s) (hmart.integrable s)
      (Filter.Eventually.of_forall (fun r => hmart.integrable r)) (hrc s) A
  -- `r ↦ ∫_A F r` is constantly `∫_A F t` on `(s, t)`.
  have heq_ev : ∀ᶠ r in nhdsWithin s (Set.Ioi s),
      (∫ x in A, F t x ∂P) = ∫ x in A, F r x ∂P := by
    refine Filter.eventually_of_mem (Ioo_mem_nhdsGT hst') (fun r hr => ?_)
    have h_le : ℱ.rightCont s ≤ ℱ r := by
      rw [MeasureTheory.Filtration.rightCont_eq]
      exact iInf₂_le r hr.1
    exact (hmart.setIntegral_eq (le_of_lt hr.2) (h_le A hA)).symm
  have htend_const : Filter.Tendsto (fun r => ∫ x in A, F r x ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds (∫ x in A, F t x ∂P)) :=
    tendsto_const_nhds.congr' heq_ev
  exact tendsto_nhds_unique htend_s htend_const

/-- **CITED AXIOM: Unified L²-Itô integral with martingale + quadVar + isometry.**

For predictable square-integrable `H : Ω → ℝ → ℝ`, there exists a process
`F : ℝ → Ω → ℝ` and a filtration `Filt` such that:

* `F` is a martingale wrt `Filt`,
* `(F t)² − ∫_0^t H² ds` is a martingale wrt `Filt` (quadVar identity),
* `∫⁻ ω, ‖F T‖₊² ∂P = ∫⁻ ω, ∫⁻ s in [0, T], ‖H ω s‖₊² ∂volume ∂P`
  for every `T > 0`
  (L²-isometry).

`F` is the canonical L²-Itô integral `t ↦ ∫_0^t H_s dW_s`. The 3-conjunct strong
existence consolidates Karatzas–Shreve Thm 3.2.6.

**Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
Springer 1991, **Theorem 3.2.6** (unified martingale + quadratic variation +
L²-isometry of the L² Itô integral); Le Gall, J.-F. *Brownian Motion, Martingales
and Stochastic Calculus*, Springer 2016, **Theorem 5.4** + equation **(5.8)**.

**Standard proof outline**: Construct `F` as the L²-limit (across the natural
filtration's progressive σ-algebras) of `simpleIntegral W (G n) t` for an adapted
Cauchy approximating sequence `G n` (e.g., `predictableDyadicSimple_brownian`).
Each `simpleIntegral W (G n) ·` is a martingale (proven as
`martingale_simpleIntegral_brownian`). The L²-limit of martingales is a
martingale via L²-continuity of conditional expectation. The quadVar identity
holds at simple level (orthogonal-increments calculation: cross terms vanish,
diagonal gives `Δt`) and passes to the limit. The L²-isometry is preserved
through `Filter.limUnder` (already proven for the per-T case via
`itoIntegralLp_brownian_L2_isometry`).

**Replacement plan**: when the unified F-construction-across-all-t is fully
formalized (the simple-level partial isometry at varying t + L²-Cauchy at varying
t + cond-exp continuity application), this `axiom` becomes a `theorem`. Tracked
in `tools/cited_axioms.md` Tier 1. -/
axiom itoIsometry_brownian_unified_existence
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    -- `Filt` pinned to `(naturalFiltration W).rightCont` (not a loose
    -- existential), closing the trivial-filtration-witness route: Karatzas-Shreve
    -- 3.2.6 asserts the L²-Itô integral is a `(naturalFiltration W).rightCont`-
    -- martingale.
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = (LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont ∧
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      (∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)

/-- The *L² Itô integral* `M_t = ∫_0^t H_s dW_s` against a Brownian motion `W`.

Defined via `Classical.choose` on the 3-conjunct unified-existence axiom
`itoIsometry_brownian_unified_existence`; the resulting `F : ℝ → Ω → ℝ`
satisfies the L²-isometry at every `T > 0` and is a martingale. -/
noncomputable def stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (T : ℝ) : Ω → ℝ :=
  Classical.choose
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas h_sq_int_global) T

/-- **Itô L² isometry.**

  `𝔼[ (∫_0^T H_s dW_s)² ] = 𝔼[ ∫_0^T |H_s|² ds ]`

for predictable square-integrable `H`. ENNReal form.

Forwards to the L²-isometry conjunct of the unified-existence axiom #5. -/
theorem itoIsometry
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (T : ℝ) (hT : 0 < T)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∫⁻ ω, (‖stochasticIntegral W H h_meas h_progMeas h_sq_int_global T ω‖₊
      : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        ((‖H ω s‖₊ : ℝ≥0∞))^2 ∂volume ∂P := by
  -- Extract conjunct 3 (isometry) from the unified existence.
  unfold stochasticIntegral
  exact (Classical.choose_spec
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
      h_sq_int_global)).choose_spec.2.2.2 T hT

/-- **Quadratic variation of the L² Itô integral.**

For predictable square-integrable `H`, the process `t ↦ (M_t)² − ∫_0^t |H_s|² ds`
is a martingale, where `M_t = ∫_0^t H_s dW_s`.

Extracts conjunct 2 (quadratic variation) of the unified-existence axiom #5. -/
theorem quadVar_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral W H h_meas h_progMeas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2)
        F P := by
  -- Extract Filt + conjunct 2 (martingale of F²-∫H²) from the unified existence.
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
      h_sq_int_global)).choose,
    (Classical.choose_spec
      (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
        h_sq_int_global)).choose_spec.2.2.1⟩

/-- **The L² Itô integral is a martingale.**

The Itô integral `M_t = ∫_0^t H_s dW_s` is a square-integrable continuous
martingale w.r.t. the natural filtration of `W`.

Extracts conjunct 1 (martingale property) of the unified-existence axiom #5. -/
theorem martingale_stochasticIntegral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ)
    (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral W H h_meas h_progMeas h_sq_int_global t) F P := by
  -- Extract Filt + conjunct 1 (martingale of F) from the unified existence.
  unfold stochasticIntegral
  exact ⟨(Classical.choose_spec
    (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
      h_sq_int_global)).choose,
    (Classical.choose_spec
      (itoIsometry_brownian_unified_existence W H h_meas h_progMeas
        h_sq_int_global)).choose_spec.2.1⟩

end LevyStochCalc.Brownian.Ito
