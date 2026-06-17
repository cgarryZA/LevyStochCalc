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
    {μ : MeasureTheory.Measure Ω} {ι : Type*} {l : Filter ι} {a : ι → Ω → ℝ} {b : Ω → ℝ}
    (ha : ∀ n, AEMeasurable (a n) μ) (hb : AEMeasurable b μ)
    (hbfin : MeasureTheory.eLpNorm b 2 μ ≠ ⊤)
    (htend : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (a n - b) 2 μ)
      l (nhds 0)) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm (fun ω => (a n ω) ^ 2 - (b ω) ^ 2) 1 μ)
      l (nhds 0) := by
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
      l (nhds 0) := by
    have h1 := htend.add (tendsto_const_nhds (x := 2 * MeasureTheory.eLpNorm b 2 μ))
    have h2C : (2 : ℝ≥0∞) * MeasureTheory.eLpNorm b 2 μ ≠ ⊤ :=
      ENNReal.mul_ne_top (by norm_num) hbfin
    have := ENNReal.Tendsto.mul htend (Or.inr (by simpa using h2C)) h1
      (Or.inr (by norm_num))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htend_bound
    (fun _ => bot_le) hbound

/-- **Right-continuity of the horizon integral.** For measurable `φ : Ω → ℝ → ℝ≥0∞`
integrable (iterated) over `[0, T]`, the slab integral over `(s₀, r]` tends to `0`
as `r ↓ s₀` (for `0 ≤ s₀ < T`). Tonelli (`setLIntegral_prod`) reduces this to
`tendsto_setLIntegral_zero` for `P ⊗ volume` on the sets `univ ×ˢ (s₀, r]`, of
product measure `ofReal (r − s₀) → 0`. Underlies the right-`L²`-continuity of the
L² Itô integral's slices (`‖F_r − F_{s₀}‖₂² = ∫∫_{(s₀,r]}‖H‖²`). -/
lemma tendsto_setLIntegral_Ioc_prod_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (φ : Ω → ℝ → ℝ≥0∞) (hφ : Measurable (Function.uncurry φ))
    {s₀ T : ℝ} (hs₀ : 0 ≤ s₀) (hs₀T : s₀ < T)
    (h_fin : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T, φ ω u ∂volume ∂P ≠ ⊤) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s₀ r, φ ω u ∂volume ∂P)
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
  have hset : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Icc
  set f : Ω × ℝ → ℝ≥0∞ :=
    ((Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T).indicator (Function.uncurry φ) with hf
  have h_tot : ∫⁻ z, f z ∂(P.prod volume) ≠ ⊤ := by
    rw [hf, MeasureTheory.lintegral_indicator hset,
        MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
        MeasureTheory.Measure.restrict_univ]
    simpa using h_fin
  have h_meas_to_zero : Filter.Tendsto (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
      (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
    have hval : (fun r => (P.prod volume) ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r))
        = fun r => ENNReal.ofReal (r - s₀) := by
      funext r
      rw [MeasureTheory.Measure.prod_prod, measure_univ, one_mul, Real.volume_Ioc]
    rw [hval]
    have h1 : Filter.Tendsto (fun r => r - s₀)
        (nhdsWithin s₀ (Set.Ioi s₀)) (nhds 0) := by
      have h0 : Filter.Tendsto (fun r => r - s₀) (nhds s₀) (nhds (s₀ - s₀)) :=
        (continuous_sub_right s₀).tendsto s₀
      rw [sub_self] at h0
      exact h0.mono_left nhdsWithin_le_nhds
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h1
    simpa using this
  have h_zero := MeasureTheory.tendsto_setLIntegral_zero (μ := P.prod volume) (f := f)
    (s := fun r => (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) h_tot h_meas_to_zero
  refine h_zero.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hs₀T] with r hr
  have hsub : (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r ⊆ (Set.univ : Set Ω) ×ˢ Set.Icc (0 : ℝ) T :=
    Set.prod_mono (le_refl _) (fun u hu => ⟨le_of_lt (lt_of_le_of_lt hs₀ hu.1),
      le_of_lt (lt_of_le_of_lt hu.2 hr.2)⟩)
  have hset' : MeasurableSet ((Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r) :=
    MeasurableSet.prod MeasurableSet.univ measurableSet_Ioc
  have hstep1 : ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, f z ∂(P.prod volume)
      = ∫⁻ z in (Set.univ : Set Ω) ×ˢ Set.Ioc s₀ r, Function.uncurry φ z ∂(P.prod volume) := by
    refine MeasureTheory.setLIntegral_congr_fun hset' (fun z hz => ?_)
    rw [hf, Set.indicator_of_mem (hsub hz)]
  rw [hstep1, MeasureTheory.setLIntegral_prod _ (hφ.aemeasurable.restrict),
      MeasureTheory.Measure.restrict_univ]
  rfl

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

/-- **Conditional Pythagoras for L² martingales.** `𝔼[(M t − M s)² | ℱ s] =ᵐ
𝔼[(M t)² | ℱ s] − (M s)²`. Conditional version of the orthogonal-increment identity;
the cross term `𝔼[M s · M t | ℱ s] =ᵐ (M s)²` by pull-out + the martingale identity. -/
lemma condExp_sq_increment_of_martingale
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    {M : ℝ → Ω → ℝ}
    (hmart : MeasureTheory.Martingale M ℱ P)
    {s t : ℝ} (hMs : MeasureTheory.MemLp (M s) 2 P) (hMt : MeasureTheory.MemLp (M t) 2 P)
    (hst : s ≤ t) :
    P[(fun ω => (M t ω - M s ω) ^ 2) | ℱ s]
      =ᵐ[P] fun ω => (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2 := by
  have hm : ℱ s ≤ ‹MeasurableSpace Ω› := ℱ.le s
  have hMt2 : MeasureTheory.Integrable (fun ω => (M t ω) ^ 2) P := hMt.integrable_sq
  have hMs2 : MeasureTheory.Integrable (fun ω => (M s ω) ^ 2) P := hMs.integrable_sq
  have hcr : MeasureTheory.Integrable (fun ω => M s ω * M t ω) P := hMs.integrable_mul hMt
  have hMsm : StronglyMeasurable[ℱ s] (M s) := hmart.stronglyAdapted s
  have hMs2m : StronglyMeasurable[ℱ s] (fun ω => (M s ω) ^ 2) := by
    have heq : (fun ω => (M s ω) ^ 2) = (fun ω => M s ω * M s ω) := by funext ω; ring
    rw [heq]; exact hMsm.mul hMsm
  have hf_int : MeasureTheory.Integrable (fun ω => (M t ω - M s ω) ^ 2) P := by
    have heq : (fun ω => (M t ω - M s ω) ^ 2)
        = (fun ω => (M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) := by funext ω; ring
    rw [heq]; exact (hMt2.sub (hcr.const_mul 2)).add hMs2
  have hcross_ae : P[(fun ω => M s ω * M t ω) | ℱ s] =ᵐ[P] fun ω => (M s ω) ^ 2 := by
    have hpull := MeasureTheory.condExp_mul_of_stronglyMeasurable_left (m := ℱ s) hMsm
      (show MeasureTheory.Integrable ((M s) * (M t)) P by simpa [Pi.mul_apply] using hcr)
      (hmart.integrable t)
    filter_upwards [hpull, hmart.condExp_ae_eq hst] with ω hp hmeq
    have hp' : P[(fun ω => M s ω * M t ω) | ℱ s] ω = M s ω * (P[M t | ℱ s]) ω := by
      simpa [Pi.mul_apply] using hp
    rw [hp', hmeq, ← pow_two]
  symm
  refine MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm hf_int
    (fun B _ _ => (MeasureTheory.integrable_condExp.sub hMs2).integrableOn)
    (fun B hB _ => ?_)
    ((MeasureTheory.stronglyMeasurable_condExp.sub hMs2m).aestronglyMeasurable)
  have hcross : ∫ ω in B, M s ω * M t ω ∂P = ∫ ω in B, (M s ω) ^ 2 ∂P :=
    calc ∫ ω in B, M s ω * M t ω ∂P
        = ∫ ω in B, (P[(fun ω => M s ω * M t ω) | ℱ s]) ω ∂P :=
          (MeasureTheory.setIntegral_condExp hm hcr hB).symm
      _ = ∫ ω in B, (M s ω) ^ 2 ∂P :=
          MeasureTheory.setIntegral_congr_ae (hm B hB) (hcross_ae.mono (fun ω hω _ => hω))
  -- LHS `∫_B (condExp(M t²|ℱ s) − M s²)`
  have e1 : ∫ ω in B, ((P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω - (M s ω) ^ 2) ∂P
      = (∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P) - ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn hMs2.integrableOn
  have e1' : ∫ ω in B, (P[(fun ω => (M t ω) ^ 2) | ℱ s]) ω ∂P = ∫ ω in B, (M t ω) ^ 2 ∂P :=
    MeasureTheory.setIntegral_condExp hm hMt2 hB
  -- RHS `∫_B (M t − M s)²`
  have hexp : ∫ ω in B, (M t ω - M s ω) ^ 2 ∂P
      = ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P :=
    MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => by ring)
  have e2a : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω) + (M s ω) ^ 2) ∂P
      = (∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P) + ∫ ω in B, (M s ω) ^ 2 ∂P :=
    MeasureTheory.integral_add ((hMt2.sub (hcr.const_mul 2)).integrableOn) hMs2.integrableOn
  have e2b : ∫ ω in B, ((M t ω) ^ 2 - 2 * (M s ω * M t ω)) ∂P
      = (∫ ω in B, (M t ω) ^ 2 ∂P) - ∫ ω in B, 2 * (M s ω * M t ω) ∂P :=
    MeasureTheory.integral_sub hMt2.integrableOn (hcr.const_mul 2).integrableOn
  have e2c : ∫ ω in B, 2 * (M s ω * M t ω) ∂P = 2 * ∫ ω in B, M s ω * M t ω ∂P :=
    MeasureTheory.integral_const_mul 2 _
  rw [e1, e1', hexp, e2a, e2b, e2c, hcross]; ring

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

/-- **A single adapted simple approximant within `ε` on `[0, T]`.** Extracted from
the convergent dense sequence `adaptedSimple_dense_L2_brownian`. -/
lemma exists_adaptedSimple_within
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    {T : ℝ} (hT : 0 < T)
    (h_sq_int : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ G : SimplePredictable Ω T,
      (∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          (G.partition i.castSucc)) (G.ξ i)) ∧
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - G.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε := by
  obtain ⟨Hn, h_adapt, h_tend⟩ :=
    adaptedSimple_dense_L2_brownian W hT H h_meas h_progMeas h_sq_int
  have hev : ∀ᶠ m in Filter.atTop,
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s - (Hn m).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ε :=
    h_tend (Iio_mem_nhds hε)
  obtain ⟨m, hm⟩ := hev.exists
  exact ⟨Hn m, h_adapt m, hm⟩

/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`. -/
lemma eLpNorm_two_rpow_eq_lintegral_sq {μ : MeasureTheory.Measure Ω} (g : Ω → ℝ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num)
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]
  refine lintegral_congr (fun ω => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl

/-- `eLpNorm g 2 μ ^ (2:ℝ) = ∫⁻ ‖g‖₊² ∂μ`, over an arbitrary base type. -/
lemma eLpNorm_sq_eq_lintegral_nnnorm_sq {β : Type*} [MeasurableSpace β]
    {μ : MeasureTheory.Measure β} (g : β → ℝ) :
    MeasureTheory.eLpNorm g 2 μ ^ (2 : ℝ) = ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ 2 ∂μ := by
  have h := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (p := (2 : NNReal))
    (f := g) (by norm_num)
  rw [show ((2 : NNReal) : ℝ≥0∞) = (2 : ℝ≥0∞) from by simp,
      show ((2 : NNReal) : ℝ) = (2 : ℝ) from by norm_num] at h
  rw [h]; refine lintegral_congr (fun x => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl

/-- `eval` is bounded by the sum of the coefficient bounds. -/
lemma eval_abs_le_sum_bounds {T : ℝ} (H : SimplePredictable Ω T) (s : ℝ) (ω : Ω) :
    |H.eval s ω| ≤ ∑ i : Fin H.N, (H.ξ_bounded i).choose := by
  unfold SimplePredictable.eval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  have hM : ∀ ω, |H.ξ i ω| ≤ (H.ξ_bounded i).choose := (H.ξ_bounded i).choose_spec
  have hM0 : 0 ≤ (H.ξ_bounded i).choose := le_trans (abs_nonneg _) (hM ω)
  split_ifs with h
  · exact hM ω
  · simpa using hM0

/-- For any `SimplePredictable` and any horizon `T`, the squared `L²(λ⊗P)` mass of
`eval` over `[0, T]` is finite (`eval` is uniformly bounded). -/
lemma eval_lintegral_sq_finite
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {T' : ℝ} (H : SimplePredictable Ω T') (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  set C : ℝ := ∑ i : Fin H.N, (H.ξ_bounded i).choose with hC
  have hbound : ∀ ω s, (‖H.eval s ω‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (C ^ 2) := by
    intro ω s
    rw [show (‖H.eval s ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H.eval s ω‖
          from (ofReal_norm_eq_enorm _).symm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : ‖H.eval s ω‖ ≤ C := by
      rw [Real.norm_eq_abs]; exact eval_abs_le_sum_bounds H s ω
    nlinarith [h1, norm_nonneg (H.eval s ω)]
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono (fun ω =>
    le_trans (MeasureTheory.lintegral_mono (fun s => hbound ω s))
      (le_of_eq (MeasureTheory.setLIntegral_const _ _)))) ?_
  rw [MeasureTheory.lintegral_const]
  exact ENNReal.mul_lt_top
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Icc_lt_top) (measure_lt_top _ _)

/-- `simpleIntegral W H t = 0` for `t ≤ 0` (all increments `W_t − W_t` vanish). -/
lemma simpleIntegral_eq_zero_of_nonpos
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {t : ℝ} (ht : t ≤ 0) (ω : Ω) :
    simpleIntegral W H t ω = 0 := by
  unfold simpleIntegral
  refine Finset.sum_eq_zero (fun i _ => ?_)
  have hp1 : 0 ≤ H.partition i.succ := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.succ)
    rwa [H.partition_zero] at this
  have hp2 : 0 ≤ H.partition i.castSucc := by
    have := H.partition_strictMono.monotone (Fin.zero_le i.castSucc)
    rwa [H.partition_zero] at this
  rw [min_eq_right (ht.trans hp1), min_eq_right (ht.trans hp2), sub_self, mul_zero]

/-- `∫⁻ ‖g‖₊² = ofReal (∫ g²)` for `g ∈ L²`. -/
lemma lintegral_nnnorm_sq_eq_ofReal_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {g : Ω → ℝ} (hg : MeasureTheory.MemLp g 2 P) :
    ∫⁻ ω, (‖g ω‖₊ : ℝ≥0∞) ^ 2 ∂P = ENNReal.ofReal (∫ ω, (g ω) ^ 2 ∂P) := by
  rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hg.integrable_sq
        (Filter.Eventually.of_forall (fun ω => sq_nonneg _))]
  refine lintegral_congr (fun ω => ?_)
  rw [show (‖g ω‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖g ω‖ from (ofReal_norm_eq_enorm _).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- `∫ (W_b − W_a)² = b − a` for `0 ≤ a < b`. -/
lemma brownian_incr_sq_integral
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P)
        = ∫ x : ℝ, x ^ 2 ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x ^ 2) _)).symm,
    W.increment_gaussian ha hab]
  exact LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment ⟨b - a, by linarith⟩

/-- **Conditional diagonal.** For a bounded `ℱ_a`-measurable factor `g`,
`∫ g · (W_b − W_a)² = (∫ g) · (b − a)` — the increment square is independent of the
`ℱ_a`-measurable `g`, with second moment `b − a`. -/
lemma integral_factor_increment_sq
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a) g)
    {C : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ^ 2 ∂P = (∫ ω, g ω ∂P) * (b - a) := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW
  have hΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have hg_m : Measurable g :=
    (hg_meas.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a)).measurable
  -- IndepFun g ΔW
  have h_indep_F := W.joint_increment_independent ha hab
  have hg_comap_le : MeasurableSpace.comap g inferInstance ≤
      ⨆ j ∈ Set.Iic a, MeasurableSpace.comap (W.W j) inferInstance := by
    have hgF : @Measurable Ω ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a) _ g := hg_meas.measurable
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have heq : (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a
        = ⨆ j ∈ Set.Iic a, MeasurableSpace.comap (W.W j) inferInstance := by
      show (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a = _
      unfold LevyStochCalc.Brownian.Martingale.naturalFiltration MeasureTheory.Filtration.natural
      rfl
    rw [← heq]; exact hgF hv
  have h_indep_g_ΔW : ProbabilityTheory.IndepFun g ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]; intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F
    exact h_indep_F u v (hg_comap_le u hu) hv
  have h_indep_g_ΔWsq : ProbabilityTheory.IndepFun g (fun ω => (ΔW ω) ^ 2) P := by
    have := h_indep_g_ΔW.comp measurable_id (measurable_id.pow_const 2)
    simpa [Function.comp] using this
  rw [show (fun ω => g ω * (W.W b ω - W.W a ω) ^ 2) = g * (fun ω => (ΔW ω) ^ 2) from rfl,
    h_indep_g_ΔWsq.integral_mul_eq_mul_integral hg_m.aestronglyMeasurable
    ((hΔW_meas.pow_const 2).aestronglyMeasurable), brownian_incr_sq_integral W ha hab]

/-- `∫ (W_b − W_a) = 0` for `0 ≤ a < b`. -/
lemma brownian_incr_mean
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ∂P = 0 := by
  have h_meas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [show (∫ ω, (W.W b ω - W.W a ω) ∂P)
        = ∫ x : ℝ, x ∂(P.map (fun ω => W.W b ω - W.W a ω)) from
      (MeasureTheory.integral_map h_meas.aemeasurable
        (by fun_prop : MeasureTheory.AEStronglyMeasurable (fun x : ℝ => x) _)).symm,
    W.increment_gaussian ha hab]
  exact ProbabilityTheory.integral_id_gaussianReal

/-- **Off-diagonal building block.** For a bounded `ℱ_a`-measurable factor `g`,
`∫ g · (W_b − W_a) = 0` — the increment is centred and independent of `g`. -/
lemma integral_factor_increment_eq_zero
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    {g : Ω → ℝ}
    (hg_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a) g)
    {C : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ C) :
    ∫ ω, g ω * (W.W b ω - W.W a ω) ∂P = 0 := by
  set ΔW : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔW
  have hΔW_meas : Measurable ΔW := (W.measurable_eval b).sub (W.measurable_eval a)
  have hg_m : Measurable g :=
    (hg_meas.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a)).measurable
  have h_indep_F := W.joint_increment_independent ha hab
  have hg_comap_le : MeasurableSpace.comap g inferInstance ≤
      ⨆ j ∈ Set.Iic a, MeasurableSpace.comap (W.W j) inferInstance := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    have heq : (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a
        = ⨆ j ∈ Set.Iic a, MeasurableSpace.comap (W.W j) inferInstance := by
      show (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a = _
      unfold LevyStochCalc.Brownian.Martingale.naturalFiltration MeasureTheory.Filtration.natural
      rfl
    rw [← heq]; exact hg_meas.measurable hv
  have h_indep_g_ΔW : ProbabilityTheory.IndepFun g ΔW P := by
    rw [ProbabilityTheory.IndepFun_iff]; intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F
    exact h_indep_F u v (hg_comap_le u hu) hv
  rw [show (fun ω => g ω * (W.W b ω - W.W a ω)) = g * ΔW from rfl,
    h_indep_g_ΔW.integral_mul_eq_mul_integral hg_m.aestronglyMeasurable hΔW_meas.aestronglyMeasurable,
    brownian_incr_mean W ha hab, mul_zero]

/-- **Weighted off-diagonal vanishing.** For two increments with the second
strictly after the first (`a₁ < b₁ ≤ a₂ < b₂`), `Fᵢ`-measurable coefficients, and
a bounded `F_{a₁}`-measurable weight `g`,
`∫ g · (ξ₁·ΔW₁)·(ξ₂·ΔW₂) = 0`. The weighted analogue of
`offDiagonal_increment_integral_zero`: `f := g·ξ₁·ΔW₁·ξ₂` is `F_{a₂}`-measurable
and `ΔW₂ ⟂ F_{a₂}` is centred, so `𝔼[f·ΔW₂] = 𝔼[f]·0 = 0`. With `g = 1_B`
(`B ∈ F_s`, `s ≤ a₁`) this gives the off-diagonal of the set-level Itô isometry. -/
lemma offDiagonal_increment_integral_zero_weighted
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {a₁ b₁ a₂ b₂ : ℝ} (ha₁ : 0 ≤ a₁) (h₁ : a₁ < b₁) (h₁₂ : b₁ ≤ a₂) (h₂ : a₂ < b₂)
    (ξ₁ ξ₂ g : Ω → ℝ)
    (hadapt₁ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₁) ξ₁)
    (hadapt₂ : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) ξ₂)
    (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₁) g) :
    ∫ ω, g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * (W.W b₂ ω - W.W a₂ ω))) ∂P
      = 0 := by
  set ΔW₂ : Ω → ℝ := fun ω => W.W b₂ ω - W.W a₂ ω with hΔW₂_def
  have ha₂_nn : 0 ≤ a₂ := le_trans ha₁ (le_trans (le_of_lt h₁) h₁₂)
  have ha₁a₂ : a₁ ≤ a₂ := le_trans (le_of_lt h₁) h₁₂
  have hξ₁meas : Measurable ξ₁ :=
    (hadapt₁.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a₁)).measurable
  have hξ₂meas : Measurable ξ₂ :=
    (hadapt₂.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a₂)).measurable
  have hgmeas : Measurable g :=
    (hg.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le a₁)).measurable
  set f : Ω → ℝ := fun ω => g ω * (ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * ξ₂ ω with hf_def
  rw [show (fun ω => g ω * ((ξ₁ ω * (W.W b₁ ω - W.W a₁ ω)) * (ξ₂ ω * ΔW₂ ω)))
        = fun ω => f ω * ΔW₂ ω from by funext ω; simp only [hf_def]; ring]
  have h_Wb₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) (W.W b₁) :=
    (MeasureTheory.Filtration.stronglyAdapted_natural (u := W.W)
      (fun u => (W.measurable_eval u).stronglyMeasurable) b₁).mono
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono h₁₂)
  have h_Wa₁_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) (W.W a₁) :=
    (MeasureTheory.Filtration.stronglyAdapted_natural (u := W.W)
      (fun u => (W.measurable_eval u).stronglyMeasurable) a₁).mono
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono
        (le_trans (le_of_lt h₁) h₁₂))
  have h_ξ₁_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) ξ₁ :=
    hadapt₁.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono ha₁a₂)
  have h_g_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) g :=
    hg.mono ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).mono ha₁a₂)
  have h_f_F_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq a₂) f :=
    (h_g_F_meas.mul (h_ξ₁_F_meas.mul (h_Wb₁_meas.sub h_Wa₁_meas))).mul hadapt₂
  have h_indep_F_ΔW₂ := W.joint_increment_independent ha₂_nn h₂
  have h_f_meas : Measurable f :=
    (hgmeas.mul (hξ₁meas.mul ((W.measurable_eval b₁).sub (W.measurable_eval a₁)))).mul hξ₂meas
  have h_ΔW₂_meas : Measurable ΔW₂ := (W.measurable_eval b₂).sub (W.measurable_eval a₂)
  have h_f_comap_le :
      MeasurableSpace.comap f inferInstance ≤
        ⨆ jj ∈ Set.Iic a₂, MeasurableSpace.comap (W.W jj) inferInstance := by
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
    exact h_f_F_meas.measurable hv
  have h_indep_f_ΔW₂ : ProbabilityTheory.IndepFun f ΔW₂ P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at h_indep_F_ΔW₂
    exact h_indep_F_ΔW₂ u v (h_f_comap_le u hu) hv
  have h_ΔW₂_mean : ∫ ω, ΔW₂ ω ∂P = 0 := brownian_incr_mean W ha₂_nn h₂
  rw [show (fun ω => f ω * ΔW₂ ω) = f * ΔW₂ from rfl,
    h_indep_f_ΔW₂.integral_mul_eq_mul_integral h_f_meas.aestronglyMeasurable
    h_ΔW₂_meas.aestronglyMeasurable, h_ΔW₂_mean, mul_zero]

/-- **Clamped-increment identity.** For `s ≤ t`,
`simpleIntegral W H t − simpleIntegral W H s = ∑ᵢ ξᵢ·(W_{cᵢ₊₁} − W_{cᵢ})` where
`cᵢ = max s (min pᵢ t)` clamps the partition points into `[s, t]`. The increment
of the simple integral between `s` and `t` rebuilds as a single sum of increments
over the `[s,t]`-clamped partition — the starting point for the conditional
(set-level) Itô isometry. -/
lemma simpleIntegral_sub_eq_clamp_sum
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {s t : ℝ} (hst : s ≤ t) (ω : Ω) :
    simpleIntegral W H t ω - simpleIntegral W H s ω
      = ∑ i : Fin H.N, H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
          - W.W (max s (min (H.partition i.castSucc) t)) ω) := by
  have key : ∀ p : ℝ,
      W.W (min p t) ω - W.W (min p s) ω = W.W (max s (min p t)) ω - W.W s ω := by
    intro p
    rcases le_or_gt s p with hsp | hps
    · rw [min_eq_right hsp, max_eq_right (le_min hsp hst)]
    · rw [min_eq_left (le_of_lt hps), min_eq_left (le_of_lt (lt_of_lt_of_le hps hst)),
        max_eq_left (le_of_lt hps), sub_self, sub_self]
  unfold simpleIntegral
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have e1 := key (H.partition i.succ)
  have e2 := key (H.partition i.castSucc)
  rw [← mul_sub]
  congr 1
  rw [show W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.castSucc) t) ω
        - (W.W (min (H.partition i.succ) s) ω - W.W (min (H.partition i.castSucc) s) ω)
      = (W.W (min (H.partition i.succ) t) ω - W.W (min (H.partition i.succ) s) ω)
        - (W.W (min (H.partition i.castSucc) t) ω
            - W.W (min (H.partition i.castSucc) s) ω) from by ring]
  rw [e1, e2]; ring

/-- **Weighted clamped Bochner increment second moment.** For adapted simple `H`,
`0 ≤ s ≤ t`, and a bounded `F_s`-measurable weight `g`,
`∫ g·(I_t − I_s)² = ∑ᵢ (cᵢ₊₁ − cᵢ)·∫ g·ξᵢ²` with `cᵢ = max s (min pᵢ t)`.
The set-level (`g = 1_B`, `B ∈ F_s`) conditional Itô isometry at simple level:
the increment squares onto the `[s,t]`-clamped partition, off-diagonal terms vanish
(`offDiagonal_increment_integral_zero_weighted`), and the diagonal gives the
clamped lengths weighted by `g` (`integral_factor_increment_sq`). -/
lemma simpleIntegral_sub_sq_bochner_clamped_weighted
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin H.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (H.partition i.castSucc)) (H.ξ i))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    {g : Ω → ℝ} (hg : @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq s) g)
    {Cg : ℝ} (hg_bdd : ∀ ω, |g ω| ≤ Cg) :
    ∫ ω, g ω * (simpleIntegral W H t ω - simpleIntegral W H s ω) ^ 2 ∂P
      = ∑ i : Fin H.N,
        (max s (min (H.partition i.succ) t) - max s (min (H.partition i.castSucc) t))
          * ∫ ω, g ω * (H.ξ i ω) ^ 2 ∂P := by
  set ℱ := LevyStochCalc.Brownian.Martingale.naturalFiltration W with hℱ
  have hgmeas : Measurable g := (hg.mono (ℱ.le s)).measurable
  have h_cl_nn : ∀ p : ℝ, 0 ≤ max s (min p t) := fun p => le_trans hs (le_max_left _ _)
  have h_cl_mono : ∀ {a b : ℝ}, a ≤ b → max s (min a t) ≤ max s (min b t) :=
    fun hab => max_le_max (le_refl s) (min_le_min hab (le_refl t))
  have h_a_le_b : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) ≤ max s (min (H.partition i.succ) t) :=
    fun i => h_cl_mono (le_of_lt (H.partition_strictMono Fin.castSucc_lt_succ))
  -- In the genuine (non-degenerate) case the lower clamp dominates the partition pt.
  have h_padapt : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) < max s (min (H.partition i.succ) t) →
        H.partition i.castSucc ≤ max s (min (H.partition i.castSucc) t) := by
    intro i hlt
    by_cases hpt : H.partition i.castSucc ≤ t
    · rw [min_eq_left hpt]; exact le_max_right _ _
    · push_neg at hpt
      exfalso
      have h1 : min (H.partition i.castSucc) t = t := min_eq_right (le_of_lt hpt)
      have h2 : min (H.partition i.succ) t = t :=
        min_eq_right (le_of_lt (lt_trans hpt (H.partition_strictMono Fin.castSucc_lt_succ)))
      rw [h1, h2] at hlt; exact lt_irrefl _ hlt
  -- ξ adaptedness lifted to the clamped left endpoint (genuine case).
  have h_ξ_cl : ∀ i : Fin H.N,
      max s (min (H.partition i.castSucc) t) < max s (min (H.partition i.succ) t) →
        @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ.seq (max s (min (H.partition i.castSucc) t))) (H.ξ i) :=
    fun i hlt => (h_adapt i).mono (ℱ.mono (h_padapt i hlt))
  set term : Fin H.N → Ω → ℝ := fun i ω =>
    H.ξ i ω * (W.W (max s (min (H.partition i.succ) t)) ω
      - W.W (max s (min (H.partition i.castSucc) t)) ω) with hterm
  -- integrability of every weighted cross product
  have h_cross : ∀ i j : Fin H.N,
      MeasureTheory.Integrable (fun ω => g ω * (term i ω * term j ω)) P := by
    intro i j
    obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
    obtain ⟨Mj, hMj⟩ := H.ξ_bounded j
    refine MeasureTheory.Integrable.bdd_mul (c := Cg)
      (cross_increment_integrable W (h_cl_nn _) (h_a_le_b i) (h_cl_nn _) (h_a_le_b j)
        (H.ξ i) (H.ξ j) (H.ξ_measurable i) (H.ξ_measurable j) Mi hMi Mj hMj)
      hgmeas.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => (Real.norm_eq_abs (g ω)).le.trans (hg_bdd ω)))
  -- off-diagonal vanishing for i < j
  have h_off : ∀ i j : Fin H.N, i < j → ∫ ω, g ω * (term i ω * term j ω) ∂P = 0 := by
    intro i j hij
    rcases eq_or_lt_of_le (h_a_le_b j) with hj_eq | hj_lt
    · rw [show (fun ω => g ω * (term i ω * term j ω)) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hj_eq]; ring]
      exact MeasureTheory.integral_zero _ _
    · rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
      · rw [show (fun ω => g ω * (term i ω * term j ω)) = fun _ => (0 : ℝ) from by
          funext ω; simp only [hterm]; rw [← hi_eq]; ring]
        exact MeasureTheory.integral_zero _ _
      · have hbi_le_aj : max s (min (H.partition i.succ) t)
            ≤ max s (min (H.partition j.castSucc) t) :=
          h_cl_mono (H.partition_strictMono.monotone (Fin.succ_le_castSucc_iff.mpr hij))
        exact offDiagonal_increment_integral_zero_weighted W (h_cl_nn _) hi_lt hbi_le_aj hj_lt
          (H.ξ i) (H.ξ j) g (h_ξ_cl i hi_lt) (h_ξ_cl j hj_lt)
          (hg.mono (ℱ.mono (le_max_left s (min (H.partition i.castSucc) t))))
  rw [show (fun ω => g ω * (simpleIntegral W H t ω - simpleIntegral W H s ω) ^ 2)
        = fun ω => ∑ i : Fin H.N, ∑ j : Fin H.N, g ω * (term i ω * term j ω) from by
    funext ω
    rw [simpleIntegral_sub_eq_clamp_sum W H hst ω,
      show (∑ i : Fin H.N, term i ω) ^ 2
          = ∑ i : Fin H.N, ∑ j : Fin H.N, term i ω * term j ω from by
        rw [sq, Finset.sum_mul_sum], Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => h_cross i j))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => h_cross i j),
    Finset.sum_eq_single i]
  · -- diagonal j = i
    rcases eq_or_lt_of_le (h_a_le_b i) with hi_eq | hi_lt
    · rw [show (fun ω => g ω * (term i ω * term i ω)) = fun _ => (0 : ℝ) from by
        funext ω; simp only [hterm]; rw [← hi_eq]; ring, MeasureTheory.integral_zero,
        ← hi_eq, sub_self, zero_mul]
    · obtain ⟨Mi, hMi⟩ := H.ξ_bounded i
      have hg2 : @MeasureTheory.StronglyMeasurable Ω ℝ _
          (ℱ.seq (max s (min (H.partition i.castSucc) t))) (fun ω => g ω * (H.ξ i ω) ^ 2) := by
        refine (hg.mono (ℱ.mono (le_max_left s (min (H.partition i.castSucc) t)))).mul ?_
        simpa [pow_two] using (h_ξ_cl i hi_lt).mul (h_ξ_cl i hi_lt)
      have hbdd2 : ∀ ω, |g ω * (H.ξ i ω) ^ 2| ≤ Cg * Mi ^ 2 := fun ω => by
        have h2 : (H.ξ i ω) ^ 2 ≤ Mi ^ 2 :=
          sq_le_sq' (neg_le_of_abs_le (hMi ω)) (le_of_abs_le (hMi ω))
        calc |g ω * (H.ξ i ω) ^ 2|
            = |g ω| * (H.ξ i ω) ^ 2 := by
              rw [abs_mul, abs_of_nonneg (sq_nonneg (H.ξ i ω))]
          _ ≤ Cg * Mi ^ 2 :=
              mul_le_mul (hg_bdd ω) h2 (sq_nonneg _) (le_trans (abs_nonneg _) (hg_bdd ω))
      have hdiag := integral_factor_increment_sq W (h_cl_nn _) hi_lt hg2 (C := Cg * Mi ^ 2) hbdd2
      rw [show (fun ω => g ω * (term i ω * term i ω))
            = fun ω => (g ω * (H.ξ i ω) ^ 2)
                * (W.W (max s (min (H.partition i.succ) t)) ω
                    - W.W (max s (min (H.partition i.castSucc) t)) ω) ^ 2 from by
          funext ω; simp only [hterm]; ring, hdiag, mul_comm]
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h_lt | h_gt
    · rw [show (fun ω => g ω * (term i ω * term j ω))
            = fun ω => g ω * (term j ω * term i ω) from by funext ω; ring]
      exact h_off j i h_lt
    · exact h_off i j h_gt
  · intro h; exact absurd (Finset.mem_univ _) h

/-- **Real clamped compensator integral.** For `0 ≤ t`,
`∫_{[0,t]} (G.eval u ω)² du = ∑ᵢ (min pᵢ₊₁ t − min pᵢ t)·ξᵢ²`. The real-Bochner
companion of `lintegral_eval_sq_clamped`, obtained from it by
`integral_eq_lintegral_of_nonneg_ae` and `ENNReal.toReal`. The simple-level
quadratic-variation compensator `A_t = ∫_{[0,t]} (eval)²` in closed sum form. -/
lemma setIntegral_eval_sq_Icc_clamped {T : ℝ} (G : SimplePredictable Ω T) (ω : Ω)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume
      = ∑ i : Fin G.N,
        (min (G.partition i.succ) t - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2 := by
  have h_len_nn : ∀ i : Fin G.N,
      0 ≤ min (G.partition i.succ) t - min (G.partition i.castSucc) t :=
    fun i => sub_nonneg.mpr (min_le_min_right t
      (le_of_lt (G.partition_strictMono Fin.castSucc_lt_succ)))
  have h_eval_meas : Measurable (fun u => G.eval u ω) :=
    G.eval_jointly_measurable.comp
      (by fun_prop : Measurable (fun s : ℝ => ((ω, s) : Ω × ℝ)))
  have h_norm_sq : ∀ x : ℝ, (‖x‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal (x ^ 2) := fun x => by
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm_eq_enorm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), show ‖x‖ ^ 2 = x ^ 2 from by
        rw [Real.norm_eq_abs, sq_abs]]
  rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae
        (Filter.Eventually.of_forall (fun u => sq_nonneg _))
        (h_eval_meas.pow_const 2).aestronglyMeasurable]
  rw [show (fun u => ENNReal.ofReal ((G.eval u ω) ^ 2))
        = fun u => (‖G.eval u ω‖₊ : ℝ≥0∞) ^ 2 from funext (fun u => (h_norm_sq _).symm),
    lintegral_eval_sq_clamped G ω ht,
    show (fun i : Fin G.N => ENNReal.ofReal (min (G.partition i.succ) t
          - min (G.partition i.castSucc) t) * (‖G.ξ i ω‖₊ : ℝ≥0∞) ^ 2)
        = fun i => ENNReal.ofReal ((min (G.partition i.succ) t
            - min (G.partition i.castSucc) t) * (G.ξ i ω) ^ 2) from
      funext (fun i => by rw [h_norm_sq, ← ENNReal.ofReal_mul (h_len_nn i)]),
    ← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)),
    ENNReal.toReal_ofReal
      (Finset.sum_nonneg (fun i _ => mul_nonneg (h_len_nn i) (sq_nonneg _)))]

/-- **Simple-level quadratic-variation martingale.** For an adapted simple
integrand `G` (horizon `T > 0`), the compensated square
`t ↦ (∫₀ᵗ G dW)² − ∫₀ᵗ G² ds` is a martingale wrt the natural filtration. The
conditional increment `𝔼[(I_t − I_s)² | ℱ_s]` equals `𝔼[A_t − A_s | ℱ_s]` by the
set-level Itô isometry (`simpleIntegral_sub_sq_bochner_clamped_weighted` with
`g = 1_B`), matched against the clamped compensator
(`setIntegral_eval_sq_Icc_clamped`); the conditional Pythagoras
(`condExp_sq_increment_of_martingale`) then gives the martingale identity for
`0 ≤ s ≤ t`, and the `s < 0` case follows by the tower property. -/
lemma martingale_simpleIntegral_sq_sub_compensator
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (hT : 0 < T) (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
        (G.partition i.castSucc)) (G.ξ i)) :
    MeasureTheory.Martingale
      (fun t ω => (simpleIntegral W G t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P := by
  set ℱ := LevyStochCalc.Brownian.Martingale.naturalFiltration W with hℱ
  have hImart : MeasureTheory.Martingale (fun u => simpleIntegral W G u) ℱ P :=
    martingale_simpleIntegral_brownian W G h_adapt
  -- `I_u ∈ L²(P)` at every time.
  have hIL2 : ∀ u, MeasureTheory.MemLp (fun ω => simpleIntegral W G u ω) 2 P := by
    intro u
    rcases le_or_gt u 0 with hu | hu
    · have heq : (fun ω => simpleIntegral W G u ω) = fun _ => (0 : ℝ) :=
        funext (fun ω => simpleIntegral_eq_zero_of_nonpos W G hu ω)
      rw [heq]; exact MeasureTheory.memLp_const 0
    · rcases le_or_gt u T with huT | huT
      · exact simpleIntegral_memLp_intermediate_brownian W hT G h_adapt (le_of_lt hu) huT
      · have heq : (fun ω => simpleIntegral W G u ω) = (fun ω => simpleIntegral W G T ω) := by
          funext ω; unfold simpleIntegral
          refine Finset.sum_congr rfl (fun i _ => ?_)
          have hps : G.partition i.succ ≤ T :=
            le_trans (G.partition_strictMono.monotone (Fin.le_last _)) G.partition_le_T
          have hpc : G.partition i.castSucc ≤ T :=
            le_trans (G.partition_strictMono.monotone (Fin.le_last _)) G.partition_le_T
          rw [min_eq_left (le_trans hps (le_of_lt huT)),
            min_eq_left (le_trans hpc (le_of_lt huT)), min_eq_left hps, min_eq_left hpc]
        rw [heq]
        exact simpleIntegral_memLp_intermediate_brownian W hT G h_adapt (le_of_lt hT) (le_refl T)
  -- `ξᵢ²` integrable.
  have hξ2int : ∀ i : Fin G.N, MeasureTheory.Integrable (fun ω => (G.ξ i ω) ^ 2) P := fun i => by
    obtain ⟨M, hM⟩ := G.ξ_bounded i
    refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (M ^ 2))
      ((G.ξ_measurable i).pow_const 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact sq_le_sq' (neg_le_of_abs_le (hM ω)) (le_of_abs_le (hM ω))
  -- The compensator `A_u = ∫₀ᵘ G²` is integrable …
  have hAint : ∀ u, MeasureTheory.Integrable
      (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume) P := by
    intro u
    rcases le_or_gt 0 u with hu | hu
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun ω => ∑ i : Fin G.N,
              (min (G.partition i.succ) u - min (G.partition i.castSucc) u) * (G.ξ i ω) ^ 2 :=
        funext (fun ω => setIntegral_eval_sq_Icc_clamped G ω hu)
      rw [heq]
      exact MeasureTheory.integrable_finsetSum _ (fun i _ => (hξ2int i).const_mul _)
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr hu)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  -- … and `ℱ_u`-adapted.
  have hA_adapt : ∀ u, @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
      (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume) := by
    intro u
    rcases le_or_gt 0 u with hu | hu
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun ω => ∑ i : Fin G.N,
              (min (G.partition i.succ) u - min (G.partition i.castSucc) u) * (G.ξ i ω) ^ 2 :=
        funext (fun ω => setIntegral_eval_sq_Icc_clamped G ω hu)
      rw [heq]
      refine Finset.stronglyMeasurable_fun_sum _ (fun i _ => ?_)
      by_cases hc : G.partition i.castSucc < u
      · have hle : ℱ.seq (G.partition i.castSucc) ≤ ℱ.seq u := ℱ.mono (le_of_lt hc)
        have hξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u) (fun ω => (G.ξ i ω) ^ 2) := by
          simpa [pow_two] using ((h_adapt i).mono hle).mul ((h_adapt i).mono hle)
        exact hξ2.const_mul _
      · push_neg at hc
        have hcoef : min (G.partition i.succ) u - min (G.partition i.castSucc) u = 0 := by
          rw [min_eq_right hc, min_eq_right
            (le_trans hc (le_of_lt (G.partition_strictMono Fin.castSucc_lt_succ)))]; ring
        rw [show (fun ω => (min (G.partition i.succ) u - min (G.partition i.castSucc) u)
              * (G.ξ i ω) ^ 2) = fun _ => (0 : ℝ) from by funext ω; rw [hcoef, zero_mul]]
        exact stronglyMeasurable_const
    · have heq : (fun ω => ∫ v in Set.Icc (0 : ℝ) u, (G.eval v ω) ^ 2 ∂volume)
          = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr hu)]; simp
      rw [heq]; exact stronglyMeasurable_const
  -- the per-point clamp identity `(Δᵗ − Δˢ) = max s (min p t) − …`.
  have hclamp : ∀ (s t : ℝ), s ≤ t → ∀ p : ℝ,
      max s (min p t) = s + min p t - min p s := by
    intro s t hst p
    have h1 : min s (min p t) = min p s := by
      rw [min_comm s (min p t), min_assoc, min_eq_right hst]
    have h2 := max_add_min s (min p t)
    rw [h1] at h2; linarith
  -- conditional martingale identity for `0 ≤ s ≤ t`, via set integrals.
  have hcond : ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      P[(fun ω => (simpleIntegral W G t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
        =ᵐ[P] fun ω => (simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
    intro s t hs hst
    have hm : ℱ.seq s ≤ ‹MeasurableSpace Ω› := ℱ.le s
    have hIt2 : MeasureTheory.Integrable (fun ω => (simpleIntegral W G t ω) ^ 2) P :=
      (hIL2 t).integrable_sq
    have hIs2 : MeasureTheory.Integrable (fun ω => (simpleIntegral W G s ω) ^ 2) P :=
      (hIL2 s).integrable_sq
    have hIinc_int : MeasureTheory.Integrable
        (fun ω => (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2) P := by
      simpa [pow_two] using ((hIL2 t).sub (hIL2 s)).integrable_sq
    have hNs_meas : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
        (fun ω => (simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) := by
      have hIs2m : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq s)
          (fun ω => (simpleIntegral W G s ω) ^ 2) := by
        simpa [pow_two] using (hImart.stronglyAdapted s).mul (hImart.stronglyAdapted s)
      exact hIs2m.sub (hA_adapt s)
    refine (MeasureTheory.ae_eq_condExp_of_forall_setIntegral_eq hm (hIt2.sub (hAint t))
      (fun B _ _ => (hIs2.sub (hAint s)).integrableOn) (fun B hB _ => ?_)
      hNs_meas.aestronglyMeasurable).symm
    -- goal: `∫_B N_s = ∫_B N_t`. Split both via term-mode `integral_sub`.
    simp only [Pi.sub_apply]
    have hsplitN_s : ∫ ω in B, ((simpleIntegral W G s ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub hIs2.integrableOn (hAint s).integrableOn
    have hsplitN_t : ∫ ω in B, ((simpleIntegral W G t ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (simpleIntegral W G t ω) ^ 2 ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub hIt2.integrableOn (hAint t).integrableOn
    have hsplitA : ∫ ω in B, ((∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P
        = (∫ ω in B, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) ∂P)
          - ∫ ω in B, (∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P :=
      MeasureTheory.integral_sub (hAint t).integrableOn (hAint s).integrableOn
    -- set Pythagoras: `∫_B (I_t−I_s)² = ∫_B I_t² − ∫_B I_s²`.
    have hsetpyth : ∫ ω in B, (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2 ∂P
        = (∫ ω in B, (simpleIntegral W G t ω) ^ 2 ∂P)
          - ∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P := by
      have hpyth := condExp_sq_increment_of_martingale hImart (hIL2 s) (hIL2 t) hst
      calc ∫ ω in B, (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2 ∂P
          = ∫ ω in B, (P[(fun ω => (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2)
              | ℱ.seq s]) ω ∂P := (MeasureTheory.setIntegral_condExp hm hIinc_int hB).symm
        _ = ∫ ω in B, ((P[(fun ω => (simpleIntegral W G t ω) ^ 2) | ℱ.seq s]) ω
              - (simpleIntegral W G s ω) ^ 2) ∂P :=
            MeasureTheory.setIntegral_congr_ae (hm B hB) (hpyth.mono (fun ω hω _ => hω))
        _ = (∫ ω in B, (P[(fun ω => (simpleIntegral W G t ω) ^ 2) | ℱ.seq s]) ω ∂P)
              - ∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P :=
            MeasureTheory.integral_sub MeasureTheory.integrable_condExp.integrableOn
              hIs2.integrableOn
        _ = (∫ ω in B, (simpleIntegral W G t ω) ^ 2 ∂P)
              - ∫ ω in B, (simpleIntegral W G s ω) ^ 2 ∂P := by
            rw [MeasureTheory.setIntegral_condExp hm hIt2 hB]
    -- set isometry: `∫_B (I_t−I_s)² = ∫_B (A_t − A_s)`.
    have hgmeas : Measurable (Set.indicator B (fun _ => (1 : ℝ))) :=
      (measurable_const).indicator (hm B hB)
    have hg_bdd : ∀ ω, |Set.indicator B (fun _ => (1 : ℝ)) ω| ≤ 1 := fun ω => by
      by_cases hω : ω ∈ B
      · rw [Set.indicator_of_mem hω]; norm_num
      · rw [Set.indicator_of_notMem hω]; norm_num
    have hind : ∀ (F : Ω → ℝ), ∫ ω in B, F ω ∂P
        = ∫ ω, Set.indicator B (fun _ => (1 : ℝ)) ω * F ω ∂P := by
      intro F
      have heqf : (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω * F ω) = Set.indicator B F := by
        funext ω
        by_cases hω : ω ∈ B <;>
          simp [Set.indicator_of_mem, Set.indicator_of_notMem, hω]
      rw [heqf, MeasureTheory.integral_indicator (hm B hB)]
    have hiso_set : ∫ ω in B, (simpleIntegral W G t ω - simpleIntegral W G s ω) ^ 2 ∂P
        = ∫ ω in B, ((∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume) ∂P := by
      rw [hind, simpleIntegral_sub_sq_bochner_clamped_weighted W G h_adapt hs hst
        (stronglyMeasurable_const.indicator hB) hg_bdd]
      have hAdiff : ∀ ω, (∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume
          = ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
              - max s (min (G.partition i.castSucc) t)) * (G.ξ i ω) ^ 2 := by
        intro ω
        rw [setIntegral_eval_sq_Icc_clamped G ω (le_trans hs hst),
          setIntegral_eval_sq_Icc_clamped G ω hs, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← sub_mul]; congr 1
        rw [hclamp s t hst (G.partition i.succ), hclamp s t hst (G.partition i.castSucc)]; ring
      rw [MeasureTheory.setIntegral_congr_fun (hm B hB) (fun ω _ => hAdiff ω), hind,
        show (fun ω => Set.indicator B (fun _ => (1 : ℝ)) ω
              * ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
                - max s (min (G.partition i.castSucc) t)) * (G.ξ i ω) ^ 2)
            = fun ω => ∑ i : Fin G.N, (max s (min (G.partition i.succ) t)
                - max s (min (G.partition i.castSucc) t))
                  * (Set.indicator B (fun _ => (1 : ℝ)) ω * (G.ξ i ω) ^ 2) from by
          funext ω; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun i _ => by ring)]
      rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
        (((hξ2int i).bdd_mul (c := 1) hgmeas.aestronglyMeasurable
          (Filter.Eventually.of_forall
            (fun ω => (Real.norm_eq_abs _).le.trans (hg_bdd ω)))).const_mul _))]
      exact Finset.sum_congr rfl (fun i _ => by rw [MeasureTheory.integral_const_mul])
    -- combine: `∫_B N_s = ∫_B N_t`.
    rw [hsetpyth] at hiso_set
    linarith [hiso_set, hsplitN_s, hsplitN_t, hsplitA]
  -- assemble the full martingale (handle `s < 0` by the tower property).
  refine ⟨?_, fun s t hst => ?_⟩
  · intro u
    have hI2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq u)
        (fun ω => (simpleIntegral W G u ω) ^ 2) := by
      simpa [pow_two] using (hImart.stronglyAdapted u).mul (hImart.stronglyAdapted u)
    exact hI2.sub (hA_adapt u)
  · rcases le_or_gt 0 s with hs | hs
    · exact hcond s t hs hst
    · have hN0 : (fun ω => (simpleIntegral W G 0 ω) ^ 2
          - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (G.eval u ω) ^ 2 ∂volume) =ᵐ[P] 0 := by
        filter_upwards with ω
        rw [simpleIntegral_eq_zero_of_nonpos W G (le_refl 0) ω,
          setIntegral_eval_sq_Icc_clamped G ω (le_refl 0)]
        have : ∀ i : Fin G.N, (min (G.partition i.succ) (0 : ℝ)
            - min (G.partition i.castSucc) (0 : ℝ)) * (G.ξ i ω) ^ 2 = 0 := by
          intro i
          have hp1 : (0 : ℝ) ≤ G.partition i.succ := by
            have := G.partition_strictMono.monotone (Fin.zero_le i.succ)
            rwa [G.partition_zero] at this
          have hp2 : (0 : ℝ) ≤ G.partition i.castSucc := by
            have := G.partition_strictMono.monotone (Fin.zero_le i.castSucc)
            rwa [G.partition_zero] at this
          rw [min_eq_right hp1, min_eq_right hp2, sub_self, zero_mul]
        rw [Finset.sum_eq_zero (fun i _ => this i)]; simp
      have hle0 : ℱ.seq s ≤ ℱ.seq 0 := ℱ.mono (le_of_lt hs)
      rcases le_or_gt 0 t with ht | ht
      · have h0 := hcond 0 t (le_refl 0) ht
        calc P[(fun ω => (simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
            =ᵐ[P] P[P[(fun ω => (simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq 0] | ℱ.seq s] :=
              (MeasureTheory.condExp_condExp_of_le hle0 (ℱ.le 0)).symm
          _ =ᵐ[P] P[(fun ω => (simpleIntegral W G 0 ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s] :=
              MeasureTheory.condExp_congr_ae h0
          _ =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hN0
          _ =ᵐ[P] fun ω => (simpleIntegral W G s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [simpleIntegral_eq_zero_of_nonpos W G (le_of_lt hs) ω,
                Set.Icc_eq_empty (not_le.mpr hs)]
              simp
      · -- `t < 0`: both sides are a.e. `0`.
        have hNt : (fun ω => (simpleIntegral W G t ω) ^ 2
            - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) =ᵐ[P] 0 := by
          filter_upwards with ω
          rw [simpleIntegral_eq_zero_of_nonpos W G (le_of_lt ht) ω,
            Set.Icc_eq_empty (not_le.mpr ht)]; simp
        calc P[(fun ω => (simpleIntegral W G t ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t, (G.eval u ω) ^ 2 ∂volume) | ℱ.seq s]
            =ᵐ[P] P[(0 : Ω → ℝ) | ℱ.seq s] := MeasureTheory.condExp_congr_ae hNt
          _ =ᵐ[P] fun ω => (simpleIntegral W G s ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) s, (G.eval u ω) ^ 2 ∂volume := by
              rw [MeasureTheory.condExp_zero]
              filter_upwards with ω
              rw [simpleIntegral_eq_zero_of_nonpos W G (le_of_lt hs) ω,
                Set.Icc_eq_empty (not_le.mpr hs)]; simp

section MasterSequence

variable
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (H : Ω → ℝ → ℝ) (h_meas : Measurable (Function.uncurry H))
    (h_progMeas : ∀ t : ℝ,
      @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
          inferInstance)
        (fun p : Ω × ℝ => H p.1 p.2))
    (h_sq_int_global : ∀ T, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- Positivity of the master horizon `(n : ℝ) + 1`. -/
private lemma master_horizon_pos (n : ℕ) : (0 : ℝ) < (n : ℝ) + 1 := by positivity

/-- Positivity of the master tolerance `((n : ℝ≥0∞) + 1)⁻¹`. -/
private lemma master_tol_pos (n : ℕ) : (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ :=
  ENNReal.inv_pos.mpr (by
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩)

/-- **Master approximating sequence.** For each `n`, an adapted `SimplePredictable`
on horizon `(n : ℝ) + 1` within `((n : ℝ≥0∞) + 1)⁻¹` of `H` in `L²([0, n+1] × Ω)`.
The horizons grow to `∞`; zero-extension lets these be compared across `n`. -/
noncomputable def masterApprox (n : ℕ) : SimplePredictable Ω ((n : ℝ) + 1) :=
  (exists_adaptedSimple_within W H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose

lemma masterApprox_adapt (n : ℕ) :
    ∀ i : Fin (masterApprox W H h_meas h_progMeas h_sq_int_global n).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq
          ((masterApprox W H h_meas h_progMeas h_sq_int_global n).partition i.castSucc))
        ((masterApprox W H h_meas h_progMeas h_sq_int_global n).ξ i) :=
  (exists_adaptedSimple_within W H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose_spec.1

lemma masterApprox_within (n : ℕ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1),
      (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ((n : ℝ≥0∞) + 1)⁻¹ :=
  (exists_adaptedSimple_within W H h_meas h_progMeas (master_horizon_pos n)
    (h_sq_int_global _ (master_horizon_pos n)) (master_tol_pos n)).choose_spec.2

/-- **Cross-horizon difference isometry for the master sequence.** Extending both
`masterApprox n` and `masterApprox m` to the common horizon `max n m + 2` (via
`appendInterval`, which leaves their `simpleIntegral` and `eval` unchanged), the
difference isometry gives `∫⁻‖Iₙ(t) − Iₘ(t)‖² = ∫⁻∫⁻_{[0,t]}‖Gₙ.eval − Gₘ.eval‖²`
for every `t ≥ 0`. -/
lemma masterApprox_diff_isometry (n m : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω
        - simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global m) t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖(masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω
            - (masterApprox W H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P := by
  set Gn := masterApprox W H h_meas h_progMeas h_sq_int_global n with hGn
  set Gm := masterApprox W H h_meas h_progMeas h_sq_int_global m with hGm
  have hKn : Gn.partition (Fin.last Gn.N) < (max n m : ℝ) + 2 := by
    have h1 : Gn.partition (Fin.last Gn.N) ≤ (n : ℝ) + 1 := Gn.partition_le_T
    have h2 : (n : ℝ) ≤ (max n m : ℝ) := by exact_mod_cast Nat.le_max_left n m
    linarith
  have hKm : Gm.partition (Fin.last Gm.N) < (max n m : ℝ) + 2 := by
    have h1 : Gm.partition (Fin.last Gm.N) ≤ (m : ℝ) + 1 := Gm.partition_le_T
    have h2 : (m : ℝ) ≤ (max n m : ℝ) := by exact_mod_cast Nat.le_max_right n m
    linarith
  have h_eq : (Gn.appendInterval hKn).partition (Fin.last (Gn.appendInterval hKn).N)
      = (Gm.appendInterval hKm).partition (Fin.last (Gm.appendInterval hKm).N) :=
    (Gn.appendInterval_partition_last hKn).trans (Gm.appendInterval_partition_last hKm).symm
  have ha_n := Gn.appendInterval_adapt W hKn (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n)
  have ha_m := Gm.appendInterval_adapt W hKm (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global m)
  have hiso := simpleIntegral_intermediate_diff_isometry W (Gn.appendInterval hKn)
    (Gm.appendInterval hKm) h_eq ha_n ha_m ht_nn
  have hL : ∫⁻ ω, (‖simpleIntegral W Gn t ω - simpleIntegral W Gm t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, (‖simpleIntegral W (Gn.appendInterval hKn) t ω
          - simpleIntegral W (Gm.appendInterval hKm) t ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    refine lintegral_congr (fun ω => ?_)
    rw [Gn.appendInterval_simpleIntegral W hKn t ω, Gm.appendInterval_simpleIntegral W hKm t ω]
  have hR : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖(Gn.appendInterval hKn).eval s ω - (Gm.appendInterval hKm).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P := by
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [Gn.appendInterval_eval hKn s ω, Gm.appendInterval_eval hKm s ω]
  rw [hL, hR]; exact hiso

/-- `((n : ℝ≥0∞) + 1)⁻¹ → 0`. -/
private lemma tendsto_master_tol :
    Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
  have := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
  refine this.congr (fun n => ?_)
  simp [Nat.cast_add_one]

/-- **Per-time eval convergence of the master sequence.** For each `t ≥ 0`,
`∫⁻∫⁻_{[0,t]}‖H − Gₙ.eval‖² → 0`: eventually (`t ≤ n+1`) it is `≤ ((n:ℝ≥0∞)+1)⁻¹`
by `Set.Icc` monotonicity + `masterApprox_within`, and that bound tends to `0`. -/
lemma masterApprox_eval_tendsto {t : ℝ} (ht_nn : 0 ≤ t) :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
      Filter.atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_master_tol
    (Filter.Eventually.of_forall (fun n => bot_le)) ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈t⌉₊] with n hn
  have htn : t ≤ (n : ℝ) + 1 := by
    have h1 : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2 : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) ((n : ℝ) + 1),
          (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P :=
        MeasureTheory.lintegral_mono
          (fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right htn))
    _ ≤ ((n : ℝ≥0∞) + 1)⁻¹ := le_of_lt (masterApprox_within W H h_meas h_progMeas h_sq_int_global n)

/-- **Cauchy bound for the master integrals.** Via the cross-horizon difference
isometry + the triangle `‖a − b‖² ≤ 2(‖a − H‖² + ‖H − b‖²)`. -/
lemma masterApprox_cauchy_le (n m : ℕ) {t : ℝ} (ht_nn : 0 ≤ t) :
    ∫⁻ ω, (‖simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω
        - simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global m) t ω‖₊
          : ℝ≥0∞) ^ 2 ∂P
      ≤ 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P) := by
  set Gn := masterApprox W H h_meas h_progMeas h_sq_int_global n with hGn
  set Gm := masterApprox W H h_meas h_progMeas h_sq_int_global m with hGm
  rw [masterApprox_diff_isometry W H h_meas h_progMeas h_sq_int_global n m ht_nn]
  -- abbreviations for the two error densities
  set A : Ω → ℝ → ℝ≥0∞ := fun ω s => (‖H ω s - Gn.eval s ω‖₊ : ℝ≥0∞) ^ 2 with hA
  set B : Ω → ℝ → ℝ≥0∞ := fun ω s => (‖H ω s - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 with hB
  have h_point : ∀ ω, ∀ s,
      (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (A ω s + B ω s) := by
    intro ω s
    have hrw : Gn.eval s ω - Gm.eval s ω
        = -(H ω s - Gn.eval s ω) + (H ω s - Gm.eval s ω) := by ring
    rw [hrw, hA, hB]
    refine le_trans (sq_nnnorm_add_le_two_mul_brownian _ _) ?_
    rw [show ‖-(H ω s - Gn.eval s ω)‖₊ = ‖H ω s - Gn.eval s ω‖₊ from by rw [nnnorm_neg]]
  -- joint measurability of `A` and the `s`-section measurability
  have hH_pair : Measurable (fun p : Ω × ℝ => H p.1 p.2) := h_meas
  have hA_pair : Measurable (fun p : Ω × ℝ => A p.1 p.2) := by
    rw [hA]
    exact (((hH_pair.sub Gn.eval_jointly_measurable).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hB_pair : Measurable (fun p : Ω × ℝ => B p.1 p.2) := by
    rw [hB]
    exact (((hH_pair.sub Gm.eval_jointly_measurable).nnnorm).coe_nnreal_ennreal).pow_const 2
  have hA_s : ∀ ω, Measurable (A ω) := fun ω =>
    hA_pair.comp (measurable_const.prodMk measurable_id)
  have hA_outer : Measurable (fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume) :=
    Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t)) hA_pair
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖Gn.eval s ω - Gm.eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, 2 * (A ω s + B ω s) ∂volume ∂P :=
        MeasureTheory.lintegral_mono (fun ω =>
          MeasureTheory.lintegral_mono (fun s => h_point ω s))
    _ = 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, B ω s ∂volume ∂P) := by
        have h_inner : ∀ ω, (∫⁻ s in Set.Icc (0 : ℝ) t, 2 * (A ω s + B ω s) ∂volume)
            = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) t, A ω s ∂volume)
              + ∫⁻ s in Set.Icc (0 : ℝ) t, B ω s ∂volume) := by
          intro ω
          rw [MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
              MeasureTheory.lintegral_add_left' (hA_s ω).aemeasurable]
        rw [MeasureTheory.lintegral_congr h_inner,
            MeasureTheory.lintegral_const_mul' 2 _ (by norm_num),
            MeasureTheory.lintegral_add_left' hA_outer.aemeasurable]

/-- The master integral `simpleIntegral W (masterApprox n) t` lifted to `Lp ℝ 2 P`
(for `0 ≤ t ≤ n+1`; `0` otherwise). The Itô integral process is its `L²`-limit. -/
noncomputable def masterLp (t : ℝ) (n : ℕ) : MeasureTheory.Lp ℝ 2 P :=
  if h : 0 ≤ t ∧ t ≤ (n : ℝ) + 1 then
    (simpleIntegral_memLp_intermediate_brownian W (master_horizon_pos n)
      (masterApprox W H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n) h.1 h.2).toLp
  else 0

lemma masterLp_coeFn {t : ℝ} (n : ℕ) (ht_nn : 0 ≤ t) (htn : t ≤ (n : ℝ) + 1) :
    (masterLp W H h_meas h_progMeas h_sq_int_global t n : Ω → ℝ)
      =ᵐ[P] fun ω => simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω := by
  rw [masterLp, dif_pos ⟨ht_nn, htn⟩]
  exact MeasureTheory.MemLp.coeFn_toLp _

/-- The Itô-integral process is `L²`-Cauchy at each time `t ≥ 0`. -/
lemma masterLp_cauchySeq {t : ℝ} (ht_nn : 0 ≤ t) :
    CauchySeq (fun n => masterLp W H h_meas h_progMeas h_sq_int_global t n) := by
  rw [EMetric.cauchySeq_iff]
  intro ε hε
  by_cases hε_top : ε = ⊤
  · refine ⟨⌈t⌉₊, fun m hm n hn => ?_⟩
    rw [hε_top]; exact lt_top_iff_ne_top.mpr (edist_ne_top _ _)
  · set δ : ℝ≥0∞ := ε ^ (2 : ℝ) / 4 with hδ
    have hε2_ne_top : ε ^ (2 : ℝ) ≠ ⊤ := by
      simp [ENNReal.rpow_eq_top_iff, hε_top]
    have hδ_pos : 0 < δ := by
      rw [hδ]; exact ENNReal.div_pos (ENNReal.rpow_pos hε hε_top).ne' (by norm_num)
    have htend := masterApprox_eval_tendsto W H h_meas h_progMeas h_sq_int_global ht_nn
    have hev : ∀ᶠ k in Filter.atTop,
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global k).eval s ω‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < δ := htend (Iio_mem_nhds hδ_pos)
    rw [Filter.eventually_atTop] at hev
    obtain ⟨N0, hN0⟩ := hev
    refine ⟨max N0 ⌈t⌉₊, fun m hm n hn => ?_⟩
    have hmt : t ≤ (m : ℝ) + 1 := by
      have : (⌈t⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_max_right N0 ⌈t⌉₊).trans hm
      have := Nat.le_ceil t; linarith
    have hnt : t ≤ (n : ℝ) + 1 := by
      have : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast (le_max_right N0 ⌈t⌉₊).trans hn
      have := Nat.le_ceil t; linarith
    have hmN0 : N0 ≤ m := (le_max_left N0 ⌈t⌉₊).trans hm
    have hnN0 : N0 ≤ n := (le_max_left N0 ⌈t⌉₊).trans hn
    -- edist = eLpNorm of the integral difference
    have em : masterLp W H h_meas h_progMeas h_sq_int_global t m
        = (simpleIntegral_memLp_intermediate_brownian W (master_horizon_pos m)
            (masterApprox W H h_meas h_progMeas h_sq_int_global m)
            (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global m) ht_nn hmt).toLp := by
      rw [masterLp]; exact dif_pos ⟨ht_nn, hmt⟩
    have en : masterLp W H h_meas h_progMeas h_sq_int_global t n
        = (simpleIntegral_memLp_intermediate_brownian W (master_horizon_pos n)
            (masterApprox W H h_meas h_progMeas h_sq_int_global n)
            (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n) ht_nn hnt).toLp := by
      rw [masterLp]; exact dif_pos ⟨ht_nn, hnt⟩
    have h_edist : edist (masterLp W H h_meas h_progMeas h_sq_int_global t m)
          (masterLp W H h_meas h_progMeas h_sq_int_global t n)
        = MeasureTheory.eLpNorm
            (fun ω => simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global m) t ω
              - simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω) 2 P := by
      rw [em, en]
      exact MeasureTheory.Lp.edist_toLp_toLp _ _ _ _
    rw [h_edist]
    -- eLpNorm² < ε²  ⇒  eLpNorm < ε
    have h_sq_lt : MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global m) t ω
          - simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω) 2 P
          ^ (2 : ℝ) < ε ^ (2 : ℝ) := by
      rw [eLpNorm_two_rpow_eq_lintegral_sq]
      refine lt_of_le_of_lt
        (masterApprox_cauchy_le W H h_meas h_progMeas h_sq_int_global m n ht_nn) ?_
      have hsum : (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P)
          + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < δ + δ :=
        ENNReal.add_lt_add (hN0 m hmN0) (hN0 n hnN0)
      calc 2 * ((∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global m).eval s ω‖₊ : ℝ≥0∞) ^ 2
                  ∂volume ∂P)
              + ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
                (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
                  ∂volume ∂P)
          < 2 * (δ + δ) := by gcongr <;> first | exact hsum | simp
        _ = ε ^ (2 : ℝ) := by
            have h4 : (2 : ℝ≥0∞) * (δ + δ) = 4 * δ := by ring
            rw [h4, hδ, ENNReal.mul_div_cancel (show (4 : ℝ≥0∞) ≠ 0 by norm_num)
              (show (4 : ℝ≥0∞) ≠ ⊤ by simp)]
    exact (ENNReal.rpow_lt_rpow_iff (by norm_num : (0 : ℝ) < 2)).mp h_sq_lt

/-- The **L² Itô integral process** as an `Lp ℝ 2 P`-valued function of time: the
`L²`-limit of the master integral sequence. -/
noncomputable def stochasticIntegralBrownianLp (t : ℝ) : MeasureTheory.Lp ℝ 2 P :=
  Filter.limUnder Filter.atTop (fun n => masterLp W H h_meas h_progMeas h_sq_int_global t n)

/-- Each master integral lies in `lpMeas` — it is `ℱ_t`-measurable. -/
lemma masterLp_mem_lpMeas (t : ℝ) (n : ℕ) :
    masterLp W H h_meas h_progMeas h_sq_int_global t n
      ∈ MeasureTheory.lpMeas ℝ ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t) 2 P := by
  rw [masterLp]
  split_ifs with h
  · rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
    refine ((simpleIntegral_stronglyAdapted_brownian W
      (masterApprox W H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n)
        t).aestronglyMeasurable).congr ?_
    exact (MeasureTheory.MemLp.coeFn_toLp _).symm
  · exact Submodule.zero_mem _

/-- The Itô integral process lies in `lpMeas` at each time (closedness of `lpMeas`
+ the `L²`-Cauchy limit of `ℱ_t`-measurable master integrals). -/
lemma stochasticIntegralBrownianLp_mem_lpMeas (t : ℝ) :
    stochasticIntegralBrownianLp W H h_meas h_progMeas h_sq_int_global t
      ∈ MeasureTheory.lpMeas ℝ ℝ
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t) 2 P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  have hcs : CauchySeq (fun n => masterLp W H h_meas h_progMeas h_sq_int_global t n) := by
    rcases le_or_gt 0 t with ht | ht
    · exact masterLp_cauchySeq W H h_meas h_progMeas h_sq_int_global ht
    · have heq : (fun n => masterLp W H h_meas h_progMeas h_sq_int_global t n)
          = fun _ => (0 : MeasureTheory.Lp ℝ 2 P) := by
        funext n; rw [masterLp, dif_neg (fun h => absurd h.1 (not_le.mpr ht))]
      rw [heq]; exact (tendsto_const_nhds (x := (0 : MeasureTheory.Lp ℝ 2 P))).cauchySeq
  rw [MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable]
  have hclosed : IsClosed {f : MeasureTheory.Lp ℝ 2 P |
      AEStronglyMeasurable[(LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t]
        (↑↑f : Ω → ℝ) P} :=
    MeasureTheory.isClosed_aestronglyMeasurable
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le t)
  exact hclosed.mem_of_tendsto hcs.tendsto_limUnder
    (Filter.Eventually.of_forall
      (fun n => MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp
        (masterLp_mem_lpMeas W H h_meas h_progMeas h_sq_int_global t n)))

/-- `↑↑(Flp t)` is `ℱ_t`-a.e.-strongly-measurable. -/
lemma stochasticIntegralBrownian_aesm (t : ℝ) :
    AEStronglyMeasurable[(LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t]
      (↑↑(stochasticIntegralBrownianLp W H h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) P :=
  MeasureTheory.mem_lpMeas_iff_aestronglyMeasurable.mp
    (stochasticIntegralBrownianLp_mem_lpMeas W H h_meas h_progMeas h_sq_int_global t)

/-- The **L² Itô integral** `t ↦ ∫_0^t H_s dW_s` as a process `ℝ → Ω → ℝ`, taken as
the honest `ℱ_t`-measurable representative of the `L²`-limit. -/
noncomputable def stochasticIntegralBrownian (t : ℝ) : Ω → ℝ :=
  (stochasticIntegralBrownian_aesm W H h_meas h_progMeas h_sq_int_global t).mk
    (↑↑(stochasticIntegralBrownianLp W H h_meas h_progMeas h_sq_int_global t))

/-- The integral process is a.e.-equal to the `L²`-limit's `coeFn`. -/
lemma stochasticIntegralBrownian_ae_eq (t : ℝ) :
    stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] (↑↑(stochasticIntegralBrownianLp W H h_meas h_progMeas h_sq_int_global t) : Ω → ℝ) :=
  (stochasticIntegralBrownian_aesm W H h_meas h_progMeas h_sq_int_global t).ae_eq_mk.symm

/-- The integral process is strongly adapted to the natural filtration. -/
lemma stochasticIntegralBrownian_stronglyAdapted :
    MeasureTheory.StronglyAdapted (LevyStochCalc.Brownian.Martingale.naturalFiltration W)
      (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global) :=
  fun t => (stochasticIntegralBrownian_aesm W H h_meas h_progMeas h_sq_int_global t).stronglyMeasurable_mk

/-- **L²-convergence of the master integrals to the Itô integral process.** -/
lemma masterApprox_tendsto_L2 {t : ℝ} (ht_nn : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω
          - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t ω) 2 P)
      Filter.atTop (nhds 0) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Flp := stochasticIntegralBrownianLp W H h_meas h_progMeas h_sq_int_global t with hFlp
  have h1 : Filter.Tendsto (fun n => masterLp W H h_meas h_progMeas h_sq_int_global t n)
      Filter.atTop (nhds Flp) :=
    (masterLp_cauchySeq W H h_meas h_progMeas h_sq_int_global ht_nn).tendsto_limUnder
  have hmem : MeasureTheory.MemLp (↑↑Flp : Ω → ℝ) 2 P := MeasureTheory.Lp.memLp Flp
  rw [← MeasureTheory.Lp.toLp_coeFn Flp hmem] at h1
  have h2 := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm
    (fun n => masterLp W H h_meas h_progMeas h_sq_int_global t n) (↑↑Flp) hmem).mp h1
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_ge_atTop ⌈t⌉₊] with n hn
  have hcn : t ≤ (n : ℝ) + 1 := by
    have h1' : t ≤ (⌈t⌉₊ : ℝ) := Nat.le_ceil t
    have h2' : (⌈t⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  refine MeasureTheory.eLpNorm_congr_ae ?_
  filter_upwards [masterLp_coeFn W H h_meas h_progMeas h_sq_int_global n ht_nn hcn,
    stochasticIntegralBrownian_ae_eq W H h_meas h_progMeas h_sq_int_global t] with ω hω hF
  simp only [Pi.sub_apply]
  rw [hω, hF]

/-- For `t < 0` the integral process is the zero `Lp` element. -/
lemma stochasticIntegralBrownianLp_eq_zero_of_neg {t : ℝ} (ht : t < 0) :
    stochasticIntegralBrownianLp W H h_meas h_progMeas h_sq_int_global t = 0 := by
  rw [stochasticIntegralBrownianLp]
  have heq : (fun n => masterLp W H h_meas h_progMeas h_sq_int_global t n)
      = fun _ => (0 : MeasureTheory.Lp ℝ 2 P) := by
    funext n; rw [masterLp, dif_neg (fun h => absurd h.1 (not_le.mpr ht))]
  rw [heq]
  exact tendsto_const_nhds.limUnder_eq

/-- For `t < 0` the integral process is a.e. zero. -/
lemma stochasticIntegralBrownian_ae_zero_of_neg {t : ℝ} (ht : t < 0) :
    stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  refine (stochasticIntegralBrownian_ae_eq W H h_meas h_progMeas h_sq_int_global t).trans ?_
  rw [stochasticIntegralBrownianLp_eq_zero_of_neg W H h_meas h_progMeas h_sq_int_global ht]
  exact MeasureTheory.Lp.coeFn_zero ℝ 2 P

/-- **Conjunct 1: the Itô integral process is a martingale** (wrt the natural
filtration). The master integrals are martingales, converge in `L¹` (from `L²`),
and `F` is adapted + integrable. -/
lemma martingale_stochasticIntegralBrownian :
    MeasureTheory.Martingale (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P := by
  refine martingale_of_tendsto_eLpNorm_one
    (M := fun n t => simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t)
    (fun n => martingale_simpleIntegral_brownian W
      (masterApprox W H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (martingale_simpleIntegral_brownian W
      (masterApprox W H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (stochasticIntegralBrownian_stronglyAdapted W H h_meas h_progMeas h_sq_int_global)
    (fun t => ((MeasureTheory.Lp.memLp _).integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)).congr
      (stochasticIntegralBrownian_ae_eq W H h_meas h_progMeas h_sq_int_global t).symm)
    (fun t => ?_)
  rcases le_or_gt 0 t with ht | ht
  · refine tendsto_eLpNorm_one_of_eLpNorm_two (fun n => ?_)
      (masterApprox_tendsto_L2 W H h_meas h_progMeas h_sq_int_global ht)
    refine (Measurable.aestronglyMeasurable ?_).sub
      (((stochasticIntegralBrownian_stronglyAdapted W H h_meas h_progMeas h_sq_int_global t).mono
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le t)).aestronglyMeasurable)
    unfold simpleIntegral
    refine Finset.measurable_sum _ (fun i _ => ?_)
    exact ((masterApprox W H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
      ((W.measurable_eval _).sub (W.measurable_eval _))
  · have hzero : ∀ n, MeasureTheory.eLpNorm
        ((fun t' => simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t') t
          - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t) 1 P = 0 := by
      intro n
      have hfae : ((fun t' => simpleIntegral W
            (masterApprox W H h_meas h_progMeas h_sq_int_global n) t') t
          - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t) =ᵐ[P] 0 := by
        filter_upwards [stochasticIntegralBrownian_ae_zero_of_neg W H h_meas h_progMeas
          h_sq_int_global ht] with ω hF
        simp only [Pi.sub_apply, Pi.zero_apply,
          simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, sub_zero]
      rw [MeasureTheory.eLpNorm_congr_ae hfae, MeasureTheory.eLpNorm_zero]
    simp only [hzero]
    exact tendsto_const_nhds

/-- **Eval-L²-norm convergence.** `∫⁻∫⁻_{[0,T]}‖Gₙ.eval‖² → ∫⁻∫⁻_{[0,T]}‖H‖²`.
Lift both to `L²` of the product measure `P ⊗ vol|_{[0,T]}` (Tonelli); the `L²`
difference vanishes (`masterApprox_eval_tendsto`), so the norms converge. -/
lemma masterApprox_evalNorm_tendsto {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) T) with hν
  set Hp : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hHp
  set Gp : ℕ → Ω × ℝ → ℝ := fun n p =>
    (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval p.2 p.1 with hGp
  have hHp_meas : Measurable Hp := h_meas
  have hGp_meas : ∀ n, Measurable (Gp n) := fun n =>
    (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval_jointly_measurable
  -- Tonelli bridge: `eLpNorm f 2 (P⊗ν) ^ 2 = ∫⁻∫⁻_{[0,T]} ‖f(ω,·)‖²`.
  have hbridge : ∀ (f : Ω × ℝ → ℝ), Measurable f →
      MeasureTheory.eLpNorm f 2 (P.prod ν) ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    intro f hf
    rw [eLpNorm_sq_eq_lintegral_nnnorm_sq,
        MeasureTheory.lintegral_prod _
          (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
  -- `eLpNorm < ⊤` from finiteness of the squared mass.
  have hfin : ∀ (f : Ω × ℝ → ℝ), Measurable f →
      (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) →
      MeasureTheory.eLpNorm f 2 (P.prod ν) < ⊤ := by
    intro f hf hfin
    refine lt_top_iff_ne_top.mpr (fun h => hfin ?_)
    rw [← hbridge f hf, h, ENNReal.top_rpow_of_pos (by norm_num)]
  have hHmemLp : MeasureTheory.MemLp Hp 2 (P.prod ν) :=
    ⟨hHp_meas.aestronglyMeasurable, hfin Hp hHp_meas (h_sq_int_global T hT).ne⟩
  have hGmemLp : ∀ n, MeasureTheory.MemLp (Gp n) 2 (P.prod ν) := fun n =>
    ⟨(hGp_meas n).aestronglyMeasurable, hfin (Gp n) (hGp_meas n)
      (eval_lintegral_sq_finite (masterApprox W H h_meas h_progMeas h_sq_int_global n) T).ne⟩
  -- `Gp n → Hp` in `L²(P⊗ν)`.
  have hdiff : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν))
      Filter.atTop (nhds 0) := by
    have hsq : ∀ n, MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ)
        = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P := by
      intro n
      rw [hbridge (Gp n - Hp) ((hGp_meas n).sub hHp_meas)]
      refine lintegral_congr (fun ω =>
        MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_))
      rw [Pi.sub_apply, hGp, hHp, ← nnnorm_neg]
      congr 1; ring
    have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ))
        Filter.atTop (nhds 0) := by
      simp_rw [hsq]
      exact masterApprox_eval_tendsto W H h_meas h_progMeas h_sq_int_global (le_of_lt hT)
    have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
    refine h3.congr (fun n => ?_)
    rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- transfer to `Lp`, take norms.
  have hLp := (MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fun n => Gp n)
    (fun n => hGmemLp n) Hp hHmemLp).mpr hdiff
  have hnorm := hLp.enorm
  simp only [MeasureTheory.Lp.enorm_def] at hnorm
  have hnorm2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n) 2 (P.prod ν))
      Filter.atTop (nhds (MeasureTheory.eLpNorm Hp 2 (P.prod ν))) := by
    rw [MeasureTheory.eLpNorm_congr_ae (MeasureTheory.MemLp.coeFn_toLp hHmemLp)] at hnorm
    refine hnorm.congr (fun n => ?_)
    exact MeasureTheory.eLpNorm_congr_ae (MeasureTheory.MemLp.coeFn_toLp (hGmemLp n))
  -- square and convert via the bridge.
  have := hnorm2.ennrpow_const 2
  simp_rw [hbridge _ (hGp_meas _)] at this
  rw [hbridge Hp hHp_meas] at this
  exact this

/-- **Conjunct 3: the L²-isometry** `∫⁻‖F T‖² = ∫⁻∫⁻_{[0,T]}‖H‖²` for `T > 0`.
The squared `L²`-norm of `Iₙ(T)` equals `∫⁻∫⁻_{[0,T]}‖Gₙ.eval‖²` (intermediate
isometry), converges to `∫⁻‖F T‖²` (norm continuity of the `L²`-limit) and to
`∫⁻∫⁻_{[0,T]}‖H‖²` (`masterApprox_evalNorm_tendsto`); uniqueness of limits. -/
lemma isometry_stochasticIntegralBrownian {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  set Flp := stochasticIntegralBrownianLp W H h_meas h_progMeas h_sq_int_global T with hFlp
  have htend : Filter.Tendsto (fun n => masterLp W H h_meas h_progMeas h_sq_int_global T n)
      Filter.atTop (nhds Flp) :=
    (masterLp_cauchySeq W H h_meas h_progMeas h_sq_int_global (le_of_lt hT)).tendsto_limUnder
  have hn := (htend.enorm).ennrpow_const 2
  simp only [MeasureTheory.Lp.enorm_def] at hn
  -- limit `eLpNorm ↑↑Flp ^ 2 = ∫⁻‖F T‖²`
  have hlim : MeasureTheory.eLpNorm (↑↑Flp : Ω → ℝ) 2 P ^ (2 : ℝ)
      = ∫⁻ ω, (‖stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P := by
    rw [eLpNorm_sq_eq_lintegral_nnnorm_sq]
    refine lintegral_congr_ae ?_
    filter_upwards [stochasticIntegralBrownian_ae_eq W H h_meas h_progMeas h_sq_int_global T]
      with ω hF
    rw [hF]
  rw [hlim] at hn
  have h_a : Filter.Tendsto (fun n => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖(masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      Filter.atTop
      (nhds (∫⁻ ω, (‖stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P)) := by
    refine hn.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop ⌈T⌉₊] with n hn'
    have hcn : T ≤ (n : ℝ) + 1 := by
      have h1' : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
      have h2' : (⌈T⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn'
      linarith
    rw [MeasureTheory.eLpNorm_congr_ae
        (masterLp_coeFn W H h_meas h_progMeas h_sq_int_global n (le_of_lt hT) hcn),
      eLpNorm_sq_eq_lintegral_nnnorm_sq,
      simpleIntegral_intermediate_isometry W
        (masterApprox W H h_meas h_progMeas h_sq_int_global n)
        (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n) (le_of_lt hT)]
  exact tendsto_nhds_unique h_a
    (masterApprox_evalNorm_tendsto W H h_meas h_progMeas h_sq_int_global hT)

/-- `F t ∈ L²(P)`. -/
lemma stochasticIntegralBrownian_memLp (t : ℝ) :
    MeasureTheory.MemLp (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t) 2 P :=
  (MeasureTheory.Lp.memLp _).ae_eq
    (stochasticIntegralBrownian_ae_eq W H h_meas h_progMeas h_sq_int_global t).symm

/-- `F t =ᵐ 0` for `t ≤ 0`. -/
lemma stochasticIntegralBrownian_ae_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) :
    stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t =ᵐ[P] 0 := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact stochasticIntegralBrownian_ae_zero_of_neg W H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    have h := masterApprox_tendsto_L2 W H h_meas h_progMeas h_sq_int_global (le_refl (0 : ℝ))
    have hconst : ∀ n, MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) 0 ω
          - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global 0 ω) 2 P
        = MeasureTheory.eLpNorm
          (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global 0) 2 P := by
      intro n
      rw [← MeasureTheory.eLpNorm_neg
        (f := stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global 0)]
      refine MeasureTheory.eLpNorm_congr_ae ?_
      filter_upwards with ω
      simp [simpleIntegral_eq_zero_of_nonpos W _ (le_refl (0 : ℝ)) ω]
    simp only [hconst] at h
    have hz : MeasureTheory.eLpNorm
        (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global 0) 2 P = 0 :=
      tendsto_nhds_unique tendsto_const_nhds h
    rwa [MeasureTheory.eLpNorm_eq_zero_iff
      (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global
        0).aestronglyMeasurable
      (by norm_num)] at hz

/-- `∫⁻‖F t‖² = ∫⁻∫⁻_{[0,t]}‖H‖²` for all `t ≥ 0` (isometry, incl. `t = 0`). -/
lemma stochasticIntegralBrownian_lintegral_sq {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact isometry_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global ht'
  · subst ht'
    rw [lintegral_congr_ae (by
      filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W H h_meas h_progMeas
        h_sq_int_global (le_refl (0:ℝ))] with ω hω; rw [hω]; simp : _ =ᵐ[P] fun _ => (0:ℝ≥0∞))]
    rw [MeasureTheory.lintegral_zero]
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr (fun ω => ?_)
    rw [MeasureTheory.setLIntegral_measure_zero _ _ (by simp)]

include h_meas in
omit [IsProbabilityMeasure P] in
/-- Additivity of the horizon integral: `[0,r] = [0,s] ⊎ (s,r]`. -/
lemma horizon_lintegral_add {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) :
    ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
        + ∫⁻ ω, ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  have hinner : ∀ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
      = ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume
        + ∫⁻ u in Set.Ioc s r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume := by
    intro ω
    rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
        MeasureTheory.lintegral_union measurableSet_Ioc
          (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))]
  rw [MeasureTheory.lintegral_congr hinner]
  exact MeasureTheory.lintegral_add_left'
    ((Measurable.lintegral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) s))
      (((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2)).aemeasurable) _

include h_meas h_sq_int_global in
/-- Right-continuity of the horizon integral `r ↦ ∫⁻∫⁻_{[0,r]}‖H‖²` at `s ≥ 0`. -/
lemma horizon_lintegral_right_tendsto {s : ℝ} (hs : 0 ≤ s) :
    Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)
      (nhdsWithin s (Set.Ioi s))
      (nhds (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)) := by
  have hz : Filter.Tendsto (fun r => ∫⁻ ω, ∫⁻ u in Set.Ioc s r,
        (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    tendsto_setLIntegral_Ioc_prod_zero (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
      ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
      (h_sq_int_global (s + 1) (by linarith)).ne
  have ht := (tendsto_const_nhds (x := ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s,
    (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P)).add hz
  rw [add_zero] at ht
  refine ht.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (horizon_lintegral_add H h_meas hs (le_of_lt hr)).symm

/-- **Right-`L²`-continuity of the Itô integral process.** `‖F r − F s‖_{L²} → 0` as
`r ↓ s`. The squared increment `∫⁻‖F r − F s‖²` equals `ofReal((∫⁻∫⁻_{[0,r]}).toReal −
(∫⁻∫⁻_{[0,s]}).toReal)` (orthogonality + isometry) and `→ 0` by horizon
right-continuity. -/
lemma stochasticIntegralBrownian_eLpNorm_two_right_tendsto (s : ℝ) :
    Filter.Tendsto (fun r => MeasureTheory.eLpNorm
        (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global r
          - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global s) 2 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
  suffices hsq : Filter.Tendsto (fun r => ∫⁻ ω,
      (‖(stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global r
        - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global s) ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) by
    have h2 := hsq.ennrpow_const ((1 : ℝ) / 2)
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
    refine h2.congr (fun r => ?_)
    rw [← eLpNorm_sq_eq_lintegral_nnnorm_sq, ← ENNReal.rpow_mul,
      show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
  -- the squared increment
  rcases le_or_gt 0 s with hs | hs
  · -- s ≥ 0: orthogonality + isometry + horizon continuity
    have hFsq : ∀ {t : ℝ}, 0 ≤ t →
        ∫ ω, (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t ω) ^ 2 ∂P
          = (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) t, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal := by
      intro t ht
      have hb := lintegral_nnnorm_sq_eq_ofReal_integral
        (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global t)
      rw [stochasticIntegralBrownian_lintegral_sq W H h_meas h_progMeas h_sq_int_global ht] at hb
      rw [hb, ENNReal.toReal_ofReal (integral_nonneg (fun ω => sq_nonneg _))]
    have hincr : ∀ {r : ℝ}, s ≤ r →
        ∫⁻ ω, (‖stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global r ω
          - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global s ω‖₊ : ℝ≥0∞) ^ 2 ∂P
          = ENNReal.ofReal
            ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
              - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal) := by
      intro r hsr
      rw [lintegral_nnnorm_sq_eq_ofReal_integral
        (g := fun ω => stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global r ω
          - stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global s ω)
        ((stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global r).sub
          (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global s))]
      congr 1
      rw [integral_sq_increment_eq_of_martingale
        (martingale_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global)
        (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global s)
        (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global r) hsr,
        hFsq (le_trans hs hsr), hFsq hs]
    -- the toReal-difference → 0
    have hcont : Filter.Tendsto (fun r =>
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) r, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal
          - (∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal))
        (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
      have hfin_s : ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤ :=
        ne_top_of_le_ne_top (h_sq_int_global (s + 1) (by linarith)).ne
          (MeasureTheory.lintegral_mono (fun ω =>
            lintegral_mono_set (Set.Icc_subset_Icc_right (by linarith))))
      have h0 := (ENNReal.tendsto_toReal hfin_s).comp
        (horizon_lintegral_right_tendsto H h_meas h_sq_int_global hs)
      have h1 := h0.sub_const
        ((∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) s, (‖H ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P).toReal)
      rw [sub_self] at h1
      exact h1
    have hof := (ENNReal.continuous_ofReal.tendsto 0).comp hcont
    rw [ENNReal.ofReal_zero] at hof
    refine hof.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with r hr
    exact (hincr (le_of_lt hr)).symm
  · -- s < 0: eventually zero
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [Ioo_mem_nhdsGT hs] with r hr
    symm
    rw [← MeasureTheory.lintegral_zero (μ := P)]
    refine lintegral_congr_ae ?_
    filter_upwards [stochasticIntegralBrownian_ae_zero_of_neg W H h_meas h_progMeas
        h_sq_int_global hr.2,
      stochasticIntegralBrownian_ae_zero_of_neg W H h_meas h_progMeas h_sq_int_global hs]
      with ω hr0 hs0
    simp [hr0, hs0]

/-- **Conjunct 1 on `rightCont`: `F` is a martingale wrt `(naturalFiltration W).rightCont`.**
Right-`L²`-continuity of the slices (`stochasticIntegralBrownian_eLpNorm_two_right_tendsto`)
feeds `martingale_rightCont_of_tendsto_eLpNorm_one`. -/
lemma martingale_rightCont_stochasticIntegralBrownian :
    MeasureTheory.Martingale (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont P := by
  refine martingale_rightCont_of_tendsto_eLpNorm_one
    (martingale_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global) (fun s => ?_)
  have hF_aesm : ∀ t, MeasureTheory.AEStronglyMeasurable
      (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t) P :=
    fun t => (stochasticIntegralBrownian_memLp W H h_meas h_progMeas
      h_sq_int_global t).aestronglyMeasurable
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (stochasticIntegralBrownian_eLpNorm_two_right_tendsto W H h_meas h_progMeas h_sq_int_global s)
    (Filter.Eventually.of_forall (fun r => bot_le))
    (Filter.Eventually.of_forall (fun r => MeasureTheory.eLpNorm_le_eLpNorm_of_exponent_le
      (by norm_num) ((hF_aesm r).sub (hF_aesm s))))

include h_meas h_sq_int_global in
omit [IsProbabilityMeasure P] in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is finite in `L²(P ⊗ vol|_{[0,t]})`,
i.e. `(ω, u) ↦ H ω u` is square-integrable over the product. -/
lemma compensatorH_memLp_prod {t : ℝ} (ht : 0 < t) :
    MeasureTheory.MemLp (fun p : Ω × ℝ => H p.1 p.2) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := by
  refine ⟨h_meas.aestronglyMeasurable, ?_⟩
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by simp : (2 : ℝ≥0∞) ≠ ⊤), show (2 : ℝ≥0∞).toReal = 2 from by simp]
  have hbridge : ∫⁻ p : Ω × ℝ, (‖H p.1 p.2‖ₑ) ^ (2 : ℝ)
        ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) t)))
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
    rw [MeasureTheory.lintegral_prod _
      ((((h_meas.nnnorm).coe_nnreal_ennreal).pow_const 2).aemeasurable.congr
        (Filter.Eventually.of_forall (fun p => by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl)))]
    refine lintegral_congr (fun ω => ?_)
    refine MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]; rfl
  rw [hbridge]; exact h_sq_int_global t ht

include h_meas h_sq_int_global in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `P`-integrable (`t ≥ 0`). -/
lemma compensatorH_integrable {t : ℝ} (ht : 0 ≤ t) :
    MeasureTheory.Integrable (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · exact (compensatorH_memLp_prod H h_meas h_sq_int_global ht').integrable_sq.integral_prod_left
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [← ht', Set.Icc_self, MeasureTheory.setIntegral_measure_zero _ (by simp)]
    rw [heq]; exact MeasureTheory.integrable_const 0

include h_progMeas in
/-- The `H`-compensator `A_t = ∫₀ᵗ H² ds` is `ℱ_t`-adapted. -/
lemma compensatorH_adapted (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) := by
  rcases le_or_gt 0 t with ht | ht
  · have hsq : @MeasureTheory.StronglyMeasurable (Ω × ℝ) ℝ _
        (@Prod.instMeasurableSpace Ω ℝ
          ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t) inferInstance)
        (fun p : Ω × ℝ => (H p.1 p.2) ^ 2) := by
      simpa [pow_two] using (h_progMeas t).mul (h_progMeas t)
    letI : MeasurableSpace Ω := (LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t
    exact hsq.integral_prod_right' (ν := volume.restrict (Set.Icc (0 : ℝ) t))
  · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
      funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
    rw [heq]; exact stronglyMeasurable_const

include h_meas h_progMeas h_sq_int_global in
/-- **Compensator `L¹`-convergence.** `∫₀ᵗ (Gₙ.eval)² → ∫₀ᵗ H²` in `L¹(P)`.
The eval-squares converge to `H²` in `L¹(P ⊗ vol|_{[0,t]})`
(`tendsto_eLpNorm_one_sq_sub` from `L²`-convergence of the evals), and the
`L¹(P)`-norm of the `u`-marginal is dominated by the joint `L¹`-norm. -/
lemma masterApprox_compensator_tendsto_L1 {t : ℝ} (ht : 0 ≤ t) :
    Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
          ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P)
      Filter.atTop (nhds 0) := by
  rcases lt_or_eq_of_le ht with ht' | ht'
  · set ν : MeasureTheory.Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) t) with hν
    set Hp : Ω × ℝ → ℝ := fun p => H p.1 p.2 with hHp
    set Gp : ℕ → Ω × ℝ → ℝ := fun n p =>
      (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval p.2 p.1 with hGp
    have hHp_meas : Measurable Hp := h_meas
    have hGp_meas : ∀ n, Measurable (Gp n) := fun n =>
      (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval_jointly_measurable
    have hHmem := compensatorH_memLp_prod H h_meas h_sq_int_global ht'
    -- `Gp n → Hp` in `L²(P ⊗ ν)`.
    have hbridge : ∀ (f : Ω × ℝ → ℝ), Measurable f →
        MeasureTheory.eLpNorm f 2 (P.prod ν) ^ (2 : ℝ)
          = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      intro f hf
      rw [eLpNorm_sq_eq_lintegral_nnnorm_sq,
          MeasureTheory.lintegral_prod _
            (((hf.nnnorm.coe_nnreal_ennreal).pow_const 2).aemeasurable)]
    have hfin2 : ∀ (f : Ω × ℝ → ℝ), Measurable f →
        (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖f (ω, s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≠ ⊤) →
        MeasureTheory.eLpNorm f 2 (P.prod ν) < ⊤ :=
      fun f hf hfv => lt_top_iff_ne_top.mpr (fun h => hfv (by
        rw [← hbridge f hf, h, ENNReal.top_rpow_of_pos (by norm_num)]))
    have hL2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν))
        Filter.atTop (nhds 0) := by
      have hsq : ∀ n, MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ)
          = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
              (‖H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω‖₊ : ℝ≥0∞) ^ 2
                ∂volume ∂P := by
        intro n
        rw [hbridge (Gp n - Hp) ((hGp_meas n).sub hHp_meas)]
        refine lintegral_congr (fun ω =>
          MeasureTheory.setLIntegral_congr_fun measurableSet_Icc (fun s _ => ?_))
        simp only [Pi.sub_apply, hGp, hHp]
        rw [show (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω - H ω s
              = -(H ω s - (masterApprox W H h_meas h_progMeas h_sq_int_global n).eval s ω)
            from by ring, nnnorm_neg]
      have h2 : Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Gp n - Hp) 2 (P.prod ν) ^ (2 : ℝ))
          Filter.atTop (nhds 0) := by
        simp_rw [hsq]
        exact masterApprox_eval_tendsto W H h_meas h_progMeas h_sq_int_global ht
      have h3 := h2.ennrpow_const ((1 : ℝ) / 2)
      rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
      refine h3.congr (fun n => ?_)
      rw [← ENNReal.rpow_mul, show (2 : ℝ) * (1 / 2) = 1 from by norm_num, ENNReal.rpow_one]
    -- squares converge in `L¹(P ⊗ ν)`.
    have hjoint : Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (fun p => (Gp n p) ^ 2 - (Hp p) ^ 2) 1 (P.prod ν))
        Filter.atTop (nhds 0) :=
      tendsto_eLpNorm_one_sq_sub (fun n => (hGp_meas n).aemeasurable) hHp_meas.aemeasurable
        hHmem.2.ne hL2
    -- marginal `L¹(P)` ≤ joint `L¹(P ⊗ ν)`.
    have hmarg : ∀ n, MeasureTheory.eLpNorm
        (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
            ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
        ≤ MeasureTheory.eLpNorm (fun p => (Gp n p) ^ 2 - (Hp p) ^ 2) 1 (P.prod ν) := by
      intro n
      set dsq : Ω × ℝ → ℝ := fun p => (Gp n p) ^ 2 - (Hp p) ^ 2 with hdsq
      have hGsq_int : MeasureTheory.Integrable (fun p => (Gp n p) ^ 2) (P.prod ν) :=
        MeasureTheory.MemLp.integrable_sq
          (show MeasureTheory.MemLp (Gp n) 2 (P.prod ν) from
            ⟨(hGp_meas n).aestronglyMeasurable, hfin2 (Gp n) (hGp_meas n)
              (eval_lintegral_sq_finite
                (masterApprox W H h_meas h_progMeas h_sq_int_global n) t).ne⟩)
      have hHsq_int : MeasureTheory.Integrable (fun p => (Hp p) ^ 2) (P.prod ν) :=
        hHmem.integrable_sq
      have hdsq_int : MeasureTheory.Integrable dsq (P.prod ν) := hGsq_int.sub hHsq_int
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
        MeasureTheory.eLpNorm_one_eq_lintegral_enorm,
        MeasureTheory.lintegral_prod _ hdsq_int.aestronglyMeasurable.enorm]
      refine MeasureTheory.lintegral_mono_ae ?_
      filter_upwards [hGsq_int.prod_right_ae, hHsq_int.prod_right_ae] with ω hGω hHω
      have hcomb : (∫ u in Set.Icc (0 : ℝ) t,
            ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume
          = ∫ u, dsq (ω, u) ∂ν := by
        rw [hdsq]; exact (MeasureTheory.integral_sub hGω hHω).symm
      rw [hcomb]
      exact MeasureTheory.enorm_integral_le_lintegral_enorm _
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjoint
      (Filter.Eventually.of_forall (fun n => bot_le)) (Filter.Eventually.of_forall hmarg)
  · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards with n
    symm
    rw [← ht']
    have hz : (fun ω => (∫ u in Set.Icc (0 : ℝ) (0 : ℝ),
        ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) (0 : ℝ), (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) := by
      funext ω
      rw [Set.Icc_self, MeasureTheory.setIntegral_measure_zero _ (by simp),
        MeasureTheory.setIntegral_measure_zero _ (by simp), sub_zero]; rfl
    rw [hz, MeasureTheory.eLpNorm_zero]

include h_meas h_progMeas h_sq_int_global in
/-- **Conjunct 2 (naturalFiltration): the compensated square is a martingale.**
`t ↦ (F t)² − ∫₀ᵗ H² ds` is a `naturalFiltration W`-martingale. The simple-level
compensated squares `martingale_simpleIntegral_sq_sub_compensator` (for `masterApprox n`)
are martingales converging in `L¹` to the `F`-process: the integrand-squares converge
(`masterApprox_tendsto_L2` + `tendsto_eLpNorm_one_sq_sub`) and the compensators
converge (`masterApprox_compensator_tendsto_L1`). -/
lemma martingale_quadVar_stochasticIntegralBrownian :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W) P := by
  set F := stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global with hF
  have hAHint : ∀ t, MeasureTheory.Integrable
      (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact compensatorH_integrable H h_meas h_sq_int_global ht
    · have heq : (fun ω => ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) = fun _ => (0 : ℝ) := by
        funext ω; rw [Set.Icc_eq_empty (not_le.mpr ht)]; simp
      rw [heq]; exact MeasureTheory.integrable_const 0
  refine martingale_of_tendsto_eLpNorm_one
    (M := fun n t ω =>
      (simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t,
            ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
    (fun n => martingale_simpleIntegral_sq_sub_compensator W (master_horizon_pos n)
      (masterApprox W H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n))
    (fun n t => (martingale_simpleIntegral_sq_sub_compensator W (master_horizon_pos n)
      (masterApprox W H h_meas h_progMeas h_sq_int_global n)
      (masterApprox_adapt W H h_meas h_progMeas h_sq_int_global n)).integrable t)
    (fun t => ?_) (fun t => ?_) (fun t => ?_)
  · -- StronglyAdapted
    have hFsq : @MeasureTheory.StronglyMeasurable Ω ℝ _
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).seq t) (fun ω => (F t ω) ^ 2) := by
      simpa [pow_two] using
        (stochasticIntegralBrownian_stronglyAdapted W H h_meas h_progMeas h_sq_int_global t).mul
          (stochasticIntegralBrownian_stronglyAdapted W H h_meas h_progMeas h_sq_int_global t)
    exact hFsq.sub (compensatorH_adapted W H h_progMeas t)
  · -- integrability of the F-process at each `t`
    exact ((stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global t).integrable_sq).sub
      (hAHint t)
  · -- `L¹`-convergence of the simple compensated squares to the F-process
    rcases le_or_gt 0 t with ht | ht
    · have hX : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
          (fun ω => (simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) 1 P) Filter.atTop (nhds 0) :=
        tendsto_eLpNorm_one_sq_sub
          (fun n => (Finset.measurable_sum _ (fun i _ =>
            ((masterApprox W H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
              ((W.measurable_eval _).sub (W.measurable_eval _)))).aemeasurable)
          (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global t).1.aemeasurable
          (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global t).2.ne
          (masterApprox_tendsto_L2 W H h_meas h_progMeas h_sq_int_global ht)
      have hY := masterApprox_compensator_tendsto_L1 W H h_meas h_progMeas h_sq_int_global ht
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
        (by simpa using hX.add hY)
        (Filter.Eventually.of_forall (fun n => bot_le))
        (Filter.Eventually.of_forall (fun n => ?_))
      have hXaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
            - (F t ω) ^ 2) P :=
        (((Finset.measurable_sum _ (fun i _ =>
          ((masterApprox W H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).mul
            ((W.measurable_eval _).sub (W.measurable_eval _)))).pow_const 2).aestronglyMeasurable).sub
          ((stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global t).1.aemeasurable.pow_const 2).aestronglyMeasurable
      have hAn_meas : Measurable (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
          ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume) := by
        rw [show (fun ω => ∫ u in Set.Icc (0 : ℝ) t,
              ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            = fun ω => ∑ i : Fin (masterApprox W H h_meas h_progMeas h_sq_int_global n).N,
                (min ((masterApprox W H h_meas h_progMeas h_sq_int_global n).partition i.succ) t
                  - min ((masterApprox W H h_meas h_progMeas h_sq_int_global n).partition
                      i.castSucc) t)
                  * ((masterApprox W H h_meas h_progMeas h_sq_int_global n).ξ i ω) ^ 2 from
          funext (fun ω => setIntegral_eval_sq_Icc_clamped
            (masterApprox W H h_meas h_progMeas h_sq_int_global n) ω ht)]
        exact Finset.measurable_sum _ (fun i _ => measurable_const.mul
          (((masterApprox W H h_meas h_progMeas h_sq_int_global n).ξ_measurable i).pow_const 2))
      have hYaesm : MeasureTheory.AEStronglyMeasurable
          (fun ω => (∫ u in Set.Icc (0 : ℝ) t,
              ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) P :=
        hAn_meas.aestronglyMeasurable.sub (hAHint t).aestronglyMeasurable
      calc MeasureTheory.eLpNorm
            ((fun t' ω => (simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t' ω) ^ 2
                - ∫ u in Set.Icc (0 : ℝ) t', ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
              - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P
          = MeasureTheory.eLpNorm
              ((fun ω => (simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t ω) ^ 2
                  - (F t ω) ^ 2)
                - fun ω => (∫ u in Set.Icc (0 : ℝ) t,
                    ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume)
                  - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P := by
            refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
            simp only [Pi.sub_apply]; ring
        _ ≤ _ := MeasureTheory.eLpNorm_sub_le hXaesm hYaesm le_rfl
    · have hzero : ∀ n, MeasureTheory.eLpNorm
          ((fun t' ω => (simpleIntegral W (masterApprox W H h_meas h_progMeas h_sq_int_global n) t' ω) ^ 2
              - ∫ u in Set.Icc (0 : ℝ) t', ((masterApprox W H h_meas h_progMeas h_sq_int_global n).eval u ω) ^ 2 ∂volume) t
            - fun ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) 1 P = 0 := by
        intro n
        refine (MeasureTheory.eLpNorm_eq_zero_of_ae_zero ?_)
        filter_upwards [stochasticIntegralBrownian_ae_zero_of_neg W H h_meas h_progMeas
          h_sq_int_global ht] with ω hF0
        simp only [Pi.sub_apply, Pi.zero_apply,
          simpleIntegral_eq_zero_of_nonpos W _ (le_of_lt ht) ω, hF, hF0,
          Set.Icc_eq_empty (not_le.mpr ht)]
        simp
      simp only [hzero]; exact tendsto_const_nhds

include h_meas h_progMeas h_sq_int_global in
/-- **Conjunct 2 on `rightCont`: `(F)² − ∫₀ᵗH²` is a `rightCont`-martingale.**
The naturalFiltration martingale (`martingale_quadVar_stochasticIntegralBrownian`) lifts
via right-`L¹`-continuity: the `F²`-part is controlled by `F`'s right-`L²`-continuity
(`tendsto_eLpNorm_one_sq_sub`), the compensator part by the horizon slab
`∫⁻∫⁻_{(s,r]}‖H‖² → 0` (`tendsto_setLIntegral_Ioc_prod_zero`). -/
lemma martingale_rightCont_quadVar_stochasticIntegralBrownian :
    MeasureTheory.Martingale
      (fun t ω => (stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume)
      (LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont P := by
  refine martingale_rightCont_of_tendsto_eLpNorm_one
    (martingale_quadVar_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global)
    (fun s => ?_)
  set F := stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global with hFdef
  -- `F²`-part: right-`L¹`-continuity of the square.
  have hF2 : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) 1 P) (nhdsWithin s (Set.Ioi s)) (nhds 0) :=
    tendsto_eLpNorm_one_sq_sub (l := nhdsWithin s (Set.Ioi s)) (a := fun r => F r) (b := F s)
      (fun r => (stochasticIntegralBrownian_memLp W H h_meas h_progMeas
        h_sq_int_global r).1.aemeasurable)
      (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global s).1.aemeasurable
      (stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global s).2.ne
      (stochasticIntegralBrownian_eLpNorm_two_right_tendsto W H h_meas h_progMeas h_sq_int_global s)
  -- compensator part: right-`L¹`-continuity of `A_t = ∫₀ᵗ H²`.
  have hA : Filter.Tendsto (fun r => MeasureTheory.eLpNorm
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P)
      (nhdsWithin s (Set.Ioi s)) (nhds 0) := by
    rcases le_or_gt 0 s with hs | hs
    · have hslab := tendsto_setLIntegral_Ioc_prod_zero (fun ω u => (‖H ω u‖₊ : ℝ≥0∞) ^ 2)
        ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) hs (lt_add_one s)
        (h_sq_int_global (s + 1) (by linarith)).ne
      refine hslab.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with r hr
      have hsr : s ≤ r := le_of_lt hr
      have hrpos : 0 < r := lt_of_le_of_lt hs hr
      have hHr : ∀ᵐ ω ∂P, MeasureTheory.Integrable
          (fun u => (H ω u) ^ 2) (volume.restrict (Set.Icc (0 : ℝ) r)) :=
        (compensatorH_memLp_prod H h_meas h_sq_int_global hrpos).integrable_sq.prod_right_ae
      rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm]
      refine (lintegral_congr_ae ?_).symm
      filter_upwards [hHr] with ω hHrω
      have hHsω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Icc (0 : ℝ) s)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono (Set.Icc_subset_Icc_right hsr)
          (le_refl _))
      have hHscω : MeasureTheory.Integrable (fun u => (H ω u) ^ 2)
          (volume.restrict (Set.Ioc s r)) :=
        hHrω.mono_measure (MeasureTheory.Measure.restrict_mono
          (Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc_left hs)) (le_refl _))
      have hsplit : (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
          - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume
          = ∫ u in Set.Ioc s r, (H ω u) ^ 2 ∂volume := by
        rw [← Set.Icc_union_Ioc_eq_Icc hs hsr,
          MeasureTheory.setIntegral_union
            (Set.disjoint_left.mpr (fun x hx1 hx2 => absurd hx2.1 (not_lt.mpr hx1.2)))
            measurableSet_Ioc hHsω hHscω]
        ring
      rw [hsplit, ← ofReal_norm_eq_enorm, Real.norm_eq_abs,
        abs_of_nonneg (MeasureTheory.integral_nonneg (fun u => sq_nonneg _)),
        MeasureTheory.ofReal_integral_eq_lintegral_ofReal hHscω
          (Filter.Eventually.of_forall (fun u => sq_nonneg _))]
      refine MeasureTheory.setLIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
      rw [show (‖H ω u‖₊ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((H ω u) ^ 2) from by
        rw [show (‖H ω u‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖H ω u‖ from (ofReal_norm_eq_enorm _).symm,
          ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]]
    · refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
      filter_upwards [Ioo_mem_nhdsGT hs] with r hr
      have hAr : (fun u => (H · u) ^ 2) = (fun u => (H · u) ^ 2) := rfl
      symm
      rw [show (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
            - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) = (0 : Ω → ℝ) from by
        funext ω
        rw [Set.Icc_eq_empty (not_le.mpr hr.2), Set.Icc_eq_empty (not_le.mpr hs)]
        simp]
      exact MeasureTheory.eLpNorm_zero
  -- combine the two parts.
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa using hF2.add hA)
    (Filter.Eventually.of_forall (fun r => bot_le)) (Filter.Eventually.of_forall (fun r => ?_))
  have hF2aesm : MeasureTheory.AEStronglyMeasurable (fun ω => (F r ω) ^ 2 - (F s ω) ^ 2) P :=
    (((stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global r).1.aemeasurable.pow_const
        2).aestronglyMeasurable).sub
      (((stochasticIntegralBrownian_memLp W H h_meas h_progMeas h_sq_int_global s).1.aemeasurable.pow_const
        2).aestronglyMeasurable)
  have hAaesm : MeasureTheory.AEStronglyMeasurable
      (fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
        - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) P :=
    ((compensatorH_adapted W H h_progMeas r).mono
      ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le r)).aestronglyMeasurable.sub
      (((compensatorH_adapted W H h_progMeas s).mono
        ((LevyStochCalc.Brownian.Martingale.naturalFiltration W).le s)).aestronglyMeasurable)
  calc MeasureTheory.eLpNorm
        ((fun t ω => (F t ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) t, (H ω u) ^ 2 ∂volume) r
          - fun ω => (F s ω) ^ 2 - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P
      = MeasureTheory.eLpNorm
          ((fun ω => (F r ω) ^ 2 - (F s ω) ^ 2)
            - fun ω => (∫ u in Set.Icc (0 : ℝ) r, (H ω u) ^ 2 ∂volume)
              - ∫ u in Set.Icc (0 : ℝ) s, (H ω u) ^ 2 ∂volume) 1 P := by
        refine MeasureTheory.eLpNorm_congr_ae (Filter.Eventually.of_forall (fun ω => ?_))
        simp only [Pi.sub_apply]; ring
    _ ≤ _ := MeasureTheory.eLpNorm_sub_le hF2aesm hAaesm le_rfl

end MasterSequence

/-- **Unified L²-Itô integral with martingale + quadVar + isometry** (formerly cited
axiom #5, now a theorem).

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

**Construction**: `F := stochasticIntegralBrownian` is the coherent `L²`-limit of the
`masterApprox` simple integrals across growing horizons. Conjunct 1
(`martingale_rightCont_stochasticIntegralBrownian`) and conjunct 3
(`isometry_stochasticIntegralBrownian`) were proven directly; conjunct 2
(`martingale_rightCont_quadVar_stochasticIntegralBrownian`) is the set-level Itô
isometry at simple level lifted through the `L¹`-limit of the compensated squares and
the `rightCont` right-`L¹`-continuity. `Filt` is pinned to
`(naturalFiltration W).rightCont`. -/
theorem itoIsometry_brownian_unified_existence
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
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = (LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont ∧
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2 - ∫ s in Set.Icc (0 : ℝ) t, (H ω s) ^ 2) Filt P ∧
      (∀ T, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) :=
  ⟨stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global,
    (LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont, rfl,
    martingale_rightCont_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global,
    martingale_rightCont_quadVar_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global,
    fun T hT => isometry_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global hT⟩

/-- The *L² Itô integral* `M_t = ∫_0^t H_s dW_s` against a Brownian motion `W`.

The **constructed** L²-limit process `stochasticIntegralBrownian` (the coherent
`L²`-limit of the `masterApprox` simple integrals), not a `Classical.choose`
witness — so it is genuinely linear-friendly (used by `itoIsometry_diff_brownian`). -/
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
  stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global T

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
  unfold stochasticIntegral
  exact isometry_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global hT

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
  unfold stochasticIntegral
  exact ⟨(LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont,
    martingale_rightCont_quadVar_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global⟩

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
  unfold stochasticIntegral
  exact ⟨(LevyStochCalc.Brownian.Martingale.naturalFiltration W).rightCont,
    martingale_rightCont_stochasticIntegralBrownian W H h_meas h_progMeas h_sq_int_global⟩

end LevyStochCalc.Brownian.Ito
