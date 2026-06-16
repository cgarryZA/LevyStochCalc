/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Construction
import Mathlib.Probability.Process.Kolmogorov
import Mathlib.Probability.Distributions.Gaussian.Fernique

/-!
# Kolmogorov-Chentsov continuous modification

Mathlib has only `IsKolmogorovProcess` (the *condition*); the modification
result is missing. We port the classical proof (Karatzas-Shreve §2.2 Thm 2.8 /
Le Gall 2016 Thm 2.9):

  *If `(X_t)_{t ≥ 0}` satisfies `𝔼[ |X_t − X_s|^p ] ≤ M · |t − s|^q` for some
  `p, q > 0` with `q > 1` and constant `M`, then there exists a modification
  `X̃` with continuous paths.*

Proof outline as named sub-lemmas below.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Continuity

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Step 2: uniform Hölder on a dense set → continuous extension.**

A function `f : ℝ → ℝ` that is α-Hölder on a dense set `D ⊆ ℝ` extends
uniquely to a continuous function on `ℝ`. (Specialised to `D = dyadicRationals`
in the KC application.)

Proof: an α-Hölder function on `D` is uniformly continuous on `D`. By
`Dense.uniformContinuous_extend`, the unique continuous extension to all
of `ℝ` exists. -/
lemma holder_dense_extends_continuous {α K : ℝ}
    (hα : 0 < α) (_hK : 0 < K)
    (D : Set ℝ) (h_dense : Dense D)
    (f : ℝ → ℝ)
    (h_holder_dyadic : ∀ s ∈ D, ∀ t ∈ D, |f s - f t| ≤ K * |s - t| ^ α) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ s ∈ D, g s = f s := by
  -- f restricted to D is uniformly continuous (α-Hölder ⇒ UC).
  set fD : D → ℝ := fun x => f x.1 with hfD_def
  have h_uc : UniformContinuous fD := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    -- Take δ such that K · δ^α ≤ ε/2 < ε.
    -- Choose δ = (ε / (2 * (K + 1)))^(1/α).
    set C : ℝ := 2 * (K + 1) with hC_def
    have hC_pos : 0 < C := by simp [hC_def]; linarith
    refine ⟨(ε / C) ^ (1/α), ?_, ?_⟩
    · exact Real.rpow_pos_of_pos (div_pos hε hC_pos) _
    · intro s t h_dist
      have h_holder := h_holder_dyadic s.1 s.2 t.1 t.2
      -- |s.1 - t.1| < δ
      have h_dist_pos : 0 ≤ |s.1 - t.1| := abs_nonneg _
      have h_dist_real : |s.1 - t.1| < (ε / C) ^ (1/α) := by
        rw [show |s.1 - t.1| = dist s.1 t.1 from (Real.dist_eq _ _).symm]
        exact h_dist
      -- |s.1 - t.1|^α < ε/C
      have h_pow_lt : |s.1 - t.1| ^ α < ε / C := by
        have h1 : |s.1 - t.1| ^ α < ((ε / C) ^ (1/α)) ^ α :=
          Real.rpow_lt_rpow h_dist_pos h_dist_real hα
        rw [show ((ε / C) ^ (1/α)) ^ α = ε / C from ?_] at h1
        · exact h1
        · rw [← Real.rpow_mul (le_of_lt (div_pos hε hC_pos))]
          rw [one_div, inv_mul_cancel₀ (ne_of_gt hα), Real.rpow_one]
      -- K · |s.1 - t.1|^α < K · ε / C ≤ ε/2 (when K ≤ K+1, K/(K+1) ≤ 1)
      -- Actually let me just bound by (K+1) · ε/C = ε/2 < ε.
      have hK1_pos : 0 < K + 1 := by linarith
      have h_K_le_K1 : K ≤ K + 1 := by linarith
      have h_holder_K1 : |f s.1 - f t.1| ≤ (K + 1) * |s.1 - t.1| ^ α := by
        refine le_trans h_holder (mul_le_mul_of_nonneg_right h_K_le_K1 ?_)
        exact Real.rpow_nonneg h_dist_pos _
      have h_bd : (K + 1) * |s.1 - t.1| ^ α < (K + 1) * (ε / C) :=
        mul_lt_mul_of_pos_left h_pow_lt hK1_pos
      have h_C_eq : (K + 1) * (ε / C) = ε / 2 := by
        simp only [hC_def]
        have h_K1_ne : (K + 1 : ℝ) ≠ 0 := ne_of_gt hK1_pos
        field_simp
      rw [h_C_eq] at h_bd
      have h_final : |f s.1 - f t.1| < ε / 2 := lt_of_le_of_lt h_holder_K1 h_bd
      have h_dist_eq : dist (fD s) (fD t) = |f s.1 - f t.1| := by
        rw [Real.dist_eq, hfD_def]
      rw [h_dist_eq]
      linarith
  -- Apply Dense.uniformContinuous_extend
  refine ⟨h_dense.extend fD, ?_, ?_⟩
  · -- Continuous (extend fD)
    exact (Dense.uniformContinuous_extend h_dense h_uc).continuous
  · -- ∀ s ∈ D, extend fD s = f s
    intro s hs
    exact Dense.extend_of_ind h_dense h_uc ⟨s, hs⟩

/-- The set of dyadic rationals: `D := {k * 2^{-n} : k ∈ ℤ, n ∈ ℕ}`. Dense in ℝ. -/
def dyadicRationals : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, ∃ n : ℕ, x = (k : ℝ) * (2 : ℝ)^(-n : ℤ)}

/-- `0` is a dyadic rational (`k = 0`, `n = 0`). -/
lemma zero_mem_dyadicRationals : (0 : ℝ) ∈ dyadicRationals := by
  refine ⟨0, 0, ?_⟩
  simp

/-- Every integer is a dyadic rational (`n = 0`). -/
lemma intCast_mem_dyadicRationals (k : ℤ) : (k : ℝ) ∈ dyadicRationals := by
  refine ⟨k, 0, ?_⟩
  simp

/-- **Dyadic rationals are dense in ℝ.** Given any `x : ℝ` and any `r > 0`,
choose `n` with `(1/2)^n < r`, then `k := ⌊x · 2^n⌋`; the dyadic
`k · 2^(-n)` is within `r` of `x`. -/
lemma dense_dyadicRationals : Dense dyadicRationals := by
  rw [Metric.dense_iff]
  intro x r hr
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr (by norm_num : (1 / 2 : ℝ) < 1)
  set k : ℤ := ⌊x * (2 : ℝ)^n⌋ with hk_def
  set y : ℝ := (k : ℝ) * (2 : ℝ)^(-n : ℤ) with hy_def
  refine ⟨y, ?_, ?_⟩
  · rw [Metric.mem_ball]
    have h2n_pos : (0 : ℝ) < (2 : ℝ)^n := by positivity
    have h_pow_neg_eq : ((2 : ℝ) ^ (-n : ℤ)) = ((2 : ℝ)^n)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have h_floor_bound : x * (2 : ℝ)^n - 1 < (k : ℝ) ∧ (k : ℝ) ≤ x * (2 : ℝ)^n :=
      ⟨Int.sub_one_lt_floor _, Int.floor_le _⟩
    have h_diff : y - x = ((k : ℝ) - x * (2 : ℝ)^n) * ((2 : ℝ)^n)⁻¹ := by
      rw [hy_def, h_pow_neg_eq]; field_simp
    rw [Real.dist_eq, h_diff, abs_mul, abs_inv, abs_of_pos h2n_pos]
    have h_bound1 : |((k : ℝ) - x * (2 : ℝ)^n)| ≤ 1 := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · linarith [h_floor_bound.1]
      · linarith [h_floor_bound.2]
    have h_step : |((k : ℝ) - x * (2 : ℝ)^n)| * ((2 : ℝ)^n)⁻¹
        ≤ 1 * ((2 : ℝ)^n)⁻¹ := by
      apply mul_le_mul_of_nonneg_right h_bound1
      positivity
    rw [one_mul] at h_step
    refine lt_of_le_of_lt h_step ?_
    have h_inv_eq : ((2 : ℝ)^n)⁻¹ = (1 / 2 : ℝ)^n := by rw [one_div, inv_pow]
    rw [h_inv_eq]
    exact hn
  · exact ⟨k, n, rfl⟩

/-- For every `t : ℝ`, there is a sequence of dyadic rationals strictly
increasing to `t`. Wrapper around `Dense.exists_seq_strictMono_tendsto` +
`dense_dyadicRationals`. -/
lemma exists_seq_dyadic_tendsto (t : ℝ) :
    ∃ u : ℕ → ℝ, StrictMono u
      ∧ (∀ n, u n ∈ Set.Iio t ∩ dyadicRationals)
      ∧ Filter.Tendsto u Filter.atTop (nhds t) :=
  dense_dyadicRationals.exists_seq_strictMono_tendsto t

/-! ### Deterministic dyadic chaining

A real function whose consecutive level-`n` dyadic increments on `[0,1]` are
bounded by `b n` (with `∑ b n` controlled) is Hölder on the dyadics of `[0,1)`.
This is the path-by-path core of the continuous-modification construction: the
a.s. Borel–Cantelli increment bounds feed `b n = C · 2^(-α n)`. -/

/-- Level-`n` dyadic truncation `⌊x·2ⁿ⌋ / 2ⁿ` — the largest level-`n` dyadic
`≤ x`. -/
noncomputable def dyadicTrunc (n : ℕ) (x : ℝ) : ℝ := (⌊x * 2 ^ n⌋ : ℝ) / 2 ^ n

lemma dyadicTrunc_mem_dyadicRationals (n : ℕ) (x : ℝ) :
    dyadicTrunc n x ∈ dyadicRationals := by
  refine ⟨⌊x * 2 ^ n⌋, n, ?_⟩
  rw [dyadicTrunc, zpow_neg, zpow_natCast, div_eq_mul_inv]

lemma dyadicTrunc_le (n : ℕ) (x : ℝ) : dyadicTrunc n x ≤ x := by
  rw [dyadicTrunc, div_le_iff₀ (by positivity)]
  exact Int.floor_le _

/-- `2⌊y⌋ ≤ ⌊2y⌋ ≤ 2⌊y⌋ + 1`. -/
lemma floor_two_mul_bounds (y : ℝ) :
    2 * ⌊y⌋ ≤ ⌊2 * y⌋ ∧ ⌊2 * y⌋ ≤ 2 * ⌊y⌋ + 1 := by
  refine ⟨?_, ?_⟩
  · apply Int.le_floor.mpr
    push_cast
    linarith [Int.floor_le y]
  · have h2 : ⌊2 * y⌋ < 2 * ⌊y⌋ + 2 := by
      apply Int.floor_lt.mpr
      push_cast
      linarith [Int.lt_floor_add_one y]
    omega

/-- **Single refinement step.** For `x ∈ [0,1]`, the level-`(n+1)` truncation
differs from the level-`n` truncation by at most one consecutive level-`(n+1)`
dyadic increment, hence `|f(trunc_{n+1} x) − f(trunc_n x)| ≤ b (n+1)`. -/
lemma dyadicTrunc_succ_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {n : ℕ} (hn : N ≤ n + 1) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    |f (dyadicTrunc (n + 1) x) - f (dyadicTrunc n x)| ≤ b (n + 1) := by
  set k : ℤ := ⌊x * 2 ^ n⌋ with hk
  set j : ℤ := ⌊x * 2 ^ (n + 1)⌋ with hj
  have hjk : j = ⌊2 * (x * 2 ^ n)⌋ := by rw [hj]; congr 1; rw [pow_succ]; ring
  obtain ⟨hlo, hhi⟩ := floor_two_mul_bounds (x * 2 ^ n)
  rw [← hjk] at hlo hhi
  have hk0 : 0 ≤ k := by
    rw [hk]; apply Int.floor_nonneg.mpr; positivity
  -- Truncations expressed over the common denominator `2^(n+1)`.
  have hDn : dyadicTrunc n x = ((2 * k : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [dyadicTrunc, ← hk, pow_succ]; push_cast; ring
  have hDn1 : dyadicTrunc (n + 1) x = ((j : ℤ) : ℝ) / 2 ^ (n + 1) := by
    rw [dyadicTrunc, ← hj]
  rcases (by omega : j = 2 * k ∨ j = 2 * k + 1) with hjeq | hjeq
  · -- No refinement: the two truncations coincide.
    rw [hDn1, hDn, hjeq, sub_self, abs_zero]
    exact hb (n + 1)
  · -- One refinement step `(2k) → (2k+1)` at level `n+1`.
    have hbound : 2 * k + 1 ≤ (2 : ℤ) ^ (n + 1) := by
      have hjle : (j : ℝ) ≤ x * 2 ^ (n + 1) := Int.floor_le _
      have hj_le : (j : ℝ) ≤ (2 : ℝ) ^ (n + 1) :=
        le_trans hjle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) (n + 1)])
      have : (j : ℤ) ≤ (2 : ℤ) ^ (n + 1) := by exact_mod_cast hj_le
      omega
    have hap := hf (n + 1) hn (2 * k) (by omega) hbound
    rw [hDn1, hDn, hjeq]
    exact_mod_cast hap

/-- **Telescoping bound across levels.** For `x ∈ [0,1]` and `m ≤ L`, the
truncation increment from level `m` to level `L` is bounded by the sum of the
per-level bounds `b (m+1) + ⋯ + b L`. -/
lemma dyadicTrunc_telescope {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {m : ℕ} (hm : N ≤ m + 1) :
    ∀ L, m ≤ L → |f (dyadicTrunc L x) - f (dyadicTrunc m x)|
      ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base =>
    rw [sub_self, abs_zero, Finset.Ico_self, Finset.sum_empty]
  | succ L hmL ih =>
    calc |f (dyadicTrunc (L + 1) x) - f (dyadicTrunc m x)|
        ≤ |f (dyadicTrunc (L + 1) x) - f (dyadicTrunc L x)|
          + |f (dyadicTrunc L x) - f (dyadicTrunc m x)| := abs_sub_le _ _ _
      _ ≤ b (L + 1) + ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
          refine add_le_add ?_ ih
          exact dyadicTrunc_succ_step hb hf (by omega) hx0 hx1
      _ = ∑ n ∈ Finset.Ico (m + 1) (L + 2), b n := by
          rw [Finset.sum_Ico_succ_top (by omega : m + 1 ≤ L + 1)]
          ring

/-- **Cross-point step at a fixed level.** For `0 ≤ s ≤ t ≤ 1` with
`t − s ≤ 2^{-m}`, the level-`m` truncations of `s` and `t` are equal or adjacent
level-`m` dyadics, so `|f(trunc_m s) − f(trunc_m t)| ≤ b m`. -/
lemma dyadicTrunc_near_step {f : ℝ → ℝ} {b : ℕ → ℝ} {N : ℕ}
    (hb : ∀ n, 0 ≤ b n)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ b n)
    {m : ℕ} (hm : N ≤ m) {s t : ℝ} (hs0 : 0 ≤ s) (ht1 : t ≤ 1) (hst : s ≤ t)
    (hclose : t - s ≤ (1 / 2) ^ m) :
    |f (dyadicTrunc m s) - f (dyadicTrunc m t)| ≤ b m := by
  set ks : ℤ := ⌊s * 2 ^ m⌋ with hks
  set kt : ℤ := ⌊t * 2 ^ m⌋ with hkt
  have hks0 : 0 ≤ ks := by rw [hks]; apply Int.floor_nonneg.mpr; positivity
  have hmono : ks ≤ kt := by
    rw [hks, hkt]; apply Int.floor_le_floor
    exact mul_le_mul_of_nonneg_right hst (by positivity)
  have hclose' : t * 2 ^ m ≤ s * 2 ^ m + 1 := by
    have hmul : (t - s) * 2 ^ m ≤ 1 := by
      calc (t - s) * 2 ^ m ≤ (1 / 2) ^ m * 2 ^ m :=
            mul_le_mul_of_nonneg_right hclose (by positivity)
        _ = 1 := by rw [div_pow, one_pow, div_mul_cancel₀]; positivity
    nlinarith
  have hkt_le : kt ≤ ks + 1 := by
    rw [hkt, hks]
    calc ⌊t * 2 ^ m⌋ ≤ ⌊s * 2 ^ m + 1⌋ := Int.floor_le_floor (by linarith)
      _ = ⌊s * 2 ^ m⌋ + 1 := Int.floor_add_one _
  have hTs : dyadicTrunc m s = ((ks : ℤ) : ℝ) / 2 ^ m := by rw [dyadicTrunc, ← hks]
  have hTt : dyadicTrunc m t = ((kt : ℤ) : ℝ) / 2 ^ m := by rw [dyadicTrunc, ← hkt]
  rcases (by omega : kt = ks ∨ kt = ks + 1) with he | he
  · rw [hTs, hTt, he, sub_self, abs_zero]; exact hb m
  · have hbnd : ks + 1 ≤ (2 : ℤ) ^ m := by
      have hktle : (kt : ℝ) ≤ t * 2 ^ m := Int.floor_le _
      have hkt_le2 : (kt : ℝ) ≤ (2 : ℝ) ^ m :=
        le_trans hktle (by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) m])
      have : (kt : ℤ) ≤ (2 : ℤ) ^ m := by exact_mod_cast hkt_le2
      omega
    have hap := hf m hm ks hks0 hbnd
    rw [hTs, hTt, he, abs_sub_comm]
    exact_mod_cast hap

/-- A dyadic rational coincides with its own level-`L` truncation for all
sufficiently large `L`. -/
lemma dyadicTrunc_eventually_eq {s : ℝ} (hs : s ∈ dyadicRationals) :
    ∃ L₀ : ℕ, ∀ L, L₀ ≤ L → dyadicTrunc L s = s := by
  obtain ⟨k, n, hkn⟩ := hs
  refine ⟨n, fun L hL => ?_⟩
  have h2n : (2 : ℝ) ^ n ≠ 0 := by positivity
  have hpow : (2 : ℝ) ^ L = (2 : ℝ) ^ (L - n) * (2 : ℝ) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hL]
  have hsL : s * 2 ^ L = ((k * 2 ^ (L - n) : ℤ) : ℝ) := by
    rw [hkn, zpow_neg, zpow_natCast, hpow]
    push_cast
    field_simp
  rw [dyadicTrunc, hsL, Int.floor_intCast, hkn, zpow_neg, zpow_natCast, hpow]
  push_cast
  field_simp

/-- **Markov / Chebyshev bound from the Kolmogorov condition.**

For a process satisfying the Kolmogorov moment condition
`∫⁻ ω, edist (X s ω) (X t ω)^p ∂P ≤ M · edist s t ^ q` and any threshold
`0 < lam < ⊤`,

  `P {ω | lam ≤ edist (X s ω) (X t ω)} ≤ M · edist s t ^ q / lam ^ p`.

This is the per-pair tail bound underlying both the convergence-in-measure
argument (`kolmogorov_modification_ae_eq`) and the per-dyadic-level Borel–
Cantelli step of the continuous-modification construction. -/
lemma kolmogorov_markov_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ≥0∞} (hlam_pos : 0 < lam) (hlam_top : lam ≠ ⊤) :
    P {ω | lam ≤ edist (X s ω) (X t ω)}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / lam ^ p := by
  have hp_pos : 0 < p := hX.p_pos
  -- {lam ≤ edist} = {lam^p ≤ edist^p} since `· ^ p` is strictly monotone.
  have h_set_eq :
      {ω | lam ≤ edist (X s ω) (X t ω)}
        = {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p} := by
    ext ω; exact (ENNReal.rpow_le_rpow_iff hp_pos).symm
  have h_edist_aemeas : AEMeasurable
      (fun ω => edist (X s ω) (X t ω) ^ p) P :=
    ((hX.measurable_edist (s := s) (t := t)).pow_const p).aemeasurable
  have h_Kol : ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P
      ≤ (M : ℝ≥0∞) * edist s t ^ q := hX.kolmogorovCondition s t
  have h_Markov :
      lam ^ p * P {ω | lam ^ p ≤ edist (X s ω) (X t ω) ^ p}
        ≤ ∫⁻ ω, edist (X s ω) (X t ω) ^ p ∂P :=
    MeasureTheory.mul_meas_ge_le_lintegral₀ h_edist_aemeas (lam ^ p)
  have h_chain :
      lam ^ p * P {ω | lam ≤ edist (X s ω) (X t ω)}
        ≤ (M : ℝ≥0∞) * edist s t ^ q := by
    rw [h_set_eq]; exact le_trans h_Markov h_Kol
  have hlamp_pos : 0 < lam ^ p := by
    apply ENNReal.rpow_pos_of_nonneg hlam_pos
    exact hp_pos.le
  have hlamp_ne_top : lam ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp_pos.le hlam_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl hlamp_pos.ne') (Or.inl hlamp_ne_top),
      mul_comm]
  exact h_chain

/-- **Step 3: extended process equals X a.s. at each t.**

By the Kolmogorov condition (Markov inequality), `X_{t_n} → X_t` in probability
as `t_n → t`. Combined with the a.s.-pointwise dyadic limit (Y is continuous
and equals X on dyadics), the extended process equals X almost surely at
each `t`.

Sub-steps:
1. **Continuity in probability of X**: `X t_n → X t` in probability via Markov
   + Kolmogorov condition.
2. **Y_{t_n} → Y_t** almost surely as t_n → t along any sequence (since Y is
   continuous a.s.).
3. **X_{t_n} = Y_{t_n}** for dyadic t_n (hypothesis).
4. Combine: at each fixed t, X_t = Y_t a.s. (limit of equal-a.s. sequences,
   one converging in probability the other a.s., are equal a.s.). -/
lemma kolmogorov_modification_ae_eq
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (Y : ℝ → Ω → ℝ)
    (h_continuous : ∀ᵐ ω ∂P, Continuous (fun t => Y t ω))
    (h_dyadic_eq : ∀ s ∈ dyadicRationals, ∀ᵐ ω ∂P, Y s ω = X s ω) :
    ∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω := by
  intro t
  -- Step 1: pick dyadic sequence u_n strictly increasing to t.
  obtain ⟨u, _hu_mono, hu_dyadic, hu_tendsto⟩ := exists_seq_dyadic_tendsto t
  -- Step 2: each X(s) is measurable (from Mathlib's IsKolmogorovProcess.measurable
  -- which needs MeasurableSpace + BorelSpace + SecondCountableTopology on E = ℝ,
  -- all of which ℝ has).
  have h_X_meas : ∀ s : ℝ, Measurable (X s) := fun s => hX.measurable s
  -- Step 3: Chebyshev / Markov on the Kolmogorov moment bound gives
  -- convergence-in-measure of X(u n) → X(t).
  have hp_pos : 0 < p := hX.p_pos
  have hq_pos : 0 < q := hX.q_pos
  -- Direct Markov: P {ω | δ^p ≤ edist^p} ≤ (∫⁻ edist^p) / δ^p
  --   ≤ M·edist(u n,t)^q/δ^p.
  -- For real-valued X, edist (X s ω) (X t ω) = ‖X s ω - X t ω‖ₑ (PseudoEMetric on ℝ
  -- via |·|), so this is convergence of (X (u n)) → X t in measure.
  have h_TIM : MeasureTheory.TendstoInMeasure P (fun n => X (u n)) Filter.atTop (X t) := by
    intro δ hδ
    -- Handle δ = ⊤ separately: edist : ENNReal-valued from real-valued X is
    -- always < ⊤, so {ω | ⊤ ≤ edist} is empty, P = 0, tendsto trivially.
    by_cases hδ_top : δ = ⊤
    · subst hδ_top
      simp_rw [top_le_iff]
      have h_edist_ne_top : ∀ n ω,
          edist (X (u n) ω) (X t ω) ≠ ⊤ := fun n ω => edist_ne_top _ _
      have h_set_empty : ∀ n,
          {ω | edist (X (u n) ω) (X t ω) = ⊤} = ∅ := by
        intro n; ext ω
        simp [h_edist_ne_top n ω]
      simp_rw [h_set_empty]
      simp
    -- Now δ ≠ ⊤. Step D: edist (u n) t → 0 from u n → t.
    have h_edist_tendsto : Filter.Tendsto (fun n => edist (u n) t)
        Filter.atTop (nhds 0) :=
      (tendsto_iff_edist_tendsto_0.mp hu_tendsto)
    -- Step E: edist (u n) t ^ q → 0 (continuity of x^q at 0, with 0^q = 0 for q > 0).
    have h_pow_tendsto : Filter.Tendsto (fun n => edist (u n) t ^ q)
        Filter.atTop (nhds 0) := by
      have := h_edist_tendsto.ennrpow_const q
      rwa [ENNReal.zero_rpow_of_pos hq_pos] at this
    -- Step F: M · edist^q → 0 (M ≠ ⊤ since M : ℝ≥0).
    have hM_ne_top : (M : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have h_M_pow_tendsto : Filter.Tendsto
        (fun n => (M : ℝ≥0∞) * edist (u n) t ^ q)
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.const_mul h_pow_tendsto (Or.inr hM_ne_top)
      simpa using this
    -- Step G: divide the per-pair Markov bound by δ^p (δ^p ≠ 0 for the
    -- constant-division tendsto below).
    have hδp_pos : 0 < δ ^ p := by
      apply ENNReal.rpow_pos_of_nonneg hδ
      exact hp_pos.le
    -- The bound on P {δ ≤ edist}: the per-pair Markov/Chebyshev tail bound.
    have h_set_bound : ∀ n, P {ω | δ ≤ edist (X (u n) ω) (X t ω)}
        ≤ ((M : ℝ≥0∞) * edist (u n) t ^ q) / δ ^ p :=
      fun n => kolmogorov_markov_bound P X hX (u n) t hδ hδ_top
    -- Step G applied: (M · edist^q) / δ^p → 0 from h_M_pow_tendsto (constant division).
    have h_bound_tendsto : Filter.Tendsto
        (fun n => ((M : ℝ≥0∞) * edist (u n) t ^ q) / δ ^ p)
        Filter.atTop (nhds 0) := by
      have := ENNReal.Tendsto.div_const h_M_pow_tendsto (Or.inr hδp_pos.ne')
      simpa using this
    -- Step H: squeeze 0 ≤ P {δ ≤ edist} ≤ bound → 0.
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds h_bound_tendsto (fun _ => bot_le) h_set_bound
  -- Step 4: extract a.s.-converging subsequence.
  obtain ⟨ns, _hns_mono, hns_ae⟩ := h_TIM.exists_seq_tendsto_ae
  -- Step 5: combine on the full-measure intersection.
  -- A := {ω : Continuous Y(·) ω}              (from h_continuous, P-full)
  -- B_k := {ω : Y(u (ns k)) ω = X(u (ns k)) ω}  (from h_dyadic_eq, P-full)
  -- C := {ω : X(u (ns k)) ω → X(t) ω}           (from hns_ae, P-full)
  -- D := A ∩ ⋂_k B_k ∩ C  (countable intersection of full sets = full)
  -- On D: Y(u (ns k)) ω = X(u (ns k)) ω → X(t) ω.
  --       Also Y(u (ns k)) ω → Y(t) ω (by continuity of Y at t along u (ns k) → t).
  --       By uniqueness of limits in ℝ: Y(t) ω = X(t) ω.
  filter_upwards [h_continuous, hns_ae,
    MeasureTheory.ae_all_iff.mpr (fun k => h_dyadic_eq (u (ns k)) (hu_dyadic (ns k)).2)]
    with ω h_Y_cont h_X_tendsto h_eq_seq
  -- u (ns k) → t (subsequence of u → t via StrictMono ns → atTop atTop)
  have h_subseq_tendsto : Filter.Tendsto (fun k => u (ns k)) Filter.atTop (nhds t) :=
    hu_tendsto.comp _hns_mono.tendsto_atTop
  -- Y is continuous at t (from a.s. continuity)
  have h_Y_tendsto : Filter.Tendsto (fun k => Y (u (ns k)) ω) Filter.atTop (nhds (Y t ω)) :=
    (h_Y_cont.tendsto t).comp h_subseq_tendsto
  -- So X(u (ns k)) ω → Y(t) ω (substitute Y(u (ns k)) ω = X(u (ns k)) ω),
  -- and also → X(t) ω. By uniqueness of limits in ℝ, Y(t) ω = X(t) ω.
  have h_X_to_Y : Filter.Tendsto (fun k => X (u (ns k)) ω) Filter.atTop (nhds (Y t ω)) := by
    have h_eq : (fun k => X (u (ns k)) ω) = fun k => Y (u (ns k)) ω := by
      funext k
      exact (h_eq_seq k).symm
    rw [h_eq]
    exact h_Y_tendsto
  exact tendsto_nhds_unique h_X_to_Y h_X_tendsto

/-- **CITED AXIOM: Kolmogorov-Chentsov continuous modification theorem.**

A real-valued stochastic process satisfying the Kolmogorov moment condition
`𝔼[|X_t − X_s|^p] ≤ M · |t − s|^q` with `q > 1` admits a modification
with continuous paths.

**Reference**: Karatzas, I. & Shreve, S. *Brownian Motion and Stochastic Calculus*,
Springer 1991, Theorem 2.2.8; Le Gall, J.-F. *Brownian Motion, Martingales and
Stochastic Calculus*, Springer 2016, Theorem 2.9; Revuz, D. & Yor, M.
*Continuous Martingales and Brownian Motion*, Springer 1999, Theorem I.2.1.

**Standard proof outline**: Apply the Markov inequality to bound
`P(|X_{(k+1)/2^n} − X_{k/2^n}| ≥ 2^{-αn}) ≤ M · 2^{-n(q-αp)}` for `α < (q-1)/p`;
sum over `n` (Borel-Cantelli) to get α-Hölder continuity on the dyadics; extend
continuously to ℝ via uniform continuity of the dyadic restriction. The dyadic
Hölder + extension steps are partially set up in `kolmogorov_dyadic_holder` and
`holder_dense_extends_continuous` (both currently `True`-stubbed).

**Replacement plan**: when Mathlib gains `ProbabilityTheory.IsKolmogorovProcess`'s
modification theorem (currently has only the condition), replace this `axiom`
with a forwarder. Tracked in `tools/cited_axioms.md`. -/
axiom kolmogorovChentsov_modification
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (_hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (_hq : 1 < q) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω)

/-- **Integrability set is `univ` for Gaussian.** `0 ∈ interior (integrableExpSet
id (gaussianReal 0 v))`. -/
lemma zero_mem_interior_integrableExpSet_gaussianReal (v : ℝ≥0) :
    0 ∈ interior
      (ProbabilityTheory.integrableExpSet id (ProbabilityTheory.gaussianReal 0 v)) := by
  rw [ProbabilityTheory.integrableExpSet_id_gaussianReal]
  rw [interior_univ]
  exact Set.mem_univ 0

/-- **First derivative of `t ↦ exp(c · t²)`.** -/
lemma deriv_exp_quadratic (c : ℝ) :
    deriv (fun t : ℝ => Real.exp (c * t^2)) = fun t => 2 * c * t * Real.exp (c * t^2) := by
  funext t
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_outer : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  rw [h_outer.deriv]
  ring

/-- **First derivative at 0 is 0.** `f'(0) = 2c·0·exp(0) = 0`. -/
lemma iteratedDeriv1_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 1 (fun t : ℝ => Real.exp (c * t^2)) 0 = 0 := by
  rw [iteratedDeriv_one, deriv_exp_quadratic]
  ring

/-- **Second derivative of `t ↦ exp(c · t²)`.** `f''(t) = (2c + 4c²t²) · exp(c·t²)`.

(Equivalently: `f'' = 2c·exp + 4c²·t²·exp`.) -/
lemma deriv2_exp_quadratic (c : ℝ) :
    deriv (deriv (fun t : ℝ => Real.exp (c * t^2)))
      = fun t => (2 * c + 4 * c^2 * t^2) * Real.exp (c * t^2) := by
  rw [deriv_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => 2*c*t * exp(c*t^2)) t = (2c + 4c²t²) exp(c*t²)
  -- Product rule: deriv (g · h) = g' · h + g · h' where g(t) = 2*c*t, h(t) = exp(c*t²).
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  have h_lin : HasDerivAt (fun t : ℝ => 2 * c * t) (2 * c) t := by
    simpa using (hasDerivAt_id t).const_mul (2 * c)
  have h_prod : HasDerivAt (fun t : ℝ => 2 * c * t * Real.exp (c * t^2))
      (2 * c * Real.exp (c * t^2) + 2 * c * t * (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_lin.mul h_exp
  rw [h_prod.deriv]
  ring

/-- **Second derivative at 0 is `2c`.** -/
lemma iteratedDeriv2_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 2 (fun t : ℝ => Real.exp (c * t^2)) 0 = 2 * c := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one,
      deriv2_exp_quadratic]
  simp [Real.exp_zero, mul_comm]

/-- **Third derivative of `t ↦ exp(c · t²)`.**
`f'''(t) = (12c²t + 8c³t³) · exp(c·t²)`. -/
lemma deriv3_exp_quadratic (c : ℝ) :
    deriv (deriv (deriv (fun t : ℝ => Real.exp (c * t^2))))
      = fun t => (12 * c^2 * t + 8 * c^3 * t^3) * Real.exp (c * t^2) := by
  rw [deriv2_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => (2c + 4c²t²) · exp(c*t²)) t = (12c²t + 8c³t³) exp(c*t²)
  -- Use product rule: g(t) := 2c + 4c²t², h(t) := exp(c*t²).
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  have h_quad : HasDerivAt (fun t : ℝ => 2 * c + 4 * c^2 * t^2)
      (4 * c^2 * (2 * t)) t := by
    have := ((hasDerivAt_pow 2 t).const_mul (4 * c^2)).const_add (2 * c)
    simpa [pow_one] using this
  have h_prod : HasDerivAt
      (fun t : ℝ => (2 * c + 4 * c^2 * t^2) * Real.exp (c * t^2))
      (4 * c^2 * (2 * t) * Real.exp (c * t^2)
        + (2 * c + 4 * c^2 * t^2) * (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_quad.mul h_exp
  rw [h_prod.deriv]
  ring

/-- **Third derivative at 0 is `0`.** -/
lemma iteratedDeriv3_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 3 (fun t : ℝ => Real.exp (c * t^2)) 0 = 0 := by
  rw [show (3 : ℕ) = 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_one, deriv3_exp_quadratic]
  ring

/-- **Fourth derivative of `t ↦ exp(c · t²)`.**
`f⁽⁴⁾(t) = (12c² + 48c³t² + 16c⁴t⁴) · exp(c·t²)`. -/
lemma deriv4_exp_quadratic (c : ℝ) :
    deriv (deriv (deriv (deriv (fun t : ℝ => Real.exp (c * t^2)))))
      = fun t => (12 * c^2 + 48 * c^3 * t^2 + 16 * c^4 * t^4) * Real.exp (c * t^2) := by
  rw [deriv3_exp_quadratic]
  funext t
  -- Goal: deriv (fun t => (12c²t + 8c³t³) · exp(c·t²)) t
  --     = (12c² + 48c³t² + 16c⁴t⁴) exp(c·t²)
  have h_inner : HasDerivAt (fun t : ℝ => c * t^2) (c * (2 * t)) t := by
    have := (hasDerivAt_pow 2 t).const_mul c
    simpa [pow_one] using this
  have h_exp : HasDerivAt (fun t : ℝ => Real.exp (c * t^2))
      (Real.exp (c * t^2) * (c * (2 * t))) t :=
    h_inner.exp
  -- Derivative of (12c²t + 8c³t³).
  have h_lin : HasDerivAt (fun t : ℝ => 12 * c^2 * t)
      (12 * c^2) t := by
    simpa using (hasDerivAt_id t).const_mul (12 * c^2)
  have h_cub : HasDerivAt (fun t : ℝ => 8 * c^3 * t^3)
      (8 * c^3 * (3 * t^2)) t := by
    have := (hasDerivAt_pow 3 t).const_mul (8 * c^3)
    simpa using this
  have h_poly : HasDerivAt (fun t : ℝ => 12 * c^2 * t + 8 * c^3 * t^3)
      (12 * c^2 + 8 * c^3 * (3 * t^2)) t := h_lin.add h_cub
  have h_prod : HasDerivAt
      (fun t : ℝ => (12 * c^2 * t + 8 * c^3 * t^3) * Real.exp (c * t^2))
      ((12 * c^2 + 8 * c^3 * (3 * t^2)) * Real.exp (c * t^2)
        + (12 * c^2 * t + 8 * c^3 * t^3) *
          (Real.exp (c * t^2) * (c * (2 * t)))) t :=
    h_poly.mul h_exp
  rw [h_prod.deriv]
  ring

/-- **Fourth derivative at 0 is `12c²`.** -/
lemma iteratedDeriv4_exp_quadratic_at_zero' (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (c * t^2)) 0 = 12 * c^2 := by
  rw [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_succ, iteratedDeriv_one, deriv4_exp_quadratic]
  simp [Real.exp_zero]

/-- **Connection**: rewrite from MGF to exponential at the function level. -/
lemma mgf_id_gaussianReal_eq_exp_quadratic (v : ℝ≥0) :
    ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v)
      = fun t : ℝ => Real.exp ((v : ℝ) / 2 * t^2) := by
  rw [ProbabilityTheory.mgf_id_gaussianReal]
  funext t
  ring_nf

/-- **MGF at 0**: `mgf id (gaussianReal 0 v) 0 = 1`. (`exp(0) = 1`.) -/
lemma mgf_id_gaussianReal_at_zero (v : ℝ≥0) :
    ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v) 0 = 1 := by
  rw [mgf_id_gaussianReal_eq_exp_quadratic]
  simp [Real.exp_zero]

/-- **Fourth derivative of `t ↦ exp(c · t²)` at `t = 0` is `12 c²`.**

Real direct calculation via 4 successive applications of chain + product rule.
Proved via `iteratedDeriv4_exp_quadratic_at_zero'` below. -/
lemma iteratedDeriv4_exp_quadratic_at_zero (c : ℝ) :
    iteratedDeriv 4 (fun t : ℝ => Real.exp (c * t^2)) 0 = 12 * c^2 :=
  iteratedDeriv4_exp_quadratic_at_zero' c

/-- **Gaussian fourth moment.** `∫ x^4 ∂(gaussianReal 0 v) = 3 v²`.

Real proof using the chain:
1. `mgf id (gaussianReal 0 v) = fun t ↦ exp(v t² / 2)` by `mgf_id_gaussianReal`.
2. `iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0 = ∫ x^4 ∂(gaussianReal 0 v)`
   by `iteratedDeriv_mgf_zero` (with integrability from
   `zero_mem_interior_integrableExpSet_gaussianReal`).
3. `iteratedDeriv 4 (fun t ↦ exp((v/2) · t²)) 0 = 12 (v/2)² = 3v²` by our
   `iteratedDeriv4_exp_quadratic_at_zero` (with `c = v/2`). -/
lemma gaussianReal_fourth_moment (v : ℝ≥0) :
    ∫ x : ℝ, x ^ 4 ∂(ProbabilityTheory.gaussianReal 0 v) = 3 * (v : ℝ)^2 := by
  -- Step 1: ∫ x^4 = iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0
  have h_int := zero_mem_interior_integrableExpSet_gaussianReal v
  have h_mgf_deriv :=
    ProbabilityTheory.iteratedDeriv_mgf_zero (X := id)
      (μ := ProbabilityTheory.gaussianReal 0 v) h_int 4
  -- h_mgf_deriv : iteratedDeriv 4 (mgf id (gaussianReal 0 v)) 0 = μ[id^4]
  -- where μ[id^4] = ∫ x, id x ^ 4 ∂μ = ∫ x, x^4 ∂μ.
  -- Step 2: rewrite mgf using mgf_id_gaussianReal
  have h_mgf : ProbabilityTheory.mgf id (ProbabilityTheory.gaussianReal 0 v)
      = fun t => Real.exp ((v : ℝ) * t^2 / 2) := by
    rw [ProbabilityTheory.mgf_id_gaussianReal]
    funext t; ring_nf
  -- Step 3: equality of the two functions at the iteratedDeriv level
  have h_funeq : (fun t : ℝ => Real.exp ((v : ℝ) * t^2 / 2))
      = (fun t : ℝ => Real.exp (((v : ℝ) / 2) * t^2)) := by
    funext t; ring_nf
  -- Step 4: apply iteratedDeriv4_exp_quadratic_at_zero with c = v/2
  have h4 := iteratedDeriv4_exp_quadratic_at_zero ((v : ℝ) / 2)
  -- h4 : iteratedDeriv 4 (fun t => exp((v/2) * t^2)) 0 = 12 * (v/2)^2
  -- Combine
  rw [show ∫ x, x^4 ∂(ProbabilityTheory.gaussianReal 0 v)
      = (ProbabilityTheory.gaussianReal 0 v)[id^4] from by
        simp [Pi.pow_apply]]
  rw [← h_mgf_deriv, h_mgf, h_funeq, h4]
  ring

/-- **Brownian increment fourth moment.** For a process `X` with Brownian-law
increments, `𝔼[(X_t − X_s)⁴] = 3 (t − s)²` for `s < t`. -/
lemma brownian_increment_fourth_moment
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩)
    {s t : ℝ} (hst : s < t) :
    ∫ ω, (X t ω - X s ω) ^ 4 ∂P = 3 * (t - s) ^ 2 := by
  -- Push to the pushforward measure via integral_map.
  have h_meas_diff : Measurable (fun ω => X t ω - X s ω) :=
    (h_meas t).sub (h_meas s)
  rw [show ∫ ω, (X t ω - X s ω) ^ 4 ∂P
        = ∫ x, x ^ 4 ∂(P.map (fun ω => X t ω - X s ω)) from
    (MeasureTheory.integral_map h_meas_diff.aemeasurable
      (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ 4) _)).symm]
  rw [h_increment hst]
  -- Goal: ∫ x, x^4 ∂(gaussianReal 0 ⟨t-s, _⟩) = 3 * (t-s)^2.
  have h := gaussianReal_fourth_moment ⟨t - s, by linarith⟩
  simpa using h

/-- **Auxiliary: Kolmogorov bound for Brownian increments (`s < t` case).**
For a process `X` with Brownian-law increments,
`∫⁻ ω, edist (X s ω) (X t ω)^4 ∂P ≤ 3 * edist s t ^ 2` when `s < t`.

Proof: convert `edist^4` to `ENNReal.ofReal ((X s ω - X t ω)^4)` (via
`edist_dist` and `|x|^4 = x^4`), push forward through the increment map,
apply `h_increment` to get `gaussianReal 0 ⟨t - s, _⟩`, then use
`gaussianReal_fourth_moment` and ENNReal arithmetic. -/
lemma brownian_continuous_modification_kol_aux
    {P : Measure Ω} [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩)
    {s t : ℝ} (hst : s < t) :
    ∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P ≤ 3 * edist s t ^ 2 := by
  have h_pow_abs : ∀ x : ℝ, |x|^4 = x^4 := fun x => by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  have h_edist_pow : ∀ ω, edist (X s ω) (X t ω) ^ 4
      = ENNReal.ofReal ((X s ω - X t ω)^4) := by
    intro ω
    rw [edist_dist, Real.dist_eq, ← ENNReal.ofReal_pow (abs_nonneg _), h_pow_abs]
  have h_meas_diff : Measurable (fun ω => X t ω - X s ω) :=
    (h_meas t).sub (h_meas s)
  have h_neg_pow : ∀ ω, (X s ω - X t ω)^4 = (X t ω - X s ω)^4 := fun ω => by ring
  rw [show (∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P)
        = ∫⁻ ω, ENNReal.ofReal ((X t ω - X s ω)^4) ∂P from
      by apply lintegral_congr; intro ω; rw [h_edist_pow ω, h_neg_pow ω]]
  rw [show (∫⁻ ω, ENNReal.ofReal ((X t ω - X s ω)^4) ∂P)
       = ∫⁻ y, ENNReal.ofReal (y^4) ∂(P.map (fun ω => X t ω - X s ω)) from
      by rw [lintegral_map (by fun_prop) h_meas_diff]]
  rw [h_increment hst]
  set v : NNReal := ⟨t - s, by linarith⟩ with hv_def
  have h_v_eq : (v : ℝ) = t - s := rfl
  have h_int : MeasureTheory.Integrable (fun x : ℝ => x^4)
      (ProbabilityTheory.gaussianReal 0 v) := by
    have h_memLp : MeasureTheory.MemLp (id : ℝ → ℝ) 4
        (ProbabilityTheory.gaussianReal 0 v) :=
      ProbabilityTheory.IsGaussian.memLp_id
        (ProbabilityTheory.gaussianReal 0 v) 4 (by simp)
    have h := h_memLp.integrable_norm_pow (p := 4) (by norm_num)
    convert h using 1
    ext x
    change x^4 = ‖x‖^4
    rw [Real.norm_eq_abs, h_pow_abs]
  have h_nn : 0 ≤ᵐ[ProbabilityTheory.gaussianReal 0 v] fun x : ℝ => x^4 := by
    filter_upwards with x
    positivity
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal h_int h_nn]
  rw [gaussianReal_fourth_moment v, h_v_eq]
  have h_edist_st : edist s t = ENNReal.ofReal (t - s) := by
    rw [edist_dist, Real.dist_eq]
    congr 1
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hst)]
  rw [h_edist_st]
  rw [show (3 : ENNReal) = ENNReal.ofReal 3 from by
    rw [ENNReal.ofReal_eq_coe_nnreal (by norm_num : (0 : ℝ) ≤ 3)]
    norm_cast]
  rw [← ENNReal.ofReal_pow (sub_nonneg.mpr (le_of_lt hst))]
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]

/-- **Continuous modification of a Brownian-increment process.** Any
real-valued process whose increments have the Brownian law
`(W_t − W_s) ~ 𝒩(0, t − s)` admits a continuous modification.

Proof structure:
* The Gaussian fourth moment identity (via `gaussianReal_fourth_moment`)
  gives `𝔼[(X_t − X_s)^4] = 3 (t − s)^2`, so the process satisfies
  `IsKolmogorovProcess` with `p = 4`, `q = 2`, `M = 3`.
* Apply `kolmogorovChentsov_modification` with `q = 2 > 1`.

The hypothesis `h_increment` is stated for **all** real `s < t` (no
nonnegativity constraint). This is consistent with a two-sided BM and is
required because the Kolmogorov bound must hold for all `s, t : ℝ`. -/
theorem brownian_continuous_modification
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ)
    (h_meas : ∀ s : ℝ, Measurable (X s))
    (h_increment : ∀ {s t : ℝ} (hst : s < t),
       P.map (fun ω => X t ω - X s ω)
         = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) :
    ∃ Y : ℝ → Ω → ℝ,
      (∀ᵐ ω ∂P, Continuous (fun t => Y t ω)) ∧
      (∀ t : ℝ, ∀ᵐ ω ∂P, Y t ω = X t ω) := by
  have h_kolmogorov :
      ProbabilityTheory.IsKolmogorovProcess X P 4 2 3 :=
    ProbabilityTheory.IsKolmogorovProcess.mk_of_secondCountableTopology
      h_meas
      (h_kol := ?_)
      (hp := by norm_num) (hq := by norm_num)
  · exact kolmogorovChentsov_modification P X h_kolmogorov (by norm_num)
  · -- Sub-goal: ∀ s t, ∫⁻ ω, edist (X s ω) (X t ω) ^ 4 ∂P ≤ 3 * edist s t ^ 2.
    intro s t
    -- The Kolmogorov condition uses ENNReal rpow `^ (4 : ℝ)`, but our aux
    -- uses Nat pow `^ (4 : ℕ)`. Bridge via `ENNReal.rpow_natCast`.
    have h_rpow_nat : ∀ ω, edist (X s ω) (X t ω) ^ (4 : ℝ)
        = edist (X s ω) (X t ω) ^ (4 : ℕ) := fun ω => by
      rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) from by norm_num,
          ENNReal.rpow_natCast]
    have h_int_eq :
        (∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℝ) ∂P)
          = ∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℕ) ∂P := by
      apply lintegral_congr
      exact h_rpow_nat
    have h_rhs : edist s t ^ (2 : ℝ) = edist s t ^ (2 : ℕ) := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num,
          ENNReal.rpow_natCast]
    rw [h_int_eq, h_rhs]
    rcases lt_trichotomy s t with hst | hst | hst
    · -- Case s < t. Use brownian_increment_fourth_moment.
      exact brownian_continuous_modification_kol_aux X h_meas h_increment hst
    · -- Case s = t. Both sides = 0.
      subst hst
      simp
    · -- Case s > t. By symmetry of edist, reduce to t < s.
      have h_swap : (∫⁻ ω, edist (X s ω) (X t ω) ^ (4 : ℕ) ∂P)
          = ∫⁻ ω, edist (X t ω) (X s ω) ^ (4 : ℕ) ∂P := by
        apply lintegral_congr
        intro ω
        rw [edist_comm]
      rw [h_swap, edist_comm s t]
      exact brownian_continuous_modification_kol_aux X h_meas h_increment hst

end LevyStochCalc.Brownian.Continuity
