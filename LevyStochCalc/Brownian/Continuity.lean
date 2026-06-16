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

/-- **Step 2: scale-limited Hölder on a dense set → continuous extension.**

A function `f : ℝ → ℝ` that is α-Hölder on a dense set `D ⊆ ℝ` *at scales
`≤ δ₀`* (i.e. `|f s − f t| ≤ K·|s−t|^α` whenever `s, t ∈ D` and `|s − t| ≤ δ₀`)
is uniformly continuous on `D`, hence extends uniquely to a continuous function
on `ℝ` agreeing with `f` on `D`. The scale restriction suffices because uniform
continuity only constrains small distances; this is exactly what the dyadic
chaining produces (`dyadic_holder_chaining`, scales `≤ 2^{−N}`).

Proof via `Dense.uniformContinuous_extend`. -/
lemma holder_dense_extends_continuous {α K δ₀ : ℝ}
    (hα : 0 < α) (_hK : 0 < K) (hδ₀ : 0 < δ₀)
    (D : Set ℝ) (h_dense : Dense D)
    (f : ℝ → ℝ)
    (h_holder_dyadic : ∀ s ∈ D, ∀ t ∈ D, |s - t| ≤ δ₀ →
      |f s - f t| ≤ K * |s - t| ^ α) :
    ∃ g : ℝ → ℝ, Continuous g ∧ ∀ s ∈ D, g s = f s := by
  -- f restricted to D is uniformly continuous (scale-limited α-Hölder ⇒ UC).
  set fD : D → ℝ := fun x => f x.1 with hfD_def
  have h_uc : UniformContinuous fD := by
    rw [Metric.uniformContinuous_iff]
    intro ε hε
    -- Choose δ = min δ₀ (ε / (2 * (K + 1)))^(1/α).
    set C : ℝ := 2 * (K + 1) with hC_def
    have hC_pos : 0 < C := by simp [hC_def]; linarith
    refine ⟨min δ₀ ((ε / C) ^ (1/α)), ?_, ?_⟩
    · exact lt_min hδ₀ (Real.rpow_pos_of_pos (div_pos hε hC_pos) _)
    · intro s t h_dist
      have h_dist_pos : 0 ≤ |s.1 - t.1| := abs_nonneg _
      have h_dist_δ₀ : |s.1 - t.1| ≤ δ₀ := by
        rw [show |s.1 - t.1| = dist s.1 t.1 from (Real.dist_eq _ _).symm]
        exact le_of_lt (lt_of_lt_of_le h_dist (min_le_left _ _))
      have h_holder := h_holder_dyadic s.1 s.2 t.1 t.2 h_dist_δ₀
      -- |s.1 - t.1| < δ
      have h_dist_real : |s.1 - t.1| < (ε / C) ^ (1/α) := by
        rw [show |s.1 - t.1| = dist s.1 t.1 from (Real.dist_eq _ _).symm]
        exact lt_of_lt_of_le h_dist (min_le_right _ _)
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

/-- Finite geometric partial sum bounded by the infinite tail
`∑_{a ≤ n < b} rⁿ ≤ rᵃ / (1 − r)` for `0 ≤ r < 1`. -/
lemma sum_Ico_geometric_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (a b : ℕ) :
    ∑ n ∈ Finset.Ico a b, r ^ n ≤ r ^ a / (1 - r) := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [pow_add]
  rw [← Finset.mul_sum, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← tsum_geometric_of_lt_one hr0 hr1]
  exact Summable.sum_le_tsum _ (fun i _ => by positivity)
    (summable_geometric_of_lt_one hr0 hr1)

/-- **Dyadic scale selection.** For `0 < d ≤ 1` there is `m` with
`(1/2)^{m+1} < d ≤ (1/2)^m`. -/
lemma exists_dyadic_scale {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m := by
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < d :=
    exists_pow_lt_of_lt_one hd0 (by norm_num)
  classical
  have hspec : (1 / 2 : ℝ) ^ Nat.find hex < d := Nat.find_spec hex
  have hpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h] at hspec; simp at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel hpos]; exact hspec
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_lt] at hmin
    exact hmin

/-- `((1/2)^α)^m ≤ 2^α · d^α` when `(1/2)^{m+1} < d`. Converts the geometric
level factor `r^m = ((1/2)^α)^m` into a Hölder factor in `d`. -/
lemma rpow_half_pow_le {α : ℝ} (hα : 0 < α) {d : ℝ} (m : ℕ)
    (hd : (1 / 2 : ℝ) ^ (m + 1) < d) :
    ((1 / 2 : ℝ) ^ α) ^ m ≤ (2 : ℝ) ^ α * d ^ α := by
  have hdpos : 0 < d := lt_of_le_of_lt (by positivity) hd
  have hstep : (1 / 2 : ℝ) ^ m < 2 * d := by
    have he : (1 / 2 : ℝ) ^ m = 2 * (1 / 2) ^ (m + 1) := by rw [pow_succ]; ring
    rw [he]; linarith
  have hr_eq : ((1 / 2 : ℝ) ^ α) ^ m = ((1 / 2 : ℝ) ^ m) ^ α := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) m,
        ← Real.rpow_natCast (1 / 2 : ℝ) m,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2),
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1 / 2), mul_comm]
  rw [hr_eq]
  calc ((1 / 2 : ℝ) ^ m) ^ α
      ≤ (2 * d) ^ α :=
        Real.rpow_le_rpow (by positivity) (le_of_lt hstep) (le_of_lt hα)
    _ = (2 : ℝ) ^ α * d ^ α := Real.mul_rpow (by norm_num) (le_of_lt hdpos)

/-- **KC exponent identity.** `2ⁿ · ((1/2)ⁿ)^q / ((1/2)^α)ⁿ)^p = ((1/2)^{q−αp−1})ⁿ`.
Collapses the per-level Borel–Cantelli factor (a `2ⁿ` union over level-`n`
dyadics, each a Markov term `(2^{−n})^q / (2^{−αn})^p`) to a single geometric
ratio `(1/2)^{q−αp−1}`, which is `< 1` exactly when `αp < q − 1`. -/
lemma kc_exponent_identity {α p q : ℝ} (n : ℕ) :
    (2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p
      = ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n := by
  have h2 : (0 : ℝ) < 1 / 2 := by norm_num
  have e1 : ((1 / 2 : ℝ) ^ n) ^ q = (1 / 2 : ℝ) ^ ((n : ℝ) * q) := by
    rw [← Real.rpow_natCast (1 / 2 : ℝ) n, ← Real.rpow_mul (le_of_lt h2)]
  have e2 : (((1 / 2 : ℝ) ^ α) ^ n) ^ p = (1 / 2 : ℝ) ^ (α * (n : ℝ) * p) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ α) n, ← Real.rpow_mul (le_of_lt h2),
        ← Real.rpow_mul (le_of_lt h2)]
  have e3 : (2 : ℝ) ^ n = (1 / 2 : ℝ) ^ (-(n : ℝ)) := by
    rw [Real.rpow_neg (le_of_lt h2), Real.rpow_natCast,
        show (1 / 2 : ℝ) ^ n = (2 ^ n)⁻¹ from by rw [one_div, inv_pow], inv_inv]
  have e4 : ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n
      = (1 / 2 : ℝ) ^ ((q - α * p - 1) * (n : ℝ)) := by
    rw [← Real.rpow_natCast ((1 / 2 : ℝ) ^ (q - α * p - 1)) n,
        ← Real.rpow_mul (le_of_lt h2)]
  rw [e1, e2, e3, e4, div_eq_mul_inv, ← Real.rpow_neg (le_of_lt h2),
      ← Real.rpow_add h2, ← Real.rpow_add h2]
  congr 1
  ring

/-- **Deterministic dyadic Hölder chaining.** If the consecutive level-`n`
dyadic increments of `f` on `[0,1]` are bounded by `C · ((1/2)^α)^n` for all
`n ≥ N`, then `f` is α-Hölder on the dyadics of `[0,1]` at scales `≤ 2^{-N}`,
with an explicit constant `K`. This is the path-by-path output of the
Borel–Cantelli increment control. -/
lemma dyadic_holder_chaining {f : ℝ → ℝ} {α C : ℝ} {N : ℕ}
    (hα : 0 < α) (hC : 0 ≤ C)
    (hf : ∀ n, N ≤ n → ∀ k : ℤ, 0 ≤ k → k + 1 ≤ 2 ^ n →
      |f ((k + 1 : ℤ) / 2 ^ n) - f ((k : ℤ) / 2 ^ n)| ≤ C * ((1 / 2 : ℝ) ^ α) ^ n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s ∈ dyadicRationals, ∀ t ∈ dyadicRationals,
      0 ≤ s → s ≤ 1 → 0 ≤ t → t ≤ 1 → |s - t| ≤ (1 / 2 : ℝ) ^ N →
      |f s - f t| ≤ K * |s - t| ^ α := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have h1r : 0 < 1 - r := by linarith
  set b : ℕ → ℝ := fun n => C * r ^ n with hb_def
  have hb : ∀ n, 0 ≤ b n := fun n => by simp only [hb_def]; positivity
  set A : ℝ := C * (1 + 2 * r / (1 - r)) with hA_def
  have hA0 : 0 ≤ A := by
    apply mul_nonneg hC
    have : 0 ≤ 2 * r / (1 - r) := div_nonneg (by positivity) (le_of_lt h1r)
    linarith
  have h2α : (0 : ℝ) < (2 : ℝ) ^ α := Real.rpow_pos_of_pos (by norm_num) α
  -- Sum bound: `∑_{Ico (m+1) (L+1)} b ≤ C·r^{m+1}/(1-r)`.
  have hsum : ∀ m L : ℕ, ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n
      ≤ C * r ^ (m + 1) / (1 - r) := by
    intro m L
    simp only [hb_def]
    rw [← Finset.mul_sum]
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hC
    exact sum_Ico_geometric_le (le_of_lt hr0) hr1 (m + 1) (L + 1)
  -- Core bound for an ordered pair `a ≤ c`.
  have core : ∀ a c, a ∈ dyadicRationals → c ∈ dyadicRationals →
      0 ≤ a → c ≤ 1 → a ≤ c → c - a ≤ (1 / 2 : ℝ) ^ N →
      |f a - f c| ≤ (A * 2 ^ α) * (c - a) ^ α := by
    intro a c ha hc ha0 hc1 hac hgap
    rcases eq_or_lt_of_le hac with hac' | hac'
    · subst hac'; simp [Real.zero_rpow hα.ne']
    set d : ℝ := c - a with hd_def
    have hd0 : 0 < d := by simp only [hd_def]; linarith
    have hNle1 : (1 / 2 : ℝ) ^ N ≤ 1 := by
      apply pow_le_one₀ (by norm_num) (by norm_num)
    have hd1 : d ≤ 1 := le_trans hgap hNle1
    obtain ⟨m, hm1, hm2⟩ := exists_dyadic_scale hd0 hd1
    have hmN : N ≤ m := by
      by_contra hlt
      have hNm1 : (1 / 2 : ℝ) ^ N ≤ (1 / 2 : ℝ) ^ (m + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith [le_trans hgap hNm1, hm1]
    obtain ⟨Ls, hLs⟩ := dyadicTrunc_eventually_eq ha
    obtain ⟨Lt, hLt⟩ := dyadicTrunc_eventually_eq hc
    set L : ℕ := max (max Ls Lt) m with hL_def
    have hsL : dyadicTrunc L a = a :=
      hLs L (le_trans (le_max_left _ _) (le_max_left _ _))
    have htL : dyadicTrunc L c = c :=
      hLt L (le_trans (le_max_right _ _) (le_max_left _ _))
    have hmL : m ≤ L := le_max_right _ _
    have hTa := dyadicTrunc_telescope hb hf ha0 (le_trans hac hc1) (by omega) L hmL
    have hTc := dyadicTrunc_telescope hb hf (le_trans ha0 hac) hc1 (by omega) L hmL
    rw [hsL] at hTa
    rw [htL] at hTc
    have hNear := dyadicTrunc_near_step hb hf hmN ha0 hc1 hac hm2
    -- Triangle: split through the two level-m truncations.
    have htri : |f a - f c|
        ≤ |f a - f (dyadicTrunc m a)|
          + |f (dyadicTrunc m a) - f (dyadicTrunc m c)|
          + |f (dyadicTrunc m c) - f c| := by
      calc |f a - f c|
          ≤ |f a - f (dyadicTrunc m a)| + |f (dyadicTrunc m a) - f c| :=
            abs_sub_le _ _ _
        _ ≤ |f a - f (dyadicTrunc m a)|
            + (|f (dyadicTrunc m a) - f (dyadicTrunc m c)|
              + |f (dyadicTrunc m c) - f c|) := by
            gcongr; exact abs_sub_le _ _ _
        _ = _ := by ring
    have hTc' : |f (dyadicTrunc m c) - f c|
        ≤ ∑ n ∈ Finset.Ico (m + 1) (L + 1), b n := by
      rw [abs_sub_comm]; exact hTc
    -- Combine the three pieces.
    have hsumbnd := hsum m L
    have hbm : b m = C * r ^ m := rfl
    have key : |f a - f c| ≤ A * r ^ m := by
      have hchain : |f a - f c|
          ≤ (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) + b m
            + (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) := by
        refine le_trans htri ?_
        gcongr
      refine le_trans hchain ?_
      have hnum : (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n) + b m
          + (∑ n ∈ Finset.Ico (m + 1) (L + 1), b n)
          ≤ C * r ^ (m + 1) / (1 - r) + C * r ^ m + C * r ^ (m + 1) / (1 - r) := by
        linarith [hsum m L, hbm]
      refine le_trans hnum (le_of_eq ?_)
      rw [hA_def]
      field_simp
      ring
    refine le_trans key ?_
    rw [show A * 2 ^ α * d ^ α = A * (2 ^ α * d ^ α) from by ring]
    apply mul_le_mul_of_nonneg_left _ hA0
    rw [hr_def]
    exact rpow_half_pow_le hα m hm1
  -- Dispatch by the order of `s, t`.
  refine ⟨A * 2 ^ α, by positivity, ?_⟩
  intro s hs t ht hs0 hs1 ht0 ht1 hclose
  rcases le_total s t with hst | hst
  · have hgap : t - s ≤ (1 / 2 : ℝ) ^ N := by
      rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ t - s), abs_sub_comm]; exact hclose
    have heq : |s - t| = t - s := by
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]
    rw [heq]
    exact core s t hs ht hs0 ht1 hst hgap
  · have hgap : s - t ≤ (1 / 2 : ℝ) ^ N := by
      rw [← abs_of_nonneg (by linarith : (0:ℝ) ≤ s - t)]; exact hclose
    have heq : |s - t| = s - t := abs_of_nonneg (by linarith)
    rw [heq, abs_sub_comm]
    exact core t s ht hs ht0 hs1 hst hgap

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

/-- Real-threshold form of the tail bound: for `lam > 0`,
`P {ω | lam < |X s ω − X t ω|} ≤ M · edist s t ^ q / (ofReal lam) ^ p`. -/
lemma kolmogorov_real_tail_bound
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    (s t : ℝ) {lam : ℝ} (hlam : 0 < lam) :
    P {ω | lam < |X s ω - X t ω|}
      ≤ (M : ℝ≥0∞) * edist s t ^ q / ENNReal.ofReal lam ^ p := by
  refine le_trans (measure_mono ?_)
    (kolmogorov_markov_bound P X hX s t
      (ENNReal.ofReal_pos.mpr hlam) ENNReal.ofReal_ne_top)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  rw [edist_dist, Real.dist_eq]
  exact ENNReal.ofReal_le_ofReal (le_of_lt hω)

/-- **Lemma A: per-level bad-set bound.** The union over level-`n` dyadic
intervals in `[0,1]` of the events `{ |increment| > ((1/2)^α)^n }` has measure
`≤ ofReal((M:ℝ)·ρⁿ)` with `ρ = (1/2)^{q−αp−1}`. (Borel–Cantelli summability
follows when `αp < q−1`, i.e. `ρ < 1`.) -/
lemma kc_level_bad_measure
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ → Ω → ℝ) {p q : ℝ} {M : ℝ≥0}
    (hX : ProbabilityTheory.IsKolmogorovProcess X P p q M)
    {α : ℝ} (n : ℕ) :
    P (⋃ k ∈ Finset.range (2 ^ n),
        {ω | ((1 / 2 : ℝ) ^ α) ^ n
            < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|})
      ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ (q - α * p - 1)) ^ n) := by
  set r : ℝ := (1 / 2 : ℝ) ^ α with hr_def
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) α
  have hrn0 : 0 < r ^ n := pow_pos hr0 n
  have hhalf_n : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  have hrnp0 : (0 : ℝ) < (r ^ n) ^ p := Real.rpow_pos_of_pos hrn0 p
  -- Per-interval Markov term, converted to `ofReal`.
  have hterm : ∀ k ∈ Finset.range (2 ^ n),
      P {ω | r ^ n < |X (((k : ℝ) + 1) / 2 ^ n) ω - X ((k : ℝ) / 2 ^ n) ω|}
        ≤ ENNReal.ofReal ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (r ^ n) ^ p) := by
    intro k _
    have hb := kolmogorov_real_tail_bound P X hX
      (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n) hrn0
    refine le_trans hb (le_of_eq ?_)
    have hedist : edist (((k : ℝ) + 1) / 2 ^ n) ((k : ℝ) / 2 ^ n)
        = ENNReal.ofReal ((1 / 2 : ℝ) ^ n) := by
      rw [edist_dist, Real.dist_eq]
      congr 1
      rw [show ((k : ℝ) + 1) / 2 ^ n - (k : ℝ) / 2 ^ n = (1 / 2 : ℝ) ^ n from by
        rw [div_pow, one_pow]; ring]
      exact abs_of_pos hhalf_n
    rw [hedist, ENNReal.ofReal_rpow_of_pos hhalf_n,
        ENNReal.ofReal_rpow_of_pos hrn0, ← ENNReal.ofReal_coe_nnreal (p := M),
        ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_div_of_pos hrnp0]
  refine le_trans (measure_biUnion_finset_le (Finset.range (2 ^ n)) _) ?_
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      show ((2 ^ n : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ n) from by
        rw [← ENNReal.ofReal_natCast]; norm_num,
      ← ENNReal.ofReal_mul (by positivity)]
  refine le_of_eq ?_
  congr 1
  rw [hr_def, show (2 : ℝ) ^ n
        * ((M : ℝ) * ((1 / 2 : ℝ) ^ n) ^ q / (((1 / 2 : ℝ) ^ α) ^ n) ^ p)
      = (M : ℝ) * ((2 : ℝ) ^ n * ((1 / 2 : ℝ) ^ n) ^ q
          / (((1 / 2 : ℝ) ^ α) ^ n) ^ p) from by ring,
      kc_exponent_identity]

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
