/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PathRegularity
import LevyStochCalc.Brownian.ItoIntegrandComplete

/-!
# The cell-average rate for a deterministic Lipschitz integrand

For a function `h : ℝ → ℝ` with `|h s - h t| ≤ K * |s - t|` and a strictly monotone partition
`0 = t_0 < ⋯ < t_M = T` of mesh at most `δ`, the pathwise average of `h` over the cell
`(t_n, t_{n+1}]` containing `s` differs from `h s` by at most `K * δ`, so the energy of
`h - conditionalTimeAverage_Z π h` over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T`.

The integrand treated here is deterministic: it is the process `Z s ω i = h s`, constant in the
sample point and in the coordinate. The cell-average rate for a random integrand is a different,
genuinely stochastic statement and is not covered by anything below.
-/

open MeasureTheory

open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u

section Lipschitz

variable {K : ℝ} {h : ℝ → ℝ}

/-- A function obeying `|h s - h t| ≤ K * |s - t|` on `ℝ` has a nonnegative constant. -/
theorem nonneg_of_lipschitz_bound (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) : 0 ≤ K := by
  have h01 := hlip 0 1
  have habs : |(0 : ℝ) - 1| = 1 := by norm_num
  rw [habs, mul_one] at h01
  exact (abs_nonneg _).trans h01

/-- A function obeying `|h s - h t| ≤ K * |s - t|` on `ℝ` is continuous. -/
theorem continuous_of_lipschitz_bound (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) :
    Continuous h := by
  have hK := nonneg_of_lipschitz_bound hlip
  refine (LipschitzWith.of_dist_le_mul (K := K.toNNReal) fun x y => ?_).continuous
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal K hK]
  exact hlip x y

/-- The average of a function obeying `|h s - h t| ≤ K * |s - t|` over `[a, b]` differs from its
value at any point of `(a, b]` by at most `K * (b - a)`. -/
theorem abs_sub_intervalAverage_le (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|)
    {a b s : ℝ} (hab : a < b) (hs : s ∈ Set.Ioc a b) :
    |h s - (1 / (b - a)) * ∫ u in Set.Icc a b, h u| ≤ K * (b - a) := by
  have hK := nonneg_of_lipschitz_bound hlip
  have hcont := continuous_of_lipschitz_bound hlip
  have hΔ : (0 : ℝ) < b - a := sub_pos.mpr hab
  have hne : b - a ≠ 0 := ne_of_gt hΔ
  have hinv : (0 : ℝ) < 1 / (b - a) := div_pos one_pos hΔ
  have hvol : (volume (Set.Icc a b)).toReal = b - a := by
    rw [Real.volume_Icc, ENNReal.toReal_ofReal hΔ.le]
  have hint : IntegrableOn h (Set.Icc a b) volume := hcont.integrableOn_Icc
  have hcst : IntegrableOn (fun _ : ℝ => h s) (Set.Icc a b) volume :=
    continuous_const.integrableOn_Icc
  have hsplit : ∫ u in Set.Icc a b, (h s - h u) = (b - a) * h s - ∫ u in Set.Icc a b, h u := by
    rw [integral_sub hcst hint, setIntegral_const, smul_eq_mul, measureReal_def, hvol]
  have hrw : h s - (1 / (b - a)) * ∫ u in Set.Icc a b, h u
      = (1 / (b - a)) * ∫ u in Set.Icc a b, (h s - h u) := by
    rw [hsplit, mul_sub, ← mul_assoc, one_div, inv_mul_cancel₀ hne, one_mul]
  have hbd : |∫ u in Set.Icc a b, (h s - h u)| ≤ K * (b - a) * (b - a) := by
    have h1 : ‖∫ u in Set.Icc a b, (h s - h u)‖
        ≤ K * (b - a) * volume.real (Set.Icc a b) := by
      refine norm_setIntegral_le_of_norm_le_const ?_ fun u hu => ?_
      · rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      · rw [Real.norm_eq_abs]
        refine (hlip s u).trans (mul_le_mul_of_nonneg_left ?_ hK)
        obtain ⟨hua, hub⟩ := hu
        obtain ⟨hsa, hsb⟩ := hs
        rw [abs_le]
        constructor <;> linarith
    rwa [Real.norm_eq_abs, measureReal_def, hvol] at h1
  rw [hrw, abs_mul, abs_of_pos hinv]
  calc 1 / (b - a) * |∫ u in Set.Icc a b, (h s - h u)|
      ≤ 1 / (b - a) * (K * (b - a) * (b - a)) := mul_le_mul_of_nonneg_left hbd hinv.le
    _ = K * (b - a) := by field_simp

end Lipschitz

section Cells

variable {M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

/-- Every point of `(0, T]` lies in exactly one cell `(π n.castSucc, π n.succ]` of a strictly
monotone partition `π` of `[0, T]`. -/
theorem existsUnique_mem_cell (hmono : StrictMono π) (h0 : π 0 = 0) (hT : π (Fin.last M) = T)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T) :
    ∃! n : Fin M, π n.castSucc < s ∧ s ≤ π n.succ := by
  classical
  obtain ⟨hs0, hsT⟩ := hs
  have huniq : ∀ m n : Fin M, π m.castSucc < s → s ≤ π m.succ →
      π n.castSucc < s → s ≤ π n.succ → m = n := by
    intro m n hm1 hm2 hn1 hn2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hval : (m : ℕ) < (n : ℕ) := Fin.lt_def.mp hlt
      have hle : (m.succ : Fin (M + 1)) ≤ n.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega
      have := hmono.monotone hle
      linarith
    · have hval : (n : ℕ) < (m : ℕ) := Fin.lt_def.mp hlt
      have hle : (n.succ : Fin (M + 1)) ≤ m.castSucc := by
        rw [Fin.le_def, Fin.val_succ, Fin.val_castSucc]
        omega
      have := hmono.monotone hle
      linarith
  rcases Nat.eq_zero_or_pos M with hM | hMpos
  · exfalso
    subst hM
    have hlast : (Fin.last 0 : Fin (0 + 1)) = 0 := by ext; simp
    have hT0 : T = 0 := by rw [← hT, ← h0, hlast]
    rw [hT0] at hsT
    linarith
  · have hzero : ((⟨0, hMpos⟩ : Fin M).castSucc : Fin (M + 1)) = 0 := by ext; simp
    have hSne : (Finset.univ.filter fun n : Fin M => π n.castSucc < s).Nonempty := by
      refine ⟨⟨0, hMpos⟩, ?_⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, by rw [hzero, h0]; exact hs0⟩
    obtain ⟨n₀, hn₀mem, hn₀max⟩ :
        ∃ n₀ ∈ Finset.univ.filter fun n : Fin M => π n.castSucc < s,
          ∀ m ∈ Finset.univ.filter fun n : Fin M => π n.castSucc < s, m ≤ n₀ :=
      ⟨_, Finset.max'_mem _ hSne, fun m hm => Finset.le_max' _ m hm⟩
    have hn₀lt : π n₀.castSucc < s := (Finset.mem_filter.mp hn₀mem).2
    have hn₀le : s ≤ π n₀.succ := by
      rw [← not_lt]
      intro hcon
      by_cases hlast : (n₀ : ℕ) + 1 = M
      · have he : (n₀.succ : Fin (M + 1)) = Fin.last M := by
          ext; simp only [Fin.val_succ, Fin.val_last]; omega
        rw [he, hT] at hcon
        linarith
      · have hlt : (n₀ : ℕ) + 1 < M := by have := n₀.isLt; omega
        have hcast : (⟨(n₀ : ℕ) + 1, hlt⟩ : Fin M).castSucc = n₀.succ := by ext; simp
        have hmem : (⟨(n₀ : ℕ) + 1, hlt⟩ : Fin M) ∈
            Finset.univ.filter fun n : Fin M => π n.castSucc < s := by
          rw [Finset.mem_filter]
          exact ⟨Finset.mem_univ _, by rw [hcast]; exact hcon⟩
        have hle : (n₀ : ℕ) + 1 ≤ (n₀ : ℕ) := hn₀max _ hmem
        omega
    exact ⟨n₀, ⟨hn₀lt, hn₀le⟩, fun m hm => huniq m n₀ hm.1 hm.2 hn₀lt hn₀le⟩

/-- On the cell `(π n.castSucc, π n.succ]` of a strictly monotone partition of mesh at most `δ`,
the average of a function obeying `|h s - h t| ≤ K * |s - t|` over that cell differs from its
value at any point of the cell by at most `K * δ`. -/
theorem cell_sub_average_le_of_lipschitz (hmono : StrictMono π)
    (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (n : Fin M) {s : ℝ}
    (hs : s ∈ Set.Ioc (π n.castSucc) (π n.succ)) :
    |h s - (1 / (π n.succ - π n.castSucc)) *
      ∫ u in Set.Icc (π n.castSucc) (π n.succ), h u| ≤ K * δ := by
  have hab : π n.castSucc < π n.succ := hmono (Fin.castSucc_lt_succ)
  exact (abs_sub_intervalAverage_le hlip hab hs).trans
    (mul_le_mul_of_nonneg_left (hδ n) (nonneg_of_lipschitz_bound hlip))

end Cells

section Deterministic

variable {Ω : Type u} [MeasurableSpace Ω]
variable {d M : ℕ} {π : Fin (M + 1) → ℝ} {T δ K : ℝ} {h : ℝ → ℝ}

omit [MeasurableSpace Ω] in
/-- For the deterministic process `Z s ω i = h s` with `|h s - h t| ≤ K * |s - t|`, the pathwise
cell average over a strictly monotone partition of `[0, T]` of mesh at most `δ` stays within
`K * δ` of `h s` at every time of `(0, T]`. -/
theorem conditionalTimeAverage_sub_le_of_lipschitz (hmono : StrictMono π) (h0 : π 0 = 0)
    (hT : π (Fin.last M) = T) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) T)
    (ω : Ω) (i : Fin d) :
    |h s - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i| ≤ K * δ := by
  classical
  obtain ⟨n₀, hn₀, huniq⟩ := existsUnique_mem_cell hmono h0 hT hs
  have hsum : conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i
      = (1 / (π n₀.succ - π n₀.castSucc)) *
        ∫ u in Set.Icc (π n₀.castSucc) (π n₀.succ), h u := by
    simp only [conditionalTimeAverage_Z]
    rw [Finset.sum_eq_single n₀]
    · rw [if_pos hn₀]
    · intro b _ hb
      exact if_neg fun hcon => hb (huniq b hcon)
    · intro hcon
      exact absurd (Finset.mem_univ n₀) hcon
  rw [hsum]
  exact cell_sub_average_le_of_lipschitz hmono hδ hlip n₀ (Set.mem_Ioc.mpr hn₀)

omit [MeasurableSpace Ω] in
/-- For the deterministic process `Z s ω i = h s` with `|h s - h t| ≤ K * |s - t|`, the squared
`L²(dt)` error of the pathwise cell average over a strictly monotone partition of `[0, T]` of
mesh at most `δ` is at most `(K * δ) ^ 2 * T`. -/
theorem lintegral_sq_sub_conditionalTimeAverage_le_of_lipschitz (hmono : StrictMono π)
    (h0 : π 0 = 0) (hT : π (Fin.last M) = T) (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (ω : Ω) (i : Fin d) :
    ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖h s - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i‖₊ :
          ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal ((K * δ) ^ 2 * T) := by
  classical
  have hae : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (‖h s - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i‖₊ :
        ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal ((K * δ) ^ 2) := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Icc]
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr (measure_singleton (0 : ℝ))] with
      s hs0 hsIcc
    have hsIoc : s ∈ Set.Ioc (0 : ℝ) T :=
      ⟨lt_of_le_of_ne hsIcc.1 (Ne.symm (by simpa using hs0)), hsIcc.2⟩
    have hbound := conditionalTimeAverage_sub_le_of_lipschitz hmono h0 hT hδ hlip hsIoc ω i
    set x := h s - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i with hx
    rw [show (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ from (ofReal_norm x).symm,
      ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg x])
  calc ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖h s - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i‖₊ :
          ℝ≥0∞) ^ 2
      ≤ ∫⁻ _ in Set.Icc (0 : ℝ) T, ENNReal.ofReal ((K * δ) ^ 2) := lintegral_mono_ae hae
    _ = ENNReal.ofReal ((K * δ) ^ 2) * volume (Set.Icc (0 : ℝ) T) := setLIntegral_const _ _
    _ = ENNReal.ofReal ((K * δ) ^ 2 * T) := by
        rw [Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul (sq_nonneg _)]

/-- For the deterministic process `Z s ω i = h s` with `|h s - h t| ≤ K * |s - t|`, the energy of
the cell-average error over the horizon `[0, T]` is at most `(K * δ) ^ 2 * T`, where `δ` bounds
the mesh of the strictly monotone partition `π` of `[0, T]`. -/
theorem energy_sub_conditionalTimeAverage_le_of_lipschitz (P : Measure Ω)
    [IsProbabilityMeasure P] (hmono : StrictMono π) (h0 : π 0 = 0) (hT : π (Fin.last M) = T)
    (hδ : ∀ n : Fin M, π n.succ - π n.castSucc ≤ δ)
    (hlip : ∀ s t : ℝ, |h s - h t| ≤ K * |s - t|) (i : Fin d) :
    Brownian.Ito.energy P T
        (fun ω s => h s - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i)
      ≤ ENNReal.ofReal ((K * δ) ^ 2 * T) := by
  calc Brownian.Ito.energy P T
        (fun ω s => h s - conditionalTimeAverage_Z π (fun u (_ : Ω) (_ : Fin d) => h u) s ω i)
      ≤ ∫⁻ _ : Ω, ENNReal.ofReal ((K * δ) ^ 2 * T) ∂P :=
        lintegral_mono fun ω =>
          lintegral_sq_sub_conditionalTimeAverage_le_of_lipschitz hmono h0 hT hδ hlip ω i
    _ = ENNReal.ofReal ((K * δ) ^ 2 * T) := by rw [lintegral_const, measure_univ, mul_one]

end Deterministic

end LevyStochCalc.BSDEJ.PathRegularity
