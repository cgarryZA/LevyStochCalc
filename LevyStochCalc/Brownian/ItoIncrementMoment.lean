/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoFourthMoment

/-!
# Fourth moment of an increment of the Itô integral

The fourth moment of `∫_a^b H dW` for an integrand bounded by `C` is at most
`(6 + c)·C⁴·(b − a)²`, with `c` the fourth moment of the standard Gaussian. The bound is the
per-tile variance budget of `LevyStochCalc.Brownian.Ito.SimplePredictable.varClock` applied to
simple approximants of `1_{(a, b]}·H` that themselves vanish off `(a, b]`, obtained by
multiplying an approximant by `stepIoc` on their common refinement.

## Main statements

* `SimplePredictable.eval_of_mem_Ioc` — a simple integrand evaluates to a tile's coefficient
  at every time in that tile.
* `SimplePredictable.varClock_le_Ioc` — the variance budget of the per-tile bound
  `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`.
* `SimplePredictable.exists_restrict_Ioc` — an adapted simple integrand multiplied by
  `1_{(a, b]}` on their common refinement, with coefficients vanishing off `(a, b]`.
* `lintegral_stochasticIntegralBrownian_pow_four_le_Ioc` — the fourth-moment bound for an
  integrand supported in `(a, b]`.
* `lintegral_stochasticIntegralBrownian_sub_pow_four_le` —
  `𝔼|∫_a^b H dW|⁴ ≤ (6 + c)·C⁴·(b − a)²` for an integrand bounded by `C`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- At most one cell of a strictly monotone partition contains a given time. -/
theorem partition_cell_unique {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    {s : ℝ} {i j : Fin M} (hi : π i.castSucc < s ∧ s ≤ π i.succ)
    (hj : π j.castSucc < s ∧ s ≤ π j.succ) : i = j := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (i.succ : Fin (M + 1)) ≤ j.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
    exact absurd (hi.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
  · have hle : (j.succ : Fin (M + 1)) ≤ i.castSucc := by
      rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
    exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hi.1)

/-- A simple integrand evaluates to a tile's coefficient at every time in that tile. -/
theorem SimplePredictable.eval_of_mem_Ioc {T : ℝ} (H : SimplePredictable Ω T) (j : Fin H.N)
    {s : ℝ} (hs : H.partition j.castSucc < s ∧ s ≤ H.partition j.succ) (ω : Ω) :
    H.eval s ω = H.ξ j ω := by
  classical
  unfold SimplePredictable.eval
  rw [Finset.sum_eq_single j
    (fun i _ hij => if_neg fun hc => hij (partition_cell_unique H.partition_strictMono hc hs))
    (fun hnm => absurd (Finset.mem_univ _) hnm)]
  exact if_pos hs

/-- A simple integrand with coefficients bounded by `C ≥ 0` has evaluations bounded by `C`. -/
theorem SimplePredictable.abs_eval_le {T : ℝ} (H : SimplePredictable Ω T) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ (i : Fin H.N) (ω : Ω), |H.ξ i ω| ≤ C) (s : ℝ) (ω : Ω) : |H.eval s ω| ≤ C := by
  classical
  by_cases h : ∃ j : Fin H.N, H.partition j.castSucc < s ∧ s ≤ H.partition j.succ
  · obtain ⟨j, hj⟩ := h
    rw [H.eval_of_mem_Ioc j hj ω]
    exact hC j ω
  · push Not at h
    have hz : H.eval s ω = 0 := by
      unfold SimplePredictable.eval
      exact Finset.sum_eq_zero fun j _ =>
        if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz, abs_zero]
    exact hC0

/-- The variance budget of the per-tile bound `C·1_{tile ⊆ (a, b]}` is at most `C²(b − a)`. -/
theorem SimplePredictable.varClock_le_Ioc {T : ℝ} (H : SimplePredictable Ω T) {a b C : ℝ}
    (hab : a ≤ b) :
    H.varClock (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0)
        H.N ≤ C ^ 2 * (b - a) := by
  classical
  set F : ℕ → ℝ := fun k =>
    min b (max a (H.partition ⟨min k H.N, Nat.lt_succ_of_le (min_le_right _ _)⟩)) with hFdef
  have hFmono : ∀ k, F k ≤ F (k + 1) := by
    intro k
    refine min_le_min le_rfl (max_le_max le_rfl (H.partition_strictMono.monotone ?_))
    rw [Fin.le_def]
    simp only
    omega
  have hFval : ∀ (j : ℕ) (hj : j < H.N),
      F j = min b (max a (H.partition (⟨j, hj⟩ : Fin H.N).castSucc))
        ∧ F (j + 1) = min b (max a (H.partition (⟨j, hj⟩ : Fin H.N).succ)) := by
    intro j hj
    have hidx0 : (⟨min j H.N, Nat.lt_succ_of_le (min_le_right j H.N)⟩ : Fin (H.N + 1))
        = (⟨j, hj⟩ : Fin H.N).castSucc := by
      apply Fin.ext
      show min j H.N = j
      omega
    have hidx1 : (⟨min (j + 1) H.N, Nat.lt_succ_of_le (min_le_right (j + 1) H.N)⟩
          : Fin (H.N + 1)) = (⟨j, hj⟩ : Fin H.N).succ := by
      apply Fin.ext
      show min (j + 1) H.N = j + 1
      omega
    refine ⟨?_, ?_⟩
    · simp only [hFdef]
      rw [hidx0]
    · simp only [hFdef]
      rw [hidx1]
  have hstep : ∀ j ∈ Finset.range H.N,
      (if h : j < H.N then
        (if a ≤ H.partition (⟨j, h⟩ : Fin H.N).castSucc
            ∧ H.partition (⟨j, h⟩ : Fin H.N).succ ≤ b then C else 0) ^ 2
          * (H.partition (⟨j, h⟩ : Fin H.N).succ - H.partition (⟨j, h⟩ : Fin H.N).castSucc)
        else 0) ≤ C ^ 2 * (F (j + 1) - F j) := by
    intro j hj
    rw [Finset.mem_range] at hj
    rw [dif_pos hj]
    obtain ⟨hFj, hFj1⟩ := hFval j hj
    have hmono := H.partition_strictMono (Fin.castSucc_lt_succ (i := (⟨j, hj⟩ : Fin H.N)))
    by_cases hin : a ≤ H.partition (⟨j, hj⟩ : Fin H.N).castSucc
        ∧ H.partition (⟨j, hj⟩ : Fin H.N).succ ≤ b
    · rw [if_pos hin, hFj, hFj1,
        max_eq_right hin.1, max_eq_right (le_trans hin.1 hmono.le),
        min_eq_right (le_trans hmono.le hin.2), min_eq_right hin.2]
    · rw [if_neg hin]
      have : F j ≤ F (j + 1) := hFmono j
      nlinarith [sq_nonneg C]
  calc H.varClock
        (fun j => if a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b then C else 0) H.N
      ≤ ∑ j ∈ Finset.range H.N, C ^ 2 * (F (j + 1) - F j) := Finset.sum_le_sum hstep
    _ = C ^ 2 * (F H.N - F 0) := by rw [← Finset.mul_sum, Finset.sum_range_sub]
    _ ≤ C ^ 2 * (b - a) := by
        have hup : F H.N ≤ b := min_le_left _ _
        have hlow : a ≤ F 0 := le_min hab (le_max_left _ _)
        nlinarith [sq_nonneg C]


/-- The simple integrand `1_{(a, b]}` for `0 ≤ a < b`. -/
noncomputable def stepIocGen (Ω) [MeasurableSpace Ω] {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    SimplePredictable Ω b :=
  if h : 0 < a then stepIoc Ω h hab else stepIoc₀ Ω (lt_of_le_of_lt ha hab)

@[simp] theorem stepIocGen_eval {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (s : ℝ) (ω : Ω) :
    (stepIocGen Ω ha hab).eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dif_pos h, stepIoc_eval]
  · rw [dif_neg h]
    have ha0 : a = 0 := le_antisymm (not_lt.mp h) ha
    subst ha0
    exact stepIoc₀_eval _ s ω

theorem stepIocGen_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a < b) :
    ∀ i : Fin (stepIocGen Ω ha hab).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((stepIocGen Ω ha hab).partition i.castSucc)) ((stepIocGen Ω ha hab).ξ i) := by
  unfold stepIocGen
  by_cases h : 0 < a
  · rw [dif_pos h]; exact stepIoc_adapt ℱ h hab
  · rw [dif_neg h]; exact stepIoc₀_adapt ℱ _

/-- A simple integrand whose coefficients vanish on every tile not contained in `(a, b]` has the
same elementary integral at every time past `b`. -/
theorem SimplePredictable.simpleIntegral_eq_of_support
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    {T : ℝ} (H : SimplePredictable Ω T) {a b : ℝ}
    (hz : ∀ (j : Fin H.N) (ω : Ω),
      ¬(a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b) → H.ξ j ω = 0)
    {t : ℝ} (hbt : b ≤ t) (ω : Ω) : simpleIntegral W H t ω = simpleIntegral W H T ω := by
  rw [simpleIntegral_eq_sum]
  unfold simpleIntegral
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : a ≤ H.partition j.castSucc ∧ H.partition j.succ ≤ b
  · have h1 : H.partition j.succ ≤ t := hj.2.trans hbt
    have h2 : H.partition j.castSucc ≤ t :=
      ((H.partition_strictMono Fin.castSucc_lt_succ).le).trans h1
    rw [min_eq_left h1, min_eq_left h2]
  · rw [hz j ω hj, zero_mul, zero_mul]


/-- **Restriction of a simple integrand to `(a, b]`.** Multiplying an adapted simple integrand
by `1_{(a, b]}` on their common refinement gives an adapted simple integrand whose evaluation is
the restricted evaluation and whose coefficients vanish on every tile not contained in `(a, b]`
and are bounded by `C` on the others. -/
theorem SimplePredictable.exists_restrict_Ioc
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω)
      ∧ (∀ (j : Fin Q.N) (ω : Ω), |Q.ξ j ω|
          ≤ if a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b then C else 0) := by
  classical
  obtain ⟨T₃, Q, hQadapt, hQeval, -⟩ :=
    SimplePredictable.exists_mul_simple W ℱ G (stepIocGen Ω ha hab) h_adapt
      (stepIocGen_adapt ℱ ha hab)
  have hQeval' : ∀ s ω, Q.eval s ω
      = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω := by
    intro s ω
    rw [hQeval s ω, stepIocGen_eval ha hab, mul_comm]
  refine ⟨T₃, Q, hQadapt, hQeval', fun j ω => ?_⟩
  have hlt : Q.partition j.castSucc < Q.partition j.succ :=
    Q.partition_strictMono Fin.castSucc_lt_succ
  by_cases hin : a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b
  · rw [if_pos hin]
    have hs : Q.partition j.castSucc < Q.partition j.succ
        ∧ Q.partition j.succ ≤ Q.partition j.succ := ⟨hlt, le_rfl⟩
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' _ ω, abs_mul]
    have h1 : |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)| ≤ 1 := by
      by_cases hm : Q.partition j.succ ∈ Set.Ioc a b
      · rw [Set.indicator_of_mem hm]; norm_num
      · rw [Set.indicator_of_notMem hm]; norm_num
    calc |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) (Q.partition j.succ)|
          * |G.eval (Q.partition j.succ) ω|
        ≤ 1 * C := by
          exact mul_le_mul h1 (G.abs_eval_le hC0 hC _ ω) (abs_nonneg _) zero_le_one
      _ = C := one_mul C
  · rw [if_neg hin]
    -- pick a time in the tile that lies outside `(a, b]`
    obtain ⟨s, hs, hsout⟩ : ∃ s : ℝ, (Q.partition j.castSucc < s ∧ s ≤ Q.partition j.succ)
        ∧ s ∉ Set.Ioc a b := by
      by_cases hb : Q.partition j.succ ≤ b
      · have hna : Q.partition j.castSucc < a := by
          by_contra hcon
          exact hin ⟨not_lt.mp hcon, hb⟩
        refine ⟨min a (Q.partition j.succ), ⟨lt_min hna hlt, min_le_right _ _⟩, ?_⟩
        exact fun hm => absurd (Set.mem_Ioc.mp hm).1 (not_lt.mpr (min_le_left _ _))
      · refine ⟨Q.partition j.succ, ⟨hlt, le_rfl⟩, ?_⟩
        exact fun hm => hb (Set.mem_Ioc.mp hm).2
    rw [← Q.eval_of_mem_Ioc j hs ω, hQeval' s ω, Set.indicator_of_notMem hsout, zero_mul,
      abs_zero]


section IncrementBound

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

/-- A process depending only on time is progressively measurable as soon as it is Borel. -/
theorem progressivelyMeasurable_of_time {g : ℝ → ℝ} (hg : Measurable g) :
    Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) s => g s) := by
  intro t
  have h : Measurable[@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance]
      (fun p : Ω × ℝ => (Set.Iic t).indicator g p.2) :=
    (hg.indicator measurableSet_Iic).comp measurable_snd
  exact h.stronglyMeasurable

include hℱ in
/-- **Fourth-moment bound for the `L²` Itô integral of an integrand supported in `(a, b]`.**
The bound sees only the length of the support. -/
theorem lintegral_stochasticIntegralBrownian_pow_four_le_Ioc
    (F : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry F))
    (hp : Probability.ProgressivelyMeasurable ℱ F)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCF : ∀ ω s, |F ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hsupp : ∀ ω s, s ∉ Set.Ioc a b → F ω s = 0) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  choose G0 hG0adapt hG0within using fun n : ℕ =>
    exists_adaptedSimple_within ℱ F hm hp hb (hq b hb)
      (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ from ENNReal.inv_pos.mpr
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  have hGadapt : ∀ n, ∀ i : Fin ((G0 n).truncate C).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (((G0 n).truncate C).partition i.castSucc)) (((G0 n).truncate C).ξ i) :=
    fun n => SimplePredictable.truncate_adapt ℱ (G0 n) C (hG0adapt n)
  have hGbdd : ∀ n, ∀ (i : Fin ((G0 n).truncate C).N) (ω : Ω),
      |((G0 n).truncate C).ξ i ω| ≤ C := fun n i ω => (G0 n).abs_truncate_xi_le hC0 i ω
  choose T3 Q hQadapt hQeval hQxi using fun n : ℕ =>
    SimplePredictable.exists_restrict_Ioc W ℱ ((G0 n).truncate C) (hGadapt n) hC0
      (hGbdd n) ha hab
  -- the restricted approximants are bounded by `C` and vanish off `(a, b]`
  have hQC : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω), |(Q n).ξ j ω| ≤ C := by
    intro n j ω
    refine (hQxi n j ω).trans ?_
    by_cases h : a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b
    · rw [if_pos h]
    · rw [if_neg h]; exact hC0
  have hQz : ∀ (n : ℕ) (j : Fin (Q n).N) (ω : Ω),
      ¬(a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b) → (Q n).ξ j ω = 0 := by
    intro n j ω h
    have := (hQxi n j ω).trans (le_of_eq (if_neg h))
    exact abs_nonpos_iff.mp this
  -- their elementary integrals at `b` are the ones the variance budget bounds
  have hQsimp : ∀ (n : ℕ) (ω : Ω),
      simpleIntegral W (Q n) b ω = simpleIntegral W (Q n) (T3 n) ω :=
    fun n ω => (Q n).simpleIntegral_eq_of_support W (hQz n) le_rfl ω
  have hQbound : ∀ n : ℕ, ∫⁻ ω, (‖simpleIntegral W (Q n) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
    intro n
    simp_rw [hQsimp n]
    refine le_trans ((Q n).lintegral_simpleIntegral_pow_four_le_varClock W ℱ hℱ (hQadapt n)
      hC0 (hQC n) (c := fun j => if a ≤ (Q n).partition j.castSucc
        ∧ (Q n).partition j.succ ≤ b then C else 0) (hQxi n)) ?_
    refine ENNReal.ofReal_le_ofReal ?_
    have hV := (Q n).varClock_le_Ioc (a := a) (b := b) (C := C) hab.le
    have hV0 := (Q n).varClock_nonneg
      (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
      (Q n).N
    have hcg : (0 : ℝ) ≤ 6 + gaussianFourthMoment := by
      linarith [gaussianFourthMoment_nonneg]
    have hsq : (Q n).varClock
        (fun j => if a ≤ (Q n).partition j.castSucc ∧ (Q n).partition j.succ ≤ b then C else 0)
        (Q n).N ^ 2 ≤ (C ^ 2 * (b - a)) ^ 2 := by
      nlinarith [hV, hV0]
    calc (6 + gaussianFourthMoment) * (Q n).varClock
            (fun j => if a ≤ (Q n).partition j.castSucc
              ∧ (Q n).partition j.succ ≤ b then C else 0) (Q n).N ^ 2
        ≤ (6 + gaussianFourthMoment) * (C ^ 2 * (b - a)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq hcg
      _ = (6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2 := by ring
  -- the restricted approximants still approximate `F`
  have hQwithin : ∀ n : ℕ, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) b,
      (‖(Q n).eval s ω - F ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine le_trans ?_ (hG0within n).le
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    have hle : ‖(Q n).eval s ω - F ω s‖₊ ≤ ‖F ω s - (G0 n).eval s ω‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      have hstep : |(Q n).eval s ω - F ω s|
          ≤ |((G0 n).truncate C).eval s ω - F ω s| := by
        rw [hQeval n s ω]
        by_cases hs : s ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem hs]
          simp
        · rw [Set.indicator_of_notMem hs, zero_mul, hsupp ω s hs]
          simp
      refine hstep.trans ?_
      rw [(G0 n).truncate_eval hC0 s ω, abs_sub_comm (F ω s)]
      exact abs_clamp_sub_le hC0 (hCF ω s)
    exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr hle) 2
  have htol : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
    refine h.congr fun n => ?_
    simp [Nat.cast_add_one]
  have hsq : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W (Q n) b ω
        - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htol
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall fun n => ?_)
    rw [isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ (Q n) (hQadapt n) F hm hp hq hb]
    exact hQwithin n
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => simpleIntegral W (Q n) b ω
        - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P) Filter.atTop (nhds 0) := by
    have hrw : ∀ n, MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W (Q n) b ω
          - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω) 2 P
        = (∫⁻ ω, (‖simpleIntegral W (Q n) b ω
            - stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
              ^ ((2 : ℝ))⁻¹ := by
      intro n
      rw [← eLpNorm_two_rpow_eq_lintegral_sq]
      exact (ENNReal.rpow_rpow_inv (by norm_num) _).symm
    simp_rw [hrw]
    have h := (ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0 |>.comp hsq
    simpa [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < ((2 : ℝ))⁻¹)] using h
  have hmeasG : ∀ n, Measurable (fun ω => simpleIntegral W (Q n) b ω) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      ((Q n).ξ_measurable i).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  have hmeasSI : Measurable (stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ F hm hp hq b).mono (ℱ.le b)).measurable
  have hTIM : MeasureTheory.TendstoInMeasure P
      (fun n ω => simpleIntegral W (Q n) b ω) Filter.atTop
      (stochasticIntegralBrownian W ℱ hℱ F hm hp hq b) :=
    MeasureTheory.tendstoInMeasure_of_tendsto_eLpNorm (by norm_num)
      (fun n => (hmeasG n).aestronglyMeasurable) hmeasSI.aestronglyMeasurable heL
  obtain ⟨ns, -, hns_ae⟩ := hTIM.exists_seq_tendsto_ae
  have hcont : Continuous fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4 := by
    have hfun : (fun x : ℝ => (‖x‖₊ : ℝ≥0∞) ^ 4)
        = fun x : ℝ => ((‖x‖₊ ^ 4 : ℝ≥0) : ℝ≥0∞) := by
      funext x; rw [ENNReal.coe_pow]
    rw [hfun]
    exact ENNReal.continuous_coe.comp (continuous_nnnorm.pow 4)
  have hfatou : ∫⁻ ω,
      (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ Filter.liminf (fun k => ∫⁻ ω,
        (‖simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4 ∂P) Filter.atTop := by
    have h1 : ∀ᵐ ω ∂P,
        (‖stochasticIntegralBrownian W ℱ hℱ F hm hp hq b ω‖₊ : ℝ≥0∞) ^ 4
        = Filter.liminf (fun k =>
            (‖simpleIntegral W (Q (ns k)) b ω‖₊ : ℝ≥0∞) ^ 4) Filter.atTop := by
      filter_upwards [hns_ae] with ω hω
      exact ((hcont.tendsto _).comp hω).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    exact lintegral_liminf_le fun k => (hcont.measurable.comp (hmeasG (ns k)))
  exact hfatou.trans (Filter.liminf_le_of_frequently_le
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => hQbound (ns k))))

include hℱ in
/-- **Fourth moment of an increment of the `L²` Itô integral.** For an integrand bounded by `C`,

  `𝔼|∫_a^b H dW|⁴ ≤ (6 + c)·C⁴·(b − a)²`,

with `c` the fourth moment of the standard Gaussian. -/
theorem lintegral_stochasticIntegralBrownian_sub_pow_four_le
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * (b - a) ^ 2) := by
  classical
  have hb : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have hindm : Measurable ((Set.Ioc a b).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator measurableSet_Ioc
  have hFle : ∀ (ω : Ω) (s : ℝ),
      |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ |H ω s| := by
    intro ω s
    by_cases hs : s ∈ Set.Ioc a b
    · rw [Set.indicator_of_mem hs, one_mul]
    · rw [Set.indicator_of_notMem hs, zero_mul, abs_zero]
      exact abs_nonneg _
  have hmF : Measurable (Function.uncurry fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s) :=
    (hindm.comp measurable_snd).mul hm
  have hpF : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s :=
    (progressivelyMeasurable_of_time ℱ hindm).mul hp
  have hqF : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      < ⊤ := by
    intro T hT
    refine lt_of_le_of_lt ?_ (hq T hT)
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    refine pow_le_pow_left' (ENNReal.coe_le_coe.mpr ?_) 2
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using hFle ω s
  have hCF : ∀ (ω : Ω) (s : ℝ),
      |(Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s| ≤ C :=
    fun ω s => (hFle ω s).trans (hCH ω s)
  have hsupp : ∀ (ω : Ω) (s : ℝ), s ∉ Set.Ioc a b →
      (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s = 0 := by
    intro ω s hs
    rw [Set.indicator_of_notMem hs, zero_mul]
  have hloc := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ H hm hp hq ha hab hmF hpF hqF hb
  rw [min_self, min_eq_left hab.le] at hloc
  have hcongr : ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq b ω
      - stochasticIntegralBrownian W ℱ hℱ H hm hp hq a ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * H ω s)
          hmF hpF hqF b ω‖₊ : ℝ≥0∞) ^ 4 ∂P := by
    refine lintegral_congr_ae ?_
    filter_upwards [hloc] with ω hω
    rw [hω]
  rw [hcongr]
  exact lintegral_stochasticIntegralBrownian_pow_four_le_Ioc W ℱ hℱ _ hmF hpF hqF hC0 hCF
    ha hab hsupp

end IncrementBound

end LevyStochCalc.Brownian.Ito
