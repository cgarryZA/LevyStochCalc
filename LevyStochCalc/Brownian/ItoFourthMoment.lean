/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoAlgebra

/-!
# Fourth moment of the elementary Brownian integral

The moments of a Brownian increment, and the fourth-moment bound they give for the elementary
integral of a uniformly bounded simple integrand. The bound comes from a recursion over the
partial sums: the odd-power cross terms drop out because a coefficient measurable before an
increment is independent of it, and the surviving terms are controlled by the second moment of
the partial sums, itself bounded by the same recursion.

## Main statements

* `integral_pow_gaussianReal_zero` — the moments of a centred real Gaussian scale with the
  standard deviation.
* `integral_pow_gaussianReal_odd` — the odd moments of the standard real Gaussian vanish.
* `integral_increment_sq`, `integral_increment_pow_four` — the second and fourth moments of a
  Brownian increment.
* `integral_mul_increment_pow` — a random variable measurable before `a` factors out of the
  integral against a power of the increment over `(a, b]`.
* `memLp_increment`, `memLp_mul_increment` — a Brownian increment, and a bounded random
  variable times one, have moments of every order.
* `SimplePredictable.partialSum` — the partial sums of the elementary integral.
* `SimplePredictable.integral_partialSum_sq_le`,
  `SimplePredictable.integral_partialSum_pow_four_le` — the second and fourth moments of the
  partial sums.
* `SimplePredictable.integral_simpleIntegral_pow_four_le_horizon` —
  `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·C⁴·T²` for a simple integrand bounded by `C`, where `c` is the
  fourth moment of the standard Gaussian.
* `SimplePredictable.varClock` — the variance budget `∑_{j<k} c_j² (τ_{j+1} − τ_j)` of a
  per-tile coefficient bound `c`, with
  `SimplePredictable.integral_simpleIntegral_pow_four_le_varClock`:
  `𝔼|∫_0^T H dW|⁴ ≤ (6 + c)·(∑_j c_j² Δ_j)²`, which for a coefficient vanishing off a
  subinterval sees only that subinterval's length.
* `SimplePredictable.truncate` — the coefficients of a simple integrand clamped to `[-C, C]`,
  with `abs_clamp_sub_le`: clamping moves a value no further from a target already in `[-C, C]`,
  so a truncated approximant is still an approximant.
* `lintegral_stochasticIntegralBrownian_pow_four_le` — the same bound for the `L²` Itô integral
  of any integrand bounded by `C`, by Fatou along an almost-everywhere convergent subsequence of
  truncated simple approximants.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u
variable {Ω : Type u} [MeasurableSpace Ω]

/-- The fourth moment of the standard real Gaussian distribution. -/
noncomputable def gaussianFourthMoment : ℝ :=
  ∫ x : ℝ, x ^ 4 ∂(gaussianReal 0 1)

theorem gaussianFourthMoment_nonneg : 0 ≤ gaussianFourthMoment :=
  integral_nonneg fun x => by positivity

/-- Every power of the identity is integrable for a real Gaussian distribution. -/
theorem integrable_pow_gaussianReal (m : ℕ) (hm : m ≠ 0) (μ' : ℝ) (v : ℝ≥0) :
    Integrable (fun x : ℝ => x ^ m) (gaussianReal μ' v) := by
  have h : MemLp (id : ℝ → ℝ) (m : ℝ≥0∞) (gaussianReal μ' v) :=
    memLp_id_gaussianReal' _ (by simp)
  refine (h.integrable_norm_pow hm).mono (by fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  simp

/-- Powers of a centred real Gaussian scale with the standard deviation. -/
theorem integral_pow_gaussianReal_zero (v : ℝ≥0) (m : ℕ) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 v)
      = Real.sqrt v ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hsq : NNReal.mk (Real.sqrt v ^ 2) (sq_nonneg _) * 1 = v := by
    rw [mul_one]
    exact NNReal.eq (by simp [Real.sq_sqrt v.coe_nonneg])
  have hmap : (gaussianReal 0 1).map (fun x : ℝ => Real.sqrt v * x) = gaussianReal 0 v := by
    have h := gaussianReal_map_const_mul (μ := (0 : ℝ)) (v := 1) (Real.sqrt v)
    rw [mul_zero, hsq] at h
    exact h
  conv_lhs => rw [← hmap]
  rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [mul_pow]
  rw [integral_const_mul]

/-- The odd moments of the standard real Gaussian vanish. -/
theorem integral_pow_gaussianReal_odd (m : ℕ) (hm : Odd m) :
    ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) = 0 := by
  have hmap : (gaussianReal (0 : ℝ) 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
    simpa using gaussianReal_map_neg (μ := (0 : ℝ)) (v := 1)
  have h1 : ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1)
      = ∫ x : ℝ, (-x) ^ m ∂(gaussianReal 0 1) := by
    conv_lhs => rw [← hmap]
    rw [integral_map (by fun_prop) (by fun_prop)]
  simp_rw [hm.neg_pow] at h1
  rw [integral_neg] at h1
  linarith

section Increments

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

/-- The moments of a Brownian increment scale with the square root of its length. -/
theorem integral_increment_pow {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (m : ℕ) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P
      = Real.sqrt (b - a) ^ m * ∫ x : ℝ, x ^ m ∂(gaussianReal 0 1) := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  rw [← integral_map hmeas.aemeasurable
      (f := fun x : ℝ => x ^ m) (by fun_prop),
    W.increment_gaussian ha hab, integral_pow_gaussianReal_zero]
  rfl

/-- Odd moments of a Brownian increment vanish. -/
theorem integral_increment_pow_odd {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {m : ℕ} (hm : Odd m) :
    ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P = 0 := by
  rw [integral_increment_pow W ha hab m, integral_pow_gaussianReal_odd m hm, mul_zero]

/-- The second moment of a Brownian increment is its length. -/
theorem integral_increment_sq {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 2 ∂P = b - a := by
  rw [integral_increment_pow W ha hab 2,
    LevyStochCalc.Brownian.Martingale.gaussianReal_second_moment 1]
  rw [Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]
  norm_num

/-- The fourth moment of a Brownian increment is the square of its length, up to the fourth
moment of the standard Gaussian. -/
theorem integral_increment_pow_four {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∫ ω, (W.W b ω - W.W a ω) ^ 4 ∂P = (b - a) ^ 2 * gaussianFourthMoment := by
  rw [integral_increment_pow W ha hab 4]
  congr 1
  rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ b - a)]

/-- A random variable measurable before `a` is independent of every power of the increment
over `(a, b]`. -/
theorem integral_mul_increment_pow (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {Y : Ω → ℝ}
    (hY : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Y) (hYm : Measurable Y) (m : ℕ) :
    ∫ ω, Y ω * (W.W b ω - W.W a ω) ^ m ∂P
      = (∫ ω, Y ω ∂P) * ∫ ω, (W.W b ω - W.W a ω) ^ m ∂P := by
  have hΔ : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hindepσ := hℱ.indep ha hab
  have hYcomap : MeasurableSpace.comap Y inferInstance ≤ ℱ a := hY.measurable.comap_le
  have hIF : ProbabilityTheory.IndepFun Y (fun ω => W.W b ω - W.W a ω) P := by
    rw [ProbabilityTheory.IndepFun_iff]
    intro u v hu hv
    rw [ProbabilityTheory.Indep_iff] at hindepσ
    exact hindepσ u v (hYcomap u hu) hv
  have hIF' : ProbabilityTheory.IndepFun Y (fun ω => (W.W b ω - W.W a ω) ^ m) P :=
    hIF.comp measurable_id (measurable_id.pow_const m)
  exact hIF'.integral_mul_eq_mul_integral hYm.aestronglyMeasurable
    (hΔ.pow_const m).aestronglyMeasurable

/-- A Brownian increment has moments of every order. -/
theorem memLp_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤) :
    MemLp (fun ω => W.W b ω - W.W a ω) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have h := (memLp_map_measure_iff (g := (id : ℝ → ℝ)) (μ := P)
    (f := fun ω => W.W b ω - W.W a ω) (p := p)
    (by fun_prop) hmeas.aemeasurable).1
  rw [W.increment_gaussian ha hab] at h
  exact h (memLp_id_gaussianReal' p hp)

/-- A bounded random variable times a Brownian increment has moments of every order. -/
theorem memLp_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (p : ℝ≥0∞) (hp : p ≠ ⊤)
    {Y : Ω → ℝ} (hYm : Measurable Y) {C : ℝ} (hC : ∀ ω, |Y ω| ≤ C) :
    MemLp (fun ω => Y ω * (W.W b ω - W.W a ω)) p P := by
  have hmeas : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  refine MemLp.mono ((memLp_increment W ha hab p hp).const_mul C)
    (hYm.mul hmeas).aestronglyMeasurable (Filter.Eventually.of_forall fun ω => ?_)
  have hC0 : 0 ≤ C := (abs_nonneg (Y ω)).trans (hC ω)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
  exact mul_le_mul_of_nonneg_right (hC ω) (abs_nonneg _)

end Increments

namespace SimplePredictable

variable {T : ℝ} (G : SimplePredictable Ω T)
  {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)

/-- The `i`-th summand of the elementary integral, indexed by a natural number. -/
noncomputable def term (i : ℕ) (ω : Ω) : ℝ :=
  if h : i < G.N then
    G.ξ ⟨i, h⟩ ω * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
      - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω)
  else 0

/-- The partial sums of the elementary integral. -/
noncomputable def partialSum (k : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range k, G.term W i ω

theorem partialSum_zero (ω : Ω) : G.partialSum W 0 ω = 0 := by simp [partialSum]

theorem partialSum_succ (k : ℕ) (ω : Ω) :
    G.partialSum W (k + 1) ω = G.partialSum W k ω + G.term W k ω :=
  Finset.sum_range_succ _ _

theorem measurable_term (i : ℕ) : Measurable (G.term W i) := by
  unfold term
  split_ifs with h
  · exact (G.ξ_measurable _).mul ((W.measurable_eval _).sub (W.measurable_eval _))
  · exact measurable_const

theorem measurable_partialSum (k : ℕ) : Measurable (G.partialSum W k) :=
  Finset.measurable_sum _ fun i _ => G.measurable_term W i

theorem partialSum_card (ω : Ω) : G.partialSum W G.N ω = simpleIntegral W G T ω := by
  rw [simpleIntegral_eq_sum, partialSum, ← Fin.sum_univ_eq_sum_range
    (fun i => G.term W i ω) G.N]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [term, dif_pos i.isLt]

omit [MeasurableSpace Ω] in
/-- A finite sum of processes measurable for a sub-σ-algebra is measurable for it. -/
private theorem stronglyMeasurable_range_sum {m : MeasurableSpace Ω} {n : ℕ} {f : ℕ → Ω → ℝ}
    (h : ∀ i ∈ Finset.range n, @MeasureTheory.StronglyMeasurable Ω ℝ _ m (f i)) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ m (fun ω => ∑ i ∈ Finset.range n, f i ω) :=
  @Finset.stronglyMeasurable_fun_sum Ω ℝ _ _ _ m _ _ _ h

omit [IsProbabilityMeasure P] in
/-- A real random variable in `Lᵐ` has an integrable `m`-th power. -/
private theorem integrable_pow_of_memLp {f : Ω → ℝ} {m : ℕ} (hm : m ≠ 0)
    {p : ℝ≥0∞} (hp : p = (m : ℝ≥0∞)) (h : MemLp f p P) : Integrable (fun ω => f ω ^ m) P := by
  subst hp
  refine (h.integrable_norm_pow hm).mono ((continuous_pow m).comp_aestronglyMeasurable h.1)
    (Filter.Eventually.of_forall fun ω => ?_)
  simp

theorem memLp_term {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (i : ℕ) : MemLp (G.term W i) p P := by
  by_cases h : i < G.N
  · have hterm : G.term W i = fun ω => G.ξ ⟨i, h⟩ ω
        * (W.W (G.partition (⟨i, h⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨i, h⟩ : Fin G.N).castSucc) ω) := by
      funext ω; rw [term, dif_pos h]
    rw [hterm]
    exact memLp_mul_increment W (G.partition_nonneg _)
      (G.partition_strictMono Fin.castSucc_lt_succ) p hp (G.ξ_measurable _) (hC ⟨i, h⟩)
  · have hterm : G.term W i = fun _ => (0 : ℝ) := by funext ω; rw [term, dif_neg h]
    rw [hterm]; exact memLp_const 0

theorem memLp_partialSum {C : ℝ} (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    (p : ℝ≥0∞) (hp : p ≠ ⊤) (k : ℕ) : MemLp (G.partialSum W k) p P :=
  memLp_finsetSum _ fun i _ => G.memLp_term W hC p hp i

theorem stronglyMeasurable_partialSum (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : IsBrownianFiltration W ℱ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {k : ℕ} (hk : k ≤ G.N) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition ⟨k, by omega⟩)) (G.partialSum W k) := by
  refine stronglyMeasurable_range_sum fun i hi => ?_
  rw [Finset.mem_range] at hi
  have hiN : i < G.N := lt_of_lt_of_le hi hk
  have hterm : G.term W i = fun ω => G.ξ ⟨i, hiN⟩ ω
      * (W.W (G.partition (⟨i, hiN⟩ : Fin G.N).succ) ω
        - W.W (G.partition (⟨i, hiN⟩ : Fin G.N).castSucc) ω) := by
    funext ω; rw [term, dif_pos hiN]
  rw [hterm]
  have hle1 : G.partition (⟨i, hiN⟩ : Fin G.N).castSucc
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.castSucc]; omega)
  have hle2 : G.partition (⟨i, hiN⟩ : Fin G.N).succ
      ≤ G.partition (⟨k, by omega⟩ : Fin (G.N + 1)) :=
    G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.succ]; omega)
  exact ((h_adapt ⟨i, hiN⟩).mono (ℱ.mono hle1)).mul
    (((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle2)).sub
      ((hℱ.measurable _).stronglyMeasurable.mono (ℱ.mono hle1)))

/-- The variance budget of the first `k` tiles for a per-tile coefficient bound `c`:
`∑_{j < k} c_j² (τ_{j+1} − τ_j)`. -/
noncomputable def varClock (c : Fin G.N → ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, if h : j < G.N then
    c ⟨j, h⟩ ^ 2 * (G.partition (⟨j, h⟩ : Fin G.N).succ
      - G.partition (⟨j, h⟩ : Fin G.N).castSucc) else 0

theorem varClock_zero (c : Fin G.N → ℝ) : G.varClock c 0 = 0 := by simp [varClock]

theorem varClock_succ (c : Fin G.N → ℝ) {k : ℕ} (hk : k < G.N) :
    G.varClock c (k + 1) = G.varClock c k
      + c ⟨k, hk⟩ ^ 2 * (G.partition (⟨k, hk⟩ : Fin G.N).succ
        - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  unfold varClock
  rw [Finset.sum_range_succ, dif_pos hk]

theorem varClock_nonneg (c : Fin G.N → ℝ) (k : ℕ) : 0 ≤ G.varClock c k := by
  unfold varClock
  refine Finset.sum_nonneg fun j _ => ?_
  by_cases h : j < G.N
  · rw [dif_pos h]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg h]

theorem varClock_mono (c : Fin G.N → ℝ) {k l : ℕ} (h : k ≤ l) :
    G.varClock c k ≤ G.varClock c l := by
  unfold varClock
  have hsub : Finset.range k ⊆ Finset.range l := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun j _ _ => ?_
  by_cases hj : j < G.N
  · rw [dif_pos hj]
    exact mul_nonneg (sq_nonneg _)
      (sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le)
  · rw [dif_neg hj]

section Moments

/-- One step of a second-moment recursion. -/
private theorem integral_add_mul_increment_sq
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS2 : MemLp S 2 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2 ∂P
      = (∫ ω, S ω ^ 2 ∂P) + (∫ ω, ξ ω ^ 2 ∂P) * (b - a) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD2 : MemLp (fun ω => W.W b ω - W.W a ω) 2 P := memLp_increment W ha hab 2 (by simp)
  have hSD : Integrable (fun ω => |S ω| * |W.W b ω - W.W a ω|) P := by
    have h := (hS2.abs).integrable_mul (hD2.abs)
    exact h
  have hD2int : Integrable (fun ω => (W.W b ω - W.W a ω) ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hD2
  have hi1 : Integrable (fun ω => S ω ^ 2) P :=
    integrable_pow_of_memLp (m := 2) (by norm_num) (by simp) hS2
  have hi2 : Integrable (fun ω => (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine (hSD.const_mul (2 * C)).mono
      (((measurable_const.mul (hSm.mul hξm)).mul (hDm.pow_const 1)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    have h2 := abs_nonneg (S ω)
    have h3 := abs_nonneg (W.W b ω - W.W a ω)
    rw [pow_one, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * C * (|S ω| * |W.W b ω - W.W a ω|))]
    have h4 : |(2 : ℝ)| = 2 := by norm_num
    rw [h4]
    nlinarith [mul_nonneg (mul_nonneg h2 h3) (sub_nonneg.mpr h1)]
  have hi3 : Integrable (fun ω => ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2) P := by
    refine (hD2int.const_mul (C ^ 2)).mono
      (((hξm.pow_const 2).mul (hDm.pow_const 2)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    have h1 := hCξ ω
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2 * (W.W b ω - W.W a ω) ^ 2)]
    have h2 : |W.W b ω - W.W a ω| ^ 2 = (W.W b ω - W.W a ω) ^ 2 := by
      rw [← abs_pow, abs_of_nonneg (sq_nonneg _)]
    rw [h2]
    nlinarith [sq_nonneg (W.W b ω - W.W a ω),
      mul_le_mul h1 h1 (abs_nonneg (ξ ω)) hC0]
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 2
      = S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + ξ ω ^ 2 * (W.W b ω - W.W a ω) ^ 2 := fun ω => by ring
  have hξ2ad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 2) := by
    have hfun : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; rw [pow_two]; rfl
    rw [hfun]; exact hξad.mul hξad
  have hi12 : Integrable
      (fun ω => S ω ^ 2 + (2 * (S ω * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  simp_rw [hexp]
  rw [integral_add hi12 hi3, integral_add hi1 hi2,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 2 * (S ω * ξ ω))
      (MeasureTheory.stronglyMeasurable_const.mul (hSad.mul hξad))
      (measurable_const.mul (hSm.mul hξm)) 1,
    integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 2)
      hξ2ad (hξm.pow_const 2) 2,
    integral_increment_sq W ha hab]

/-- One step of a fourth-moment recursion. -/
private theorem integral_add_mul_increment_pow_four
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {S ξ : Ω → ℝ}
    (hS4 : MemLp S 4 P) (hSm : Measurable S)
    (hSad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) S)
    (hξm : Measurable ξ) (hξad : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) ξ)
    {C : ℝ} (hC0 : 0 ≤ C) (hCξ : ∀ ω, |ξ ω| ≤ C) :
    ∫ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4 ∂P
      = (∫ ω, S ω ^ 4 ∂P)
        + 6 * ((∫ ω, S ω ^ 2 * ξ ω ^ 2 ∂P) * (b - a))
        + (∫ ω, ξ ω ^ 4 ∂P) * ((b - a) ^ 2 * gaussianFourthMoment) := by
  have hDm : Measurable (fun ω => W.W b ω - W.W a ω) :=
    (W.measurable_eval b).sub (W.measurable_eval a)
  have hD4 : MemLp (fun ω => W.W b ω - W.W a ω) 4 P := memLp_increment W ha hab 4 (by simp)
  have hU4 : Integrable
      (fun ω => (|S ω| + |W.W b ω - W.W a ω|) ^ 4) P :=
    integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) (hS4.abs.add hD4.abs)
  have hpow : ∀ (i j : ℕ), i + j = 4 → ∀ ω,
      |S ω| ^ i * |W.W b ω - W.W a ω| ^ j ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by
    intro i j hij ω
    have hx : |S ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (W.W b ω - W.W a ω)]
    have hy : |W.W b ω - W.W a ω| ≤ |S ω| + |W.W b ω - W.W a ω| := by
      linarith [abs_nonneg (S ω)]
    calc |S ω| ^ i * |W.W b ω - W.W a ω| ^ j
        ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ i * (|S ω| + |W.W b ω - W.W a ω|) ^ j :=
          mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hx i)
            (pow_le_pow_left₀ (abs_nonneg _) hy j) (by positivity) (by positivity)
      _ = (|S ω| + |W.W b ω - W.W a ω|) ^ 4 := by rw [← pow_add, hij]
  have key : ∀ (K : ℝ), 0 ≤ K → ∀ (A : Ω → ℝ), Measurable A → ∀ (i j : ℕ), i + j = 4 →
      (∀ ω, |A ω| ≤ K * |S ω| ^ i) →
      Integrable (fun ω => A ω * (W.W b ω - W.W a ω) ^ j) P := by
    intro K hK A hAm i j hij hA
    refine (hU4.const_mul K).mono ((hAm.mul (hDm.pow_const j)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow, abs_mul, abs_of_nonneg hK,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (|S ω| + |W.W b ω - W.W a ω|) ^ 4)]
    calc |A ω| * |W.W b ω - W.W a ω| ^ j
        ≤ (K * |S ω| ^ i) * |W.W b ω - W.W a ω| ^ j :=
          mul_le_mul_of_nonneg_right (hA ω) (by positivity)
      _ = K * (|S ω| ^ i * |W.W b ω - W.W a ω| ^ j) := by ring
      _ ≤ K * (|S ω| + |W.W b ω - W.W a ω|) ^ 4 :=
          mul_le_mul_of_nonneg_left (hpow i j hij ω) hK
  have hi1 : Integrable (fun ω => S ω ^ 4) P :=
    integrable_pow_of_memLp (m := 4) (by norm_num) (by simp) hS4
  have hi2 : Integrable
      (fun ω => (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := by
    refine key (4 * C) (by positivity) (fun ω => 4 * (S ω ^ 3 * ξ ω))
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 3 1 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num]
    have := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 3, abs_nonneg (ξ ω)]
  have hi3 : Integrable
      (fun ω => (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := by
    refine key (6 * C ^ 2) (by positivity) (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2))
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2 2 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, abs_pow, show |(6 : ℝ)| = 6 from by norm_num]
    have h := hCξ ω
    nlinarith [pow_nonneg (abs_nonneg (S ω)) 2, abs_nonneg (ξ ω),
      mul_le_mul h h (abs_nonneg (ξ ω)) hC0]
  have hi4 : Integrable
      (fun ω => (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := by
    refine key (4 * C ^ 3) (by positivity) (fun ω => 4 * (S ω * ξ ω ^ 3))
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 1 3 rfl fun ω => ?_
    rw [abs_mul, abs_mul, abs_pow, show |(4 : ℝ)| = 4 from by norm_num, pow_one]
    have h3 : |ξ ω| ^ 3 ≤ C ^ 3 := pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 3
    nlinarith [mul_nonneg (abs_nonneg (S ω)) (sub_nonneg.mpr h3)]
  have hi5 : Integrable (fun ω => ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4) P := by
    refine key (C ^ 4) (by positivity) (fun ω => ξ ω ^ 4) (hξm.pow_const 4) 0 4 rfl fun ω => ?_
    rw [abs_pow, pow_zero, mul_one]
    exact pow_le_pow_left₀ (abs_nonneg _) (hCξ ω) 4
  have hexp : ∀ ω, (S ω + ξ ω * (W.W b ω - W.W a ω)) ^ 4
      = S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3
        + ξ ω ^ 4 * (W.W b ω - W.W a ω) ^ 4 := fun ω => by ring
  have hi12 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1) P := hi1.add hi2
  have hi123 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2) P := hi12.add hi3
  have hi1234 : Integrable
      (fun ω => S ω ^ 4 + (4 * (S ω ^ 3 * ξ ω)) * (W.W b ω - W.W a ω) ^ 1
        + (6 * (S ω ^ 2 * ξ ω ^ 2)) * (W.W b ω - W.W a ω) ^ 2
        + (4 * (S ω * ξ ω ^ 3)) * (W.W b ω - W.W a ω) ^ 3) P := hi123.add hi4
  have hS3ξ : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω ^ 3 * ξ ω)) := by
    have h3 : (fun ω => S ω ^ 3) = S * S * S := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul ((h3 ▸ ((hSad.mul hSad).mul hSad)).mul hξad)
  have hS2ξ2 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) := by
    have h2 : (fun ω => S ω ^ 2) = S * S := by funext ω; simp only [Pi.mul_apply]; ring
    have h2' : (fun ω => ξ ω ^ 2) = ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul
      ((h2 ▸ (hSad.mul hSad)).mul (h2' ▸ (hξad.mul hξad)))
  have hSξ3 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a)
      (fun ω => 4 * (S ω * ξ ω ^ 3)) := by
    have h3 : (fun ω => ξ ω ^ 3) = ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact MeasureTheory.stronglyMeasurable_const.mul (hSad.mul (h3 ▸ ((hξad.mul hξad).mul hξad)))
  have hξ4 : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) (fun ω => ξ ω ^ 4) := by
    have h4 : (fun ω => ξ ω ^ 4) = ξ * ξ * ξ * ξ := by funext ω; simp only [Pi.mul_apply]; ring
    exact h4 ▸ (((hξad.mul hξad).mul hξad).mul hξad)
  simp_rw [hexp]
  rw [integral_add hi1234 hi5, integral_add hi123 hi4, integral_add hi12 hi3,
    integral_add hi1 hi2,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω ^ 3 * ξ ω)) hS3ξ
      (measurable_const.mul ((hSm.pow_const 3).mul hξm)) 1,
    integral_increment_pow_odd W ha hab odd_one, mul_zero, add_zero,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 6 * (S ω ^ 2 * ξ ω ^ 2)) hS2ξ2
      (measurable_const.mul ((hSm.pow_const 2).mul (hξm.pow_const 2))) 2,
    integral_increment_sq W ha hab,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => 4 * (S ω * ξ ω ^ 3)) hSξ3
      (measurable_const.mul (hSm.mul (hξm.pow_const 3))) 3,
    integral_increment_pow_odd W ha hab (by decide : Odd 3), mul_zero, add_zero,
    integral_mul_increment_pow W ℱ hℱ ha hab (Y := fun ω => ξ ω ^ 4) hξ4
      (hξm.pow_const 4) 4,
    integral_increment_pow_four W ha hab]
  rw [integral_const_mul]
  ring

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
    (ℱ (G.partition i.castSucc)) (G.ξ i))
  {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)

include hℱ h_adapt hC0 hC in
/-- One step of the second-moment recursion for the partial sums. -/
theorem integral_partialSum_sq_succ {k : ℕ} (hk : k < G.N) :
    ∫ ω, (G.partialSum W (k + 1) ω) ^ 2 ∂P
      = (∫ ω, (G.partialSum W k ω) ^ 2 ∂P)
        + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
          * (G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) := by
  have hrw : ∀ ω, G.partialSum W (k + 1) ω
      = G.partialSum W k ω + G.ξ ⟨k, hk⟩ ω
        * (W.W (G.partition (⟨k, hk⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ω) := fun ω => by
    rw [G.partialSum_succ W k ω, term, dif_pos hk]
  simp_rw [hrw]
  exact integral_add_mul_increment_sq W ℱ hℱ (G.partition_nonneg _)
    (G.partition_strictMono Fin.castSucc_lt_succ)
    (G.memLp_partialSum W hC 2 (by simp) k) (G.measurable_partialSum W k)
    (G.stronglyMeasurable_partialSum W ℱ hℱ h_adapt hk.le)
    (G.ξ_measurable _) (h_adapt ⟨k, hk⟩) hC0 (hC ⟨k, hk⟩)

include hℱ h_adapt hC0 hC in
/-- One step of the fourth-moment recursion for the partial sums. -/
theorem integral_partialSum_pow_four_succ {k : ℕ} (hk : k < G.N) :
    ∫ ω, (G.partialSum W (k + 1) ω) ^ 4 ∂P
      = (∫ ω, (G.partialSum W k ω) ^ 4 ∂P)
        + 6 * ((∫ ω, (G.partialSum W k ω) ^ 2 * (G.ξ ⟨k, hk⟩ ω) ^ 2 ∂P)
          * (G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc))
        + (∫ ω, (G.ξ ⟨k, hk⟩ ω) ^ 4 ∂P)
          * ((G.partition (⟨k, hk⟩ : Fin G.N).succ
            - G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ^ 2 * gaussianFourthMoment) := by
  have hrw : ∀ ω, G.partialSum W (k + 1) ω
      = G.partialSum W k ω + G.ξ ⟨k, hk⟩ ω
        * (W.W (G.partition (⟨k, hk⟩ : Fin G.N).succ) ω
          - W.W (G.partition (⟨k, hk⟩ : Fin G.N).castSucc) ω) := fun ω => by
    rw [G.partialSum_succ W k ω, term, dif_pos hk]
  simp_rw [hrw]
  exact integral_add_mul_increment_pow_four W ℱ hℱ (G.partition_nonneg _)
    (G.partition_strictMono Fin.castSucc_lt_succ)
    (G.memLp_partialSum W hC 4 (by simp) k) (G.measurable_partialSum W k)
    (G.stronglyMeasurable_partialSum W ℱ hℱ h_adapt hk.le)
    (G.ξ_measurable _) (h_adapt ⟨k, hk⟩) hC0 (hC ⟨k, hk⟩)

/-- A coefficient bounded by `c` has even moments at most the matching power of `c`. -/
private theorem integral_xi_even_le {c : ℝ} (i : Fin G.N)
    (hci : ∀ ω, |G.ξ i ω| ≤ c) (m : ℕ) :
    ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ c ^ (2 * m) := by
  have hnn : ∀ ω, (0 : ℝ) ≤ (G.ξ i ω) ^ (2 * m) := fun ω => by
    rw [pow_mul]; positivity
  have hcnn : (0 : ℝ) ≤ c ^ (2 * m) := by rw [pow_mul]; positivity
  have hpow : ∀ ω, (G.ξ i ω) ^ (2 * m) ≤ c ^ (2 * m) := fun ω => by
    have h : |G.ξ i ω| ^ (2 * m) ≤ c ^ (2 * m) :=
      pow_le_pow_left₀ (abs_nonneg _) (hci ω) _
    rwa [← abs_pow, abs_of_nonneg (hnn ω)] at h
  have hint : Integrable (fun ω => (G.ξ i ω) ^ (2 * m)) P := by
    refine (integrable_const (c ^ (2 * m))).mono
      ((G.ξ_measurable _).pow_const _).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (hnn ω), abs_of_nonneg hcnn]
    exact hpow ω
  calc ∫ ω, (G.ξ i ω) ^ (2 * m) ∂P ≤ ∫ _ω : Ω, c ^ (2 * m) ∂P :=
        integral_mono hint (integrable_const _) hpow
    _ = c ^ (2 * m) := by simp

include hC0 hC in
/-- A bounded coefficient has second moment at most `C²`. -/
private theorem integral_xi_sq_le (i : Fin G.N) : ∫ ω, (G.ξ i ω) ^ 2 ∂P ≤ C ^ 2 := by
  simpa using G.integral_xi_even_le (P := P) i (hC i) 1

include hC in
/-- A bounded coefficient has fourth moment at most `C⁴`. -/
private theorem integral_xi_pow_four_le (i : Fin G.N) : ∫ ω, (G.ξ i ω) ^ 4 ∂P ≤ C ^ 4 := by
  simpa using G.integral_xi_even_le (P := P) i (hC i) 2

include hℱ h_adapt hC0 hC in
/-- The second moment of a partial sum is at most `C²` times the elapsed time. -/
theorem integral_partialSum_sq_le : ∀ (k : ℕ) (hk : k ≤ G.N),
    ∫ ω, (G.partialSum W k ω) ^ 2 ∂P
      ≤ C ^ 2 * G.partition ⟨k, Nat.lt_succ_of_le hk⟩ := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    have hp : G.partition (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) = 0 := G.partition_zero
    simp_rw [h0]
    simp [G.partition_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have he1 : G.partition (⟨n, hn⟩ : Fin G.N).castSucc
        = G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) := rfl
    have he2 : G.partition (⟨n, hn⟩ : Fin G.N).succ
        = G.partition (⟨n + 1, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) := rfl
    rw [G.integral_partialSum_sq_succ W ℱ hℱ h_adapt hC0 hC hn]
    have h1 := ih hn.le
    have h2 := G.integral_xi_sq_le (P := P) hC0 hC ⟨n, hn⟩
    have h3 := mul_le_mul_of_nonneg_right h2 hΔ0
    rw [he1, he2] at h3 hΔ0 ⊢
    linarith

include hℱ h_adapt hC0 hC in
/-- The fourth moment of a partial sum is controlled by the elapsed time. -/
theorem integral_partialSum_pow_four_le : ∀ (k : ℕ) (hk : k ≤ G.N),
    ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
      ≤ 6 * C ^ 4 * (G.partition (Fin.last G.N)
          * G.partition ⟨k, Nat.lt_succ_of_le hk⟩)
        + gaussianFourthMoment * C ^ 4 * G.partition ⟨k, Nat.lt_succ_of_le hk⟩ ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    have hp : G.partition (⟨0, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) = 0 := G.partition_zero
    simp_rw [h0]
    simp [G.partition_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have he1 : G.partition (⟨n, hn⟩ : Fin G.N).castSucc
        = G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) := rfl
    have he2 : G.partition (⟨n, hn⟩ : Fin G.N).succ
        = G.partition (⟨n + 1, Nat.lt_succ_of_le hk⟩ : Fin (G.N + 1)) := rfl
    -- the mixed second moment
    have hSint : Integrable (fun ω => (G.partialSum W n ω) ^ 2) P :=
      integrable_pow_of_memLp (m := 2) (by norm_num) (by simp)
        (G.memLp_partialSum W hC 2 (by simp) n)
    have hmix : Integrable
        (fun ω => (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2) P := by
      refine (hSint.const_mul (C ^ 2)).mono
        (((G.measurable_partialSum W n).pow_const 2).mul
          ((G.ξ_measurable _).pow_const 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      have hx := hC ⟨n, hn⟩ ω
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ C ^ 2)]
      have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
      nlinarith [pow_nonneg (abs_nonneg (G.partialSum W n ω)) 2]
    have hmix_le : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
        ≤ C ^ 2 * ∫ ω, (G.partialSum W n ω) ^ 2 ∂P := by
      have hstep : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
          ≤ ∫ ω, C ^ 2 * (G.partialSum W n ω) ^ 2 ∂P :=
        integral_mono hmix (hSint.const_mul _) fun ω => by
          have hx := hC ⟨n, hn⟩ ω
          have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hx 2
          have h5 : (G.ξ ⟨n, hn⟩ ω) ^ 2 ≤ C ^ 2 := by
            rwa [← abs_pow, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (G.ξ ⟨n, hn⟩ ω) ^ 2)] at h4
          nlinarith [sq_nonneg (G.partialSum W n ω)]
      rwa [integral_const_mul] at hstep
    have hS2 := G.integral_partialSum_sq_le W ℱ hℱ h_adapt hC0 hC n hn.le
    have hlast : G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1))
        ≤ G.partition (Fin.last G.N) :=
      G.partition_strictMono.monotone (by rw [Fin.le_def]; simp [Fin.last]; omega)
    have hτ0 : (0 : ℝ) ≤ G.partition (⟨n, Nat.lt_succ_of_le hn.le⟩ : Fin (G.N + 1)) :=
      G.partition_nonneg _
    have hc0 : (0 : ℝ) ≤ gaussianFourthMoment := gaussianFourthMoment_nonneg
    have hξ4 := G.integral_xi_pow_four_le (P := P) hC ⟨n, hn⟩
    rw [G.integral_partialSum_pow_four_succ W ℱ hℱ h_adapt hC0 hC hn]
    have h1 := ih hn.le
    rw [he1, he2] at hΔ0 ⊢
    nlinarith [mul_nonneg (pow_nonneg hC0 4) hΔ0, sq_nonneg C,
      mul_nonneg hc0 (mul_nonneg (pow_nonneg hC0 4) (mul_nonneg hτ0 hΔ0)),
      mul_le_mul_of_nonneg_right hmix_le hΔ0,
      mul_le_mul_of_nonneg_right hS2 hΔ0,
      mul_le_mul_of_nonneg_right hξ4
        (mul_nonneg (mul_nonneg hΔ0 hΔ0) hc0)]

include hℱ h_adapt hC0 hC in
/-- **Fourth-moment bound for the elementary integral of a uniformly bounded simple
integrand.** -/
theorem integral_simpleIntegral_pow_four_le :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := by
  have hcard := G.integral_partialSum_pow_four_le W ℱ hℱ h_adapt hC0 hC G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  have hlast : G.partition (⟨G.N, Nat.lt_succ_of_le le_rfl⟩ : Fin (G.N + 1))
      = G.partition (Fin.last G.N) := rfl
  rw [hlast] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * C ^ 4 * (G.partition (Fin.last G.N) * G.partition (Fin.last G.N))
        + gaussianFourthMoment * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * C ^ 4 * G.partition (Fin.last G.N) ^ 2 := by ring

include hℱ h_adapt hC0 hC in
/-- The fourth-moment bound stated on the horizon. -/
theorem integral_simpleIntegral_pow_four_le_horizon :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * C ^ 4 * T ^ 2 := by
  refine (G.integral_simpleIntegral_pow_four_le W ℱ hℱ h_adapt hC0 hC).trans ?_
  have h1 : G.partition (Fin.last G.N) ≤ T := G.partition_le_T
  have h2 : (0 : ℝ) ≤ G.partition (Fin.last G.N) := G.partition_nonneg _
  have h3 : (0 : ℝ) ≤ 6 + gaussianFourthMoment := by
    linarith [gaussianFourthMoment_nonneg]
  have h4 : G.partition (Fin.last G.N) ^ 2 ≤ T ^ 2 := by nlinarith
  nlinarith [pow_nonneg hC0 4, mul_nonneg h3 (pow_nonneg hC0 4)]


include hℱ h_adapt hC0 hC in
/-- Second moment of a partial sum against a per-tile coefficient bound. -/
theorem integral_partialSum_sq_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 2 ∂P ≤ G.varClock c k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    simp_rw [h0]
    simp [G.varClock_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    rw [G.integral_partialSum_sq_succ W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    have h2 : ∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P ≤ c ⟨n, hn⟩ ^ 2 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 1
    linarith [mul_le_mul_of_nonneg_right h2 hΔ0]

include hℱ h_adapt hC0 hC in
/-- Fourth moment of a partial sum against a per-tile coefficient bound: the elapsed
variance budget `∑_{j<k} c_j² (τ_{j+1} − τ_j)` replaces `C²τ_k`. -/
theorem integral_partialSum_pow_four_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∀ (k : ℕ) (_hk : k ≤ G.N),
      ∫ ω, (G.partialSum W k ω) ^ 4 ∂P
        ≤ 6 * (G.varClock c G.N * G.varClock c k)
          + gaussianFourthMoment * G.varClock c k ^ 2 := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : ∀ ω, G.partialSum W 0 ω = 0 := G.partialSum_zero W
    simp_rw [h0]
    simp [G.varClock_zero]
  | succ n ih =>
    intro hk
    have hn : n < G.N := hk
    have hΔ0 : (0 : ℝ) ≤ G.partition (⟨n, hn⟩ : Fin G.N).succ
        - G.partition (⟨n, hn⟩ : Fin G.N).castSucc :=
      sub_nonneg.mpr (G.partition_strictMono Fin.castSucc_lt_succ).le
    have hcn2 : (0 : ℝ) ≤ c ⟨n, hn⟩ ^ 2 := sq_nonneg _
    have hxi2 : ∀ ω, (G.ξ ⟨n, hn⟩ ω) ^ 2 ≤ c ⟨n, hn⟩ ^ 2 := fun ω => by
      have h := pow_le_pow_left₀ (abs_nonneg (G.ξ ⟨n, hn⟩ ω)) (hc ⟨n, hn⟩ ω) 2
      rwa [← abs_pow, abs_of_nonneg (sq_nonneg (G.ξ ⟨n, hn⟩ ω))] at h
    have hSint : Integrable (fun ω => (G.partialSum W n ω) ^ 2) P :=
      integrable_pow_of_memLp (m := 2) (by norm_num) (by simp)
        (G.memLp_partialSum W hC 2 (by simp) n)
    have hmix : Integrable
        (fun ω => (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2) P := by
      refine (hSint.const_mul (c ⟨n, hn⟩ ^ 2)).mono
        (((G.measurable_partialSum W n).pow_const 2).mul
          ((G.ξ_measurable _).pow_const 2)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_pow,
        abs_of_nonneg hcn2]
      have h4 : |G.ξ ⟨n, hn⟩ ω| ^ 2 ≤ c ⟨n, hn⟩ ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hc ⟨n, hn⟩ ω) 2
      nlinarith [pow_nonneg (abs_nonneg (G.partialSum W n ω)) 2]
    have hmix_le : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
        ≤ c ⟨n, hn⟩ ^ 2 * ∫ ω, (G.partialSum W n ω) ^ 2 ∂P := by
      have hstep : ∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P
          ≤ ∫ ω, c ⟨n, hn⟩ ^ 2 * (G.partialSum W n ω) ^ 2 ∂P :=
        integral_mono hmix (hSint.const_mul _) fun ω => by
          nlinarith [sq_nonneg (G.partialSum W n ω), hxi2 ω]
      rwa [integral_const_mul] at hstep
    have hS2 := G.integral_partialSum_sq_le_varClock W ℱ hℱ h_adapt hC0 hC hc n hn.le
    have hVN : G.varClock c n ≤ G.varClock c G.N := G.varClock_mono c hn.le
    have hV0 : (0 : ℝ) ≤ G.varClock c n := G.varClock_nonneg c n
    have hcg : (0 : ℝ) ≤ gaussianFourthMoment := gaussianFourthMoment_nonneg
    have hA : (∫ ω, (G.partialSum W n ω) ^ 2 * (G.ξ ⟨n, hn⟩ ω) ^ 2 ∂P)
        ≤ c ⟨n, hn⟩ ^ 2 * G.varClock c G.N :=
      hmix_le.trans (mul_le_mul_of_nonneg_left (hS2.trans hVN) hcn2)
    have hB : (∫ ω, (G.ξ ⟨n, hn⟩ ω) ^ 4 ∂P) ≤ c ⟨n, hn⟩ ^ 4 := by
      simpa using G.integral_xi_even_le (P := P) ⟨n, hn⟩ (hc ⟨n, hn⟩) 2
    rw [G.integral_partialSum_pow_four_succ W ℱ hℱ h_adapt hC0 hC hn, G.varClock_succ c hn]
    have h1 := ih hn.le
    nlinarith [mul_le_mul_of_nonneg_right hA hΔ0,
      mul_le_mul_of_nonneg_right hB
        (mul_nonneg (mul_nonneg hΔ0 hΔ0) hcg),
      mul_nonneg (mul_nonneg (mul_nonneg hcg hV0) hcn2) hΔ0]

include hℱ h_adapt hC0 hC in
/-- **Fourth-moment bound for the elementary integral against a per-tile coefficient
bound.** -/
theorem integral_simpleIntegral_pow_four_le_varClock {c : Fin G.N → ℝ}
    (hc : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ c i) :
    ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by
  have hcard := G.integral_partialSum_pow_four_le_varClock W ℱ hℱ h_adapt hC0 hC hc G.N le_rfl
  have hfun : ∀ ω, G.partialSum W G.N ω = simpleIntegral W G T ω := G.partialSum_card W
  simp_rw [hfun] at hcard
  calc ∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P
      ≤ 6 * (G.varClock c G.N * G.varClock c G.N)
        + gaussianFourthMoment * G.varClock c G.N ^ 2 := hcard
    _ = (6 + gaussianFourthMoment) * G.varClock c G.N ^ 2 := by ring

end Moments



end SimplePredictable

/-- A function fixing `0` commutes with a step sum over a strictly monotone partition. -/
theorem comp_sum_ite {M : ℕ} {π : Fin (M + 1) → ℝ} (hπ : StrictMono π)
    (f : Fin M → ℝ) (s : ℝ) (g : ℝ → ℝ) (hg0 : g 0 = 0) :
    g (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then f j else 0)
      = ∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then g (f j) else 0 := by
  classical
  by_cases h : ∃ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ
  · obtain ⟨j₀, hj₀⟩ := h
    have huniq : ∀ j : Fin M, π j.castSucc < s ∧ s ≤ π j.succ → j = j₀ := by
      intro j hj
      by_contra hne
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · have hle : (j.succ : Fin (M + 1)) ≤ j₀.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hlt
        exact absurd (hj.2.trans (hπ.monotone hle)) (not_le.mpr hj₀.1)
      · have hle : (j₀.succ : Fin (M + 1)) ≤ j.castSucc := by
          rw [Fin.le_def]; simpa [Fin.succ, Fin.castSucc] using hgt
        exact absurd (hj₀.2.trans (hπ.monotone hle)) (not_le.mpr hj.1)
    have hsum : ∀ h : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h j else 0) = h j₀ := by
      intro h
      rw [Finset.sum_eq_single j₀ (fun j _ hjne => if_neg fun hc => hjne (huniq j hc))
        (fun hnm => absurd (Finset.mem_univ _) hnm)]
      exact if_pos hj₀
    rw [hsum f, hsum fun j => g (f j)]
  · push Not at h
    have hz : ∀ h' : Fin M → ℝ,
        (∑ j : Fin M, if π j.castSucc < s ∧ s ≤ π j.succ then h' j else 0) = 0 :=
      fun h' => Finset.sum_eq_zero fun j _ => if_neg fun hc => absurd hc.2 (not_le.mpr (h j hc.1))
    rw [hz f, hz fun j => g (f j), hg0]

/-- The coefficients of a simple integrand clamped to `[-C, C]`. -/
noncomputable def SimplePredictable.truncate {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ) :
    SimplePredictable Ω T where
  N := G.N
  partition := G.partition
  partition_zero := G.partition_zero
  partition_le_T := G.partition_le_T
  partition_strictMono := G.partition_strictMono
  ξ := fun i ω => max (-C) (min C (G.ξ i ω))
  ξ_bounded := fun i => ⟨|C|, fun ω => abs_le.mpr
    ⟨le_max_of_le_left (neg_le_neg (le_abs_self C)),
      max_le (neg_le_abs C) ((min_le_left C (G.ξ i ω)).trans (le_abs_self C))⟩⟩
  ξ_measurable := fun i =>
    measurable_const.max (measurable_const.min (G.ξ_measurable i))

theorem SimplePredictable.abs_truncate_xi_le {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (i : Fin G.N) (ω : Ω) : |(G.truncate C).ξ i ω| ≤ C := by
  refine abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem SimplePredictable.truncate_eval {T : ℝ} (G : SimplePredictable Ω T) {C : ℝ}
    (hC : 0 ≤ C) (s : ℝ) (ω : Ω) :
    (G.truncate C).eval s ω = max (-C) (min C (G.eval s ω)) := by
  have hg0 : max (-C) (min C (0 : ℝ)) = 0 := by
    rw [min_eq_right hC, max_eq_right (by linarith : -C ≤ (0 : ℝ))]
  exact (comp_sum_ite G.partition_strictMono (fun i => G.ξ i ω) s
    (fun x => max (-C) (min C x)) hg0).symm

theorem SimplePredictable.truncate_adapt (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T) (C : ℝ)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i)) :
    ∀ i : Fin (G.truncate C).N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ ((G.truncate C).partition i.castSucc)) ((G.truncate C).ξ i) := by
  intro i
  exact (measurable_const.max
    (measurable_const.min (h_adapt i).measurable)).stronglyMeasurable

/-- Clamping to `[-C, C]` moves a value no further from any target already in `[-C, C]`. -/
theorem abs_clamp_sub_le {C x y : ℝ} (hC : 0 ≤ C) (hy : |y| ≤ C) :
    |max (-C) (min C x) - y| ≤ |x - y| := by
  obtain ⟨hy1, hy2⟩ := abs_le.mp hy
  rcases le_or_gt x (-C) with hx | hx
  · rw [min_eq_right (by linarith : x ≤ C), max_eq_left hx,
      abs_of_nonpos (by linarith : -C - y ≤ 0), abs_of_nonpos (by linarith : x - y ≤ 0)]
    linarith
  · rcases le_or_gt x C with hx' | hx'
    · rw [min_eq_right hx', max_eq_right (by linarith : -C ≤ x)]
    · rw [min_eq_left hx'.le, max_eq_right (by linarith : -C ≤ C),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ C - y),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ x - y)]
      linarith

section LintegralForm

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- The fourth-moment bound for a simple integrand, in `lintegral` form. -/
theorem SimplePredictable.lintegral_simpleIntegral_pow_four_le {T : ℝ}
    (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C) :
    ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * T ^ 2) := by
  have hmem : MemLp (fun ω => simpleIntegral W G T ω) 4 P := by
    have h := G.memLp_partialSum W hC 4 (by simp) G.N
    have hfun : G.partialSum W G.N = fun ω => simpleIntegral W G T ω := by
      funext ω; exact G.partialSum_card W ω
    rwa [hfun] at h
  have hmem' : MemLp (fun ω => simpleIntegral W G T ω) ((4 : ℕ) : ℝ≥0∞) P := by
    simpa using hmem
  have hint : Integrable (fun ω => (simpleIntegral W G T ω) ^ 4) P := by
    refine (hmem'.integrable_norm_pow (by norm_num)).mono
      ((continuous_pow 4).comp_aestronglyMeasurable hmem.1)
      (Filter.Eventually.of_forall fun ω => by simp)
  have hpt : ∀ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4
      = ENNReal.ofReal ((simpleIntegral W G T ω) ^ 4) := by
    intro ω
    have h1 : (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞)
        = ENNReal.ofReal |simpleIntegral W G T ω| := by
      rw [ENNReal.ofReal_eq_coe_nnreal (abs_nonneg _)]
      exact congrArg _ (NNReal.eq (by simp [Real.norm_eq_abs]))
    rw [h1, ← ENNReal.ofReal_pow (abs_nonneg _), ← abs_pow,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ simpleIntegral W G T ω ^ 4)]
  have heq : ∫⁻ ω, (‖simpleIntegral W G T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      = ENNReal.ofReal (∫ ω, (simpleIntegral W G T ω) ^ 4 ∂P) := by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun ω => by positivity)]
    exact lintegral_congr hpt
  rw [heq]
  exact ENNReal.ofReal_le_ofReal
    (G.integral_simpleIntegral_pow_four_le_horizon W ℱ hℱ h_adapt hC0 hC)

include hℱ in
/-- **Fourth-moment bound for the `L²` Itô integral of a uniformly bounded integrand.** -/
theorem lintegral_stochasticIntegralBrownian_pow_four_le
    (H : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {C : ℝ} (hC0 : 0 ≤ C) (hCH : ∀ ω s, |H ω s| ≤ C)
    {T : ℝ} (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ ENNReal.ofReal ((6 + gaussianFourthMoment) * C ^ 4 * T ^ 2) := by
  classical
  choose G0 hG0adapt hG0within using fun n : ℕ =>
    exists_adaptedSimple_within ℱ H hm hp hT (hq T hT)
      (show (0 : ℝ≥0∞) < ((n : ℝ≥0∞) + 1)⁻¹ from ENNReal.inv_pos.mpr
        (ENNReal.add_ne_top.mpr ⟨ENNReal.natCast_ne_top n, ENNReal.one_ne_top⟩))
  have hGadapt : ∀ n, ∀ i : Fin ((G0 n).truncate C).N,
      @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (((G0 n).truncate C).partition i.castSucc)) (((G0 n).truncate C).ξ i) :=
    fun n => SimplePredictable.truncate_adapt ℱ (G0 n) C (hG0adapt n)
  have hGbdd : ∀ n, ∀ (i : Fin ((G0 n).truncate C).N) (ω : Ω),
      |((G0 n).truncate C).ξ i ω| ≤ C := fun n i ω => (G0 n).abs_truncate_xi_le hC0 i ω
  have hGwithin : ∀ n, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖((G0 n).truncate C).eval s ω - H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n
    refine le_trans ?_ (hG0within n).le
    refine lintegral_mono fun ω => lintegral_mono fun s => ?_
    have hle : ‖((G0 n).truncate C).eval s ω - H ω s‖₊ ≤ ‖H ω s - (G0 n).eval s ω‖₊ := by
      rw [← NNReal.coe_le_coe]
      simp only [coe_nnnorm, Real.norm_eq_abs]
      rw [(G0 n).truncate_eval hC0 s ω, abs_sub_comm (H ω s)]
      exact abs_clamp_sub_le hC0 (hCH ω s)
    exact pow_le_pow_left' (ENNReal.coe_le_coe.mpr hle) 2
  have htol : Filter.Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) Filter.atTop (nhds 0) := by
    have hg : Filter.Tendsto (fun n : ℕ => n + 1) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_mono (fun n => Nat.le_succ n) Filter.tendsto_id
    have h := ENNReal.tendsto_inv_nat_nhds_zero.comp hg
    refine h.congr fun n => ?_
    simp [Nat.cast_add_one]
  have hsq : Filter.Tendsto (fun n => ∫⁻ ω,
      (‖simpleIntegral W ((G0 n).truncate C) T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (nhds 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds htol
      (Filter.Eventually.of_forall fun _ => bot_le) (Filter.Eventually.of_forall fun n => ?_)
    rw [isometry_simple_sub_stochasticIntegralBrownian W ℱ hℱ ((G0 n).truncate C)
      (hGadapt n) H hm hp hq hT]
    exact hGwithin n
  have heL : Filter.Tendsto (fun n => MeasureTheory.eLpNorm
      (fun ω => simpleIntegral W ((G0 n).truncate C) T ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P) Filter.atTop (nhds 0) := by
    have hrw : ∀ n, MeasureTheory.eLpNorm
        (fun ω => simpleIntegral W ((G0 n).truncate C) T ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω) 2 P
        = (∫⁻ ω, (‖simpleIntegral W ((G0 n).truncate C) T ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
              ^ ((2 : ℝ))⁻¹ := by
      intro n
      rw [← eLpNorm_two_rpow_eq_lintegral_sq]
      exact (ENNReal.rpow_rpow_inv (by norm_num) _).symm
    simp_rw [hrw]
    have h := (ENNReal.continuous_rpow_const (y := ((2 : ℝ))⁻¹)).tendsto 0 |>.comp hsq
    simpa [Function.comp_def,
      ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < ((2 : ℝ))⁻¹)] using h
  have hmeasG : ∀ n, Measurable (simpleIntegral W ((G0 n).truncate C) T) := by
    intro n
    unfold simpleIntegral
    exact Finset.measurable_sum _ fun i _ =>
      (((G0 n).truncate C).ξ_measurable i).mul
        ((W.measurable_eval _).sub (W.measurable_eval _))
  have hmeasSI : Measurable (stochasticIntegralBrownian W ℱ hℱ H hm hp hq T) :=
    ((stochasticIntegralBrownian_stronglyAdapted W ℱ hℱ H hm hp hq T).mono (ℱ.le T)).measurable
  have hTIM : MeasureTheory.TendstoInMeasure P
      (fun n => simpleIntegral W ((G0 n).truncate C) T) Filter.atTop
      (stochasticIntegralBrownian W ℱ hℱ H hm hp hq T) :=
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
      (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 4 ∂P
      ≤ Filter.liminf (fun k => ∫⁻ ω,
        (‖simpleIntegral W ((G0 (ns k)).truncate C) T ω‖₊ : ℝ≥0∞) ^ 4 ∂P) Filter.atTop := by
    have h1 : ∀ᵐ ω ∂P,
        (‖stochasticIntegralBrownian W ℱ hℱ H hm hp hq T ω‖₊ : ℝ≥0∞) ^ 4
        = Filter.liminf (fun k =>
            (‖simpleIntegral W ((G0 (ns k)).truncate C) T ω‖₊ : ℝ≥0∞) ^ 4) Filter.atTop := by
      filter_upwards [hns_ae] with ω hω
      exact ((hcont.tendsto _).comp hω).liminf_eq.symm
    rw [lintegral_congr_ae h1]
    exact lintegral_liminf_le fun k => (hcont.measurable.comp (hmeasG (ns k)))
  refine hfatou.trans (Filter.liminf_le_of_frequently_le
    (Filter.Eventually.frequently (Filter.Eventually.of_forall fun k => ?_)))
  exact SimplePredictable.lintegral_simpleIntegral_pow_four_le W ℱ hℱ
    ((G0 (ns k)).truncate C) (hGadapt (ns k)) hC0 (hGbdd (ns k))

end LintegralForm

end LevyStochCalc.Brownian.Ito
