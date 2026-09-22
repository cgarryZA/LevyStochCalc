/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.SimpleProfile

/-!
# The character of a compensated step integral of a mark profile

The count of a Poisson random measure on a region of finite intensity is Poisson, so the
character of the compensated count carries the Lévy–Khintchine integrand `e^{iuc} - 1 - iuc`
at the coefficient `c`. A simple mark profile pairs pairwise-disjoint mark sets with constant
coefficients, so over a step its compensated integral is a sum of independent compensated
counts and its character is the product of the counts' characters,

  `E[exp (i u J(f))] = exp ((b - a) ∫ (exp (i u f) - 1 - i u f) dν)`.

The right-hand side is continuous along `L²(ν)` convergence of the profile, so the identity
transfers to a profile approximated by simple ones together with any `L²(P)` limit of their
compensated step integrals.

## Main definitions

* `LevyStochCalc.Poisson.levyCharIntegrand` — the integrand `e^{iux} - 1 - iux`.

## Main statements

* `LevyStochCalc.Poisson.integral_exp_I_mul_compensated` — the character of a compensated
  count on a region of finite intensity.
* `LevyStochCalc.Poisson.SimpleProfile.integral_exp_I_mul_stepIntegral` — the character of the
  compensated step integral of a simple mark profile.
* `LevyStochCalc.Poisson.integrable_levyCharIntegrand` — integrability of the integrand at a
  square-integrable mark profile.
* `LevyStochCalc.Poisson.tendsto_integral_levyCharIntegrand` — continuity of the Lévy
  characteristic exponent along `L²(ν)` convergence of the profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_of_tendsto_stepIntegral` — the character of an
  `L²(P)` limit of the compensated step integrals of simple profiles converging in `L²(ν)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### The Lévy–Khintchine integrand -/

/-- The integrand `e^{iux} - 1 - iux` of the Lévy characteristic exponent. -/
noncomputable def levyCharIntegrand (u x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1 - Complex.I * ((u * x : ℝ) : ℂ)

@[simp] theorem levyCharIntegrand_zero (u : ℝ) : levyCharIntegrand u 0 = 0 := by
  simp [levyCharIntegrand]

theorem continuous_levyCharIntegrand (u : ℝ) : Continuous (levyCharIntegrand u) := by
  unfold levyCharIntegrand
  fun_prop

theorem measurable_levyCharIntegrand (u : ℝ) : Measurable (levyCharIntegrand u) :=
  (continuous_levyCharIntegrand u).measurable

/-- The Lévy characteristic integrand is bounded by three times the square of its argument. -/
theorem norm_levyCharIntegrand_le (u x : ℝ) :
    ‖levyCharIntegrand u x‖ ≤ 3 * (u * x) ^ 2 := by
  set t : ℝ := u * x with ht
  rcases le_or_gt |t| 1 with h | h
  · have hnorm : ‖Complex.I * ((t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact h
    have := Complex.norm_exp_sub_one_sub_id_le hnorm
    have hsq : ‖Complex.I * ((t : ℝ) : ℂ)‖ ^ 2 = t ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [levyCharIntegrand, ← ht]
    calc ‖Complex.exp (Complex.I * (t : ℂ)) - 1 - Complex.I * (t : ℂ)‖
        ≤ ‖Complex.I * ((t : ℝ) : ℂ)‖ ^ 2 := this
      _ = t ^ 2 := hsq
      _ ≤ 3 * t ^ 2 := by nlinarith [sq_nonneg t]
  · have h1 : ‖Complex.exp (Complex.I * ((t : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp_I_mul_ofReal]
    have h2 : ‖Complex.I * ((t : ℝ) : ℂ)‖ = |t| := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
    have hle : ‖levyCharIntegrand u x‖ ≤ 1 + 1 + |t| := by
      rw [levyCharIntegrand, ← ht]
      refine (norm_sub_le _ _).trans ?_
      gcongr
      · exact (norm_sub_le _ _).trans (by rw [h1, norm_one])
      · exact h2.le
    have habs : |t| ≤ t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    have h1t : (1 : ℝ) ≤ t ^ 2 := by nlinarith [abs_nonneg t, sq_abs t]
    linarith

/-- A bound on the increment of the Lévy characteristic integrand between two arguments. -/
theorem norm_levyCharIntegrand_sub_le (u x y : ℝ) :
    ‖levyCharIntegrand u x - levyCharIntegrand u y‖
      ≤ 3 * (u * (x - y)) ^ 2 + u ^ 2 * |y| * |x - y| := by
  have hsplit : levyCharIntegrand u x - levyCharIntegrand u y
      = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) * levyCharIntegrand u (x - y)
        + (Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1)
          * (Complex.I * ((u * (x - y) : ℝ) : ℂ)) := by
    have hexp : Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
        = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
          * Complex.exp (Complex.I * ((u * (x - y) : ℝ) : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [levyCharIntegrand, levyCharIntegrand, levyCharIntegrand, hexp]
    push_cast
    ring
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 : ‖Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) * levyCharIntegrand u (x - y)‖
      ≤ 3 * (u * (x - y)) ^ 2 := by
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    exact norm_levyCharIntegrand_le u (x - y)
  have h2 : ‖(Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1)
      * (Complex.I * ((u * (x - y) : ℝ) : ℂ))‖ ≤ u ^ 2 * |y| * |x - y| := by
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_mul]
    have hu : ‖Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1‖ ≤ |u| * |y| := by
      refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
      rw [Real.norm_eq_abs, abs_mul]
    calc ‖Complex.exp (Complex.I * ((u * y : ℝ) : ℂ)) - 1‖ * (|u| * |x - y|)
        ≤ (|u| * |y|) * (|u| * |x - y|) := by
          gcongr
      _ = u ^ 2 * |y| * |x - y| := by
          rw [← sq_abs u]; ring
  linarith

/-! ### The character of a count and of a compensated count -/

/-- The character of a Poisson count on a region of finite intensity. -/
theorem integral_exp_I_mul_count (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * (N.N ω B).toReal : ℝ) : ℂ)) ∂P
      = Complex.exp ((referenceIntensity ν B).toReal
          * (Complex.exp (Complex.I * (u : ℂ)) - 1)) := by
  classical
  set r : ℝ≥0 := (referenceIntensity ν B).toNNReal with hrdef
  have hrR : ((r : ℝ) : ℂ) = ((referenceIntensity ν B).toReal : ℂ) := rfl
  set g : ℝ≥0∞ → ℂ := fun x => Complex.exp (Complex.I * ((u * x.toReal : ℝ) : ℂ)) with hg
  have hgm : Measurable g := by
    rw [hg]
    fun_prop
  have hXm : Measurable fun ω => N.N ω B := N.measurable_eval hB
  have hstep1 : ∫ ω, g (N.N ω B) ∂P = ∫ x, g x ∂(P.map fun ω => N.N ω B) :=
    (integral_map hXm.aemeasurable hgm.aestronglyMeasurable).symm
  have hstep2 : ∫ x, g x ∂(P.map fun ω => N.N ω B)
      = ∫ n : ℕ, g ((n : ℝ≥0∞)) ∂(poissonMeasure r) := by
    rw [N.poisson_law hB hfin, poissonMeasureENN, ← hrdef]
    exact integral_map (by fun_prop) hgm.aestronglyMeasurable
  have hstep3 : ∫ n : ℕ, g ((n : ℝ≥0∞)) ∂(poissonMeasure r)
      = charFun ((poissonMeasure r).map (Nat.cast : ℕ → ℝ)) u := by
    rw [charFun_apply_real,
      integral_map (by fun_prop : AEMeasurable (Nat.cast : ℕ → ℝ) (poissonMeasure r))
        (by fun_prop : AEStronglyMeasurable (fun x : ℝ => Complex.exp ((u : ℂ) * (x : ℂ)
          * Complex.I)) _)]
    refine integral_congr_ae (Eventually.of_forall fun n => ?_)
    rw [hg]
    simp only [ENNReal.toReal_natCast]
    congr 1
    push_cast
    ring
  rw [hstep1, hstep2, hstep3, charFun_map_cast_poissonMeasure, hrR]
  congr 2
  rw [mul_comm]

/-- The character of the compensated count on a region of finite intensity. -/
theorem integral_exp_I_mul_compensated (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * N.compensated B ω : ℝ) : ℂ)) ∂P
      = Complex.exp ((referenceIntensity ν B).toReal
          * (Complex.exp (Complex.I * (u : ℂ)) - 1 - Complex.I * (u : ℂ))) := by
  have hfactor : ∀ ω, Complex.exp (Complex.I * ((u * N.compensated B ω : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((u * (N.N ω B).toReal : ℝ) : ℂ))
        * Complex.exp (-(Complex.I * ((u * (referenceIntensity ν B).toReal : ℝ) : ℂ))) := by
    intro ω
    rw [← Complex.exp_add]
    congr 1
    rw [PoissonRandomMeasure.compensated]
    push_cast
    ring
  simp_rw [hfactor]
  rw [integral_mul_const, integral_exp_I_mul_count N hB hfin u, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-! ### The character at a simple mark profile -/

namespace SimpleProfile

omit [SigmaFinite ν] in
/-- On one of its mark sets a simple profile takes the matching coefficient. -/
theorem toFun_of_mem (G : SimpleProfile E ν) {k : Fin G.K} {e : E} (he : e ∈ G.B k) :
    G.toFun e = G.c k := by
  classical
  rw [toFun]
  refine (Finset.sum_eq_single k (fun l _ hl => ?_)
    (fun h => absurd (Finset.mem_univ _) h)).trans ?_
  · rw [Set.indicator_of_notMem (fun hmem =>
      (Set.disjoint_left.1 (G.B_disjoint hl) hmem) he), mul_zero]
  · rw [Set.indicator_of_mem he, mul_one]

omit [SigmaFinite ν] in
/-- Outside all of its mark sets a simple profile vanishes. -/
theorem toFun_of_notMem (G : SimpleProfile E ν) {e : E} (he : ∀ k, e ∉ G.B k) :
    G.toFun e = 0 := by
  rw [toFun]
  exact Finset.sum_eq_zero fun k _ => by rw [Set.indicator_of_notMem (he k), mul_zero]

omit [SigmaFinite ν] in
/-- The Lévy characteristic integrand at a simple profile, through the indicators of its mark
sets. -/
theorem levyCharIntegrand_toFun (G : SimpleProfile E ν) (u : ℝ) (e : E) :
    levyCharIntegrand u (G.toFun e)
      = ∑ k, (G.B k).indicator (fun _ => levyCharIntegrand u (G.c k)) e := by
  classical
  by_cases h : ∃ k, e ∈ G.B k
  · obtain ⟨k, hk⟩ := h
    rw [G.toFun_of_mem hk, Finset.sum_eq_single_of_mem k (Finset.mem_univ k)
      (fun l _ hl => Set.indicator_of_notMem
        (fun hmem => (Set.disjoint_left.1 (G.B_disjoint hl) hmem) hk) _),
      Set.indicator_of_mem hk]
  · simp only [not_exists] at h
    rw [G.toFun_of_notMem h, levyCharIntegrand_zero]
    exact (Finset.sum_eq_zero fun k _ => Set.indicator_of_notMem (h k) _).symm

omit [SigmaFinite ν] in
/-- The Lévy characteristic exponent of a simple profile, as a sum over its mark sets. -/
theorem integral_levyCharIntegrand_toFun (G : SimpleProfile E ν) (u : ℝ) :
    ∫ e, levyCharIntegrand u (G.toFun e) ∂ν
      = ∑ k, ((ν (G.B k)).toReal : ℂ) * levyCharIntegrand u (G.c k) := by
  classical
  have hint : ∀ k : Fin G.K, Integrable
      (fun e => (G.B k).indicator (fun _ => levyCharIntegrand u (G.c k)) e) ν := fun k =>
    memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (G.B_measurable k) _ (Or.inr (G.B_finite k)))
  simp_rw [G.levyCharIntegrand_toFun u]
  rw [integral_finsetSum _ fun k _ => hint k]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_indicator_const _ (G.B_measurable k), Complex.real_smul, measureReal_def]

/-- **The character of the compensated step integral of a simple mark profile.** -/
theorem integral_exp_I_mul_stepIntegral (G : SimpleProfile E ν)
    (N : PoissonRandomMeasure P ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * G.stepIntegral N a b ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (G.toFun e) ∂ν) := by
  classical
  have hRm : ∀ k : Fin G.K, MeasurableSet (Set.Ioc a b ×ˢ G.B k) := fun k =>
    measurableSet_Ioc.prod (G.B_measurable k)
  have hRfin : ∀ k : Fin G.K, referenceIntensity ν (Set.Ioc a b ×ˢ G.B k) ≠ ⊤ := fun k => by
    rw [referenceIntensity_Ioc_prod' _ ha]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k)
  have hRint : ∀ k : Fin G.K, (referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal
      = (b - a) * (ν (G.B k)).toReal := fun k => by
    rw [referenceIntensity_Ioc_prod' _ ha, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith)]
  set f : Fin G.K → ℝ≥0∞ → ℂ := fun k x =>
    Complex.exp (Complex.I * (((u * G.c k)
      * (x.toReal - (referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal) : ℝ) : ℂ)) with hf
  have hfm : ∀ k, Measurable (f k) := by
    intro k
    rw [hf]
    fun_prop
  have hXi : iIndepFun
      (fun (i : ULift (Fin G.K)) (ω : Ω) => N.N ω (Set.Ioc a b ×ˢ G.B i.down)) P := by
    refine N.independent_disjoint (fun i : ULift (Fin G.K) => Set.Ioc a b ×ˢ G.B i.down)
      (fun i => hRm i.down) ?_
    intro i j hij
    refine Set.disjoint_left.2 fun p hp hq => ?_
    refine (Set.disjoint_left.1 (G.B_disjoint ?_) hp.2) hq.2
    exact fun h => hij (ULift.down_injective h)
  have hprod : ∀ ω, ∏ i : ULift (Fin G.K), f i.down (N.N ω (Set.Ioc a b ×ˢ G.B i.down))
      = Complex.exp (Complex.I * ((u * G.stepIntegral N a b ω : ℝ) : ℂ)) := by
    intro ω
    rw [hf]
    simp only
    rw [← Complex.exp_sum,
      Fintype.sum_equiv Equiv.ulift
        (fun i : ULift (Fin G.K) => Complex.I * (((u * G.c i.down)
          * ((N.N ω (Set.Ioc a b ×ˢ G.B i.down)).toReal
            - (referenceIntensity ν (Set.Ioc a b ×ˢ G.B i.down)).toReal) : ℝ) : ℂ))
        (fun k : Fin G.K => Complex.I * (((u * G.c k)
          * ((N.N ω (Set.Ioc a b ×ˢ G.B k)).toReal
            - (referenceIntensity ν (Set.Ioc a b ×ˢ G.B k)).toReal) : ℝ) : ℂ))
        (fun i => rfl)]
    congr 1
    rw [SimpleProfile.stepIntegral, Finset.mul_sum, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PoissonRandomMeasure.compensated]
    push_cast
    ring
  have hfac : ∀ k : Fin G.K, ∫ ω, f k (N.N ω (Set.Ioc a b ×ˢ G.B k)) ∂P
      = Complex.exp ((((b - a) * (ν (G.B k)).toReal : ℝ) : ℂ)
          * levyCharIntegrand u (G.c k)) := by
    intro k
    have hrw : ∀ ω, f k (N.N ω (Set.Ioc a b ×ˢ G.B k))
        = Complex.exp (Complex.I * (((u * G.c k)
            * N.compensated (Set.Ioc a b ×ˢ G.B k) ω : ℝ) : ℂ)) := fun ω => by
      rw [hf, PoissonRandomMeasure.compensated]
    simp_rw [hrw]
    rw [integral_exp_I_mul_compensated N (hRm k) (hRfin k) (u * G.c k), hRint k,
      levyCharIntegrand]
  simp_rw [← hprod]
  rw [hXi.integral_fun_prod_comp (fun i => (N.measurable_eval (hRm i.down)).aemeasurable)
      (fun i => (hfm i.down).aestronglyMeasurable)]
  rw [Fintype.prod_equiv Equiv.ulift
    (fun i : ULift (Fin G.K) => ∫ ω, f i.down (N.N ω (Set.Ioc a b ×ˢ G.B i.down)) ∂P)
    (fun k : Fin G.K => ∫ ω, f k (N.N ω (Set.Ioc a b ×ˢ G.B k)) ∂P) (fun i => rfl)]
  simp_rw [hfac]
  rw [← Complex.exp_sum, integral_levyCharIntegrand_toFun, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  push_cast
  ring

end SimpleProfile

/-! ### Passage to a general square-integrable profile -/

omit [SigmaFinite ν] in
/-- The Lévy characteristic integrand of a square-integrable mark profile is integrable. -/
theorem integrable_levyCharIntegrand (u : ℝ) {g : E → ℝ} (hg : MemLp g 2 ν) :
    Integrable (fun e => levyCharIntegrand u (g e)) ν := by
  refine Integrable.mono' (g := fun e => 3 * u ^ 2 * g e ^ 2) (hg.integrable_sq.const_mul _)
    ((continuous_levyCharIntegrand u).comp_aestronglyMeasurable hg.1)
    (Eventually.of_forall fun e => ?_)
  calc ‖levyCharIntegrand u (g e)‖ ≤ 3 * (u * g e) ^ 2 := norm_levyCharIntegrand_le u (g e)
    _ = 3 * u ^ 2 * g e ^ 2 := by ring

/-- The second moment of a square-integrable function through its `L²` seminorm. -/
private theorem integral_sq_eq_toReal_eLpNorm_sq {α : Type*} [MeasurableSpace α]
    {m : Measure α} {F : α → ℝ} (hF : MemLp F 2 m) :
    ∫ x, F x ^ 2 ∂m = ((eLpNorm F 2 m).toReal) ^ 2 := by
  have h0 : 0 ≤ ∫ x, F x ^ 2 ∂m := integral_nonneg fun x => sq_nonneg _
  have hE : eLpNorm F 2 m = (ENNReal.ofReal (∫ x, F x ^ 2 ∂m)) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
      show (2 : ℝ≥0∞).toReal = 2 from by norm_num,
      ← Compensated.lintegral_sq_eq_ofReal_integral hF]
    refine congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (lintegral_congr fun x => ?_)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
    rfl
  rw [hE, ← ENNReal.toReal_rpow, ENNReal.toReal_ofReal h0, ← Real.sqrt_eq_rpow,
    Real.sq_sqrt h0]

/-- Cauchy–Schwarz for two square-integrable real functions. -/
private theorem integral_abs_mul_le_sqrt {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F H : α → ℝ} (hF : MemLp F 2 m) (hH : MemLp H 2 m) :
    ∫ x, |F x| * |H x| ∂m
      ≤ Real.sqrt (∫ x, F x ^ 2 ∂m) * Real.sqrt (∫ x, H x ^ 2 ∂m) := by
  have h2 : ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) := by norm_num
  have hF' : MemLp (fun x => |F x|) (ENNReal.ofReal 2) m := by
    rw [h2]; simpa [Real.norm_eq_abs] using hF.norm
  have hH' : MemLp (fun x => |H x|) (ENNReal.ofReal 2) m := by
    rw [h2]; simpa [Real.norm_eq_abs] using hH.norm
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := m) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (Eventually.of_forall fun x => abs_nonneg (F x))
    (Eventually.of_forall fun x => abs_nonneg (H x)) hF' hH'
  have hconv : ∀ K : α → ℝ, ∫ x, |K x| ^ (2 : ℝ) ∂m = ∫ x, K x ^ 2 ∂m := by
    intro K
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    change |K x| ^ (2 : ℝ) = K x ^ 2
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast, sq_abs]
  rw [hconv F, hconv H] at h
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  exact h

omit [SigmaFinite ν] in
/-- **The Lévy characteristic exponent is continuous along `L²(ν)` convergence.** -/
theorem tendsto_integral_levyCharIntegrand (u : ℝ) {g : ℕ → E → ℝ} {f : E → ℝ}
    (hg : ∀ n, MemLp (g n) 2 ν) (hf : MemLp f 2 ν)
    (hconv : Tendsto (fun n => eLpNorm (fun e => g n e - f e) 2 ν) atTop (nhds 0)) :
    Tendsto (fun n => ∫ e, levyCharIntegrand u (g n e) ∂ν) atTop
      (nhds (∫ e, levyCharIntegrand u (f e) ∂ν)) := by
  have hDm : ∀ n, MemLp (fun e => g n e - f e) 2 ν := fun n => (hg n).sub hf
  have hdconv : Tendsto (fun n => ∫ e, (g n e - f e) ^ 2 ∂ν) atTop (nhds 0) := by
    have hEq : ∀ n, ∫ e, (g n e - f e) ^ 2 ∂ν
        = ((eLpNorm (fun e => g n e - f e) 2 ν).toReal) ^ 2 := fun n =>
      integral_sq_eq_toReal_eLpNorm_sq (hDm n)
    simp_rw [hEq]
    have h1 : Tendsto (fun n => (eLpNorm (fun e => g n e - f e) 2 ν).toReal) atTop (nhds 0) := by
      have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hconv
      simpa [Function.comp_def] using h
    simpa using h1.pow 2
  have hbound : ∀ n, ‖(∫ e, levyCharIntegrand u (g n e) ∂ν)
      - ∫ e, levyCharIntegrand u (f e) ∂ν‖
      ≤ 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)
        + u ^ 2 * Real.sqrt (∫ e, f e ^ 2 ∂ν)
          * Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν) := by
    intro n
    have hint1 : Integrable (fun e => 3 * u ^ 2 * (g n e - f e) ^ 2) ν :=
      (hDm n).integrable_sq.const_mul _
    have hint2 : Integrable (fun e => u ^ 2 * (|f e| * |g n e - f e|)) ν := by
      refine Integrable.const_mul ?_ _
      refine ((hf.integrable_mul (hDm n)).abs).congr (Eventually.of_forall fun e => ?_)
      change |f e * (g n e - f e)| = |f e| * |g n e - f e|
      exact abs_mul _ _
    rw [← integral_sub (integrable_levyCharIntegrand u (hg n))
      (integrable_levyCharIntegrand u hf)]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ e, ‖levyCharIntegrand u (g n e) - levyCharIntegrand u (f e)‖ ∂ν
        ≤ ∫ e, (3 * u ^ 2 * (g n e - f e) ^ 2 + u ^ 2 * (|f e| * |g n e - f e|)) ∂ν := by
          refine integral_mono (((integrable_levyCharIntegrand u (hg n)).sub
            (integrable_levyCharIntegrand u hf)).norm) (hint1.add hint2) fun e => ?_
          calc ‖levyCharIntegrand u (g n e) - levyCharIntegrand u (f e)‖
              ≤ 3 * (u * (g n e - f e)) ^ 2 + u ^ 2 * |f e| * |g n e - f e| :=
                norm_levyCharIntegrand_sub_le u (g n e) (f e)
            _ = 3 * u ^ 2 * (g n e - f e) ^ 2 + u ^ 2 * (|f e| * |g n e - f e|) := by ring
      _ = 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)
            + u ^ 2 * ∫ e, |f e| * |g n e - f e| ∂ν := by
          rw [integral_add hint1 hint2, integral_const_mul, integral_const_mul]
      _ ≤ 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)
            + u ^ 2 * (Real.sqrt (∫ e, f e ^ 2 ∂ν)
              * Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν)) := by
          gcongr
          exact integral_abs_mul_le_sqrt hf (hDm n)
      _ = _ := by ring
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hbound ?_)
  have h1 : Tendsto (fun n => 3 * u ^ 2 * (∫ e, (g n e - f e) ^ 2 ∂ν)) atTop (nhds 0) := by
    simpa using hdconv.const_mul (3 * u ^ 2)
  have h2 : Tendsto (fun n => Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν)) atTop (nhds 0) := by
    simpa using hdconv.sqrt
  have h3 : Tendsto (fun n => u ^ 2 * Real.sqrt (∫ e, f e ^ 2 ∂ν)
      * Real.sqrt (∫ e, (g n e - f e) ^ 2 ∂ν)) atTop (nhds 0) := by
    simpa using h2.const_mul (u ^ 2 * Real.sqrt (∫ e, f e ^ 2 ∂ν))
  simpa using h1.add h3

/-- The increment of the character of a real variable. -/
private theorem norm_exp_I_mul_sub_le (u x y : ℝ) :
    ‖Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))‖ ≤ |u| * |x - y| := by
  have h1 : Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
        * Complex.exp (Complex.I * ((u * (x - y) : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h2 : Complex.exp (Complex.I * ((u * x : ℝ) : ℂ))
      - Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
      = Complex.exp (Complex.I * ((u * y : ℝ) : ℂ))
        * (Complex.exp (Complex.I * ((u * (x - y) : ℝ) : ℂ)) - 1) := by
    rw [h1]; ring
  rw [h2, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans ?_
  rw [Real.norm_eq_abs, abs_mul]

/-- The first absolute moment of a square-integrable variable on a probability space. -/
private theorem integral_abs_le_sqrt {F : Ω → ℝ} (hF : MemLp F 2 P) :
    ∫ ω, |F ω| ∂P ≤ Real.sqrt (∫ ω, F ω ^ 2 ∂P) := by
  have h := integral_abs_mul_le_sqrt hF (memLp_const (μ := P) (p := 2) (1 : ℝ))
  simpa using h

/-- The character of a real variable is continuous along `L²(P)` convergence. -/
private theorem tendsto_integral_exp_I_mul {X : ℕ → Ω → ℝ} {Y : Ω → ℝ}
    (hX : ∀ n, MemLp (X n) 2 P) (hY : MemLp Y 2 P)
    (hconv : Tendsto (fun n => eLpNorm (fun ω => X n ω - Y ω) 2 P) atTop (nhds 0)) (u : ℝ) :
    Tendsto (fun n => ∫ ω, Complex.exp (Complex.I * ((u * X n ω : ℝ) : ℂ)) ∂P) atTop
      (nhds (∫ ω, Complex.exp (Complex.I * ((u * Y ω : ℝ) : ℂ)) ∂P)) := by
  have hcexp : Continuous fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)) := by fun_prop
  have hint : ∀ Z : Ω → ℝ, MemLp Z 2 P →
      Integrable (fun ω => Complex.exp (Complex.I * ((u * Z ω : ℝ) : ℂ))) P := by
    intro Z hZ
    refine Integrable.mono' (g := fun _ => (1 : ℝ)) (integrable_const 1)
      (hcexp.comp_aestronglyMeasurable (hZ.1.const_mul u)) (Eventually.of_forall fun ω => ?_)
    rw [Complex.norm_exp_I_mul_ofReal]
  have hDm : ∀ n, MemLp (fun ω => X n ω - Y ω) 2 P := fun n => (hX n).sub hY
  have hdconv : Tendsto (fun n => ∫ ω, (X n ω - Y ω) ^ 2 ∂P) atTop (nhds 0) := by
    have hEq : ∀ n, ∫ ω, (X n ω - Y ω) ^ 2 ∂P
        = ((eLpNorm (fun ω => X n ω - Y ω) 2 P).toReal) ^ 2 := fun n =>
      integral_sq_eq_toReal_eLpNorm_sq (hDm n)
    simp_rw [hEq]
    have h1 : Tendsto (fun n => (eLpNorm (fun ω => X n ω - Y ω) 2 P).toReal) atTop (nhds 0) := by
      have h := (ENNReal.tendsto_toReal (a := 0) (by simp)).comp hconv
      simpa [Function.comp_def] using h
    simpa using h1.pow 2
  have hbound : ∀ n, ‖(∫ ω, Complex.exp (Complex.I * ((u * X n ω : ℝ) : ℂ)) ∂P)
      - ∫ ω, Complex.exp (Complex.I * ((u * Y ω : ℝ) : ℂ)) ∂P‖
      ≤ |u| * Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P) := by
    intro n
    have hintD : Integrable (fun ω => |u| * |X n ω - Y ω|) P :=
      (((hDm n).integrable one_le_two).abs).const_mul _
    rw [← integral_sub (hint _ (hX n)) (hint _ hY)]
    refine (norm_integral_le_integral_norm _).trans ?_
    calc ∫ ω, ‖Complex.exp (Complex.I * ((u * X n ω : ℝ) : ℂ))
          - Complex.exp (Complex.I * ((u * Y ω : ℝ) : ℂ))‖ ∂P
        ≤ ∫ ω, |u| * |X n ω - Y ω| ∂P := by
          refine integral_mono (((hint _ (hX n)).sub (hint _ hY)).norm) hintD fun ω => ?_
          exact norm_exp_I_mul_sub_le u (X n ω) (Y ω)
      _ = |u| * ∫ ω, |X n ω - Y ω| ∂P := integral_const_mul _ _
      _ ≤ |u| * Real.sqrt (∫ ω, (X n ω - Y ω) ^ 2 ∂P) := by
          gcongr
          exact integral_abs_le_sqrt (hDm n)
  refine tendsto_iff_norm_sub_tendsto_zero.2 (squeeze_zero (fun n => norm_nonneg _) hbound ?_)
  simpa using (hdconv.sqrt).const_mul |u|

/-- **The character of an `L²(P)` limit of compensated step integrals.** If simple mark
profiles converge in `L²(ν)` to a square-integrable mark profile and their compensated
integrals over a step converge in `L²(P)`, the limit has the Lévy character of the profile at
that step. -/
theorem integral_exp_I_mul_of_tendsto_stepIntegral (N : PoissonRandomMeasure P ν)
    (G : ℕ → SimpleProfile E ν) {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) {J : Ω → ℝ} (hJ : MemLp J 2 P)
    (hGf : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hJlim : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
      atTop (nhds 0)) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * J ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν) := by
  have hLHS : Tendsto (fun n => ∫ ω,
      Complex.exp (Complex.I * ((u * (G n).stepIntegral N a b ω : ℝ) : ℂ)) ∂P) atTop
      (nhds (∫ ω, Complex.exp (Complex.I * ((u * J ω : ℝ) : ℂ)) ∂P)) :=
    tendsto_integral_exp_I_mul (fun n => (G n).memLp_stepIntegral N ha b) hJ hJlim u
  have hRHS : Tendsto (fun n => Complex.exp (((b - a : ℝ) : ℂ)
      * ∫ e, levyCharIntegrand u ((G n).toFun e) ∂ν)) atTop
      (nhds (Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν))) :=
    (Complex.continuous_exp.tendsto _).comp
      ((tendsto_integral_levyCharIntegrand u (fun n => (G n).memLp_toFun) hf hGf).const_mul _)
  exact tendsto_nhds_unique hLHS
    (hRHS.congr fun n => ((G n).integral_exp_I_mul_stepIntegral N ha hab u).symm)

end LevyStochCalc.Poisson
