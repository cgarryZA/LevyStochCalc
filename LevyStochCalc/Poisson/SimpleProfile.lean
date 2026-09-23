/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedDensityLimit
import LevyStochCalc.Poisson.CompensatedDensityStepIntegral

/-!
# Simple mark profiles and their compensated step integrals

A *simple mark profile* for an intensity `ν` on the mark space is a finite family of pairwise
disjoint mark sets of finite intensity carrying constant coefficients, `∑ₖ cₖ 𝟙_{Bₖ}`. Every
square-integrable mark profile is the `L²(ν)` limit of simple profiles, obtained from the nonzero
level sets of square-integrable simple functions approximating it in `L²(ν)`; a bounded one is
the limit of simple profiles obeying the same bound, obtained from the simple functions
approximating it inside the interval the bound cuts out.

The compensated integral of a simple profile over the step `(a, b]` is
`∑ₖ cₖ Ñ((a, b] × Bₖ)`. The `L²(P)` pairing of two such integrals over a common step is
`(b − a) ∫ f g dν`, so profiles converging in `L²(ν)` have compensated integrals converging in
`L²(P)`.

## Main definitions

* `LevyStochCalc.Poisson.SimpleProfile` — a simple mark profile.
* `LevyStochCalc.Poisson.SimpleProfile.toFun` — the function it carries.
* `LevyStochCalc.Poisson.SimpleProfile.stepIntegral` — its compensated integral over a step.

## Main statements

* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2_of_memLp` — approximation of a
  square-integrable mark profile by simple profiles.
* `LevyStochCalc.Poisson.exists_simpleProfile_tendsto_L2` — approximation of a bounded
  square-integrable mark profile by simple profiles obeying the same bound.
* `LevyStochCalc.Poisson.SimpleProfile.integral_stepIntegral_mul` — the `L²(P)` pairing of two
  compensated step integrals.
* `LevyStochCalc.Poisson.SimpleProfile.eLpNorm_stepIntegral_sub` — the isometry
  `‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`.
* `LevyStochCalc.Poisson.exists_memLp_tendsto_stepIntegral` — convergence of the compensated
  integrals in `L²(P)`.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- The reference intensity of a step of the time axis times a mark set. -/
theorem referenceIntensity_Ioc_prod' (A : Set E) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    referenceIntensity ν (Set.Ioc a b ×ˢ A) = ENNReal.ofReal (b - a) * ν A := by
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  congr 1
  rw [show Set.Ioc a b ∩ Set.Ici (0 : ℝ) = Set.Ioc a b from by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Ici, and_iff_left_iff_imp]
    exact fun h => ha.trans h.1.le]
  rw [Real.volume_Ioc]

/-- A simple mark profile: finitely many pairwise disjoint mark sets of finite intensity
carrying constant coefficients. -/
structure SimpleProfile (E : Type v) [MeasurableSpace E] (ν : Measure E) where
  /-- Number of mark sets. -/
  K : ℕ
  /-- The mark sets. -/
  B : Fin K → Set E
  B_measurable : ∀ k, MeasurableSet (B k)
  B_disjoint : Pairwise fun k l => Disjoint (B k) (B l)
  B_finite : ∀ k, ν (B k) ≠ ⊤
  /-- The coefficients. -/
  c : Fin K → ℝ

namespace SimpleProfile

/-- The mark function carried by a simple profile. -/
noncomputable def toFun (G : SimpleProfile E ν) (e : E) : ℝ :=
  ∑ k, G.c k * (G.B k).indicator (fun _ => (1 : ℝ)) e

omit [SigmaFinite ν] in
/-- The function of a simple profile is measurable. -/
theorem measurable_toFun (G : SimpleProfile E ν) : Measurable G.toFun :=
  Finset.measurable_sum _ fun k _ =>
    (measurable_const.indicator (G.B_measurable k)).const_mul _

omit [SigmaFinite ν] in
/-- The function of a simple profile is square integrable. -/
theorem memLp_toFun (G : SimpleProfile E ν) : MemLp G.toFun 2 ν :=
  memLp_finsetSum _ fun k _ =>
    (memLp_indicator_const 2 (G.B_measurable k) (1 : ℝ) (Or.inr (G.B_finite k))).const_mul _

/-- The indicator of an intersection as a product of indicators. -/
private theorem indicator_one_mul {α : Type*} (s t : Set α) (e : α) :
    s.indicator (fun _ => (1 : ℝ)) e * t.indicator (fun _ => (1 : ℝ)) e
      = (s ∩ t).indicator (fun _ => (1 : ℝ)) e := by
  by_cases hs : e ∈ s <;> by_cases ht : e ∈ t <;> simp [hs, ht]

omit [SigmaFinite ν] in
/-- The pointwise product of the functions of two simple profiles, through the indicators of
the intersections of their mark sets. -/
theorem toFun_mul (G G' : SimpleProfile E ν) (e : E) :
    G.toFun e * G'.toFun e
      = ∑ k, ∑ l, G.c k * G'.c l * (G.B k ∩ G'.B l).indicator (fun _ => (1 : ℝ)) e := by
  rw [toFun, toFun, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← indicator_one_mul (G.B k) (G'.B l) e]
  ring

omit [SigmaFinite ν] in
/-- The `L²(ν)` pairing of the functions of two simple profiles through the intensities of the
intersections of their mark sets. -/
theorem integral_toFun_mul (G G' : SimpleProfile E ν) :
    ∫ e, G.toFun e * G'.toFun e ∂ν
      = ∑ k, ∑ l, G.c k * G'.c l * (ν (G.B k ∩ G'.B l)).toReal := by
  have hmeas : ∀ (k : Fin G.K) (l : Fin G'.K), MeasurableSet (G.B k ∩ G'.B l) :=
    fun k l => (G.B_measurable k).inter (G'.B_measurable l)
  have hfin : ∀ (k : Fin G.K) (l : Fin G'.K), ν (G.B k ∩ G'.B l) ≠ ⊤ :=
    fun k l => ne_top_of_le_ne_top (G.B_finite k) (measure_mono Set.inter_subset_left)
  have hint : ∀ (k : Fin G.K) (l : Fin G'.K),
      Integrable (fun e => G.c k * G'.c l
        * (G.B k ∩ G'.B l).indicator (fun _ => (1 : ℝ)) e) ν := fun k l =>
    Integrable.const_mul (memLp_one_iff_integrable.1
      (memLp_indicator_const 1 (hmeas k l) (1 : ℝ) (Or.inr (hfin k l)))) _
  simp_rw [toFun_mul]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, integral_indicator_const (1 : ℝ) (hmeas k l), smul_eq_mul, mul_one,
    measureReal_def]

/-! ### The compensated integral of a simple profile over a step -/

/-- The compensated integral of a simple mark profile over the step `(a, b]`. -/
noncomputable def stepIntegral (G : SimpleProfile E ν) (N : PoissonRandomMeasure P ν)
    (a b : ℝ) (ω : Ω) : ℝ :=
  ∑ k, G.c k * N.compensated (Set.Ioc a b ×ˢ G.B k) ω

variable (N : PoissonRandomMeasure P ν)

/-- The compensated measure of a step times a mark set of a simple profile is square
integrable. -/
theorem memLp_compensated_step (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ)
    (k : Fin G.K) :
    MemLp (fun ω => N.compensated (Set.Ioc a b ×ˢ G.B k) ω) 2 P :=
  Compensated.compensated_memLp N (measurableSet_Ioc.prod (G.B_measurable k))
    (by rw [referenceIntensity_Ioc_prod' _ ha]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k))

/-- The compensated step integral of a simple mark profile is square integrable. -/
theorem memLp_stepIntegral (G : SimpleProfile E ν) {a : ℝ} (ha : 0 ≤ a) (b : ℝ) :
    MemLp (G.stepIntegral N a b) 2 P :=
  memLp_finsetSum _ fun k _ => (G.memLp_compensated_step N ha b k).const_mul _

/-- The `L²(P)` pairing of the compensated step integrals of two simple mark profiles is the
step length times their `L²(ν)` pairing. -/
theorem integral_stepIntegral_mul (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ ω, G.stepIntegral N a b ω * G'.stepIntegral N a b ω ∂P
      = (b - a) * ∫ e, G.toFun e * G'.toFun e ∂ν := by
  have hmemk : ∀ k : Fin G.K, MemLp (fun ω => G.c k
      * N.compensated (Set.Ioc a b ×ˢ G.B k) ω) 2 P :=
    fun k => (G.memLp_compensated_step N ha b k).const_mul _
  have hmeml : ∀ l : Fin G'.K, MemLp (fun ω => G'.c l
      * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω) 2 P :=
    fun l => (G'.memLp_compensated_step N ha b l).const_mul _
  have hint : ∀ (k : Fin G.K) (l : Fin G'.K), Integrable (fun ω =>
      (G.c k * N.compensated (Set.Ioc a b ×ˢ G.B k) ω)
        * (G'.c l * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω)) P :=
    fun k l => (hmemk k).integrable_mul (hmeml l)
  have hcross : ∀ (k : Fin G.K) (l : Fin G'.K),
      ∫ ω, N.compensated (Set.Ioc a b ×ˢ G.B k) ω
        * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω ∂P
        = (b - a) * (ν (G.B k ∩ G'.B l)).toReal := by
    intro k l
    rw [Compensated.compensated_cross_covariance N (measurableSet_Ioc.prod (G.B_measurable k))
      (measurableSet_Ioc.prod (G'.B_measurable l))
      (by rw [referenceIntensity_Ioc_prod' _ ha]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G.B_finite k))
      (by rw [referenceIntensity_Ioc_prod' _ ha]
          exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (G'.B_finite l))]
    rw [Set.prod_inter_prod, Set.inter_self, referenceIntensity_Ioc_prod' _ ha,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)]
  simp_rw [stepIntegral, Fintype.sum_mul_sum]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint k l,
    integral_toFun_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint k l, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [show (fun ω => (G.c k * N.compensated (Set.Ioc a b ×ˢ G.B k) ω)
        * (G'.c l * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω))
      = fun ω => (G.c k * G'.c l) * (N.compensated (Set.Ioc a b ×ˢ G.B k) ω
        * N.compensated (Set.Ioc a b ×ˢ G'.B l) ω) from by funext ω; ring,
    integral_const_mul, hcross k l]
  ring

/-- Expansion of the integral of the square of a difference. -/
private theorem integral_sub_sq_aux {α : Type*} [MeasurableSpace α] (m : Measure α)
    (F F' : α → ℝ) (h11 : Integrable (fun x => F x * F x) m)
    (h12 : Integrable (fun x => F x * F' x) m) (h21 : Integrable (fun x => F' x * F x) m)
    (h22 : Integrable (fun x => F' x * F' x) m) :
    ∫ x, (F x - F' x) ^ 2 ∂m
      = ∫ x, F x * F x ∂m - ∫ x, F x * F' x ∂m - ∫ x, F' x * F x ∂m + ∫ x, F' x * F' x ∂m := by
  have h2 : Integrable (fun x => F x * F x - F x * F' x) m := h11.sub h12
  have h1 : Integrable (fun x => F x * F x - F x * F' x - F' x * F x) m := h2.sub h21
  rw [show (fun x => (F x - F' x) ^ 2)
      = fun x => F x * F x - F x * F' x - F' x * F x + F' x * F' x from by funext x; ring,
    integral_add h1 h22, integral_sub h2 h21, integral_sub h11 h12]

/-- **The isometry at a step, in second-moment form.** The second moment of the difference of
the compensated step integrals of two simple mark profiles is the step length times the
`L²(ν)` distance of their functions, squared. -/
theorem integral_stepIntegral_sub_sq (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    ∫ ω, (G.stepIntegral N a b ω - G'.stepIntegral N a b ω) ^ 2 ∂P
      = (b - a) * ∫ e, (G.toFun e - G'.toFun e) ^ 2 ∂ν := by
  have hP : ∀ H H' : SimpleProfile E ν, Integrable (fun ω =>
      H.stepIntegral N a b ω * H'.stepIntegral N a b ω) P :=
    fun H H' => (H.memLp_stepIntegral N ha b).integrable_mul (H'.memLp_stepIntegral N ha b)
  have hν : ∀ H H' : SimpleProfile E ν, Integrable (fun e => H.toFun e * H'.toFun e) ν :=
    fun H H' => H.memLp_toFun.integrable_mul H'.memLp_toFun
  rw [integral_sub_sq_aux P _ _ (hP G G) (hP G G') (hP G' G) (hP G' G'),
    integral_sub_sq_aux ν _ _ (hν G G) (hν G G') (hν G' G) (hν G' G'),
    integral_stepIntegral_mul N G G ha hab, integral_stepIntegral_mul N G G' ha hab,
    integral_stepIntegral_mul N G' G ha hab, integral_stepIntegral_mul N G' G' ha hab]
  ring

/-- The `L²` seminorm of a square-integrable real function through its second moment. -/
private theorem eLpNorm_two_eq_ofReal {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F : α → ℝ} (hF : MemLp F 2 m) :
    eLpNorm F 2 m = (ENNReal.ofReal (∫ x, F x ^ 2 ∂m)) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    show (2 : ℝ≥0∞).toReal = 2 from by norm_num,
    ← Compensated.lintegral_sq_eq_ofReal_integral hF]
  refine congrArg (fun x : ℝ≥0∞ => x ^ (1 / 2 : ℝ)) (lintegral_congr fun x => ?_)
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rfl

/-- **The isometry at a step.** The `L²(P)` distance of the compensated step integrals of two
simple mark profiles is the square root of the step length times their `L²(ν)` distance. -/
theorem eLpNorm_stepIntegral_sub (G G' : SimpleProfile E ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) :
    eLpNorm (fun ω => G.stepIntegral N a b ω - G'.stepIntegral N a b ω) 2 P
      = ENNReal.ofReal (Real.sqrt (b - a))
        * eLpNorm (fun e => G.toFun e - G'.toFun e) 2 ν := by
  have hba : (0 : ℝ) ≤ b - a := by linarith
  have hPsub : MemLp (fun ω => G.stepIntegral N a b ω - G'.stepIntegral N a b ω) 2 P :=
    (G.memLp_stepIntegral N ha b).sub (G'.memLp_stepIntegral N ha b)
  have hνsub : MemLp (fun e => G.toFun e - G'.toFun e) 2 ν := G.memLp_toFun.sub G'.memLp_toFun
  rw [eLpNorm_two_eq_ofReal hPsub, eLpNorm_two_eq_ofReal hνsub,
    integral_stepIntegral_sub_sq N G G' ha hab,
    ENNReal.ofReal_mul hba, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg hba (by norm_num : (0 : ℝ) ≤ 1 / 2), Real.sqrt_eq_rpow]

/-! ### Simple profiles from simple functions -/

/-- The nonzero values of a simple function on the mark space, indexed by a finite type. -/
private noncomputable def nzValue (g : SimpleFunc E ℝ) : Fin (g.range.erase 0).card → ℝ :=
  fun k => (((g.range.erase 0).equivFin.symm k : {x // x ∈ g.range.erase 0}) : ℝ)

private theorem nzValue_injective (g : SimpleFunc E ℝ) : Function.Injective (nzValue g) :=
  fun _ _ hkl => (g.range.erase 0).equivFin.symm.injective (Subtype.ext hkl)

private theorem nzValue_ne_zero (g : SimpleFunc E ℝ) (k : Fin (g.range.erase 0).card) :
    nzValue g k ≠ 0 :=
  Finset.ne_of_mem_erase ((g.range.erase 0).equivFin.symm k).2

private theorem sum_nzValue_indicator (g : SimpleFunc E ℝ) (e : E) :
    ∑ k, nzValue g k * (g ⁻¹' {nzValue g k}).indicator (fun _ => (1 : ℝ)) e = g e := by
  classical
  by_cases h0 : g e = 0
  · refine (Finset.sum_eq_zero fun k _ => ?_).trans h0.symm
    rw [Set.indicator_of_notMem (by
      simp only [Set.mem_preimage, Set.mem_singleton_iff, h0]
      exact fun hc => nzValue_ne_zero g k hc.symm), mul_zero]
  · have hmem : g e ∈ g.range.erase 0 := Finset.mem_erase.2 ⟨h0, g.mem_range_self e⟩
    have hvk : nzValue g ((g.range.erase 0).equivFin ⟨g e, hmem⟩) = g e := by
      simp [nzValue]
    refine (Finset.sum_eq_single ((g.range.erase 0).equivFin ⟨g e, hmem⟩)
      (fun k _ hk => ?_) (fun h => absurd (Finset.mem_univ _) h)).trans ?_
    · rw [Set.indicator_of_notMem (by
        simp only [Set.mem_preimage, Set.mem_singleton_iff]
        exact fun hc => hk (nzValue_injective g (hvk.trans hc)).symm), mul_zero]
    · rw [Set.indicator_of_mem (by simp [hvk]), mul_one, hvk]

/-- The simple mark profile carried by the nonzero level sets of a square-integrable simple
function on the mark space. -/
noncomputable def ofSimpleFunc {g : SimpleFunc E ℝ} (hg : MemLp g 2 ν) : SimpleProfile E ν where
  K := (g.range.erase 0).card
  B := fun k => g ⁻¹' {nzValue g k}
  B_measurable := fun k => g.measurableSet_fiber _
  B_disjoint := fun k l hkl => Set.disjoint_left.2 fun e he he' => by
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at he he'
    exact hkl (nzValue_injective g (he.symm.trans he'))
  B_finite := fun k => (SimpleFunc.measure_preimage_lt_top_of_memLp (by norm_num) (by norm_num)
    g hg _ (nzValue_ne_zero g k)).ne
  c := nzValue g

omit [SigmaFinite ν] in
@[simp] theorem toFun_ofSimpleFunc {g : SimpleFunc E ℝ} (hg : MemLp g 2 ν) (e : E) :
    (ofSimpleFunc hg).toFun e = g e :=
  sum_nzValue_indicator g e

end SimpleProfile

/-! ### Approximation of a square-integrable mark profile -/

omit [SigmaFinite ν] in
/-- **Simple-profile approximation.** A square-integrable mark profile is the `L²(ν)` limit of
simple mark profiles. -/
theorem exists_simpleProfile_tendsto_L2_of_memLp {f : E → ℝ} (hf : MemLp f 2 ν) :
    ∃ G : ℕ → SimpleProfile E ν,
      Filter.Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν)
        Filter.atTop (nhds 0) := by
  have hε : ∀ n : ℕ, (n : ℝ≥0∞)⁻¹ ≠ 0 := fun n =>
    ENNReal.inv_ne_zero.2 (ENNReal.natCast_ne_top n)
  choose g hg hgm using fun n : ℕ =>
    hf.exists_simpleFunc_eLpNorm_sub_lt (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hε n)
  refine ⟨fun n => SimpleProfile.ofSimpleFunc (hgm n), ?_⟩
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    ENNReal.tendsto_inv_nat_nhds_zero (fun _ => zero_le) fun n => ?_
  calc eLpNorm (fun e => (SimpleProfile.ofSimpleFunc (hgm n)).toFun e - f e) 2 ν
      = eLpNorm (f - ⇑(g n)) 2 ν := by
        rw [← eLpNorm_neg]
        congr 1
        funext e
        simp
    _ ≤ (n : ℝ≥0∞)⁻¹ := (hg n).le

omit [SigmaFinite ν] in
/-- **Simple-profile approximation.** A bounded square-integrable mark profile is the `L²(ν)`
limit of simple mark profiles obeying the same bound. -/
theorem exists_simpleProfile_tendsto_L2 {f : E → ℝ} (hf : MemLp f 2 ν) {Cb : ℝ}
    (hb : ∀ e, |f e| ≤ Cb) :
    ∃ G : ℕ → SimpleProfile E ν, (∀ n e, |(G n).toFun e| ≤ Cb) ∧
      Filter.Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν)
        Filter.atTop (nhds 0) := by
  rcases le_or_gt 0 Cb with hCb | hCb
  · have h₀ : (0 : ℝ) ∈ Set.Icc (-Cb) Cb := Set.mem_Icc.2 ⟨by linarith, hCb⟩
    set f₀ : E → ℝ := fun e => max (-Cb) (min Cb (hf.1.mk f e)) with hf₀def
    have hf₀m : Measurable f₀ :=
      measurable_const.max (measurable_const.min hf.1.stronglyMeasurable_mk.measurable)
    have hf₀s : ∀ e, f₀ e ∈ Set.Icc (-Cb) Cb := fun e =>
      Set.mem_Icc.2 ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
    have hf₀ae : f₀ =ᵐ[ν] f := by
      filter_upwards [hf.1.ae_eq_mk] with e he
      have h1 := abs_le.1 (hb e)
      simp only [hf₀def, ← he]
      rw [min_eq_right h1.2, max_eq_right h1.1]
    have hf₀L : MemLp f₀ 2 ν := MemLp.ae_eq hf₀ae.symm hf
    have happrox : ∀ n, MemLp (SimpleFunc.approxOn f₀ hf₀m (Set.Icc (-Cb) Cb) 0 h₀ n) 2 ν :=
      fun n => SimpleFunc.memLp_approxOn hf₀m hf₀L h₀ (by simp) n
    refine ⟨fun n => SimpleProfile.ofSimpleFunc (happrox n), fun n e => ?_, ?_⟩
    · rw [SimpleProfile.toFun_ofSimpleFunc]
      exact abs_le.2 (Set.mem_Icc.1 (SimpleFunc.approxOn_mem hf₀m h₀ n e))
    · have htend := SimpleFunc.tendsto_approxOn_Lp_eLpNorm hf₀m h₀ (p := 2) (by norm_num)
        (Filter.Eventually.of_forall fun e => subset_closure (hf₀s e))
        (by simpa using hf₀L.eLpNorm_lt_top)
      refine htend.congr fun n => eLpNorm_congr_ae ?_
      filter_upwards [hf₀ae] with e he
      simp [he]
  · have hE : IsEmpty E := ⟨fun e => absurd ((abs_nonneg (f e)).trans (hb e)) (not_le.2 hCb)⟩
    have hν0 : ν = 0 := by
      ext s _
      rw [Set.eq_empty_of_isEmpty s]
      simp
    exact ⟨fun _ => ⟨0, fun k => k.elim0, fun k => k.elim0, fun k => k.elim0,
      fun k => k.elim0, fun k => k.elim0⟩, fun _ e => (hE.false e).elim,
      by simp [hν0]⟩

/-! ### Convergence of the compensated step integrals -/

/-- **Compensated step integrals of converging profiles converge.** If simple mark profiles
converge in `L²(ν)` to a square-integrable mark profile, their compensated integrals over a
common step converge in `L²(P)`. -/
theorem exists_memLp_tendsto_stepIntegral (N : PoissonRandomMeasure P ν)
    (G : ℕ → SimpleProfile E ν) {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hG : Filter.Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν)
      Filter.atTop (nhds 0)) :
    ∃ J : Ω → ℝ, MemLp J 2 P ∧
      Filter.Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
        Filter.atTop (nhds 0) := by
  set u : ℕ → Lp ℝ 2 P := fun n => ((G n).memLp_stepIntegral N ha b).toLp _
  have hcoe : ∀ n, ⇑(u n) =ᵐ[P] (G n).stepIntegral N a b :=
    fun n => MemLp.coeFn_toLp ((G n).memLp_stepIntegral N ha b)
  have hstep : ∀ m n, eLpNorm (⇑(u m) - ⇑(u n)) 2 P
      = ENNReal.ofReal (Real.sqrt (b - a))
        * eLpNorm (fun e => (G m).toFun e - (G n).toFun e) 2 ν := by
    intro m n
    rw [← SimpleProfile.eLpNorm_stepIntegral_sub N (G m) (G n) ha hab]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hcoe m, hcoe n] with ω h1 h2
    simp [h1, h2]
  have hbound : ∀ m n, eLpNorm (fun e => (G m).toFun e - (G n).toFun e) 2 ν
      ≤ eLpNorm (fun e => (G m).toFun e - f e) 2 ν
        + eLpNorm (fun e => (G n).toFun e - f e) 2 ν := by
    intro m n
    have hm : MemLp (fun e => (G m).toFun e - f e) 2 ν := (G m).memLp_toFun.sub hf
    have hn : MemLp (fun e => (G n).toFun e - f e) 2 ν := (G n).memLp_toFun.sub hf
    calc eLpNorm (fun e => (G m).toFun e - (G n).toFun e) 2 ν
        = eLpNorm ((fun e => (G m).toFun e - f e) - fun e => (G n).toFun e - f e) 2 ν := by
          refine eLpNorm_congr_ae (Filter.Eventually.of_forall fun e => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le hm.aestronglyMeasurable hn.aestronglyMeasurable one_le_two
  have hfst : Filter.Tendsto
      (fun mn : ℕ × ℕ => eLpNorm (fun e => (G mn.1).toFun e - f e) 2 ν)
      Filter.atTop (nhds 0) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact hG.comp Filter.tendsto_fst
  have hsnd : Filter.Tendsto
      (fun mn : ℕ × ℕ => eLpNorm (fun e => (G mn.2).toFun e - f e) 2 ν)
      Filter.atTop (nhds 0) := by
    rw [← Filter.prod_atTop_atTop_eq]
    exact hG.comp Filter.tendsto_snd
  have hsum : Filter.Tendsto (fun mn : ℕ × ℕ => ENNReal.ofReal (Real.sqrt (b - a))
      * (eLpNorm (fun e => (G mn.1).toFun e - f e) 2 ν
        + eLpNorm (fun e => (G mn.2).toFun e - f e) 2 ν)) Filter.atTop (nhds 0) := by
    have := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt (b - a)))
      (hfst.add hsnd) (Or.inr ENNReal.ofReal_ne_top)
    simpa using this
  have hcauchy : CauchySeq u := by
    rw [Lp.cauchySeq_Lp_iff_cauchySeq_eLpNorm]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
      (fun _ => by simp) fun mn => ?_
    rw [hstep]
    exact _root_.mul_le_mul_right (hbound mn.1 mn.2) _
  obtain ⟨J, hJ⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨⇑J, Lp.memLp J, ?_⟩
  refine ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' u J).1 hJ).congr fun n => eLpNorm_congr_ae ?_
  filter_upwards [hcoe n] with ω h1
  simp [h1]

end LevyStochCalc.Poisson
