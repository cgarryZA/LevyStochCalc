/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.ProfileCharacter

/-!
# The compensated integral of a deterministic mark profile over a step

The compensated step integrals of simple mark profiles obey the isometry
`‖J(f) − J(g)‖_{L²(P)} = √(b − a) ‖f − g‖_{L²(ν)}`, so an `L²(P)` limit of the compensated step
integrals of simple profiles converging in `L²(ν)` is determined, up to a null set, by the limit
profile alone. That limit is the compensated integral over the step `(a, b]` of a
square-integrable deterministic mark profile `f : E → ℝ` against a Poisson random measure with
intensity `ν`. It agrees with the compensated step integral at a simple profile and carries the
Lévy character

  `E[exp (i u J(f))] = exp ((b − a) ∫ (exp (i u f) − 1 − i u f) dν)`.

## Main definitions

* `LevyStochCalc.Poisson.IsCompensatedProfile` — being a strongly measurable `L²(P)` limit at a
  step of the compensated step integrals of every sequence of simple mark profiles converging to
  a mark profile in `L²(ν)`.
* `LevyStochCalc.Poisson.compensatedProfile` — the compensated integral of a square-integrable
  deterministic mark profile over a step.

## Main statements

* `LevyStochCalc.Poisson.ae_eq_of_tendsto_stepIntegral` — an `L²(P)` limit of the compensated
  step integrals of simple profiles converging in `L²(ν)` depends only on the limit profile.
* `LevyStochCalc.Poisson.stronglyMeasurable_compensatedProfile`,
  `LevyStochCalc.Poisson.memLp_compensatedProfile` — measurability and square integrability.
* `LevyStochCalc.Poisson.tendsto_stepIntegral_compensatedProfile` — the compensated step
  integrals of simple profiles converging to a profile in `L²(ν)` converge to its compensated
  integral in `L²(P)`.
* `LevyStochCalc.Poisson.compensatedProfile_toFun` — agreement with the compensated step
  integral at a simple mark profile.
* `LevyStochCalc.Poisson.integral_exp_I_mul_compensatedProfile` — the Lévy character of the
  compensated integral of a mark profile over a step.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-! ### Independence of the approximating sequence -/

/-- The `L²` seminorm of a difference through two intermediate functions. -/
private theorem eLpNorm_sub_le_three {α : Type*} [MeasurableSpace α] {m : Measure α}
    {F H X Y : α → ℝ} (h1 : AEStronglyMeasurable (fun x => X x - F x) m)
    (h2 : AEStronglyMeasurable (fun x => X x - Y x) m)
    (h3 : AEStronglyMeasurable (fun x => Y x - H x) m) :
    eLpNorm (fun x => F x - H x) 2 m
      ≤ eLpNorm (fun x => X x - F x) 2 m + eLpNorm (fun x => X x - Y x) 2 m
        + eLpNorm (fun x => Y x - H x) 2 m := by
  have hsplit : (fun x => F x - H x)
      = -((fun x => X x - F x) - ((fun x => X x - Y x) + fun x => Y x - H x)) := by
    funext x
    simp only [Pi.neg_apply, Pi.sub_apply, Pi.add_apply]
    ring
  rw [hsplit, eLpNorm_neg, add_assoc]
  refine (eLpNorm_sub_le h1 (h2.add h3) one_le_two).trans ?_
  gcongr
  exact eLpNorm_add_le h2 h3 one_le_two

/-- **The `L²(P)` limit depends only on the limit profile.** Two sequences of simple mark
profiles converging in `L²(ν)` to the same square-integrable mark profile have compensated step
integrals with the same `L²(P)` limit over a common step. -/
theorem ae_eq_of_tendsto_stepIntegral (N : PoissonRandomMeasure P ν)
    {G G' : ℕ → SimpleProfile E ν} {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) {J J' : Ω → ℝ} (hJ : MemLp J 2 P) (hJ' : MemLp J' 2 P)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hG' : Tendsto (fun n => eLpNorm (fun e => (G' n).toFun e - f e) 2 ν) atTop (nhds 0))
    (hJlim : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
      atTop (nhds 0))
    (hJ'lim : Tendsto (fun n => eLpNorm (fun ω => (G' n).stepIntegral N a b ω - J' ω) 2 P)
      atTop (nhds 0)) :
    J =ᵐ[P] J' := by
  have hmid : ∀ n, eLpNorm (fun ω => (G n).stepIntegral N a b ω
      - (G' n).stepIntegral N a b ω) 2 P
      ≤ ENNReal.ofReal (Real.sqrt (b - a))
        * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
          + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν) := by
    intro n
    rw [SimpleProfile.eLpNorm_stepIntegral_sub N (G n) (G' n) ha hab]
    gcongr
    calc eLpNorm (fun e => (G n).toFun e - (G' n).toFun e) 2 ν
        = eLpNorm ((fun e => (G n).toFun e - f e) - fun e => (G' n).toFun e - f e) 2 ν := by
          refine eLpNorm_congr_ae (Eventually.of_forall fun e => ?_)
          simp only [Pi.sub_apply]
          ring
      _ ≤ _ := eLpNorm_sub_le ((G n).memLp_toFun.sub hf).aestronglyMeasurable
          ((G' n).memLp_toFun.sub hf).aestronglyMeasurable one_le_two
  have hbound : ∀ n, eLpNorm (fun ω => J ω - J' ω) 2 P
      ≤ eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P
        + ENNReal.ofReal (Real.sqrt (b - a))
          * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
            + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν)
        + eLpNorm (fun ω => (G' n).stepIntegral N a b ω - J' ω) 2 P := by
    intro n
    refine (eLpNorm_sub_le_three
      (((G n).memLp_stepIntegral N ha b).sub hJ).aestronglyMeasurable
      (((G n).memLp_stepIntegral N ha b).sub
        ((G' n).memLp_stepIntegral N ha b)).aestronglyMeasurable
      (((G' n).memLp_stepIntegral N ha b).sub hJ').aestronglyMeasurable).trans ?_
    gcongr
    exact hmid n
  have hzero : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P
      + ENNReal.ofReal (Real.sqrt (b - a))
        * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
          + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν)
      + eLpNorm (fun ω => (G' n).stepIntegral N a b ω - J' ω) 2 P) atTop (nhds 0) := by
    have hprod : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (b - a))
        * (eLpNorm (fun e => (G n).toFun e - f e) 2 ν
          + eLpNorm (fun e => (G' n).toFun e - f e) 2 ν)) atTop (nhds 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal (Real.sqrt (b - a)))
        (hG.add hG') (Or.inr ENNReal.ofReal_ne_top)
      simpa using h
    simpa using (hJlim.add hprod).add hJ'lim
  have h0 : eLpNorm (fun ω => J ω - J' ω) 2 P = 0 :=
    le_antisymm (ge_of_tendsto hzero (Eventually.of_forall hbound)) zero_le
  have hae := (eLpNorm_eq_zero_iff (hJ.sub hJ').aestronglyMeasurable (by norm_num)).1 h0
  filter_upwards [hae] with ω hω
  simpa [sub_eq_zero] using hω

/-! ### The compensated integral of a mark profile over a step -/

/-- The property of being a strongly measurable square-integrable `L²(P)` limit over the step
`(a, b]` of the compensated step integrals of every sequence of simple mark profiles converging
to `f` in `L²(ν)`. -/
def IsCompensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) (J : Ω → ℝ) :
    Prop :=
  StronglyMeasurable J ∧ MemLp J 2 P ∧ ∀ G : ℕ → SimpleProfile E ν,
    Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0) →
    Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P) atTop (nhds 0)

open scoped Classical in
/-- The compensated integral over the step `(a, b]` of a square-integrable deterministic mark
profile `f` against a Poisson random measure with intensity `ν`: the `L²(P)` limit of the
compensated step integrals of any sequence of simple mark profiles converging to `f` in `L²(ν)`.
Where no such sequence exists the value is unspecified. -/
noncomputable def compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) :
    Ω → ℝ :=
  if h : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J then h.choose else 0

/-- The compensated integral of a mark profile over a step is strongly measurable. -/
theorem stronglyMeasurable_compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ)
    (a b : ℝ) : StronglyMeasurable (compensatedProfile N f a b) := by
  by_cases h : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J
  · rw [show compensatedProfile N f a b = h.choose from dif_pos h]
    exact h.choose_spec.1
  · rw [show compensatedProfile N f a b = 0 from dif_neg h]
    exact stronglyMeasurable_const

/-- The compensated integral of a mark profile over a step is measurable. -/
theorem measurable_compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) :
    Measurable (compensatedProfile N f a b) :=
  (stronglyMeasurable_compensatedProfile N f a b).measurable

/-- The compensated integral of a mark profile over a step is square integrable. -/
theorem memLp_compensatedProfile (N : PoissonRandomMeasure P ν) (f : E → ℝ) (a b : ℝ) :
    MemLp (compensatedProfile N f a b) 2 P := by
  by_cases h : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J
  · rw [show compensatedProfile N f a b = h.choose from dif_pos h]
    exact h.choose_spec.2.1
  · rw [show compensatedProfile N f a b = 0 from dif_neg h]
    exact MemLp.zero

/-- The compensated integral of a square-integrable mark profile approximated in `L²(ν)` by
simple mark profiles is an `L²(P)` limit of their compensated step integrals. -/
theorem isCompensatedProfile_compensatedProfile (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (G : ℕ → SimpleProfile E ν)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0)) :
    IsCompensatedProfile N f a b (compensatedProfile N f a b) := by
  have hex : ∃ J : Ω → ℝ, IsCompensatedProfile N f a b J := by
    obtain ⟨J₀, hJ₀, hJ₀lim⟩ := exists_memLp_tendsto_stepIntegral N G hf ha hab hG
    set J := hJ₀.1.mk J₀
    have hJae : J₀ =ᵐ[P] J := hJ₀.1.ae_eq_mk
    have hJ : MemLp J 2 P := MemLp.ae_eq hJae hJ₀
    have hJlim : Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω - J ω) 2 P)
        atTop (nhds 0) := by
      refine hJ₀lim.congr fun n => eLpNorm_congr_ae ?_
      filter_upwards [hJae] with ω hω
      simp [hω]
    refine ⟨J, hJ₀.1.stronglyMeasurable_mk, hJ, fun G' hG' => ?_⟩
    obtain ⟨J', hJ', hJ'lim⟩ := exists_memLp_tendsto_stepIntegral N G' hf ha hab hG'
    have hJJ' : J' =ᵐ[P] J :=
      ae_eq_of_tendsto_stepIntegral N hf ha hab hJ' hJ hG' hG hJ'lim hJlim
    refine hJ'lim.congr fun n => eLpNorm_congr_ae ?_
    filter_upwards [hJJ'] with ω hω
    simp [hω]
  rw [show compensatedProfile N f a b = hex.choose from dif_pos hex]
  exact hex.choose_spec

/-- **The defining convergence.** The compensated step integrals of simple mark profiles
converging to a square-integrable mark profile in `L²(ν)` converge in `L²(P)` to its compensated
integral over the step. -/
theorem tendsto_stepIntegral_compensatedProfile (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (G : ℕ → SimpleProfile E ν)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0)) :
    Tendsto (fun n => eLpNorm (fun ω => (G n).stepIntegral N a b ω
      - compensatedProfile N f a b ω) 2 P) atTop (nhds 0) :=
  (isCompensatedProfile_compensatedProfile N hf ha hab G hG).2.2 G hG

/-- The compensated integral of a square-integrable mark profile over a step is an `L²(P)`
limit of the compensated step integrals of any sequence of simple mark profiles converging to the
profile in `L²(ν)`. -/
theorem isCompensatedProfile_compensatedProfile_of_memLp (N : PoissonRandomMeasure P ν)
    {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IsCompensatedProfile N f a b (compensatedProfile N f a b) := by
  obtain ⟨G, hG⟩ := exists_simpleProfile_tendsto_L2_of_memLp hf
  exact isCompensatedProfile_compensatedProfile N hf ha hab G hG

/-! ### Agreement at a simple mark profile -/

/-- At the mark function of a simple mark profile the compensated integral over a step is the
compensated step integral of that profile. -/
theorem compensatedProfile_toFun (N : PoissonRandomMeasure P ν) (G : SimpleProfile E ν)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    compensatedProfile N G.toFun a b =ᵐ[P] G.stepIntegral N a b := by
  have hconst : Tendsto
      (fun n : ℕ => eLpNorm (fun e => ((fun _ => G) n).toFun e - G.toFun e) 2 ν)
      atTop (nhds 0) := by
    simp
  have h := tendsto_stepIntegral_compensatedProfile N G.memLp_toFun ha hab (fun _ => G) hconst
  have h0 : eLpNorm (fun ω => G.stepIntegral N a b ω
      - compensatedProfile N G.toFun a b ω) 2 P = 0 :=
    (tendsto_nhds_unique h tendsto_const_nhds).symm
  have hsub : MemLp (fun ω => G.stepIntegral N a b ω
      - compensatedProfile N G.toFun a b ω) 2 P :=
    (G.memLp_stepIntegral N ha b).sub (memLp_compensatedProfile N G.toFun a b)
  have hae := (eLpNorm_eq_zero_iff hsub.aestronglyMeasurable (by norm_num)).1 h0
  filter_upwards [hae] with ω hω
  simp only [Pi.zero_apply, sub_eq_zero] at hω
  exact hω.symm

/-! ### The character -/

/-- **The character of the compensated integral of a mark profile over a step.** -/
theorem integral_exp_I_mul_compensatedProfile (N : PoissonRandomMeasure P ν) {f : E → ℝ}
    (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (G : ℕ → SimpleProfile E ν)
    (hG : Tendsto (fun n => eLpNorm (fun e => (G n).toFun e - f e) 2 ν) atTop (nhds 0))
    (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N f a b ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν) :=
  integral_exp_I_mul_of_tendsto_stepIntegral N G hf ha hab
    (memLp_compensatedProfile N f a b) hG
    (tendsto_stepIntegral_compensatedProfile N hf ha hab G hG) u

/-- The character of the compensated integral of a square-integrable mark profile over a
step. -/
theorem integral_exp_I_mul_compensatedProfile_of_memLp (N : PoissonRandomMeasure P ν)
    {f : E → ℝ} (hf : MemLp f 2 ν) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (u : ℝ) :
    ∫ ω, Complex.exp (Complex.I * ((u * compensatedProfile N f a b ω : ℝ) : ℂ)) ∂P
      = Complex.exp (((b - a : ℝ) : ℂ) * ∫ e, levyCharIntegrand u (f e) ∂ν) := by
  obtain ⟨G, hG⟩ := exists_simpleProfile_tendsto_L2_of_memLp hf
  exact integral_exp_I_mul_compensatedProfile N hf ha hab G hG u

end LevyStochCalc.Poisson
