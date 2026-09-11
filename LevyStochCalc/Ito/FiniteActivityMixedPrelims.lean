/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaMixedDictionary
import LevyStochCalc.Ito.JumpFormulaGeneralShift
import LevyStochCalc.Ito.CappedJumpSumMeasurable
import LevyStochCalc.Ito.JumpIntegrandLeftLim
import LevyStochCalc.Ito.JumpSplittingPath
import LevyStochCalc.Brownian.VectorItoTimeAug

/-!
# Preliminaries for the finite-activity Itô–Lévy identity in the mixed form

The small facts the finite-activity identity along a truncated path assembles from: the
left-limit jump sum of the mark-cut coefficient bundle is the prescribed-path jump sum along the
left limits; the left limit of the time-augmented path; the value of a progressively measurable
vector process at a stopping time is known at that time; the drift reconciliation for the mixed
integrands asked at almost every time only; and the bounds on the partial derivatives of the
time-augmented representative of a state function with bounded derivatives.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath`
* `LevyStochCalc.Ito.JumpFormula.leftLim_timeAugProcess_eq_cons`
* `LevyStochCalc.Ito.JumpFormula.measurable_stoppingTime_eval_untopA`
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_splitDrift_and_jumpSum_mixed_ae`
* `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv_timeAug_le`,
  `LevyStochCalc.Ito.JumpFormula.abs_coordDeriv₂_timeAug_mul_le`
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal
open LevyStochCalc.Ito.Setting LevyStochCalc.Probability LevyStochCalc.Brownian.Ito

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section JumpSum

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The left-limit jump sum over a mark set of the coefficient bundle cut to that set is the
prescribed-path jump sum along the left limits of the jump diffusion. -/
theorem jumpSumLeftAt_markCutγ_eq_jumpSumAt_leftLimPath (X : JumpDiffusion W N coeffs x₀)
    {B : Set E} (hB : MeasurableSet B) (t : ℝ) (ω : Ω) (i : Fin n) :
    JumpSplitting.jumpSumLeftAt (coeffs.markCutγ B) N X.X B t ω i
      = jumpSumAt X (JumpSplitting.leftLimPath X) B t ω i := by
  unfold JumpSplitting.jumpSumLeftAt jumpSumAt
  refine setIntegral_congr_fun (measurableSet_Ioc.prod hB) fun q hq => ?_
  rw [JumpDiffusionCoeffs.markCutγ_γ_apply, Set.indicator_of_mem hq.2]
  rfl

/-- The horizon clipped at an arrival time is the capped arrival time read back as a real. -/
theorem clipTime_jumpTime_eq_untopA (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (A : Set E) (T : ℝ) (k : ℕ) (ω : Ω) :
    clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω = (cappedJumpTime N A T k ω).untopA :=
  clipTime_eq_untopA_min _ _ _

end JumpSum

section LeftLimit

variable {Ω : Type u} {n : ℕ}

/-- The left limit of the time-augmented path is the time consed onto the left limit of the
path, at a time where every coordinate of the path has a left limit. -/
theorem leftLim_timeAugProcess_eq_cons (Z : ℝ → Ω → Fin n → ℝ) {ω : Ω} {t : ℝ}
    (h : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Z s ω i) (𝓝[<] t) (𝓝 L)) :
    Function.leftLim (fun s => timeAugProcess Z s ω) t
      = Fin.cons t (JumpSplitting.leftLimPathAt Z t ω) := by
  refine leftLim_eq_of_tendsto ?_
  refine tendsto_pi_nhds.mpr fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [timeAugProcess, Fin.cons_zero]
    exact tendsto_id.mono_left nhdsWithin_le_nhds
  | succ q =>
    simp only [timeAugProcess, Fin.cons_succ]
    exact JumpSplitting.tendsto_nhdsLT_leftLimPathAt h q

/-- A path that is right continuous on `[0, ∞)` and has left limits at the positive times
differs from its left limits at countably many positive times only. -/
theorem countable_setOf_pos_leftLimPathAt_ne {Z : ℝ → Ω → Fin n → ℝ} {ω : Ω}
    (hright : ∀ t : ℝ, 0 ≤ t → Tendsto (fun s => Z s ω) (𝓝[>] t) (𝓝 (Z t ω)))
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      ∃ L : ℝ, Tendsto (fun s => Z s ω i) (𝓝[<] t) (𝓝 L)) :
    {s : ℝ | 0 < s ∧ JumpSplitting.leftLimPathAt Z s ω ≠ Z s ω}.Countable := by
  have h := LevyStochCalc.Ito.countable_setOf_pos_ne_of_cadlag (f := fun s => Z s ω)
    (g := fun s => JumpSplitting.leftLimPathAt Z s ω) hright
    (fun t ht i => JumpSplitting.tendsto_nhdsLT_leftLimPathAt (hleft t ht) i)
  refine h.mono fun s hs => ?_
  simp only [Set.mem_setOf_eq] at hs ⊢
  exact ⟨hs.1, fun heq => hs.2 heq.symm⟩

/-- Two processes that meet a pair of processes at all but countably many positive times each
meet them jointly at all but countably many positive times. -/
theorem countable_setOf_pos_ne_pair {α β : Type*} {Y₁ Z₁ : ℝ → Ω → α} {Y₂ Z₂ : ℝ → Ω → β}
    {ω : Ω} (h₁ : {s : ℝ | 0 < s ∧ Y₁ s ω ≠ Z₁ s ω}.Countable)
    (h₂ : {s : ℝ | 0 < s ∧ Y₂ s ω ≠ Z₂ s ω}.Countable) :
    {s : ℝ | 0 < s ∧ (Y₁ s ω, Y₂ s ω) ≠ (Z₁ s ω, Z₂ s ω)}.Countable := by
  refine (h₁.union h₂).mono fun s hs => ?_
  by_contra hcon
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_and, not_not] at hcon
  exact hs.2 (Prod.ext (hcon.1 hs.1) (hcon.2 hs.1))

end LeftLimit

section StoppingTime

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {n : ℕ} {ℱ : Filtration ℝ mΩ}

/-- The value of a progressively measurable vector process at a stopping time is measurable for
the σ-algebra of that stopping time. -/
theorem measurable_stoppingTime_eval_untopA {Y : ℝ → Ω → Fin n → ℝ}
    (hY : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => Y s ω i)
    {σ : Ω → WithTop ℝ} (hσ : IsStoppingTime ℱ σ) :
    Measurable[hσ.measurableSpace] fun ω => Y (σ ω).untopA ω := by
  letI : MeasurableSpace Ω := hσ.measurableSpace
  refine measurable_pi_lambda _ fun i => ?_
  exact measurable_stoppedValue (hY i).isStronglyProgressive hσ

/-- Prepending a zero coordinate preserves measurability of a random vector. -/
theorem Measurable.finCons_zero {mΩ' : MeasurableSpace Ω} {c : Ω → Fin n → ℝ}
    (hc : Measurable[mΩ'] c) :
    Measurable[mΩ'] fun ω => (Fin.cons 0 (c ω) : Fin (n + 1) → ℝ) := by
  letI : MeasurableSpace Ω := mΩ'
  refine measurable_pi_lambda _ fun p => ?_
  induction p using Fin.cases with
  | zero =>
    simp only [Fin.cons_zero]
    exact measurable_const
  | succ q =>
    simp only [Fin.cons_succ]
    exact (measurable_pi_apply q).comp hc

end StoppingTime

section MixedAe

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- Along a pair of paths the mixed compensator-drift integral over a time window is the
intensity integral of the mixed jump increment minus the first-order term, when the mark
integrability holds at almost every time of the window. -/
theorem setIntegral_mixedCompensatorDrift_eq_sub_ae (A : Set E) (y x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν)
      = (∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν := by
  rw [← integral_sub hΔt hgt]
  refine integral_congr_ae ?_
  filter_upwards [hγ, hΔ] with s hγs hΔs
  exact setIntegral_mixedCompensatorDriftIntegrand_eq_sub A s (y s) (x s) hγs hΔs

/-- The drift reconciliation for the mixed integrands, with the mark integrability asked at
almost every time of the window only. -/
theorem setIntegral_firstOrder_add_mixedCompensatorDrift_ae (A : Set E)
    (y x : ℝ → Fin n → ℝ) (T : ℝ)
    (hγ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => γ s (x s) e i) A ν)
    (hΔ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => mixedJumpIncrement u γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn (fun s => ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume) :
    (∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (y s) i * ∫ e in A, γ s (x s) e i ∂ν)
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u γ s (y s) (x s) e ∂ν
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in A, mixedJumpIncrement u γ s (y s) (x s) e ∂ν := by
  have h := setIntegral_mixedCompensatorDrift_eq_sub_ae (u := u) (γ := γ) A y x T hγ hΔ hΔt hgt
  linarith

end MixedAe

section MixedAssemblyAe

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ} {coeffs : JumpDiffusionCoeffs n d E}

/-- The Itô–Lévy formula for the mixed integrands from the split-drift form, with the mark
integrability of the jump coefficient and of the mixed jump increment asked at almost every
time of the window only. -/
theorem itoLevy_of_splitDrift_and_jumpSum_mixed_ae {A : Set E} {y x : ℝ → Fin n → ℝ} {T : ℝ}
    {Dm Cm Js : ℝ}
    (hγ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ i : Fin n,
      IntegrableOn (fun e => coeffs.γ s (x s) e i) A ν)
    (hΔ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      IntegrableOn (fun e => mixedJumpIncrement u coeffs.γ s (y s) (x s) e) A ν)
    (hΔt : IntegrableOn
      (fun s => ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν)
      (Set.Icc (0 : ℝ) T) volume)
    (hgt : IntegrableOn (fun s => ∑ i : Fin n,
      gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν) (Set.Icc (0 : ℝ) T) volume)
    (hdt : IntegrableOn (fun s => mixedDriftIntegrand u coeffs s (y s) (x s))
      (Set.Icc (0 : ℝ) T) volume)
    (hsplit : u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
            - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
        + Dm + Js)
    (hjump : Js = Cm + ∫ s in Set.Icc (0 : ℝ) T,
      ∫ e in A, mixedJumpIncrement u coeffs.γ s (y s) (x s) e ∂ν) :
    u T (y T) - u 0 (y 0)
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s)) + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e in A, mixedCompensatorDriftIntegrand u coeffs.γ s (y s) (x s) e ∂ν := by
  have hcancel := setIntegral_firstOrder_add_mixedCompensatorDrift_ae (u := u) (γ := coeffs.γ)
    A y x T hγ hΔ hΔt hgt
  have hdsplit : (∫ s in Set.Icc (0 : ℝ) T, (mixedDriftIntegrand u coeffs s (y s) (x s)
        - ∑ i : Fin n, gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν))
      = (∫ s in Set.Icc (0 : ℝ) T, mixedDriftIntegrand u coeffs s (y s) (x s))
        - ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
            gradient u s (y s) i * ∫ e in A, coeffs.γ s (x s) e i ∂ν :=
    integral_sub hdt hgt
  rw [hdsplit] at hsplit
  rw [hjump] at hsplit
  linarith

end MixedAssemblyAe

section TimeAugBounds

variable {Ω : Type u} {n d : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ} {f : (Fin (n + 1) → ℝ) → ℝ}
  {f' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] ℝ}
  {f'' : (Fin (n + 1) → ℝ) → (Fin (n + 1) → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) →L[ℝ] ℝ}

/-- The time-augmented representative of a `C²` function of time and state is `C²`. -/
theorem contDiff_timeAugFun (hu : ContDiff ℝ 2 (Function.uncurry u)) :
    ContDiff ℝ 2 (timeAugFun u) := by
  have hproj : ∀ i : Fin (n + 1), ContDiff ℝ 2 fun z : Fin (n + 1) → ℝ => z i :=
    fun i => contDiff_pi.mp contDiff_id i
  have h : timeAugFun u
      = Function.uncurry u ∘ fun z : Fin (n + 1) → ℝ => (z 0, fun q => z q.succ) := by
    funext z
    rfl
  rw [h]
  exact hu.comp ((hproj 0).prodMk (contDiff_pi.mpr fun q => hproj q.succ))

/-- The partial derivatives of the time-augmented representative are bounded by the larger of
the bounds on the time derivative and on the gradient. -/
theorem abs_coordDeriv_timeAug_le (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) {K₀ K₁ : ℝ}
    (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀) (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (p : Fin (n + 1)) (z : Fin (n + 1) → ℝ) : |coordDeriv f' p z| ≤ max K₀ K₁ := by
  induction p using Fin.cases with
  | zero =>
    rw [coordDeriv_zero_eq_timeDeriv hfu hf]
    exact (hK₀ _ _).trans (le_max_left _ _)
  | succ q =>
    rw [coordDeriv_succ_eq_gradient hfu hf]
    exact (hK₁ _ _ _).trans (le_max_right _ _)

/-- Against the quadratic covariation density of the time-augmented diffusion, whose time row
vanishes, the second partial derivatives of the time-augmented representative are bounded by
the Hessian bound. -/
theorem abs_coordDeriv₂_timeAug_mul_le (hfu : ∀ z, f z = timeAugFun u z)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z) {K₂ : ℝ}
    (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂) (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (p q : Fin (n + 1)) (z : Fin (n + 1) → ℝ) (ω : Ω) (s : ℝ) :
    |coordDeriv₂ f'' p q z|
        * |∑ k : Fin d, timeAugDiffusion H p k ω s * timeAugDiffusion H q k ω s|
      ≤ K₂ * |∑ k : Fin d, timeAugDiffusion H p k ω s * timeAugDiffusion H q k ω s| := by
  induction p using Fin.cases with
  | zero => simp [timeAugDiffusion]
  | succ p' =>
    induction q using Fin.cases with
    | zero => simp [timeAugDiffusion]
    | succ q' =>
      rw [coordDeriv₂_succ_succ_eq_hessian hfu hf hf']
      exact mul_le_mul_of_nonneg_right (hK₂ _ _ _ _) (abs_nonneg _)

/-- Adding a vector with a zero time coordinate to a time-consed vector adds the states. -/
theorem cons_add_cons_zero (s : ℝ) (x v : Fin n → ℝ) :
    (Fin.cons s x : Fin (n + 1) → ℝ) + Fin.cons 0 v = Fin.cons s (x + v) := by
  funext p
  refine Fin.cases ?_ ?_ p <;> simp

/-- The time-augmented representative at a time-consed state translated by a state. -/
theorem timeAugFun_cons_add_cons_zero (u : ℝ → (Fin n → ℝ) → ℝ) (s : ℝ) (x v : Fin n → ℝ) :
    timeAugFun u (Fin.cons s x + Fin.cons 0 v) = u s (x + v) := by
  rw [cons_add_cons_zero, timeAugFun_cons]

end TimeAugBounds

end LevyStochCalc.Ito.JumpFormula
