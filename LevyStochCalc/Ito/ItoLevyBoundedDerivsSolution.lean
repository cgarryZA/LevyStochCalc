/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoLevyBoundedDerivs
import LevyStochCalc.Ito.PicardWellPosed
import LevyStochCalc.Ito.PicardLocality
import LevyStochCalc.Ito.SdeDataOfSolvesOn

/-!
# The Itô–Lévy formula at bounded derivatives, from the solution data

`itoLevyFormula_jumpResidual_of_boundedDerivs` asks, besides the bounded derivatives of the state
function, for the admissibility of the derived integrands `(∇u)ᵀσ` and `u(x + γ) − u(x)` along the
solution, for left limits of the solution at every sample point and every time, and for the
progressive measurability of the drift along the solution. This file derives each of these from
the data the well-posedness theorem produces — regular Lipschitz coefficients, a filtration
satisfying the usual conditions, and the window solutions of `exists_globalSolution` — and
states the formula for a solution built from that data alone.

## The càdlàg representative

The well-posedness theorem gives paths that are càdlàg on `[0, ∞)` almost surely. The formula
needs left limits at every sample point and every time, so the solution is replaced by
`cadlagRep G X`: the same path on a measurable set `G` of full measure where the paths are
càdlàg, the constant zero path off `G`, and the zero state before time zero. The representative
agrees with the original at every nonnegative time on `G`, is adapted because `G` belongs to the
initial σ-algebra (which contains the null sets), is progressively measurable because it is
right-continuous everywhere, and satisfies the same window equations because both stochastic
integrals depend only on the class of their integrand.

## Main statements

* `cadlagRep_cadlag`, `progressivelyMeasurable_cadlagRep`, `solvesOn_cadlagRep` — the
  representative is càdlàg at every sample point and every time, progressively measurable, and
  solves the equation on every window.
* `measurable_diffusionIntegrand_path`, `progressivelyMeasurable_diffusionIntegrand_path`,
  `lintegral_sq_diffusionIntegrand_path_lt_top` — admissibility of `(∇u)ᵀσ` along a path.
* `measurable_jumpIncrement_path`, `markedProgressivelyMeasurable_jumpIncrement_path`,
  `lintegral_sq_jumpIncrement_path_lt_top` — admissibility of `u(x + γ) − u(x)` along a path.
* `ae_integrableOn_drift_path`, `ae_lintegral_compensatorDriftIntegrand_lt_top` — integrability
  of the drift and of the compensator-drift integrand along a path.
* `itoLevyFormula_jumpResidual_of_solvesOn` — the formula for a jump diffusion solving the
  equation relative to the given filtration, every admissibility input being one of the lemmas
  above.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

open LevyStochCalc.Ito.Setting LevyStochCalc.Ito.Picard LevyStochCalc.Ito.BigJump
  LevyStochCalc.Probability

universe u v

section CadlagRep

variable {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}

/-- A path map replaced by the constant zero path off a set of sample points and frozen at the
zero state before time zero. -/
noncomputable def cadlagRep (G : Set Ω) (X : ℝ → Ω → Fin n → ℝ) (s : ℝ) (ω : Ω) : Fin n → ℝ :=
  (Set.Ici (0 : ℝ)).indicator (fun r => repairOn G X r ω) s

variable {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

omit [MeasurableSpace Ω] in
theorem cadlagRep_of_nonneg {s : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    cadlagRep G X s ω = repairOn G X s ω :=
  Set.indicator_of_mem (Set.mem_Ici.mpr hs) _

omit [MeasurableSpace Ω] in
theorem cadlagRep_of_neg {s : ℝ} (hs : s < 0) (ω : Ω) : cadlagRep G X s ω = 0 :=
  Set.indicator_of_notMem (fun h => absurd (Set.mem_Ici.mp h) (not_le.mpr hs)) _

omit [MeasurableSpace Ω] in
/-- On the good set and at nonnegative times the representative is the original path. -/
theorem cadlagRep_eq_of_mem {s : ℝ} (hs : 0 ≤ s) {ω : Ω} (hω : ω ∈ G) :
    cadlagRep G X s ω = X s ω := by
  rw [cadlagRep_of_nonneg hs, repairOn_of_mem hω]

/-- The representative is jointly measurable in the time and the sample point. -/
theorem measurable_uncurry_cadlagRep (hGm : MeasurableSet G)
    (hX : Measurable (Function.uncurry X)) :
    Measurable (Function.uncurry (cadlagRep G X)) := by
  have hrep := measurable_uncurry_repairOn hGm hX
  have heq : Function.uncurry (cadlagRep G X)
      = {q : ℝ × Ω | 0 ≤ q.1}.indicator (Function.uncurry (repairOn G X)) := by
    funext q
    by_cases hq : 0 ≤ q.1
    · change cadlagRep G X q.1 q.2 = _
      rw [cadlagRep_of_nonneg hq, Set.indicator_of_mem (show q ∈ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
      rfl
    · change cadlagRep G X q.1 q.2 = _
      rw [cadlagRep_of_neg (not_le.mp hq),
        Set.indicator_of_notMem (show q ∉ {q : ℝ × Ω | 0 ≤ q.1} from hq)]
  rw [heq]
  exact hrep.indicator (measurableSet_le measurable_const measurable_fst)

variable (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
  Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
    ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))

omit [MeasurableSpace Ω] in
include hGp in
/-- The representative is right-continuous at every sample point and every time, when the
original paths are càdlàg on the good set. -/
theorem cadlagRep_rightContinuous (ω : Ω) (t : ℝ) :
    Tendsto (fun s => cadlagRep G X s ω) (𝓝[>] t) (𝓝 (cadlagRep G X t ω)) := by
  rcases lt_or_ge t 0 with ht | ht
  · rw [cadlagRep_of_neg ht]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds ht)] with s hs
    exact (cadlagRep_of_neg (Set.mem_Iio.mp hs) ω).symm
  · rw [cadlagRep_of_nonneg ht]
    refine (repairOn_cadlag hGp ω t ht).1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (cadlagRep_of_nonneg (ht.trans (le_of_lt (Set.mem_Ioi.mp hs))) ω).symm

omit [MeasurableSpace Ω] in
include hGp in
/-- Every coordinate of the representative has a left limit at every sample point and every
time, when the original paths are càdlàg on the good set. -/
theorem cadlagRep_leftLim (ω : Ω) (t : ℝ) (i : Fin n) :
    ∃ L : ℝ, Tendsto (fun s => cadlagRep G X s ω i) (𝓝[<] t) (𝓝 L) := by
  rcases le_or_gt t 0 with ht | ht
  · refine ⟨0, tendsto_const_nhds.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [cadlagRep_of_neg (lt_of_lt_of_le (Set.mem_Iio.mp hs) ht)]
    rfl
  · obtain ⟨L, hL⟩ := (repairOn_cadlag hGp ω t ht.le).2 i
    refine ⟨L, hL.congr' ?_⟩
    filter_upwards [Ioo_mem_nhdsLT ht] with s hs
    rw [cadlagRep_of_nonneg hs.1.le]

omit [MeasurableSpace Ω] in
include hGp in
/-- The representative is càdlàg at every sample point and every time. -/
theorem cadlagRep_cadlag (ω : Ω) (t : ℝ) :
    Tendsto (fun s => cadlagRep G X s ω) (𝓝[>] t) (𝓝 (cadlagRep G X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => cadlagRep G X s ω i) (𝓝[<] t) (𝓝 L) :=
  ⟨cadlagRep_rightContinuous hGp ω t, cadlagRep_leftLim hGp ω t⟩

/-- The representative is adapted whenever the original path is adapted and the good set belongs
to the initial σ-algebra. -/
theorem measurable_cadlagRep {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hG : MeasurableSet[ℱ 0] G) (hX : ∀ t : ℝ, Measurable[ℱ t] (X t)) (t : ℝ) :
    Measurable[ℱ t] (cadlagRep G X t) := by
  classical
  rcases lt_or_ge t 0 with ht | ht
  · have hz : cadlagRep G X t = fun _ => 0 := funext fun ω => cadlagRep_of_neg ht ω
    rw [hz]
    exact measurable_const
  · have hite : cadlagRep G X t = fun ω => if ω ∈ G then X t ω else 0 := by
      funext ω
      rw [cadlagRep_of_nonneg ht]
      by_cases hω : ω ∈ G <;> simp [repairOn, hω]
    rw [hite]
    exact Measurable.ite (ℱ.mono ht _ hG) (hX t) measurable_const

include hGp in
/-- The representative is progressively measurable: it is adapted and right-continuous. -/
theorem progressivelyMeasurable_cadlagRep {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hG : MeasurableSet[ℱ 0] G) (hX : ∀ t : ℝ, Measurable[ℱ t] (X t)) (i : Fin n) :
    ProgressivelyMeasurable ℱ fun ω s => cadlagRep G X s ω i :=
  progressivelyMeasurable_of_rightContinuous
    (fun t => (measurable_pi_apply i).comp (measurable_cadlagRep hG hX t))
    (fun ω t => ((continuous_apply i).tendsto _).comp (cadlagRep_rightContinuous hGp ω t))

end CadlagRep

section Representative

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E) {x₀ : Fin n → ℝ}
  {G : Set Ω} {X : ℝ → Ω → Fin n → ℝ}

/-- A path map adapted to the initial σ-algebra at time `0` is adapted at every time, once it is
progressively measurable. -/
theorem measurable_of_progressivelyMeasurable
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) (t : ℝ) :
    Measurable[ℱ t] (X t) := by
  letI : MeasurableSpace Ω := ℱ t
  exact measurable_pi_lambda _ fun i => ((hXa i).stronglyMeasurable_eval t).measurable

omit [IsProbabilityMeasure P] in
/-- The representative starts at the initial state almost surely. -/
theorem ae_cadlagRep_zero (hG0 : P Gᶜ = 0) (hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀) :
    ∀ᵐ ω ∂P, cadlagRep G X 0 ω = x₀ := by
  filter_upwards [mem_ae_iff.mpr hG0, hX0] with ω hω h0
  rw [cadlagRep_eq_of_mem le_rfl hω, h0]

omit [IsProbabilityMeasure P] in
/-- The representative agrees with the original path at every nonnegative time, almost surely. -/
theorem ae_forall_cadlagRep_eq (hG0 : P Gᶜ = 0) :
    ∀ᵐ ω ∂P, ∀ s : ℝ, 0 ≤ s → cadlagRep G X s ω = X s ω := by
  filter_upwards [mem_ae_iff.mpr hG0] with ω hω s hs
  exact cadlagRep_eq_of_mem hs hω

omit [IsProbabilityMeasure P] in
/-- The representative has the same running second moment as the original path. -/
theorem lintegral_iSup_cadlagRep (hG0 : P Gᶜ = 0) (T' : ℝ) :
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖cadlagRep G X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P
      = ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
  exact iSup_congr fun t => by rw [hω t t.2.1]

/-- The representative solves the equation on every window, relative to the same filtration. -/
theorem solvesOn_cadlagRep (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : coeffs.IsRegular ν) {L : ℝ} (hLip : coeffs.IsLipschitz ν L)
    (hXm : Measurable (Function.uncurry X))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀)
    (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (hXS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤)
    (hXsol : ∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ (cadlagRep G X) T := by
  have hG : MeasurableSet[ℱ 0] G := by
    simpa using (hnull Gᶜ hGm.compl hG0).compl
  have hXad : ∀ t : ℝ, Measurable[ℱ t] (X t) := measurable_of_progressivelyMeasurable ℱ hXa
  have hYm : Measurable (Function.uncurry (cadlagRep G X)) := measurable_uncurry_cadlagRep hGm hXm
  have hYa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => cadlagRep G X s ω i :=
    fun i => progressivelyMeasurable_cadlagRep hGp hG hXad i
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖cadlagRep G X (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P
        < ⊤ := fun T' hT' => by
    rw [lintegral_iSup_cadlagRep hG0]
    exact hXS T' hT'
  have hYsq := fun b => lintegral_lintegral_sq_lt_top_of_supL2 hYS b
  have hσm : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => coeffs.σ s (cadlagRep G X s ω) i j) :=
    fun i j => measurable_sigma_comp_state coeffs hReg hYm i j
  have hσp : ∀ i : Fin n, ∀ j : Fin d,
      ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (cadlagRep G X s ω) i j :=
    fun i j => progressivelyMeasurable_comp_state hYa (f := fun s x => coeffs.σ s x i j)
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hReg.2.1))
  have hσq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (cadlagRep G X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i j T' hT' => lintegral_sq_sigma_lt_top_of_energy coeffs hReg hLip hYm hYsq i j hT'
  have hγm : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (cadlagRep G X p.2.1 p.1) p.2.2 i :=
    fun i => measurable_gamma_comp_state coeffs hReg hYm i
  have hγp : ∀ i : Fin n,
      MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (cadlagRep G X s ω) e i :=
    fun i => markedProgressivelyMeasurable_comp_state hYa (g := fun s x e => coeffs.γ s x e i)
      ((measurable_pi_apply i).comp hReg.2.2.1)
  have hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (cadlagRep G X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun i T' hT' => lintegral_sq_gamma_lt_top_of_energy coeffs hReg hLip hYm hYsq i hT'
  refine ⟨hσm, hσp, hσq, hγm, hγp, hγq, fun t ht => ?_⟩
  rcases ht.1.lt_or_eq with ht0 | ht0
  · -- at a positive time, the step reads the two paths on `[0, t]`, where they agree a.s.
    have hXY : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        cadlagRep G X s ω = X s ω := by
      filter_upwards [ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact hω s hs.1
    have hstep := picardStep_congr_ae W N ℱ hℱW hℱN coeffs (cadlagRep G X) X x₀ hσm hσp hσq
      hγm hγp hγq (hXsol T).h_σ_meas (hXsol T).h_σ_progMeas (hXsol T).h_σ_sq
      (hXsol T).h_γ_meas (hXsol T).h_γ_progMeas (hXsol T).h_γ_sq ht0 hXY
    filter_upwards [hstep, (hXsol T).eqn t ht, ae_forall_cadlagRep_eq (P := P) hG0]
      with ω hω heq hagree
    intro i
    rw [hagree t ht.1, heq i, hω]
  · -- at time zero both sides are the initial state
    subst ht0
    filter_upwards [ae_cadlagRep_zero hG0 hX0,
      ae_picardStep_zero W N ℱ hℱW hℱN coeffs (cadlagRep G X) x₀ hσm hσp hσq hγm hγp hγq]
      with ω h0 hstep
    intro i
    rw [h0, hstep i]

end Representative

section DerivedIntegrands

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {coeffs : JumpDiffusionCoeffs n d E} {u : ℝ → (Fin n → ℝ) → ℝ}
  {X : ℝ → Ω → Fin n → ℝ}

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a `C²` state function along a jointly measurable path is
jointly measurable. -/
theorem measurable_diffusionIntegrand_path (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hσ : Measurable (Function.uncurry coeffs.σ)) (hXm : Measurable (Function.uncurry X))
    (j : Fin d) :
    Measurable (Function.uncurry fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j) := by
  have hstate : Measurable fun p : Ω × ℝ => ((p.2, X p.2 p.1) : ℝ × (Fin n → ℝ)) :=
    measurable_snd.prodMk (hXm.comp (measurable_snd.prodMk measurable_fst))
  change Measurable fun p : Ω × ℝ =>
    ∑ i, gradient u p.2 (X p.2 p.1) i * coeffs.σ p.2 (X p.2 p.1) i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (continuous_gradient_uncurry hu i).measurable.comp hstate
  · exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)).comp hstate

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a `C²` state function along a progressively measurable
path is progressively measurable. -/
theorem progressivelyMeasurable_diffusionIntegrand_path {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (hσ : Measurable (Function.uncurry coeffs.σ))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) (j : Fin d) :
    ProgressivelyMeasurable ℱ fun ω s => diffusionIntegrand u coeffs.σ s (X s ω) j := by
  refine progressivelyMeasurable_comp_state hXa
    (f := fun s x => diffusionIntegrand u coeffs.σ s x j) ?_
  change Measurable fun q : ℝ × (Fin n → ℝ) => ∑ i, gradient u q.1 q.2 i * coeffs.σ q.1 q.2 i j
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_
  · exact (continuous_gradient_uncurry hu i).measurable
  · exact (measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσ)

omit [MeasurableSpace E] [SigmaFinite ν] in
/-- The diffusion integrand `(∇u)ᵀσ` of a state function with a bounded gradient has finite
energy on every window on which the diffusion coefficient along the path has. -/
theorem lintegral_sq_diffusionIntegrand_path_lt_top {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hσm : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => coeffs.σ s (X s ω) i j))
    (hσq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (j : Fin d) {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (X s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  have hK₁' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  refine lintegral_window_sq_le_of_abs_le (a := fun i ω s => coeffs.σ s (X s ω) i j)
    (c := max K₁ 0) (fun i => hσm i j) (fun ω s => ?_) T' (fun i => hσq i j T' hT')
  exact abs_mixedDiffusionIntegrand_le hK₁' s (X s ω) (X s ω) j

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The jump increment `u(x + γ) − u(x)` of a `C²` state function along a jointly measurable
path is jointly measurable. -/
theorem measurable_jumpIncrement_path (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X)) :
    Measurable fun p : Ω × ℝ × E =>
      (fun ω' s e => u s (X s ω' + coeffs.γ s (X s ω') e) - u s (X s ω')) p.1 p.2.1 p.2.2 := by
  have hXp : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγp : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 :=
    hγ.comp (measurable_snd.fst.prodMk (hXp.prodMk measurable_snd.snd))
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  exact (hu'.comp (measurable_snd.fst.prodMk (hXp.add hγp))).sub
    (hu'.comp (measurable_snd.fst.prodMk hXp))

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The jump increment `u(x + γ) − u(x)` of a `C²` state function along a progressively
measurable path is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_jumpIncrement_path {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i) :
    MarkedProgressivelyMeasurable ℱ
      fun ω' s e => u s (X s ω' + coeffs.γ s (X s ω') e) - u s (X s ω') := by
  refine markedProgressivelyMeasurable_comp_state hXa
    (g := fun s x e => u s (x + coeffs.γ s x e) - u s x) ?_
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  exact (hu'.comp (measurable_fst.prodMk (measurable_snd.fst.add hγ))).sub
    (hu'.comp (measurable_fst.prodMk measurable_snd.fst))

/-- The jump increment `u(x + γ) − u(x)` of a state function with a bounded gradient has finite
energy on every window on which the jump coefficient along the path has. -/
theorem lintegral_sq_jumpIncrement_path_lt_top (hu : ContDiff ℝ 2 (Function.uncurry u)) {K₁ : ℝ}
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁)
    (hγm : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T' : ℝ} (hT' : 0 < T') :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖u s (X s ω + coeffs.γ s (X s ω) e) - u s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  have hK₁' : ∀ s x i, |gradient u s x i| ≤ max K₁ 0 :=
    fun s x i => (hK₁ s x i).trans (le_max_left _ _)
  refine lintegral_window_mark_sq_le_of_abs_le (a := fun i ω s e => coeffs.γ s (X s ω) e i)
    (c := n * max K₁ 0) (fun i => hγm i) (fun ω s e => ?_) T' (fun i => hγq i T' hT')
  exact abs_mixedJumpIncrement_le hu hK₁' (le_max_right _ _) s (X s ω) (X s ω) e

omit [MeasurableSpace E] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The drift along a path of finite drift energy is integrable on every window, almost surely.
-/
theorem ae_integrableOn_drift_path
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∀ i : Fin n, IntegrableOn (fun s => coeffs.μ s (X s ω) i) (Set.Icc (0 : ℝ) T) := by
  rw [ae_all_iff]
  intro i
  filter_upwards [ae_integrableOn_of_lintegral_sq (hμm i) (hμq i)] with ω hω
  exact hω T

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The compensator-drift integrand of a `C²` state function along a jointly measurable path is
jointly measurable. -/
theorem measurable_compensatorDriftIntegrand_path (hu : ContDiff ℝ 2 (Function.uncurry u))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X)) :
    Measurable fun p : Ω × ℝ × E =>
      compensatorDriftIntegrand u coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 := by
  have hXp : Measurable fun p : Ω × ℝ × E => X p.2.1 p.1 :=
    hXm.comp (measurable_snd.fst.prodMk measurable_fst)
  have hγp : Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 :=
    hγ.comp (measurable_snd.fst.prodMk (hXp.prodMk measurable_snd.snd))
  have hu' : Measurable fun q : ℝ × (Fin n → ℝ) => u q.1 q.2 := hu.continuous.measurable
  have hstate : Measurable fun p : Ω × ℝ × E => ((p.2.1, X p.2.1 p.1) : ℝ × (Fin n → ℝ)) :=
    measurable_snd.fst.prodMk hXp
  change Measurable fun p : Ω × ℝ × E =>
    u p.2.1 (X p.2.1 p.1 + coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2) - u p.2.1 (X p.2.1 p.1)
      - ∑ i, coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i * gradient u p.2.1 (X p.2.1 p.1) i
  refine ((hu'.comp (measurable_snd.fst.prodMk (hXp.add hγp))).sub (hu'.comp hstate)).sub
    (Finset.measurable_sum _ fun i _ => Measurable.mul ?_ ?_)
  · exact (measurable_pi_apply i).comp hγp
  · exact (continuous_gradient_uncurry hu i).measurable.comp hstate

/-- The compensator-drift integrand of a state function with a bounded Hessian is integrable over
the marks and a window, almost surely, when the jump coefficient along the path has finite energy
on that window. -/
theorem ae_lintegral_compensatorDriftIntegrand_lt_top (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₂ : ℝ} (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hXm : Measurable (Function.uncurry X))
    (hγm : ∀ i : Fin n, Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i)
    (hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume < ⊤ := by
  have hK₂' : ∀ s x i j, |hessian u s x i j| ≤ max K₂ 0 :=
    fun s x i j => (hK₂ s x i j).trans (le_max_left _ _)
  set C : ℝ := (n : ℝ) ^ 2 * max K₂ 0 * n with hC
  have hC0 : 0 ≤ C := by positivity
  -- the pointwise bound, in extended form
  have hpt : ∀ ω s e, (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal C * ∑ i, (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 := by
    intro ω s e
    have hreal : |compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
        ≤ C * ∑ i, coeffs.γ s (X s ω) e i ^ 2 := by
      have h := abs_mixedCompensatorDriftIntegrand_le hu (γ := coeffs.γ) hK₂' (le_max_right _ _)
        s (X s ω) (X s ω) e
      rw [hC]
      calc |compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
          ≤ (n : ℝ) ^ 2 * max K₂ 0 * ((n : ℝ) * ∑ i, coeffs.γ s (X s ω) e i ^ 2) := h
        _ = (n : ℝ) ^ 2 * max K₂ 0 * n * ∑ i, coeffs.γ s (X s ω) e i ^ 2 := by ring
    rw [show ((‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞))
        = ‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖ₑ from rfl,
      Real.enorm_eq_ofReal_abs]
    calc ENNReal.ofReal |compensatorDriftIntegrand u coeffs.γ s (X s ω) e|
        ≤ ENNReal.ofReal (C * ∑ i, coeffs.γ s (X s ω) e i ^ 2) := ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal C * ∑ i, (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.ofReal_mul hC0, ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
        exact congrArg _ (Finset.sum_congr rfl fun i _ => (sq_coe_nnnorm_real _).symm)
  have hm : ∀ i, Measurable fun p : Ω × ℝ × E =>
      (‖coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2 i‖₊ : ℝ≥0∞) ^ 2 :=
    fun i => (((hγm i).nnnorm).coe_nnreal_ennreal).pow_const 2
  -- the energy of the integrand is finite
  have houter : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞) ∂ν ∂volume ∂P < ⊤ := by
    refine lt_of_le_of_lt
      (lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => hpt ω s e) ?_
    have hC' : ENNReal.ofReal C ≠ ⊤ := ENNReal.ofReal_ne_top
    simp_rw [lintegral_const_mul' _ _ hC']
    rw [lintegral_window_mark_sum
      (f := fun i ω s e => (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2) hm T]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.sum_lt_top.mpr fun i _ => hγq i T hT)
  have hfm : Measurable fun p : Ω × ℝ × E =>
      (‖compensatorDriftIntegrand u coeffs.γ p.2.1 (X p.2.1 p.1) p.2.2‖₊ : ℝ≥0∞) :=
    (measurable_compensatorDriftIntegrand_path hu hγ hXm).nnnorm.coe_nnreal_ennreal
  exact ae_lt_top (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
    (f := fun ω s e => (‖compensatorDriftIntegrand u coeffs.γ s (X s ω) e‖₊ : ℝ≥0∞)) hfm T)
    houter.ne

end DerivedIntegrands

section Main

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
  (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
  (coeffs : JumpDiffusionCoeffs n d E)

/-- **The Itô–Lévy formula at bounded derivatives, from the solution data.** For regular
Lipschitz coefficients and a right-continuous filtration containing the null sets at time zero,
there is a jump diffusion solving the equation on every window relative to that filtration, with
progressively measurable coordinates and càdlàg paths at every sample point and every time,
along which a `C²` state function with bounded time derivative, gradient and Hessian satisfies
the Itô–Lévy formula: its increment is the drift integral, the Brownian integral of `(∇u)ᵀσ`,
the compensated integral of `u(x + γ) − u(x)` and the compensator-drift integral. Every
admissibility input of the two stochastic integrals is derived from the solution data. -/
theorem itoLevyFormula_jumpResidual_of_solvesOn [ℱ.IsRightContinuous]
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hReg : coeffs.IsRegular ν) {L : ℝ} (hLip : coeffs.IsLipschitz ν L) (x₀ : Fin n → ℝ)
    (u : ℝ → (Fin n → ℝ) → ℝ) (hu : ContDiff ℝ 2 (Function.uncurry u))
    {K₀ K₁ K₂ : ℝ} (hK₀ : ∀ s x, |timeDeriv u s x| ≤ K₀)
    (hK₁ : ∀ s x i, |gradient u s x i| ≤ K₁) (hK₂ : ∀ s x i j, |hessian u s x i j| ≤ K₂)
    (T : ℝ) (hT : 0 < T) :
    ∃ (X : JumpDiffusion W N coeffs x₀)
      (hsol : ∀ T' : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X.X T')
      (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X.X s ω i),
      (∀ (ω : Ω) (t : ℝ), Tendsto (fun s => X.X s ω) (𝓝[>] t) (𝓝 (X.X t ω))
          ∧ ∀ j : Fin n, ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
      ∧ ∀ᵐ ω ∂P,
        (u T (X.X T ω) - u 0 (X.X 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
          - MultidimBrownianMotion.stochasticIntegral W ℱ hℱW
              (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
              (fun j => measurable_diffusionIntegrand_path hu hReg.2.1 X.measurable_path j)
              (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hReg.2.1 hXa j)
              (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
                (hsol 0).h_σ_meas (hsol 0).h_σ_sq j hT') T ω)
          = LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
              (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω'))
              (measurable_jumpIncrement_path hu hReg.2.2.1 X.measurable_path)
              (markedProgressivelyMeasurable_jumpIncrement_path hu hReg.2.2.1 hXa)
              (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ (hsol 0).h_γ_meas
                (hsol 0).h_γ_sq hT') T ω
          + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
              compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  -- the solution of the well-posedness theorem
  obtain ⟨X₀, hXm, hXa₀, hX0, hXcad, hXS, hXsol⟩ :=
    exists_globalSolution W N ℱ hℱW hℱN coeffs hℱ0 hnull hReg hLip x₀
  -- the good set, on which its paths are càdlàg
  obtain ⟨G, hGm, hG0, hGp⟩ := exists_measurable_full_of_ae (P := P) hXcad
  have hG : MeasurableSet[ℱ 0] G := by
    simpa using (hnull Gᶜ hGm.compl hG0).compl
  have hXad : ∀ t : ℝ, Measurable[ℱ t] (X₀ t) := measurable_of_progressivelyMeasurable ℱ hXa₀
  -- the representative and its data
  set Y : ℝ → Ω → Fin n → ℝ := cadlagRep G X₀ with hYdef
  have hYm : Measurable (Function.uncurry Y) := measurable_uncurry_cadlagRep hGm hXm
  have hYa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => Y s ω i :=
    fun i => progressivelyMeasurable_cadlagRep hGp hG hXad i
  have hY0 : ∀ᵐ ω ∂P, Y 0 ω = x₀ := ae_cadlagRep_zero hG0 hX0
  have hYcad : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => Y s ω) (𝓝[>] t) (𝓝 (Y t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Y s ω i) (𝓝[<] t) (𝓝 L) :=
    fun ω t => cadlagRep_cadlag hGp ω t
  have hYS : ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T', ∑ i, (‖Y (t : ℝ) ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ :=
    fun T' hT' => by
      rw [hYdef, lintegral_iSup_cadlagRep hG0]
      exact hXS T' hT'
  have hYsol : ∀ T' : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ Y T' := fun T' =>
    solvesOn_cadlagRep W N ℱ hℱW hℱN coeffs hGm hG0 hnull hReg hLip hXm hXa₀ hX0 hGp hXS
      hXsol T'
  let X : JumpDiffusion W N coeffs x₀ :=
    jumpDiffusionOfSolvesOn W N ℱ hℱW hℱN coeffs x₀ hYm hY0
      (Eventually.of_forall fun ω t _ => hYcad ω t) hYS hYsol
  refine ⟨X, hYsol, hYa, hYcad, ?_⟩
  -- the SDE data of the representative at the given filtration
  let S : SdeData X := SdeData.ofSolvesOn X ℱ hℱW hℱN hYsol
  haveI : S.ℱ.IsRightContinuous := ‹ℱ.IsRightContinuous›
  have hrc : ℱ.rightCont = ℱ := Filtration.IsRightContinuous.eq
  have hℱ0' : ∀ t : ℝ, t ≤ 0 → S.ℱ.rightCont 0 ≤ S.ℱ.rightCont t := by
    intro t ht
    change ℱ.rightCont 0 ≤ ℱ.rightCont t
    rw [hrc]
    exact hℱ0 t ht
  have hYsq := fun b => lintegral_lintegral_sq_lt_top_of_supL2 hYS b
  have hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (Y s ω) i) :=
    fun i => measurable_mu_comp_state coeffs hReg hYm i
  have hμp : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => coeffs.μ s (Y s ω) i :=
    fun i => progressivelyMeasurable_comp_state hYa (f := fun s x => coeffs.μ s x i)
      ((measurable_pi_apply i).comp hReg.1)
  have hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.μ s (Y s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i T' hT' => lintegral_sq_mu_lt_top_of_energy coeffs hReg hLip hYm hYsq i hT'
  exact itoLevyFormula_jumpResidual_of_boundedDerivs W N coeffs x₀ X S hℱ0' hnull
    (fun t => measurable_of_progressivelyMeasurable ℱ hYa t) (fun ω t j => (hYcad ω t).2 j)
    hμm hμp hμq hReg.2.2.1 u hu hK₀ hK₁ hK₂ T hT (ae_integrableOn_drift_path hμm hμq T)
    (fun j => measurable_diffusionIntegrand_path hu hReg.2.1 X.measurable_path j)
    (fun j => progressivelyMeasurable_diffusionIntegrand_path hu hReg.2.1 hYa j)
    (fun j _ hT' => lintegral_sq_diffusionIntegrand_path_lt_top hK₁
      (hYsol 0).h_σ_meas (hYsol 0).h_σ_sq j hT')
    (measurable_jumpIncrement_path hu hReg.2.2.1 X.measurable_path)
    (markedProgressivelyMeasurable_jumpIncrement_path hu hReg.2.2.1 hYa)
    (fun _ hT' => lintegral_sq_jumpIncrement_path_lt_top hu hK₁ (hYsol 0).h_γ_meas
      (hYsol 0).h_γ_sq hT')
    (ae_lintegral_compensatorDriftIntegrand_lt_top hu hK₂ hReg.2.2.1 X.measurable_path
      (hYsol 0).h_γ_meas (hYsol 0).h_γ_sq hT)

end Main

end LevyStochCalc.Ito.JumpFormula
