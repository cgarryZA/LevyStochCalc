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
# The càdlàg representative of a solution path

The Itô–Lévy formula at bounded derivatives asks for left limits of the solution at every sample
point and every time, while the well-posedness theorem produces paths that are càdlàg only on a
measurable set `G` of full measure. `cadlagRep G X` is the path map that agrees with `X` on `G` at
nonnegative times, is the constant zero path off `G`, and is frozen at the zero state before time
zero. It is càdlàg at every sample point and every time, adapted whenever `G` belongs to the
initial σ-algebra, progressively measurable because it is right-continuous everywhere, and solves
the equation on every window, because both stochastic integrals depend only on the class of their
integrand.
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

omit [IsProbabilityMeasure P] in
/-- A function of the time and the state has the same window energy along the representative as
along the original path. -/
theorem lintegral_sq_comp_cadlagRep (hG0 : P Gᶜ = 0) (f : ℝ → (Fin n → ℝ) → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (cadlagRep G X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s (X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
  exact setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hω s hs.1]

omit [IsProbabilityMeasure P] in
/-- A marked function of the time and the state has the same window energy along the
representative as along the original path. -/
theorem lintegral_sq_marked_comp_cadlagRep {E : Type*} [MeasurableSpace E] {ν : Measure E}
    (hG0 : P Gᶜ = 0) (g : ℝ → (Fin n → ℝ) → E → ℝ) (T : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖g s (cadlagRep G X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g s (X s ω) e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  refine lintegral_congr_ae ?_
  filter_upwards [ae_forall_cadlagRep_eq (P := P) hG0] with ω hω
  exact setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [hω s hs.1]

/-- The representative solves the equation on every window, relative to the same filtration. -/
theorem solvesOn_cadlagRep (hGm : MeasurableSet G) (hG0 : P Gᶜ = 0)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hσmeas : Measurable (Function.uncurry coeffs.σ))
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    (hσq : ∀ (i : Fin n) (j : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hγq : ∀ (i : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (hXm : Measurable (Function.uncurry X))
    (hXa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => X s ω i)
    (hX0 : ∀ᵐ ω ∂P, X 0 ω = x₀)
    (hGp : ∀ ω ∈ G, ∀ t : ℝ, 0 ≤ t →
      Tendsto (fun s => X s ω) (𝓝[>] t) (𝓝 (X t ω))
        ∧ ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => X s ω i) (𝓝[<] t) (𝓝 L))
    (hXsol : ∀ T : ℝ, SolvesOn W N ℱ hℱW hℱN coeffs x₀ X T) (T : ℝ) :
    SolvesOn W N ℱ hℱW hℱN coeffs x₀ (cadlagRep G X) T := by
  have hG : MeasurableSet[ℱ 0] G := by
    simpa using (hnull Gᶜ hGm.compl hG0).compl
  have hXad : ∀ t : ℝ, Measurable[ℱ t] (X t) := measurable_of_progressivelyMeasurable ℱ hXa
  have hYm : Measurable (Function.uncurry (cadlagRep G X)) := measurable_uncurry_cadlagRep hGm hXm
  have hYa : ∀ i : Fin n, ProgressivelyMeasurable ℱ fun ω s => cadlagRep G X s ω i :=
    fun i => progressivelyMeasurable_cadlagRep hGp hG hXad i
  have hσm : ∀ i : Fin n, ∀ j : Fin d,
      Measurable (Function.uncurry fun ω s => coeffs.σ s (cadlagRep G X s ω) i j) :=
    fun i j => ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσmeas)).comp
      (measurable_snd.prodMk (hYm.comp (measurable_snd.prodMk measurable_fst)))
  have hσp : ∀ i : Fin n, ∀ j : Fin d,
      ProgressivelyMeasurable ℱ fun ω s => coeffs.σ s (cadlagRep G X s ω) i j :=
    fun i j => progressivelyMeasurable_comp_state hYa (f := fun s x => coeffs.σ s x i j)
      ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hσmeas))
  have hσq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.σ s (cadlagRep G X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i j T' hT' => (lintegral_sq_comp_cadlagRep hG0 (fun s x => coeffs.σ s x i j) T').trans_lt
      (hσq i j T' hT')
  have hγm : ∀ i : Fin n,
      Measurable fun p : Ω × ℝ × E => coeffs.γ p.2.1 (cadlagRep G X p.2.1 p.1) p.2.2 i :=
    fun i => ((measurable_pi_apply i).comp hγmeas).comp
      ((measurable_fst.comp measurable_snd).prodMk
        ((hYm.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).prodMk
          (measurable_snd.comp measurable_snd)))
  have hγp : ∀ i : Fin n,
      MarkedProgressivelyMeasurable ℱ fun ω s e => coeffs.γ s (cadlagRep G X s ω) e i :=
    fun i => markedProgressivelyMeasurable_comp_state hYa (g := fun s x e => coeffs.γ s x e i)
      ((measurable_pi_apply i).comp hγmeas)
  have hγq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖coeffs.γ s (cadlagRep G X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ :=
    fun i T' hT' => (lintegral_sq_marked_comp_cadlagRep hG0 (fun s x e => coeffs.γ s x e i)
      T').trans_lt (hγq i T' hT')
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

end LevyStochCalc.Ito.JumpFormula
