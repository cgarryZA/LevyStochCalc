/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaCutoff
import LevyStochCalc.Probability.OpenExitTime
import LevyStochCalc.Brownian.ItoLocalityStrict
import LevyStochCalc.Ito.AtomJumpRelation

/-!
# Agreement of the continuous integrands with their cut-off, along a confined path

`JumpFormulaCutoff.integrands_cutoffFun₂_eq_of_mem` compares all five integrands of a state
function with those of its cut-off, and for the two jump integrands it needs the jump coefficient
itself bounded over the window, for every mark. That hypothesis is not available in general: the
jump coefficient is only square integrable against the intensity, so `x + γ(s, x, e)` leaves
every ball however large the cut-off radius.

The three *continuous* integrands need no such hypothesis. They are read at path values only, so
a path confined to a ball is enough. `integrands_cutoffFun₂_eq_of_boundedPath` records that,
adding the gradient, which the pathwise form of the jump part also reads at path values.

For the Brownian transfer the confinement has to come from a stopping time rather than an event,
so the same agreement is restated below `min (openExitTime …) T`: strictly below the exit time
the path is in the ball, and strictly below `T` the time cut-off is inactive. That is exactly the
hypothesis shape of `stochasticIntegralBrownian_congr_of_lt`.

## Main statements

* `integrands_cutoffFun₂_eq_of_boundedPath` — drift, diffusion, path value and gradient agree
  with their cut-off along a path confined to the ball, with no hypothesis on the jumps.
* `boundedPathSet_subset_le_openExitTime` — a path confined to the ball over the window has not
  exited by the end of it.
* `diffusionIntegrand_cutoffFun₂_eq_of_lt` — the agreement in the form the strict locality
  transfer consumes.
* `stochasticIntegralBrownian_cutoffFun₂_eq_of_le` — the Brownian term of the cut-off and of the
  function itself agree almost surely on the event that the path has not left the ball.
* `norm_leftLimPathAt_le_of_boundedPath`,
  `gradient_cutoffFun₂_leftLim_eq_of_boundedPath` — a confined path has its left limits in the
  ball, where the gradient of the cut-off is that of the function.
* `jumpIncrement_cutoffFun₂_eq_of_boundedPath`,
  `ae_setIntegral_jumpIncrement_cutoffFun₂_eq` — the jump increment agrees with its cut-off at
  every atom of a window of finite intensity, because the state reached by the jump is a value of
  the path; hence the two integrals against the random measure agree.
-/

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.CutoffPath

open LevyStochCalc.Ito.JumpFormulaCutoff

universe u v

variable {Ω : Type u} {n d : ℕ} {E : Type v}

/-- **The continuous integrands agree with their cut-off along a path confined to the ball**, with
no hypothesis on the jump coefficient. The gradient is included: the pathwise form of the jump
part reads it at path values too. -/
theorem integrands_cutoffFun₂_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    JumpFormula.driftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs s (Xp s ω)
          = JumpFormula.driftIntegrand u coeffs s (Xp s ω)
      ∧ JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
          = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω)
      ∧ cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω) = u s (Xp s ω)
      ∧ JumpFormula.gradient (cutoffFun₂ u (2 * (m : ℝ))) s (Xp s ω)
          = JumpFormula.gradient u s (Xp s ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  have hsabs : |s| < 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hTm
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) := hb s hs
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  exact ⟨driftIntegrand_cutoffFun₂ u coeffs hR hsabs hx,
    diffusionIntegrand_cutoffFun₂ u coeffs.σ hR (le_of_lt hsabs) hx,
    cutoffFun₂_eq hR (le_of_lt hsabs) (le_of_lt hx),
    gradient_cutoffFun₂ u hR (le_of_lt hsabs) hx⟩

/-- **A path confined to the ball over the window has not exited by the end of it.** -/
theorem boundedPathSet_subset_le_openExitTime (Xp : ℝ → Ω → Fin n → ℝ) (T : ℝ) (m : ℕ) :
    Brownian.Ito.boundedPathSet Xp T m
      ⊆ {ω : Ω | ((T : ℝ) : WithTop ℝ)
          ≤ Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω} := by
  intro ω hω
  exact Probability.le_openExitTime_of_forall_norm_le fun s hs0 hsT => hω s ⟨hs0, hsT⟩

/-- **The diffusion integrand agrees with its cut-off strictly below the exit time**, in the
shape the strict locality transfer consumes. Strictly below the exit time the path is in the
ball; strictly below `T` the time cut-off is inactive. -/
theorem diffusionIntegrand_cutoffFun₂_eq_of_lt {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) (ω : Ω) (s : ℝ) (hs : 0 < s)
    (hlt : ((s : ℝ) : WithTop ℝ)
      < min (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω) ((T : ℝ) : WithTop ℝ)) :
    JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
      = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  obtain ⟨hltτ, hltT⟩ := lt_min_iff.mp hlt
  have hsT : s < T := by exact_mod_cast hltT
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) :=
    Probability.norm_le_of_lt_openExitTime hs.le hltτ
  have hsabs : |s| ≤ 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.le]
    exact le_of_lt (lt_trans hsT hTm)
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  exact diffusionIntegrand_cutoffFun₂ u coeffs.σ hR hsabs hx

section BrownianTransfer

open MeasureTheory
open LevyStochCalc.Ito.JumpFormula (diffusionIntegrand)

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {E : Type v}

/-- **The Brownian term transfers between a state function and its cut-off** on the event that
the path has not left the ball. The two integrands agree strictly below the minimum of the exit
time and the horizon, and strict locality of the Itô integral turns that into almost sure
equality where the stopping time has not been reached. -/
theorem stochasticIntegralBrownian_cutoffFun₂_eq_of_le
    (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) [ℱ.IsRightContinuous]
    (hℱ : LevyStochCalc.Brownian.IsBrownianFiltration W ℱ)
    {Xp : ℝ → Ω → Fin n → ℝ} {coeffs : Setting.JumpDiffusionCoeffs n d E}
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) (hT : 0 < T)
    (hadapt : Adapted ℱ Xp)
    (hright : ∀ (ω : Ω) (s : ℝ),
      Filter.Tendsto (fun r => Xp r ω) (nhdsWithin s (Set.Ioi s)) (nhds (Xp s ω)))
    (j : Fin d)
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j)
    (hq₁ : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      diffusionIntegrand u coeffs.σ s (Xp s ω) j)
    (hq₂ : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖diffusionIntegrand u coeffs.σ s (Xp s ω) j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ)
        ≤ Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω →
      LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j)
          hm₁ hp₁ hq₁ T ω
        = LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ
            (fun ω s => diffusionIntegrand u coeffs.σ s (Xp s ω) j) hm₂ hp₂ hq₂ T ω := by
  classical
  have hrc : ℱ.rightCont = ℱ := MeasureTheory.Filtration.IsRightContinuous.eq
  have hstopτ : IsStoppingTime ℱ
      (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ)) := by
    have h := Probability.isStoppingTime_openExitTime (ℱ := ℱ) (X := fun ω' s' => Xp s' ω')
      hadapt hright (m : ℝ)
    rwa [hrc] at h
  have hstop : IsStoppingTime ℱ
      (fun ω => min (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω)
        ((T : ℝ) : WithTop ℝ)) := hstopτ.min_const _
  have hagree : ∀ (ω : Ω) (s : ℝ), 0 < s →
      ((s : ℝ) : WithTop ℝ) < min (Probability.openExitTime (fun ω' s' => Xp s' ω') (m : ℝ) ω)
        ((T : ℝ) : WithTop ℝ) →
      diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω) j
        = diffusionIntegrand u coeffs.σ s (Xp s ω) j := by
    intro ω s hs hlt
    exact congrFun (diffusionIntegrand_cutoffFun₂_eq_of_lt u hm hTm ω s hs hlt) j
  have hmain := LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_congr_of_lt W ℱ hℱ
    hstop hm₁ hp₁ hq₁ hm₂ hp₂ hq₂ hagree hT
  filter_upwards [hmain] with ω hω hle
  exact hω (le_min hle le_rfl)

end BrownianTransfer

open LevyStochCalc.Ito.JumpSplitting (leftLimPathAt tendsto_nhdsLT_leftLimPathAt jumpSumLeftAt
  ae_exists_atomEnum_jump_eq_gamma)

/-- The left limit of a path confined to the ball over the window is in the ball. -/
theorem norm_leftLimPathAt_le_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ} {T : ℝ} {m : ℕ} {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) :
    ‖leftLimPathAt Xp θ ω‖ ≤ (m : ℝ) :=
  norm_le_of_tendsto_nhdsLT hθ
    (tendsto_pi_nhds.mpr fun i => tendsto_nhdsLT_leftLimPathAt hleft i) hb

/-- The time window and the ball of a path confined to it sit inside the plateau of the cut-off
of radius `2m`. -/
theorem abs_le_of_mem_Ioc {T : ℝ} {m : ℕ} (hTm : T < 3 * (m : ℝ)) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (0 : ℝ) T) : |θ| ≤ 3 * (2 * (m : ℝ)) / 2 := by
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  rw [hrad, abs_of_nonneg hθ.1.le]
  exact le_of_lt (lt_of_le_of_lt hθ.2 hTm)

/-- The gradient agrees with that of the cut-off at the left limits of a path confined to the
ball. -/
theorem gradient_cutoffFun₂_leftLim_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) :
    JumpFormula.gradient (cutoffFun₂ u (2 * (m : ℝ))) θ (leftLimPathAt Xp θ ω)
      = JumpFormula.gradient u θ (leftLimPathAt Xp θ ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  refine gradient_cutoffFun₂ u hR (abs_le_of_mem_Ioc hTm hθ) ?_
  rw [hrad]
  exact lt_of_le_of_lt (norm_leftLimPathAt_le_of_boundedPath hb hθ hleft) (by linarith)

/-- **The jump increment agrees with its cut-off at an atom of the window, along a path confined
to the ball.** The state reached by the jump is the value of the path at the arrival time, so the
cut-off is inactive at the shifted point as well as at the base point, and no bound on the jump
coefficient is needed. -/
theorem jumpIncrement_cutoffFun₂_eq_of_boundedPath {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m)
    {θ : ℝ} (hθ : θ ∈ Set.Ioc (0 : ℝ) T)
    (hleft : ∀ i : Fin n, ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] θ) (𝓝 L)) {e : E}
    (hjump : Xp θ ω = leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e) :
    cutoffFun₂ u (2 * (m : ℝ)) θ (leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e)
        - cutoffFun₂ u (2 * (m : ℝ)) θ (leftLimPathAt Xp θ ω)
      = u θ (leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e)
        - u θ (leftLimPathAt Xp θ ω) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  have hsabs : |θ| ≤ 3 * (2 * (m : ℝ)) / 2 := abs_le_of_mem_Ioc hTm hθ
  have hbase : ‖leftLimPathAt Xp θ ω‖ ≤ 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad]
    exact le_trans (norm_leftLimPathAt_le_of_boundedPath hb hθ hleft) (by linarith)
  have hshift : ‖leftLimPathAt Xp θ ω + coeffs.γ θ (leftLimPathAt Xp θ ω) e‖
      ≤ 3 * (2 * (m : ℝ)) / 2 := by
    rw [← hjump, hrad]
    exact le_trans (hb θ ⟨hθ.1.le, hθ.2⟩) (by linarith)
  rw [cutoffFun₂_eq hR hsabs hshift, cutoffFun₂_eq hR hsabs hbase]

section JumpTransfer

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] [MeasurableSpace.CountablyGenerated E]
  [MeasurableSingletonClass E] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}

/-- **The cut-off does not change the jump integral against the random measure, on the event the
path stays in the ball.** At finite activity that integral is the sum over the atoms of the
window, and at each atom both the base point and the state reached by the jump are values of the
path, hence in the ball. -/
theorem ae_setIntegral_jumpIncrement_cutoffFun₂_eq
    (coeffs : Setting.JumpDiffusionCoeffs n d E)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (Xp : ℝ → Ω → Fin n → ℝ)
    (A : Set E) (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ} (hm : 0 < m) (hTm : T < 3 * (m : ℝ))
    (V : ℝ → Ω → Fin n → ℝ) (hVc : ∀ᵐ ω ∂P, Continuous fun t => V t ω)
    (hsplit : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ i : Fin n,
      Xp t ω i = V t ω i + jumpSumLeftAt coeffs N Xp A t ω i)
    (hleft : ∀ᵐ ω ∂P, ∀ (t : ℝ) (i : Fin n),
      ∃ L : ℝ, Tendsto (fun s => Xp s ω i) (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ ω ∂P, ω ∈ Brownian.Ito.boundedPathSet Xp T m →
      ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
          (cutoffFun₂ u (2 * (m : ℝ)) q.1
              (leftLimPathAt Xp q.1 ω + coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
            - cutoffFun₂ u (2 * (m : ℝ)) q.1 (leftLimPathAt Xp q.1 ω)) ∂(N.N ω)
        = ∫ q in Set.Ioc (0 : ℝ) T ×ˢ A,
            (u q.1 (leftLimPathAt Xp q.1 ω + coeffs.γ q.1 (leftLimPathAt Xp q.1 ω) q.2)
              - u q.1 (leftLimPathAt Xp q.1 ω)) ∂(N.N ω) := by
  filter_upwards [ae_exists_atomEnum_jump_eq_gamma coeffs N Xp A hA hAν T V hVc hsplit, hleft]
    with ω hω hlω hb
  obtain ⟨K, θ, ε, -, hmem, hg, hjump⟩ := hω
  rw [hg, hg]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact jumpIncrement_cutoffFun₂_eq_of_boundedPath u hm hTm hb (hmem j).1
    (fun i => hlω (θ j) i) (hjump j)

end JumpTransfer

end LevyStochCalc.Ito.CutoffPath
