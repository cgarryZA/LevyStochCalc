/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormula
import LevyStochCalc.Ito.ItoFormulaExhaustion
import LevyStochCalc.Ito.ItoFormulaLocalised

/-!
# Cutting a function of time and space off outside a box

Multiplying a function of time and space by the product of a one-dimensional smooth cutoff in
time with a box cutoff in space leaves it, together with its time derivative and its first two
space derivatives, unchanged on a box around the origin, and gives it compact support. Along a
path that stays in a ball over a bounded window the two functions therefore give the same
Itô–Lévy integrands, except at the shifted state `x + γ(s, x, e)` reached by a jump, which needs
its own bound. A càdlàg path is bounded on a compact interval, so the events on which a path
stays in a ball over the window exhaust the sample space; the same exhaustion carries the
increment formula for a translated path from functions with globally bounded derivatives to
functions with none, with no bound on the translation.

## Main definitions

* `LevyStochCalc.Ito.JumpFormulaCutoff.timeBoxCut` — the time–space cutoff.
* `LevyStochCalc.Ito.JumpFormulaCutoff.cutoffFun₂` — a function of time and space multiplied by
  it.
* `LevyStochCalc.Ito.JumpFormulaCutoff.boundedJumpSet` — the sample points whose jump coefficient
  along the path is bounded over the window, uniformly in the mark.

## Main statements

* `LevyStochCalc.Ito.JumpFormulaCutoff.ae_exists_bound_norm` — almost every path of a jump
  diffusion is bounded over a bounded window.
* `LevyStochCalc.Ito.JumpFormulaCutoff.integrands_cutoffFun₂_eq_of_mem` — on the members of the
  two exhausting families the cutoff carries the same drift, diffusion, compensator-drift and
  jump integrands as the function itself.
* `LevyStochCalc.Ito.JumpFormulaCutoff.itoFormula_between_shift_localise` — Itô's formula for the
  increment of a translated path between two ordered stopping times, for a twice continuously
  differentiable function, with no bound on the derivatives and none on the translation.
* `LevyStochCalc.Ito.JumpFormulaCutoff.stochasticIntegralBrownian_stopped_sub_congr_of_mem` — the
  matching of the stochastic terms that theorem takes as input, from a stopping time below which
  the two integrands agree.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

universe u v

section Cutoff

variable {n : ℕ}

/-- The product of the one-dimensional smooth cutoff in time with the box cutoff in space. -/
noncomputable def timeBoxCut (R : ℝ) (z : ℝ × (Fin n → ℝ)) : ℝ :=
  smoothCut R z.1 * boxCut R z.2

/-- The product of a function of time and space with the time–space cutoff of radius `R`. -/
noncomputable def cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) (R : ℝ) : ℝ → (Fin n → ℝ) → ℝ :=
  fun s x => u s x * timeBoxCut R (s, x)

theorem uncurry_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) (R : ℝ) :
    Function.uncurry (cutoffFun₂ u R) = fun z => Function.uncurry u z * timeBoxCut R z := rfl

theorem contDiff_timeBoxCut (R : ℝ) : ContDiff ℝ 2 (timeBoxCut (n := n) R) :=
  ((contDiff_smoothCut R).comp contDiff_fst).mul ((contDiff_boxCut R).comp contDiff_snd)

theorem timeBoxCut_eq_one {R : ℝ} (hR : 0 < R) {z : ℝ × (Fin n → ℝ)} (hz : ‖z‖ ≤ 3 * R / 2) :
    timeBoxCut R z = 1 := by
  rw [Prod.norm_def, max_le_iff] at hz
  rw [timeBoxCut, smoothCut_eq_one hR (by simpa [Real.norm_eq_abs] using hz.1),
    boxCut_eq_one hR hz.2, mul_one]

theorem timeBoxCut_eq_zero {R : ℝ} (hR : 0 < R) {z : ℝ × (Fin n → ℝ)} (hz : 2 * R < ‖z‖) :
    timeBoxCut R z = 0 := by
  rw [Prod.norm_def, lt_max_iff] at hz
  rcases hz with h | h
  · rw [timeBoxCut, smoothCut_eq_zero hR (by simpa [Real.norm_eq_abs] using h.le), zero_mul]
  · rw [timeBoxCut, boxCut_eq_zero hR h, mul_zero]

theorem hasCompactSupport_timeBoxCut {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (timeBoxCut (n := n) R) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ × (Fin n → ℝ)) (2 * R))
    fun z hz => ?_
  refine timeBoxCut_eq_zero hR ?_
  simpa [Metric.mem_closedBall, dist_eq_norm] using not_le.mp fun h => hz (by simpa using h)

theorem timeBoxCut_eventuallyEq_one {R : ℝ} (hR : 0 < R) {z : ℝ × (Fin n → ℝ)}
    (hz : ‖z‖ < 3 * R / 2) : timeBoxCut (n := n) R =ᶠ[𝓝 z] fun _ => (1 : ℝ) := by
  have hopen : IsOpen {w : ℝ × (Fin n → ℝ) | ‖w‖ < 3 * R / 2} :=
    isOpen_lt continuous_norm continuous_const
  filter_upwards [hopen.mem_nhds hz] with w hw
  exact timeBoxCut_eq_one hR hw.le

theorem contDiff_uncurry_cutoffFun₂ {u : ℝ → (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ 2 (Function.uncurry u)) (R : ℝ) :
    ContDiff ℝ 2 (Function.uncurry (cutoffFun₂ u R)) := by
  rw [uncurry_cutoffFun₂]
  exact hu.mul (contDiff_timeBoxCut R)

theorem hasCompactSupport_uncurry_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R : ℝ} (hR : 0 < R) :
    HasCompactSupport (Function.uncurry (cutoffFun₂ u R)) := by
  rw [uncurry_cutoffFun₂]
  exact (hasCompactSupport_timeBoxCut hR).mul_left

/-- At a time inside the window the cutoff is the space cutoff of the time slice. -/
theorem cutoffFun₂_slice (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| ≤ 3 * R / 2) : cutoffFun₂ u R s = cutoffFun (u s) R := by
  funext x
  simp only [cutoffFun₂, timeBoxCut, cutoffFun, smoothCut_eq_one hR hs, one_mul]

theorem cutoffFun₂_eq {u : ℝ → (Fin n → ℝ) → ℝ} {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ ≤ 3 * R / 2) : cutoffFun₂ u R s x = u s x := by
  simp only [cutoffFun₂, timeBoxCut, smoothCut_eq_one hR hs, boxCut_eq_one hR hx, mul_one]

/-- The space gradient of the cutoff agrees with that of the function inside the window. -/
theorem gradient_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| ≤ 3 * R / 2) {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.gradient (cutoffFun₂ u R) s x = JumpFormula.gradient u s x := by
  funext i
  simp only [JumpFormula.gradient, cutoffFun₂_slice u hR hs, fderiv_cutoffFun hR hx]

/-- The space Hessian of the cutoff agrees with that of the function inside the window. -/
theorem hessian_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| ≤ 3 * R / 2) {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.hessian (cutoffFun₂ u R) s x = JumpFormula.hessian u s x := by
  have hopen : IsOpen {w : Fin n → ℝ | ‖w‖ < 3 * R / 2} :=
    isOpen_lt continuous_norm continuous_const
  funext i j
  simp only [JumpFormula.hessian, cutoffFun₂_slice u hR hs]
  have hev : (fun y => fderiv ℝ (cutoffFun (u s) R) y (Pi.single i 1))
      =ᶠ[𝓝 x] fun y => fderiv ℝ (u s) y (Pi.single i 1) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [fderiv_cutoffFun hR hy]
  rw [hev.fderiv_eq]

/-- The time derivative of the cutoff agrees with that of the function inside the window. -/
theorem timeDeriv_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ) {R s : ℝ} (hR : 0 < R)
    (hs : |s| < 3 * R / 2) {x : Fin n → ℝ} (hx : ‖x‖ ≤ 3 * R / 2) :
    JumpFormula.timeDeriv (cutoffFun₂ u R) s x = JumpFormula.timeDeriv u s x := by
  have hopen : IsOpen {t : ℝ | |t| < 3 * R / 2} := isOpen_lt continuous_abs continuous_const
  have hev : (fun t => cutoffFun₂ u R t x) =ᶠ[𝓝 s] fun t => u t x := by
    filter_upwards [hopen.mem_nhds hs] with t ht
    exact cutoffFun₂_eq hR (le_of_lt ht) hx
  simp only [JumpFormula.timeDeriv]
  exact hev.deriv_eq

end Cutoff

section Integrands

variable {n d : ℕ} {E : Type v}

/-- The diffusion integrand of the cutoff agrees with that of the function inside the window. -/
theorem diffusionIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)) {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.diffusionIntegrand (cutoffFun₂ u R) σ s x
      = JumpFormula.diffusionIntegrand u σ s x := by
  funext j
  simp only [JumpFormula.diffusionIntegrand, gradient_cutoffFun₂ u hR hs hx]

/-- The drift integrand of the cutoff agrees with that of the function inside the window. -/
theorem driftIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (coeffs : Setting.JumpDiffusionCoeffs n d E) {R s : ℝ} (hR : 0 < R) (hs : |s| < 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) :
    JumpFormula.driftIntegrand (cutoffFun₂ u R) coeffs s x
      = JumpFormula.driftIntegrand u coeffs s x := by
  simp only [JumpFormula.driftIntegrand, JumpFormula.levyGenerator,
    timeDeriv_cutoffFun₂ u hR hs (le_of_lt hx), gradient_cutoffFun₂ u hR (le_of_lt hs) hx,
    hessian_cutoffFun₂ u hR (le_of_lt hs) hx]

/-- The compensator-drift integrand of the cutoff agrees with that of the function inside the
window, provided the shifted state also lies inside it. -/
theorem compensatorDriftIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ < 3 * R / 2) (e : E) (hxe : ‖x + γ s x e‖ ≤ 3 * R / 2) :
    JumpFormula.compensatorDriftIntegrand (cutoffFun₂ u R) γ s x e
      = JumpFormula.compensatorDriftIntegrand u γ s x e := by
  simp only [JumpFormula.compensatorDriftIntegrand, gradient_cutoffFun₂ u hR hs hx,
    cutoffFun₂_eq hR hs hxe, cutoffFun₂_eq hR hs (le_of_lt hx)]

/-- The jump integrand of the cutoff agrees with that of the function inside the window,
provided the shifted state also lies inside it. -/
theorem jumpIntegrand_cutoffFun₂ (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) {R s : ℝ} (hR : 0 < R) (hs : |s| ≤ 3 * R / 2)
    {x : Fin n → ℝ} (hx : ‖x‖ ≤ 3 * R / 2) (e : E) (hxe : ‖x + γ s x e‖ ≤ 3 * R / 2) :
    cutoffFun₂ u R s (x + γ s x e) - cutoffFun₂ u R s x = u s (x + γ s x e) - u s x := by
  rw [cutoffFun₂_eq hR hs hxe, cutoffFun₂_eq hR hs hx]

end Integrands

section Cadlag

/-- A function that is bounded near every point of a compact interval is bounded on it. -/
theorem exists_bound_of_locally_bounded {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {T : ℝ}
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ M : ℝ, ∀ᶠ s in 𝓝 t, ‖f s‖ ≤ M) :
    ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖f s‖ ≤ M := by
  classical
  choose! M hM using h
  obtain ⟨A, -, hcov⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).elim_nhds_subcover
    (fun t => {s : ℝ | ‖f s‖ ≤ M t}) fun t ht => hM t ht
  refine ⟨∑ t ∈ A, |M t|, fun s hs => ?_⟩
  obtain ⟨t, htA, hst⟩ := Set.mem_iUnion₂.1 (hcov hs)
  exact le_trans (le_trans hst (le_abs_self _))
    (Finset.single_le_sum (fun i _ => abs_nonneg (M i)) htA)

/-- Right-continuity at a point together with a left limit there bounds the function on a
neighbourhood of the point. -/
theorem exists_eventually_norm_le {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {t : ℝ} {L : F}
    (hr : Filter.Tendsto f (𝓝[>] t) (𝓝 (f t))) (hl : Filter.Tendsto f (𝓝[<] t) (𝓝 L)) :
    ∃ M : ℝ, ∀ᶠ s in 𝓝 t, ‖f s‖ ≤ M := by
  refine ⟨max (‖f t‖ + 1) (‖L‖ + 1), ?_⟩
  have hlt : ∀ᶠ s in 𝓝[<] t, ‖f s‖ ≤ max (‖f t‖ + 1) (‖L‖ + 1) := by
    filter_upwards [hl.norm.eventually_lt_const (lt_add_one ‖L‖)] with s hs
    exact le_trans hs.le (le_max_right _ _)
  have hgt : ∀ᶠ s in 𝓝[>] t, ‖f s‖ ≤ max (‖f t‖ + 1) (‖L‖ + 1) := by
    filter_upwards [hr.norm.eventually_lt_const (lt_add_one ‖f t‖)] with s hs
    exact le_trans hs.le (le_max_left _ _)
  have hpt : ∀ᶠ s in 𝓝[{t}] t, ‖f s‖ ≤ max (‖f t‖ + 1) (‖L‖ + 1) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    rw [show s = t from hs]
    exact le_trans (by linarith : ‖f t‖ ≤ ‖f t‖ + 1) (le_max_left _ _)
  rw [← nhdsLT_sup_nhdsGE t, ← nhdsGT_sup_nhdsWithin_singleton t]
  exact Filter.eventually_sup.2 ⟨hlt, Filter.eventually_sup.2 ⟨hgt, hpt⟩⟩

/-- A left limit of a path bounded over a window is bounded by the same constant. -/
theorem norm_le_of_tendsto_nhdsLT {F : Type*} [NormedAddCommGroup F] {f : ℝ → F} {T M t : ℝ}
    (ht : t ∈ Set.Ioc (0 : ℝ) T) {L : F} (hL : Filter.Tendsto f (𝓝[<] t) (𝓝 L))
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖f s‖ ≤ M) : ‖L‖ ≤ M := by
  refine le_of_tendsto hL.norm ?_
  have h0 : ∀ᶠ s in 𝓝[<] t, 0 < s :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_gt_nhds ht.1)
  filter_upwards [h0, self_mem_nhdsWithin] with s hs0 hst
  exact hb s ⟨hs0.le, le_trans (le_of_lt hst) ht.2⟩

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- Almost every path of a jump diffusion is bounded over a bounded window. -/
theorem ae_exists_bound_norm (X : Setting.JumpDiffusion W N coeffs x₀) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X.X s ω‖ ≤ M := by
  filter_upwards [X.cadlag_paths] with ω hω
  refine exists_bound_of_locally_bounded fun t ht => ?_
  obtain ⟨hr, hl⟩ := hω t ht.1
  choose L hL using hl
  exact exists_eventually_norm_le hr (tendsto_pi_nhds.2 hL)

/-- Almost every path of a jump diffusion lies in one member of the exhausting family of events
on which the path stays in a ball over a bounded window. -/
theorem ae_exists_mem_boundedPathSet (X : Setting.JumpDiffusion W N coeffs x₀) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ Brownian.Ito.boundedPathSet X.X T m :=
  Brownian.Ito.ae_exists_mem_boundedPathSet (ae_exists_bound_norm X T)

end Cadlag

section Localising

variable {Ω : Type u} {E : Type v} {n d : ℕ}

/-- The sample points whose jump coefficient along the path is bounded by `m` over `[0, T]`,
uniformly in the mark. -/
def boundedJumpSet (Xp : ℝ → Ω → Fin n → ℝ) (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (T : ℝ)
    (m : ℕ) : Set Ω :=
  {ω : Ω | ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e : E, ‖γ s (Xp s ω) e‖ ≤ (m : ℝ)}

theorem boundedJumpSet_mono (Xp : ℝ → Ω → Fin n → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (T : ℝ) {m m' : ℕ} (h : m ≤ m') :
    boundedJumpSet Xp γ T m ⊆ boundedJumpSet Xp γ T m' := fun _ hω s hs e =>
  (hω s hs e).trans (by exact_mod_cast h)

/-- On the `m`-th member of the two exhausting families the cutoff of radius `2m` carries, along
the path and for every mark, the same drift, diffusion, compensator-drift and jump integrands as
the function itself. -/
theorem integrands_cutoffFun₂_eq_of_mem {Xp : ℝ → Ω → Fin n → ℝ}
    {coeffs : Setting.JumpDiffusionCoeffs n d E} (u : ℝ → (Fin n → ℝ) → ℝ) {T : ℝ} {m : ℕ}
    (hm : 0 < m) (hTm : T < 3 * (m : ℝ)) {ω : Ω}
    (hb : ω ∈ Brownian.Ito.boundedPathSet Xp T m) (hj : ω ∈ boundedJumpSet Xp coeffs.γ T m)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    JumpFormula.driftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs s (Xp s ω)
          = JumpFormula.driftIntegrand u coeffs s (Xp s ω)
      ∧ JumpFormula.diffusionIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.σ s (Xp s ω)
          = JumpFormula.diffusionIntegrand u coeffs.σ s (Xp s ω)
      ∧ cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω) = u s (Xp s ω)
      ∧ (∀ e : E,
          JumpFormula.compensatorDriftIntegrand (cutoffFun₂ u (2 * (m : ℝ))) coeffs.γ s
              (Xp s ω) e
            = JumpFormula.compensatorDriftIntegrand u coeffs.γ s (Xp s ω) e)
      ∧ (∀ e : E, cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω + coeffs.γ s (Xp s ω) e)
              - cutoffFun₂ u (2 * (m : ℝ)) s (Xp s ω)
            = u s (Xp s ω + coeffs.γ s (Xp s ω) e) - u s (Xp s ω)) := by
  have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hR : (0 : ℝ) < 2 * (m : ℝ) := by linarith
  have hrad : 3 * (2 * (m : ℝ)) / 2 = 3 * (m : ℝ) := by ring
  have hsabs : |s| < 3 * (2 * (m : ℝ)) / 2 := by
    rw [hrad, abs_of_nonneg hs.1]
    exact lt_of_le_of_lt hs.2 hTm
  have hxb : ‖Xp s ω‖ ≤ (m : ℝ) := hb s hs
  have hx : ‖Xp s ω‖ < 3 * (2 * (m : ℝ)) / 2 := by rw [hrad]; linarith
  have hxe : ∀ e : E, ‖Xp s ω + coeffs.γ s (Xp s ω) e‖ ≤ 3 * (2 * (m : ℝ)) / 2 := by
    intro e
    refine le_trans (norm_add_le _ _) ?_
    have := hj s hs e
    rw [hrad]
    linarith
  refine ⟨driftIntegrand_cutoffFun₂ u coeffs hR hsabs hx,
    diffusionIntegrand_cutoffFun₂ u coeffs.σ hR (le_of_lt hsabs) hx,
    cutoffFun₂_eq hR (le_of_lt hsabs) (le_of_lt hx), fun e => ?_, fun e => ?_⟩
  · exact compensatorDriftIntegrand_cutoffFun₂ u coeffs.γ hR (le_of_lt hsabs) hx e (hxe e)
  · exact jumpIntegrand_cutoffFun₂ u coeffs.γ hR (le_of_lt hsabs) (le_of_lt hx) e (hxe e)

variable [MeasurableSpace Ω] {P : Measure Ω}

/-- If almost every path carries a jump coefficient bounded over the window, the family of events
on which that bound is `m` covers almost every sample point. -/
theorem ae_exists_mem_boundedJumpSet {Xp : ℝ → Ω → Fin n → ℝ}
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {T : ℝ}
    (h : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e : E, ‖γ s (Xp s ω) e‖ ≤ M) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ boundedJumpSet Xp γ T m := by
  filter_upwards [h] with ω hω
  obtain ⟨M, hM⟩ := hω
  obtain ⟨m, hm⟩ := exists_nat_ge M
  exact ⟨m, fun s hs e => (hM s hs e).trans hm⟩

/-- Two exhausting families and a lower bound on the radius forced by the window combine into a
single exhausting family. -/
theorem ae_exists_mem_inter {Xp : ℝ → Ω → Fin n → ℝ}
    {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)} {T : ℝ}
    (hb : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ Brownian.Ito.boundedPathSet Xp T m)
    (hj : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ boundedJumpSet Xp γ T m) :
    ∀ᵐ ω ∂P, ∃ m : ℕ, 0 < m ∧ T < 3 * (m : ℝ) ∧
      ω ∈ Brownian.Ito.boundedPathSet Xp T m ∧ ω ∈ boundedJumpSet Xp γ T m := by
  filter_upwards [hb, hj] with ω hbω hjω
  obtain ⟨m₁, hm₁⟩ := hbω
  obtain ⟨m₂, hm₂⟩ := hjω
  set M : ℕ := max (max m₁ m₂) (⌊T⌋₊ + 1) with hMdef
  have hMge : ⌊T⌋₊ + 1 ≤ M := le_max_right _ _
  have h2 : (⌊T⌋₊ : ℝ) + 1 ≤ (M : ℝ) := by exact_mod_cast hMge
  have h3 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  refine ⟨M, Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (Nat.le_add_left 1 ⌊T⌋₊) hMge), ?_,
    Brownian.Ito.boundedPathSet_mono Xp T
      (le_trans (le_max_left m₁ m₂) (le_max_left _ _)) hm₁,
    boundedJumpSet_mono Xp γ T (le_trans (le_max_right m₁ m₂) (le_max_left _ _)) hm₂⟩
  linarith [Nat.lt_floor_add_one T]

end Localising

section Localise

open LevyStochCalc.Brownian.Ito

/-- Two integrands agreeing strictly between two ordered stopping times give the same increment
of the cut-off integrand. -/
theorem stopped_sub_congr {Ω : Type u} {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω)
    {A B : Ω → ℝ → ℝ} {ω : Ω} {s : ℝ}
    (h : σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω → A ω s = B ω s) :
    Probability.stopped τ A ω s - Probability.stopped σ A ω s
      = Probability.stopped τ B ω s - Probability.stopped σ B ω s := by
  simp only [Probability.stopped]
  by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
  · by_cases hσs : ((s : ℝ) : WithTop ℝ) ≤ σ ω
    · simp only [if_pos hτs, if_pos hσs, sub_self]
    · simp only [if_pos hτs, if_neg hσs, sub_zero, h (not_le.mp hσs) hτs]
  · have hσs : ¬(((s : ℝ) : WithTop ℝ) ≤ σ ω) := fun hh => hτs (hh.trans (hστ ω))
    simp only [if_neg hτs, if_neg hσs]

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

set_option maxHeartbeats 1000000 in
/-- **Itô's formula for the increment of a path between two ordered stopping times, for a twice
continuously differentiable function translated by a random vector.** Neither the derivatives of
the function nor the translation carry a global bound: the family of events on which the
translated path stays in a ball over the window supplies the localisation, and the stochastic
terms are matched there by hypothesis. -/
theorem itoFormula_between_shift_localise
    (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (W.W k) ℱ')
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {T : ℝ}
    {c : Ω → Fin n → ℝ} (hc : Measurable c)
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hpShift : ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → ∀ (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s => φ (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped σ (fun ω s => φ (X s ω + c ω) * H p k ω s) ω s)
    (S : ℕ → Set Ω) (hScover : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ S m)
    (hSball : ∀ (m : ℕ) (ω : Ω), ω ∈ S m → ∀ s : ℝ, σ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) ≤ τ ω → ‖X s ω + c ω‖ ≤ (m : ℝ))
    (hSend : ∀ (m : ℕ) (ω : Ω), ω ∈ S m →
      ‖X (clipTime τ T ω) ω + c ω‖ ≤ (m : ℝ) ∧ ‖X (clipTime σ T ω) ω + c ω‖ ≤ (m : ℝ))
    (hSI : ∀ (m : ℕ) (p : Fin n) (k : Fin d)
      (hmg : Measurable (Function.uncurry fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s))
      (hpg : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s)
      (hqg : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      ∀ᵐ ω ∂P, ω ∈ S m →
        stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                    * H p k ω s) ω s
                - Probability.stopped σ (fun ω s =>
                    coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                      * H p k ω s) ω s)
            hmg hpg hqg T ω
          = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
            (hmSc p k) (hpSc p k) (hqSc p k) T ω)
    (hbase : ∀ (g : (Fin n → ℝ) → ℝ) (g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
      (g'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      ContDiff ℝ 2 g → (∀ z, HasFDerivAt g (g' z) z) → (∀ z, HasFDerivAt g' (g'' z) z) →
      (∀ (p : Fin n) (z : Fin n → ℝ), |coordDeriv g' p z| ≤ K₁) →
      (∀ (p q : Fin n) (z : Fin n → ℝ), |coordDeriv₂ g'' p q z| ≤ K₂) →
      ∀ (hmSg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s))
        (hpSg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s)
        (hqSg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖Probability.stopped τ
                  (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s‖₊
              : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω : Ω => g (X (clipTime τ T ω) ω + c ω) - g (X (clipTime σ T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv g' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped τ
                      (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped σ
                        (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSg p k) (hpSg p k) (hqSg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped τ (fun ω s => coordDeriv₂ g'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped σ (fun ω s => coordDeriv₂ g'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hf'eq : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
  have hf''eq : f'' = fderiv ℝ (fderiv ℝ f) := by
    funext z
    have hz := (hf' z).fderiv
    rw [← hf'eq]
    exact hz.symm
  refine ae_eq_of_ae_eq_on_exhausting hScover ?_
  intro m
  have hR0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hRlt : (m : ℝ) < 3 * ((m : ℝ) + 1) / 2 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hXcm : Measurable (Function.uncurry fun ω s => X s ω + c ω) :=
    hXm.add (hc.comp measurable_fst)
  have hgC : ContDiff ℝ 2 (cutoffFun f ((m : ℝ) + 1)) := contDiff_cutoffFun hfC _
  have hgf : ∀ z, HasFDerivAt (cutoffFun f ((m : ℝ) + 1))
      (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)) z) z :=
    fun z => (differentiable_cutoffFun hfC _ z).hasFDerivAt
  have hgf' : ∀ z, HasFDerivAt (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))
      (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) z) z :=
    fun z => (differentiable_fderiv_cutoffFun hfC _ z).hasFDerivAt
  have hg'c : Continuous (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) :=
    continuous_fderiv_cutoffFun hfC _
  obtain ⟨K₁, hK₁n⟩ := exists_bound_fderiv_cutoffFun hfC hR0
  obtain ⟨K₂, hK₂0, hK₂n⟩ := exists_bound_fderiv_fderiv_cutoffFun hfC hR0
  have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hK₁n 0)
  have hK₁c : ∀ (p : Fin n) (z : Fin n → ℝ),
      |coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p z| ≤ K₁ :=
    fun p => abs_coordDeriv_le hK₁n p
  have hK₂c : ∀ (p q : Fin n) (z : Fin n → ℝ),
      |coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q z| ≤ K₂ :=
    fun p q => abs_coordDeriv₂_le hK₂n p q
  have hcut : ∀ (p : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * ((m : ℝ) + 1) / 2 →
      coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p z = coordDeriv f' p z := by
    intro p z hz
    rw [hf'eq]
    unfold coordDeriv
    rw [fderiv_cutoffFun (f := f) hR0 hz]
  have hcut₂ : ∀ (p q : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * ((m : ℝ) + 1) / 2 →
      coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q z
        = coordDeriv₂ f'' p q z := by
    intro p q z hz
    rw [hf''eq]
    unfold coordDeriv₂
    rw [fderiv_fderiv_cutoffFun (f := f) hR0 hz]
  have hcut₀ : ∀ z : Fin n → ℝ, ‖z‖ < 3 * ((m : ℝ) + 1) / 2 →
      cutoffFun f ((m : ℝ) + 1) z = f z := by
    intro z hz
    rw [cutoffFun, boxCut_eq_one hR0 hz.le, mul_one]
  have hmAg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H p k ω s) :=
    fun p k => ((continuous_coordDeriv hg'c p).measurable.comp hXcm).mul (hHm p k)
  have hqAg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
          * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    refine energy_lt_top_of_abs_le_mul (c := K₁) hK₁0 (fun ω s => ?_) (hHs p k)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁c p _) (abs_nonneg _)
  have hmSg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s =>
          coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
            * H p k ω s) ω s
        - Probability.stopped σ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s) := fun p k =>
    measurable_uncurry_stopped_sub hσ hτ (hmAg p k)
  have hpSg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s =>
          coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
            * H p k ω s) ω s
        - Probability.stopped σ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s := fun p k =>
    hpShift (coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p)
      (continuous_coordDeriv hg'c p) p k
  have hqSg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun p k =>
    energy_stopped_sub_lt_top hσ hτ (hmAg p k) (hqAg p k)
  have hform := hbase (cutoffFun f ((m : ℝ) + 1)) (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))
    (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) K₁ K₂ hgC hgf hgf' hK₁c hK₂c
    hmSg hpSg hqSg
  have hSIall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d), ω ∈ S m →
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            Probability.stopped τ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s
              - Probability.stopped σ (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                    * H p k ω s) ω s)
          (hmSg p k) (hpSg p k) (hqSg p k) T ω
        = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            Probability.stopped τ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
          (hmSc p k) (hpSc p k) (hqSc p k) T ω := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact hSI m p k (hmSg p k) (hpSg p k) (hqSg p k)
  filter_upwards [hform, hSIall] with ω hω hSIω hmem
  have hball : ∀ s : ℝ, σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω →
      ‖X s ω + c ω‖ < 3 * ((m : ℝ) + 1) / 2 := fun s h1 h2 =>
    lt_of_le_of_lt (hSball m ω hmem s h1 h2) hRlt
  have hendτ : ‖X (clipTime τ T ω) ω + c ω‖ < 3 * ((m : ℝ) + 1) / 2 :=
    lt_of_le_of_lt (hSend m ω hmem).1 hRlt
  have hendσ : ‖X (clipTime σ T ω) ω + c ω‖ < 3 * ((m : ℝ) + 1) / 2 :=
    lt_of_le_of_lt (hSend m ω hmem).2 hRlt
  have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * bdrift p ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * bdrift p ω s) ω s) ∂volume)
      = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume := by
    refine Finset.sum_congr rfl fun p _ => ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    refine stopped_sub_congr hστ fun h1 h2 => ?_
    rw [hcut p _ (hball s h1 h2)]
  have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s =>
              coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
    refine congrArg (fun x => 1 / 2 * x) ?_
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    refine stopped_sub_congr hστ fun h1 h2 => ?_
    rw [hcut₂ p q _ (hball s h1 h2)]
  have e2 : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s)
        (hmSg p k) (hpSg p k) (hqSg p k) T ω)
      = ∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
        (hmSc p k) (hpSc p k) (hqSc p k) T ω :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => hSIω p k hmem
  rw [← hcut₀ _ hendτ, ← hcut₀ _ hendσ, hω, e1, e2, e3]

/-- Two stopped increments whose integrands agree between the two stopping times and below a
third one have the same Itô integral on an event where that third time has not been reached. -/
theorem stochasticIntegralBrownian_stopped_sub_congr_of_mem
    (W : Brownian.BrownianMotion P) (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : Brownian.IsBrownianFiltration W ℱ')
    {σ τ ρ : Ω → WithTop ℝ} (hρ : MeasureTheory.IsStoppingTime ℱ' ρ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {A B : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ A ω s - Probability.stopped σ A ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ A ω s - Probability.stopped σ A ω s)
    (hq₁ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ A ω s - Probability.stopped σ A ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ B ω s - Probability.stopped σ B ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ B ω s - Probability.stopped σ B ω s)
    (hq₂ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ B ω s - Probability.stopped σ B ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ ρ ω →
      σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω → A ω s = B ω s)
    {T : ℝ} (hT : 0 < T) {Sset : Set Ω}
    (hS : ∀ ω ∈ Sset, ((T : ℝ) : WithTop ℝ) ≤ ρ ω) :
    ∀ᵐ ω ∂P, ω ∈ Sset →
      stochasticIntegralBrownian W ℱ' hℱ
          (fun ω s => Probability.stopped τ A ω s - Probability.stopped σ A ω s)
          hm₁ hp₁ hq₁ T ω
        = stochasticIntegralBrownian W ℱ' hℱ
          (fun ω s => Probability.stopped τ B ω s - Probability.stopped σ B ω s)
          hm₂ hp₂ hq₂ T ω := by
  have h := stochasticIntegralBrownian_congr_of_le ρ W ℱ' hℱ hρ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂
    (fun ω s hs hle => stopped_sub_congr hστ fun h1 h2 => hagree ω s hs hle h1 h2) hT
  filter_upwards [h] with ω hω hmem
  exact hω (hS ω hmem)

end Localise

end LevyStochCalc.Ito.JumpFormulaCutoff
