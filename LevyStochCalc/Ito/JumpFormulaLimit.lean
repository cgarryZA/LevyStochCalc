/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaFiniteActivity

/-!
# The small-jump limit of the Itô–Lévy formula

The finite-activity Itô–Lévy formula applies to a jump diffusion whose jump coefficient is cut to
a set of marks. Along a family `A : ℕ → Set E` of small-jump sets with `ν`-null intersection the
cut coefficients restore the original ones, and the formula is passed to the limit term by term:
the increment of the state function and the drift, diffusion and compensated jump terms converge
along the truncated paths, and the compensator-drift term converges by dominated convergence on
the product of the time window with the intensity. The identity of the limits is then the
uniqueness of the limit of a real sequence, read on the two sides of the formula.

Cutting the jump coefficient to a set of marks leaves the drift integrand `∂_t u + 𝓛u` unchanged
— it reads only `μ` and `σ` — and turns the compensator-drift integrand into its restriction to
that set. The two presentations of the drift differ by the first-order term `∑ᵢ ∂ᵢu ∫ γᵢ dν`,
which is finite only when the jump coefficient is `ν`-integrable: for a jump coefficient that is
merely square-integrable near the small marks, the first-order term and the mark integral of the
jump increment `u(x + γ) − u(x)` each diverge and only their difference, the compensator-drift
integrand `u(x + γ) − u(x) − γᵀ∇u`, is integrable. The limit statements below are therefore
carried by the compensator-drift integrand; the first-order term is passed to the limit
separately only under an integrability hypothesis on the jump coefficient itself.

## Main definitions

* `LevyStochCalc.Ito.JumpFormula.markTruncCoeffs` — the coefficient bundle with the jump
  coefficient cut to a set of marks.
* `LevyStochCalc.Ito.JumpFormula.firstOrderIntegrand` — the first-order term `∑ᵢ γᵢ ∂ᵢu` of the
  compensator-drift integrand.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_of_antitone`,
  `LevyStochCalc.Ito.JumpFormula.ae_eventually_notMem_comp` — almost every mark eventually lies
  outside an antitone family of mark sets with null intersection, also along a subsequence.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_of_dominated` — dominated convergence for
  the mark integral over the complements of the family, integrated over a time window.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_compensatorDrift` — the compensator-drift
  integrals over the complements of the family converge to the compensator-drift integral over
  the whole mark space along the limit path.
* `LevyStochCalc.Ito.JumpFormula.tendsto_setIntegral_firstOrder` — the same for the first-order
  term, under integrability of the jump coefficient against the intensity.
* `LevyStochCalc.Ito.JumpFormula.driftIntegrand_markTruncCoeffs`,
  `LevyStochCalc.Ito.JumpFormula.integral_compensatorDriftIntegrand_markTruncCoeffs` — cutting
  the jump coefficient leaves the drift integrand unchanged and restricts the compensator-drift
  integral to the cut.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_sub_of_markTruncCoeffs` — the Itô–Lévy identity for cut
  coefficients, in the vocabulary of the uncut ones.
* `LevyStochCalc.Ito.JumpFormula.itoLevy_of_tendsto`,
  `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto` — the two sides of an identity of
  real sequences have equal limits, pointwise and almost surely.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_terms` — the Itô–Lévy identity along
  the limit path, from the identities along the truncated paths with the drift and
  compensator-drift terms given as arbitrary sequences, and the convergence of the five terms.
* `LevyStochCalc.Ito.JumpFormula.ae_itoLevy_of_ae_tendsto_integrals` — the same with the drift
  and compensator-drift terms given as the integrals along the truncated paths, the latter over
  the complements of the truncated mark sets.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed., 2009, Theorem 4.4.7, step (II).
-/

open MeasureTheory Filter Topology
open LevyStochCalc.Ito.Setting

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section MarkSets

variable {E : Type v} [MeasurableSpace E] {ν : Measure E}

/-- Along an antitone family of mark sets whose intersection is `ν`-null, almost every mark lies
outside all but finitely many members of the family. -/
theorem ae_eventually_notMem_of_antitone {A : ℕ → Set E} (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with e he
  simp only [Set.mem_iInter, not_forall] at he
  obtain ⟨m₀, hm₀⟩ := he
  filter_upwards [eventually_ge_atTop m₀] with m hm
  exact fun hcon => hm₀ (hanti hm hcon)

/-- Reading an antitone family of mark sets with `ν`-null intersection along an index map that
dominates the identity keeps almost every mark eventually outside the family. -/
theorem ae_eventually_notMem_comp {A : ℕ → Set E} (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {ms : ℕ → ℕ} (hms : ∀ k, k ≤ ms k) :
    ∀ᵐ e ∂ν, ∀ᶠ k in atTop, e ∉ A (ms k) := by
  filter_upwards [ae_eventually_notMem_of_antitone hanti hnull] with e he
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop m₀] with k hk
  exact hm₀ (ms k) (le_trans hk (hms k))

end MarkSets

section Dominated

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]

/-- **Dominated convergence for a mark integral over a shrinking family of cuts.** For integrands
dominated on a time window by a function integrable against the product of the window with the
intensity, the mark integrals over the complements of the family converge to the mark integral of
the pointwise limit over the whole mark space. -/
theorem tendsto_setIntegral_of_dominated
    {T : ℝ} {A : ℕ → Set E} {fs : ℕ → ℝ → E → ℝ} {f g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable (fun p : ℝ × E => fs m p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e, |fs m s e| ≤ g s e)
    (hconv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e, Tendsto (fun m => fs m s e) atTop (𝓝 (f s e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν)) := by
  classical
  have hwin : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      p.1 ∈ Set.Icc (0 : ℝ) T :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  have hevp : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ∀ᶠ m in atTop, p.2 ∉ A m :=
    Measure.quasiMeasurePreserving_snd.ae hev
  have hSm : ∀ m, MeasurableSet {p : ℝ × E | p.2 ∈ (A m)ᶜ} := fun m =>
    measurable_snd (hA m).compl
  set F : ℕ → ℝ × E → ℝ :=
    fun m => {p : ℝ × E | p.2 ∈ (A m)ᶜ}.indicator (fun q => fs m q.1 q.2) with hF
  have hFmeas : ∀ m, AEStronglyMeasurable (F m)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    fun m => (hmeas m).indicator (hSm m)
  have hbound : ∀ m, ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖F m p‖ ≤ g p.1 p.2 := by
    intro m
    filter_upwards [hwin] with p hp
    have hle : |fs m p.1 p.2| ≤ g p.1 p.2 := hdom m p.1 hp p.2
    by_cases hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ}
    · rw [hF]
      simp only [Set.indicator_of_mem hpS, Real.norm_eq_abs]
      exact hle
    · rw [hF]
      simp only [Set.indicator_of_notMem hpS, norm_zero]
      exact le_trans (abs_nonneg _) hle
  have hlim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      Tendsto (fun m => F m p) atTop (𝓝 (f p.1 p.2)) := by
    filter_upwards [hwin, hevp] with p hp hpe
    refine Tendsto.congr' ?_ (hconv p.1 hp p.2)
    filter_upwards [hpe] with m hm
    have hpS : p ∈ {q : ℝ × E | q.2 ∈ (A m)ᶜ} := hm
    rw [hF]
    simp only [Set.indicator_of_mem hpS]
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := (volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) (F := F)
    (f := fun p : ℝ × E => f p.1 p.2) (fun p : ℝ × E => g p.1 p.2)
    hFmeas hg hbound hlim
  have hLHS : ∀ m, ∫ p, F m p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ, fs m s e ∂ν := by
    intro m
    have hint : Integrable (F m) ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
      hg.mono' (hFmeas m) (hbound m)
    rw [integral_prod _ hint]
    refine integral_congr_ae (Eventually.of_forall fun s => ?_)
    show ∫ e, F m (s, e) ∂ν = ∫ e in (A m)ᶜ, fs m s e ∂ν
    have hfun : (fun e => F m (s, e)) = ((A m)ᶜ).indicator (fun e => fs m s e) := by
      funext e
      by_cases he : e ∈ (A m)ᶜ
      · rw [hF]
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem (show (s, e) ∈
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
      · rw [hF]
        simp only [Set.indicator_of_notMem he, Set.indicator_of_notMem (show (s, e) ∉
          {q : ℝ × E | q.2 ∈ (A m)ᶜ} from he)]
    rw [hfun, integral_indicator (hA m).compl]
  have hmlim : AEStronglyMeasurable (fun p : ℝ × E => f p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν) :=
    aestronglyMeasurable_of_tendsto_ae atTop hFmeas hlim
  have hblim : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν),
      ‖f p.1 p.2‖ ≤ g p.1 p.2 := by
    filter_upwards [MeasureTheory.ae_all_iff.mpr hbound, hlim] with p hb hl
    exact le_of_tendsto hl.norm (Eventually.of_forall hb)
  have hRHS : ∫ p, f p.1 p.2 ∂((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e, f s e ∂ν :=
    integral_prod _ (hg.mono' hmlim hblim)
  simp_rw [hLHS] at hDCT
  rwa [hRHS] at hDCT

end Dominated

section Continuity

variable {n : ℕ} {E : Type v} {u : ℝ → (Fin n → ℝ) → ℝ}
  {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- Each coordinate of the gradient of a `C²` function of time and state is continuous in the
state. -/
theorem continuous_gradient (hu : ContDiff ℝ 2 (Function.uncurry u)) (s : ℝ) (i : Fin n) :
    Continuous fun y : Fin n → ℝ => gradient u s y i := by
  have hus : ContDiff ℝ 2 fun y : Fin n → ℝ => u s y :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  exact (hus.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The compensator-drift integrand of a `C²` function of time and state is continuous in the
state at a mark at which the jump coefficient is. -/
theorem continuous_compensatorDriftIntegrand (hu : ContDiff ℝ 2 (Function.uncurry u))
    (s : ℝ) (e : E) (hγ : Continuous fun y : Fin n → ℝ => γ s y e) :
    Continuous fun y : Fin n → ℝ => compensatorDriftIntegrand u γ s y e := by
  have hus : Continuous fun y : Fin n → ℝ => u s y := by
    have heq : (fun y : Fin n → ℝ => u s y) = Function.uncurry u ∘ fun y => (s, y) := rfl
    rw [heq]
    exact hu.continuous.comp (continuous_const.prodMk continuous_id)
  refine ((hus.comp (continuous_id.add hγ)).sub hus).sub ?_
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hγ).mul (continuous_gradient hu s i)

/-- The compensator-drift integrand of a `C²` function of time and state transports convergence
of states at a mark at which the jump coefficient is continuous. -/
theorem tendsto_compensatorDriftIntegrand_of_tendsto (hu : ContDiff ℝ 2 (Function.uncurry u))
    (s : ℝ) (e : E) (hγ : Continuous fun y : Fin n → ℝ => γ s y e)
    {z : ℕ → Fin n → ℝ} {w : Fin n → ℝ} (h : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun m => compensatorDriftIntegrand u γ s (z m) e) atTop
      (𝓝 (compensatorDriftIntegrand u γ s w e)) :=
  ((continuous_compensatorDriftIntegrand hu s e hγ).tendsto w).comp h

end Continuity

section CompensatorDriftLimit

variable {n : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  {u : ℝ → (Fin n → ℝ) → ℝ} {γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)}

/-- **The compensator-drift limit.** Along a family of mark sets that almost every mark
eventually avoids, and for compensator-drift integrands along paths converging pointwise on a
time window and dominated there by a function integrable against the product of the window with
the intensity, the compensator-drift integrals over the complements of the family converge to the
compensator-drift integral over the whole mark space along the limit path. -/
theorem tendsto_setIntegral_compensatorDrift
    {T : ℝ} {A : ℕ → Set E} {xs : ℕ → ℝ → (Fin n → ℝ)} {x : ℝ → (Fin n → ℝ)} {g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun p : ℝ × E => compensatorDriftIntegrand u γ p.1 (xs m p.1) p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e,
      |compensatorDriftIntegrand u γ s (xs m s) e| ≤ g s e)
    (hconv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e,
      Tendsto (fun m => compensatorDriftIntegrand u γ s (xs m s) e) atTop
        (𝓝 (compensatorDriftIntegrand u γ s (x s) e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ,
        compensatorDriftIntegrand u γ s (xs m s) e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u γ s (x s) e ∂ν)) :=
  tendsto_setIntegral_of_dominated hA hev hmeas hg hdom hconv

/-- The first-order term `∑ᵢ γᵢ ∂ᵢu` of the compensator-drift integrand. -/
noncomputable def firstOrderIntegrand (u : ℝ → (Fin n → ℝ) → ℝ)
    (γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)) (s : ℝ) (x : Fin n → ℝ) (e : E) : ℝ :=
  ∑ i : Fin n, γ s x e i * gradient u s x i

/-- **The first-order limit.** Under the hypotheses of the compensator-drift limit for the
first-order integrand, and with each coordinate of the jump coefficient integrable against the
intensity on the complements of the family and, in the limit, on the whole mark space, the
first-order corrections converge to the first-order correction along the limit path. The
integrability of the jump coefficient itself is a genuine restriction: it fails for a jump
coefficient that is only square-integrable near the small marks. -/
theorem tendsto_setIntegral_firstOrder
    {T : ℝ} {A : ℕ → Set E} {xs : ℕ → ℝ → (Fin n → ℝ)} {x : ℝ → (Fin n → ℝ)} {g : ℝ → E → ℝ}
    (hA : ∀ m, MeasurableSet (A m))
    (hev : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m)
    (hγs : ∀ (m : ℕ), ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n,
      IntegrableOn (fun e => γ s (xs m s) e i) (A m)ᶜ ν)
    (hγ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ i : Fin n, Integrable (fun e => γ s (x s) e i) ν)
    (hmeas : ∀ m, AEStronglyMeasurable
      (fun p : ℝ × E => firstOrderIntegrand u γ p.1 (xs m p.1) p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hg : Integrable (fun p : ℝ × E => g p.1 p.2)
      ((volume.restrict (Set.Icc (0 : ℝ) T)).prod ν))
    (hdom : ∀ m, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e,
      |firstOrderIntegrand u γ s (xs m s) e| ≤ g s e)
    (hconv : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ e,
      Tendsto (fun m => firstOrderIntegrand u γ s (xs m s) e) atTop
        (𝓝 (firstOrderIntegrand u γ s (x s) e))) :
    Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
        gradient u s (xs m s) i * ∫ e in (A m)ᶜ, γ s (xs m s) e i ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
        gradient u s (x s) i * ∫ e, γ s (x s) e i ∂ν)) := by
  have hcore := tendsto_setIntegral_of_dominated (ν := ν) (T := T) (A := A)
    (fs := fun m s e => firstOrderIntegrand u γ s (xs m s) e)
    (f := fun s e => firstOrderIntegrand u γ s (x s) e) (g := g) hA hev hmeas hg hdom hconv
  have hLHS : ∀ m, (∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ,
        firstOrderIntegrand u γ s (xs m s) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (xs m s) i * ∫ e in (A m)ᶜ, γ s (xs m s) e i ∂ν := by
    intro m
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    show (∫ e in (A m)ᶜ, (∑ i : Fin n, γ s (xs m s) e i * gradient u s (xs m s) i) ∂ν) = _
    exact setIntegral_firstOrder_eq _ s (xs m s) (hγs m s hs)
  have hRHS : (∫ s in Set.Icc (0 : ℝ) T, ∫ e, firstOrderIntegrand u γ s (x s) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∑ i : Fin n,
          gradient u s (x s) i * ∫ e, γ s (x s) e i ∂ν := by
    refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    show (∫ e, (∑ i : Fin n, γ s (x s) e i * gradient u s (x s) i) ∂ν) = _
    have h := setIntegral_firstOrder_eq (u := u) (γ := γ) Set.univ s (x s)
      (fun i => integrableOn_univ.mpr (hγ s hs i))
    simpa only [setIntegral_univ] using h
  simp_rw [hLHS] at hcore
  rwa [hRHS] at hcore

end CompensatorDriftLimit

section MarkTruncation

variable {n d : ℕ} {E : Type v} [MeasurableSpace E] {ν : Measure E}
  {u : ℝ → (Fin n → ℝ) → ℝ}

/-- The coefficient bundle with the jump coefficient cut to a set of marks. -/
noncomputable def markTruncCoeffs (coeffs : JumpDiffusionCoeffs n d E) (S : Set E) :
    JumpDiffusionCoeffs n d E where
  μ := coeffs.μ
  σ := coeffs.σ
  γ := fun s y e => S.indicator (fun _ => coeffs.γ s y e) e

omit [MeasurableSpace E] in
@[simp] theorem markTruncCoeffs_mu (coeffs : JumpDiffusionCoeffs n d E) (S : Set E) :
    (markTruncCoeffs coeffs S).μ = coeffs.μ := rfl

omit [MeasurableSpace E] in
@[simp] theorem markTruncCoeffs_sigma (coeffs : JumpDiffusionCoeffs n d E) (S : Set E) :
    (markTruncCoeffs coeffs S).σ = coeffs.σ := rfl

omit [MeasurableSpace E] in
/-- The drift integrand reads only the drift and the diffusion matrix, so cutting the jump
coefficient to a set of marks leaves it unchanged. -/
theorem driftIntegrand_markTruncCoeffs (coeffs : JumpDiffusionCoeffs n d E) (S : Set E)
    (s : ℝ) (y : Fin n → ℝ) :
    driftIntegrand u (markTruncCoeffs coeffs S) s y = driftIntegrand u coeffs s y := rfl

omit [MeasurableSpace E] in
/-- Cutting the jump coefficient to a set of marks cuts the compensator-drift integrand to the
same set. -/
theorem compensatorDriftIntegrand_markTruncCoeffs (coeffs : JumpDiffusionCoeffs n d E)
    (S : Set E) (s : ℝ) (y : Fin n → ℝ) (e : E) :
    compensatorDriftIntegrand u (markTruncCoeffs coeffs S).γ s y e
      = S.indicator (fun _ => compensatorDriftIntegrand u coeffs.γ s y e) e := by
  by_cases he : e ∈ S
  · simp [compensatorDriftIntegrand, markTruncCoeffs, he]
  · simp [compensatorDriftIntegrand, markTruncCoeffs, he]

/-- The compensator-drift integral of a cut jump coefficient over the whole mark space is the
compensator-drift integral of the uncut one over the cut. -/
theorem integral_compensatorDriftIntegrand_markTruncCoeffs
    (coeffs : JumpDiffusionCoeffs n d E) {S : Set E} (hS : MeasurableSet S)
    (s : ℝ) (y : Fin n → ℝ) :
    (∫ e, compensatorDriftIntegrand u (markTruncCoeffs coeffs S).γ s y e ∂ν)
      = ∫ e in S, compensatorDriftIntegrand u coeffs.γ s y e ∂ν := by
  simp_rw [compensatorDriftIntegrand_markTruncCoeffs]
  exact integral_indicator hS

/-- **The Itô–Lévy identity for cut coefficients, read in the vocabulary of the uncut ones.** The
drift integral is unchanged and the compensator-drift integral is taken over the cut. -/
theorem itoLevy_sub_of_markTruncCoeffs (coeffs : JumpDiffusionCoeffs n d E) {S : Set E}
    (hS : MeasurableSet S) {xp : ℝ → (Fin n → ℝ)} {T Dm Cm : ℝ}
    (h : u T (xp T) - u 0 (xp 0)
      = (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u (markTruncCoeffs coeffs S) s (xp s))
        + Dm + Cm
        + ∫ s in Set.Icc (0 : ℝ) T,
            ∫ e, compensatorDriftIntegrand u (markTruncCoeffs coeffs S).γ s (xp s) e ∂ν) :
    u T (xp T) - u 0 (xp 0)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (xp s)) - Dm
      = Cm + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in S,
          compensatorDriftIntegrand u coeffs.γ s (xp s) e ∂ν := by
  have hc : (∫ s in Set.Icc (0 : ℝ) T,
        ∫ e, compensatorDriftIntegrand u (markTruncCoeffs coeffs S).γ s (xp s) e ∂ν)
      = ∫ s in Set.Icc (0 : ℝ) T, ∫ e in S,
          compensatorDriftIntegrand u coeffs.γ s (xp s) e ∂ν :=
    setIntegral_congr_fun measurableSet_Icc fun s _ =>
      integral_compensatorDriftIntegrand_markTruncCoeffs coeffs hS s (xp s)
  simp only [driftIntegrand_markTruncCoeffs, hc] at h
  linarith

end MarkTruncation

section Assembly

/-- **The five-term limit identity.** If the two sides of the Itô–Lévy identity agree along a
sequence and each of the five terms converges, the limits satisfy the same identity. -/
theorem itoLevy_of_tendsto {Lhs Drift Bro Cmp CDrift : ℕ → ℝ} {L D B C CD : ℝ}
    (hm : ∀ m, Lhs m - Drift m - Bro m = Cmp m + CDrift m)
    (hL : Tendsto Lhs atTop (𝓝 L)) (hD : Tendsto Drift atTop (𝓝 D))
    (hB : Tendsto Bro atTop (𝓝 B)) (hC : Tendsto Cmp atTop (𝓝 C))
    (hCD : Tendsto CDrift atTop (𝓝 CD)) :
    L - D - B = C + CD :=
  tendsto_nhds_unique ((hL.sub hD).sub hB)
    (Tendsto.congr (fun m => (hm m).symm) (hC.add hCD))

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- **The five-term limit identity at almost every sample point.** -/
theorem ae_itoLevy_of_ae_tendsto {Lhs Drift Bro Cmp CDrift : ℕ → Ω → ℝ} {L D B C CD : Ω → ℝ}
    (hm : ∀ m, ∀ᵐ ω ∂P, Lhs m ω - Drift m ω - Bro m ω = Cmp m ω + CDrift m ω)
    (hL : ∀ᵐ ω ∂P, Tendsto (fun m => Lhs m ω) atTop (𝓝 (L ω)))
    (hD : ∀ᵐ ω ∂P, Tendsto (fun m => Drift m ω) atTop (𝓝 (D ω)))
    (hB : ∀ᵐ ω ∂P, Tendsto (fun m => Bro m ω) atTop (𝓝 (B ω)))
    (hC : ∀ᵐ ω ∂P, Tendsto (fun m => Cmp m ω) atTop (𝓝 (C ω)))
    (hCD : ∀ᵐ ω ∂P, Tendsto (fun m => CDrift m ω) atTop (𝓝 (CD ω))) :
    ∀ᵐ ω ∂P, L ω - D ω - B ω = C ω + CD ω := by
  filter_upwards [MeasureTheory.ae_all_iff.mpr hm, hL, hD, hB, hC, hCD]
    with ω h1 h2 h3 h4 h5 h6
  exact itoLevy_of_tendsto h1 h2 h3 h4 h5 h6

/-- **The Itô–Lévy identity along the limit path, from convergent terms.** From the identity
along each truncated path, with the drift and compensator-drift terms given as arbitrary
sequences, and the convergence of the increment of the state function, of the drift term to the
drift integral along the limit path, of the diffusion and compensated jump terms, and of the
compensator-drift term to the compensator-drift integral along the limit path over the whole mark
space, the identity holds along the limit path. -/
theorem ae_itoLevy_of_ae_tendsto_terms {E : Type v} [MeasurableSpace E] {ν : Measure E}
    {n d : ℕ} (coeffs : JumpDiffusionCoeffs n d E) (u : ℝ → (Fin n → ℝ) → ℝ) (T : ℝ)
    (xs : ℕ → ℝ → Ω → (Fin n → ℝ)) (x : ℝ → Ω → (Fin n → ℝ))
    (Dr : ℕ → Ω → ℝ) (Bro : ℕ → Ω → ℝ) (B : Ω → ℝ) (Cmp : ℕ → Ω → ℝ) (C : Ω → ℝ)
    (Cd : ℕ → Ω → ℝ)
    (hstep : ∀ m, ∀ᵐ ω ∂P,
      u T (xs m T ω) - u 0 (xs m 0 ω) - Dr m ω - Bro m ω = Cmp m ω + Cd m ω)
    (hend : ∀ᵐ ω ∂P, Tendsto (fun m => u T (xs m T ω) - u 0 (xs m 0 ω)) atTop
      (𝓝 (u T (x T ω) - u 0 (x 0 ω))))
    (hdrift : ∀ᵐ ω ∂P, Tendsto (fun m => Dr m ω) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s ω))))
    (hbro : ∀ᵐ ω ∂P, Tendsto (fun m => Bro m ω) atTop (𝓝 (B ω)))
    (hcmp : ∀ᵐ ω ∂P, Tendsto (fun m => Cmp m ω) atTop (𝓝 (C ω)))
    (hcdrift : ∀ᵐ ω ∂P, Tendsto (fun m => Cd m ω) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (x s ω) e ∂ν))) :
    ∀ᵐ ω ∂P,
      u T (x T ω) - u 0 (x 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s ω)) - B ω
        = C ω + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (x s ω) e ∂ν :=
  ae_itoLevy_of_ae_tendsto hstep hend hdrift hbro hcmp hcdrift

/-- **The Itô–Lévy identity along the limit path.** From the identity along each truncated path,
with the compensator-drift integral taken over the complement of the truncated mark set, and the
convergence of the increment of the state function, of the drift integral, of the diffusion and
compensated jump terms and of the compensator-drift integral, the identity holds along the limit
path with the compensator-drift integral taken over the whole mark space. -/
theorem ae_itoLevy_of_ae_tendsto_integrals {E : Type v} [MeasurableSpace E] {ν : Measure E}
    {n d : ℕ} (coeffs : JumpDiffusionCoeffs n d E) (u : ℝ → (Fin n → ℝ) → ℝ) (T : ℝ)
    (A : ℕ → Set E) (xs : ℕ → ℝ → Ω → (Fin n → ℝ)) (x : ℝ → Ω → (Fin n → ℝ))
    (Bro : ℕ → Ω → ℝ) (B : Ω → ℝ) (Cmp : ℕ → Ω → ℝ) (C : Ω → ℝ)
    (hstep : ∀ m, ∀ᵐ ω ∂P,
      u T (xs m T ω) - u 0 (xs m 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (xs m s ω)) - Bro m ω
        = Cmp m ω + ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ,
            compensatorDriftIntegrand u coeffs.γ s (xs m s ω) e ∂ν)
    (hend : ∀ᵐ ω ∂P, Tendsto (fun m => u T (xs m T ω) - u 0 (xs m 0 ω)) atTop
      (𝓝 (u T (x T ω) - u 0 (x 0 ω))))
    (hdrift : ∀ᵐ ω ∂P, Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T,
        driftIntegrand u coeffs s (xs m s ω)) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s ω))))
    (hbro : ∀ᵐ ω ∂P, Tendsto (fun m => Bro m ω) atTop (𝓝 (B ω)))
    (hcmp : ∀ᵐ ω ∂P, Tendsto (fun m => Cmp m ω) atTop (𝓝 (C ω)))
    (hcdrift : ∀ᵐ ω ∂P, Tendsto (fun m => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ,
        compensatorDriftIntegrand u coeffs.γ s (xs m s ω) e ∂ν) atTop
      (𝓝 (∫ s in Set.Icc (0 : ℝ) T, ∫ e,
        compensatorDriftIntegrand u coeffs.γ s (x s ω) e ∂ν))) :
    ∀ᵐ ω ∂P,
      u T (x T ω) - u 0 (x 0 ω)
          - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (x s ω)) - B ω
        = C ω + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (x s ω) e ∂ν :=
  ae_itoLevy_of_ae_tendsto_terms coeffs u T xs x
    (fun m ω => ∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (xs m s ω)) Bro B Cmp C
    (fun m ω => ∫ s in Set.Icc (0 : ℝ) T, ∫ e in (A m)ᶜ,
      compensatorDriftIntegrand u coeffs.γ s (xs m s ω) e ∂ν)
    hstep hend hdrift hbro hcmp hcdrift

end Assembly

end LevyStochCalc.Ito.JumpFormula
