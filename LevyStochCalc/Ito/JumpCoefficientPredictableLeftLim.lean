/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpCoefficientPredictableCriteria
import LevyStochCalc.Ito.JumpSplittingLeftLim

/-!
# The jump coefficient read at the left limits of the path

The left limits of a path are the limit along a dyadic grid of the path itself, so for a path
having left limits at the positive times they are known at the current time whenever the path is
adapted and they are left-continuous there; cut to the positive times they are predictable, hence
the jump coefficient of a jump diffusion evaluated at them is predictable on the time–mark space.

## References

* Protter, *Stochastic Integration and Differential Equations*, 2005, §III.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpSplitting

open LevyStochCalc.Probability

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The left limits of the path of a jump diffusion, cut to the positive times. -/
noncomputable def leftLimPathPos (X : Setting.JumpDiffusion W N coeffs x₀) (s : ℝ) (ω : Ω) :
    Fin n → ℝ := if 0 < s then leftLimPath X s ω else 0

/-- The left limits at a time of an adapted path having left limits there are known at that
time. -/
theorem measurable_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t)) {t : ℝ}
    (hleft : ∀ (ω : Ω) (i : Fin n), ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L)) :
    Measurable[ℱ t] (leftLimPath X t) := by
  refine (@measurable_pi_iff Ω (Fin n) (fun _ => ℝ) (ℱ t) inferInstance
    (leftLimPath X t)).mpr fun i => ?_
  have hrw : (fun ω => leftLimPath X t ω i)
      = fun ω => limsup (fun k : ℕ => X.X (leftGridPoint k t) ω i) atTop := by
    funext ω
    exact (((tendsto_nhdsLT_leftLimPath (fun j => hleft ω j) i).comp
      (tendsto_leftGridPoint t)).limsup_eq).symm
  rw [hrw]
  refine Measurable.limsup fun k => ?_
  have hm : Measurable[ℱ (leftGridPoint k t)] fun ω => X.X (leftGridPoint k t) ω i :=
    (measurable_pi_apply i).comp (hXadapt (leftGridPoint k t))
  exact hm.mono (ℱ.mono (leftGridPoint_lt k t).le) le_rfl

/-- **The left limits of a path having left limits at the positive times are left-continuous
there.** -/
theorem tendsto_nhdsLT_leftLimPath_self (X : Setting.JumpDiffusion W N coeffs x₀) {ω : Ω}
    (hleft : ∀ t : ℝ, 0 < t → ∀ i : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun u => leftLimPath X u ω) (𝓝[<] t) (𝓝 (leftLimPath X t ω)) := by
  refine tendsto_pi_nhds.mpr fun i => ?_
  refine Metric.tendsto_nhdsWithin_nhds.mpr fun ε hε => ?_
  obtain ⟨δ, hδ, hδ'⟩ := Metric.tendsto_nhdsWithin_nhds.mp
    (tendsto_nhdsLT_leftLimPath (hleft t ht) i) (ε / 2) (by linarith)
  refine ⟨min δ t, lt_min hδ ht, fun {u} hu hdu => ?_⟩
  have hut : u < t := hu
  have hdist : dist u t = t - u := by
    rw [Real.dist_eq, abs_of_nonpos (by linarith : u - t ≤ 0)]
    ring
  rw [hdist] at hdu
  have hupos : 0 < u := by
    have h := lt_of_lt_of_le hdu (min_le_right δ t)
    linarith
  have hδu : t - δ < u := by
    have h := lt_of_lt_of_le hdu (min_le_left δ t)
    linarith
  have hconv : Tendsto (fun s => X.X s ω i) (𝓝[<] u) (𝓝 (leftLimPath X u ω i)) :=
    tendsto_nhdsLT_leftLimPath (hleft u hupos) i
  have hev : ∀ᶠ x in 𝓝[<] u, dist (X.X x ω i) (leftLimPath X t ω i) ≤ ε / 2 := by
    filter_upwards [Ioo_mem_nhdsLT hδu] with x hx
    have hxt : x < t := lt_trans hx.2 hut
    have hdx : dist x t < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith : x - t ≤ 0)]
      linarith [hx.1]
    exact (hδ' (Set.mem_Iio.mpr hxt) hdx).le
  have hle : dist (leftLimPath X u ω i) (leftLimPath X t ω i) ≤ ε / 2 :=
    le_of_tendsto (hconv.dist tendsto_const_nhds) hev
  linarith

/-- **The left limits of an adapted path having left limits at the positive times, cut to those
times, are predictable.** -/
theorem measurable_predictableSigma_leftLimPathPos (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ i : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω i) (𝓝[<] t) (𝓝 L)) :
    Measurable[predictableSigma ℱ] fun p : ℝ × Ω => leftLimPathPos X p.1 p.2 := by
  classical
  refine (@measurable_pi_iff (ℝ × Ω) (Fin n) (fun _ => ℝ) (predictableSigma ℱ) inferInstance
    (fun p : ℝ × Ω => leftLimPathPos X p.1 p.2)).mpr fun i => ?_
  refine measurable_predictableSigma_of_tendsto_leftGridPoint
    (Z := fun t ω => if 0 < t then X.X t ω i else 0)
    (Y := fun t ω => leftLimPathPos X t ω i) (fun t => ?_) (fun s ω => ?_)
  · by_cases h : (0 : ℝ) < t
    · have hm : Measurable[ℱ t] fun ω => X.X t ω i := (measurable_pi_apply i).comp (hXadapt t)
      simpa [h] using hm
    · simp only [if_neg h]
      exact measurable_const
  · by_cases hs : (0 : ℝ) < s
    · have hnhds : Tendsto (fun k : ℕ => leftGridPoint k s) atTop (𝓝 s) :=
        (tendsto_leftGridPoint s).mono_right nhdsWithin_le_nhds
      have hev : ∀ᶠ k : ℕ in atTop, 0 < leftGridPoint k s := hnhds.eventually (lt_mem_nhds hs)
      have hconv : Tendsto (fun k : ℕ => X.X (leftGridPoint k s) ω i) atTop
          (𝓝 (leftLimPath X s ω i)) :=
        (tendsto_nhdsLT_leftLimPath (hleft ω s hs) i).comp (tendsto_leftGridPoint s)
      have hcong : (fun k : ℕ => X.X (leftGridPoint k s) ω i)
          =ᶠ[atTop] fun k : ℕ =>
            if 0 < leftGridPoint k s then X.X (leftGridPoint k s) ω i else 0 := by
        filter_upwards [hev] with k hk
        rw [if_pos hk]
      simpa [leftLimPathPos, hs] using hconv.congr' hcong
    · have h0 : ∀ k : ℕ, ¬(0 < leftGridPoint k s) := fun k hk =>
        hs (lt_trans hk (leftGridPoint_lt k s))
      have hzero : (fun k : ℕ =>
          if 0 < leftGridPoint k s then X.X (leftGridPoint k s) ω i else 0)
          = fun _ : ℕ => (0 : ℝ) := by
        funext k
        exact if_neg (h0 k)
      rw [hzero]
      simp [leftLimPathPos, hs]

/-- **The jump coefficient of a jump diffusion, evaluated at the left limits of the path, is
predictable on the time–mark space.** -/
theorem markedPredictable_jumpCoeff_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (i : Fin n)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hγ : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2 i)
    (hγ0 : ∀ s : ℝ, s ≤ 0 → ∀ (x : Fin n → ℝ) (e : E), coeffs.γ s x e i = 0) :
    MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (leftLimPath X s ω) e i := by
  classical
  have h := markedPredictable_ite_of_predictable (ν := ν)
    (measurable_predictableSigma_leftLimPathPos X ℱ hXadapt hleft)
    (f := fun s x e => coeffs.γ s x e i) hγ
  have hrw : (fun (ω : Ω) (s : ℝ) (e : E) =>
      if 0 < s then coeffs.γ s (leftLimPathPos X s ω) e i else 0)
      = fun (ω : Ω) (s : ℝ) (e : E) => coeffs.γ s (leftLimPath X s ω) e i := by
    funext ω s e
    by_cases hs : 0 < s
    · simp only [if_pos hs, leftLimPathPos]
    · rw [if_neg hs, hγ0 s (not_lt.mp hs)]
  rwa [hrw] at h

/-- **The jump coefficients of a regular jump-diffusion coefficient bundle, evaluated at the left
limits of the path, are predictable on the time–mark space.** -/
theorem markedPredictable_forall_jumpCoeff_leftLimPath (X : Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    (hleft : ∀ (ω : Ω) (t : ℝ), 0 < t → ∀ j : Fin n,
      ∃ L : ℝ, Tendsto (fun s => X.X s ω j) (𝓝[<] t) (𝓝 L))
    (hreg : coeffs.IsRegular ν)
    (hγ0 : ∀ s : ℝ, s ≤ 0 → ∀ (x : Fin n → ℝ) (e : E), coeffs.γ s x e = 0) :
    ∀ i : Fin n, MarkedPredictable ℱ ν fun ω s e => coeffs.γ s (leftLimPath X s ω) e i :=
  fun i => markedPredictable_jumpCoeff_leftLimPath X ℱ i hXadapt hleft
    ((measurable_pi_apply i).comp hreg.2.2.1)
    (fun s hs x e => by rw [hγ0 s hs x e]; rfl)

end LevyStochCalc.Ito.JumpSplitting
