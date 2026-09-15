/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardStep
import LevyStochCalc.BSDEJ.IntegralLocality

/-!
# The Itô–Lévy decomposition of a Picard output

The output `Y` of a Picard step satisfies the backward equation on the horizon `[0, T]` only.
Frozen at the horizon, `t ↦ Y (min t T)`, it carries an Itô–Lévy decomposition at every
nonnegative time, with drift `-b` for a drift `b` that is almost everywhere the generator along
the input triple, diffusion vector `Z` and jump integrand `U`: subtracting the backward equation
at `t` from the backward equation at `0` turns the remaining window `[t, T]` of the drift
integral into the initial window `[0, t]`, and past the horizon neither the drift integral nor
either stochastic leg moves.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.clampT` — a process frozen at the horizon.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.clampT_decomposition_of_eqn` — the decomposition of a frozen path
  satisfying the backward equation, for abstract stochastic legs.
* `LevyStochCalc.BSDEJ.Solves.PicardOutput.isItoLevyProcess_clampT` — the frozen Picard output
  is an Itô–Lévy process.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Freezing a process at the horizon -/

/-- The process `Y` frozen at the horizon `T`, that is `t ↦ Y (min t T)`. -/
def clampT (T : ℝ) (Y : ℝ → Ω → ℝ) : ℝ → Ω → ℝ := fun t ω => Y (min t T) ω

omit [MeasurableSpace Ω] in
/-- The value of a frozen process is the value of the process at the clamped time. -/
theorem clampT_apply (T : ℝ) (Y : ℝ → Ω → ℝ) (t : ℝ) (ω : Ω) :
    clampT T Y t ω = Y (min t T) ω := rfl

omit [MeasurableSpace Ω] in
/-- Before the horizon the frozen process is the process. -/
theorem clampT_apply_of_le {T t : ℝ} (ht : t ≤ T) (Y : ℝ → Ω → ℝ) : clampT T Y t = Y t := by
  funext ω
  rw [clampT_apply, min_eq_left ht]

omit [MeasurableSpace Ω] in
/-- After the horizon the frozen process is the process at the horizon. -/
theorem clampT_apply_of_ge {T t : ℝ} (ht : T ≤ t) (Y : ℝ → Ω → ℝ) : clampT T Y t = Y T := by
  funext ω
  rw [clampT_apply, min_eq_right ht]

/-- The frozen process is jointly measurable. -/
theorem measurable_uncurry_clampT {T : ℝ} {Y : ℝ → Ω → ℝ}
    (hY : Measurable (Function.uncurry Y)) : Measurable (Function.uncurry (clampT T Y)) := by
  have hcomp : Function.uncurry (clampT T Y)
      = Function.uncurry Y ∘ fun p : ℝ × Ω => (min p.1 T, p.2) := rfl
  rw [hcomp]
  exact hY.comp ((measurable_fst.min measurable_const).prodMk measurable_snd)

/-! ### The drift integral past the horizon -/

/-- The integral over `[0, t]` of a function vanishing off `[0, T]` is its integral over
`[0, T]`, at every time past the horizon. -/
theorem setIntegral_Icc_eq_of_vanishing {g : ℝ → ℝ} {T t : ℝ} (hTt : T ≤ t)
    (hg : ∀ s, s ∉ Set.Icc (0 : ℝ) T → g s = 0) :
    ∫ s in Set.Icc (0 : ℝ) t, g s = ∫ s in Set.Icc (0 : ℝ) T, g s := by
  have hind : (Set.Icc (0 : ℝ) t).indicator g = (Set.Icc (0 : ℝ) T).indicator g := by
    funext s
    by_cases hsT : s ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem (Set.Icc_subset_Icc le_rfl hTt hsT) g,
        Set.indicator_of_mem hsT g]
    · rw [Set.indicator_of_notMem hsT g]
      by_cases hst : s ∈ Set.Icc (0 : ℝ) t
      · rw [Set.indicator_of_mem hst g]
        exact hg s hsT
      · rw [Set.indicator_of_notMem hst g]
  rw [← integral_indicator measurableSet_Icc, ← integral_indicator measurableSet_Icc, hind]

/-! ### The decomposition of a frozen backward path -/

omit [IsProbabilityMeasure P] in
/-- A path satisfying the backward equation on `[0, T]` with drift `b` and stochastic legs
`M^W`, `M^N` vanishing at `0` and constant past `T` has, frozen at the horizon, the
decomposition `Y_{t ∧ T} = Y_0 - ∫_0^t b_s ds + M^W_t + M^N_t` at every nonnegative time. -/
theorem clampT_decomposition_of_eqn {T : ℝ} (hT : 0 < T) {Y : ℝ → Ω → ℝ} {ξ : Ω → ℝ}
    {b : Ω → ℝ → ℝ} {MW MN : ℝ → Ω → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (heqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, Y t ω = ξ ω + (∫ s in Set.Icc t T, b ω s)
      - (MW T ω - MW t ω) - (MN T ω - MN t ω))
    (hW0 : MW 0 =ᵐ[P] 0) (hN0 : MN 0 =ᵐ[P] 0)
    (hWT : ∀ t : ℝ, T ≤ t → MW t =ᵐ[P] MW T)
    (hNT : ∀ t : ℝ, T ≤ t → MN t =ᵐ[P] MN T) :
    ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, clampT T Y t ω
      = Y 0 ω + (∫ s in Set.Icc (0 : ℝ) t, -b ω s) + MW t ω + MN t ω := by
  have hkey : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      Y t ω = Y 0 ω + (∫ s in Set.Icc (0 : ℝ) t, -b ω s) + MW t ω + MN t ω := by
    intro t ht
    filter_upwards [heqn t ht, heqn 0 ⟨le_rfl, hT.le⟩, hW0, hN0, driftLeg_ae_eq hbm hbq T,
      driftLeg_ae_eq hbm hbq t, driftLeg_sub_ae hbm hbq ht.1 ht.2] with ω h1 h2 h3 h4 h5 h6 h7
    rw [integral_neg]
    simp only [Pi.zero_apply] at h3 h4
    linarith
  intro t ht
  rcases le_or_gt t T with htT | htT
  · filter_upwards [hkey t ⟨ht, htT⟩] with ω k
    rw [clampT_apply_of_le htT Y]
    exact k
  · have hTt : T ≤ t := htT.le
    have hcut : ∀ ω : Ω, ∫ s in Set.Icc (0 : ℝ) t, -b ω s
        = ∫ s in Set.Icc (0 : ℝ) T, -b ω s := fun ω =>
      setIntegral_Icc_eq_of_vanishing hTt fun s hs => by rw [hbz ω s hs, neg_zero]
    filter_upwards [hkey T ⟨hT.le, le_rfl⟩, hWT t hTt, hNT t hTt] with ω k1 k2 k3
    rw [clampT_apply_of_ge hTt Y, hcut ω, k2, k3]
    exact k1

/-! ### The frozen Picard output -/


/-- The Picard output frozen at the horizon is an Itô–Lévy process with drift `-b`, diffusion
vector `Z` and jump integrand `U`. -/
theorem PicardOutput.isItoLevyProcess_clampT
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y' : ℝ → Ω → ℝ}
    {Z' : ℝ → Ω → (Fin d → ℝ)} {U' : ℝ → Ω → E → ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : PicardOutput D f ξ T Y' Z' U' Y Z U) (hT : 0 < T)
    {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hb : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b p.1 p.2 = f p.2 (Y' p.2 p.1) (Z' p.2 p.1) (U' p.2 p.1)) :
    LevyStochCalc.Ito.Setting.IsItoLevyProcess D.W D.N (augJoint D)
      D.isBrownianFiltration_aug D.isPoissonFiltration_aug (clampT T Y) (Y 0)
      (fun s ω => -b ω s) Z (fun ω s e => U s ω e) where
  measurable_path := measurable_uncurry_clampT h.Y_meas
  σ_meas := h.Z_meas
  σ_prog := h.Z_prog
  σ_sq := sq_int_global_of_vanishing h.Z_vanish h.Z_sq
  γ_meas := h.U_meas
  γ_prog := h.U_prog
  γ_sq := marked_sq_int_global_of_vanishing h.U_vanish h.U_sq
  decomposition := by
    refine clampT_decomposition_of_eqn (ξ := ξ) hT hbm hbq hbz ?_ ?_ ?_ ?_ ?_
    · intro t ht
      have hbf : ∀ᵐ ω ∂P, ∫ s in Set.Icc t T, b ω s
          = ∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω) := by
        filter_upwards [Measure.ae_ae_of_ae_prod hb] with ω hω
        exact integral_congr_ae
          (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl) hω)
      filter_upwards [h.eqn t ht, hbf] with ω h1 h2
      rw [h2]
      exact h1
    · exact Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W
        (augJoint D) D.isBrownianFiltration_aug Z h.Z_meas h.Z_prog
        (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) le_rfl
    · exact Poisson.Compensated.stochasticIntegral_ae_zero_of_nonpos
        (φ := fun ω s e => U s ω e) D.N D.isPoissonFiltration_aug h.U_meas h.U_prog
        (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) le_rfl
    · exact fun t hTt =>
        Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_eq_of_vanish D.W
          (augJoint D) D.isBrownianFiltration_aug h.Z_meas h.Z_prog
          (sq_int_global_of_vanishing h.Z_vanish h.Z_sq) hT hTt h.Z_vanish
    · exact fun t hTt =>
        Poisson.Compensated.stochasticIntegral_ae_eq_of_vanish (φ := fun ω s e => U s ω e) D.N
          D.isPoissonFiltration_aug h.U_meas h.U_prog
          (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq) hT hTt h.U_vanish

end LevyStochCalc.BSDEJ.Solves
