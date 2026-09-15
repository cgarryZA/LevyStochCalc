/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.MultidimIto
import LevyStochCalc.Ito.PicardOutput
import LevyStochCalc.Martingale.CadlagModification

/-!
# An everywhere-càdlàg version of the multidimensional Brownian integral

The multidimensional `L²` Itô integral `∫_0^t Z_s · dW_s = ∑_i ∫_0^t Z_s^i dW_s^i` is defined
separately at each time, so it carries no path regularity. Each coordinate integral has an
adapted modification with almost surely càdlàg paths; when the null set on which the paths fail
to be càdlàg belongs to `ℱ 0` and the filtration is constant before time `0`, that modification
can be replaced by `0` there, which makes every path càdlàg. Summing the `d` coordinate
modifications gives a version of the vector integral that is adapted to the right-continuous
filtration, jointly measurable, càdlàg at every sample point and a martingale.

## Main statements

* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.martingale_finsetSum` — a finite sum
  of martingales is a martingale.
* `LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.exists_everywhere_cadlag_vectorIntegral`
  — the multidimensional Brownian integral has an everywhere-càdlàg martingale version.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §3.2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim
namespace MultidimBrownianMotion

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {d : ℕ}

omit [IsProbabilityMeasure P] in
/-- A finite sum of martingales is a martingale. -/
theorem martingale_finsetSum {ι : Type v} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (s : Finset ι) (F : ι → ℝ → Ω → ℝ) (hF : ∀ i ∈ s, Martingale (F i) ℱ P) :
    Martingale (fun t ω => ∑ i ∈ s, F i t ω) ℱ P := by
  have hsum : Martingale (∑ i ∈ s, F i) ℱ P :=
    Finset.sum_induction F (fun G => Martingale G ℱ P) (fun _ _ ha hb => ha.add hb)
      (martingale_zero ℝ ℱ P) hF
  have heq : (∑ i ∈ s, F i) = fun t ω => ∑ i ∈ s, F i t ω := by
    funext t ω
    simp
  rwa [heq] at hsum

/-- **An everywhere-càdlàg martingale version of the multidimensional Brownian integral.**
Under the usual conditions on `ℱ` — the null sets lie in `ℱ 0` and the filtration is constant
before time `0` — the integral `∫_0^t Z_s · dW_s` has a version, adapted to `ℱ.rightCont`, that
is jointly measurable in the time and the sample point, right-continuous with left limits along
every path, and a martingale for `ℱ.rightCont`. -/
theorem exists_everywhere_cadlag_vectorIntegral
    (W : MultidimBrownianMotion P d)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ i : Fin d, IsBrownianFiltration (W.W i) ℱ)
    (Z : ℝ → Ω → (Fin d → ℝ))
    (hm : ∀ i : Fin d, Measurable (Function.uncurry (fun ω s => Z s ω i)))
    (hp : ∀ i : Fin d, Probability.ProgressivelyMeasurable ℱ (fun ω s => Z s ω i))
    (hq : ∀ i : Fin d, ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ.rightCont 0 ≤ ℱ.rightCont t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s) :
    ∃ M : ℝ → Ω → ℝ, Adapted ℱ.rightCont M ∧ Measurable (Function.uncurry M) ∧
      (∀ t : ℝ, M t =ᵐ[P] fun ω =>
        MultidimBrownianMotion.stochasticIntegral W ℱ hℱW Z hm hp hq t ω) ∧
      (∀ (ω : Ω) (t : ℝ),
        Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω)) ∧
          ∃ L : ℝ, Tendsto (fun s => M s ω) (𝓝[<] t) (𝓝 L)) ∧
      Martingale M ℱ.rightCont P := by
  classical
  -- a càdlàg-modulo-null adapted modification of each coordinate integral
  choose Y hYadapt hYae hYcad using fun i : Fin d =>
    LevyStochCalc.Ito.Picard.exists_cadlag_modification_itoIntegral (W.W i) ℱ (hℱW i)
      (fun ω s => Z s ω i) (hm i) (hp i) (hq i)
  -- the exceptional null set is `ℱ 0`-measurable, so it can be zeroed out
  choose M hMadapt hMae hMright hMleft using fun i : Fin d =>
    LevyStochCalc.Probability.exists_everywhere_cadlag_modification
      (P := P) (ℱ := ℱ.rightCont) hℱ0
      (fun s hs h0 => (ℱ.le_rightCont 0) _ (hnull s hs h0)) (hYadapt i) (hYcad i)
  have hMae' : ∀ (i : Fin d) (t : ℝ), M i t =ᵐ[P]
      LevyStochCalc.Brownian.Ito.stochasticIntegral (W.W i) ℱ (hℱW i)
        (fun ω s => Z s ω i) (hm i) (hp i) (hq i) t :=
    fun i t => (hMae i t).trans (hYae i t)
  refine ⟨fun t ω => ∑ i : Fin d, M i t ω, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun t => Finset.measurable_sum _ fun i _ => hMadapt i t
  · refine LevyStochCalc.Probability.measurable_uncurry_of_rightContinuous
      (fun t => Finset.measurable_sum _ fun i _ => hMadapt i t) fun ω t => ?_
    exact tendsto_finsetSum _ fun i _ => hMright i ω t
  · intro t
    filter_upwards [MeasureTheory.ae_all_iff.mpr fun i : Fin d => hMae' i t] with ω hω
    exact Finset.sum_congr rfl fun i _ => hω i
  · refine fun ω t => ⟨tendsto_finsetSum _ fun i _ => hMright i ω t, ?_⟩
    choose L hL using fun i : Fin d => hMleft i ω t
    exact ⟨∑ i : Fin d, L i, tendsto_finsetSum _ fun i _ => hL i⟩
  · refine martingale_finsetSum Finset.univ M fun i _ => ?_
    exact LevyStochCalc.Martingale.martingale_of_ae_eq
      (LevyStochCalc.Brownian.Ito.martingale_rightCont_stochasticIntegralBrownian (W.W i) ℱ
        (hℱW i) (fun ω s => Z s ω i) (hm i) (hp i) (hq i))
      (Adapted.stronglyAdapted (hMadapt i)) (hMae' i)

end MultidimBrownianMotion
end LevyStochCalc.Brownian.Multidim
