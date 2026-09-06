/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2
import LevyStochCalc.Probability.AEMeasurableInf
import LevyStochCalc.Probability.ProjectionLimit

/-!
# `L²` conditional expectations along a decreasing sequence of σ-algebras

For an antitone sequence of sub-σ-algebras the subspaces `lpMeas (m n)` of `L²` are antitone with
intersection `lpMeas (⨅ n, m n)` (`lpMeas_iInf_of_antitone`, over the `limsup` construction of
`AEMeasurableInf.lean`), and `condExpL2` is the orthogonal projection onto them. Projections along
an antitone chain of closed subspaces converge to the projection onto the intersection
(`ProjectionLimit.lean`), so

  `𝔼[f | m n] → 𝔼[f | ⨅ n, m n]` in `L²`.

This is the downward counterpart of Mathlib's `Integrable.tendsto_eLpNorm_condExp`, which goes
upward along an increasing filtration. Applied at `m n := ℱ (t + 1/(n+1))` for a right-continuous
filtration it gives the right-`L²`-continuity of `t ↦ 𝔼[ξ | ℱ t]` that the càdlàg regularisation
of cited result #13b needs.

## Main statements

* `lpMeas_iInf_of_antitone` — `⨅ n, lpMeas (m n) = lpMeas (⨅ n, m n)`.
* `tendsto_condExpL2_of_antitone` — the `L²` conditional expectations converge.
-/

open MeasureTheory Filter Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*}

/-- `lpMeas` is monotone in the σ-algebra. -/
theorem lpMeas_mono {m m' m₀ : MeasurableSpace Ω} {μ : Measure Ω} (h : m ≤ m') :
    lpMeas ℝ ℝ m 2 μ ≤ lpMeas ℝ ℝ m' 2 μ := by
  intro f hf
  rw [mem_lpMeas_iff_aestronglyMeasurable] at hf ⊢
  obtain ⟨g, hg, hfg⟩ := hf
  exact ⟨g, hg.mono h, hfg⟩

variable {m : ℕ → MeasurableSpace Ω} {m₀ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The `lpMeas` subspaces of an antitone sequence are antitone. -/
theorem antitone_lpMeas (hanti : Antitone m) :
    Antitone fun n => lpMeas ℝ ℝ (m n) 2 μ := fun _ _ hab => lpMeas_mono (m₀ := m₀) (hanti hab)

/-- **The intersection of the `lpMeas` subspaces of an antitone sequence is the `lpMeas` subspace
of the infimum.** -/
theorem lpMeas_iInf_of_antitone (hanti : Antitone m) :
    ⨅ n, lpMeas ℝ ℝ (m n) 2 μ = lpMeas ℝ ℝ (⨅ n, m n) 2 μ := by
  refine le_antisymm (fun f hf => ?_)
    (le_iInf fun n => lpMeas_mono (m₀ := m₀) (iInf_le m n))
  rw [Submodule.mem_iInf] at hf
  rw [mem_lpMeas_iff_aestronglyMeasurable]
  exact aestronglyMeasurable_iInf_of_antitone hanti fun n =>
    mem_lpMeas_iff_aestronglyMeasurable.1 (hf n)

/-- **The `L²` conditional expectations converge along a decreasing sequence of σ-algebras** —
the downward counterpart of `Integrable.tendsto_eLpNorm_condExp`, which goes upward. -/
theorem tendsto_condExpL2_of_antitone (hanti : Antitone m) (hle : ∀ n, m n ≤ m₀)
    (hle_inf : (⨅ n, m n) ≤ m₀) (f : Lp ℝ 2 μ) :
    Tendsto (fun n => ((condExpL2 ℝ ℝ (hle n) f : Lp ℝ 2 μ))) atTop
      (𝓝 ((condExpL2 ℝ ℝ hle_inf f : Lp ℝ 2 μ))) := by
  haveI hfn : ∀ n, Fact (m n ≤ m₀) := fun n => ⟨hle n⟩
  haveI hfi : Fact ((⨅ n, m n) ≤ m₀) := ⟨hle_inf⟩
  set V : ℕ → Submodule ℝ (Lp ℝ 2 μ) := fun n => lpMeas ℝ ℝ (m n) 2 μ with hVdef
  have hViInf : ⨅ n, V n = lpMeas ℝ ℝ (⨅ n, m n) 2 μ := lpMeas_iInf_of_antitone hanti
  haveI hVc : ∀ n, CompleteSpace (V n) := fun n => inferInstanceAs (CompleteSpace (lpMeas ..))
  haveI : (⨅ n, V n).HasOrthogonalProjection := by rw [hViInf]; infer_instance
  have hclosed : ∀ n, IsClosed ((V n : Set (Lp ℝ 2 μ))) :=
    fun n => (completeSpace_coe_iff_isComplete.1 (hVc n)).isClosed
  have key := tendsto_starProjection_of_antitone (antitone_lpMeas (m₀ := m₀) hanti) hclosed f
  have heq : (lpMeas ℝ ℝ (⨅ n, m n) 2 μ).starProjection f = (⨅ n, V n).starProjection f := by
    refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
    · exact hViInf ▸ (⨅ n, V n).starProjection_apply_mem f
    · exact hViInf ▸ (⨅ n, V n).sub_starProjection_mem_orthogonal f
  change Tendsto (fun n => (lpMeas ℝ ℝ (m n) 2 μ).starProjection f) atTop
    (𝓝 ((lpMeas ℝ ℝ (⨅ n, m n) 2 μ).starProjection f))
  rw [heq]
  exact key

end LevyStochCalc.Probability
