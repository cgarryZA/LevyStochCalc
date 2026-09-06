/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Probability.Process.Filtration
import LevyStochCalc.Probability.CondExpInf

/-!
# Right continuity in `L²` of the conditional expectation along a right-continuous filtration

For a filtration `ℱ` indexed by `ℝ` the σ-algebras `ℱ (t + 1/(n+1))` form an antitone sequence
whose infimum is `⨅ r > t, ℱ r`, which is `ℱ t` when `ℱ` is right-continuous. The `L²`
conditional expectations therefore converge to `𝔼[f | ℱ t]` along that sequence
(`CondExpInf.lean`), and `r ↦ ‖𝔼[f | ℱ r] − 𝔼[f | ℱ t]‖` is monotone on `[t, ∞)` because the
subspaces `lpMeas (ℱ r)` grow, so the convergence upgrades from the sequence to the filter
`𝓝[>] t`.

## Main statements

* `iInf_filtration_add_one_div` — `⨅ n, ℱ (t + 1/(n+1)) = ⨅ r > t, ℱ r`.
* `tendsto_condExpL2_nhdsGT` — `𝔼[f | ℱ r] → 𝔼[f | ℱ t]` in `L²` as `r ↓ t`.
-/

open Filter MeasureTheory Topology
open scoped MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {m₀ : MeasurableSpace Ω} {μ : MeasureTheory.Measure Ω}

section Sequence

variable (ℱ : Filtration ℝ m₀) (t : ℝ)

/-- The sequence `t + 1/(n+1)` is a strictly decreasing sequence of times above `t`. -/
theorem lt_add_one_div (n : ℕ) : t < t + 1 / (n + 1 : ℝ) := by
  have : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  linarith

/-- Evaluating a filtration along `t + 1/(n+1)` gives an antitone sequence of σ-algebras. -/
theorem antitone_filtration_add_one_div :
    Antitone fun n : ℕ => ℱ (t + 1 / (n + 1 : ℝ)) := by
  intro a b hab
  refine ℱ.mono ?_
  have hab' : (a : ℝ) + 1 ≤ (b : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hab
  have : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
    apply one_div_le_one_div_of_le _ hab'
    positivity
  linarith

/-- The σ-algebras of a filtration along `t + 1/(n+1)` have infimum `⨅ r > t, ℱ r`. -/
theorem iInf_filtration_add_one_div :
    ⨅ n : ℕ, ℱ (t + 1 / (n + 1 : ℝ)) = ⨅ r > t, ℱ r := by
  refine le_antisymm (le_iInf₂ fun r hr => ?_) (le_iInf fun n => ?_)
  · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hr)
    exact iInf_le_of_le n (ℱ.mono (by linarith))
  · exact iInf₂_le_of_le (t + 1 / (n + 1 : ℝ)) (lt_add_one_div t n) le_rfl

/-- Along a right-continuous filtration the σ-algebras `ℱ (t + 1/(n+1))` have infimum `ℱ t`. -/
theorem iInf_filtration_add_one_div_of_isRightContinuous [ℱ.IsRightContinuous] :
    ⨅ n : ℕ, ℱ (t + 1 / (n + 1 : ℝ)) = ℱ t := by
  rw [iInf_filtration_add_one_div, ← ℱ.rightCont_eq t, Filtration.IsRightContinuous.eq]

end Sequence

/-- **The `L²` conditional expectation is right-continuous along a right-continuous filtration.**
-/
theorem tendsto_condExpL2_nhdsGT (ℱ : Filtration ℝ m₀) [ℱ.IsRightContinuous] (t : ℝ)
    (f : Lp ℝ 2 μ) :
    Tendsto (fun r => ((condExpL2 ℝ ℝ (ℱ.le r) f : Lp ℝ 2 μ))) (𝓝[>] t)
      (𝓝 ((condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ))) := by
  haveI hFact : ∀ r : ℝ, Fact (ℱ r ≤ m₀) := fun r => ⟨ℱ.le r⟩
  set s : ℕ → ℝ := fun n => t + 1 / (n + 1 : ℝ) with hs
  have hinf : ⨅ n, ℱ (s n) = ℱ t := iInf_filtration_add_one_div_of_isRightContinuous ℱ t
  have hle_inf : (⨅ n, ℱ (s n)) ≤ m₀ := hinf ▸ ℱ.le t
  haveI : Fact ((⨅ n, ℱ (s n)) ≤ m₀) := ⟨hle_inf⟩
  have key := tendsto_condExpL2_of_antitone (antitone_filtration_add_one_div ℱ t)
    (fun n => ℱ.le (s n)) hle_inf f
  have hlimit : ((condExpL2 ℝ ℝ hle_inf f : Lp ℝ 2 μ))
      = ((condExpL2 ℝ ℝ (ℱ.le t) f : Lp ℝ 2 μ)) := by
    change (lpMeas ℝ ℝ (⨅ n, ℱ (s n)) 2 μ).starProjection f
      = (lpMeas ℝ ℝ (ℱ t) 2 μ).starProjection f
    exact starProjection_congr (congrArg (fun mm => lpMeas ℝ ℝ mm 2 μ) hinf) f
  rw [hlimit] at key
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 key ε hε
  filter_upwards [Ioo_mem_nhdsGT (lt_add_one_div t N)] with r hr
  refine lt_of_le_of_lt ?_ (hN N le_rfl)
  simp only [dist_eq_norm]
  exact norm_starProjection_sub_le_of_le (lpMeas_mono (m₀ := m₀) (ℱ.mono hr.1.le))
    (lpMeas_mono (m₀ := m₀) (ℱ.mono hr.2.le)) f

end LevyStochCalc.Probability
