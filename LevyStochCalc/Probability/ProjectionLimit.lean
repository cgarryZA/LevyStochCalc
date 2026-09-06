/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Orthogonal projections along a decreasing sequence of subspaces

For nested closed subspaces `W ≤ V` the projections compose, `P_W ∘ P_V = P_W`, and Pythagoras
splits the larger projection, `‖P_V x‖² = ‖P_W x‖² + ‖P_V x − P_W x‖²`. Along an antitone sequence
`V 0 ≥ V 1 ≥ ⋯` that makes `n ↦ ‖P_{V n} x‖²` antitone and bounded below, hence convergent, and the
same identity turns its Cauchy property into the Cauchy property of `(P_{V n} x)` itself. The limit
lies in every `V N` and is orthogonal to `⨅ n, V n`, so it *is* the projection onto the
intersection.

This is the Hilbert-space half of the downward `L²` convergence of conditional expectations that
cited result #13b needs; the measure-theoretic half is
`LevyStochCalc/Probability/AEMeasurableInf.lean`, which identifies the intersection of the
`lpMeas` subspaces.

## Main statements

* `starProjection_starProjection_of_le` — the projections compose on nested subspaces.
* `norm_sq_starProjection_of_le` — Pythagoras for nested projections.
* `norm_starProjection_sub_le_of_le` — `‖P_V x − P_U x‖ ≤ ‖P_W x − P_U x‖` for `U ≤ V ≤ W`.
* `tendsto_starProjection_of_antitone` — `P_{V n} x → P_{⨅ V n} x`.
-/

open Filter Topology Submodule

namespace LevyStochCalc.Probability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- On nested subspaces the orthogonal projections compose: `P_W ∘ P_V = P_W` for `W ≤ V`. -/
theorem starProjection_starProjection_of_le {V W : Submodule ℝ E} [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (h : W ≤ V) (x : E) :
    W.starProjection (V.starProjection x) = W.starProjection x := by
  have hx : x - V.starProjection x ∈ Wᗮ :=
    Submodule.orthogonal_le h (V.sub_starProjection_mem_orthogonal x)
  have h0 : W.starProjection (x - V.starProjection x) = 0 :=
    Submodule.eq_starProjection_of_mem_orthogonal W.zero_mem (by simpa using hx)
  rw [map_sub] at h0
  exact (sub_eq_zero.1 h0).symm

omit [CompleteSpace E] in
/-- **Pythagoras for nested projections.** -/
theorem norm_sq_starProjection_of_le {V W : Submodule ℝ E} [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (h : W ≤ V) (x : E) :
    ‖V.starProjection x‖ ^ 2
      = ‖W.starProjection x‖ ^ 2 + ‖V.starProjection x - W.starProjection x‖ ^ 2 := by
  have key := W.norm_sq_eq_add_norm_sq_starProjection (V.starProjection x)
  rw [starProjection_starProjection_of_le h x] at key
  have horth : Wᗮ.starProjection (V.starProjection x)
      = V.starProjection x - W.starProjection x := by
    rw [Submodule.starProjection_orthogonal W]
    simp [starProjection_starProjection_of_le h x]
  rwa [horth] at key

omit [CompleteSpace E] in
/-- Equal subspaces have equal orthogonal projections. -/
theorem starProjection_congr {V W : Submodule ℝ E} [V.HasOrthogonalProjection]
    [W.HasOrthogonalProjection] (h : V = W) (x : E) :
    V.starProjection x = W.starProjection x := by
  subst h; rfl

omit [CompleteSpace E] in
/-- For nested subspaces `U ≤ V ≤ W` the projection onto the larger of the two outer subspaces is
the further one from `P_U x`. -/
theorem norm_starProjection_sub_le_of_le {U V W : Submodule ℝ E} [U.HasOrthogonalProjection]
    [V.HasOrthogonalProjection] [W.HasOrthogonalProjection] (hUV : U ≤ V) (hVW : V ≤ W) (x : E) :
    ‖V.starProjection x - U.starProjection x‖ ≤ ‖W.starProjection x - U.starProjection x‖ := by
  have h₁ := norm_sq_starProjection_of_le hUV x
  have h₂ := norm_sq_starProjection_of_le (hUV.trans hVW) x
  have h₃ := norm_sq_starProjection_of_le hVW x
  refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 ?_
  nlinarith [sq_nonneg ‖W.starProjection x - V.starProjection x‖]

section Antitone

variable {V : ℕ → Submodule ℝ E} [∀ n, (V n).HasOrthogonalProjection]

omit [CompleteSpace E] in
/-- Along an antitone sequence the squared norms of the projections are antitone. -/
theorem antitone_norm_sq_starProjection (hV : Antitone V) (x : E) :
    Antitone fun n => ‖(V n).starProjection x‖ ^ 2 := by
  intro a b hab
  have := norm_sq_starProjection_of_le (hV hab) x
  nlinarith [sq_nonneg ‖(V a).starProjection x - (V b).starProjection x‖]

/-- **The projections converge to the projection onto the intersection.** -/
theorem tendsto_starProjection_of_antitone (hV : Antitone V)
    (hclosed : ∀ n, IsClosed ((V n : Set E)))
    [(⨅ n, V n).HasOrthogonalProjection] (x : E) :
    Tendsto (fun n => (V n).starProjection x) atTop (𝓝 ((⨅ n, V n).starProjection x)) := by
  set a : ℕ → ℝ := fun n => ‖(V n).starProjection x‖ ^ 2 with ha
  have ha_anti : Antitone a := antitone_norm_sq_starProjection hV x
  have ha_bdd : BddBelow (Set.range a) := ⟨0, by rintro _ ⟨n, rfl⟩; positivity⟩
  have ha_tendsto : Tendsto a atTop (𝓝 (⨅ n, a n)) := tendsto_atTop_ciInf ha_anti ha_bdd
  -- the projections form a Cauchy sequence
  have hcauchy : CauchySeq fun n => (V n).starProjection x := by
    refine cauchySeq_of_le_tendsto_0 (fun N => Real.sqrt (a N - ⨅ n, a n)) ?_ ?_
    · intro n m N hn hm
      have hsplit : ∀ p q : ℕ, p ≤ q →
          ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2 = a p - a q := by
        intro p q hpq
        have := norm_sq_starProjection_of_le (hV hpq) x
        simp only [ha]
        linarith
      have hle : ∀ p q : ℕ, N ≤ p → N ≤ q → p ≤ q →
          dist ((V p).starProjection x) ((V q).starProjection x)
            ≤ Real.sqrt (a N - ⨅ k, a k) := by
        intro p q hp hq hpq
        have h1 : ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2 = a p - a q :=
          hsplit p q hpq
        have h2 : a p ≤ a N := ha_anti hp
        have h3 : (⨅ k, a k) ≤ a q := ciInf_le ha_bdd q
        have h4 : ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2
            ≤ a N - ⨅ k, a k := by rw [h1]; linarith
        rw [dist_eq_norm]
        have h5 : 0 ≤ ‖(V p).starProjection x - (V q).starProjection x‖ := norm_nonneg _
        nlinarith [Real.sq_sqrt (le_trans (by positivity : (0:ℝ) ≤
            ‖(V p).starProjection x - (V q).starProjection x‖ ^ 2) h4),
          Real.sqrt_nonneg (a N - ⨅ k, a k)]
      rcases le_total n m with hnm | hmn
      · exact hle n m hn hm hnm
      · rw [dist_comm]; exact hle m n hm hn hmn
    · have h1 : Tendsto (fun N => a N - ⨅ n, a n) atTop (𝓝 0) := by
        simpa using ha_tendsto.sub (tendsto_const_nhds (x := ⨅ n, a n))
      have h2 : Tendsto (fun N => Real.sqrt (a N - ⨅ n, a n)) atTop (𝓝 (Real.sqrt 0)) :=
        (Real.continuous_sqrt.tendsto 0).comp h1
      simpa using h2
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit lies in every `V N`, hence in the intersection
  have hyV : ∀ N, y ∈ V N := by
    intro N
    refine (hclosed N).mem_of_tendsto (hy.comp (tendsto_add_atTop_nat N)) ?_
    filter_upwards with n
    exact hV (Nat.le_add_left N n) ((V (n + N)).starProjection_apply_mem x)
  have hymem : y ∈ ⨅ n, V n := (Submodule.mem_iInf _).2 hyV
  -- and `x - y` is orthogonal to the intersection
  have horth : x - y ∈ (⨅ n, V n)ᗮ := by
    rw [Submodule.mem_orthogonal]
    intro w hw
    have hstep : ∀ n, inner ℝ w (x - (V n).starProjection x) = 0 := by
      intro n
      have hwn : w ∈ V n := (Submodule.mem_iInf _).1 hw n
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal' _ _).1 ((V n).sub_starProjection_mem_orthogonal x) w hwn
    have hlim : Tendsto (fun n => inner ℝ w (x - (V n).starProjection x)) atTop
        (𝓝 (inner ℝ w (x - y))) :=
      Filter.Tendsto.inner tendsto_const_nhds (tendsto_const_nhds.sub hy)
    have hzero : inner ℝ w (x - y) = 0 := by
      refine tendsto_nhds_unique hlim ?_
      simp [hstep]
    simpa [real_inner_comm] using hzero
  have hproj : (⨅ n, V n).starProjection x = y :=
    Submodule.eq_starProjection_of_mem_orthogonal hymem horth
  rw [hproj]
  exact hy

end Antitone

end LevyStochCalc.Probability
