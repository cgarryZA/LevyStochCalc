/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import Mathlib.Topology.Order.LeftRightLim
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Bases

/-!
# The jumps of a càdlàg function

A function on the line that is right-continuous and has left limits everywhere jumps only at
isolated points of each level of the jump size, so its jump set is countable and therefore
Lebesgue-null: such a function agrees with its left limits almost everywhere.
-/

open Filter Set MeasureTheory
open scoped Topology

namespace LevyStochCalc.Analysis

/-- A bound on a function just left of a point bounds its left limit there. -/
theorem abs_leftLim_sub_le {f : ℝ → ℝ} {s a c r : ℝ} (has : a < s)
    (hL : ∃ L : ℝ, Tendsto f (𝓝[<] s) (𝓝 L)) (h : ∀ u ∈ Set.Ioo a s, |f u - c| ≤ r) :
    |Function.leftLim f s - c| ≤ r := by
  obtain ⟨L, hLt⟩ := hL
  have hlim : Function.leftLim f s = L := leftLim_eq_of_tendsto hLt
  rw [hlim]
  have hev : ∀ᶠ u in 𝓝[<] s, |f u - c| ≤ r := by
    filter_upwards [Ioo_mem_nhdsLT has] with u hu
    exact h u hu
  exact le_of_tendsto ((hLt.sub_const c).abs) hev

/-- **A jump of a càdlàg function is isolated among the jumps of its size.** -/
theorem exists_isolating_radius {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ δ > 0, ∀ s ∈ Set.Ioo (t - δ) (t + δ), s ≠ t → |f s - Function.leftLim f s| < ε := by
  have hε3 : (0 : ℝ) < ε / 3 := by positivity
  obtain ⟨δ₁, hδ₁, hr1⟩ := Metric.tendsto_nhdsWithin_nhds.mp (hright t) (ε / 3) hε3
  obtain ⟨L, hLt⟩ := hleft t
  obtain ⟨δ₂, hδ₂, hr2⟩ := Metric.tendsto_nhdsWithin_nhds.mp hLt (ε / 3) hε3
  have h1 : ∀ s, t < s → dist s t < δ₁ → |f s - f t| < ε / 3 := by
    intro s hs hd
    have := hr1 hs hd
    rwa [Real.dist_eq] at this
  have h2 : ∀ s, s < t → dist s t < δ₂ → |f s - L| < ε / 3 := by
    intro s hs hd
    have := hr2 hs hd
    rwa [Real.dist_eq] at this
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun s hs hst => ?_⟩
  have hmin₁ : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
  have hmin₂ : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
  rcases lt_or_gt_of_ne hst with hlt | hgt
  · -- `s` is to the left of `t`
    have hsd : dist s t < δ₂ := by
      rw [Real.dist_eq, abs_of_neg (by linarith : s - t < 0)]
      have := hs.1
      linarith
    have hfs : |f s - L| < ε / 3 := h2 s hlt hsd
    have hls : |Function.leftLim f s - L| ≤ ε / 3 := by
      refine abs_leftLim_sub_le (a := t - δ₂) (by linarith [hs.1]) (hleft s) fun u hu => ?_
      have hud : dist u t < δ₂ := by
        rw [Real.dist_eq, abs_of_neg (by linarith [hu.2] : u - t < 0)]
        linarith [hu.1]
      exact (h2 u (by linarith [hu.2]) hud).le
    have htri : |f s - Function.leftLim f s| ≤ |f s - L| + |Function.leftLim f s - L| := by
      calc |f s - Function.leftLim f s| ≤ |f s - L| + |L - Function.leftLim f s| :=
            abs_sub_le _ _ _
        _ = |f s - L| + |Function.leftLim f s - L| := by rw [abs_sub_comm L]
    linarith
  · -- `s` is to the right of `t`
    have hsd : dist s t < δ₁ := by
      rw [Real.dist_eq, abs_of_pos (by linarith : 0 < s - t)]
      have := hs.2
      linarith
    have hfs : |f s - f t| < ε / 3 := h1 s hgt hsd
    have hls : |Function.leftLim f s - f t| ≤ ε / 3 := by
      refine abs_leftLim_sub_le (a := t) hgt (hleft s) fun u hu => ?_
      have hud : dist u t < δ₁ := by
        rw [Real.dist_eq, abs_of_pos (by linarith [hu.1] : 0 < u - t)]
        linarith [hu.2, hs.2]
      exact (h1 u hu.1 hud).le
    have htri : |f s - Function.leftLim f s| ≤ |f s - f t| + |Function.leftLim f s - f t| := by
      calc |f s - Function.leftLim f s| ≤ |f s - f t| + |f t - Function.leftLim f s| :=
            abs_sub_le _ _ _
        _ = |f s - f t| + |Function.leftLim f s - f t| := by rw [abs_sub_comm (f t)]
    linarith

/-- **The jump set of a càdlàg function is countable.** -/
theorem countable_setOf_ne_leftLim {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) :
    {t : ℝ | f t ≠ Function.leftLim f t}.Countable := by
  have hcov : {t : ℝ | f t ≠ Function.leftLim f t}
      = ⋃ n : ℕ, {t : ℝ | 1 / (n + 1 : ℝ) < |f t - Function.leftLim f t|} := by
    ext t
    simp only [Set.mem_iUnion, Set.mem_setOf_eq]
    constructor
    · intro h
      exact exists_nat_one_div_lt (abs_pos.mpr (sub_ne_zero.mpr h))
    · rintro ⟨n, hn⟩ heq
      rw [heq, sub_self, abs_zero] at hn
      exact absurd hn (not_lt.mpr (by positivity))
  rw [hcov]
  refine Set.countable_iUnion fun n => ?_
  have hε : (0 : ℝ) < 1 / (n + 1 : ℝ) := by positivity
  choose δ hδpos hδ using fun t : ℝ => exists_isolating_radius hright hleft hε t
  refine Set.PairwiseDisjoint.countable_of_isOpen
    (s := fun t : ℝ => Set.Ioo (t - δ t / 2) (t + δ t / 2)) ?_ (fun t _ => isOpen_Ioo)
    (fun t _ => ⟨t, ⟨by linarith [hδpos t], by linarith [hδpos t]⟩⟩)
  intro a ha b hb hab
  refine Set.disjoint_left.mpr fun x hx hx' => ?_
  have hxa : |x - a| < δ a / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hxb : |x - b| < δ b / 2 := by
    rw [abs_lt]
    exact ⟨by linarith [hx'.1], by linarith [hx'.2]⟩
  have hab' : |a - b| < δ a / 2 + δ b / 2 := by
    calc |a - b| ≤ |a - x| + |x - b| := abs_sub_le _ _ _
      _ = |x - a| + |x - b| := by rw [abs_sub_comm a]
      _ < δ a / 2 + δ b / 2 := by linarith
  rw [abs_lt] at hab'
  rcases le_total (δ b) (δ a) with hle | hle
  · have hba : b ∈ Set.Ioo (a - δ a) (a + δ a) := by
      constructor <;> linarith [hab'.1, hab'.2, hδpos b]
    have hjump := hδ a b hba (Ne.symm hab)
    have hb' : 1 / ((n : ℝ) + 1) < |f b - Function.leftLim f b| := hb
    linarith
  · have hab2 : a ∈ Set.Ioo (b - δ b) (b + δ b) := by
      constructor <;> linarith [hab'.1, hab'.2, hδpos a]
    have hjump := hδ b a hab2 hab
    have ha' : 1 / ((n : ℝ) + 1) < |f a - Function.leftLim f a| := ha
    linarith

/-- **A càdlàg function agrees with its left limits almost everywhere.** -/
theorem ae_eq_leftLim_of_cadlag {f : ℝ → ℝ}
    (hright : ∀ t : ℝ, Tendsto f (𝓝[>] t) (𝓝 (f t)))
    (hleft : ∀ t : ℝ, ∃ L : ℝ, Tendsto f (𝓝[<] t) (𝓝 L)) :
    ∀ᵐ t ∂(volume : Measure ℝ), f t = Function.leftLim f t := by
  rw [ae_iff]
  exact (countable_setOf_ne_leftLim hright hleft).measure_zero _

end LevyStochCalc.Analysis
