import Mathlib

/-!
# LevyStochCalc.Basic

Project-wide imports and milestone-tagging primitive.

A `levyStochCalc_milestone` attribute (analogous to the main dissertation's
`dissertation_axiom`) will be added when the first headline theorem of a
layer is proved CLEAN; until then there is nothing to register.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace LevyStochCalc

/-- **Reverse triangle for `eLpNorm` in `tsub` form.** Standard consequence of
`MeasureTheory.eLpNorm_add_le`: for `1 ≤ p`,
`eLpNorm f p μ - eLpNorm g p μ ≤ eLpNorm (f - g) p μ` (ENNReal truncated). -/
lemma eLpNorm_sub_eLpNorm_le_eLpNorm_sub
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f g : α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hg : MeasureTheory.AEStronglyMeasurable g μ) :
    MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm g p μ
      ≤ MeasureTheory.eLpNorm (f - g) p μ := by
  rw [tsub_le_iff_left]
  have h_decomp : f = g + (f - g) := by ext x; simp
  have h_meas_diff : MeasureTheory.AEStronglyMeasurable (f - g) μ := hf.sub hg
  conv_lhs => rw [h_decomp]
  exact MeasureTheory.eLpNorm_add_le hg h_meas_diff hp

/-- **L²-norm continuity from L²-difference vanishing.** If
`eLpNorm (fn n - f) p μ → 0`, then `eLpNorm (fn n) p μ → eLpNorm f p μ`.

Squeeze argument:
* upper bound `eLpNorm (fn n) ≤ eLpNorm f + eLpNorm (fn n - f)` from
  `fn n = f + (fn n - f)` plus triangle (`eLpNorm_add_le`);
* lower bound `eLpNorm f - eLpNorm (fn n - f) ≤ eLpNorm (fn n)` from
  the same decomposition with the role of `f` and `fn n` swapped.

Both bounds tend to `eLpNorm f` (upper via `Tendsto.const_add`, lower via
`ENNReal.Tendsto.sub`); squeeze closes the proof.

This is a generic version, namespace-shared between Brownian and Compensated chains. -/
lemma eLpNorm_tendsto_of_eLpNorm_sub_tendsto_zero
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure α}
    {f : α → E} {fn : ℕ → α → E}
    (hf : MeasureTheory.AEStronglyMeasurable f μ)
    (hfn : ∀ n, MeasureTheory.AEStronglyMeasurable (fn n) μ)
    (h_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n - f) p μ) Filter.atTop (nhds 0)) :
    Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fn n) p μ) Filter.atTop
      (nhds (MeasureTheory.eLpNorm f p μ)) := by
  have h_upper : ∀ n, MeasureTheory.eLpNorm (fn n) p μ ≤
      MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ := by
    intro n
    have h_decomp : fn n = f + (fn n - f) := by ext x; simp
    have h_meas_diff : MeasureTheory.AEStronglyMeasurable (fn n - f) μ :=
      (hfn n).sub hf
    conv_lhs => rw [h_decomp]
    exact MeasureTheory.eLpNorm_add_le hf h_meas_diff hp
  have h_lower : ∀ n,
      MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ
        ≤ MeasureTheory.eLpNorm (fn n) p μ := by
    intro n
    rw [tsub_le_iff_right]
    have h_decomp : f = fn n + -(fn n - f) := by ext x; simp
    have h_meas_diff : MeasureTheory.AEStronglyMeasurable (fn n - f) μ :=
      (hfn n).sub hf
    have h_meas_neg_diff : MeasureTheory.AEStronglyMeasurable (-(fn n - f)) μ :=
      h_meas_diff.neg
    calc MeasureTheory.eLpNorm f p μ
        = MeasureTheory.eLpNorm (fn n + -(fn n - f)) p μ := by rw [← h_decomp]
      _ ≤ MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (-(fn n - f)) p μ :=
          MeasureTheory.eLpNorm_add_le (hfn n) h_meas_neg_diff hp
      _ = MeasureTheory.eLpNorm (fn n) p μ
            + MeasureTheory.eLpNorm (fn n - f) p μ := by
          rw [MeasureTheory.eLpNorm_neg]
  have h_lower_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ - MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := ENNReal.Tendsto.sub
      (tendsto_const_nhds (x := MeasureTheory.eLpNorm f p μ))
      h_tendsto (Or.inr ENNReal.zero_ne_top)
    simpa using h
  have h_upper_tendsto : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm f p μ + MeasureTheory.eLpNorm (fn n - f) p μ)
      Filter.atTop (nhds (MeasureTheory.eLpNorm f p μ)) := by
    have h := h_tendsto.const_add (MeasureTheory.eLpNorm f p μ)
    simpa using h
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    h_lower_tendsto h_upper_tendsto h_lower h_upper

end LevyStochCalc
