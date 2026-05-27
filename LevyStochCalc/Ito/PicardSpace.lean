/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.Picard
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Typeclass instances for `SBoundedProcess` — Banach fixed-point preconditions

This file provides the three typeclass instances on `SBoundedProcess P T` that
are required by the Banach fixed-point shim
`LevyStochCalc.Ito.Picard.picardFixedPoint` in `Ito/PicardBanach.lean`:

* `Nonempty (SBoundedProcess P T)` — witnessed by the constant-zero process.
* `MetricSpace (SBoundedProcess P T)` — equipping the structure with a metric.
* `CompleteSpace (SBoundedProcess P T)` — every Cauchy sequence converges.

## TYPECLASS-PLACEHOLDER WARNING (red-team 3rd-audit HIGH #1, 2026-05-27)

**The `MetricSpace` and `CompleteSpace` instances in this file use the
*discrete metric* (`dist X Y = 0 if X = Y else 1`). These are
TYPECLASS-PLACEHOLDER instances — they exist solely so that the generic
Banach fixed-point shim `picardFixedPoint` in `PicardBanach.lean` can be
specialised to `SBoundedProcess` at the level of Lean's typeclass system.**

**Discrete-metric `picardFixedPoint` (on `SBoundedProcess` directly) is
typeclass-trivial: completeness is vacuous (Cauchy sequences are
eventually constant), contractions in the discrete metric collapse to
the identity on the fixed-point fibre, and the unique fixed point is
the starting iterate. NO SUBSTANTIVE MATHEMATICAL CONTENT is carried by
the discrete-metric specialisation — it discharges the typeclass
obligation only.**

**All substantive Banach work (the literature Bielecki β-weighted L²-sup
norm with genuine contraction at the analytical rate
`3 n L² (T+2) / (2β)`) is carried out in the `AEQuot β T` quotient space
defined in `PicardSpaceBielecki.lean` (β-norm pseudometric → genuine
metric on a.e.-equivalence classes) + `PicardSpaceBieleckiComplete.lean`
(`CompleteSpace` instance via Lp completeness + Doob càdlàg modification),
and the SDE chain wraps up via
`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot` in the latter
file. The literature-strength fixed point of the Picard iteration is
delivered there, NOT here.**

## Design choice

The natural metric for the literature Picard iteration is the Bielecki
β-weighted L²-sup norm
`‖X‖_{β,T} = sup_{t ≤ T} e^{-βt} √(𝔼[‖X_t‖²])`
defined in `Picard.bieleckiNorm`. However this is only a *pseudo*-norm on
`SBoundedProcess`: two processes that agree almost surely have zero Bielecki
distance but are not equal as elements of the structure (which carries the
raw path map `X : ℝ → Ω → Fin n → ℝ`). Promoting to a genuine `MetricSpace`
therefore requires a quotient by P-null sets — DONE in
`PicardSpaceBielecki.lean`'s `AEQuot β T` (and completed in
`PicardSpaceBieleckiComplete.lean`).

We adopt the discrete metric here:
`dist X Y = 0 if X = Y else 1` (via classical decidability of equality).
This satisfies all `MetricSpace` axioms by construction, gives a trivially
complete metric (every Cauchy sequence is eventually constant), and lets
the Banach fixed-point shim specialise to `SBoundedProcess` immediately.
The substantive Bielecki-norm contraction estimate (developed across
`PicardContraction.lean`, `PicardSigmaLipschitz.lean`,
`PicardGammaLipschitz.lean`) operates on the pseudo-edist
`bieleckiNorm (X - Y)` directly via the `bielecki_*` lemma family and is
independent of which `MetricSpace` instance is installed on the structure
type itself (the Banach shim is parameterized by an arbitrary contraction
map `Φ` and rate `K`, so the actual contraction proof can be carried out
in any metric that's appropriate to the problem at hand — and indeed
the literature one is carried out on the AE-quotient, not here).

## Status

Sorry-free. Adds three `instance` declarations under
`LevyStochCalc.Ito.Picard`. The Banach shim `picardFixedPoint` (in
`PicardBanach.lean`) can now be invoked with no remaining typeclass
obligations beyond the user-supplied contraction `ContractingWith K Φ`.
The literature substantive contraction work happens on
`PicardSpaceBielecki.AEQuot`, not on `SBoundedProcess`-with-discrete-metric.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Picard

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]

/-! ### Nonempty: the constant-zero process witnesses inhabitedness. -/

/-- **Constant-zero `SBoundedProcess`.** The map `X t ω = 0` (the zero
vector in `Fin n → ℝ`) is the canonical witness of `Nonempty
(SBoundedProcess P T)`:

* **Measurability** — `Function.uncurry (fun _ _ => 0) = fun _ => 0` is the
  zero constant, hence trivially measurable (`Measurable.const 0`).
* **Càdlàg paths** — every constant function is continuous, so the
  right-limit `Filter.Tendsto` is `tendsto_const_nhds`; for the left
  limit, the witness `L = 0` makes the left-limit `Filter.Tendsto` also
  `tendsto_const_nhds`.
* **`sup_L2`** — `bieleckiNorm β T 0 = 0 < ⊤` because the integrand
  `(∑ i, ‖0‖²) = 0` makes the inner `∫⁻` and the outer rpow both zero;
  multiplying by `ENNReal.ofReal (exp (-β·t))` and taking the supremum
  over `t ∈ [0, T]` still gives zero, which is `< ⊤`. -/
noncomputable def constantZeroProcess
    {n : ℕ} (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) :
    SBoundedProcess (n := n) P T where
  X := fun _ _ => 0
  measurable_path := by
    have : Function.uncurry (fun (_ : ℝ) (_ : Ω) => (0 : Fin n → ℝ)) =
        fun _ => 0 := by
      funext p
      simp [Function.uncurry]
    rw [this]
    exact measurable_const
  cadlag_paths := by
    refine Filter.Eventually.of_forall (fun ω => ?_)
    intro t
    refine ⟨?_, ?_⟩
    · exact tendsto_const_nhds
    · intro _
      exact ⟨0, tendsto_const_nhds⟩
  sup_L2 := by
    unfold bieleckiNorm
    refine lt_of_le_of_lt ?_ ENNReal.zero_lt_top
    refine iSup_le (fun t => ?_)
    refine iSup_le (fun _ => ?_)
    have h_sum_zero : (fun ω : Ω =>
        (∑ i, (‖(fun _ _ => (0 : Fin n → ℝ)) t ω i‖₊ : ℝ≥0∞) ^ 2)) =
        fun _ => 0 := by
      funext ω
      simp
    rw [h_sum_zero]
    simp

/-- `Nonempty` instance: constant zero process. -/
noncomputable instance instNonemptySBoundedProcess
    {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ} :
    Nonempty (SBoundedProcess (n := n) P T) :=
  ⟨constantZeroProcess P T⟩

/-! ### MetricSpace: discrete metric for typeclass satisfaction.

**TYPECLASS-PLACEHOLDER NOTICE (red-team 3rd-audit HIGH #1):** the metric
installed in this section is the *discrete metric* on `SBoundedProcess`:
`dist X Y = 0 if X = Y, else 1`. This satisfies all `MetricSpace` axioms
mechanically but carries **NO substantive analytical content**: it makes
every fixed-point question on `SBoundedProcess`-with-this-metric trivially
discrete (Cauchy ↔ eventually constant; contractions ↔ identity on the
fixed-point fibre; the unique fixed point is the starting iterate). The
goal of this instance is to discharge the typeclass obligation of the
generic Banach shim `picardFixedPoint`, NOT to deliver mathematics.

The literature Banach work (Bielecki β-weighted L²-sup norm with genuine
contraction at the analytical rate `3 n L² (T+2) / (2β)` for
`β > 3 n L² (T+2) / 2`) lives on the AE-quotient
`PicardSpaceBielecki.AEQuot β T` and wraps up in
`PicardSpaceBieleckiComplete.lean`'s
`picardFixedPoint_jumpDiffusion_exists_unique_via_aeQuot`. Downstream
consumers should treat the discrete-metric `picardFixedPoint` invocation
on `SBoundedProcess` as a typeclass shim only.

This is a genuine metric (separation holds by definition, triangle inequality
holds via case analysis), and is **complete** because every Cauchy sequence
in the discrete metric is eventually constant (Cauchy at scale `< 1` forces
all sufficiently far-out terms to be equal).

The discrete metric is **not** the literature `S²` / Bielecki norm — that
is a pseudometric on `SBoundedProcess` (zero distance iff a.s.-equal,
which is weaker than structure equality). The actual Picard contraction
estimate is developed against the pseudo-edist `bieleckiNorm (X - Y)`
in the `bielecki_*` lemma family and against the genuine metric on
`AEQuot β T`, and is logically independent of which `MetricSpace`
instance lives on the `SBoundedProcess` structure type.
-/

section DiscreteMetric
-- The discrete metric construction below uses `if X = Y then 0 else 1`,
-- which needs `Decidable (X = Y)`. Since `SBoundedProcess` is not decidably
-- equal in general, we `open Classical` for this section so the elaborator
-- pulls in the classical decidability instance. Linter is locally disabled
-- via a `set_option` because the `open Classical` is the simplest tactic
-- to thread classical decidability through every declaration in the section.
set_option linter.style.openClassical false
open Classical

variable {n : ℕ} {P : Measure Ω} [IsProbabilityMeasure P] {T : ℝ}

/-- The discrete distance on `SBoundedProcess`: zero on the diagonal,
one elsewhere. Uses classical decidability of equality (via the
section-local `open Classical`) to make `if X = Y then 0 else 1`
well-typed without needing a `[DecidableEq]` instance. -/
noncomputable def discreteDist
    (X Y : SBoundedProcess (n := n) P T) : ℝ :=
  if X = Y then 0 else 1

lemma discreteDist_self (X : SBoundedProcess (n := n) P T) :
    discreteDist X X = 0 := by
  simp [discreteDist]

lemma discreteDist_comm (X Y : SBoundedProcess (n := n) P T) :
    discreteDist X Y = discreteDist Y X := by
  unfold discreteDist
  by_cases h : X = Y
  · subst h; rfl
  · have h' : ¬ Y = X := fun heq => h heq.symm
    rw [if_neg h, if_neg h']

lemma discreteDist_triangle (X Y Z : SBoundedProcess (n := n) P T) :
    discreteDist X Z ≤ discreteDist X Y + discreteDist Y Z := by
  unfold discreteDist
  by_cases hXZ : X = Z
  · -- LHS = 0; RHS ≥ 0.
    rw [if_pos hXZ]
    have h₁ : (0 : ℝ) ≤ (if X = Y then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    have h₂ : (0 : ℝ) ≤ (if Y = Z then (0 : ℝ) else 1) := by
      split_ifs <;> norm_num
    linarith
  · -- LHS = 1; need 1 ≤ RHS.
    rw [if_neg hXZ]
    by_cases hXY : X = Y
    · by_cases hYZ : Y = Z
      · exact absurd (hXY.trans hYZ) hXZ
      · rw [if_pos hXY, if_neg hYZ]; linarith
    · rw [if_neg hXY]
      have h₂ : (0 : ℝ) ≤ (if Y = Z then (0 : ℝ) else 1) := by
        split_ifs <;> norm_num
      linarith

lemma discreteDist_eq_zero_iff
    (X Y : SBoundedProcess (n := n) P T) :
    discreteDist X Y = 0 ↔ X = Y := by
  unfold discreteDist
  by_cases h : X = Y
  · simp [h]
  · rw [if_neg h]
    exact ⟨fun h₀ => by linarith, fun heq => absurd heq h⟩

lemma discreteDist_nonneg (X Y : SBoundedProcess (n := n) P T) :
    0 ≤ discreteDist X Y := by
  unfold discreteDist
  split_ifs <;> norm_num

/-- **`PseudoMetricSpace` instance via the discrete distance.** -/
noncomputable instance instPseudoMetricSpaceSBoundedProcess :
    PseudoMetricSpace (SBoundedProcess (n := n) P T) where
  dist := discreteDist
  dist_self := discreteDist_self
  dist_comm := discreteDist_comm
  dist_triangle := discreteDist_triangle

/-- **`MetricSpace` instance via the discrete distance.** Promotes the
pseudo-metric to a genuine metric by adding the separation axiom
`dist X Y = 0 → X = Y`, which holds for the discrete distance by
construction. -/
noncomputable instance instMetricSpaceSBoundedProcess :
    MetricSpace (SBoundedProcess (n := n) P T) where
  __ := instPseudoMetricSpaceSBoundedProcess
  eq_of_dist_eq_zero {X Y} h := (discreteDist_eq_zero_iff X Y).mp h

/-! ### CompleteSpace: every Cauchy sequence in the discrete metric is
eventually constant, hence converges. -/

/-- **Cauchy sequence in the discrete metric is eventually constant.** If
`u : ℕ → SBoundedProcess` is Cauchy with respect to the discrete distance
inherited from `instMetricSpaceSBoundedProcess`, then there exists `N`
such that `u n = u N` for all `n ≥ N`. The witness `N` is obtained from
the Cauchy property at scale `ε = 1/2`: any two terms `u m`, `u n` with
`m, n ≥ N` have `dist (u m) (u n) < 1`, hence by the discrete distance
must satisfy `u m = u n`. -/
lemma cauchySeq_eventually_constant
    (u : ℕ → SBoundedProcess (n := n) P T) (hu : CauchySeq u) :
    ∃ N : ℕ, ∀ n ≥ N, u n = u N := by
  rw [Metric.cauchySeq_iff] at hu
  obtain ⟨N, hN⟩ := hu (1/2) (by norm_num)
  refine ⟨N, ?_⟩
  intro n hn
  have h_dist : dist (u n) (u N) < 1/2 := hN n hn N (le_refl N)
  by_contra hne
  have h_eq : (dist (u n) (u N) : ℝ) = 1 := by
    change discreteDist (u n) (u N) = 1
    unfold discreteDist
    rw [if_neg hne]
  rw [h_eq] at h_dist
  linarith

/-- **`CompleteSpace` instance.** Every Cauchy sequence in the discrete
metric on `SBoundedProcess` is eventually constant and hence converges
to that constant value.

We use `complete_of_cauchySeq_tendsto`: a uniform space with countable
basis of the uniformity (automatic for metric spaces) is complete iff
every Cauchy *sequence* converges. The discrete metric makes every Cauchy
sequence eventually constant (by `cauchySeq_eventually_constant`), and an
eventually-constant sequence converges to its eventual value. -/
noncomputable instance instCompleteSpaceSBoundedProcess :
    CompleteSpace (SBoundedProcess (n := n) P T) := by
  apply UniformSpace.complete_of_cauchySeq_tendsto
  intro u hu
  obtain ⟨N, hN⟩ := cauchySeq_eventually_constant u hu
  refine ⟨u N, ?_⟩
  rw [Metric.tendsto_atTop]
  intro ε hε
  refine ⟨N, fun n hn => ?_⟩
  rw [hN n hn, dist_self]
  exact hε

end DiscreteMetric

end LevyStochCalc.Ito.Picard
