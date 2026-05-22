/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.Martingale

/-!
# Layer 1.5d: d-dimensional Brownian motion

A `d`-dimensional Brownian motion is a `Fin d`-tuple of independent 1-D
Brownian motions on the same probability space. Constructed via
`Probability.Independence.InfinitePi`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.1.
* User's dissertation, ch02 §"Probability-space prerequisites", line 13
  (defines `d`-dim standard Brownian motion).

## Status

Phase 2 spec: `components_independent` wired to `iIndepFun`.

Phase (a): existence theorem proved via `Measure.pi` (finite product of
probability spaces) + `iIndepFun_pi` (independence of coordinate evaluations
on a product measure). Internal proofs of structure-field preservation
under projection are intermediate `sorry`s (each follows from a Mathlib API
call but the boilerplate is non-trivial).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A `d`-dimensional Brownian motion: a `Fin d`-tuple of independent
1-dimensional Brownian motions on the same probability space. -/
structure MultidimBrownianMotion (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) where
  /-- The component-wise Brownian motions. -/
  W : Fin d → LevyStochCalc.Brownian.BrownianMotion P
  /-- The components are mutually independent — each component, viewed as a
  random variable into the path space `ℝ → ℝ` (with the product measurable
  structure), is jointly independent across `i : Fin d`. -/
  components_independent :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin d) (ω : Ω) (t : ℝ) => (W i).W t ω) P

/-- σ-algebra-level `Indep` lifts through a measure-preserving map.
Given `Indep m₁ m₂ μ_b` with `m₁, m₂ ≤ mβ` and `MeasurePreserving h μ_a μ_b`,
the comap σ-algebras `m₁.comap h, m₂.comap h` are independent under `μ_a`. -/
private lemma indep_compMeasurePreserving
    {α β : Type*} [mα : MeasurableSpace α] [mβ : MeasurableSpace β]
    {μ_a : Measure α} {μ_b : Measure β}
    {h : α → β} (hmp : MeasureTheory.MeasurePreserving h μ_a μ_b)
    {m₁ m₂ : MeasurableSpace β}
    (hm₁_le : m₁ ≤ mβ) (hm₂_le : m₂ ≤ mβ)
    (hindep : ProbabilityTheory.Indep m₁ m₂ μ_b) :
    ProbabilityTheory.Indep (m₁.comap h) (m₂.comap h) μ_a := by
  have h_aux : ∀ s : Set β, @MeasurableSet β mβ s → μ_a (h ⁻¹' s) = μ_b s := by
    intro s hs
    refine @MeasureTheory.MeasurePreserving.measure_preimage α β mα mβ μ_a μ_b h hmp s ?_
    refine @MeasurableSet.nullMeasurableSet β mβ μ_b s ?_
    exact hs
  rw [ProbabilityTheory.Indep_iff]
  intro u v hu hv
  obtain ⟨u', hu'_meas, rfl⟩ := hu
  obtain ⟨v', hv'_meas, rfl⟩ := hv
  have hu'_full : @MeasurableSet β mβ u' := hm₁_le _ hu'_meas
  have hv'_full : @MeasurableSet β mβ v' := hm₂_le _ hv'_meas
  rw [show (h ⁻¹' u') ∩ (h ⁻¹' v') = h ⁻¹' (u' ∩ v') from rfl]
  rw [h_aux _ (@MeasurableSet.inter β mβ _ _ hu'_full hv'_full),
      h_aux _ hu'_full, h_aux _ hv'_full]
  rw [ProbabilityTheory.Indep_iff] at hindep
  exact hindep u' v' hu'_meas hv'_meas

/-- `IndepFun` is preserved by pre-composition with a measure-preserving map.
This is a small helper Mathlib doesn't directly provide for this combination
of `IndepFun` (rather than `Indep` between σ-algebras) and `MeasurePreserving`. -/
private lemma indepFun_compMeasurePreserving
    {α β γ δ : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    [mγ : MeasurableSpace γ] [mδ : MeasurableSpace δ]
    {μa : Measure α} {μb : Measure β}
    {f : β → γ} {g : β → δ}
    {h : α → β}
    (hf : Measurable f) (hg : Measurable g)
    (hindep : ProbabilityTheory.IndepFun f g μb)
    (hmp : MeasureTheory.MeasurePreserving h μa μb) :
    ProbabilityTheory.IndepFun (f ∘ h) (g ∘ h) μa := by
  rw [ProbabilityTheory.IndepFun_iff]
  intro t1 t2 ht1 ht2
  rcases ht1 with ⟨s1, hs1, rfl⟩
  rcases ht2 with ⟨s2, hs2, rfl⟩
  -- s1 : Set γ; t1 = (f ∘ h) ⁻¹' s1 = h ⁻¹' (f ⁻¹' s1).
  have hfs1 : MeasurableSet (f ⁻¹' s1) := hf hs1
  have hgs2 : MeasurableSet (g ⁻¹' s2) := hg hs2
  have hint : MeasurableSet (f ⁻¹' s1 ∩ g ⁻¹' s2) := hfs1.inter hgs2
  -- (f ∘ h) ⁻¹' s = h ⁻¹' (f ⁻¹' s) — the goal rewrites cleanly via these
  -- and measure-preservation.
  change μa (h ⁻¹' (f ⁻¹' s1) ∩ h ⁻¹' (g ⁻¹' s2))
    = μa (h ⁻¹' (f ⁻¹' s1)) * μa (h ⁻¹' (g ⁻¹' s2))
  rw [← Set.preimage_inter,
      hmp.measure_preimage hint.nullMeasurableSet,
      hmp.measure_preimage hfs1.nullMeasurableSet,
      hmp.measure_preimage hgs2.nullMeasurableSet]
  -- Now: μb (f ⁻¹' s1 ∩ g ⁻¹' s2) = μb (f ⁻¹' s1) * μb (g ⁻¹' s2)
  -- This is exactly the IndepFun characterization with t = f ⁻¹' s, etc.
  exact (ProbabilityTheory.IndepFun_iff _ _ _).mp hindep _ _
    ⟨s1, hs1, rfl⟩ ⟨s2, hs2, rfl⟩

/-- Lift a 1-dimensional Brownian motion `W₀` on `(Ω₀, P₀)` to a 1-D BM on the
product space `(Fin d → Ω₀, Measure.pi)` along the `i`-th coordinate. -/
private noncomputable def project_BM
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    (W₀ : LevyStochCalc.Brownian.BrownianMotion P₀)
    (d : ℕ) (i : Fin d) :
    @LevyStochCalc.Brownian.BrownianMotion (Fin d → Ω₀) MeasurableSpace.pi
      (MeasureTheory.Measure.pi (fun _ => P₀))
      (by infer_instance) where
  W := fun t (ω : Fin d → Ω₀) => W₀.W t (ω i)
  measurable_eval := fun t =>
    (W₀.measurable_eval t).comp (measurable_pi_apply i)
  joint_measurable := by
    -- Joint measurability inherits from 1D BM's joint measurability via
    -- the measurable evaluation map at coordinate i.
    have h₀ := W₀.joint_measurable
    -- Function.uncurry (fun t ω => W₀.W t (ω i)) = (fun p => W₀.W p.1 (p.2 i))
    -- = h₀ ∘ (fun p => (p.1, p.2 i))
    have h_eval_meas : Measurable (fun (p : ℝ × (Fin d → Ω₀)) => (p.1, p.2 i)) := by
      refine Measurable.prodMk (measurable_fst) ?_
      exact (measurable_pi_apply i).comp measurable_snd
    exact h₀.comp h_eval_meas
  initial_zero := by
    -- W₀.initial_zero : ∀ᵐ ω₀ ∂P₀, W₀.W 0 ω₀ = 0; lift via measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.initial_zero
  increment_gaussian := by
    intro s t hs hst
    -- Pushforward through eval_i preserves the Gaussian increment law.
    have h_eval : (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)).map
        (Function.eval i) = P₀ :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin d => P₀) i).map_eq
    have h_inc := W₀.increment_gaussian hs hst
    rw [show (fun ω : Fin d → Ω₀ => W₀.W t (ω i) - W₀.W s (ω i))
        = (fun ω₀ : Ω₀ => W₀.W t ω₀ - W₀.W s ω₀) ∘ Function.eval i from rfl,
      ← MeasureTheory.Measure.map_map
        ((W₀.measurable_eval t).sub (W₀.measurable_eval s))
        (measurable_pi_apply i),
      h_eval]
    exact h_inc
  increment_independent := by
    intro u s t hu hus hst
    -- IndepFun on Ω₀ lifts to IndepFun on the product through eval_i,
    -- via our `indepFun_compMeasurePreserving` helper.
    exact indepFun_compMeasurePreserving
      (W₀.measurable_eval u)
      ((W₀.measurable_eval t).sub (W₀.measurable_eval s))
      (W₀.increment_independent hu hus hst)
      (MeasureTheory.measurePreserving_eval (fun _ : Fin d => P₀) i)
  continuous_paths := by
    -- W₀.continuous_paths lifts via measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.continuous_paths
  negative_zero := by
    -- W₀.negative_zero lifts via measure-preserving eval i.
    intro s hs
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae (W₀.negative_zero s hs)
  joint_increment_independent := by
    -- W₀.joint_increment_independent + indep_compMeasurePreserving.
    intro s t hs hst
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    have h_inc_comap :
        MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W t (ω i) - W₀.W s (ω i)) inferInstance
        = (MeasurableSpace.comap (fun ω => W₀.W t ω - W₀.W s ω) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    have h_past_comap :
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W j (ω i)) inferInstance)
        = (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W₀.W j) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun j => ?_)
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun _ => ?_)
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [h_past_comap, h_inc_comap]
    apply indep_compMeasurePreserving mp
    · -- past σ-algebra ≤ ambient
      refine iSup₂_le ?_
      intro j _ u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact (W₀.measurable_eval j) hv
    · -- increment σ-algebra ≤ ambient
      intro u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact ((W₀.measurable_eval t).sub (W₀.measurable_eval s)) hv
    · exact W₀.joint_increment_independent hs hst

/-- **Existence of d-dimensional Brownian motion.** For any `d ≥ 0`, there
exists a probability space carrying a `d`-dimensional Brownian motion.

Proof: take `d` independent copies of the construction from
`LevyStochCalc.Brownian.BrownianMotion.exists`, joined via the product
probability space. -/
theorem MultidimBrownianMotion.exists (d : ℕ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (MultidimBrownianMotion P d) := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, ⟨W₀⟩⟩ := LevyStochCalc.Brownian.BrownianMotion.exists
  refine ⟨Fin d → Ω₀, MeasurableSpace.pi,
    MeasureTheory.Measure.pi (fun _ => P₀), inferInstance, ?_⟩
  refine ⟨{
    W := fun i => project_BM W₀ d i
    components_independent := ?_
  }⟩
  -- Components are independent: use ProbabilityTheory.iIndepFun_pi
  -- with X_i = (fun ω : Ω₀ => fun t => W₀.W t ω) for each i.
  have h_meas_W₀ : ∀ _ : Fin d,
      AEMeasurable (fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀) P₀ := by
    intro _
    -- Function into ℝ → ℝ is measurable iff each evaluation is measurable.
    refine (measurable_pi_iff.mpr ?_).aemeasurable
    intro t
    exact W₀.measurable_eval t
  have := ProbabilityTheory.iIndepFun_pi (X := fun _ : Fin d => fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀)
    (μ := fun _ : Fin d => P₀) h_meas_W₀
  convert this using 1

end LevyStochCalc.Brownian.Multidim
