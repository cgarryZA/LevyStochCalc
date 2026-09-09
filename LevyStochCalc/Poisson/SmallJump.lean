/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.Compensated

/-!
# The compensated integral over a shrinking family of marks

Restricting an admissible integrand to a measurable set of marks keeps it admissible, and by the
Itô–Lévy isometry the `L²` size of its compensated integral is the energy carried by that set.
Along an antitone family of mark sets whose intersection is null, that energy vanishes by
dominated convergence on the intensity, so the compensated integrals tend to `0` in `L²`.

## Main statements

* `LevyStochCalc.Poisson.Compensated.markCut` — an integrand restricted to a set of marks.
* `LevyStochCalc.Poisson.Compensated.tendsto_lintegral_sq_stochasticIntegral_markCut` — the
  compensated integrals over a shrinking family of marks tend to `0` in `L²`.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Cut

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- An integrand restricted to a measurable set of marks. -/
noncomputable def markCut (A : Set E) (φ : Ω → ℝ → E → ℝ) : Ω → ℝ → E → ℝ :=
  fun ω s e => A.indicator (fun _ => φ ω s e) e

omit [MeasurableSpace Ω] [MeasurableSpace E] in
@[simp] theorem markCut_apply (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    markCut A φ ω s e = A.indicator (fun _ => φ ω s e) e := rfl

theorem measurable_markCut {φ : Ω → ℝ → E → ℝ}
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) {A : Set E}
    (hA : MeasurableSet A) :
    Measurable fun p : Ω × ℝ × E => markCut A φ p.1 p.2.1 p.2.2 := by
  have hset : MeasurableSet {p : Ω × ℝ × E | p.2.2 ∈ A} := measurable_snd.snd hA
  have : (fun p : Ω × ℝ × E => markCut A φ p.1 p.2.1 p.2.2)
      = {p : Ω × ℝ × E | p.2.2 ∈ A}.indicator (fun p => φ p.1 p.2.1 p.2.2) := by
    funext p
    by_cases hp : p.2.2 ∈ A <;> simp [markCut, hp]
  rw [this]
  exact h_meas.indicator hset

omit [MeasurableSpace Ω] [MeasurableSpace E] in
theorem enorm_sq_markCut (A : Set E) (φ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    (‖markCut A φ ω s e‖₊ : ℝ≥0∞) ^ 2
      = A.indicator (fun _ => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2) e := by
  by_cases hp : e ∈ A <;> simp [markCut, hp]

theorem sq_markCut {φ : Ω → ℝ → E → ℝ}
    (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) (A : Set E) (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖markCut A φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  refine lt_of_le_of_lt ?_ (h_sq T hT)
  refine lintegral_mono fun ω => lintegral_mono fun s => lintegral_mono fun e => ?_
  rw [enorm_sq_markCut]
  exact Set.indicator_le_self' (fun _ _ => zero_le) e

/-- The energy of a jointly measurable nonnegative kernel is measurable in the sample point. -/
theorem measurable_markEnergy {f : Ω → ℝ → E → ℝ≥0∞}
    (hf : Measurable fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, f ω s e ∂ν ∂volume := by
  have hcurry : Measurable fun q : (Ω × ℝ) × E => f q.1.1 q.1.2 q.2 :=
    hf.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have h1 : Measurable fun p : Ω × ℝ => ∫⁻ e, f p.1 p.2 e ∂ν :=
    Measurable.lintegral_prod_right' (f := fun q : (Ω × ℝ) × E => f q.1.1 q.1.2 q.2) hcurry
  exact Measurable.lintegral_prod_right'
    (ν := volume.restrict (Set.Icc (0 : ℝ) T)) (f := fun q : Ω × ℝ => ∫⁻ e, f q.1 q.2 e ∂ν) h1

end Cut

section Tendsto

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

omit [IsProbabilityMeasure P] in
/-- The energy carried by a set of marks, with the mark integral outermost. -/
theorem lintegral_markCut_eq_setLIntegral {A : Set E} (hA : MeasurableSet A)
    (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2) (T : ℝ) (ω : Ω) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖markCut A φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume
      = ∫⁻ e in A, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν := by
  have hcut : Measurable fun q : ℝ × E => (‖markCut A φ ω q.1 q.2‖₊ : ℝ≥0∞) ^ 2 := by
    have := (measurable_markCut h_meas hA).comp
      (measurable_const.prodMk (measurable_fst.prodMk measurable_snd) :
        Measurable fun q : ℝ × E => ((ω, q.1, q.2) : Ω × ℝ × E))
    exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
  rw [lintegral_lintegral_swap hcut.aemeasurable, ← lintegral_indicator hA]
  refine lintegral_congr fun e => ?_
  by_cases he : e ∈ A
  · simp only [Set.indicator_of_mem he]
    exact lintegral_congr fun s => by simp [markCut, he]
  · simp only [Set.indicator_of_notMem he]
    exact (lintegral_congr fun s => by simp [markCut, he]).trans lintegral_zero

include hℱ in
/-- **The compensated integrals over a shrinking family of marks tend to `0` in `L²`.** -/
theorem tendsto_lintegral_sq_stochasticIntegral_markCut
    (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m)) (hanti : Antitone A)
    (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    Filter.Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m) φ)
        (measurable_markCut h_meas (hA m)) (h_progMeas.indicator_mark (hA m))
        (fun T' hT' => sq_markCut h_sq (A m) T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      Filter.atTop (𝓝 0) := by
  classical
  set G : Ω → E → ℝ≥0∞ :=
    fun ω e => ∫⁻ s in Set.Icc (0 : ℝ) T, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂volume with hGdef
  -- each term is the energy carried by `A m`
  have hiso : ∀ m, ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m) φ)
        (measurable_markCut h_meas (hA m)) (h_progMeas.indicator_mark (hA m))
        (fun T' hT' => sq_markCut h_sq (A m) T' hT') T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e in A m, G ω e ∂ν ∂P := by
    intro m
    rw [isometry_stochasticIntegral N ℱ hℱ (markCut (A m) φ)
      (measurable_markCut h_meas (hA m)) (h_progMeas.indicator_mark (hA m))
      (fun T' hT' => sq_markCut h_sq (A m) T' hT') T hT]
    exact lintegral_congr fun ω =>
      lintegral_markCut_eq_setLIntegral φ (hA m) h_meas T ω
  simp_rw [hiso]
  -- the total energy, as a function of the sample point
  have htot : ∀ ω : Ω, ∫⁻ e, G ω e ∂ν
      = ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
    intro ω
    have := lintegral_markCut_eq_setLIntegral (ν := ν) φ MeasurableSet.univ h_meas T ω
    simpa [markCut] using this.symm
  have htotmeas : Measurable fun ω => ∫⁻ e, G ω e ∂ν := by
    simp_rw [htot]
    exact measurable_markEnergy (f := fun ω s e => (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2)
      ((h_meas.nnnorm.coe_nnreal_ennreal).pow_const 2) T
  have htotfin : ∫⁻ ω, (∫⁻ e, G ω e ∂ν) ∂P ≠ ⊤ := by
    simp_rw [htot]
    exact (h_sq T hT).ne
  -- for almost every sample point the mark energy is finite, so the shrinking sets carry none
  have hGmeas : ∀ ω : Ω, Measurable (G ω) := by
    intro ω
    have hcurry : Measurable fun q : E × ℝ => (‖φ ω q.2 q.1‖₊ : ℝ≥0∞) ^ 2 := by
      have := h_meas.comp (measurable_const.prodMk
        (measurable_snd.prodMk measurable_fst) :
          Measurable fun q : E × ℝ => ((ω, q.2, q.1) : Ω × ℝ × E))
      exact (this.nnnorm.coe_nnreal_ennreal).pow_const 2
    exact Measurable.lintegral_prod_right'
      (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hcurry
  have hindic : ∀ (m : ℕ) (ω : Ω), ∫⁻ e, (A m).indicator (G ω) e ∂ν = ∫⁻ e in A m, G ω e ∂ν :=
    fun m ω => lintegral_indicator (hA m) _
  have hae : ∀ᵐ ω ∂P, Filter.Tendsto (fun m => ∫⁻ e in A m, G ω e ∂ν) Filter.atTop (𝓝 0) := by
    filter_upwards [MeasureTheory.ae_lt_top htotmeas htotfin] with ω hfin
    have hbound : ∀ m, (fun e => (A m).indicator (G ω) e) ≤ᵐ[ν] G ω :=
      fun m => Filter.Eventually.of_forall fun e =>
        Set.indicator_le_self' (fun _ _ => zero_le) e
    have hmeasF : ∀ m, Measurable fun e => (A m).indicator (G ω) e :=
      fun m => (hGmeas ω).indicator (hA m)
    have hlim : ∀ᵐ e ∂ν, Filter.Tendsto
        (fun m => (A m).indicator (G ω) e) Filter.atTop
        (𝓝 ((⋂ m, A m).indicator (G ω) e)) := by
      refine Filter.Eventually.of_forall fun e => ?_
      by_cases he : e ∈ ⋂ m, A m
      · have hall : ∀ m, e ∈ A m := fun m => Set.mem_iInter.mp he m
        simp only [Set.indicator_of_mem he, Set.indicator_of_mem (hall _)]
        exact tendsto_const_nhds
      · obtain ⟨m₀, hm₀⟩ : ∃ m₀, e ∉ A m₀ := by
          by_contra hcon
          push_neg at hcon
          exact he (Set.mem_iInter.mpr fun m => hcon m)
        refine tendsto_atTop_of_eventually_const (i₀ := m₀) fun m hm => ?_
        rw [Set.indicator_of_notMem (fun hmem => hm₀ (hanti hm hmem)),
          Set.indicator_of_notMem he]
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (F := fun m e => (A m).indicator (G ω) e)
      (f := (⋂ m, A m).indicator (G ω)) (bound := G ω) hmeasF hbound hfin.ne hlim
    rw [lintegral_indicator (MeasurableSet.iInter hA),
      MeasureTheory.setLIntegral_measure_zero _ _ hnull] at hconv
    simpa only [hindic] using hconv
  -- dominated convergence in the sample point
  have hmeasFm : ∀ m, Measurable fun ω => ∫⁻ e in A m, G ω e ∂ν := by
    intro m
    have hrw : (fun ω => ∫⁻ e in A m, G ω e ∂ν)
        = fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖markCut (A m) φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
      funext ω
      exact (lintegral_markCut_eq_setLIntegral φ (hA m) h_meas T ω).symm
    rw [hrw]
    exact measurable_markEnergy
      (f := fun ω s e => (‖markCut (A m) φ ω s e‖₊ : ℝ≥0∞) ^ 2)
      (((measurable_markCut h_meas (hA m)).nnnorm.coe_nnreal_ennreal).pow_const 2) T
  have hboundP : ∀ m, (fun ω => ∫⁻ e in A m, G ω e ∂ν) ≤ᵐ[P] fun ω => ∫⁻ e, G ω e ∂ν :=
    fun m => Filter.Eventually.of_forall fun ω =>
      MeasureTheory.setLIntegral_le_lintegral _ _
  have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (F := fun m ω => ∫⁻ e in A m, G ω e ∂ν) (f := fun _ : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ∫⁻ e, G ω e ∂ν) hmeasFm hboundP htotfin hae
  simpa using hconv

end Tendsto

end LevyStochCalc.Poisson.Compensated
