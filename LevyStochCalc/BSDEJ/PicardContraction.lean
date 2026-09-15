/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardItoLevy
import LevyStochCalc.BSDEJ.YoungLipschitz
import LevyStochCalc.Ito.SecondMomentBackward
import LevyStochCalc.Ito.StabilityEstimate
import LevyStochCalc.Driver.AugJointUsualConditions
import LevyStochCalc.BSDEJ.SupBound

/-!
# The exponentially weighted norm of a triple and the Picard contraction

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.wNorm` — the exponentially weighted norm of a triple.
* `LevyStochCalc.BSDEJ.Solves.density` — the pointwise energy density of a triple.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput_of_two_le` — the weighted norm of
  the difference of two Picard outputs is at most `6 L² / β` times that of the difference of
  the inputs, at every Young weight `β ≥ 2`.
* `LevyStochCalc.BSDEJ.Solves.wNorm_sub_le_of_picardOutput` — the same with the factor `1/4`,
  at the Young weight `β = max 2 (24 L²)`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

section Norm

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {d : ℕ}

/-- The pointwise energy density of a triple `(Y, Z, U)`: the squared value, the sum of the
squared diffusion coordinates and the marked energy of the jump integrand. -/
noncomputable def density (ν : Measure E) (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ))
    (U : ℝ → Ω → E → ℝ) (ω : Ω) (s : ℝ) : ℝ≥0∞ :=
  (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 + ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν

/-- The exponentially weighted `L²` norm of a triple `(Y, Z, U)` over the horizon `[0, T]`, with
weight `e^{βs}`. -/
noncomputable def wNorm (P : Measure Ω) (ν : Measure E) (β T : ℝ) (Y : ℝ → Ω → ℝ)
    (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : ℝ≥0∞ :=
  ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (β * s)) *
    ((‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2
      + ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume ∂P

variable {P : Measure Ω} {ν : Measure E} {β T : ℝ}

/-- The weighted norm is the weighted integral of the pointwise energy density. -/
theorem wNorm_eq_lintegral_density {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} :
    wNorm P ν β T Y Z U = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      ENNReal.ofReal (Real.exp (β * s)) * density ν Y Z U ω s ∂volume ∂P := rfl

/-- Triples agreeing on the horizon have the same weighted norm. -/
theorem wNorm_congr_Icc {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    {U₁ U₂ : ℝ → Ω → E → ℝ} (hY : ∀ s ∈ Set.Icc (0 : ℝ) T, Y₁ s = Y₂ s)
    (hZ : ∀ s ∈ Set.Icc (0 : ℝ) T, Z₁ s = Z₂ s) (hU : ∀ s ∈ Set.Icc (0 : ℝ) T, U₁ s = U₂ s) :
    wNorm P ν β T Y₁ Z₁ U₁ = wNorm P ν β T Y₂ Z₂ U₂ := by
  refine lintegral_congr fun ω => ?_
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [hY s hs, hZ s hs, hU s hs]

/-- Freezing the two value processes at the horizon does not change the weighted norm of the
difference of two triples. -/
theorem wNorm_clampT_sub_eq {Y₁ Y₂ : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} :
    wNorm P ν β T (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω) Z U
      = wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) Z U :=
  wNorm_congr_Icc (fun s hs => by simp only [clampT_apply, min_eq_left hs.2])
    (fun _ _ => rfl) (fun _ _ => rfl)

variable [SigmaFinite ν]

/-- The squared value of a process, jointly in the sample point and the time. -/
theorem measurable_uncurry_sq_value {Y : ℝ → Ω → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω)) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2) :=
  hYm.nnnorm.coe_nnreal_ennreal.pow_const 2

/-- The marked energy density of a jump integrand, jointly in the sample point and the time. -/
theorem measurable_uncurry_sq_jump {U : ℝ → Ω → E → ℝ}
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) :=
  ((hUm.nnnorm.coe_nnreal_ennreal.pow_const 2).comp (by fun_prop :
    Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E))).lintegral_prod_right'
      (ν := ν)

/-- The pointwise energy density of a triple, jointly in the sample point and the time. -/
theorem measurable_uncurry_density {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Measurable (Function.uncurry (density ν Y Z U)) :=
  ((measurable_uncurry_sq_value hYm).add
    (Finset.measurable_sum _ fun j _ => measurable_uncurry_sq_value (hZm j))).add
      (measurable_uncurry_sq_jump hUm)

/-- The sample energy density of a triple is measurable in time. -/
theorem measurable_lintegral_density [SFinite P] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    Measurable fun s : ℝ => ∫⁻ ω, density ν Y Z U ω s ∂P :=
  Measurable.lintegral_prod_left' (measurable_uncurry_density hYm hZm hUm)

omit [SigmaFinite ν] in
/-- At each time, the sample energy density splits into the energy of the value, the energies of
the diffusion coordinates and the marked energy of the jump integrand. -/
theorem lintegral_density_slice_eq {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) (s : ℝ) :
    ∫⁻ ω, density ν Y Z U ω s ∂P
      = (∫⁻ ω, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂P) + (∑ j, ∫⁻ ω, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P)
        + ∫⁻ ω, ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P := by
  classical
  have hA : Measurable fun ω : Ω => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_uncurry_sq_value hYm).comp (measurable_id.prodMk measurable_const)
  have hB : ∀ j : Fin d, Measurable fun ω : Ω => (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 := fun j =>
    (measurable_uncurry_sq_value (hZm j)).comp (measurable_id.prodMk measurable_const)
  have h12 : Measurable fun ω : Ω => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
    hA.add (Finset.measurable_sum _ fun j _ => hB j)
  simp only [density]
  rw [lintegral_add_left h12, lintegral_add_left hA, lintegral_finsetSum _ fun j _ => hB j]

omit [SigmaFinite ν] in
/-- The energy of the pointwise density of a triple is the sum of the energy of the value, of
the energies of the diffusion coordinates and of the marked energy of the jump integrand. -/
theorem lintegral_density_eq [SFinite P] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P
      = Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) := by
  classical
  have hA := measurable_uncurry_sq_value hYm
  have hB : ∀ j : Fin d, Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) := fun j => measurable_uncurry_sq_value (hZm j)
  have hA' : ∀ ω : Ω, Measurable fun s : ℝ => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    hA.comp (measurable_const.prodMk measurable_id)
  have hB' : ∀ (j : Fin d) (ω : Ω), Measurable fun s : ℝ => (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
    fun j ω => (hB j).comp (measurable_const.prodMk measurable_id)
  have hinner : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume
      = (∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + (∑ j, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume)
        + ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ∂volume := by
    intro ω
    have h12 : Measurable fun s : ℝ =>
        (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 + ∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 :=
      (hA' ω).add (Finset.measurable_sum _ fun j _ => hB' j ω)
    simp only [density]
    rw [lintegral_add_left h12, lintegral_add_left (hA' ω),
      lintegral_finsetSum _ fun j _ => hB' j ω]
  have hoA : Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume := hA.lintegral_prod_right'
  have hoB : ∀ j : Fin d, Measurable fun ω : Ω =>
      ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun j => (hB j).lintegral_prod_right'
  have ho12 : Measurable fun ω : Ω => (∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume)
      + ∑ j, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    hoA.add (Finset.measurable_sum _ fun j _ => hoB j)
  rw [lintegral_congr hinner, lintegral_add_left ho12, lintegral_add_left hoA,
    lintegral_finsetSum _ fun j _ => hoB j]
  rfl

omit [SigmaFinite ν] in
/-- The weighted norm of a triple whose value, diffusion coordinates and jump integrand have
finite energy on the horizon is finite. -/
theorem wNorm_ne_top_of_energies [SFinite P] (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZ : ∀ j, Brownian.Ito.energy P T (fun ω s => Z s ω j) ≠ ⊤)
    (hU : Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    wNorm P ν β T Y Z U ≠ ⊤ := by
  classical
  have hbound : wNorm P ν β T Y Z U
      ≤ ENNReal.ofReal (Real.exp (β * T)) * (Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)) := by
    rw [wNorm_eq_lintegral_density, ← lintegral_density_eq hYm hZm,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun ω => ?_
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hs.2 hβ))) le_rfl
  refine ne_top_of_le_ne_top ?_ hbound
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.add_ne_top.mpr ⟨hY,
      (ENNReal.sum_ne_top).2 fun j _ => hZ j⟩, hU⟩)

/-- The weighted norm, with the time integral outside. -/
theorem wNorm_eq_setLIntegral [SFinite P] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) :
    wNorm P ν β T Y Z U = ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (β * s))
      * (∫⁻ ω, density ν Y Z U ω s ∂P) ∂volume := by
  have hm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ENNReal.ofReal (Real.exp (β * s)) * density ν Y Z U ω s) := by
    refine Measurable.mul ?_ (measurable_uncurry_density hYm hZm hUm)
    exact (ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_snd)))
  rw [wNorm_eq_lintegral_density, lintegral_lintegral_swap (μ := P)
    (ν := volume.restrict (Set.Icc (0 : ℝ) T)) hm.aemeasurable]
  exact setLIntegral_congr_fun measurableSet_Icc fun s _ =>
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

omit [SigmaFinite ν] in
/-- The energy of the pointwise density on the horizon is finite when the weighted norm is. -/
theorem lintegral_density_ne_top_of_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P ≠ ⊤ := by
  refine ne_top_of_le_ne_top hfin ?_
  rw [wNorm_eq_lintegral_density]
  refine lintegral_mono fun ω => lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact Real.one_le_exp (mul_nonneg hβ hs.1)

/-- The sample energy at each time of a finite window energy is almost everywhere finite. -/
theorem ae_lintegral_ne_top [SFinite P] {F : Ω → ℝ → ℝ≥0∞}
    (hF : Measurable (Function.uncurry F))
    (hfin : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), (∫⁻ ω, F ω s ∂P) ≠ ⊤ := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, F ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, F ω s ∂P) ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      hF.aemeasurable
  rw [hswap] at hfin
  filter_upwards [ae_lt_top hF.lintegral_prod_left hfin] with s hs
  exact hs.ne

/-- The sample energy density of a triple of finite weighted norm is almost everywhere finite in
time. -/
theorem ae_lintegral_density_ne_top [SFinite P] (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), (∫⁻ ω, density ν Y Z U ω s ∂P) ≠ ⊤ := by
  have hswap : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P
      = ∫⁻ s in Set.Icc (0 : ℝ) T, (∫⁻ ω, density ν Y Z U ω s ∂P) ∂volume :=
    lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Icc (0 : ℝ) T))
      (measurable_uncurry_density hYm hZm hUm).aemeasurable
  have h := lintegral_density_ne_top_of_wNorm hβ hfin
  rw [hswap] at h
  filter_upwards [ae_lt_top (measurable_lintegral_density hYm hZm hUm) h] with s hs
  exact hs.ne

/-- The weighted sample energy density of a triple of finite weighted norm is integrable in
time on the horizon. -/
theorem integrableOn_exp_mul_toReal_density [IsProbabilityMeasure P] (hβ : 0 ≤ β)
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    IntegrableOn (fun s => Real.exp (β * s) * (∫⁻ ω, density ν Y Z U ω s ∂P).toReal)
      (Set.Icc (0 : ℝ) T) :=
  Ito.SecondMoment.integrableOn_exp_mul β
    (Ito.SecondMoment.integrableOn_toReal_lintegral (measurable_uncurry_density hYm hZm hUm)
      (lt_top_iff_ne_top.mpr (lintegral_density_ne_top_of_wNorm hβ hfin)))

omit [SigmaFinite ν] in
/-- A finite, integrable time density integrates to the same weighted total in `ℝ≥0∞` and in
`ℝ`. -/
theorem setLIntegral_exp_mul_eq_ofReal {G : ℝ → ℝ≥0∞}
    (hfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), G s ≠ ⊤)
    (hint : IntegrableOn (fun s => Real.exp (β * s) * (G s).toReal) (Set.Icc (0 : ℝ) T)) :
    ∫⁻ s in Set.Icc (0 : ℝ) T, ENNReal.ofReal (Real.exp (β * s)) * G s ∂volume
      = ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (G s).toReal) := by
  rw [ofReal_integral_eq_lintegral_ofReal hint
    (Eventually.of_forall fun s => by positivity)]
  refine lintegral_congr_ae ?_
  filter_upwards [hfin] with s hs
  rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal hs]

/-- A finite weighted norm, as a real integral of the weighted sample energy density. -/
theorem wNorm_eq_ofReal_setIntegral [IsProbabilityMeasure P] (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hfin : wNorm P ν β T Y Z U ≠ ⊤) :
    wNorm P ν β T Y Z U = ENNReal.ofReal (∫ s in Set.Icc (0 : ℝ) T,
      Real.exp (β * s) * (∫⁻ ω, density ν Y Z U ω s ∂P).toReal) := by
  rw [wNorm_eq_setLIntegral hYm hZm hUm]
  exact setLIntegral_exp_mul_eq_ofReal (ae_lintegral_density_ne_top hβ hYm hZm hUm hfin)
    (integrableOn_exp_mul_toReal_density hβ hYm hZm hUm hfin)

/-- At each time, the energy density of a triple is measurable in the sample point. -/
theorem measurable_density_slice {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2) (s : ℝ) :
    Measurable fun ω : Ω => density ν Y Z U ω s := by
  classical
  have hA : Measurable fun ω : Ω => (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 :=
    (measurable_uncurry_sq_value hYm).comp (measurable_id.prodMk measurable_const)
  have hB : ∀ j : Fin d, Measurable fun ω : Ω => (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2 := fun j =>
    (measurable_uncurry_sq_value (hZm j)).comp (measurable_id.prodMk measurable_const)
  have hC : Measurable fun ω : Ω => ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
    (measurable_uncurry_sq_jump hUm).comp (measurable_id.prodMk measurable_const)
  simp only [density]
  exact (hA.add (Finset.measurable_sum _ fun j _ => hB j)).add hC

omit [MeasurableSpace Ω] [SigmaFinite ν] in
/-- The real part of the energy density at a point where the marked energy is finite. -/
theorem toReal_density_apply {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    {ω : Ω} {s : ℝ} (hU : ∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ≠ ⊤) :
    (density ν Y Z U ω s).toReal
      = (Y s ω) ^ 2 + (∑ j, (Z s ω j) ^ 2) + (∫⁻ e, (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal := by
  classical
  have hsq : ∀ a : ℝ, ((‖a‖₊ : ℝ≥0∞) ^ 2).toReal = a ^ 2 := by
    intro a
    rw [← ENNReal.coe_pow, ENNReal.coe_toReal, NNReal.coe_pow, coe_nnnorm, Real.norm_eq_abs,
      sq_abs]
  have hfinA : ((‖Y s ω‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := by finiteness
  have hfinB : ∀ j : Fin d, ((‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := fun j => by finiteness
  have hfinS : (∑ j, (‖Z s ω j‖₊ : ℝ≥0∞) ^ 2) ≠ ⊤ := ENNReal.sum_ne_top.2 fun j _ => hfinB j
  rw [density, ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinA, hfinS⟩) hU,
    ENNReal.toReal_add hfinA hfinS, ENNReal.toReal_sum fun j _ => hfinB j]
  simp only [hsq]

end Norm

section Energies

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {T : ℝ}

/-- The energy of a process on a horizon is at most the length of the horizon times its `S²`
seminorm. -/
theorem energy_le_of_biSup {Y : ℝ → Ω → ℝ} :
    Brownian.Ito.energy P T (fun ω s => Y s ω)
      ≤ ENNReal.ofReal T * ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun ω => ?_
  have hb : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Y s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume
      ≤ ∫⁻ _s in Set.Icc (0 : ℝ) T,
          (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂volume := by
    refine lintegral_mono_ae ?_
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) s hs
  refine hb.trans ?_
  rw [setLIntegral_const, Real.volume_Icc, sub_zero]
  exact le_of_eq (mul_comm _ _)

/-- The energy of a difference of two processes is finite when both energies are. -/
theorem energy_sub_ne_top {H₁ H₂ : Ω → ℝ → ℝ} (hm₁ : Measurable (Function.uncurry H₁))
    (hm₂ : Measurable (Function.uncurry H₂)) (h₁ : Brownian.Ito.energy P T H₁ ≠ ⊤)
    (h₂ : Brownian.Ito.energy P T H₂ ≠ ⊤) :
    Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s) ≠ ⊤ := by
  have hA : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    hm₁.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hB : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    hm₂.nnnorm.coe_nnreal_ennreal.pow_const 2
  have hA' : ∀ ω : Ω, Measurable fun s : ℝ => (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 := fun ω =>
    hA.comp (measurable_const.prodMk measurable_id)
  have hstep : Brownian.Ito.energy P T (fun ω s => H₁ ω s - H₂ ω s)
      ≤ 2 * (Brownian.Ito.energy P T H₁ + Brownian.Ito.energy P T H₂) := by
    have hpt : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s - H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
            2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume ∂P :=
      lintegral_mono fun ω => lintegral_mono fun s =>
        Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _
    refine hpt.trans (le_of_eq ?_)
    have hin : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        2 * ((‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 + (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2) ∂volume
        = 2 * ((∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
          + ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) := by
      intro ω
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hA' ω)]
    have hoA : Measurable fun ω : Ω =>
        ∫⁻ s in Set.Icc (0 : ℝ) T, (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := hA.lintegral_prod_right'
    rw [lintegral_congr hin, lintegral_const_mul' _ _ (by norm_num),
      lintegral_add_left hoA]
    rfl
  exact ne_top_of_le_ne_top (by finiteness) hstep

/-- A drift vanishing off a horizon on which it has finite energy is square integrable on every
horizon. -/
theorem drift_sq_int_global {b : Ω → ℝ → ℝ}
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
  lt_of_le_of_lt (Brownian.Ito.energy_le_of_vanishing hbz T') (lt_top_iff_ne_top.mpr hbq)

/-- The negative of a drift vanishing off a horizon of finite energy is square integrable on
every horizon. -/
theorem neg_drift_sq_int_global {b : Ω → ℝ → ℝ}
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤) (T' : ℝ) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖-b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  simpa only [nnnorm_neg] using drift_sq_int_global hbz hbq T'

/-- Freezing a process at the horizon does not change its energy there. -/
theorem energy_clampT {Y : ℝ → Ω → ℝ} :
    Brownian.Ito.energy P T (fun ω s => clampT T Y s ω)
      = Brownian.Ito.energy P T (fun ω s => Y s ω) :=
  lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    simp only [clampT_apply, min_eq_left hs.2]

end Energies

section Pointwise

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  {β T : ℝ}

/-- At almost every time of the horizon, twice the pairing of a process against the difference
of two evaluations of a Lipschitz generator is at most `β / 2` times the second moment of the
process plus `6 L² / β` times the sample energy density of the differenced arguments. -/
theorem ae_two_mul_integral_mul_sub_le
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hβ : 0 < β) {X : ℝ → Ω → ℝ} {b₁ b₂ : Ω → ℝ → ℝ}
    {Y'₁ Y'₂ : ℝ → Ω → ℝ} {Z'₁ Z'₂ : ℝ → Ω → (Fin d → ℝ)} {U'₁ U'₂ : ℝ → Ω → E → ℝ}
    {ΔY : ℝ → Ω → ℝ} {ΔZ : ℝ → Ω → (Fin d → ℝ)} {ΔU : ℝ → Ω → E → ℝ}
    (hΔY : ∀ s ω, ΔY s ω = Y'₁ s ω - Y'₂ s ω)
    (hΔZ : ∀ s ω j, ΔZ s ω j = Z'₁ s ω j - Z'₂ s ω j)
    (hΔU : ∀ s ω e, ΔU s ω e = U'₁ s ω e - U'₂ s ω e)
    (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖X s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁m : Measurable (Function.uncurry b₁)) (hb₂m : Measurable (Function.uncurry b₂))
    (hbq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖b₁ ω s - b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    (hΔYm : Measurable (Function.uncurry fun ω s => ΔY s ω))
    (hΔZm : ∀ j, Measurable (Function.uncurry fun ω s => ΔZ s ω j))
    (hΔUm : Measurable fun p : Ω × ℝ × E => ΔU p.2.1 p.1 p.2.2)
    (hin : wNorm P ν β T ΔY ΔZ ΔU ≠ ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      2 * ∫ ω, X s ω * (b₁ ω s - b₂ ω s) ∂P
        ≤ β / 2 * (∫ ω, X s ω * X s ω ∂P)
          + 6 * L ^ 2 / β * (∫⁻ ω, density ν ΔY ΔZ ΔU ω s ∂P).toReal := by
  classical
  have hg₁ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      b₁ ω s = f s (Y'₁ s ω) (Z'₁ s ω) (U'₁ s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc (0 : ℝ) T))
        (ν := P)).quasiMeasurePreserving.ae hb₁)
  have hg₂ : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ ω ∂P,
      b₂ ω s = f s (Y'₂ s ω) (Z'₂ s ω) (U'₂ s ω) :=
    Measure.ae_ae_of_ae_prod
      ((Measure.measurePreserving_swap (μ := volume.restrict (Set.Icc (0 : ℝ) T))
        (ν := P)).quasiMeasurePreserving.ae hb₂)
  have hdens := ae_lintegral_density_ne_top hβ.le hΔYm hΔZm hΔUm hin
  have hX2 := Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => X s ω) hXm hXq
  have hb2 := Ito.SecondMoment.ae_memLp_two_eval (f := fun ω s => b₁ ω s - b₂ ω s)
    (hb₁m.sub hb₂m) hbq
  filter_upwards [hg₁, hg₂, hdens, hX2, hb2] with s hs₁ hs₂ hdf hXs hbs
  have hdm := measurable_density_slice (ν := ν) hΔYm hΔZm hΔUm s
  have hdω := ae_lt_top hdm hdf
  have hJ : ∀ᵐ ω ∂P, (∫⁻ e, (‖ΔU s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ≠ ⊤ := by
    filter_upwards [hdω] with ω hω
    simp only [density] at hω
    exact (ENNReal.add_ne_top.mp hω.ne).2
  have hptw : ∀ᵐ ω ∂P, 2 * (X s ω * (b₁ ω s - b₂ ω s))
      ≤ β / 2 * (X s ω * X s ω) + 6 * L ^ 2 / β * (density ν ΔY ΔZ ΔU ω s).toReal := by
    filter_upwards [hs₁, hs₂, hJ] with ω h1 h2 hJω
    have hueq : (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        = ∫⁻ e, (‖ΔU s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν :=
      lintegral_congr fun e => by rw [hΔU s ω e]
    have hu : (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ≠ ⊤ := by
      rw [hueq]; exact hJω
    have key := Contraction.two_mul_mul_generator_sub_le hβ hL hlip s (Y'₁ s ω) (Y'₂ s ω)
      (Z'₁ s ω) (Z'₂ s ω) (U'₁ s ω) (U'₂ s ω) hu (X s ω)
    have hsq2 : X s ω ^ 2 = X s ω * X s ω := pow_two _
    have hdens_eq : (density ν ΔY ΔZ ΔU ω s).toReal
        = (Y'₁ s ω - Y'₂ s ω) ^ 2 + (∑ j, (Z'₁ s ω j - Z'₂ s ω j) ^ 2)
          + (∫⁻ e, (‖U'₁ s ω e - U'₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν).toReal := by
      rw [toReal_density_apply hJω]
      simp only [hΔY, hΔZ, hΔU]
    rw [h1, h2, hdens_eq]
    linarith [key]
  have hint1 : Integrable (fun ω => 2 * (X s ω * (b₁ ω s - b₂ ω s))) P :=
    (hXs.integrable_mul hbs).const_mul 2
  have hintA : Integrable (fun ω => β / 2 * (X s ω * X s ω)) P :=
    (hXs.integrable_mul hXs).const_mul _
  have hintB : Integrable
      (fun ω => 6 * L ^ 2 / β * (density ν ΔY ΔZ ΔU ω s).toReal) P :=
    (integrable_toReal_of_lintegral_ne_top hdm.aemeasurable hdf).const_mul _
  have hmono := integral_mono_ae hint1 (hintA.add hintB) hptw
  simp only [Pi.add_apply] at hmono
  rw [integral_const_mul, integral_add hintA hintB, integral_const_mul, integral_const_mul,
    integral_toReal hdm.aemeasurable hdω] at hmono
  exact hmono

end Pointwise

section RealCore

/-- The real-variable core of the Picard contraction: a weighted energy dominated by the
weighted pairing, itself dominated by the Young combination, contracts by the factor `c`. -/
theorem contraction_real_core {A Gout Gin V : ℝ → ℝ} {β c T : ℝ} (hβ : 2 ≤ β)
    (hA0 : ∀ s, 0 ≤ A s)
    (hAint : IntegrableOn (fun s => Real.exp (β * s) * A s) (Set.Icc (0 : ℝ) T))
    (hGoutint : IntegrableOn (fun s => Real.exp (β * s) * Gout s) (Set.Icc (0 : ℝ) T))
    (hGinint : IntegrableOn (fun s => Real.exp (β * s) * Gin s) (Set.Icc (0 : ℝ) T))
    (hVint : IntegrableOn (fun s => Real.exp (β * s) * V s) (Set.Icc (0 : ℝ) T))
    (hL : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (Gout s + (β - 1) * A s)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * V s)
    (hpt : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), V s ≤ β / 2 * A s + c * Gin s) :
    ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gout s
      ≤ c * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gin s := by
  have hM0 : (0 : ℝ) ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s :=
    setIntegral_nonneg measurableSet_Icc fun s _ => mul_nonneg (Real.exp_nonneg _) (hA0 s)
  have h1 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (Gout s + (β - 1) * A s)
      = (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gout s)
        + (β - 1) * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s := by
    have hc1 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Real.exp (β * s) * (Gout s + (β - 1) * A s)
          = Real.exp (β * s) * Gout s + (β - 1) * (Real.exp (β * s) * A s) :=
      Eventually.of_forall fun s => by ring
    rw [integral_congr_ae hc1, integral_add hGoutint (hAint.const_mul (β - 1)),
      integral_const_mul]
  have hRHSint : IntegrableOn
      (fun s => Real.exp (β * s) * (β / 2 * A s + c * Gin s)) (Set.Icc (0 : ℝ) T) := by
    refine Integrable.congr ((hAint.const_mul (β / 2)).add (hGinint.const_mul c)) ?_
    filter_upwards with s
    simp only [Pi.add_apply]
    ring
  have h2 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * V s
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β / 2 * A s + c * Gin s) := by
    refine integral_mono_ae hVint hRHSint ?_
    filter_upwards [hpt] with s hs
    exact mul_le_mul_of_nonneg_left hs (Real.exp_nonneg _)
  have h3 : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (β / 2 * A s + c * Gin s)
      = β / 2 * (∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * A s)
        + c * ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * Gin s := by
    have hc3 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        Real.exp (β * s) * (β / 2 * A s + c * Gin s)
          = β / 2 * (Real.exp (β * s) * A s) + c * (Real.exp (β * s) * Gin s) :=
      Eventually.of_forall fun s => by ring
    rw [integral_congr_ae hc3, integral_add (hAint.const_mul (β / 2)) (hGinint.const_mul c),
      integral_const_mul, integral_const_mul]
  rw [h1] at hL
  have hfin := hL.trans (h2.trans_eq h3)
  nlinarith [hfin, mul_nonneg (by linarith : (0 : ℝ) ≤ β - 2) hM0]

end RealCore

section Contraction

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- **One Picard step contracts the weighted norm.** At a Young weight `β ≥ 2` the weighted
norm of the difference of two Picard outputs is at most `6 L² / β` times the weighted norm of
the difference of their input triples. -/
theorem wNorm_sub_le_of_picardOutput_of_two_le
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ}
    {Y'₁ Y₁ Y'₂ Y₂ : ℝ → Ω → ℝ} {Z'₁ Z₁ Z'₂ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    {U'₁ U₁ U'₂ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : PicardOutput D f ξ T Y'₁ Z'₁ U'₁ Y₁ Z₁ U₁)
    (h₂ : PicardOutput D f ξ T Y'₂ Z'₂ U'₂ Y₂ Z₂ U₂)
    (hY'm : Measurable (Function.uncurry fun ω s => Y'₁ s ω - Y'₂ s ω))
    (hZ'm : ∀ j, Measurable (Function.uncurry fun ω s => Z'₁ s ω j - Z'₂ s ω j))
    (hU'm : Measurable fun p : Ω × ℝ × E => U'₁ p.2.1 p.1 p.2.2 - U'₂ p.2.1 p.1 p.2.2)
    {b₁ b₂ : Ω → ℝ → ℝ} (hb₁m : Measurable (Function.uncurry b₁))
    (hb₁p : Probability.ProgressivelyMeasurable (augJoint D) b₁)
    (hb₁z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₁ ω s = 0)
    (hb₁q : Brownian.Ito.energy P T b₁ ≠ ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂m : Measurable (Function.uncurry b₂))
    (hb₂p : Probability.ProgressivelyMeasurable (augJoint D) b₂)
    (hb₂z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₂ ω s = 0)
    (hb₂q : Brownian.Ito.energy P T b₂ ≠ ⊤)
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    {β : ℝ} (hβ : 2 ≤ β)
    (hin : wNorm P ν β T (fun t ω => Y'₁ t ω - Y'₂ t ω) (fun t ω => Z'₁ t ω - Z'₂ t ω)
      (fun t ω e => U'₁ t ω e - U'₂ t ω e) ≠ ⊤) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
        (fun t ω e => U₁ t ω e - U₂ t ω e)
      ≤ ENNReal.ofReal (6 * L ^ 2 / β) * wNorm P ν β T (fun t ω => Y'₁ t ω - Y'₂ t ω)
        (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) := by
  classical
  have hβ0 : (0 : ℝ) < β := lt_of_lt_of_le (by norm_num) hβ
  -- measurability of the output triples
  have hCm₁ : Measurable (Function.uncurry fun ω s => clampT T Y₁ s ω) :=
    (measurable_uncurry_clampT h₁.Y_meas).comp (measurable_snd.prodMk measurable_fst)
  have hCm₂ : Measurable (Function.uncurry fun ω s => clampT T Y₂ s ω) :=
    (measurable_uncurry_clampT h₂.Y_meas).comp (measurable_snd.prodMk measurable_fst)
  have hXm : Measurable (Function.uncurry fun ω s => clampT T Y₁ s ω - clampT T Y₂ s ω) :=
    hCm₁.sub hCm₂
  have hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j) :=
    fun j => (h₁.Z_meas j).sub (h₂.Z_meas j)
  have hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2 :=
    h₁.U_meas.sub h₂.U_meas
  -- energies of the output triple
  have hEY₁ : Brownian.Ito.energy P T (fun ω s => clampT T Y₁ s ω) ≠ ⊤ := by
    rw [energy_clampT]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₁.Y_sup.ne) energy_le_of_biSup
  have hEY₂ : Brownian.Ito.energy P T (fun ω s => clampT T Y₂ s ω) ≠ ⊤ := by
    rw [energy_clampT]
    exact ne_top_of_le_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h₂.Y_sup.ne) energy_le_of_biSup
  have hEX : Brownian.Ito.energy P T
      (fun ω s => clampT T Y₁ s ω - clampT T Y₂ s ω) ≠ ⊤ :=
    energy_sub_ne_top hCm₁ hCm₂ hEY₁ hEY₂
  have hEZ : ∀ j, Brownian.Ito.energy P T (fun ω s => Z₁ s ω j - Z₂ s ω j) ≠ ⊤ :=
    fun j => energy_sub_ne_top (h₁.Z_meas j) (h₂.Z_meas j) (h₁.Z_sq j) (h₂.Z_sq j)
  have hEU : Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U₁ s ω e - U₂ s ω e) ≠ ⊤ :=
    (Ito.Stability.lintegral_sq_sub_marked_lt_top (φ := fun ω s e => U₁ s ω e)
      (ψ := fun ω s e => U₂ s ω e) h₁.U_meas h₂.U_meas
      (lt_top_iff_ne_top.mpr h₁.U_sq) (lt_top_iff_ne_top.mpr h₂.U_sq)).ne
  have hEb : Brownian.Ito.energy P T (fun ω s => b₁ ω s - b₂ ω s) ≠ ⊤ :=
    energy_sub_ne_top hb₁m hb₂m hb₁q hb₂q
  -- the differenced Itô–Lévy process
  have hI₁ := h₁.isItoLevyProcess_clampT hT hb₁m hb₁z hb₁q hb₁
  have hI₂ := h₂.isItoLevyProcess_clampT hT hb₂m hb₂z hb₂q hb₂
  have hd₁q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-b₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' _ => neg_drift_sq_int_global hb₁z hb₁q T'
  have hd₂q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' _ => neg_drift_sq_int_global hb₂z hb₂q T'
  have hXproc := Ito.Stability.isItoLevyProcess_sub hI₁ hI₂ hb₁m.neg hb₂m.neg hd₁q hd₂q
  -- the data of the backward weighted energy inequality
  have hX₀ : StronglyMeasurable[Brownian.augFiltration D.filtration P 0]
      (fun ω => Y₁ 0 ω - Y₂ 0 ω) :=
    (D.stronglyMeasurable_augFiltration_zero (h₁.Y_adapted 0).stronglyMeasurable).sub
      (D.stronglyMeasurable_augFiltration_zero (h₂.Y_adapted 0).stronglyMeasurable)
  have hmem : ∀ Y : ℝ → Ω → ℝ, Measurable (Function.uncurry Y) →
      (∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤) → MemLp (Y 0) 2 P := by
    intro Y hYm hsup
    refine Brownian.Ito.memLp_two_of_lintegral_sq_lt_top
      (hYm.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable ?_
    refine lt_of_le_of_lt (lintegral_mono fun ω => ?_) hsup
    exact le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) => (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) 0
      ⟨le_rfl, hT.le⟩
  have hX₀2 : MemLp (fun ω => Y₁ 0 ω - Y₂ 0 ω) 2 P :=
    (hmem Y₁ h₁.Y_meas h₁.Y_sup).sub (hmem Y₂ h₂.Y_meas h₂.Y_sup)
  have hbm' : Measurable (Function.uncurry fun ω s => -b₁ ω s - -b₂ ω s) :=
    hb₁m.neg.sub hb₂m.neg
  have hbp' : Probability.ProgressivelyMeasurable (Brownian.augFiltration D.filtration P)
      fun ω s => -b₁ ω s - -b₂ ω s :=
    (continuous_neg.comp_progressivelyMeasurable neg_zero hb₁p).sub
      (continuous_neg.comp_progressivelyMeasurable neg_zero hb₂p)
  have hbq' : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖-b₁ ω s - -b₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    Brownian.Ito.lintegral_energy_lt_top_of_bound (K := fun ω s => -b₁ ω s - -b₂ ω s)
      (H₁ := fun ω s => -b₁ ω s) (H₂ := fun ω s => -b₂ ω s)
      (fun ω s => Brownian.Ito.sq_nnnorm_sub_le_two_mul _ _) hb₁m.neg hb₂m.neg hd₁q hd₂q
  have hXT : (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω) T =ᵐ[P] 0 := by
    filter_upwards [h₁.Y_terminal, h₂.Y_terminal] with ω k1 k2
    simp only [clampT_apply, min_self, Pi.zero_apply]
    rw [k1, k2, sub_self]
  have hL15 := Ito.SecondMoment.weighted_energy_le_of_terminal_zero hXproc hX₀ hX₀2 hbm' hbp'
    hbq' β hT hXT
  -- the real integrands
  have hWout : wNorm P ν β T (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
      (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ≠ ⊤ :=
    wNorm_ne_top_of_energies (ν := ν) (Y := fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e)
      hβ0.le hXm hZm hEX hEZ hEU
  have hAint : IntegrableOn (fun s => Real.exp (β * s) * ∫ ω,
      (clampT T Y₁ s ω - clampT T Y₂ s ω) * (clampT T Y₁ s ω - clampT T Y₂ s ω) ∂P)
      (Set.Icc (0 : ℝ) T) :=
    Ito.SecondMoment.integrableOn_exp_mul β
      (Ito.SecondMoment.integrableOn_integral_mul_self hXproc D.crossWitness.aug hX₀ hX₀2
        hbm' hbp' hbq' hT)
  have hGoutint := integrableOn_exp_mul_toReal_density (ν := ν)
      (Y := fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e)
      hβ0.le hXm hZm hUm hWout
  have hGinint := integrableOn_exp_mul_toReal_density (ν := ν) (Y := fun t ω => Y'₁ t ω - Y'₂ t ω)
      (Z := fun t ω => Z'₁ t ω - Z'₂ t ω) (U := fun t ω e => U'₁ t ω e - U'₂ t ω e)
      hβ0.le hY'm hZ'm hU'm hin
  have hVint : IntegrableOn (fun s => Real.exp (β * s) * (2 * ∫ ω,
      (clampT T Y₁ s ω - clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P)) (Set.Icc (0 : ℝ) T) := by
    refine Ito.SecondMoment.integrableOn_exp_mul β ?_
    refine Integrable.congr ((Ito.SecondMoment.integrableOn_integral_mul_drift hXproc hX₀2
      hbm' hbp' hbq' hT).const_mul (-2)) ?_
    filter_upwards with s
    have hsw : ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P
        = -∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω) * (-b₁ ω s - -b₂ ω s) ∂P := by
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun ω => by ring)
    rw [hsw]; ring
  -- the pointwise Young bound
  have hpt := ae_two_mul_integral_mul_sub_le (ν := ν) (T := T) hL hlip hβ0
    (X := fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
    (ΔY := fun t ω => Y'₁ t ω - Y'₂ t ω) (ΔZ := fun t ω => Z'₁ t ω - Z'₂ t ω)
    (ΔU := fun t ω e => U'₁ t ω e - U'₂ t ω e)
    (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl) hXm
    (lt_top_iff_ne_top.mpr hEX) hb₁m hb₂m (lt_top_iff_ne_top.mpr hEb) hb₁ hb₂
    hY'm hZ'm hU'm hin
  -- the output density splits at almost every time
  have hXmem := Ito.SecondMoment.ae_memLp_two_eval
    (f := fun ω s => clampT T Y₁ s ω - clampT T Y₂ s ω) hXm (lt_top_iff_ne_top.mpr hEX)
  have hZfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      ∀ j : Fin d, (∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ :=
    ae_all_iff.mpr fun j => ae_lintegral_ne_top (measurable_uncurry_sq_value (hZm j)) (hEZ j)
  have hUfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (∫⁻ ω, ∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P) ≠ ⊤ :=
    ae_lintegral_ne_top (measurable_uncurry_sq_jump hUm) hEU
  have hGout : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      (∫⁻ ω, density ν (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
          (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal
        = (∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω)
              * (clampT T Y₁ s ω - clampT T Y₂ s ω) ∂P)
            + (∑ j, (∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal := by
    filter_upwards [hXmem, hZfin, hUfin] with s hXs hZs hUs
    have hfinA := (Ito.SecondMoment.lintegral_sq_lt_top_of_memLp_two hXs).ne
    have hfinS : (∑ j, ∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P) ≠ ⊤ :=
      ENNReal.sum_ne_top.2 fun j _ => hZs j
    rw [lintegral_density_slice_eq (ν := ν) (Y := fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e) hXm hZm s]
    simp only [Pi.sub_apply]
    rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hfinA, hfinS⟩) hUs,
      ENNReal.toReal_add hfinA hfinS, ENNReal.toReal_sum fun j _ => hZs j,
      ← Ito.SecondMoment.integral_mul_self_eq_toReal hXs]
  -- the backward inequality in the shape of the real core
  have hLconv : ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s)
        * ((∫⁻ ω, density ν (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
              (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal
          + (β - 1) * ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω)
              * (clampT T Y₁ s ω - clampT T Y₂ s ω) ∂P)
      ≤ ∫ s in Set.Icc (0 : ℝ) T, Real.exp (β * s) * (2 * ∫ ω,
          (clampT T Y₁ s ω - clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P) := by
    have e1 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Real.exp (β * s)
          * ((∫⁻ ω, density ν (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
                (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal
            + (β - 1) * ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω)
                * (clampT T Y₁ s ω - clampT T Y₂ s ω) ∂P)
        = Real.exp (β * s) * (β * ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω)
              * (clampT T Y₁ s ω - clampT T Y₂ s ω) ∂P
            + (∑ j, (∫⁻ ω, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2 ∂P).toReal)
          + (∫⁻ ω, ∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂P).toReal) := by
      filter_upwards [hGout] with s hs
      rw [hs]; ring
    have e2 : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), Real.exp (β * s) * (2 * ∫ ω,
          (clampT T Y₁ s ω - clampT T Y₂ s ω) * -(-b₁ ω s - -b₂ ω s) ∂P)
        = Real.exp (β * s) * (2 * ∫ ω,
          (clampT T Y₁ s ω - clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P) := by
      filter_upwards with s
      have : ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω) * -(-b₁ ω s - -b₂ ω s) ∂P
          = ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P :=
        integral_congr_ae (Eventually.of_forall fun ω => by ring)
      rw [this]
    rw [integral_congr_ae e1, ← integral_congr_ae e2]
    exact hL15
  have hcore := contraction_real_core (β := β) (c := 6 * L ^ 2 / β) (T := T)
    (A := fun s => ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω)
      * (clampT T Y₁ s ω - clampT T Y₂ s ω) ∂P)
    (Gout := fun s => (∫⁻ ω, density ν (fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
      (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e) ω s ∂P).toReal)
    (Gin := fun s => (∫⁻ ω, density ν (fun t ω => Y'₁ t ω - Y'₂ t ω)
      (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) ω s ∂P).toReal)
    (V := fun s => 2 * ∫ ω, (clampT T Y₁ s ω - clampT T Y₂ s ω) * (b₁ ω s - b₂ ω s) ∂P)
    hβ (fun s => integral_nonneg fun ω => mul_self_nonneg _) hAint hGoutint hGinint hVint
    hLconv hpt
  rw [← wNorm_clampT_sub_eq (Y₁ := Y₁) (Y₂ := Y₂),
    wNorm_eq_ofReal_setIntegral (ν := ν) (Y := fun t ω => clampT T Y₁ t ω - clampT T Y₂ t ω)
      (Z := fun t ω => Z₁ t ω - Z₂ t ω) (U := fun t ω e => U₁ t ω e - U₂ t ω e)
      hβ0.le hXm hZm hUm hWout,
    wNorm_eq_ofReal_setIntegral (ν := ν) (Y := fun t ω => Y'₁ t ω - Y'₂ t ω)
      (Z := fun t ω => Z'₁ t ω - Z'₂ t ω) (U := fun t ω e => U'₁ t ω e - U'₂ t ω e)
      hβ0.le hY'm hZ'm hU'm hin,
    ← ENNReal.ofReal_mul (div_nonneg (by positivity) hβ0.le)]
  exact ENNReal.ofReal_le_ofReal hcore

/-- **One Picard step contracts the weighted norm by `1/4`** at the Young weight
`β = max 2 (24 L²)`. -/
theorem wNorm_sub_le_of_picardOutput
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ}
    {Y'₁ Y₁ Y'₂ Y₂ : ℝ → Ω → ℝ} {Z'₁ Z₁ Z'₂ Z₂ : ℝ → Ω → (Fin d → ℝ)}
    {U'₁ U₁ U'₂ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : PicardOutput D f ξ T Y'₁ Z'₁ U'₁ Y₁ Z₁ U₁)
    (h₂ : PicardOutput D f ξ T Y'₂ Z'₂ U'₂ Y₂ Z₂ U₂)
    (hY'm : Measurable (Function.uncurry fun ω s => Y'₁ s ω - Y'₂ s ω))
    (hZ'm : ∀ j, Measurable (Function.uncurry fun ω s => Z'₁ s ω j - Z'₂ s ω j))
    (hU'm : Measurable fun p : Ω × ℝ × E => U'₁ p.2.1 p.1 p.2.2 - U'₂ p.2.1 p.1 p.2.2)
    {b₁ b₂ : Ω → ℝ → ℝ} (hb₁m : Measurable (Function.uncurry b₁))
    (hb₁p : Probability.ProgressivelyMeasurable (augJoint D) b₁)
    (hb₁z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₁ ω s = 0)
    (hb₁q : Brownian.Ito.energy P T b₁ ≠ ⊤)
    (hb₁ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₁ p.1 p.2 = f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1))
    (hb₂m : Measurable (Function.uncurry b₂))
    (hb₂p : Probability.ProgressivelyMeasurable (augJoint D) b₂)
    (hb₂z : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b₂ ω s = 0)
    (hb₂q : Brownian.Ito.energy P T b₂ ≠ ⊤)
    (hb₂ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b₂ p.1 p.2 = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1))
    (hin : wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y'₁ t ω - Y'₂ t ω)
      (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) ≠ ⊤) :
    wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y₁ t ω - Y₂ t ω)
        (fun t ω => Z₁ t ω - Z₂ t ω) (fun t ω e => U₁ t ω e - U₂ t ω e)
      ≤ 4⁻¹ * wNorm P ν (max 2 (24 * L ^ 2)) T (fun t ω => Y'₁ t ω - Y'₂ t ω)
        (fun t ω => Z'₁ t ω - Z'₂ t ω) (fun t ω e => U'₁ t ω e - U'₂ t ω e) := by
  obtain ⟨hfac, hβ⟩ := Contraction.contraction_factor_le L
  refine (wNorm_sub_le_of_picardOutput_of_two_le hL hlip hT h₁ h₂ hY'm hZ'm hU'm hb₁m hb₁p
    hb₁z hb₁q hb₁ hb₂m hb₂p hb₂z hb₂q hb₂ hβ hin).trans (mul_le_mul' ?_ le_rfl)
  have h4 : ENNReal.ofReal (1 / 4 : ℝ) = (4 : ℝ≥0∞)⁻¹ := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 4), ENNReal.ofReal_one,
      ENNReal.ofReal_ofNat, one_div]
  rw [← h4]
  exact ENNReal.ofReal_le_ofReal hfac

end Contraction

end LevyStochCalc.BSDEJ.Solves
