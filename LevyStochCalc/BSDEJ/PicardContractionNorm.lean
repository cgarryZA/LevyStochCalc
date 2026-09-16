/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardItoLevy
import LevyStochCalc.Ito.SecondMomentBackward

/-!
# The exponentially weighted norm of a triple

The exponentially weighted `L²` norm `wNorm` of a triple `(Y, Z, U)` over a horizon `[0, T]`
weights the squared value, the squared diffusion coordinates and the marked energy of the jump
integrand by `e^{βs}` and integrates them over the horizon and the sample space. Its integrand at
a sample point and a time is the pointwise energy density `density`; the norm is finite when the
value, the diffusion coordinates and the jump integrand have finite energy on the horizon, and it
is then the real integral over the horizon of the weighted sample energy density.
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

end LevyStochCalc.BSDEJ.Solves
