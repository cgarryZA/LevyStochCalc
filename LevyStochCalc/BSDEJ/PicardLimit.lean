/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardIterates
import LevyStochCalc.BSDEJ.PicardContraction
import LevyStochCalc.BSDEJ.DriftModification
import LevyStochCalc.Brownian.ItoIntegrandComplete
import LevyStochCalc.Poisson.CompensatedIntegrandComplete

/-!
# The limit of the Picard iterates and existence of a solution

The Picard iterates of a backward equation with jumps are Cauchy for the energy of the value
process, for the energies of the diffusion coordinates and for the marked energy of the jump
integrand, so completeness of the admissible integrands produces an admissible limit triple
which the iterates approach in the exponentially weighted norm at the Young weight
`max 2 (24 L²)`. A further Picard step along the limit triple contracts that distance by `1/4`
against every iterate, so its output is at zero weighted distance from the limit triple; a
Lipschitz generator takes the same value along two triples agreeing almost everywhere on
`Ω × [0, T]`, so the output is its own Picard output and solves the equation.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.congr_inputs` — a Picard output along one input
  triple is a Picard output along any input triple agreeing with it almost everywhere on the
  horizon.
* `LevyStochCalc.BSDEJ.Solves.exists_admissible_wNorm_limit` — an energy-Cauchy sequence of
  admissible triples converges in the weighted norm to an admissible triple.
* `LevyStochCalc.BSDEJ.Solves.exists_solvesBSDEJ` — a backward equation with jumps whose
  generator is Lipschitz and square integrable at the origin and whose terminal datum is square
  integrable has a solution.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Truncation to the horizon -/

/-- Restricting the times of a progressively measurable process to a measurable set preserves
progressive measurability. -/
theorem progressivelyMeasurable_indicator_time {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {H : Ω → ℝ → ℝ} (h : Probability.ProgressivelyMeasurable ℱ H) {S : Set ℝ}
    (hS : MeasurableSet S) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => S.indicator (fun _ => H ω s) s := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have hrw : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (fun s => S.indicator (fun _ => H p.1 s) s) p.2)
      = {p : Ω × ℝ | p.2 ∈ S}.indicator fun p => (Set.Iic t).indicator (H p.1) p.2 := by
    funext p
    by_cases ht : p.2 ∈ Set.Iic t <;> by_cases hp : p.2 ∈ S <;> simp [ht, hp]
  rw [hrw]
  exact (h t).indicator (measurable_snd hS)

omit [IsProbabilityMeasure P] in
/-- Processes agreeing on the horizon have the same energy there. -/
theorem energy_congr_on_Icc {T : ℝ} {H K : Ω → ℝ → ℝ}
    (h : ∀ ω : Ω, ∀ s ∈ Set.Icc (0 : ℝ) T, H ω s = K ω s) :
    Brownian.Ito.energy P T H = Brownian.Ito.energy P T K :=
  lintegral_congr fun ω =>
    setLIntegral_congr_fun measurableSet_Icc fun s hs => by rw [h ω s hs]

omit [IsProbabilityMeasure P] in
/-- An energy-Cauchy sequence of jointly and progressively measurable processes has a jointly
and progressively measurable limit of finite energy on the horizon. -/
theorem exists_progressive_energy_limit_of_window (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} {H : ℕ → Ω → ℝ → ℝ} (hm : ∀ n, Measurable (Function.uncurry (H n)))
    (hp : ∀ n, Probability.ProgressivelyMeasurable ℱ (H n))
    (hfin : ∀ n, Brownian.Ito.energy P T (H n) ≠ ⊤)
    (hcau : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => H m ω s - H n ω s) < ε) :
    ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ Probability.ProgressivelyMeasurable ℱ K
      ∧ Brownian.Ito.energy P T K ≠ ⊤
      ∧ Tendsto (fun n => Brownian.Ito.energy P T (fun ω s => H n ω s - K ω s))
          atTop (𝓝 0) := by
  classical
  set H' : ℕ → Ω → ℝ → ℝ :=
    fun n ω s => (Set.Icc (0 : ℝ) T).indicator (fun _ => H n ω s) s with hH'
  have hval : ∀ (n : ℕ) (ω : Ω), ∀ s ∈ Set.Icc (0 : ℝ) T, H' n ω s = H n ω s :=
    fun n ω s hs => Set.indicator_of_mem hs _
  have hm' : ∀ n, Measurable (Function.uncurry (H' n)) := by
    intro n
    have heq : Function.uncurry (H' n)
        = (Prod.snd ⁻¹' Set.Icc (0 : ℝ) T).indicator (Function.uncurry (H n)) := by
      funext p
      by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
      · simp [hH', Function.uncurry, hp]
      · simp [hH', Function.uncurry, hp, Set.indicator_of_notMem]
    rw [heq]
    exact (hm n).indicator (measurable_snd measurableSet_Icc)
  have hz' : ∀ (n : ℕ) (ω : Ω), ∀ s ∉ Set.Icc (0 : ℝ) T, H' n ω s = 0 :=
    fun n ω s hs => Set.indicator_of_notMem hs _
  have hfin' : ∀ n, Brownian.Ito.energy P T (H' n) ≠ ⊤ := by
    intro n
    have he : Brownian.Ito.energy P T (H' n) = Brownian.Ito.energy P T (H n) :=
      energy_congr_on_Icc (hval n)
    rw [he]
    exact hfin n
  have hcau' : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => H' m ω s - H' n ω s) < ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := hcau ε hε
    refine ⟨N, fun m hmN n hnN => ?_⟩
    have he : Brownian.Ito.energy P T (fun ω s => H' m ω s - H' n ω s)
        = Brownian.Ito.energy P T (fun ω s => H m ω s - H n ω s) :=
      energy_congr_on_Icc fun ω s hs => by rw [hval m ω s hs, hval n ω s hs]
    rw [he]
    exact hN m hmN n hnN
  obtain ⟨K, hKm, hKp, -, hKq, hKt⟩ := Brownian.Ito.exists_progressive_energy_limit ℱ hm'
    (fun n => progressivelyMeasurable_indicator_time (hp n) measurableSet_Icc) hz' hfin' hcau'
  refine ⟨K, hKm, hKp, hKq, ?_⟩
  have heq : (fun n => Brownian.Ito.energy P T (fun ω s => H n ω s - K ω s))
      = fun n => Brownian.Ito.energy P T (fun ω s => H' n ω s - K ω s) := by
    funext n
    exact energy_congr_on_Icc fun ω s hs => by rw [hval n ω s hs]
  rw [heq]
  exact hKt

/-- The zero marked process is marked progressively measurable. -/
theorem markedProgressivelyMeasurable_zero (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) :
    Probability.MarkedProgressivelyMeasurable ℱ
      fun (_ : Ω) (_ : ℝ) (_ : E) => (0 : ℝ) := by
  intro t
  letI : MeasurableSpace Ω := ℱ t
  have h : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun _ => (0 : ℝ)) p.2.1)
      = fun _ : Ω × ℝ × E => (0 : ℝ) := by
    funext p
    simp [Set.indicator_apply]
  rw [h]
  exact stronglyMeasurable_const

/-! ### Changing the input triple of a Picard step on a null set -/

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A Lipschitz generator takes the same value on two jump arguments differing on a null set of
marks. -/
theorem generator_congr_of_lintegral_eq_zero {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u₁ u₂ : E → ℝ)
    (hu : ∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0) :
    f s y z u₁ = f s y z u₂ := by
  have h := hlip s y y z z u₁ u₂
  rw [hu, ENNReal.zero_rpow_of_pos (by norm_num : (0 : ℝ) < 1 / 2)] at h
  simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, add_zero, mul_zero,
    nonpos_iff_eq_zero, ENNReal.coe_eq_zero, nnnorm_eq_zero, sub_eq_zero] at h
  exact h

/-- The output of a Picard step along an input triple is the output of a Picard step along any
input triple agreeing with it almost everywhere on the horizon. -/
theorem PicardOutput.congr_inputs {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {ξ : Ω → ℝ} {T : ℝ} {Y'₁ Y'₂ Y : ℝ → Ω → ℝ} {Z'₁ Z'₂ Z : ℝ → Ω → (Fin d → ℝ)}
    {U'₁ U'₂ U : ℝ → Ω → E → ℝ}
    (hY : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Y'₁ p.2 p.1 = Y'₂ p.2 p.1)
    (hZ : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Z'₁ p.2 p.1 = Z'₂ p.2 p.1)
    (hU : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      ∫⁻ e, (‖U'₁ p.2 p.1 e - U'₂ p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0)
    (h : PicardOutput D f ξ T Y'₁ Z'₁ U'₁ Y Z U) :
    PicardOutput D f ξ T Y'₂ Z'₂ U'₂ Y Z U := by
  have hfeq : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      f p.2 (Y'₁ p.2 p.1) (Z'₁ p.2 p.1) (U'₁ p.2 p.1)
        = f p.2 (Y'₂ p.2 p.1) (Z'₂ p.2 p.1) (U'₂ p.2 p.1) := by
    filter_upwards [hY, hZ, hU] with p h1 h2 h3
    rw [h1, h2]
    exact generator_congr_of_lintegral_eq_zero hlip _ _ _ _ _ h3
  refine
    { Z_meas := h.Z_meas, Z_prog := h.Z_prog, Z_vanish := h.Z_vanish, Z_sq := h.Z_sq,
      U_meas := h.U_meas, U_prog := h.U_prog, U_vanish := h.U_vanish, U_sq := h.U_sq,
      Y_meas := h.Y_meas, Y_adapted := h.Y_adapted, Y_cadlag := h.Y_cadlag,
      Y_terminal := h.Y_terminal, Y_sup := h.Y_sup, eqn := ?_ }
  intro t ht
  filter_upwards [h.eqn t ht, Measure.ae_ae_of_ae_prod hfeq] with ω h1 h2
  have hint : (∫ s in Set.Icc t T, f s (Y'₁ s ω) (Z'₁ s ω) (U'₁ s ω))
      = ∫ s in Set.Icc t T, f s (Y'₂ s ω) (Z'₂ s ω) (U'₂ s ω) :=
    integral_congr_ae
      (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl) h2)
  rw [h1, hint]

/-! ### Triples at zero weighted distance -/

omit [IsProbabilityMeasure P] in
/-- The energy density of a triple of vanishing weighted norm vanishes almost everywhere on the
horizon. -/
theorem ae_density_eq_zero_of_wNorm_eq_zero {β T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (h : wNorm P ν β T Y Z U = 0) :
    ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      density ν Y Z U p.1 p.2 = 0 := by
  have hm : Measurable fun p : Ω × ℝ =>
      ENNReal.ofReal (Real.exp (β * p.2)) * density ν Y Z U p.1 p.2 := by
    refine Measurable.mul ?_ (measurable_uncurry_density hYm hZm hUm)
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_snd))
  have hprod : ∫⁻ p, ENNReal.ofReal (Real.exp (β * p.2)) * density ν Y Z U p.1 p.2
      ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) = 0 := by
    rw [lintegral_prod _ hm.aemeasurable]
    exact h
  filter_upwards [(lintegral_eq_zero_iff' hm.aemeasurable).mp hprod] with p hp
  have hw : ENNReal.ofReal (Real.exp (β * p.2)) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  exact (mul_eq_zero.mp hp).resolve_left hw

omit [IsProbabilityMeasure P] in
/-- Two triples at zero weighted distance agree almost everywhere on the horizon, the jump
integrands up to a null set of marks. -/
theorem ae_eq_of_wNorm_sub_eq_zero {β T : ℝ} {Y₁ Y₂ : ℝ → Ω → ℝ}
    {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y₁ s ω - Y₂ s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2)
    (h : wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
      (fun t ω e => U₁ t ω e - U₂ t ω e) = 0) :
    (∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Y₁ p.2 p.1 = Y₂ p.2 p.1)
      ∧ (∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))), Z₁ p.2 p.1 = Z₂ p.2 p.1)
      ∧ ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          ∫⁻ e, (‖U₁ p.2 p.1 e - U₂ p.2 p.1 e‖₊ : ℝ≥0∞) ^ 2 ∂ν = 0 := by
  classical
  have hd := ae_density_eq_zero_of_wNorm_eq_zero hYm hZm hUm h
  refine ⟨?_, ?_, ?_⟩ <;> filter_upwards [hd] with p hp <;> rw [density] at hp <;>
    obtain ⟨hab, hc⟩ := add_eq_zero.mp hp
  · obtain ⟨ha, -⟩ := add_eq_zero.mp hab
    have h0 : (‖Y₁ p.2 p.1 - Y₂ p.2 p.1‖₊ : ℝ≥0∞) = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp ha
    simpa [sub_eq_zero] using h0
  · obtain ⟨-, hb⟩ := add_eq_zero.mp hab
    funext j
    have hj := Finset.sum_eq_zero_iff.mp hb j (Finset.mem_univ j)
    have h0 : (‖Z₁ p.2 p.1 j - Z₂ p.2 p.1 j‖₊ : ℝ≥0∞) = 0 :=
      (pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hj
    simpa [sub_eq_zero] using h0
  · exact hc

/-- A quantity dominated along a null sequence by the factor-two triangle bound vanishes. -/
theorem eq_zero_of_le_two_mul_of_tendsto (x : ℝ≥0∞) {W : ℕ → ℝ≥0∞}
    (hW : Tendsto W atTop (𝓝 0))
    (h : ∀ n, x ≤ 2 * (4⁻¹ * W n) + 2 * W (n + 1)) : x = 0 := by
  have h1 : Tendsto (fun n => (4 : ℝ≥0∞)⁻¹ * W n) atTop (𝓝 ((4 : ℝ≥0∞)⁻¹ * 0)) :=
    ENNReal.Tendsto.const_mul hW (Or.inr (by simp))
  rw [mul_zero] at h1
  have h2 : Tendsto (fun n => (2 : ℝ≥0∞) * ((4 : ℝ≥0∞)⁻¹ * W n)) atTop
      (𝓝 ((2 : ℝ≥0∞) * 0)) := ENNReal.Tendsto.const_mul h1 (Or.inr (by simp))
  rw [mul_zero] at h2
  have h3 : Tendsto (fun n => W (n + 1)) atTop (𝓝 0) := hW.comp (tendsto_add_atTop_nat 1)
  have h4 : Tendsto (fun n => (2 : ℝ≥0∞) * W (n + 1)) atTop (𝓝 ((2 : ℝ≥0∞) * 0)) :=
    ENNReal.Tendsto.const_mul h3 (Or.inr (by simp))
  rw [mul_zero] at h4
  have h5 : Tendsto (fun n => 2 * (4⁻¹ * W n) + 2 * W (n + 1)) atTop (𝓝 0) := by
    simpa using h2.add h4
  exact nonpos_iff_eq_zero.mp (ge_of_tendsto' h5 h)

/-! ### The weighted norm against the energies -/

omit [SigmaFinite ν] in
/-- The weighted norm of a triple on the horizon is at most `e^{βT}` times the sum of the
energy of the value, of the energies of the diffusion coordinates and of the marked energy of
the jump integrand. -/
theorem wNorm_le_energies {β T : ℝ} (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    wNorm P ν β T Y Z U ≤ ENNReal.ofReal (Real.exp (β * T)) *
      (Brownian.Ito.energy P T (fun ω s => Y s ω)
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

/-! ### The limit of an energy-Cauchy sequence of admissible triples -/

section Limit

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν} {T : ℝ}

/-- An energy-Cauchy sequence of admissible triples has an admissible limit, which the sequence
approaches in the exponentially weighted norm on the horizon. -/
theorem exists_admissible_wNorm_limit {q : ℕ → Triple Ω E d}
    (hA : ∀ n, Admissible D T (q n).1 (q n).2.1 (q n).2.2)
    (hcY : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (q m).1 s ω - (q n).1 s ω) < ε)
    (hcZ : ∀ i : Fin d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (q m).2.1 s ω i - (q n).2.1 s ω i) < ε)
    (hcU : ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => (q m).2.2 s ω e - (q n).2.2 s ω e) < ε)
    {β : ℝ} (hβ : 0 ≤ β) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      Admissible D T Y Z U ∧ Tendsto (fun n => wNorm P ν β T
        (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
        (fun t ω e => (q n).2.2 t ω e - U t ω e)) atTop (𝓝 0) := by
  classical
  obtain ⟨KY, hKYm, hKYp, hKYq, hKYt⟩ :=
    exists_progressive_energy_limit_of_window (augJoint D).rightCont
      (H := fun n ω s => (q n).1 s ω) (fun n => (hA n).measurable_uncurry_Y)
      (fun n => (hA n).Y_prog) (fun n => (hA n).Y_sq) hcY
  have hZlim : ∀ i : Fin d, ∃ K : Ω → ℝ → ℝ, Measurable (Function.uncurry K)
      ∧ Probability.ProgressivelyMeasurable (augJoint D) K
      ∧ (∀ ω, ∀ s ∉ Set.Icc (0 : ℝ) T, K ω s = 0)
      ∧ Brownian.Ito.energy P T K ≠ ⊤
      ∧ Tendsto (fun n => Brownian.Ito.energy P T
          (fun ω s => (q n).2.1 s ω i - K ω s)) atTop (𝓝 0) := by
    intro i
    refine Brownian.Ito.exists_progressive_energy_limit (augJoint D)
      (fun n => (hA n).Z_meas i) (fun n => (hA n).Z_prog i) (fun n ω s hs => ?_)
      (fun n => (hA n).Z_sq i) (hcZ i)
    have hv := (hA n).Z_vanish ω s hs
    simp [hv]
  choose KZ hKZm hKZp hKZz hKZq hKZt using hZlim
  obtain ⟨KU, hKUm, hKUp, hKUz, hKUq, hKUt⟩ :=
    Poisson.Compensated.exists_marked_progressive_energy_limit (augJoint D)
      (fun n => (hA n).U_meas) (fun n => (hA n).U_prog) (fun n => (hA n).U_vanish)
      (fun n => (hA n).U_sq) hcU
  refine ⟨fun s ω => KY ω s, fun s ω i => KZ i ω s, fun s ω e => KU ω s e,
    { Y_meas := hKYm.comp measurable_swap, Y_prog := hKYp, Y_sq := hKYq,
      Z_meas := hKZm, Z_prog := hKZp,
      Z_vanish := fun ω s hs => funext fun i => hKZz i ω s hs, Z_sq := hKZq,
      U_meas := hKUm, U_prog := hKUp, U_vanish := hKUz, U_sq := hKUq }, ?_⟩
  have hsumZ : Tendsto (fun n => ∑ j, Brownian.Ito.energy P T
      (fun ω s => (q n).2.1 s ω j - KZ j ω s)) atTop (𝓝 0) := by
    have hfs := tendsto_finsetSum (Finset.univ : Finset (Fin d))
      fun j (_ : j ∈ Finset.univ) => hKZt j
    simpa using hfs
  have hsum : Tendsto (fun n => Brownian.Ito.energy P T
        (fun ω s => (q n).1 s ω - KY ω s)
      + (∑ j, Brownian.Ito.energy P T (fun ω s => (q n).2.1 s ω j - KZ j ω s))
      + Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => (q n).2.2 s ω e - KU ω s e)) atTop (𝓝 0) := by
    simpa using (hKYt.add hsumZ).add hKUt
  have hlim : Tendsto (fun n => ENNReal.ofReal (Real.exp (β * T)) *
      (Brownian.Ito.energy P T (fun ω s => (q n).1 s ω - KY ω s)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => (q n).2.1 s ω j - KZ j ω s))
        + Poisson.Compensated.markedEnergy P ν T
          (fun ω s e => (q n).2.2 s ω e - KU ω s e))) atTop
      (𝓝 (ENNReal.ofReal (Real.exp (β * T)) * 0)) :=
    ENNReal.Tendsto.const_mul hsum (Or.inr ENNReal.ofReal_ne_top)
  rw [mul_zero] at hlim
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le)
    (fun n => wNorm_le_energies hβ ((hA n).measurable_uncurry_Y.sub hKYm)
      fun j => ((hA n).Z_meas j).sub (hKZm j))

end Limit

/-! ### The fixed point of the Picard step -/

section FixedPoint

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

/-- The output of a Picard step along the limit of a sequence of Picard iterates converging in
the weighted norm solves the backward equation. -/
theorem exists_solvesBSDEJ_of_wNorm_limit (hL : 0 ≤ L) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun r : ℝ × ℝ × (Fin d → ℝ) => f r.1 r.2.1 r.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)
    {q : ℕ → Triple Ω E d} (hA : ∀ n, Admissible D T (q n).1 (q n).2.1 (q n).2.2)
    (hstep : ∀ n, IsStep D f ξ T (q n).1 (q n).2.1 (q n).2.2
      (q (n + 1)).1 (q (n + 1)).2.1 (q (n + 1)).2.2)
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (hq : Admissible D T Y Z U)
    (hlim : Tendsto (fun n => wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
      (fun t ω e => (q n).2.2 t ω e - U t ω e)) atTop (𝓝 0)) :
    ∃ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y' Z' U' := by
  obtain ⟨Ys, Zs, Us, hAs, b, hbm, hbp, hbz, hbq, hb, hout⟩ :=
    hq.exists_step (L := L) hT hf hlip hf0 hξ2 hξm
  refine ⟨Ys, Zs, Us, ?_⟩
  have hcomm : ∀ n : ℕ, wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => Y t ω - (q n).1 t ω) (fun t ω => Z t ω - (q n).2.1 t ω)
      (fun t ω e => U t ω e - (q n).2.2 t ω e)
      = wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
        (fun t ω e => (q n).2.2 t ω e - U t ω e) := fun n =>
    wNorm_sub_comm _ _ _ _ _ _
  have hbound : ∀ n : ℕ, wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => Ys t ω - Y t ω) (fun t ω => Zs t ω - Z t ω)
      (fun t ω e => Us t ω e - U t ω e)
      ≤ 2 * (4⁻¹ * wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (q n).1 t ω - Y t ω) (fun t ω => (q n).2.1 t ω - Z t ω)
          (fun t ω e => (q n).2.2 t ω e - U t ω e))
        + 2 * wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (q (n + 1)).1 t ω - Y t ω)
          (fun t ω => (q (n + 1)).2.1 t ω - Z t ω)
          (fun t ω e => (q (n + 1)).2.2 t ω e - U t ω e) := by
    intro n
    obtain ⟨b₂, hb₂m, hb₂p, hb₂z, hb₂q, hb₂, hout₂⟩ := hstep n
    have hcon : wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => Ys t ω - (q (n + 1)).1 t ω)
        (fun t ω => Zs t ω - (q (n + 1)).2.1 t ω)
        (fun t ω e => Us t ω e - (q (n + 1)).2.2 t ω e)
        ≤ 4⁻¹ * wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => Y t ω - (q n).1 t ω) (fun t ω => Z t ω - (q n).2.1 t ω)
          (fun t ω e => U t ω e - (q n).2.2 t ω e) :=
      wNorm_sub_le_of_picardOutput hL hlip hT hout hout₂
        (hq.measurable_uncurry_Y.sub (hA n).measurable_uncurry_Y)
        (fun j => (hq.Z_meas j).sub ((hA n).Z_meas j)) (hq.U_meas.sub (hA n).U_meas)
        hbm hbp hbz hbq hb hb₂m hb₂p hb₂z hb₂q hb₂
        (hq.wNorm_sub_ne_top (hA n) (zero_le_youngWeight L))
    refine le_trans (wNorm_sub_le_two_mul_mid (Y₂ := (q (n + 1)).1)
      (Z₂ := (q (n + 1)).2.1) (U₂ := (q (n + 1)).2.2)
      (hAs.measurable_uncurry_Y.sub (hA (n + 1)).measurable_uncurry_Y)
      (fun j => (hAs.Z_meas j).sub ((hA (n + 1)).Z_meas j))
      (hAs.U_meas.sub (hA (n + 1)).U_meas)) ?_
    refine add_le_add (mul_le_mul' le_rfl ?_) le_rfl
    rw [← hcomm n]
    exact hcon
  have hzero := eq_zero_of_le_two_mul_of_tendsto _ hlim hbound
  obtain ⟨hY, hZ, hU⟩ := ae_eq_of_wNorm_sub_eq_zero
    (hAs.measurable_uncurry_Y.sub hq.measurable_uncurry_Y)
    (fun j => (hAs.Z_meas j).sub (hq.Z_meas j)) (hAs.U_meas.sub hq.U_meas) hzero
  refine PicardOutput.toSolvesBSDEJ
    (PicardOutput.congr_inputs (L := L) hlip ?_ ?_ ?_ hout)
  · filter_upwards [hY] with p hp
    exact hp.symm
  · filter_upwards [hZ] with p hp
    exact hp.symm
  · filter_upwards [hU] with p hp
    rw [← hp]
    exact lintegral_congr fun e => by rw [coe_nnnorm_sub_comm]

end FixedPoint

/-! ### Existence of a solution -/

/-- The zero triple is admissible. -/
theorem admissible_zero (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ) :
    Admissible D T (fun _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) (fun _ _ _ => (0 : ℝ)) where
  Y_meas := measurable_const
  Y_prog := Brownian.Ito.progressivelyMeasurable_zero _
  Y_sq := by simp [Brownian.Ito.energy]
  Z_meas := fun _ => measurable_const
  Z_prog := fun _ => Brownian.Ito.progressivelyMeasurable_zero _
  Z_vanish := fun _ _ _ => rfl
  Z_sq := fun _ => by simp [Brownian.Ito.energy]
  U_meas := measurable_const
  U_prog := markedProgressivelyMeasurable_zero _
  U_vanish := fun _ _ _ _ => rfl
  U_sq := by simp [Poisson.Compensated.markedEnergy]

/-- **Existence for a backward equation with jumps.** A Lipschitz generator that is square
integrable at the origin on the horizon, together with a square integrable terminal datum
measurable for the augmented joint filtration at the horizon, admits a solution triple. -/
theorem exists_solvesBSDEJ (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ u : E → ℝ, Measurable fun r : ℝ × ℝ × (Fin d → ℝ) => f r.1 r.2.1 r.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    {T : ℝ} (hT : 0 < T)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    {ξ : Ω → ℝ} (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y Z U := by
  classical
  set p₀ : AdmTriple D T :=
    ⟨(fun _ _ => (0 : ℝ), fun _ _ _ => (0 : ℝ), fun _ _ _ => (0 : ℝ)), admissible_zero D T⟩
  obtain ⟨Y, Z, U, hq, hlim⟩ := exists_admissible_wNorm_limit
    (q := picardSeq hT hf hlip hf0 hξ2 hξm p₀)
    (picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀)
    (energy_picardSeq_cauchy hT hf hlip hf0 hξ2 hξm hL p₀)
    (fun i => energy_picardSeq_cauchy_coord hT hf hlip hf0 hξ2 hξm hL p₀ i)
    (markedEnergy_picardSeq_cauchy hT hf hlip hf0 hξ2 hξm hL p₀) (zero_le_youngWeight L)
  exact exists_solvesBSDEJ_of_wNorm_limit hL hT hf hlip hf0 hξ2 hξm
    (picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀)
    (picardSeq_succ_isStep hT hf hlip hf0 hξ2 hξm p₀) hq hlim

end LevyStochCalc.BSDEJ.Solves
