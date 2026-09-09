/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoQuadVarSum
import LevyStochCalc.Brownian.ItoLinear
import LevyStochCalc.Brownian.DriftIncrement

/-!
# The polarised quadratic variation

For two integrands against the *same* Brownian motion, the product of the increments of their
Itô integrals, compensated by the window integral of the product of the integrands, is
conditionally centred at the left endpoint. The identity `2xy = (x+y)² − x² − y²` reduces this
to the compensated square increments of `H₁ + H₂`, of `H₁` and of `H₂`, using additivity of the
Itô integral in the integrand.

## Main statements

* `LevyStochCalc.Brownian.Ito.polarQuadVarIncrement` — the compensated product of increments.
* `LevyStochCalc.Brownian.Ito.smul_two_polarQuadVarIncrement_ae` — the polarisation identity.
* `LevyStochCalc.Brownian.Ito.condExp_polarQuadVarIncrement` — it is conditionally centred at
  the left endpoint.
* `LevyStochCalc.Brownian.Ito.integral_sq_polarQuadVarIncrement_le` — its second moment.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Polarised

variable {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
  (H₁ H₂ : Ω → ℝ → ℝ)
  (hm₁ : Measurable (Function.uncurry H₁)) (hm₂ : Measurable (Function.uncurry H₂))
  (hp₁ : Probability.ProgressivelyMeasurable ℱ H₁)
  (hp₂ : Probability.ProgressivelyMeasurable ℱ H₂)
  (hq₁ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hq₂ : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hma : Measurable (Function.uncurry fun ω s => H₁ ω s + H₂ ω s))
  (hpa : Probability.ProgressivelyMeasurable ℱ fun ω s => H₁ ω s + H₂ ω s)
  (hqa : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H₁ ω s + H₂ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

/-- The product of the increments of the Itô integrals of `H₁` and `H₂` against the same Brownian
motion, compensated by the window integral of `H₁·H₂`. -/
noncomputable def polarQuadVarIncrement (a b : ℝ) (ω : Ω) : ℝ :=
  (stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ a ω)
    * (stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ b ω
      - stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ a ω)
    - ((∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume)
      - ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume)

include hℱ in
/-- Additivity of the Itô integral in the integrand, at every nonnegative time. -/
theorem stochasticIntegralBrownian_add_ae_of_nonneg {t : ℝ} (ht : 0 ≤ t) :
    stochasticIntegralBrownian W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁ t ω
        + stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂ t ω := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · filter_upwards [stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ
        (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₁ hm₁ hp₁ hq₁ (le_refl (0 : ℝ)),
      stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ H₂ hm₂ hp₂ hq₂ (le_refl (0 : ℝ))]
      with ω e0 e1 e2
    rw [e0, e1, e2, Pi.zero_apply, add_zero]
  · exact stochasticIntegralBrownian_add W ℱ hℱ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ hma hpa hqa ht'

section Bounds

variable {C : ℝ} (hC0 : 0 ≤ C) (hCH₁ : ∀ ω s, |H₁ ω s| ≤ C) (hCH₂ : ∀ ω s, |H₂ ω s| ≤ C)

include hC0 hCH₁ hCH₂ hm₁ hm₂ in
/-- The compensator of the sum expands by the binomial identity. -/
theorem compensator_add_sq_eq {t : ℝ} (ht : 0 ≤ t) (ω : Ω) :
    ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = (∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u) ^ 2 ∂volume)
        + 2 * (∫ u in Set.Icc (0 : ℝ) t, H₁ ω u * H₂ ω u ∂volume)
        + ∫ u in Set.Icc (0 : ℝ) t, (H₂ ω u) ^ 2 ∂volume := by
  have hfin : volume (Set.Icc (0 : ℝ) t) ≠ ⊤ := (measure_Icc_lt_top).ne
  have hm₁' : Measurable (H₁ ω) := Measurable.of_uncurry_left hm₁
  have hm₂' : Measurable (H₂ ω) := Measurable.of_uncurry_left hm₂
  have hsq : ∀ x : ℝ, |x| ≤ C → x ^ 2 ≤ C ^ 2 := by
    intro x hx
    nlinarith [abs_nonneg x, sq_abs x]
  have hi₁ : IntegrableOn (fun u => (H₁ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_of_bounded_of_measurable (hm₁'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₁ ω u)) hfin
  have hi₂ : IntegrableOn (fun u => (H₂ ω u) ^ 2) (Set.Icc (0 : ℝ) t) volume :=
    integrableOn_of_bounded_of_measurable (hm₂'.pow_const 2)
      (fun u => by rw [abs_of_nonneg (sq_nonneg _)]; exact hsq _ (hCH₂ ω u)) hfin
  have hi₁₂ : IntegrableOn (fun u => 2 * (H₁ ω u * H₂ ω u)) (Set.Icc (0 : ℝ) t) volume := by
    refine integrableOn_of_bounded_of_measurable (B := 2 * C ^ 2)
      ((measurable_const).mul (hm₁'.mul hm₂')) (fun u => ?_) hfin
    show |2 * (H₁ ω u * H₂ ω u)| ≤ 2 * C ^ 2
    have habs : |2 * (H₁ ω u * H₂ ω u)| = 2 * (|H₁ ω u| * |H₂ ω u|) := by
      rw [abs_mul, abs_mul, abs_two]
    rw [habs]
    nlinarith [hCH₁ ω u, hCH₂ ω u, abs_nonneg (H₁ ω u), abs_nonneg (H₂ ω u)]
  have hexp : ∀ u : ℝ, (H₁ ω u + H₂ ω u) ^ 2
      = (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2 := fun u => by ring
  have hcongr : ∫ u in Set.Icc (0 : ℝ) t, (H₁ ω u + H₂ ω u) ^ 2 ∂volume
      = ∫ u in Set.Icc (0 : ℝ) t,
          ((H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u) + (H₂ ω u) ^ 2) ∂volume :=
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun u _ => hexp u
  have hiSum : IntegrableOn (fun u => (H₁ ω u) ^ 2 + 2 * (H₁ ω u * H₂ ω u))
      (Set.Icc (0 : ℝ) t) volume := hi₁.add hi₁₂
  rw [hcongr, MeasureTheory.integral_add hiSum hi₂,
    MeasureTheory.integral_add hi₁ hi₁₂, MeasureTheory.integral_const_mul]

include hℱ hC0 hCH₁ hCH₂ in
/-- **Polarisation.** Twice the compensated product is the compensated square increment of
`H₁ + H₂` less those of `H₁` and of `H₂`. -/
theorem smul_two_polarQuadVarIncrement_ae {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (2 : ℝ) • polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b
      =ᵐ[P] fun ω =>
        quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
          - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
          - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω := by
  have hb : (0 : ℝ) ≤ b := ha.trans hab
  filter_upwards [stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂
      hq₁ hq₂ hma hpa hqa hb,
    stochasticIntegralBrownian_add_ae_of_nonneg W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
      hma hpa hqa ha] with ω eb ea
  simp only [Pi.smul_apply, smul_eq_mul, polarQuadVarIncrement, quadVarIncrement]
  rw [eb, ea, compensator_add_sq_eq H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ hb ω,
    compensator_add_sq_eq H₁ H₂ hm₁ hm₂ hC0 hCH₁ hCH₂ ha ω]
  ring

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- The compensated product lies in `L²`. -/
theorem memLp_two_polarQuadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    MemLp (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) 2 P := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have mAdd := memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab
  have m₁ := memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab
  have m₂ := memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab
  have hZ : MemLp (fun ω =>
      quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω) 2 P := (mAdd.sub m₁).sub m₂
  have hpol := smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hae : (fun ω => (1 / 2 : ℝ) *
      (quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b ω
        - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b ω
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b ω))
      =ᵐ[P] polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b := by
    filter_upwards [hpol] with ω hω
    simp only [Pi.smul_apply, smul_eq_mul] at hω
    linarith
  exact (hZ.const_mul (1 / 2 : ℝ)).ae_eq hae

include hℱ hma hpa hqa hC0 hCH₁ hCH₂ in
/-- **The compensated product is conditionally centred at the left endpoint.** -/
theorem condExp_polarQuadVarIncrement {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    P[polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b | ℱ.rightCont a]
      =ᵐ[P] 0 := by
  have hC20 : (0 : ℝ) ≤ 2 * C := by linarith
  have hb₁ : ∀ ω s, |H₁ ω s| ≤ 2 * C := fun ω s => (hCH₁ ω s).trans (by linarith)
  have hb₂ : ∀ ω s, |H₂ ω s| ≤ 2 * C := fun ω s => (hCH₂ ω s).trans (by linarith)
  have hba : ∀ ω s, |H₁ ω s + H₂ ω s| ≤ 2 * C := fun ω s =>
    (abs_add_le _ _).trans (by linarith [hCH₁ ω s, hCH₂ ω s])
  have iAdd := (memLp_two_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa
    hC20 hba ha hab).integrable (by norm_num)
  have i₁ := (memLp_two_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ hC20 hb₁ ha hab).integrable
    (by norm_num)
  have i₂ := (memLp_two_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ hC20 hb₂ ha hab).integrable
    (by norm_num)
  have cAdd := condExp_quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa ha hab.le
  have c₁ := condExp_quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ ha hab.le
  have c₂ := condExp_quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ ha hab.le
  have e1 := MeasureTheory.condExp_sub (iAdd.sub i₁) i₂ (ℱ.rightCont a)
  have e2 := MeasureTheory.condExp_sub iAdd i₁ (ℱ.rightCont a)
  have hcond0 : P[quadVarIncrement W ℱ hℱ (fun ω s => H₁ ω s + H₂ ω s) hma hpa hqa a b
        - quadVarIncrement W ℱ hℱ H₁ hm₁ hp₁ hq₁ a b
        - quadVarIncrement W ℱ hℱ H₂ hm₂ hp₂ hq₂ a b | ℱ.rightCont a] =ᵐ[P] 0 := by
    filter_upwards [e1, e2, cAdd, c₁, c₂] with ω h1 h2 hA hh1 hh2
    rw [h1, Pi.sub_apply, h2, Pi.sub_apply, hA, hh1, hh2, Pi.zero_apply]
    ring
  have hpol := smul_two_polarQuadVarIncrement_ae W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂
    hma hpa hqa hC0 hCH₁ hCH₂ ha hab.le
  have hkey := (MeasureTheory.condExp_congr_ae hpol).trans hcond0
  have hsm := MeasureTheory.condExp_smul (μ := P) (m := ℱ.rightCont a) (2 : ℝ)
    (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b)
  filter_upwards [hkey, hsm] with ω h1 h2
  rw [h2, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h1
  rw [Pi.zero_apply]
  linarith

include hℱ in
/-- The compensated product across a cell is measurable for the σ-algebra at the right
endpoint. -/
theorem stronglyMeasurable_polarQuadVarIncrement {a b : ℝ} (hab : a ≤ b) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (polarQuadVarIncrement W ℱ hℱ H₁ H₂ hm₁ hm₂ hp₁ hp₂ hq₁ hq₂ a b) := by
  have hM₁ := martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H₁ hm₁ hp₁ hq₁
  have hM₂ := martingale_rightCont_stochasticIntegralBrownian W ℱ hℱ H₂ hm₂ hp₂ hq₂
  have h1b := hM₁.1 b
  have h1a := (hM₁.1 a).mono (ℱ.rightCont.mono hab)
  have h2b := hM₂.1 b
  have h2a := (hM₂.1 a).mono (ℱ.rightCont.mono hab)
  have hcb : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) b, H₁ ω u * H₂ ω u ∂volume) :=
    (((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont b))
  have hca : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.rightCont b)
      (fun ω => ∫ u in Set.Icc (0 : ℝ) a, H₁ ω u * H₂ ω u ∂volume) :=
    ((((hp₁.mul hp₂).stronglyMeasurable_setIntegral measurableSet_Icc
      Set.Icc_subset_Iic_self volume).mono (ℱ.le_rightCont a)).mono (ℱ.rightCont.mono hab))
  exact ((h1b.sub h1a).mul (h2b.sub h2a)).sub (hcb.sub hca)

end Bounds

end Polarised

end LevyStochCalc.Brownian.Ito
