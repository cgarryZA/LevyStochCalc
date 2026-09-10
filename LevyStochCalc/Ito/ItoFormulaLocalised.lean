/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaGeneralShift
import LevyStochCalc.Brownian.ItoCutoff

/-!
# The increment formula with a random shift and no bound on the derivatives

Multiplying a twice continuously differentiable function by a smooth box cutoff of radius `R`
leaves the function and its first two derivatives unchanged on the ball of radius `3R/2` and
makes those derivatives globally bounded. A path that has not left the ball of radius `j`,
translated by a shift of norm at most `M`, stays inside that ball as soon as `R = j + M`, so the
increment formula for the cutoff carries the same integrands as the increment formula for the
function; the stochastic terms are matched by the local property of the Itô integral at the exit
time of the path, and letting `j` grow exhausts almost every sample point.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_between_generalShift_localise` — the increment formula
  between two stopping times for a function translated by a bounded random vector, deduced from
  the same formula for functions whose first two derivatives are globally bounded.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Localise

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **Itô's formula for the increment of a path between two stopping times, for a twice
continuously differentiable function translated by a bounded random vector.** No bound is placed
on the derivatives of the function. -/
theorem itoFormula_between_generalShift_localise
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    (hXc : ∀ ω, Continuous fun s => X s ω)
    (hXa : MeasureTheory.Adapted ℱ' fun r ω => X r ω)
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω) (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable c) {M : ℝ} (hcb : ∀ ω, ‖c ω‖ ≤ M)
    (hmSc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s))
    (hpSc : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
    (hqSc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤)
    (hpShift : ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → ∀ (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s => φ (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped σ (fun ω s => φ (X s ω + c ω) * H p k ω s) ω s)
    (hbase : ∀ (g : (Fin n → ℝ) → ℝ) (g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
      (g'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      ContDiff ℝ 2 g → (∀ z, HasFDerivAt g (g' z) z) → (∀ z, HasFDerivAt g' (g'' z) z) →
      (∀ (p : Fin n) (z : Fin n → ℝ), |coordDeriv g' p z| ≤ K₁) →
      (∀ (p q : Fin n) (z : Fin n → ℝ), |coordDeriv₂ g'' p q z| ≤ K₂) →
      ∀ (hmSg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s))
        (hpSg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s)
        (hqSg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
            (‖Probability.stopped τ
                  (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s‖₊
              : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω : Ω => g (X (clipTime τ T ω) ω + c ω) - g (X (clipTime σ T ω) ω + c ω))
        =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ
                (fun ω s => coordDeriv g' p (X s ω + c ω) * bdrift p ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv g' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (fun ω s =>
                  Probability.stopped τ
                      (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s
                    - Probability.stopped σ
                        (fun ω s => coordDeriv g' p (X s ω + c ω) * H p k ω s) ω s)
                (hmSg p k) (hpSg p k) (hqSg p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              (Probability.stopped τ (fun ω s => coordDeriv₂ g'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                - Probability.stopped σ (fun ω s => coordDeriv₂ g'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω))
      =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
  classical
  have hf'eq : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
  have hf''eq : f'' = fderiv ℝ (fderiv ℝ f) := by
    funext z
    have hz := (hf' z).fderiv
    rw [← hf'eq]
    exact hz.symm
  obtain ⟨M', hM'0, hcb'⟩ : ∃ M' : ℝ, 0 ≤ M' ∧ ∀ ω, ‖c ω‖ ≤ M' :=
    ⟨max M 0, le_max_right M 0, fun ω => (hcb ω).trans (le_max_left M 0)⟩
  have hρ : ∀ j : ℕ, MeasureTheory.IsStoppingTime ℱ'
      (Probability.exitTime (fun ω t => X t ω) (j : ℝ)) := fun j =>
    Probability.isStoppingTime_exitTime (X := fun ω t => X t ω) hXa hXc (j : ℝ)
  have hstep : ∀ j : ℕ, 0 < j → ∀ᵐ ω ∂P,
      ((T : ℝ) : WithTop ℝ) < Probability.exitTime (fun ω t => X t ω) (j : ℝ) ω →
        f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                (Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                  (fun ω s =>
                    Probability.stopped τ
                        (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                      - Probability.stopped σ
                          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
                  (hmSc p k) (hpSc p k) (hqSc p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                  - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                      * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
    intro j hj0
    have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj0
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = (j : ℝ) + M' := ⟨_, rfl⟩
    have hR0 : (0 : ℝ) < R := by rw [hRdef]; linarith
    have hR32 : R < 3 * R / 2 := by linarith
    have hgC : ContDiff ℝ 2 (cutoffFun f R) := contDiff_cutoffFun hfC R
    have hgf : ∀ z, HasFDerivAt (cutoffFun f R) (fderiv ℝ (cutoffFun f R) z) z :=
      fun z => (differentiable_cutoffFun hfC R z).hasFDerivAt
    have hgf' : ∀ z, HasFDerivAt (fderiv ℝ (cutoffFun f R))
        (fderiv ℝ (fderiv ℝ (cutoffFun f R)) z) z :=
      fun z => (differentiable_fderiv_cutoffFun hfC R z).hasFDerivAt
    have hg'c : Continuous (fderiv ℝ (cutoffFun f R)) := continuous_fderiv_cutoffFun hfC R
    obtain ⟨K₁, hK₁n⟩ := exists_bound_fderiv_cutoffFun hfC hR0
    obtain ⟨K₂, hK₂0, hK₂n⟩ := exists_bound_fderiv_fderiv_cutoffFun hfC hR0
    have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hK₁n 0)
    have hK₁c : ∀ (p : Fin n) (z : Fin n → ℝ),
        |coordDeriv (fderiv ℝ (cutoffFun f R)) p z| ≤ K₁ := fun p => abs_coordDeriv_le hK₁n p
    have hK₂c : ∀ (p q : Fin n) (z : Fin n → ℝ),
        |coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f R))) p q z| ≤ K₂ :=
      fun p q => abs_coordDeriv₂_le hK₂n p q
    have hcut : ∀ (p : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        coordDeriv (fderiv ℝ (cutoffFun f R)) p z = coordDeriv f' p z := by
      intro p z hz
      rw [hf'eq]
      unfold coordDeriv
      rw [fderiv_cutoffFun (f := f) hR0 hz]
    have hcut₂ : ∀ (p q : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f R))) p q z = coordDeriv₂ f'' p q z := by
      intro p q z hz
      rw [hf''eq]
      unfold coordDeriv₂
      rw [fderiv_fderiv_cutoffFun (f := f) hR0 hz]
    have hcut₀ : ∀ z : Fin n → ℝ, ‖z‖ < 3 * R / 2 → cutoffFun f R z = f z := by
      intro z hz
      rw [cutoffFun, boxCut_eq_one hR0 hz.le, mul_one]
    have hmAg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
        coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω) * H p k ω s) := fun p k =>
      ((continuous_coordDeriv hg'c p).measurable.comp
        (hXm.add (hc.comp measurable_fst))).mul (hHm p k)
    have hqAg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤ := by
      intro p k
      refine energy_lt_top_of_abs_le_mul (c := K₁) hK₁0 (fun ω s => ?_) (hHs p k)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hK₁c p _) (abs_nonneg _)
    have hmSg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
        Probability.stopped τ
            (fun ω s => coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω)
                * H p k ω s) ω s) := fun p k =>
      measurable_uncurry_stopped_sub hσ hτ (hmAg p k)
    have hpSg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ
            (fun ω s => coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω)
                * H p k ω s) ω s := fun p k =>
      hpShift (coordDeriv (fderiv ℝ (cutoffFun f R)) p) (continuous_coordDeriv hg'c p) p k
    have hqSg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖Probability.stopped τ
                (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω) * H p k ω s) ω s
              - Probability.stopped σ
                  (fun ω s =>
                    coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω)
                      * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun p k =>
      energy_stopped_sub_lt_top hσ hτ (hmAg p k) (hqAg p k)
    have hform := hbase (cutoffFun f R) (fderiv ℝ (cutoffFun f R))
      (fderiv ℝ (fderiv ℝ (cutoffFun f R))) K₁ K₂ hgC hgf hgf' hK₁c hK₂c hmSg hpSg hqSg
    have hSI : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
        ((T : ℝ) : WithTop ℝ) ≤ Probability.exitTime (fun ω t => X t ω) (j : ℝ) ω →
          stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s =>
                      coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s =>
                        coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω)
                          * H p k ω s) ω s)
              (hmSg p k) (hpSg p k) (hqSg p k) T ω
            = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (fun ω s =>
                Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
              (hmSc p k) (hpSc p k) (hqSc p k) T ω := by
      rw [MeasureTheory.ae_all_iff]
      intro p
      rw [MeasureTheory.ae_all_iff]
      intro k
      refine stochasticIntegralBrownian_congr_of_le
        (Probability.exitTime (fun ω t => X t ω) (j : ℝ)) (W.W k) ℱ' (hcoord k) (hρ j)
        (hmSg p k) (hpSg p k) (hqSg p k) (hmSc p k) (hpSc p k) (hqSc p k)
        (fun ω s hs hle => ?_) hT
      have hnorm : ‖X s ω‖ ≤ (j : ℝ) := Probability.norm_le_of_le_exitTime (hXc ω) hs hle
      have hz : ‖X s ω + c ω‖ < 3 * R / 2 := by
        refine lt_of_le_of_lt (norm_add_le _ _) ?_
        have hcω := hcb' ω
        linarith
      have hval : coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω)
          = coordDeriv f' p (X s ω + c ω) := hcut p _ hz
      simp only [Probability.stopped, hval]
    filter_upwards [hform, hSI] with ω hω hSIω hlt
    have hball : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ < (j : ℝ) := by
      intro s hs
      by_contra hcon
      have hmem : ∃ u ∈ Set.Icc (0 : ℝ) T, (j : ℝ) ≤ ‖X u ω‖ := ⟨s, hs, not_lt.mp hcon⟩
      have hle := (Probability.exitTime_le_iff (X := fun ω t => X t ω) (hXc ω) (j : ℝ) T).2 hmem
      exact absurd hle (not_le.mpr hlt)
    have hshift : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω + c ω‖ < 3 * R / 2 := by
      intro s hs
      refine lt_of_le_of_lt (norm_add_le _ _) ?_
      have h1 := hball s hs
      have h2 := hcb' ω
      linarith
    have hshifts : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖X s ω + c ω‖ < 3 * R / 2 := fun s hs =>
      hshift s ⟨hs.1.le, hs.2⟩
    have hclipτ : clipTime τ T ω ∈ Set.Icc (0 : ℝ) T :=
      ⟨clipTime_nonneg hT.le (hτ0 ω), clipTime_le_self τ T ω⟩
    have hclipσ : clipTime σ T ω ∈ Set.Icc (0 : ℝ) T :=
      ⟨clipTime_nonneg hT.le (hσ0 ω), clipTime_le_self σ T ω⟩
    have hleρ : ((T : ℝ) : WithTop ℝ)
        ≤ Probability.exitTime (fun ω t => X t ω) (j : ℝ) ω := le_of_lt hlt
    have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ (fun ω s => coordDeriv (fderiv ℝ (cutoffFun f R)) p
                (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ (fun ω s => coordDeriv (fderiv ℝ (cutoffFun f R)) p
                (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
        = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          (Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have hval : coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω)
          = coordDeriv f' p (X s ω + c ω) := hcut p _ (hshifts s hs)
      simp only [Probability.stopped, hval]
    have e2 : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s =>
                    coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s =>
                      coordDeriv (fderiv ℝ (cutoffFun f R)) p (X s ω + c ω)
                        * H p k ω s) ω s)
            (hmSg p k) (hpSg p k) (hqSg p k) T ω)
        = ∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
            (hmSc p k) (hpSc p k) (hqSc p k) T ω :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => hSIω p k hleρ
    have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ
                (fun ω s => coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f R))) p q
                  (X s ω + c ω) * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ
                  (fun ω s => coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f R))) p q
                    (X s ω + c ω) * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
        = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
              - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                  * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
      refine congrArg (fun x => 1 / 2 * x) ?_
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      have hval : coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f R))) p q (X s ω + c ω)
          = coordDeriv₂ f'' p q (X s ω + c ω) := hcut₂ p q _ (hshifts s hs)
      simp only [Probability.stopped, hval]
    rw [← hcut₀ _ (hshift _ hclipτ), ← hcut₀ _ (hshift _ hclipσ), hω, e1, e2, e3]
  have hall : ∀ᵐ ω ∂P, ∀ j : ℕ, 0 < j →
      ((T : ℝ) : WithTop ℝ) < Probability.exitTime (fun ω t => X t ω) (j : ℝ) ω →
        f (X (clipTime τ T ω) ω + c ω) - f (X (clipTime σ T ω) ω + c ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                (Probability.stopped τ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
                  - Probability.stopped σ
                      (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume)
            + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                  (fun ω s =>
                    Probability.stopped τ
                        (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                      - Probability.stopped σ
                          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
                  (hmSc p k) (hpSc p k) (hqSc p k) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                    * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
                  - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
                      * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
    rw [MeasureTheory.ae_all_iff]
    intro j
    by_cases hj : 0 < j
    · filter_upwards [hstep j hj] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω hcon => absurd hcon hj
  filter_upwards [hall] with ω hω
  obtain ⟨K, hK⟩ := Probability.exists_lt_exitTime (X := fun ω t => X t ω) (hXc ω) hT.le
  exact hω (max K 1) (lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1))
    (hK (max K 1) (le_max_left K 1))

end Localise

end LevyStochCalc.Brownian.Ito
