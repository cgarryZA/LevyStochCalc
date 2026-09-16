/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaCutoffIntegrands
import LevyStochCalc.Ito.ItoFormulaLocalised

/-!
# The increment formula for a translated path with no bound on the derivatives

The family of events on which a translated path stays in a ball over a bounded window exhausts
the sample space, and on the `m`-th member a twice continuously differentiable function agrees
with its box cutoff of radius `m + 1` along the translated path, together with its first two
derivatives. Transferring the increment formula for the cutoff along that family therefore gives
Itô's formula for the increment of the translated path between two ordered stopping times, with
no bound on the derivatives of the function and none on the translation; the stochastic terms
are matched there by hypothesis, from a stopping time below which the two integrands agree.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.Ito.JumpFormulaCutoff

universe u

section Localise

open LevyStochCalc.Brownian.Ito

/-- Two integrands agreeing strictly between two ordered stopping times give the same increment
of the cut-off integrand. -/
theorem stopped_sub_congr {Ω : Type u} {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω)
    {A B : Ω → ℝ → ℝ} {ω : Ω} {s : ℝ}
    (h : σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω → A ω s = B ω s) :
    Probability.stopped τ A ω s - Probability.stopped σ A ω s
      = Probability.stopped τ B ω s - Probability.stopped σ B ω s := by
  simp only [Probability.stopped]
  by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
  · by_cases hσs : ((s : ℝ) : WithTop ℝ) ≤ σ ω
    · simp only [if_pos hτs, if_pos hσs, sub_self]
    · simp only [if_pos hτs, if_neg hσs, sub_zero, h (not_le.mp hσs) hτs]
  · have hσs : ¬(((s : ℝ) : WithTop ℝ) ≤ σ ω) := fun hh => hτs (hh.trans (hστ ω))
    simp only [if_neg hτs, if_neg hσs]

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {n d : ℕ}

set_option maxHeartbeats 1000000 in
-- the localisation case split against the shifted, translated coefficients elaborates a large
-- number of nested `nlinarith`/`linarith` goals and needs more than the default budget.
/-- **Itô's formula for the increment of a path between two ordered stopping times, for a twice
continuously differentiable function translated by a random vector.** Neither the derivatives of
the function nor the translation carry a global bound: the family of events on which the
translated path stays in a ball over the window supplies the localisation, and the stochastic
terms are matched there by hypothesis. -/
theorem itoFormula_between_shift_localise
    (W : Brownian.Multidim.MultidimBrownianMotion P d)
    (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k : Fin d, Brownian.IsBrownianFiltration (W.W k) ℱ')
    {X : ℝ → Ω → Fin n → ℝ} (hXm : Measurable (Function.uncurry fun ω s => X s ω))
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {bdrift : Fin n → Ω → ℝ → ℝ}
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {T : ℝ}
    {c : Ω → Fin n → ℝ} (hc : Measurable c)
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
    (S : ℕ → Set Ω) (hScover : ∀ᵐ ω ∂P, ∃ m : ℕ, ω ∈ S m)
    (hSball : ∀ (m : ℕ) (ω : Ω), ω ∈ S m → ∀ s : ℝ, σ ω < ((s : ℝ) : WithTop ℝ) →
      ((s : ℝ) : WithTop ℝ) ≤ τ ω → ‖X s ω + c ω‖ ≤ (m : ℝ))
    (hSend : ∀ (m : ℕ) (ω : Ω), ω ∈ S m →
      ‖X (clipTime τ T ω) ω + c ω‖ ≤ (m : ℝ) ∧ ‖X (clipTime σ T ω) ω + c ω‖ ≤ (m : ℝ))
    (hSI : ∀ (m : ℕ) (p : Fin n) (k : Fin d)
      (hmg : Measurable (Function.uncurry fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s))
      (hpg : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s)
      (hqg : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      ∀ᵐ ω ∂P, ω ∈ S m →
        stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                    * H p k ω s) ω s
                - Probability.stopped σ (fun ω s =>
                    coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                      * H p k ω s) ω s)
            hmg hpg hqg T ω
          = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (fun ω s =>
              Probability.stopped τ
                  (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
                - Probability.stopped σ
                    (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
            (hmSc p k) (hpSc p k) (hqSc p k) T ω)
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
  refine ae_eq_of_ae_eq_on_exhausting hScover ?_
  intro m
  have hR0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hRlt : (m : ℝ) < 3 * ((m : ℝ) + 1) / 2 := by
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hXcm : Measurable (Function.uncurry fun ω s => X s ω + c ω) :=
    hXm.add (hc.comp measurable_fst)
  have hgC : ContDiff ℝ 2 (cutoffFun f ((m : ℝ) + 1)) := contDiff_cutoffFun hfC _
  have hgf : ∀ z, HasFDerivAt (cutoffFun f ((m : ℝ) + 1))
      (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)) z) z :=
    fun z => (differentiable_cutoffFun hfC _ z).hasFDerivAt
  have hgf' : ∀ z, HasFDerivAt (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))
      (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) z) z :=
    fun z => (differentiable_fderiv_cutoffFun hfC _ z).hasFDerivAt
  have hg'c : Continuous (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) :=
    continuous_fderiv_cutoffFun hfC _
  obtain ⟨K₁, hK₁n⟩ := exists_bound_fderiv_cutoffFun hfC hR0
  obtain ⟨K₂, hK₂0, hK₂n⟩ := exists_bound_fderiv_fderiv_cutoffFun hfC hR0
  have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hK₁n 0)
  have hK₁c : ∀ (p : Fin n) (z : Fin n → ℝ),
      |coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p z| ≤ K₁ :=
    fun p => abs_coordDeriv_le hK₁n p
  have hK₂c : ∀ (p q : Fin n) (z : Fin n → ℝ),
      |coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q z| ≤ K₂ :=
    fun p q => abs_coordDeriv₂_le hK₂n p q
  have hcut : ∀ (p : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * ((m : ℝ) + 1) / 2 →
      coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p z = coordDeriv f' p z := by
    intro p z hz
    rw [hf'eq]
    unfold coordDeriv
    rw [fderiv_cutoffFun (f := f) hR0 hz]
  have hcut₂ : ∀ (p q : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * ((m : ℝ) + 1) / 2 →
      coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q z
        = coordDeriv₂ f'' p q z := by
    intro p q z hz
    rw [hf''eq]
    unfold coordDeriv₂
    rw [fderiv_fderiv_cutoffFun (f := f) hR0 hz]
  have hcut₀ : ∀ z : Fin n → ℝ, ‖z‖ < 3 * ((m : ℝ) + 1) / 2 →
      cutoffFun f ((m : ℝ) + 1) z = f z := by
    intro z hz
    rw [cutoffFun, boxCut_eq_one hR0 hz.le, mul_one]
  have hmAg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω) * H p k ω s) :=
    fun p k => ((continuous_coordDeriv hg'c p).measurable.comp hXcm).mul (hHm p k)
  have hqAg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
          * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    refine energy_lt_top_of_abs_le_mul (c := K₁) hK₁0 (fun ω s => ?_) (hHs p k)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁c p _) (abs_nonneg _)
  have hmSg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s =>
          coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
            * H p k ω s) ω s
        - Probability.stopped σ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s) := fun p k =>
    measurable_uncurry_stopped_sub hσ hτ (hmAg p k)
  have hpSg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ (fun ω s =>
          coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
            * H p k ω s) ω s
        - Probability.stopped σ (fun ω s =>
            coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
              * H p k ω s) ω s := fun p k =>
    hpShift (coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p)
      (continuous_coordDeriv hg'c p) p k
  have hqSg : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun p k =>
    energy_stopped_sub_lt_top hσ hτ (hmAg p k) (hqAg p k)
  have hform := hbase (cutoffFun f ((m : ℝ) + 1)) (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))
    (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) K₁ K₂ hgC hgf hgf' hK₁c hK₂c
    hmSg hpSg hqSg
  have hSIall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d), ω ∈ S m →
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s =>
            Probability.stopped τ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s
              - Probability.stopped σ (fun ω s =>
                  coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
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
    exact hSI m p k (hmSg p k) (hpSg p k) (hqSg p k)
  filter_upwards [hform, hSIall] with ω hω hSIω hmem
  have hball : ∀ s : ℝ, σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω →
      ‖X s ω + c ω‖ < 3 * ((m : ℝ) + 1) / 2 := fun s h1 h2 =>
    lt_of_le_of_lt (hSball m ω hmem s h1 h2) hRlt
  have hendτ : ‖X (clipTime τ T ω) ω + c ω‖ < 3 * ((m : ℝ) + 1) / 2 :=
    lt_of_le_of_lt (hSend m ω hmem).1 hRlt
  have hendσ : ‖X (clipTime σ T ω) ω + c ω‖ < 3 * ((m : ℝ) + 1) / 2 :=
    lt_of_le_of_lt (hSend m ω hmem).2 hRlt
  have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * bdrift p ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * bdrift p ω s) ω s) ∂volume)
      = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * bdrift p ω s) ω s) ∂volume := by
    refine Finset.sum_congr rfl fun p _ => ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    refine stopped_sub_congr hστ fun h1 h2 => ?_
    rw [hcut p _ (hball s h1 h2)]
  have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s =>
              coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped σ (fun ω s =>
              coordDeriv₂ (fderiv ℝ (fderiv ℝ (cutoffFun f ((m : ℝ) + 1)))) p q (X s ω + c ω)
                * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume)
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        (Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) ω s
          - Probability.stopped σ (fun ω s => coordDeriv₂ f'' p q (X s ω + c ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s) ∂volume := by
    refine congrArg (fun x => 1 / 2 * x) ?_
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ => ?_
    refine stopped_sub_congr hστ fun h1 h2 => ?_
    rw [hcut₂ p q _ (hball s h1 h2)]
  have e2 : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          Probability.stopped τ (fun ω s =>
              coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                * H p k ω s) ω s
            - Probability.stopped σ (fun ω s =>
                coordDeriv (fderiv ℝ (cutoffFun f ((m : ℝ) + 1))) p (X s ω + c ω)
                  * H p k ω s) ω s)
        (hmSg p k) (hpSg p k) (hqSg p k) T ω)
      = ∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s =>
          Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s)
        (hmSc p k) (hpSc p k) (hqSc p k) T ω :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => hSIω p k hmem
  rw [← hcut₀ _ hendτ, ← hcut₀ _ hendσ, hω, e1, e2, e3]

/-- Two stopped increments whose integrands agree between the two stopping times and below a
third one have the same Itô integral on an event where that third time has not been reached. -/
theorem stochasticIntegralBrownian_stopped_sub_congr_of_mem
    (W : Brownian.BrownianMotion P) (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : Brownian.IsBrownianFiltration W ℱ')
    {σ τ ρ : Ω → WithTop ℝ} (hρ : MeasureTheory.IsStoppingTime ℱ' ρ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {A B : Ω → ℝ → ℝ}
    (hm₁ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ A ω s - Probability.stopped σ A ω s))
    (hp₁ : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ A ω s - Probability.stopped σ A ω s)
    (hq₁ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ A ω s - Probability.stopped σ A ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hm₂ : Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ B ω s - Probability.stopped σ B ω s))
    (hp₂ : Probability.ProgressivelyMeasurable ℱ' fun ω s =>
      Probability.stopped τ B ω s - Probability.stopped σ B ω s)
    (hq₂ : ∀ t : ℝ, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped τ B ω s - Probability.stopped σ B ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤)
    (hagree : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ ρ ω →
      σ ω < ((s : ℝ) : WithTop ℝ) → ((s : ℝ) : WithTop ℝ) ≤ τ ω → A ω s = B ω s)
    {T : ℝ} (hT : 0 < T) {Sset : Set Ω}
    (hS : ∀ ω ∈ Sset, ((T : ℝ) : WithTop ℝ) ≤ ρ ω) :
    ∀ᵐ ω ∂P, ω ∈ Sset →
      stochasticIntegralBrownian W ℱ' hℱ
          (fun ω s => Probability.stopped τ A ω s - Probability.stopped σ A ω s)
          hm₁ hp₁ hq₁ T ω
        = stochasticIntegralBrownian W ℱ' hℱ
          (fun ω s => Probability.stopped τ B ω s - Probability.stopped σ B ω s)
          hm₂ hp₂ hq₂ T ω := by
  have h := stochasticIntegralBrownian_congr_of_le ρ W ℱ' hℱ hρ hm₁ hp₁ hq₁ hm₂ hp₂ hq₂
    (fun ω s hs hle => stopped_sub_congr hστ fun h1 h2 => hagree ω s hs hle h1 h2) hT
  filter_upwards [h] with ω hω hmem
  exact hω (hS ω hmem)

end Localise

end LevyStochCalc.Ito.JumpFormulaCutoff
