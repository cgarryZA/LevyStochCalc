/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaGridShift
import LevyStochCalc.Ito.GridStopTruncated

/-!
# Itô's formula between two stopping times for a simple shift known at the earlier time

The upward grid discretisations of two ordered stopping times, truncated at the horizon, take
finitely many grid values strictly below the horizon or the value `⊤`, and a random vector known
at the earlier stopping time is known at each of its discretisations. For a function translated
by a random vector taking finitely many values, Itô's formula for the increment between the
truncated discretisations is therefore the identity for a simple shift; it transfers to the
untruncated discretisations and passes to the limit in the mesh.

## Main statements

* `LevyStochCalc.Brownian.Ito.gridStopTrunc_eq_or_top` — for every mesh, the truncated grid
  discretisation takes a grid value strictly below the horizon, or the value `⊤`.
* `LevyStochCalc.Brownian.Ito.measurableSet_cell_gridStop` — a mark known at a stopping time
  has cells measurable at the deterministic times its grid discretisation takes.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_gridStop_simple` — the
  increment between the grid discretisations of an integrand read along a simple mark known at
  the earlier stopping time is progressively measurable.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_gridShift_of_simpleShift` — Itô's formula for
  the increment of a path between two stopping times of unrestricted range, for a function
  translated by a random vector taking finitely many values and known at the earlier time.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section FiniteRange

variable {Ω : Type u}

theorem gridPt_image_succ_nonneg {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ (Finset.range (m + 1)).image (gridPt T m), 0 ≤ a := by
  intro a ha
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
  exact gridPt_nonneg hT.le m k

theorem gridPt_filter_nonneg {T : ℝ} (hT : 0 < T) (m : ℕ) :
    ∀ a ∈ ((Finset.range (m + 1)).image (gridPt T m)).filter (fun a => a < T), 0 ≤ a :=
  fun a ha => gridPt_image_succ_nonneg hT m a (Finset.mem_filter.mp ha).1

theorem gridPt_filter_lt (T : ℝ) (m : ℕ) :
    ∀ a ∈ ((Finset.range (m + 1)).image (gridPt T m)).filter (fun a => a < T), a < T :=
  fun _ ha => (Finset.mem_filter.mp ha).2

/-- For every mesh, the truncated grid discretisation takes one of the grid values strictly
below the horizon, or the value `⊤`. -/
theorem gridStopTrunc_eq_or_top (σ : Ω → WithTop ℝ) (T : ℝ) (m : ℕ) (ω : Ω) :
    (∃ a ∈ ((Finset.range (m + 1)).image (gridPt T m)).filter (fun a => a < T),
        gridStopTrunc σ T m ω = ((a : ℝ) : WithTop ℝ))
      ∨ gridStopTrunc σ T m ω = ⊤ := by
  rcases gridStop_eq_or_top σ T m ω with ⟨a, ha, hae⟩ | htop
  · by_cases haT : a < T
    · refine Or.inl ⟨a, Finset.mem_filter.mpr ⟨ha, haT⟩, ?_⟩
      have hlt : gridStop σ T m ω < ((T : ℝ) : WithTop ℝ) := by
        rw [hae]
        exact_mod_cast haT
      rw [gridStopTrunc_of_lt σ T m hlt, hae]
    · refine Or.inr (gridStopTrunc_of_le σ T m ?_)
      rw [hae]
      exact_mod_cast not_lt.mp haT
  · exact Or.inr (gridStopTrunc_of_le σ T m (by rw [htop]; exact le_top))

end FiniteRange

section Cells

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ : Ω → WithTop ℝ}

/-- The cells of a mark known at a stopping time are measurable at the deterministic times the
upward grid discretisation of that stopping time takes. -/
theorem measurableSet_cell_gridStop (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (T : ℝ) (m : ℕ) (a : ℝ) (v : α) :
    MeasurableSet[ℱ a] {ω | gridStop σ T m ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} :=
  measurableSet_cell_of_measurable (isStoppingTime_gridStop σ hσ T m)
    (measurable_gridStop_measurableSpace hσ hc T m) a v

/-- The cells of a mark known at a stopping time are measurable at the deterministic times the
truncated grid discretisation of that stopping time takes. -/
theorem measurableSet_cell_gridStopTrunc (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → α}
    (hc : Measurable[hσ.measurableSpace] c) (T : ℝ) (m : ℕ) (a : ℝ) (v : α) :
    MeasurableSet[ℱ a] {ω | gridStopTrunc σ T m ω = ((a : ℝ) : WithTop ℝ) ∧ c ω = v} :=
  measurableSet_cell_of_measurable (isStoppingTime_gridStopTrunc hσ T m)
    (hc.mono (measurableSpace_le_gridStopTrunc hσ T m) le_rfl) a v

end Cells

section Progressive

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α] {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}

/-- The increment between the upward grid discretisations of two ordered stopping times of an
integrand read along a simple mark known at the earlier one is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_gridStop_simple
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) {c : Ω → α} (hc : Measurable[hσ.measurableSpace] c)
    {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs) {T : ℝ} (hT : 0 < T) (m : ℕ)
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStop τ T m) Kc ω s
        - Probability.stopped (gridStop σ T m) Kc ω s :=
  progressivelyMeasurable_stopped_sub_simple (isStoppingTime_gridStop σ hσ T m)
    (isStoppingTime_gridStop τ hτ T m) (gridStop_mono hστ T m) hcVs
    (gridPt_image_succ_nonneg hT m) (gridStop_eq_or_top σ T m)
    (fun a _ v _ => measurableSet_cell_gridStop hσ hc T m a v) K hpK hKc

/-- The increment between the truncated grid discretisations of two ordered stopping times of
an integrand read along a simple mark known at the earlier one is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_gridStopTrunc_simple
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) {c : Ω → α} (hc : Measurable[hσ.measurableSpace] c)
    {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs) {T : ℝ} (hT : 0 < T) (m : ℕ)
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped (gridStopTrunc τ T m) Kc ω s
        - Probability.stopped (gridStopTrunc σ T m) Kc ω s :=
  progressivelyMeasurable_stopped_sub_simple (isStoppingTime_gridStopTrunc hσ T m)
    (isStoppingTime_gridStopTrunc hτ T m) (gridStopTrunc_mono hστ T m) hcVs
    (gridPt_filter_nonneg hT m) (gridStopTrunc_eq_or_top σ T m)
    (fun a _ v _ => measurableSet_cell_gridStopTrunc hσ hc T m a v) K hpK hKc

end Progressive

section GridShiftClosed

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **Itô's formula for the increment of a path between two stopping times of unrestricted
range, for a function translated by a random vector taking finitely many values and known at the
earlier time.** -/
theorem itoFormula_between_gridShift_of_simpleShift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ' σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ' τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    (hσ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ σ ω)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f) (hf : ∀ z, HasFDerivAt f (f' z) z)
    (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    {K₁ K₂ : ℝ} (hK₁ : ∀ (p : Fin n) (z : Fin n → ℝ), |coordDeriv f' p z| ≤ K₁)
    (hK₂ : ∀ (p q : Fin n) (z : Fin n → ℝ) (ω : Ω) (s : ℝ),
      |coordDeriv₂ f'' p q z| * |∑ k : Fin d, H p k ω s * H q k ω s|
        ≤ K₂ * |∑ k : Fin d, H p k ω s * H q k ω s|)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
    {Vs : Finset (Fin n → ℝ)} (hcVs : ∀ ω, c ω ∈ Vs)
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
          ∂volume ∂P < ⊤) :
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
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := h.measurable_uncurry
  have hXc : ∀ ω, Continuous fun s : ℝ => X s ω := h.continuous_path
  have hcm : Measurable c := hc.mono hσ.measurableSpace_le le_rfl
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hf''c : Continuous f'' := by
    have h1 : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
    have h2 : f'' = fderiv ℝ f' := funext fun z => (hf' z).fderiv.symm
    rw [h2, h1]
    exact ((hfC.fderiv_right (m := 1) (by norm_num)).fderiv_right
      (m := 0) (by norm_num)).continuous
  -- admissibility of the integrands translated by a fixed vector
  have hmG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s) := fun v p k =>
    ((continuous_coordDeriv hf'c p).measurable.comp (hXm.add_const v)).mul (hHm p k)
  have hpG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s := fun v p k =>
    (h.progressivelyMeasurable_comp (φ := fun z => coordDeriv f' p (z + v))
      ((continuous_coordDeriv hf'c p).comp (continuous_id.add continuous_const))).mul (hHp p k)
  have hqG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖coordDeriv f' p (X s ω + v) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro v p k
    refine energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hHs p k)
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hmD : ∀ (v : Fin n → ℝ) (p : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + v) * bdrift p ω s) := fun v p =>
    ((continuous_coordDeriv hf'c p).measurable.comp (hXm.add_const v)).mul (hbm p)
  have hqD : ∀ (v : Fin n → ℝ) (p : Fin n) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖coordDeriv f' p (X s ω + v) * bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro v p
    refine energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hbq p)
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hmQ : ∀ (v : Fin n → ℝ) (p q : Fin n), Measurable (Function.uncurry
      fun ω s => coordDeriv₂ f'' p q (X s ω + v) * ∑ k : Fin d, H p k ω s * H q k ω s) := by
    intro v p q
    refine ((continuous_coordDeriv₂ hf''c p q).measurable.comp (hXm.add_const v)).mul ?_
    exact Finset.measurable_sum _ fun k _ => (hHm p k).mul (hHm q k)
  -- admissibility of the integrands translated by the random vector
  have hXcm : Measurable (Function.uncurry fun ω s => X s ω + c ω) :=
    hXm.add (hcm.comp measurable_fst)
  have hmGc : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) :=
    fun p k => ((continuous_coordDeriv hf'c p).measurable.comp hXcm).mul (hHm p k)
  have hqGc : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖coordDeriv f' p (X s ω + c ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    refine energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hHs p k)
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  -- the increments between the grid discretisations
  have hmSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStop τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStop σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s) :=
    fun m p k => measurable_uncurry_stopped_sub (isStoppingTime_gridStop σ hσ T m)
      (isStoppingTime_gridStop τ hτ T m) (hmGc p k)
  have hpSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped (gridStop τ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped (gridStop σ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s :=
    fun m p k => progressivelyMeasurable_stopped_sub_gridStop_simple hσ hτ hστ hc hcVs hT m
      (fun v ω s => coordDeriv f' p (X s ω + v) * H p k ω s) (fun v => hpG v p k)
      (Kc := fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) (fun _ _ => rfl)
  have hqSm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStop σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun m p k => energy_stopped_sub_lt_top (isStoppingTime_gridStop σ hσ T m)
      (isStoppingTime_gridStop τ hτ T m) (hmGc p k) (hqGc p k)
  -- the increments between the truncated grid discretisations
  have hmSt : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped (gridStopTrunc τ T m)
          (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
        - Probability.stopped (gridStopTrunc σ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s) :=
    fun m p k => measurable_uncurry_stopped_sub (isStoppingTime_gridStopTrunc hσ T m)
      (isStoppingTime_gridStopTrunc hτ T m) (hmGc p k)
  have hpSt : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped (gridStopTrunc τ T m)
            (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
          - Probability.stopped (gridStopTrunc σ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s :=
    fun m p k => progressivelyMeasurable_stopped_sub_gridStopTrunc_simple hσ hτ hστ hc hcVs
      hT m (fun v ω s => coordDeriv f' p (X s ω + v) * H p k ω s) (fun v => hpG v p k)
      (Kc := fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) (fun _ _ => rfl)
  have hqSt : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStopTrunc τ T m)
              (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s
            - Probability.stopped (gridStopTrunc σ T m)
                (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun m p k => energy_stopped_sub_lt_top (isStoppingTime_gridStopTrunc hσ T m)
      (isStoppingTime_gridStopTrunc hτ T m) (hmGc p k) (hqGc p k)
  -- window integrability of the drift and of the quadratic covariation density
  have hbint : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (fun s => bdrift p ω s) (Set.Ioc (0 : ℝ) T) volume :=
    MeasureTheory.ae_all_iff.mpr fun p => ae_integrableOn_Ioc_of_energy (hbm p) (hbq p T hT)
  have hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume :=
    ae_integrableOn_Ioc_sum_mul hHm fun p k => hHs p k T hT
  have hQintv : ∀ v : Fin n → ℝ, ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => coordDeriv₂ f'' p q (X s ω + v) * ∑ k : Fin d, H p k ω s * H q k ω s)
      (Set.Ioc (0 : ℝ) T) volume := by
    intro v
    filter_upwards [hQint] with ω hω p q
    refine MeasureTheory.Integrable.mono ((hω p q).const_mul K₂)
      (Measurable.of_uncurry_left (hmQ v p q)).aestronglyMeasurable ?_
    filter_upwards with s
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
    exact (hK₂ p q _ ω s).trans (mul_le_mul_of_nonneg_right (le_abs_self K₂) (abs_nonneg _))
  refine itoFormula_between_gridShift W ℱ' hcoord hXm hXc hHm hHs hbm hσ hτ hσ0 hτ0 hfC hf hf'
    hK₁ hK₂ hT hcm hbint hQint hmSc hpSc hqSc hmSm hpSm hqSm fun m => ?_
  refine itoFormula_between_gridStop_of_gridStopTrunc W ℱ' hcoord hT m (hmSt m) (hpSt m)
    (hqSt m) (hmSm m) (hpSm m) (hqSm m) ?_
  exact itoFormula_between_simpleShift W ℱ' hcoord h hℱ0 hnull hX₀ hbm hbp hbq
    (isStoppingTime_gridStopTrunc hσ T m) (isStoppingTime_gridStopTrunc hτ T m)
    (gridStopTrunc_mono hστ T m) (zero_le_gridStopTrunc hσ0 T m) (zero_le_gridStopTrunc hτ0 T m)
    hfC hf hf' hmG hpG hqG hmD hqD hmQ hT hQintv hcVs (gridPt_filter_nonneg hT m)
    (gridPt_filter_lt T m) (gridStopTrunc_eq_or_top σ T m)
    (fun a _ v _ => measurableSet_cell_gridStopTrunc hσ hc T m a v) (hmSt m) (hpSt m) (hqSt m)

end GridShiftClosed

end LevyStochCalc.Brownian.Ito
