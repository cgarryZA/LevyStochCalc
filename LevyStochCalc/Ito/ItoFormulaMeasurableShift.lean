/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaGridShiftClosed

/-!
# Itô's formula between two stopping times for a shift known at the earlier time

A random variable known at a stopping time, cut to the event that the time has already occurred by
a deterministic time, is measurable for the σ-algebra at that deterministic time; multiplying by
such a variable therefore preserves progressive measurability of a process that vanishes up to the
stopping time. Reading an integrand along a mark taking finitely many values splits the increment
of the integrand between two ordered stopping times over the values of the mark, so that increment
is progressively measurable as soon as the mark is known at the earlier time. The dyadic lattice
points below a bounded random vector known at the earlier stopping time form such marks and
converge to it, and truncating a random vector on the event that its norm exceeds a level produces
bounded vectors eventually equal to it, so Itô's formula for the increment holds for a shift that
is merely known at the earlier stopping time.

## Main statements

* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stoppingTimeWeight_mul` — a random variable
  known at a stopping time times a progressively measurable process vanishing up to that time is
  progressively measurable.
* `LevyStochCalc.Brownian.Ito.progressivelyMeasurable_stopped_sub_of_measurableShift` — the
  increment between two ordered stopping times of an integrand read along a mark taking finitely
  many values and known at the earlier time is progressively measurable.
* `LevyStochCalc.Brownian.Ito.exists_simpleShift_approx_measurableSpace` — a bounded random vector
  known at a stopping time is a pointwise limit of random vectors taking finitely many values and
  known at that stopping time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_boundedShift` — Itô's formula for the increment of
  a path between two stopping times, for a function translated by a bounded random vector known at
  the earlier time.
* `LevyStochCalc.Brownian.Ito.itoFormula_between_measurableShift` — the same for a function
  translated by a random vector known at the earlier time and subject to no bound.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Weight

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A random variable known at a stopping time, cut to the event that the time has occurred by a
deterministic time, is measurable for the σ-algebra at that deterministic time. -/
theorem measurable_indicator_le_of_measurableSpace {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) {V : Ω → ℝ}
    (hV : Measurable[hσ.measurableSpace] V) (t : ℝ) :
    Measurable[ℱ t] (Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V) := by
  intro B hB
  have hA : MeasurableSet[ℱ t] {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} := hσ t
  have hVB : MeasurableSet[ℱ t] (V ⁻¹' B ∩ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}) :=
    ((hσ.measurableSet (V ⁻¹' B)).mp (hV hB)).2 t
  by_cases h0 : (0 : ℝ) ∈ B
  · have hset : Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V ⁻¹' B
        = (V ⁻¹' B ∩ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)})
          ∪ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω
      by_cases hω : ω ∈ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}
      · simp [hω]
      · simp [hω, h0]
    rw [hset]
    exact hVB.union hA.compl
  · have hset : Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V ⁻¹' B
        = V ⁻¹' B ∩ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} := by
      ext ω
      by_cases hω : ω ∈ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}
      · simp [hω]
      · simp [hω, h0]
    rw [hset]
    exact hVB

/-- A random variable known at a stopping time, times a progressively measurable process that
vanishes up to that stopping time, is progressively measurable. -/
theorem progressivelyMeasurable_stoppingTimeWeight_mul {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) {V : Ω → ℝ}
    (hV : Measurable[hσ.measurableSpace] V) {D : Ω → ℝ → ℝ}
    (hpD : Probability.ProgressivelyMeasurable ℱ D)
    (hD0 : ∀ (ω : Ω) (s : ℝ), ((s : ℝ) : WithTop ℝ) ≤ σ ω → D ω s = 0) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => V ω * D ω s := by
  intro t
  have hVt : Measurable[ℱ t] (Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V) :=
    measurable_indicator_le_of_measurableSpace hσ hV t
  have hDt := hpD t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => V p.1 * D p.1 s) p.2)
      = fun p : Ω × ℝ => Set.indicator {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)} V p.1
          * (Set.Iic t).indicator (D p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
      by_cases hω : p.1 ∈ {ω | σ ω ≤ ((t : ℝ) : WithTop ℝ)}
      · rw [Set.indicator_of_mem hω]
      · have h1 : ((p.2 : ℝ) : WithTop ℝ) ≤ ((t : ℝ) : WithTop ℝ) := by
          exact_mod_cast Set.mem_Iic.mp hp
        have h2 : ((t : ℝ) : WithTop ℝ) ≤ σ p.1 := (not_le.mp hω).le
        rw [Set.indicator_of_notMem hω, zero_mul, hD0 p.1 p.2 (h1.trans h2), mul_zero]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, mul_zero]
  rw [key]
  letI : MeasurableSpace Ω := ℱ t
  exact ((hVt.comp measurable_fst).stronglyMeasurable).mul hDt

end Weight

section MarkDecomposition

variable {Ω : Type u} {α : Type*}

/-- The increment between two stopping times of an integrand read along a mark taking finitely many
values is the sum, over the values of the mark, of the indicator of the level set of the value
times the increment of the integrand at that value. -/
theorem stopped_sub_eq_sum_indicator {σ τ : Ω → WithTop ℝ} {c : Ω → α} {Vs : Finset α}
    (hcVs : ∀ ω, c ω ∈ Vs) (K : α → Ω → ℝ → ℝ) (Kc : Ω → ℝ → ℝ)
    (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    (fun (ω : Ω) (s : ℝ) => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
      = fun (ω : Ω) (s : ℝ) => ∑ v ∈ Vs, Set.indicator {ω | c ω = v} (fun _ => (1 : ℝ)) ω
          * (Probability.stopped τ (K v) ω s - Probability.stopped σ (K v) ω s) := by
  funext ω s
  have hsum := Finset.sum_eq_single_of_mem (c ω) (hcVs ω)
    (f := fun v => Set.indicator {ω | c ω = v} (fun _ => (1 : ℝ)) ω
      * (Probability.stopped τ (K v) ω s - Probability.stopped σ (K v) ω s))
    (fun v _ hv => by rw [Set.indicator_of_notMem fun hmem => hv hmem.symm, zero_mul])
  rw [hsum, Set.indicator_of_mem (show ω ∈ {ω' | c ω' = c ω} from rfl), one_mul]
  unfold LevyStochCalc.Probability.stopped
  rw [hKc]

end MarkDecomposition

section SimpleMark

variable {Ω : Type u} [MeasurableSpace Ω] {α : Type*} [MeasurableSpace α]
  [MeasurableSingletonClass α]

/-- The increment between two ordered stopping times of an integrand read along a mark taking
finitely many values and known at the earlier stopping time is progressively measurable. -/
theorem progressivelyMeasurable_stopped_sub_of_measurableShift
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {σ τ : Ω → WithTop ℝ}
    (hσ : MeasureTheory.IsStoppingTime ℱ σ) (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hστ : ∀ ω, σ ω ≤ τ ω) {c : Ω → α} (hc : Measurable[hσ.measurableSpace] c)
    {Vs : Finset α} (hcVs : ∀ ω, c ω ∈ Vs)
    (K : α → Ω → ℝ → ℝ) (hpK : ∀ v, Probability.ProgressivelyMeasurable ℱ (K v))
    {Kc : Ω → ℝ → ℝ} (hKc : ∀ ω s, Kc ω s = K (c ω) ω s) :
    Probability.ProgressivelyMeasurable ℱ fun ω s =>
      Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s := by
  rw [stopped_sub_eq_sum_indicator hcVs K Kc hKc]
  refine progressivelyMeasurable_finsetSum ℱ
    (fun (v : α) (ω : Ω) (s : ℝ) => Set.indicator {ω | c ω = v} (fun _ => (1 : ℝ)) ω
      * (Probability.stopped τ (K v) ω s - Probability.stopped σ (K v) ω s))
    (fun v => ?_) Vs
  have hset : MeasurableSet[hσ.measurableSpace] {ω | c ω = v} := hc (measurableSet_singleton v)
  exact progressivelyMeasurable_stoppingTimeWeight_mul hσ (measurable_const.indicator hset)
    (progressivelyMeasurable_stopped_sub hσ hτ (hpK v))
    fun ω s hs => stopped_sub_stopped_eq_zero hστ _ ω hs

end SimpleMark

section TwoPieceMark

variable {Ω : Type u}

/-- The increment between two stopping times of an integrand agreeing with one integrand on a set
and with another off it splits over that set. -/
theorem stopped_sub_eq_indicator_add {σ τ : Ω → WithTop ℝ} {A : Set Ω}
    (K K₀ Kc : Ω → ℝ → ℝ) (hin : ∀ ω ∈ A, ∀ s, Kc ω s = K ω s)
    (hout : ∀ ω ∉ A, ∀ s, Kc ω s = K₀ ω s) :
    (fun (ω : Ω) (s : ℝ) => Probability.stopped τ Kc ω s - Probability.stopped σ Kc ω s)
      = fun (ω : Ω) (s : ℝ) => A.indicator (fun _ => (1 : ℝ)) ω
            * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)
          + Aᶜ.indicator (fun _ => (1 : ℝ)) ω
            * (Probability.stopped τ K₀ ω s - Probability.stopped σ K₀ ω s) := by
  funext ω s
  by_cases hω : ω ∈ A
  · rw [Set.indicator_of_mem hω, Set.indicator_of_notMem (by simp [hω]), one_mul, zero_mul,
      add_zero]
    unfold LevyStochCalc.Probability.stopped
    rw [hin ω hω s]
  · rw [Set.indicator_of_notMem hω, Set.indicator_of_mem hω, zero_mul, one_mul, zero_add]
    unfold LevyStochCalc.Probability.stopped
    rw [hout ω hω s]

end TwoPieceMark

section Approximation

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A bounded random vector known at a stopping time is the pointwise limit of random vectors
taking finitely many values and known at that stopping time. -/
theorem exists_simpleShift_approx_measurableSpace {n : ℕ} {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ) {c : Ω → Fin n → ℝ}
    (hc : Measurable[hσ.measurableSpace] c) {M : ℝ} (hcb : ∀ ω, ‖c ω‖ ≤ M) :
    ∃ (cm : ℕ → Ω → Fin n → ℝ) (Vs : ℕ → Finset (Fin n → ℝ)),
      (∀ m, Measurable[hσ.measurableSpace] (cm m)) ∧ (∀ m ω, cm m ω ∈ Vs m) ∧
      ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (𝓝 (c ω)) := by
  classical
  have hcoord : ∀ (ω : Ω) (i : Fin n), |c ω i| ≤ M := by
    intro ω i
    calc |c ω i| = ‖c ω i‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖c ω‖ := norm_le_pi_norm (c ω) i
      _ ≤ M := hcb ω
  refine ⟨fun m ω => dyadicShift m (c ω), fun m =>
    (Fintype.piFinset fun _ : Fin n =>
        Finset.Icc (-(⌈(2 : ℝ) ^ m * M⌉ + 1)) (⌈(2 : ℝ) ^ m * M⌉ + 1)).image
      fun g : Fin n → ℤ => fun i => (g i : ℝ) / (2 : ℝ) ^ m,
    fun m => measurable_dyadicShift.comp hc, ?_, ?_⟩
  · intro m ω
    refine Finset.mem_image.mpr ⟨fun i => ⌊(2 : ℝ) ^ m * c ω i⌋, ?_, rfl⟩
    exact Fintype.mem_piFinset.mpr fun i => floor_mul_mem_Icc m (hcoord ω i)
  · intro ω
    have hhalf : Filter.Tendsto (fun m : ℕ => ((1 : ℝ) / 2) ^ m) Filter.atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hg : Filter.Tendsto (fun m : ℕ => (1 : ℝ) / 2 ^ m) Filter.atTop (𝓝 0) := by
      simpa [div_pow] using hhalf
    refine tendsto_pi_nhds.2 fun i => ?_
    rw [← tendsto_sub_nhds_zero_iff]
    have hb : ∀ m : ℕ, ‖dyadicShift m (c ω) i - c ω i‖ ≤ 1 / 2 ^ m := by
      intro m
      rw [Real.norm_eq_abs]
      exact abs_dyadicShift_sub_le m (c ω) i
    exact squeeze_zero_norm hb hg

end Approximation

section MeasurableShift

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

/-- **Itô's formula for the increment of a path between two stopping times of unrestricted range,
for a function translated by a bounded random vector known at the earlier time.** -/
theorem itoFormula_between_boundedShift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, Multidim.MultidimBrownianMotion.CrossWitness W ℱ' j)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hHQ : ∀ (p q : Fin n) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖∑ k : Fin d, H p k ω s * H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
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
    (hK₂ : ∀ (p q : Fin n) (z : Fin n → ℝ), |coordDeriv₂ f'' p q z| ≤ K₂)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
    {M : ℝ} (hcb : ∀ ω, ‖c ω‖ ≤ M)
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
  classical
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := h.measurable_uncurry
  have hcmeas : Measurable c := hc.mono hσ.measurableSpace_le le_rfl
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hpG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s := fun v p k =>
    (h.progressivelyMeasurable_comp (φ := fun z => coordDeriv f' p (z + v))
      ((continuous_coordDeriv hf'c p).comp (continuous_id.add continuous_const))).mul (hHp p k)
  obtain ⟨cm, Vs, hcmσ, hcmVs, hlim⟩ := exists_simpleShift_approx_measurableSpace hσ hc hcb
  have hcmm : ∀ m, Measurable (cm m) := fun m => (hcmσ m).mono hσ.measurableSpace_le le_rfl
  have hmGcm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) := fun m p k =>
    ((continuous_coordDeriv hf'c p).measurable.comp
      (hXm.add ((hcmm m).comp measurable_fst))).mul (hHm p k)
  have hqGcm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖coordDeriv f' p (X s ω + cm m ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro m p k
    refine energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hHs p k)
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hmScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s) :=
    fun m p k => measurable_uncurry_stopped_sub hσ hτ (hmGcm m p k)
  have hpScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s :=
    fun m p k => progressivelyMeasurable_stopped_sub_of_measurableShift hσ hτ hστ (hcmσ m)
      (hcmVs m) (fun v ω s => coordDeriv f' p (X s ω + v) * H p k ω s) (fun v => hpG v p k)
      (Kc := fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) fun _ _ => rfl
  have hqScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun m p k => energy_stopped_sub_lt_top hσ hτ (hmGcm m p k) (hqGcm m p k)
  have hbint : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (fun s => bdrift p ω s) (Set.Ioc (0 : ℝ) T) volume :=
    MeasureTheory.ae_all_iff.mpr fun p => ae_integrableOn_Ioc_of_energy (hbm p) (hbq p T hT)
  have hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume :=
    ae_integrableOn_Ioc_sum_mul hHm fun p k => hHs p k T hT
  exact itoFormula_between_generalShift W ℱ' hcoord hXm hHm hHs hbm hσ hτ hfC hf hf' hK₁ hK₂ hT
    hcmeas hcmm hlim hbint hQint hmSc hpSc hqSc hmScm hpScm hqScm fun m =>
      itoFormula_between_gridShift_of_simpleShift W ℱ' hcoord h 𝒲 hℱ0 hnull hX₀ hHQ hbm hbp hbq
        hσ hτ hστ hσ0 hτ0 hfC hf hf' hK₁ hK₂ hT (hcmσ m) (hcmVs m) (hmScm m) (hpScm m) (hqScm m)

/-- **Itô's formula for the increment of a path between two stopping times of unrestricted range,
for a function translated by a random vector known at the earlier time.** -/
theorem itoFormula_between_measurableShift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, Multidim.MultidimBrownianMotion.CrossWitness W ℱ' j)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hHQ : ∀ (p q : Fin n) (t : ℝ), 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖∑ k : Fin d, H p k ω s * H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
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
    (hK₂ : ∀ (p q : Fin n) (z : Fin n → ℝ), |coordDeriv₂ f'' p q z| ≤ K₂)
    {T : ℝ} (hT : 0 < T)
    {c : Ω → Fin n → ℝ} (hc : Measurable[hσ.measurableSpace] c)
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
  classical
  have hXm : Measurable (Function.uncurry fun ω s => X s ω) := h.measurable_uncurry
  have hcmeas : Measurable c := hc.mono hσ.measurableSpace_le le_rfl
  have hf'c : Continuous f' := Differentiable.continuous fun z => (hf' z).differentiableAt
  have hpG : ∀ (v : Fin n → ℝ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X s ω + v) * H p k ω s := fun v p k =>
    (h.progressivelyMeasurable_comp (φ := fun z => coordDeriv f' p (z + v))
      ((continuous_coordDeriv hf'c p).comp (continuous_id.add continuous_const))).mul (hHp p k)
  obtain ⟨cm, hcmdef⟩ : ∃ cm : ℕ → Ω → Fin n → ℝ,
      ∀ (m : ℕ) (ω : Ω), cm m ω = if ‖c ω‖ ≤ (m : ℝ) then c ω else 0 :=
    ⟨fun m ω => if ‖c ω‖ ≤ (m : ℝ) then c ω else 0, fun _ _ => rfl⟩
  have hA : ∀ m : ℕ, MeasurableSet[hσ.measurableSpace] {ω | ‖c ω‖ ≤ (m : ℝ)} := fun m =>
    hc (measurableSet_le measurable_norm measurable_const)
  have hcmσ : ∀ m, Measurable[hσ.measurableSpace] (cm m) := by
    intro m
    have hfun : cm m = fun ω => if ‖c ω‖ ≤ (m : ℝ) then c ω else 0 := funext (hcmdef m)
    rw [hfun]
    exact Measurable.ite (hA m) hc measurable_const
  have hcmm : ∀ m, Measurable (cm m) := fun m => (hcmσ m).mono hσ.measurableSpace_le le_rfl
  have hcmb : ∀ (m : ℕ) (ω : Ω), ‖cm m ω‖ ≤ (m : ℝ) := by
    intro m ω
    rw [hcmdef m ω]
    by_cases hω : ‖c ω‖ ≤ (m : ℝ)
    · rwa [if_pos hω]
    · rw [if_neg hω, norm_zero]
      exact Nat.cast_nonneg m
  have hlim : ∀ ω, Filter.Tendsto (fun m => cm m ω) Filter.atTop (𝓝 (c ω)) := by
    intro ω
    have hev : (fun _ : ℕ => c ω) =ᶠ[Filter.atTop] fun m => cm m ω := by
      refine Filter.eventually_atTop.2 ⟨⌈‖c ω‖⌉₊, fun m hm => ?_⟩
      have hle : ‖c ω‖ ≤ (m : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hm)
      change c ω = cm m ω
      rw [hcmdef m ω, if_pos hle]
    exact Filter.Tendsto.congr' hev tendsto_const_nhds
  have hmGcm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) := fun m p k =>
    ((continuous_coordDeriv hf'c p).measurable.comp
      (hXm.add ((hcmm m).comp measurable_fst))).mul (hHm p k)
  have hqGcm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖coordDeriv f' p (X s ω + cm m ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro m p k
    refine energy_lt_top_of_abs_le_mul (le_trans (abs_nonneg _) (hK₁ p 0)) ?_ (hHs p k)
    intro ω s
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hK₁ p _) (abs_nonneg _)
  have hmScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry fun ω s =>
      Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
        - Probability.stopped σ
            (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s) :=
    fun m p k => measurable_uncurry_stopped_sub hσ hτ (hmGcm m p k)
  have hpScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ' fun ω s =>
        Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
          - Probability.stopped σ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s := by
    intro m p k
    rw [stopped_sub_eq_indicator_add (A := {ω | ‖c ω‖ ≤ (m : ℝ)})
      (fun ω s => coordDeriv f' p (X s ω + c ω) * H p k ω s)
      (fun ω s => coordDeriv f' p (X s ω + 0) * H p k ω s)
      (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s)
      (fun ω hω s => by
        have hω' : ‖c ω‖ ≤ (m : ℝ) := hω
        rw [hcmdef m ω, if_pos hω'])
      (fun ω hω s => by
        have hω' : ¬‖c ω‖ ≤ (m : ℝ) := hω
        rw [hcmdef m ω, if_neg hω'])]
    refine Probability.ProgressivelyMeasurable.add ?_ ?_
    · exact progressivelyMeasurable_stoppingTimeWeight_mul hσ
        (measurable_const.indicator (hA m)) (hpSc p k)
        fun ω s hs => stopped_sub_stopped_eq_zero hστ _ ω hs
    · exact progressivelyMeasurable_stoppingTimeWeight_mul hσ
        (measurable_const.indicator (hA m).compl)
        (progressivelyMeasurable_stopped_sub hσ hτ (hpG 0 p k))
        fun ω s hs => stopped_sub_stopped_eq_zero hστ _ ω hs
  have hqScm : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (t : ℝ), 0 < t →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped τ
              (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s
            - Probability.stopped σ
                (fun ω s => coordDeriv f' p (X s ω + cm m ω) * H p k ω s) ω s‖₊ : ℝ≥0∞) ^ 2
          ∂volume ∂P < ⊤ :=
    fun m p k => energy_stopped_sub_lt_top hσ hτ (hmGcm m p k) (hqGcm m p k)
  have hbint : ∀ᵐ ω ∂P, ∀ p : Fin n, MeasureTheory.IntegrableOn
      (fun s => bdrift p ω s) (Set.Ioc (0 : ℝ) T) volume :=
    MeasureTheory.ae_all_iff.mpr fun p => ae_integrableOn_Ioc_of_energy (hbm p) (hbq p T hT)
  have hQint : ∀ᵐ ω ∂P, ∀ p q : Fin n, MeasureTheory.IntegrableOn
      (fun s => ∑ k : Fin d, H p k ω s * H q k ω s) (Set.Ioc (0 : ℝ) T) volume :=
    ae_integrableOn_Ioc_sum_mul hHm fun p k => hHs p k T hT
  exact itoFormula_between_generalShift W ℱ' hcoord hXm hHm hHs hbm hσ hτ hfC hf hf' hK₁ hK₂ hT
    hcmeas hcmm hlim hbint hQint hmSc hpSc hqSc hmScm hpScm hqScm fun m =>
      itoFormula_between_boundedShift W ℱ' hcoord h 𝒲 hℱ0 hnull hX₀ hHQ hbm hbp hbq hσ hτ hστ
        hσ0 hτ0 hfC hf hf' hK₁ hK₂ hT (hcmσ m) (hcmb m) (hmScm m) (hpScm m) (hqScm m)

end MeasurableShift

end LevyStochCalc.Brownian.Ito
