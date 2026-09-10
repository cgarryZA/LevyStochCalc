/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaStopped
import LevyStochCalc.Brownian.ItoLocality

/-!
# Itô's formula for a translated function

Translating the argument of a twice continuously differentiable function by a fixed vector
translates its Fréchet derivatives and its partial derivatives by the same vector, so Itô's
formula along a stopped path holds for the translate with every derivative read at the
translated path.

A weight that is known at a deterministic time and vanishes off the event that a stopping time
equals that time passes inside the Itô integral of an integrand that vanishes up to that
stopping time: the integrand is then carried by the window between that time and the horizon,
and the increment removed by the window is invisible on the event.

## Main statements

* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_shift` — Itô's formula along a stopped path for
  a function translated by a fixed vector.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd` — a bounded weight known at
  a deterministic time, cut to the event that a stopping time equals it, passes inside the Itô
  integral of an integrand vanishing up to that stopping time.
* `LevyStochCalc.Brownian.Ito.mul_stochasticIntegralBrownian_hitInd_stopped_sub` — the same for
  the increment of an integrand between two stopping times.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section Translate

variable {n : ℕ}

/-- The translate of a twice continuously differentiable function is twice continuously
differentiable. -/
theorem contDiff_shiftArg {f : (Fin n → ℝ) → ℝ} (hfC : ContDiff ℝ 2 f) (c : Fin n → ℝ) :
    ContDiff ℝ 2 fun z => f (z + c) := by
  have hin : ContDiff ℝ 2 fun z : Fin n → ℝ => z + c := contDiff_id.add contDiff_const
  exact hfC.comp hin

/-- The Fréchet derivative of a translate is the derivative read at the translated point. -/
theorem hasFDerivAt_shiftArg {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : (Fin n → ℝ) → F} {g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] F}
    (hg : ∀ z, HasFDerivAt g (g' z) z) (c z : Fin n → ℝ) :
    HasFDerivAt (fun w => g (w + c)) (g' (z + c)) z := by
  have hin : HasFDerivAt (fun w : Fin n → ℝ => w + c)
      (ContinuousLinearMap.id ℝ (Fin n → ℝ)) z := (hasFDerivAt_id z).add_const c
  have hcomp : HasFDerivAt (g ∘ fun w : Fin n → ℝ => w + c)
      ((g' (z + c)).comp (ContinuousLinearMap.id ℝ (Fin n → ℝ))) z := (hg (z + c)).comp z hin
  rw [ContinuousLinearMap.comp_id] at hcomp
  exact hcomp

/-- A partial derivative of a translated first derivative is the partial derivative read at the
translated point. -/
theorem coordDeriv_shiftArg (f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ) (c : Fin n → ℝ)
    (p : Fin n) (z : Fin n → ℝ) :
    coordDeriv (fun w => f' (w + c)) p z = coordDeriv f' p (z + c) := rfl

/-- A second partial derivative of a translated second derivative is the second partial
derivative read at the translated point. -/
theorem coordDeriv₂_shiftArg (f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ)
    (c : Fin n → ℝ) (p q : Fin n) (z : Fin n → ℝ) :
    coordDeriv₂ (fun w => f'' (w + c)) p q z = coordDeriv₂ f'' p q (z + c) := rfl

end Translate

section ShiftedFormula

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in
/-- **Itô's formula along a stopped path, for a function translated by a fixed vector.** -/
theorem itoFormula_stopped_shift
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, Multidim.MultidimBrownianMotion.CrossWitness W ℱ' j)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    (J : Finset ℝ) (hJ0 : ∀ c ∈ J, 0 ≤ c)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (c : Fin n → ℝ)
    (hmg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s)))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s))
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω + c) - f (X 0 ω + c)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ
            (fun ω s => coordDeriv f' p (X s ω + c) * bdrift p ω s) ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω + c) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω + c)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume :=
  itoFormula_stopped W ℱ' hcoord h 𝒲 hℱ0 hnull hX₀ hbm hbp hbq hτ hτ0 J hJ0 hτJ
    (f := fun z => f (z + c)) (f' := fun z => f' (z + c)) (f'' := fun z => f'' (z + c))
    (contDiff_shiftArg hfC c) (fun z => hasFDerivAt_shiftArg hf c z)
    (fun z => hasFDerivAt_shiftArg hf' c z) hmg hpg hqg hT

end ShiftedFormula

section StoppedIncrement

variable {Ω : Type u}

/-- The increment, over an integrand cut off at a stopping time, of the same integrand cut off at
a later stopping time vanishes up to the earlier time. -/
theorem stopped_sub_stopped_eq_zero {σ τ : Ω → WithTop ℝ} (hστ : ∀ ω, σ ω ≤ τ ω)
    (K : Ω → ℝ → ℝ) (ω : Ω) {s : ℝ} (hs : ((s : ℝ) : WithTop ℝ) ≤ σ ω) :
    Probability.stopped τ K ω s - Probability.stopped σ K ω s = 0 := by
  unfold LevyStochCalc.Probability.stopped
  rw [if_pos hs, if_pos (le_trans hs (hστ ω)), sub_self]

end StoppedIncrement

section HitIndPullOut

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- **A past weight cut to the event that a stopping time equals a deterministic time passes
inside an Itô integral.** For `V` bounded and `ℱ_a`-measurable and an integrand vanishing at
positive times up to the stopping time, multiplying by the weight outside the integral is the
same as multiplying the integrand by it. -/
theorem mul_stochasticIntegralBrownian_hitInd
    {σ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    {D : Ω → ℝ → ℝ} (hmD : Measurable (Function.uncurry D))
    (hpD : Probability.ProgressivelyMeasurable ℱ D)
    (hqD : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hD0 : ∀ (ω : Ω) (s : ℝ), 0 < s → ((s : ℝ) : WithTop ℝ) ≤ σ ω → D ω s = 0)
    (hwm : Measurable (Function.uncurry fun ω s => hitInd σ a ω * V ω * D ω s))
    (hwp : Probability.ProgressivelyMeasurable ℱ fun ω s => hitInd σ a ω * V ω * D ω s)
    (hwq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖hitInd σ a ω * V ω * D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    (fun ω => hitInd σ a ω * V ω
        * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD T ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω * D ω s) hwm hwp hwq T := by
  classical
  have hT : (0 : ℝ) < T := lt_of_le_of_lt ha haT
  obtain ⟨M, hM⟩ := hVb
  have hwbdd : ∀ ω, |hitInd σ a ω * V ω| ≤ M := by
    intro ω
    calc |hitInd σ a ω * V ω| = |hitInd σ a ω| * |V ω| := abs_mul _ _
      _ ≤ 1 * |V ω| := mul_le_mul_of_nonneg_right (abs_hitInd_le_one σ a ω) (abs_nonneg _)
      _ = |V ω| := one_mul _
      _ ≤ M := hM ω
  have hwmeas : Measurable fun ω => hitInd σ a ω * V ω := (measurable_hitInd σ hσ a).mul hVm
  have hwsm : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) fun ω => hitInd σ a ω * V ω :=
    (stronglyMeasurable_hitInd σ hσ a).mul hVa
  -- where the weight does not vanish the integrand is carried by the window `(a, T]`
  have hkeypt : ∀ (ω : Ω) (s : ℝ),
      hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s
        = indIoc Ω 0 T ω s * (hitInd σ a ω * V ω * D ω s) := by
    intro ω s
    by_cases hev : σ ω = ((a : ℝ) : WithTop ℝ)
    · by_cases hsa : a < s
      · have hIeq : indIoc Ω a T ω s = indIoc Ω 0 T ω s := by
          by_cases hsT : s ≤ T
          · have h1 : s ∈ Set.Ioc a T := ⟨hsa, hsT⟩
            have h2 : s ∈ Set.Ioc (0 : ℝ) T := ⟨lt_of_le_of_lt ha hsa, hsT⟩
            simp only [indIoc, Set.indicator_of_mem h1, Set.indicator_of_mem h2]
          · have h1 : s ∉ Set.Ioc a T := fun hm => hsT hm.2
            have h2 : s ∉ Set.Ioc (0 : ℝ) T := fun hm => hsT hm.2
            simp only [indIoc, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
        rw [hIeq]; ring
      · rw [not_lt] at hsa
        have hind : indIoc Ω a T ω s = 0 := by
          have hm : s ∉ Set.Ioc a T := fun hm => absurd hm.1 (not_lt.mpr hsa)
          simp only [indIoc, Set.indicator_of_notMem hm]
        by_cases hs0 : 0 < s
        · have hD : D ω s = 0 := by
            refine hD0 ω s hs0 ?_
            rw [hev]
            exact_mod_cast hsa
          rw [hind, hD]; ring
        · rw [not_lt] at hs0
          have hind0 : indIoc Ω 0 T ω s = 0 := by
            have hm : s ∉ Set.Ioc (0 : ℝ) T := fun hm => absurd hm.1 (not_lt.mpr hs0)
            simp only [indIoc, Set.indicator_of_notMem hm]
          rw [hind, hind0]; ring
    · have hh : hitInd σ a ω = 0 := by
        simp [hitInd, Set.indicator_of_notMem
          (show ω ∉ {ω | σ ω = ((a : ℝ) : WithTop ℝ)} from hev)]
      rw [hh]; ring
  have hkey : (fun (ω : Ω) (s : ℝ) => hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s)
      = indTerm (fun ω s => hitInd σ a ω * V ω * D ω s) 0 T := by
    funext ω s
    exact hkeypt ω s
  have habs : ∀ (ω : Ω) (s : ℝ),
      |hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s| ≤ |hitInd σ a ω * V ω * D ω s| := by
    intro ω s
    calc |hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s|
        = |hitInd σ a ω * V ω| * |indIoc Ω a T ω s| * |D ω s| := by rw [abs_mul, abs_mul]
      _ ≤ |hitInd σ a ω * V ω| * 1 * |D ω s| :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (indIoc_le_one a T ω s) (abs_nonneg _)) (abs_nonneg _)
      _ = |hitInd σ a ω * V ω * D ω s| := by rw [mul_one, ← abs_mul]
  have hindm : Measurable fun p : Ω × ℝ => indIoc Ω a T p.1 p.2 := by
    simp only [indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  have hiM : Measurable (Function.uncurry fun (ω : Ω) s => indIoc Ω a T ω s * D ω s) :=
    measurable_indTerm hmD a T
  have hiP : Probability.ProgressivelyMeasurable ℱ
      (fun (ω : Ω) s => indIoc Ω a T ω s * D ω s) :=
    progressivelyMeasurable_indTerm ℱ hpD ha haT
  have hiQ : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖indIoc Ω a T ω s * D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    energy_lt_top_of_abs_le (P := P) (fun ω s => abs_indTerm_le (H := D) a T ω s) hqD
  have hcm : Measurable (Function.uncurry
      fun (ω : Ω) s => hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s) :=
    ((hwmeas.comp measurable_fst).mul hindm).mul hmD
  have hcp : Probability.ProgressivelyMeasurable ℱ
      (fun (ω : Ω) s => hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s) :=
    (progressivelyMeasurable_mul_indIoc ℱ ha haT ⟨M, hwbdd⟩ hwmeas hwsm).mul hpD
  have hcq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    energy_lt_top_of_abs_le (P := P) habs hwq
  have hzm : Measurable (Function.uncurry
      (indTerm (fun (ω : Ω) s => hitInd σ a ω * V ω * D ω s) 0 T)) :=
    measurable_indTerm hwm 0 T
  have hzp : Probability.ProgressivelyMeasurable ℱ
      (indTerm (fun (ω : Ω) s => hitInd σ a ω * V ω * D ω s) 0 T) :=
    progressivelyMeasurable_indTerm ℱ hwp (le_refl (0 : ℝ)) hT
  have hzq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖indTerm (fun (ω : Ω) s => hitInd σ a ω * V ω * D ω s) 0 T ω s‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤ :=
    energy_lt_top_of_abs_le (P := P)
      (fun ω s => abs_indTerm_le (H := fun ω s => hitInd σ a ω * V ω * D ω s) 0 T ω s) hwq
  have hpull := mul_stochasticIntegralBrownian_indIoc W ℱ hℱ ha haT
    (V := fun ω => hitInd σ a ω * V ω) ⟨M, hwbdd⟩ hwmeas hwsm D hmD hpD hqD
    hiM hiP hiQ hcm hcp hcq hT
  have hloc := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ D hmD hpD hqD ha haT
    hiM hiP hiQ hT
  have hstep := stochasticIntegralBrownian_indTerm_zero W ℱ hℱ hT hwm hwp hwq hzm hzp hzq
  have hcongr := stochasticIntegralBrownian_congr_fun W ℱ hℱ hkey hcm hcp hcq hzm hzp hzq T
  -- the increment removed by the window is invisible where the stopping time equals `a`
  have hzero : ∀ᵐ ω ∂P,
      hitInd σ a ω * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω = 0 := by
    rcases eq_or_lt_of_le ha with hA | hA
    · have hz := stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ D hmD hpD hqD
        (le_of_eq hA.symm)
      filter_upwards [hz] with ω hω
      have hval : stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω = 0 := hω
      rw [hval, mul_zero]
    · have hz0m : Measurable (Function.uncurry fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) :=
        measurable_const
      have hz0p : Probability.ProgressivelyMeasurable ℱ (fun (_ : Ω) (_ : ℝ) => (0 : ℝ)) :=
        Probability.progressivelyMeasurable_zero ℱ
      have hz0q : ∀ t, 0 < t → ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) t,
          (‖(0 : ℝ)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
        intro t _
        simp
      have hcl := stochasticIntegralBrownian_congr_of_le σ W ℱ hℱ hσ hmD hpD hqD
        hz0m hz0p hz0q (fun ω s hs hsσ => hD0 ω s hs hsσ) hA
      have hzz := stochasticIntegralBrownian_ae_zero W ℱ hℱ hz0m hz0p hz0q a
      filter_upwards [hcl, hzz] with ω h1 h2
      by_cases hev : σ ω = ((a : ℝ) : WithTop ℝ)
      · have hle : ((a : ℝ) : WithTop ℝ) ≤ σ ω := le_of_eq hev.symm
        have hval : stochasticIntegralBrownian W ℱ hℱ
            (fun _ _ => (0 : ℝ)) hz0m hz0p hz0q a ω = 0 := h2
        rw [h1 hle, hval, mul_zero]
      · have hh : hitInd σ a ω = 0 := by
          simp [hitInd, Set.indicator_of_notMem
            (show ω ∉ {ω | σ ω = ((a : ℝ) : WithTop ℝ)} from hev)]
        rw [hh, zero_mul]
  filter_upwards [hpull, hloc, hstep, hzero] with ω h1 h2 h3 h4
  show hitInd σ a ω * V ω * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD T ω
      = stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω * D ω s) hwm hwp hwq T ω
  have h1' : hitInd σ a ω * V ω * stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => indIoc Ω a T ω s * D ω s) hiM hiP hiQ T ω
      = stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω * indIoc Ω a T ω s * D ω s) hcm hcp hcq T ω := h1
  have h2' : stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => indIoc Ω a T ω s * D ω s) hiM hiP hiQ T ω
      = stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD (min T T) ω
        - stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD (min a T) ω := h2
  have h3' : stochasticIntegralBrownian W ℱ hℱ
      (indTerm (fun ω s => hitInd σ a ω * V ω * D ω s) 0 T) hzm hzp hzq T ω
      = stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω * D ω s) hwm hwp hwq T ω := h3
  have hprod : hitInd σ a ω * V ω
      * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω = 0 := by
    calc hitInd σ a ω * V ω * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω
        = V ω * (hitInd σ a ω * stochasticIntegralBrownian W ℱ hℱ D hmD hpD hqD a ω) := by
          ring
      _ = 0 := by rw [h4, mul_zero]
  rw [← h3', ← congrFun hcongr ω, ← h1', h2', min_self, min_eq_left haT.le]
  linear_combination hprod

include hℱ in
/-- **The increment of an integrand between two stopping times carries a past weight inside the
Itô integral.** The weight is cut to the event that the earlier stopping time equals a
deterministic time and is otherwise known at that time. -/
theorem mul_stochasticIntegralBrownian_hitInd_stopped_sub
    {σ τ : Ω → WithTop ℝ} (hσ : MeasureTheory.IsStoppingTime ℱ σ)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (hστ : ∀ ω, σ ω ≤ τ ω)
    {a T : ℝ} (ha : 0 ≤ a) (haT : a < T)
    {V : Ω → ℝ} (hVb : ∃ M : ℝ, ∀ ω, |V ω| ≤ M) (hVm : Measurable V)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) V)
    {K : Ω → ℝ → ℝ} (hmK : Measurable (Function.uncurry K))
    (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hwm : Measurable (Function.uncurry fun ω s => hitInd σ a ω * V ω
      * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)))
    (hwp : Probability.ProgressivelyMeasurable ℱ fun ω s => hitInd σ a ω * V ω
      * (Probability.stopped τ K ω s - Probability.stopped σ K ω s))
    (hwq : ∀ t, 0 < t → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖hitInd σ a ω * V ω
        * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)‖₊ : ℝ≥0∞) ^ 2
        ∂volume ∂P < ⊤) :
    (fun ω => hitInd σ a ω * V ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => Probability.stopped τ K ω s - Probability.stopped σ K ω s)
        ((Probability.measurable_uncurry_stopped hτ hmK).sub
          (Probability.measurable_uncurry_stopped hσ hmK))
        ((Probability.ProgressivelyMeasurable.stopped hτ hpK).sub
          (Probability.ProgressivelyMeasurable.stopped hσ hpK))
        (lintegral_energy_lt_top_of_bound (fun _ _ => sq_nnnorm_sub_le_two_mul _ _)
          (Probability.measurable_uncurry_stopped hτ hmK)
          (Probability.measurable_uncurry_stopped hσ hmK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ K ω s) hqK)
          (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le σ K ω s) hqK))
        T ω)
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => hitInd σ a ω * V ω
          * (Probability.stopped τ K ω s - Probability.stopped σ K ω s)) hwm hwp hwq T :=
  mul_stochasticIntegralBrownian_hitInd W ℱ hℱ hσ ha haT hVb hVm hVa _ _ _
    (fun ω _ _ hs => stopped_sub_stopped_eq_zero hστ K ω hs) hwm hwp hwq

end HitIndPullOut

end LevyStochCalc.Brownian.Ito
