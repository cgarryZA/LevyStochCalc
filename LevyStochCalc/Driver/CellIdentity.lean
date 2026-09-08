/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.ProductRule
import LevyStochCalc.Driver.CellPairing
import LevyStochCalc.Brownian.CellCharacter
import LevyStochCalc.Poisson.CharacterStrictProcess
import LevyStochCalc.Poisson.CharacterOrthogonal

/-!
# The product rule on a cell, in the shape the pairing consumes

The product rule of a trigonometric function of a Brownian increment with a bounded pure-jump
process, rewritten so that the Itô integrand is a bounded progressive factor times the
indicator of the cell and the jump term is an integral over the window up to the time.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}

section Window

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [MeasurableSpace E]
  [IsProbabilityMeasure P] [SigmaFinite ν] [MeasurableSpace Ω] in
/-- The window of the horizon met with the times up to `t` is the window up to `t`. -/
theorem window_inter_Ioc {T t : ℝ} (htT : t ≤ T) (A : Set E) :
    (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioc (0 : ℝ) t ×ˢ (Set.univ : Set E)
      = Set.Ioc (0 : ℝ) t ×ˢ A := by
  rw [Set.prod_inter_prod, Set.inter_univ, Set.Ioc_inter_Ioc, max_self,
    min_eq_right htT]

end Window

section Identity

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

include hℱW in
/-- **The cell identity.** The product rule for `g (l X)` and a bounded pure-jump process, with
the Itô integrand written as a bounded factor times the cell's indicator and the jump term over
the window up to the time. -/
theorem hid_cell
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g)
    (hgb : ∀ x, |g x| ≤ 1)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (G : MarkedHorizonIntegrand P ν ℱ T)
    {Y Yminus : ℝ → Ω → ℝ} (hYb : ∀ s ω, |Y s ω| ≤ 1) (hYm : ∀ s, Measurable (Y s))
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s))
    (hY : ∀ᵐ ω ∂P, ∀ s : ℝ, Y s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hYmb : ∀ s ω, |Yminus s ω| ≤ 1)
    (hYminus : ∀ᵐ ω ∂P, ∀ s : ℝ, Yminus s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hmm2 : Measurable (Function.uncurry fun ω s =>
      (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s))
    (hpm2 : Probability.ProgressivelyMeasurable ℱ fun ω s =>
      (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s)
    (hqm2 : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∀ᵐ ω ∂P, g (l * X t ω) * Y t ω - g (l * X 0 ω) * Y 0 ω
      = stochasticIntegralBrownian W ℱ hℱW
          (fun ω s => (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s) hmm2 hpm2 hqm2 t ω
        + (∫ s in Set.Ioc (0 : ℝ) t,
            Yminus s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume)
        + ∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * G.toFun ω q.1 q.2 ∂(N.N ω) := by
  classical
  have hglc : Continuous fun x : ℝ => g (l * x) :=
    hgc.comp (continuous_const.mul continuous_id)
  have hbm := measurable_trigDriftCell hXbase l (g := fun x : ℝ => g (l * x)) hglc
  have hXtrig := isItoVersion_trig hXbase l hgc hmg hpg hqg hito hX0
  have hRm : MeasurableSet (Set.Ioc (0 : ℝ) T ×ˢ A) := measurableSet_Ioc.prod hA
  have hRfin : referenceIntensity ν (Set.Ioc (0 : ℝ) T ×ˢ A) ≠ ⊤ :=
    referenceIntensity_Ioc_prod_ne_top hAν T
  -- the two integrand shapes agree
  have hEq : (fun (ω : Ω) (s : ℝ) => Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s))
      = fun ω s => (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s := by
    funext ω s
    ring
  have hmm1 : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s)) := by rw [hEq]; exact hmm2
  have hpm1 : Probability.ProgressivelyMeasurable ℱ fun (ω : Ω) (s : ℝ) =>
      Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s) := by rw [hEq]; exact hpm2
  have hqm1 : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Yminus s ω * (g' (X s ω) * indIoc Ω a b ω s)‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T' hT'
    have h := hqm2 T' hT'
    simpa only [mul_assoc] using h
  have hSIB := stochasticIntegralBrownian_congr_fun W ℱ hℱW hEq hmm1 hpm1 hqm1 hmm2 hpm2 hqm2 t
  have hpr := product_rule N W ℱ hℱW
    (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg hXtrig hbm
    (fun ω s => abs_trigDriftCell_le l (fun x => hgb (l * x)) zero_le_one X a b ω s) hRm hRfin
    Y hYb hYm hYad hY Yminus hYmb hYminus hmm1 hpm1 hqm1 ht
  filter_upwards [hpr] with ω hω
  rw [hω, congrFun hSIB ω, window_inter_Ioc htT A]

end Identity

section Paired

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

include hℱN hℱW in
/-- **The paired cell identity.** Pairing the product rule of a trigonometric function of a
Brownian increment with a bounded pure-jump process against a weight orthogonal to every Itô
integral and every compensated integral leaves the drift term and the compensator. -/
theorem paired_cell_char
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (G : MarkedHorizonIntegrand P ν ℱ T) (hGpred : Probability.MarkedPredictable ℱ ν G.toFun)
    (hGa : ∀ ω s e, s ≤ a → G.toFun ω s e = 0) {Cg : ℝ} (hGb : ∀ ω s e, |G.toFun ω s e| ≤ Cg)
    {Y Yminus : ℝ → Ω → ℝ} (hYb : ∀ s ω, |Y s ω| ≤ 1) (hYm : ∀ s, Measurable (Y s))
    (hYad : ∀ s, StronglyMeasurable[ℱ s] (Y s))
    (hY : ∀ᵐ ω ∂P, ∀ s : ℝ, Y s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioc (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hYmb : ∀ s ω, |Yminus s ω| ≤ 1)
    (hYminus : ∀ᵐ ω ∂P, ∀ s : ℝ, Yminus s ω = Y 0 ω
      + ∫ p in (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ Set.Ioo (0 : ℝ) s ×ˢ Set.univ,
          G.toFun ω p.1 p.2 ∂(N.N ω))
    (hYmmeas : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Yminus s ω))
    (hYmprog : Probability.ProgressivelyMeasurable ℱ fun (ω : Ω) (s : ℝ) => Yminus s ω)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) (haT : a ≤ T) :
    ∫ ω, Z ω * V ω * (g (l * X t ω) * Y t ω) ∂P
      = ∫ ω, Z ω * V ω * (g (l * X 0 ω) * Y 0 ω) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            Yminus s ω * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * G.toFun ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  classical
  have hglc : Continuous fun x : ℝ => g (l * x) :=
    hgc.comp (continuous_const.mul continuous_id)
  -- the Brownian factor
  have hXgc : ∀ ω, Continuous fun s => g (l * X s ω) := fun ω =>
    hglc.comp (hXbase.continuous_path ω)
  have hXga : ∀ s : ℝ, StronglyMeasurable[ℱ s] fun ω => g (l * X s ω) := fun s =>
    hglc.comp_stronglyMeasurable (hXbase.adapted s)
  have hXgb : ∀ s ω, |g (l * X s ω)| ≤ 1 := fun s ω => hgb _
  -- the Itô integrand of the paired identity
  have hKm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) => Yminus s ω * g' (X s ω)) :=
    hYmmeas.mul (hg'c.measurable.comp hXbase.measurable_uncurry)
  have hKp : Probability.ProgressivelyMeasurable ℱ
      fun (ω : Ω) (s : ℝ) => Yminus s ω * g' (X s ω) :=
    hYmprog.mul (hXbase.progressivelyMeasurable_comp hg'c)
  have hKbd : ∀ (ω : Ω) (s : ℝ), |Yminus s ω * g' (X s ω)| ≤ |l| := by
    intro ω s
    rw [abs_mul]
    calc |Yminus s ω| * |g' (X s ω)| ≤ 1 * |l| :=
          mul_le_mul (hYmb s ω) (hg'b _) (abs_nonneg _) zero_le_one
      _ = |l| := one_mul _
  have hmm2 : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s) := hKm.mul hm
  have hpm2 : Probability.ProgressivelyMeasurable ℱ fun (ω : Ω) (s : ℝ) =>
      (Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s := hKp.mul hp
  have hbd2 : ∀ (ω : Ω) (s : ℝ),
      |(Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s| ≤ |l| := by
    intro ω s
    rw [abs_mul]
    calc |Yminus s ω * g' (X s ω)| * |indIoc Ω a b ω s| ≤ |l| * 1 :=
          mul_le_mul (hKbd ω s) (indIoc_le_one a b ω s) (abs_nonneg _) (abs_nonneg _)
      _ = |l| := mul_one _
  have hqm2 : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖(Yminus s ω * g' (X s ω)) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T' hT' => lintegral_sq_lt_top_of_bounded hbd2 T' hT'
  -- the identity, then the pairing
  have hid := hid_cell N W hℱW hXbase hX0 l hgc hgb hmg hpg hqg hito hA hAν G hYb hYm
    hYad hY hYmb hYminus hmm2 hpm2 hqm2 ht htT
  exact pairing_of_product_rule N hℱN W hℱW hT ha hab haT hZ2 hZito hZcomp hVa hMv0 hVb
    hXgc hXga zero_le_one hXgb hYm hYb hYmmeas hYmb
    (measurable_trigDriftCell hXbase l hglc)
    (fun ω s => abs_trigDriftCell_le l (fun x => hgb (l * x)) zero_le_one X a b ω s)
    G hGpred hGa hGb hA hAν hKm hKp (abs_nonneg l) hKbd hmm2 hpm2 hqm2 ht htT hid

end Paired

section Parts

variable (N : PoissonRandomMeasure P ν) (hℱN : IsPoissonFiltration N ℱ)
  (W : LevyStochCalc.Brownian.BrownianMotion P) (hℱW : IsBrownianFiltration W ℱ)
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ} {ι : Type*} [Fintype ι]

include hℱN hℱW in
/-- **The paired cell identity, real part.** -/
theorem paired_cell_re
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫ ω, Z ω * V ω * (g (l * X t ω) * (charAt N w Bfam t ω).re) ∂P
      = ∫ ω, Z ω * V ω * (g (l * X 0 ω) * (charAt N w Bfam 0 ω).re) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            (charStrictPred N w Bfam A T e₀ s ω).re
              * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * charRe N w Bfam A T ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have haT : a ≤ T := le_trans hab.le hbT.le
  refine paired_cell_char N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b hmg hpg hqg hito
    hT hA hAν (charReIntegrand N hℱN w hBm hA hAν hBsub')
    (markedPredictable_charRe N hℱN w hBm hA hAν hBsub')
    (fun ω s e hs => charRe_eq_zero_of_le N w hBsub T ω hs e)
    (abs_charRe_le N w Bfam A T)
    (fun s ω => abs_charAt_re_le N w s ω)
    (fun s => Complex.measurable_re.comp (measurable_charAt N w hBm s))
    (fun s => Complex.continuous_re.comp_stronglyMeasurable
      (stronglyMeasurable_charAt N hℱN w hBm s))
    ?_ (fun s ω => abs_charStrictPred_re_le N w Bfam A T e₀ s ω) ?_
    (Complex.measurable_re.comp (measurable_uncurry_charStrictPred N w hℱN hBm hA hAν T e₀))
    (progressivelyMeasurable_charStrictPred_re N w hℱN hBm hA hAν T e₀)
    hZ2 hZito hZcomp hVa hMv0 hVb ht htT haT
  · filter_upwards [ae_forall_charAt_re_im_sub N w hBm hA hAν hBsub' hℱN] with ω hω s
    exact (hω s).1
  · filter_upwards [ae_forall_charStrict_re_im_sub N w hBm hA hAν hBsub' hℱN] with ω hω s
    rw [charStrictPred_eq N w hT hbT hBsub0 he₀ s ω]
    exact (hω s).1

include hℱN hℱW in
/-- **The paired cell identity, imaginary part.** -/
theorem paired_cell_im
    (hXbase : IsItoVersion W ℱ hℱW (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) (ha : 0 ≤ a) (hab : a < b)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hg'c : Continuous g') (hg'b : ∀ x, |g' x| ≤ |l|)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T', 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T' : ℝ, 0 < T' →
      (fun ω : Ω => g (l * X T' ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱW
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T' ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T',
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    {T : ℝ} (hT : 0 < T) (hbT : b < T) {A : Set E} (hA : MeasurableSet A) (hAν : ν A ≠ ⊤)
    (w : ι → ℝ) {Bfam : ι → Set (ℝ × E)} (hBm : ∀ j, MeasurableSet (Bfam j))
    (hBsub : ∀ j, Bfam j ⊆ Set.Ioc a b ×ˢ A) {e₀ : E} (he₀ : e₀ ∈ A)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZito : PerpItoIntegrals W ℱ hℱW fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    {V : Ω → ℝ} (hVa : StronglyMeasurable[ℱ a] V) {Mv : ℝ} (hMv0 : 0 ≤ Mv)
    (hVb : ∀ ω, |V ω| ≤ Mv)
    {t : ℝ} (ht : 0 < t) (htT : t ≤ T) :
    ∫ ω, Z ω * V ω * (g (l * X t ω) * (charAt N w Bfam t ω).im) ∂P
      = ∫ ω, Z ω * V ω * (g (l * X 0 ω) * (charAt N w Bfam 0 ω).im) ∂P
        + ∫ ω, Z ω * V ω * (∫ s in Set.Ioc (0 : ℝ) t,
            (charStrictPred N w Bfam A T e₀ s ω).im
              * trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) ∂P
        + ∫ ω, Z ω * V ω * (∫ q in Set.Ioc (0 : ℝ) t ×ˢ A,
            g (l * X q.1 ω) * charIm N w Bfam A T ω q.1 q.2 ∂(referenceIntensity ν)) ∂P := by
  have hBsub' : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) T ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha hbT.le) le_rfl)
  have hBsub0 : ∀ j, Bfam j ⊆ Set.Ioc (0 : ℝ) b ×ˢ A := fun j =>
    (hBsub j).trans (Set.prod_mono (Set.Ioc_subset_Ioc ha le_rfl) le_rfl)
  have haT : a ≤ T := le_trans hab.le hbT.le
  refine paired_cell_char N hℱN W hℱW hXbase hX0 ha hab l hgc hgb hg'c hg'b hmg hpg hqg hito
    hT hA hAν (charImIntegrand N hℱN w hBm hA hAν hBsub')
    (markedPredictable_charIm N hℱN w hBm hA hAν hBsub')
    (fun ω s e hs => charIm_eq_zero_of_le N w hBsub T ω hs e)
    (abs_charIm_le N w Bfam A T)
    (fun s ω => abs_charAt_im_le N w s ω)
    (fun s => Complex.measurable_im.comp (measurable_charAt N w hBm s))
    (fun s => Complex.continuous_im.comp_stronglyMeasurable
      (stronglyMeasurable_charAt N hℱN w hBm s))
    ?_ (fun s ω => abs_charStrictPred_im_le N w Bfam A T e₀ s ω) ?_
    (Complex.measurable_im.comp (measurable_uncurry_charStrictPred N w hℱN hBm hA hAν T e₀))
    (progressivelyMeasurable_charStrictPred_im N w hℱN hBm hA hAν T e₀)
    hZ2 hZito hZcomp hVa hMv0 hVb ht htT haT
  · filter_upwards [ae_forall_charAt_re_im_sub N w hBm hA hAν hBsub' hℱN] with ω hω s
    exact (hω s).2
  · filter_upwards [ae_forall_charStrict_re_im_sub N w hBm hA hAν hBsub' hℱN] with ω hω s
    rw [charStrictPred_eq N w hT hbT hBsub0 he₀ s ω]
    exact (hω s).2

end Parts

end LevyStochCalc.Driver
