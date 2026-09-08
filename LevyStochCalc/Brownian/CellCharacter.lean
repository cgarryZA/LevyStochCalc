/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoTrigIncrement
import LevyStochCalc.Brownian.ItoVersionExists

/-!
# The trigonometric functions of a Brownian increment are Itô processes

For a continuous version `X` of `∫ 1_{(a,b]} dW`, Itô's formula for the scaled cosine and sine
says that `cos (l X)` and `sin (l X)` are themselves Itô processes: their integrands are
`∓ l sin (l X) 1_{(a,b]}` and `± l cos (l X) 1_{(a,b]}` and their drifts are
`−(l²/2) cos (l X) 1_{(a,b]}²` and `−(l²/2) sin (l X) 1_{(a,b]}²`, with initial value `1` and `0`.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

section Version

variable {P : Measure Ω} [IsProbabilityMeasure P] {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

/-- The drift of a trigonometric function of a Brownian increment. -/
noncomputable def trigDriftCell (l : ℝ) (g : ℝ → ℝ) (X : ℝ → Ω → ℝ) (a b : ℝ) (ω : Ω)
    (s : ℝ) : ℝ :=
  1 / 2 * ((-l ^ 2 * g (X s ω)) * indIoc Ω a b ω s ^ 2)

theorem abs_trigDriftCell_le (l : ℝ) {g : ℝ → ℝ} {M : ℝ} (hg : ∀ x, |g x| ≤ M) (hM0 : 0 ≤ M)
    (X : ℝ → Ω → ℝ) (a b : ℝ) (ω : Ω) (s : ℝ) :
    |trigDriftCell l g X a b ω s| ≤ 1 / 2 * (l ^ 2 * M) := by
  unfold trigDriftCell
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2), abs_mul, abs_mul, abs_neg,
    abs_pow, abs_pow]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have h1 : |l| ^ 2 * |g (X s ω)| ≤ l ^ 2 * M := by
    rw [sq_abs]
    exact mul_le_mul_of_nonneg_left (hg _) (sq_nonneg l)
  have h2 : |indIoc Ω a b ω s| ^ 2 ≤ 1 :=
    (pow_le_pow_left₀ (abs_nonneg _) (indIoc_le_one a b ω s) 2).trans (by norm_num)
  calc |l| ^ 2 * |g (X s ω)| * |indIoc Ω a b ω s| ^ 2 ≤ (l ^ 2 * M) * 1 :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = l ^ 2 * M := mul_one _

theorem measurable_trigDriftCell
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable (Function.uncurry (trigDriftCell l g X a b)) :=
  (((hg.measurable.comp hX.measurable_uncurry).const_mul (-l ^ 2)).mul
    (hm.pow_const 2)).const_mul (1 / 2)

theorem progressivelyMeasurable_trigDriftCell
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g : ℝ → ℝ} (hg : Continuous g) :
    Probability.ProgressivelyMeasurable ℱ (trigDriftCell l g X a b) := by
  have hconst : ∀ c : ℝ, Probability.ProgressivelyMeasurable ℱ fun (_ : Ω) (_ : ℝ) => c :=
    fun c => Probability.ProgressivelyMeasurable.of_isStronglyProgressive
      (MeasureTheory.StronglyAdapted.isStronglyProgressive_of_continuous
        (fun _ => stronglyMeasurable_const) fun _ => continuous_const)
  have h1 : Probability.ProgressivelyMeasurable ℱ fun ω s => -l ^ 2 * g (X s ω) :=
    (hconst (-l ^ 2)).mul (hX.progressivelyMeasurable_comp hg)
  have h2 : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s ^ 2 := by
    have := hp.mul hp
    simpa [sq] using this
  exact (hconst (1 / 2)).mul (h1.mul h2)

/-- **A trigonometric function of a Brownian increment is an Itô process.** -/
theorem isItoVersion_trig
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X)
    (l : ℝ) {g g' : ℝ → ℝ} (hgc : Continuous g)
    (hmg : Measurable (Function.uncurry fun ω s => g' (X s ω) * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => g' (X s ω) * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖g' (X s ω) * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hito : ∀ T : ℝ, 0 < T →
      (fun ω : Ω => g (l * X T ω) - g (l * X 0 ω)) =ᵐ[P] fun ω =>
        stochasticIntegralBrownian W ℱ hℱ
            (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg T ω
          + 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) T,
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume)
    (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ)) :
    IsItoVersion W ℱ hℱ (fun ω s => g' (X s ω) * indIoc Ω a b ω s) hmg hpg hqg
      (fun _ => g 0) (trigDriftCell l (fun x => g (l * x)) X a b)
      (fun t ω => g (l * X t ω)) where
  continuous_path ω := hgc.comp ((continuous_const.mul (hX.continuous_path ω)))
  adapted t := hgc.comp_stronglyMeasurable
    ((continuous_const.mul continuous_id).comp_stronglyMeasurable (hX.adapted t))
  ae_eq t ht := by
    have hglc : Continuous fun x : ℝ => g (l * x) :=
      hgc.comp (continuous_const.mul continuous_id)
    have hbm := measurable_trigDriftCell hX l (g := fun x : ℝ => g (l * x)) hglc
    rcases eq_or_lt_of_le ht with rfl | ht'
    · filter_upwards [hX0, stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ _ hmg hpg hqg
        (le_refl (0 : ℝ))] with ω h0 hI
      have hz : (∫ s in Set.Icc (0 : ℝ) 0,
          trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume) = 0 := by
        rw [show Set.Icc (0 : ℝ) 0 = {0} from Set.Icc_self 0,
          setIntegral_measure_zero _ Real.volume_singleton]
      change g (l * X 0 ω) = _
      unfold itoProcess
      rw [hz, hI, h0]
      norm_num
    · filter_upwards [hito t ht', hX0] with ω hω h0
      unfold itoProcess
      have hdrift : (∫ s in Set.Icc (0 : ℝ) t,
            trigDriftCell l (fun x => g (l * x)) X a b ω s ∂volume)
          = 1 / 2 * ∫ s in Set.Ioc (0 : ℝ) t,
              (-l ^ 2 * g (l * X s ω)) * indIoc Ω a b ω s ^ 2 ∂volume := by
        rw [integral_Icc_eq_integral_Ioc]
        unfold trigDriftCell
        rw [integral_const_mul]
      rw [hdrift]
      have h1 : g (l * X t ω) - g (l * X 0 ω) = _ := hω
      rw [h0] at h1
      simp only [mul_zero] at h1
      linarith [h1]

end Version

end LevyStochCalc.Brownian.Ito
