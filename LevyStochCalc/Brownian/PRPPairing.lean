/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoTrigIncrement
import LevyStochCalc.Brownian.ItoPullOut
import LevyStochCalc.Probability.PairingFubini
import LevyStochCalc.Analysis.GronwallIntegral

/-!
# Pairing a weight orthogonal to the Itô integrals against a trigonometric increment

If `Z` pairs to zero against every Itô integral, then pairing it against `g (X_t)`, for `X` a
version of `∫ 1_{(a,b]} dW` and `g` one of the scaled trigonometric functions, gives a scalar
function of `t` that solves `Λ(t) = −(l²/2) ∫_0^t 1_{(a,b]}(s) Λ(s) ds`. Grönwall then forces
`Λ` to vanish.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The indicator of a window is idempotent. -/
theorem indIoc_sq (a b : ℝ) (ω : Ω) (s : ℝ) :
    indIoc Ω a b ω s ^ 2 = indIoc Ω a b ω s := by
  unfold indIoc
  by_cases h : s ∈ Set.Ioc a b
  · rw [Set.indicator_of_mem h]; norm_num
  · rw [Set.indicator_of_notMem h]; norm_num

section Pairing

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- An integrable weight times a bounded function is integrable. -/
theorem integrable_mul_of_bounded {Z : Ω → ℂ} (hZ : Integrable Z P) {F : Ω → ℂ}
    (hFm : AEStronglyMeasurable F P) {c : ℝ} (hFb : ∀ ω, ‖F ω‖ ≤ c) :
    Integrable (fun ω => Z ω * F ω) P := by
  refine Integrable.mono' (hZ.norm.const_mul c) (hZ.aestronglyMeasurable.mul hFm)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [norm_mul]
  calc ‖Z ω‖ * ‖F ω‖ ≤ ‖Z ω‖ * c := mul_le_mul_of_nonneg_left (hFb ω) (norm_nonneg _)
    _ = c * ‖Z ω‖ := mul_comm _ _

variable {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}

/-- A weight that pairs to zero against every `L²` Itô integral. -/
structure PerpItoIntegrals (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)
    (Z : Ω → ℂ) : Prop where
  /-- The pairing against every Itô integral vanishes. -/
  perp : ∀ (K : Ω → ℝ → ℝ) (hm : Measurable (Function.uncurry K))
    (hp : Probability.ProgressivelyMeasurable ℱ K)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) (t : ℝ), 0 < t →
    ∫ ω, Z ω * ((stochasticIntegralBrownian W ℱ hℱ K hm hp hq t ω : ℝ) : ℂ) ∂P = 0

/-- The pairing of a weight against a bounded continuous function of a jointly measurable
process is measurable in the time parameter. -/
theorem measurable_pairing {Z : Ω → ℂ} (hZm : Measurable Z) {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) {g : ℝ → ℝ} (hg : Continuous g) :
    Measurable fun t : ℝ => ∫ ω, Z ω * ((g (X t ω) : ℝ) : ℂ) ∂P := by
  have hjoint : StronglyMeasurable (Function.uncurry fun (t : ℝ) (ω : Ω) =>
      Z ω * ((g (X t ω) : ℝ) : ℂ)) := by
    refine Measurable.stronglyMeasurable ?_
    refine (hZm.comp measurable_snd).mul ?_
    refine Complex.measurable_ofReal.comp (hg.measurable.comp ?_)
    exact hXm.comp (measurable_snd.prodMk measurable_fst)
  exact (hjoint.integral_prod_right).measurable

variable {a b : ℝ}
  {hm : Measurable (Function.uncurry (indIoc Ω a b))}
  {hp : Probability.ProgressivelyMeasurable ℱ (indIoc Ω a b)}
  {hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X : ℝ → Ω → ℝ}

include hℱ in
/-- A version of `∫ 1_{(a,b]} dW` vanishes at time zero. -/
theorem ae_eq_zero_of_isItoVersion_indIoc (ha : 0 ≤ a) (hab : a < b)
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X) :
    X 0 =ᵐ[P] fun _ => (0 : ℝ) := by
  have h1 := hX.ae_eq 0 le_rfl
  have h2 := stochasticIntegralBrownian_indIoc W ℱ hℱ ha hab hm hp hq (le_refl (0 : ℝ))
  have hb0 : (0 : ℝ) ≤ b := le_trans ha hab.le
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  show (0 : ℝ) + (∫ _s in Set.Icc (0 : ℝ) 0, (0 : ℝ) ∂volume)
      + stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq 0 ω = 0
  rw [hω2]
  simp [min_eq_right hb0, min_eq_right ha]

include hℱ in
/-- At the right end of the window a version of `∫ 1_{(a,b]} dW` is the Brownian increment. -/
theorem ae_eq_increment_of_isItoVersion_indIoc (ha : 0 ≤ a) (hab : a < b)
    (hX : IsItoVersion W ℱ hℱ (indIoc Ω a b) hm hp hq (fun _ => 0) (fun _ _ => 0) X) :
    X b =ᵐ[P] fun ω => W.W b ω - W.W a ω := by
  have hb0 : (0 : ℝ) < b := lt_of_le_of_lt ha hab
  have h1 := hX.ae_eq b hb0.le
  have h2 := stochasticIntegralBrownian_indIoc W ℱ hℱ ha hab hm hp hq hb0.le
  filter_upwards [h1, h2] with ω hω1 hω2
  rw [hω1]
  show (0 : ℝ) + (∫ _s in Set.Icc (0 : ℝ) b, (0 : ℝ) ∂volume)
      + stochasticIntegralBrownian W ℱ hℱ (indIoc Ω a b) hm hp hq b ω = _
  rw [hω2]
  simp [min_self, min_eq_left hab.le]

/-- A real function in `L²` stays in `L²` after coercion to `ℂ`. -/
theorem memLp_ofReal {P : Measure Ω} {f : Ω → ℝ} (hf : MemLp f 2 P) :
    MemLp (fun ω => ((f ω : ℝ) : ℂ)) 2 P := by
  refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hf.1, ?_⟩
  have hnorm : eLpNorm (fun ω => ((f ω : ℝ) : ℂ)) 2 P = eLpNorm f 2 P :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => by simp)
  rw [hnorm]
  exact hf.2

end Pairing

section Perp

variable {P : Measure Ω} [IsProbabilityMeasure P]
  {W : LevyStochCalc.Brownian.BrownianMotion P}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} {hℱ : IsBrownianFiltration W ℱ}
  {a b : ℝ}

include hℱ in
/-- **The `dW` term pairs to zero.** A weight orthogonal to every Itô integral stays orthogonal
after multiplication by a bounded weight measurable before the window, because that weight passes
inside the integral. -/
theorem pairing_ito_eq_zero (ha : 0 ≤ a) (hab : a < b)
    {Z : Ω → ℂ} (hZ2 : MemLp Z 2 P) (hZp : PerpItoIntegrals W ℱ hℱ Z)
    {V : Ω → ℂ} (hVm : Measurable V) {Mv : ℝ} (hMv0 : 0 ≤ Mv) (hVb : ∀ ω, ‖V ω‖ ≤ Mv)
    (hVa : @MeasureTheory.StronglyMeasurable Ω ℂ _ (ℱ a) V)
    {K : Ω → ℝ → ℝ} (hKm : Measurable (Function.uncurry K))
    (hKp : Probability.ProgressivelyMeasurable ℱ K) {Kb : ℝ} (hKb0 : 0 ≤ Kb)
    (hKbd : ∀ ω s, |K ω s| ≤ Kb)
    (hmg : Measurable (Function.uncurry fun ω s => K ω s * indIoc Ω a b ω s))
    (hpg : Probability.ProgressivelyMeasurable ℱ fun ω s => K ω s * indIoc Ω a b ω s)
    (hqg : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s * indIoc Ω a b ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) :
    ∫ ω, Z ω * V ω * ((stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) ∂P = 0 := by
  classical
  have hswap : (fun (ω : Ω) (s : ℝ) => indIoc Ω a b ω s * K ω s)
      = fun ω s => K ω s * indIoc Ω a b ω s := by
    funext ω s; ring
  have him : Measurable (Function.uncurry fun ω s => indIoc Ω a b ω s * K ω s) := by
    rw [hswap]; exact hmg
  have hip : Probability.ProgressivelyMeasurable ℱ fun ω s => indIoc Ω a b ω s * K ω s := by
    rw [hswap]; exact hpg
  have hiq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro T hT
    have hpt : ∀ (ω : Ω) (s : ℝ),
        indIoc Ω a b ω s * K ω s = K ω s * indIoc Ω a b ω s := fun ω s => mul_comm _ _
    simp_rw [hpt]
    exact hqg T hT
  have hIeq := stochasticIntegralBrownian_congr_fun W ℱ hℱ hswap him hip hiq hmg hpg hqg t
  have hKq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun T hT => lintegral_sq_lt_top_of_bounded hKbd T hT
  -- each real component of the weight passes inside the integral
  have hcomp : ∀ Vr : Ω → ℝ, Measurable Vr → (∀ ω, |Vr ω| ≤ Mv) →
      @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ a) Vr →
      Integrable (fun ω => Z ω * ((Vr ω * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)) P
        ∧ ∫ ω, Z ω * ((Vr ω * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) ∂P = 0 := by
    intro Vr hVrm hVrb hVra
    have hvm : Measurable (Function.uncurry fun ω s => Vr ω * indIoc Ω a b ω s * K ω s) := by
      have h1 : Measurable fun p : Ω × ℝ => Vr p.1 * indIoc Ω a b p.1 p.2 :=
        (hVrm.comp measurable_fst).mul (measurable_uncurry_indIoc a b)
      exact h1.mul hKm
    have hvp : Probability.ProgressivelyMeasurable ℱ
        fun ω s => Vr ω * indIoc Ω a b ω s * K ω s :=
      (progressivelyMeasurable_mul_indIoc ℱ ha hab ⟨Mv, hVrb⟩ hVrm hVra).mul hKp
    have hvbd : ∀ (ω : Ω) (s : ℝ), |Vr ω * indIoc Ω a b ω s * K ω s| ≤ Mv * 1 * Kb := by
      intro ω s
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul (hVrb ω) (indIoc_le_one a b ω s) (abs_nonneg _) hMv0)
        (hKbd ω s) (abs_nonneg _) (by positivity)
    have hvq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖Vr ω * indIoc Ω a b ω s * K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
      fun T hT => lintegral_sq_lt_top_of_bounded hvbd T hT
    have hpull := mul_stochasticIntegralBrownian_indIoc W ℱ hℱ ha hab ⟨Mv, hVrb⟩ hVrm hVra
      K hKm hKp hKq him hip hiq hvm hvp hvq ht
    -- the product is a.e. an Itô integral, hence square integrable
    have hae : (fun ω => Vr ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω)
        =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Vr ω * indIoc Ω a b ω s * K ω s) hvm hvp hvq t := by
      filter_upwards [hpull] with ω hω
      rw [← hIeq]
      exact hω
    have hL2 : MemLp (fun ω => ((Vr ω * stochasticIntegralBrownian W ℱ hℱ
        (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)) 2 P :=
      memLp_ofReal
        ((stochasticIntegralBrownian_memLp W ℱ hℱ _ hvm hvp hvq t).ae_eq hae.symm)
    refine ⟨hZ2.integrable_mul hL2, ?_⟩
    have hcong : ∫ ω, Z ω * ((Vr ω * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) ∂P
        = ∫ ω, Z ω * ((stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => Vr ω * indIoc Ω a b ω s * K ω s) hvm hvp hvq t ω : ℝ) : ℂ) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hae] with ω hω
      exact congrArg (fun x : ℝ => Z ω * ((x : ℝ) : ℂ)) hω
    rw [hcong]
    exact hZp.perp _ hvm hvp hvq t ht
  obtain ⟨hreint, hre⟩ := hcomp (fun ω => (V ω).re) (Complex.measurable_re.comp hVm)
    (fun ω => le_trans (Complex.abs_re_le_norm _) (hVb ω))
    (Complex.continuous_re.comp_stronglyMeasurable hVa)
  obtain ⟨himint, himz⟩ := hcomp (fun ω => (V ω).im) (Complex.measurable_im.comp hVm)
    (fun ω => le_trans (Complex.abs_im_le_norm _) (hVb ω))
    (Complex.continuous_im.comp_stronglyMeasurable hVa)
  have hdecomp : ∀ ω : Ω, Z ω * V ω * ((stochasticIntegralBrownian W ℱ hℱ
      (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
      = Z ω * (((V ω).re * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
        + Complex.I * (Z ω * (((V ω).im * stochasticIntegralBrownian W ℱ hℱ
          (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)) := by
    intro ω
    have hV : ((V ω).re : ℂ) + ((V ω).im : ℂ) * Complex.I = V ω := Complex.re_add_im (V ω)
    calc Z ω * V ω * ((stochasticIntegralBrownian W ℱ hℱ
            (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ)
        = Z ω * (((V ω).re : ℂ) + ((V ω).im : ℂ) * Complex.I)
            * ((stochasticIntegralBrownian W ℱ hℱ
              (fun ω s => K ω s * indIoc Ω a b ω s) hmg hpg hqg t ω : ℝ) : ℂ) := by rw [hV]
      _ = _ := by push_cast; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hdecomp),
    integral_add hreint (himint.const_mul Complex.I), hre, integral_const_mul, himz,
    mul_zero, add_zero]

end Perp

section Equation

variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The time-integral term of Itô's formula for a trigonometric function of a process. -/
noncomputable def trigDrift (l : ℝ) (g : ℝ → ℝ) (X : ℝ → Ω → ℝ) (a b t : ℝ) (ω : Ω) : ℝ :=
  1 / 2 * ∫ s in Set.Ioc (0 : ℝ) t, -l ^ 2 * g (X s ω) * indIoc Ω a b ω s ^ 2 ∂volume

/-- The drift term, with the indicator's idempotence used and the constants pulled out. -/
theorem trigDrift_eq (l : ℝ) {g : ℝ → ℝ} (X : ℝ → Ω → ℝ) (a b t : ℝ) (ω : Ω) :
    trigDrift l g X a b t ω
      = -(l ^ 2 / 2) * ∫ s in Set.Ioc (0 : ℝ) t, g (X s ω) * indIoc Ω a b ω s ∂volume := by
  rw [trigDrift]
  simp only [indIoc_sq]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  ring

/-- **The pairing is bounded by its own running integral.** If a weight `Y` has mean zero and
pairs to zero with `A`, and `g (X_t) − g (X_0) = A + trigDrift`, then the pairing of `Y` against
`g (X_t)` is at most `l²/2` times the integral of its own norm. -/
theorem norm_pairing_le_setIntegral_norm {a b : ℝ} {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ))
    {Y : Ω → ℂ} (hYm : Measurable Y) (hY : Integrable Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    {A : Ω → ℝ} (hAperp : ∫ ω, Y ω * ((A ω : ℝ) : ℂ) ∂P = 0)
    {t : ℝ} (ht : 0 < t)
    (hIto : ∀ᵐ ω ∂P, g (X t ω) - g (X 0 ω) = A ω + trigDrift l g X a b t ω) :
    ‖∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P‖
      ≤ l ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ) t, ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖ := by
  classical
  have hgm : ∀ u : ℝ, Measurable fun ω : Ω => ((g (X u ω) : ℝ) : ℂ) := fun u =>
    Complex.measurable_ofReal.comp (hgc.measurable.comp
      (hXm.comp ((measurable_id (α := Ω)).prodMk measurable_const)))
  have hgbC : ∀ (u : ℝ) (ω : Ω), ‖((g (X u ω) : ℝ) : ℂ)‖ ≤ 1 := by
    intro u ω
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgb _
  have hint : ∀ u : ℝ, Integrable (fun ω => Y ω * ((g (X u ω) : ℝ) : ℂ)) P := fun u =>
    integrable_mul_of_bounded hY (hgm u).aestronglyMeasurable (hgbC u)
  -- the pairing vanishes at time zero
  have hΛ0 : ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = 0 := by
    have hcong : ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = ∫ ω, Y ω * ((g 0 : ℝ) : ℂ) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hX0] with ω hω
      rw [hω]
    rw [hcong, integral_mul_const, hY0, zero_mul]
  -- the drift term is bounded and measurable
  have hjoint : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      -l ^ 2 * g (X s ω) * indIoc Ω a b ω s ^ 2) := by
    have h1 : Measurable fun p : Ω × ℝ => -l ^ 2 * g (X p.2 p.1) :=
      (hgc.measurable.comp hXm).const_mul _
    have h2 : Measurable fun p : Ω × ℝ => indIoc Ω a b p.1 p.2 ^ 2 :=
      (measurable_uncurry_indIoc a b).pow_const 2
    exact h1.mul h2
  have hDmeas : Measurable fun ω : Ω => ((trigDrift l g X a b t ω : ℝ) : ℂ) := by
    refine Complex.measurable_ofReal.comp ?_
    have hDr : Measurable (trigDrift l g X a b t) :=
      (StronglyMeasurable.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) t))
        hjoint.stronglyMeasurable).measurable.const_mul _
    exact hDr
  have hDbd : ∀ ω : Ω, ‖((trigDrift l g X a b t ω : ℝ) : ℂ)‖ ≤ l ^ 2 / 2 * t := by
    intro ω
    rw [Complex.norm_real, trigDrift_eq, Real.norm_eq_abs, abs_mul, abs_neg,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ l ^ 2 / 2)]
    have hb : |∫ s in Set.Ioc (0 : ℝ) t, g (X s ω) * indIoc Ω a b ω s ∂volume| ≤ 1 * t := by
      have hC : ∀ s ∈ Set.Ioc (0 : ℝ) t, ‖g (X s ω) * indIoc Ω a b ω s‖ ≤ 1 := by
        intro s _
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_one₀ (hgb _) (abs_nonneg _) (indIoc_le_one a b ω s)
      have hnorm := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Set.Ioc (0 : ℝ) t) (f := fun s => g (X s ω) * indIoc Ω a b ω s) (C := 1)
        (by simp [Real.volume_Ioc]) hC
      rw [Real.norm_eq_abs] at hnorm
      refine hnorm.trans (le_of_eq ?_)
      rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
      ring
    calc l ^ 2 / 2 * |∫ s in Set.Ioc (0 : ℝ) t, g (X s ω) * indIoc Ω a b ω s ∂volume|
        ≤ l ^ 2 / 2 * (1 * t) := mul_le_mul_of_nonneg_left hb (by positivity)
      _ = l ^ 2 / 2 * t := by ring
  have hYDint : Integrable (fun ω => Y ω * ((trigDrift l g X a b t ω : ℝ) : ℂ)) P :=
    integrable_mul_of_bounded hY hDmeas.aestronglyMeasurable hDbd
  have hYABint : Integrable
      (fun ω => Y ω * (((A ω + trigDrift l g X a b t ω : ℝ)) : ℂ)) P := by
    refine ((hint t).sub (hint 0)).congr ?_
    filter_upwards [hIto] with ω hω
    simp only [Pi.sub_apply, ← hω]
    push_cast
    ring
  have hYAint : Integrable (fun ω => Y ω * ((A ω : ℝ) : ℂ)) P := by
    have hsub : (fun ω => Y ω * ((A ω : ℝ) : ℂ))
        = fun ω => Y ω * (((A ω + trigDrift l g X a b t ω : ℝ)) : ℂ)
            - Y ω * ((trigDrift l g X a b t ω : ℝ) : ℂ) := by
      funext ω; push_cast; ring
    rw [hsub]
    exact hYABint.sub hYDint
  -- the pairing at time `t` is the pairing against the drift term
  have hΛt : ∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P
      = ∫ ω, Y ω * ((trigDrift l g X a b t ω : ℝ) : ℂ) ∂P := by
    have hcong : ∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P
        = ∫ ω, (Y ω * (((A ω + trigDrift l g X a b t ω : ℝ)) : ℂ)
            + Y ω * ((g (X 0 ω) : ℝ) : ℂ)) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hIto] with ω hω
      have hval : g (X t ω) = A ω + trigDrift l g X a b t ω + g (X 0 ω) := by linarith
      rw [hval]
      push_cast
      ring
    rw [hcong, integral_add hYABint (hint 0), hΛ0, add_zero]
    have hsplit : ∫ ω, Y ω * (((A ω + trigDrift l g X a b t ω : ℝ)) : ℂ) ∂P
        = (∫ ω, Y ω * ((A ω : ℝ) : ℂ) ∂P)
          + ∫ ω, Y ω * ((trigDrift l g X a b t ω : ℝ) : ℂ) ∂P := by
      rw [← integral_add hYAint hYDint]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      push_cast
      ring
    rw [hsplit, hAperp, zero_add]
  -- the drift pairing, by Fubini, is the running integral of the pairing
  have hstep1 : ∫ ω, Y ω * ((trigDrift l g X a b t ω : ℝ) : ℂ) ∂P
      = -((l ^ 2 / 2 : ℝ) : ℂ) * ∫ ω, Y ω *
          (∫ s in Set.Ioc (0 : ℝ) t, ((g (X s ω) * indIoc Ω a b ω s : ℝ) : ℂ)) ∂P := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp only [trigDrift_eq, integral_complex_ofReal]
    push_cast
    ring
  have hΦm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ((g (X s ω) * indIoc Ω a b ω s : ℝ) : ℂ)) :=
    Complex.measurable_ofReal.comp
      ((hgc.measurable.comp hXm).mul (measurable_uncurry_indIoc a b))
  have hΦb : ∀ (ω : Ω) (s : ℝ), ‖((g (X s ω) * indIoc Ω a b ω s : ℝ) : ℂ)‖ ≤ 1 := by
    intro ω s
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul]
    exact mul_le_one₀ (hgb _) (abs_nonneg _) (indIoc_le_one a b ω s)
  have hfub := LevyStochCalc.Probability.integral_mul_setIntegral_Ioc
    (a := (0 : ℝ)) (t := t) hYm hY hΦm hΦb
  have hinner : ∀ s : ℝ, ∫ ω, Y ω * ((g (X s ω) * indIoc Ω a b ω s : ℝ) : ℂ) ∂P
      = (∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
        * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ) := by
    intro s
    rw [← integral_mul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    change Y ω * ((g (X s ω) * (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ) = _
    push_cast
    ring
  -- the pairing is uniformly bounded and measurable in time
  have hΛmeas : Measurable fun u : ℝ => ∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P :=
    measurable_pairing hYm hXm hgc
  have hΛbd : ∀ u : ℝ, ‖∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P‖ ≤ ∫ ω, ‖Y ω‖ ∂P := by
    intro u
    refine (norm_integral_le_integral_norm _).trans (integral_mono (hint u).norm hY.norm ?_)
    intro ω
    calc ‖Y ω * ((g (X u ω) : ℝ) : ℂ)‖ = ‖Y ω‖ * ‖((g (X u ω) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖Y ω‖ * 1 := mul_le_mul_of_nonneg_left (hgbC u ω) (norm_nonneg _)
      _ = ‖Y ω‖ := mul_one _
  have hIntΛ : IntegrableOn
      (fun s => ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖) (Set.Ioc (0 : ℝ) t) volume := by
    refine Measure.integrableOn_of_bounded (M := ∫ ω, ‖Y ω‖ ∂P) (by simp [Real.volume_Ioc])
      hΛmeas.norm.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact hΛbd s
  have hIntΛind : IntegrableOn (fun s => ‖(∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
      * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ)‖) (Set.Ioc (0 : ℝ) t) volume := by
    have hmeas : Measurable fun s : ℝ => ‖(∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
        * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ)‖ :=
      (hΛmeas.mul (Complex.measurable_ofReal.comp
        (measurable_const.indicator measurableSet_Ioc))).norm
    refine Measure.integrableOn_of_bounded (M := ∫ ω, ‖Y ω‖ ∂P) (by simp [Real.volume_Ioc])
      hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun s => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), norm_mul, Complex.norm_real,
      Real.norm_eq_abs]
    refine le_trans (mul_le_of_le_one_right (norm_nonneg _) ?_) (hΛbd s)
    by_cases h : s ∈ Set.Ioc a b
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  have hbound : ‖∫ s in Set.Ioc (0 : ℝ) t, (∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P)
        * (((Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s : ℝ) : ℂ)‖
      ≤ ∫ s in Set.Ioc (0 : ℝ) t, ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖ := by
    refine (norm_integral_le_integral_norm _).trans (integral_mono hIntΛind hIntΛ fun s => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    refine mul_le_of_le_one_right (norm_nonneg _) ?_
    by_cases h : s ∈ Set.Ioc a b
    · simp [Set.indicator_of_mem h]
    · simp [Set.indicator_of_notMem h]
  rw [hΛt, hstep1, hfub]
  simp only [hinner]
  rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ l ^ 2 / 2)]
  exact mul_le_mul_of_nonneg_left hbound (by positivity)

/-- The pairing vanishes at time zero when the weight has mean zero. -/
theorem pairing_zero_time {X : ℝ → Ω → ℝ} (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ))
    {Y : Ω → ℂ} (hY0 : ∫ ω, Y ω ∂P = 0) (g : ℝ → ℝ) :
    ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = 0 := by
  have hcong : ∫ ω, Y ω * ((g (X 0 ω) : ℝ) : ℂ) ∂P = ∫ ω, Y ω * ((g 0 : ℝ) : ℂ) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hX0] with ω hω
    rw [hω]
  rw [hcong, integral_mul_const, hY0, zero_mul]

/-- **Grönwall closes the cell.** A pairing bounded by its own running integral, and vanishing at
time zero, vanishes on the whole window. -/
theorem pairing_eq_zero_of_norm_le {b : ℝ} {X : ℝ → Ω → ℝ}
    (hXm : Measurable (Function.uncurry fun ω s => X s ω)) (hX0 : X 0 =ᵐ[P] fun _ => (0 : ℝ))
    {Y : Ω → ℂ} (hYm : Measurable Y) (hY : Integrable Y P) (hY0 : ∫ ω, Y ω ∂P = 0)
    (l : ℝ) {g : ℝ → ℝ} (hgc : Continuous g) (hgb : ∀ x, |g x| ≤ 1)
    (hstep : ∀ t : ℝ, 0 < t → t ≤ b →
      ‖∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P‖
        ≤ l ^ 2 / 2 * ∫ s in Set.Ioc (0 : ℝ) t, ‖∫ ω, Y ω * ((g (X s ω) : ℝ) : ℂ) ∂P‖) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, ∫ ω, Y ω * ((g (X t ω) : ℝ) : ℂ) ∂P = 0 := by
  have hgm : ∀ u : ℝ, Measurable fun ω : Ω => ((g (X u ω) : ℝ) : ℂ) := fun u =>
    Complex.measurable_ofReal.comp (hgc.measurable.comp
      (hXm.comp ((measurable_id (α := Ω)).prodMk measurable_const)))
  have hgbC : ∀ (u : ℝ) (ω : Ω), ‖((g (X u ω) : ℝ) : ℂ)‖ ≤ 1 := by
    intro u ω
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hgb _
  have hint : ∀ u : ℝ, Integrable (fun ω => Y ω * ((g (X u ω) : ℝ) : ℂ)) P := fun u =>
    integrable_mul_of_bounded hY (hgm u).aestronglyMeasurable (hgbC u)
  have hΛmeas : Measurable fun u : ℝ => ∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P :=
    measurable_pairing hYm hXm hgc
  have hΛbd : ∀ u : ℝ, ‖∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P‖ ≤ ∫ ω, ‖Y ω‖ ∂P := by
    intro u
    refine (norm_integral_le_integral_norm _).trans (integral_mono (hint u).norm hY.norm ?_)
    intro ω
    calc ‖Y ω * ((g (X u ω) : ℝ) : ℂ)‖ = ‖Y ω‖ * ‖((g (X u ω) : ℝ) : ℂ)‖ := norm_mul _ _
      _ ≤ ‖Y ω‖ * 1 := mul_le_mul_of_nonneg_left (hgbC u ω) (norm_nonneg _)
      _ = ‖Y ω‖ := mul_one _
  have hzero := LevyStochCalc.Analysis.eq_zero_of_le_mul_setIntegral
    (a := (0 : ℝ)) (b := b) (c := l ^ 2 / 2) (B := ∫ ω, ‖Y ω‖ ∂P) (by positivity)
    (f := fun u => ‖∫ ω, Y ω * ((g (X u ω) : ℝ) : ℂ) ∂P‖) hΛmeas.norm
    (fun u => norm_nonneg _) (fun u _ => hΛbd u) ?_
  · intro t ht
    have := hzero t ht
    simpa using this
  · rintro t ⟨ht0, htb⟩
    rcases eq_or_lt_of_le ht0 with rfl | ht0'
    · rw [pairing_zero_time hX0 hY0 g]
      simp
    · exact hstep t ht0' htb

end Equation

end LevyStochCalc.Brownian.Ito
