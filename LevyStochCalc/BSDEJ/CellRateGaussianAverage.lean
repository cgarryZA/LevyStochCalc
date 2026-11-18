/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CellMomentBound
import LevyStochCalc.BSDEJ.CellRateMartingale
import LevyStochCalc.Brownian.GaussianRegression

/-!
# Conditional averages of the control process for a Gaussian terminal datum

Let `W` be the Brownian motion of a Lévy driver with one Brownian coordinate, `ℱ` a Brownian
filtration for it, and `(Y, Z)` solve, for `t ∈ [0, T]`,

  `Y_t = g(ξ₀ + W_T σ) + ∫_t^T h − (∫_0^T Z dW − ∫_0^t Z dW)`

with `ξ₀` square-integrable and measurable at `0`, `σ ∈ ℝⁿ`, `g` an `L`-Lipschitz function on
`ℝⁿ`, `h` a deterministic function of time and `Y` adapted. For `0 ≤ t < T` put

  `N_t = (T − t)⁻¹ E[∫_t^T Z_s ds | ℱ_t]`.

The Gaussian regression of `W_r − W_t` on `W_T − W_t` shows that the conditional average of `Z`
over every interval `[t, r] ⊆ [0, T]` with left endpoint `t` equals `N_t`. The duality bound
against the increment `W_T − W_t` gives `E N_t² ≤ L² ‖σ‖²`, and `N_t = E[N_{t'} | ℱ_t]` for
`t ≤ t' < T`, so `t ↦ E N_t²` is nondecreasing.

## Main statements

* `condAvgToHorizon` — the conditional average `N_t` over the remaining horizon.
* `condAvg_eq_condAvg_terminal` — the conditional averages over `[t, r]` and `[t, T]` agree.
* `integral_condAvgToHorizon_sq_le` — `E N_t² ≤ L² ‖σ‖²`.
* `condAvgToHorizon_eq_condExp` — `N_t = E[N_{t'} | ℱ_t]`, and
  `integral_condAvgToHorizon_sq_mono`.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Helpers

/-- A Brownian motion is square-integrable at every nonnegative time. -/
theorem memLp_brownian_eval (W : Brownian.BrownianMotion P) {t : ℝ} (ht : 0 ≤ t) :
    MemLp (W.W t) 2 P := by
  rcases eq_or_lt_of_le ht with rfl | ht'
  · exact (memLp_const (0 : ℝ)).ae_eq (by
      filter_upwards [W.initial_zero] with ω hω using hω.symm)
  · refine (Brownian.Ito.memLp_increment W le_rfl ht' 2 (by norm_num)).ae_eq ?_
    filter_upwards [W.initial_zero] with ω hω
    simp [hω]

omit [IsProbabilityMeasure P] in
/-- A square-integrable real variable times a fixed vector is square-integrable. -/
theorem memLp_smul_const {n : ℕ} {f : Ω → ℝ} (hf : MemLp f 2 P) (σ : Fin n → ℝ) :
    MemLp (fun ω => f ω • σ) 2 P :=
  MemLp.of_le (hf.norm.mul_const ‖σ‖)
    (hf.aestronglyMeasurable.smul aestronglyMeasurable_const)
    (Eventually.of_forall fun ω => by
      rw [norm_smul, Real.norm_eq_abs (‖f ω‖ * ‖σ‖), abs_of_nonneg (by positivity)])

/-- For a square-integrable `M` and an `ℱ`-measurable `η` with `η M` and `η E[M | ℱ]`
integrable, the pairing of `η` with `M` is the pairing with its conditional expectation. -/
theorem integral_mul_condExp_eq (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (t : ℝ) {η M : Ω → ℝ}
    (hηm : StronglyMeasurable[ℱ t] η) (hη : MemLp η 2 P) (hM : MemLp M 2 P) :
    ∫ ω, η ω * M ω ∂P = ∫ ω, η ω * P[M | ℱ t] ω ∂P := by
  have hce := condExp_mul_of_stronglyMeasurable_left (m := ℱ t) hηm (hη.integrable_mul hM)
    (hM.integrable one_le_two)
  calc ∫ ω, η ω * M ω ∂P = ∫ ω, P[η * M | ℱ t] ω ∂P := (integral_condExp (ℱ.le t)).symm
    _ = _ := integral_congr_ae hce

end Helpers

/-- The conditional average at `t` of `f` over the remaining horizon `[t, T]`. -/
noncomputable def condAvgToHorizon (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (P : Measure Ω)
    (T : ℝ) (f : ℝ → Ω → ℝ) (t : ℝ) : Ω → ℝ := fun ω =>
  (T - t)⁻¹ * P[fun ω' => ∫ s in Set.Icc t T, f s ω' | ℱ t] ω

omit [IsProbabilityMeasure P] in
/-- The conditional average over the remaining horizon is measurable at its time. -/
theorem stronglyMeasurable_condAvgToHorizon (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (T : ℝ)
    (f : ℝ → Ω → ℝ) (t : ℝ) : StronglyMeasurable[ℱ t] (condAvgToHorizon ℱ P T f t) :=
  stronglyMeasurable_condExp.const_mul _

omit [IsProbabilityMeasure P] in
/-- The conditional average over the remaining horizon of a process of finite energy is
square-integrable. -/
theorem memLp_condAvgToHorizon (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ}
    {f : ℝ → Ω → ℝ} (hf : Measurable (Function.uncurry fun ω s => f s ω))
    (hfs : ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) {t : ℝ}
    (ht : 0 ≤ t) (htT : t < T) : MemLp (condAvgToHorizon ℱ P T f t) 2 P := by
  have hc : ∫⁻ ω, ∫⁻ s in Set.Icc t T, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc ht le_rfl))
      hfs
  exact memLp_condIntervalAvg ℱ t htT hf hc

section Identification

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  (D : Driver.LevyDriver.{u, v, w} P 1 ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {Z : ℝ → Ω → (Fin 1 → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
  (hZs : ∀ k, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc 0 T', (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hcoord in
/-- The vector stochastic integral against a one-dimensional Brownian motion is the scalar one. -/
theorem stochasticIntegral_fin_one (t : ℝ) (ω : Ω) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp hZs t ω
      = Brownian.Ito.stochasticIntegralBrownian (D.W.W 0) ℱ (hcoord 0) (fun ω s => Z s ω 0)
        (hZm 0) (hZp 0) (hZs 0) t ω := by
  simp [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
    Brownian.Ito.stochasticIntegral]

include hcoord in
/-- The vector stochastic integral is square-integrable at every time. -/
theorem memLp_stochasticIntegral_fin_one (t : ℝ) :
    MemLp (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
      hZs t) 2 P := by
  have h := Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W 0) ℱ (hcoord 0)
    (fun ω s => Z s ω 0) (hZm 0) (hZp 0) (hZs 0) t
  refine h.ae_eq (Eventually.of_forall fun ω => ?_)
  exact (stochasticIntegral_fin_one D ℱ hcoord hZm hZp hZs t ω).symm

include hcoord in
/-- **Orthogonality of the future increment of the integral.** For `0 ≤ r ≤ T` the increment of
the stochastic integral over `(r, T]` is orthogonal to every square-integrable variable
measurable at `r`. -/
theorem integral_increment_mul_eq_zero {r T : ℝ} (hrT : r ≤ T) {η : Ω → ℝ}
    (hηm : StronglyMeasurable[ℱ r] η) (hη : MemLp η 2 P) :
    ∫ ω, (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
        hZs T ω
      - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
        hZs r ω) * η ω ∂P = 0 := by
  set J := Brownian.Ito.stochasticIntegralBrownian (D.W.W 0) ℱ (hcoord 0) (fun ω s => Z s ω 0)
    (hZm 0) (hZp 0) (hZs 0) with hJ
  have hmart := Brownian.Ito.martingale_stochasticIntegralBrownian (D.W.W 0) ℱ (hcoord 0)
    (fun ω s => Z s ω 0) (hZm 0) (hZp 0) (hZs 0)
  have hJ2 : ∀ t, MemLp (J t) 2 P := fun t =>
    Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W 0) ℱ (hcoord 0) _ (hZm 0) (hZp 0)
      (hZs 0) t
  have h1 : ∫ ω, η ω * J T ω ∂P = ∫ ω, η ω * J r ω ∂P := by
    rw [integral_mul_condExp_eq ℱ r hηm hη (hJ2 T)]
    exact integral_congr_ae (by
      filter_upwards [hmart.condExp_ae_eq hrT] with ω hω
      rw [hω])
  have e : (fun ω => (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
        hZm hZp hZs T ω
      - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
        hZs r ω) * η ω) = fun ω => η ω * J T ω - η ω * J r ω := by
    funext ω
    rw [stochasticIntegral_fin_one, stochasticIntegral_fin_one]
    ring
  have i1 : Integrable (fun ω => η ω * J T ω) P := hη.integrable_mul (hJ2 T)
  have i2 : Integrable (fun ω => η ω * J r ω) P := hη.integrable_mul (hJ2 r)
  rw [e, integral_sub i1 i2, h1, sub_self]

omit [IsProbabilityMeasure P] in
private theorem setIntegral_mul_eq {G : Set Ω} (hG : MeasurableSet G) (f A : Ω → ℝ) :
    ∫ ω in G, f ω * A ω ∂P = ∫ ω, G.indicator f ω * A ω ∂P := by
  rw [← integral_indicator hG]
  exact integral_congr_ae (Eventually.of_forall fun ω => Set.indicator_mul_left G f A)

variable {T : ℝ} {n : ℕ} {ξ₀ : Ω → (Fin n → ℝ)} {σ : Fin n → ℝ} {g : (Fin n → ℝ) → ℝ}
  {L : ℝ≥0} {h : ℝ → ℝ} {Y : ℝ → Ω → ℝ}

include hcoord in
/-- The increment of the stochastic integral over `(t, T]` is the terminal datum plus the
integral of the driver over `[t, T]` minus `Y_t`. -/
theorem increment_ae_eq_terminal
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    (fun ω => Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
        hZs T ω
      - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
        hZs t ω)
      =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ) + (∫ s in Set.Icc t T, h s) - Y t ω := by
  filter_upwards [heq t ht] with ω hω
  rw [hω]; ring

include hcoord in
/-- The terminal datum, and the solution at each time of the horizon, are square-integrable. -/
theorem memLp_terminal_and_solution (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    MemLp (fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)) 2 P ∧ MemLp (Y t) 2 P := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hξT : MemLp (fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)) 2 P :=
    memLp_comp_of_lipschitzWith hg (hξ.add (memLp_smul_const (memLp_brownian_eval _ hT) σ))
  refine ⟨hξT, ?_⟩
  refine ((hξT.add (memLp_const (∫ s in Set.Icc t T, h s))).sub
    ((memLp_stochasticIntegral_fin_one D ℱ hcoord hZm hZp
    hZs T).sub (memLp_stochasticIntegral_fin_one D ℱ hcoord hZm hZp hZs t))).ae_eq ?_
  filter_upwards [heq t ht] with ω hω
  rw [hω]; rfl

include hcoord in
/-- **The regression identity for the stochastic integral.** For `0 ≤ t < r ≤ T` and an event
`G` measurable at `t`,
`E[1_G (I_r − I_t)(W_r − W_t)] = (r − t)/(T − t) · E[1_G (I_T − I_t)(W_T − W_t)]`, where `I` is
the stochastic integral of `Z`. -/
theorem setIntegral_increment_mul_regression (hξm : StronglyMeasurable[ℱ 0] ξ₀)
    (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {t r : ℝ} (ht : 0 ≤ t) (htr : t < r) (hrT : r ≤ T) {G : Set Ω}
    (hG : MeasurableSet[ℱ t] G) :
    ∫ ω in G, (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm
        hZp hZs r ω
      - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp hZs
        t ω) * ((D.W.W 0).W r ω - (D.W.W 0).W t ω) ∂P
      = (r - t) / (T - t) * ∫ ω in G, (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
          D.W ℱ hcoord Z hZm hZp hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp hZs
          t ω) * ((D.W.W 0).W T ω - (D.W.W 0).W t ω) ∂P := by
  set W := D.W.W 0 with hWdef
  set I := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
    hZs with hIdef
  set ξT : Ω → ℝ := fun ω => g (ξ₀ ω + W.W T ω • σ) with hξTdef
  set c : ℝ := ∫ s in Set.Icc t T, h s with hc
  have htI : t ∈ Set.Icc 0 T := ⟨ht, htr.le.trans hrT⟩
  have hrI : r ∈ Set.Icc 0 T := ⟨ht.trans htr.le, hrT⟩
  have hGm : MeasurableSet G := ℱ.le t G hG
  obtain ⟨hξT2, hY2⟩ := memLp_terminal_and_solution D ℱ hcoord hZm hZp hZs hξ hg heq htI
  have hI2 : ∀ u, MemLp (I u) 2 P := memLp_stochasticIntegral_fin_one D ℱ hcoord hZm hZp hZs
  have hA2 : MemLp (fun ω => W.W r ω - W.W t ω) 2 P :=
    Brownian.Ito.memLp_increment W ht htr 2 (by norm_num)
  have hS2 : MemLp (fun ω => W.W T ω - W.W t ω) 2 P :=
    Brownian.Ito.memLp_increment W ht (htr.trans_le hrT) 2 (by norm_num)
  -- the part of `I_T − I_t` measurable at `t` is orthogonal to the increments after `t`
  have hcY : ∀ {b : ℝ}, t < b → ∫ ω, G.indicator (fun ω => c - Y t ω) ω
      * (W.W b ω - W.W t ω) ∂P = 0 := by
    intro b htb
    have hm : StronglyMeasurable[ℱ t] (G.indicator fun ω => c - Y t ω) :=
      (stronglyMeasurable_const.sub (hYa t htI)).indicator hG
    have h := Brownian.Ito.integral_mul_increment_pow W ℱ (hcoord 0) ht htb hm
      (hm.mono (ℱ.le t)).measurable 1
    rw [Brownian.Ito.integral_increment_pow_odd W ht htb odd_one, mul_zero] at h
    simpa only [pow_one] using h
  -- `I_T − I_t` against an increment after `t`
  have hsplit : ∀ {b : ℝ}, t < b → b ≤ T → ∫ ω in G, (I T ω - I t ω) * (W.W b ω - W.W t ω) ∂P
      = ∫ ω, G.indicator ξT ω * (W.W b ω - W.W t ω) ∂P := by
    intro b htb hbT
    have hB2 : MemLp (fun ω => W.W b ω - W.W t ω) 2 P :=
      Brownian.Ito.memLp_increment W ht htb 2 (by norm_num)
    rw [setIntegral_mul_eq hGm]
    have hae := increment_ae_eq_terminal D ℱ hcoord hZm hZp hZs heq htI
    calc ∫ ω, G.indicator (fun ω => I T ω - I t ω) ω * (W.W b ω - W.W t ω) ∂P
        = ∫ ω, (G.indicator ξT ω * (W.W b ω - W.W t ω)
            + G.indicator (fun ω => c - Y t ω) ω * (W.W b ω - W.W t ω)) ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hae] with ω hω
          by_cases hωG : ω ∈ G
          · simp only [Set.indicator_of_mem hωG]
            rw [hω]; ring
          · simp [Set.indicator_of_notMem hωG]
      _ = _ := by
          have i1 : Integrable (fun ω => G.indicator ξT ω * (W.W b ω - W.W t ω)) P :=
            (hξT2.indicator hGm).integrable_mul hB2
          have i2 : Integrable (fun ω => G.indicator (fun ω => c - Y t ω) ω
              * (W.W b ω - W.W t ω)) P :=
            (((memLp_const c).sub hY2).indicator hGm).integrable_mul hB2
          rw [integral_add i1 i2, hcY htb, add_zero]
  -- the regression
  have hΦm : StronglyMeasurable[ℱ t ⊔ MeasurableSpace.comap (fun ω => W.W T ω - W.W t ω)
      inferInstance] (G.indicator ξT) := by
    have hξ' : StronglyMeasurable[ℱ t ⊔ MeasurableSpace.comap (fun ω => W.W T ω - W.W t ω)
        inferInstance] ξ₀ := (hξm.mono ((ℱ.mono ht).trans le_sup_left))
    have hWt : StronglyMeasurable[ℱ t ⊔ MeasurableSpace.comap (fun ω => W.W T ω - W.W t ω)
        inferInstance] (W.W t) :=
      ((hcoord 0).measurable t).stronglyMeasurable.mono le_sup_left
    have hSm : StronglyMeasurable[ℱ t ⊔ MeasurableSpace.comap (fun ω => W.W T ω - W.W t ω)
        inferInstance] (fun ω => W.W T ω - W.W t ω) :=
      (comap_measurable _).stronglyMeasurable.mono le_sup_right
    have hrepr : ξT = fun ω => g (ξ₀ ω + (W.W t ω + (W.W T ω - W.W t ω)) • σ) := by
      funext ω; simp only [hξTdef, add_sub_cancel]
    rw [hrepr]
    refine StronglyMeasurable.indicator ?_ (le_sup_left (b := MeasurableSpace.comap
      (fun ω => W.W T ω - W.W t ω) inferInstance) G hG)
    exact hg.continuous.comp_stronglyMeasurable (hξ'.add ((hWt.add hSm).smul_const σ))
  have hreg := Brownian.integral_mul_increment_eq_regression W ℱ (hcoord 0) ht htr hrT hΦm
    (hξT2.indicator hGm)
  -- the increment over `(r, T]` is orthogonal to `1_G (W_r − W_t)`
  have hfut : ∫ ω in G, (I T ω - I r ω) * (W.W r ω - W.W t ω) ∂P = 0 := by
    rw [← integral_indicator hGm]
    have hAm : StronglyMeasurable[ℱ r] (G.indicator fun ω => W.W r ω - W.W t ω) :=
      (((hcoord 0).measurable r).sub (((hcoord 0).measurable t).mono (ℱ.mono htr.le)
        le_rfl)).stronglyMeasurable.indicator (ℱ.mono htr.le G hG)
    have h0 := integral_increment_mul_eq_zero D ℱ hcoord hZm hZp hZs hrT hAm
      (hA2.indicator hGm)
    rw [← h0]
    exact integral_congr_ae (Eventually.of_forall fun ω => Set.indicator_mul_right G _ _)
  have i1 : Integrable (fun ω => (I T ω - I t ω) * (W.W r ω - W.W t ω)) P :=
    ((hI2 T).sub (hI2 t)).integrable_mul hA2
  have i2 : Integrable (fun ω => (I T ω - I r ω) * (W.W r ω - W.W t ω)) P :=
    ((hI2 T).sub (hI2 r)).integrable_mul hA2
  have e1 : ∫ ω in G, (I r ω - I t ω) * (W.W r ω - W.W t ω) ∂P
      = ∫ ω in G, (I T ω - I t ω) * (W.W r ω - W.W t ω) ∂P
        - ∫ ω in G, (I T ω - I r ω) * (W.W r ω - W.W t ω) ∂P := by
    rw [← integral_sub i1.integrableOn i2.integrableOn]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
  rw [e1, hfut, sub_zero, hsplit htr hrT, hsplit (htr.trans_le hrT) le_rfl, hreg]

include hcoord in
/-- **The conditional averages over `[t, r]` and `[t, T]` agree.** For `0 ≤ t < r ≤ T` the
conditional average at `t` of `Z` over `[t, r]` is its conditional average at `t` over the
remaining horizon `[t, T]`. -/
theorem condAvg_eq_condAvg_terminal
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {t r : ℝ} (ht : 0 ≤ t) (htr : t < r) (hrT : r ≤ T) :
    (fun ω => (r - t)⁻¹ * P[fun ω' => ∫ s in Set.Icc t r, Z s ω' 0 | ℱ t] ω)
      =ᵐ[P] fun ω => (T - t)⁻¹ * P[fun ω' => ∫ s in Set.Icc t T, Z s ω' 0 | ℱ t] ω := by
  set W := D.W.W 0 with hWdef
  set I := Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
    hZs with hIdef
  have htT : t < T := htr.trans_le hrT
  have hI2 : ∀ u, MemLp (I u) 2 P := memLp_stochasticIntegral_fin_one D ℱ hcoord hZm hZp hZs
  have hA2 : MemLp (fun ω => W.W r ω - W.W t ω) 2 P :=
    Brownian.Ito.memLp_increment W ht htr 2 (by norm_num)
  have hS2 : MemLp (fun ω => W.W T ω - W.W t ω) 2 P :=
    Brownian.Ito.memLp_increment W ht htT 2 (by norm_num)
  have hfA : Integrable (fun ω => (I r ω - I t ω) * (W.W r ω - W.W t ω)) P :=
    ((hI2 r).sub (hI2 t)).integrable_mul hA2
  have hfS : Integrable (fun ω => (I T ω - I t ω) * (W.W T ω - W.W t ω)) P :=
    ((hI2 T).sub (hI2 t)).integrable_mul hS2
  have hA := condExp_increment_mul_increment D ℱ hcoord hZm hZp hZs ht htr 0
  have hS := condExp_increment_mul_increment D ℱ hcoord hZm hZp hZs ht htT 0
  have hkey : (fun ω => (r - t) / (T - t)
        * P[fun ω => (I T ω - I t ω) * (W.W T ω - W.W t ω) | ℱ t] ω)
      =ᵐ[P] P[fun ω => (I r ω - I t ω) * (W.W r ω - W.W t ω) | ℱ t] := by
    refine ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le t) hfA
      (fun _ _ _ => (integrable_condExp.const_mul _).integrableOn) (fun G hG _ => ?_)
      (stronglyMeasurable_condExp.const_mul _).aestronglyMeasurable
    rw [integral_const_mul, setIntegral_condExp (ℱ.le t) hfS hG]
    exact (setIntegral_increment_mul_regression D ℱ hcoord hZm hZp hZs hξm hξ hg hYa heq ht htr
      hrT hG).symm
  filter_upwards [hA, hS, hkey] with ω e1 e2 e3
  rw [← e1, ← e3, e2]
  have h1 : r - t ≠ 0 := by linarith
  have h2 : T - t ≠ 0 := by linarith
  field_simp

include hcoord in
/-- **The second moment of the conditional average over the remaining horizon.** For
`0 ≤ t < T`, `E N_t² ≤ L² ‖σ‖²`, where `N_t` is the conditional average at `t` of `Z` over
`[t, T]`. -/
theorem integral_condAvgToHorizon_sq_le
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {t : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω ^ 2 ∂P ≤ (L : ℝ) ^ 2 * ‖σ‖ ^ 2 := by
  set W := D.W.W 0 with hWdef
  have htI : t ∈ Set.Icc 0 T := ⟨ht, htT.le⟩
  have hτ : 0 < T - t := sub_pos.mpr htT
  obtain ⟨hξT2, hY2⟩ := memLp_terminal_and_solution D ℱ hcoord hZm hZp hZs hξ hg heq htI
  have hZc : ∫⁻ ω, ∫⁻ s in Set.Icc t T, (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc ht le_rfl))
      (hZs 0 T (ht.trans_lt htT))
  set V : Ω → ℝ := P[fun ω' => ∫ s in Set.Icc t T, Z s ω' 0 | ℱ t] with hVdef
  have hVm : StronglyMeasurable[ℱ t] V := stronglyMeasurable_condExp
  have hV : MemLp V 2 P := (memLp_integral_interval htT (hZm 0) hZc).condExp one_le_two
  set gV : Ω → ℝ := fun ω => g (ξ₀ ω + W.W t ω • σ) with hgV
  have hgV2 : MemLp gV 2 P :=
    memLp_comp_of_lipschitzWith hg (hξ.add (memLp_smul_const (memLp_brownian_eval _ ht) σ))
  have hgVm : StronglyMeasurable[ℱ t] gV :=
    hg.continuous.comp_stronglyMeasurable ((hξm.mono (ℱ.mono ht)).add
      (((hcoord 0).measurable t).stronglyMeasurable.smul_const σ))
  set G : Ω → ℝ := fun ω => g (ξ₀ ω + W.W T ω • σ) - gV ω with hGdef
  set D' : Ω → ℝ := fun ω => gV ω + (∫ s in Set.Icc t T, h s) - Y t ω with hD'def
  have hG2 : MemLp G 2 P := hξT2.sub hgV2
  have hD'2 : MemLp D' 2 P := (hgV2.add (memLp_const _)).sub hY2
  have hD'm : StronglyMeasurable[ℱ t] D' :=
    (hgVm.add stronglyMeasurable_const).sub (hYa t htI)
  have hVeq : V =ᵐ[P] P[fun ω => (G ω + D' ω) * (W.W T ω - W.W t ω) | ℱ t] := by
    refine (condExp_increment_mul_increment D ℱ hcoord hZm hZp hZs ht htT 0).symm.trans ?_
    refine condExp_congr_ae ?_
    filter_upwards [increment_ae_eq_terminal D ℱ hcoord hZm hZp hZs heq htI] with ω hω
    rw [hω]
    simp only [hGdef, hD'def]
    ring
  have hdual := integral_sq_le_of_eq_condExp_mul_increment W ℱ (hcoord 0) ht htT hVm hV hD'm
    hD'2 hG2 hVeq
  have hS2 : MemLp (fun ω => W.W T ω - W.W t ω) 2 P :=
    Brownian.Ito.memLp_increment W ht htT 2 (by norm_num)
  have hGle : ∫ ω, G ω ^ 2 ∂P ≤ (L : ℝ) ^ 2 * ‖σ‖ ^ 2 * (T - t) := by
    rw [← Brownian.Ito.integral_increment_sq W ht htT, ← integral_const_mul]
    refine integral_mono hG2.integrable_sq (hS2.integrable_sq.const_mul _) fun ω => ?_
    have h1 := hg.norm_sub_le (ξ₀ ω + W.W T ω • σ) (ξ₀ ω + W.W t ω • σ)
    rw [add_sub_add_left_eq_sub, ← sub_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      at h1
    have h2 : |G ω| ≤ (L : ℝ) * ‖σ‖ * |W.W T ω - W.W t ω| := by
      simp only [hGdef, hgV]; linarith
    calc G ω ^ 2 = |G ω| ^ 2 := (sq_abs _).symm
      _ ≤ ((L : ℝ) * ‖σ‖ * |W.W T ω - W.W t ω|) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h2 2
      _ = (L : ℝ) ^ 2 * ‖σ‖ ^ 2 * (W.W T ω - W.W t ω) ^ 2 := by rw [mul_pow, mul_pow, sq_abs]
  have hV2 : ∫ ω, V ω ^ 2 ∂P ≤ (T - t) ^ 2 * ((L : ℝ) ^ 2 * ‖σ‖ ^ 2) := by
    calc ∫ ω, V ω ^ 2 ∂P ≤ (T - t) * ∫ ω, G ω ^ 2 ∂P := hdual
      _ ≤ (T - t) * ((L : ℝ) ^ 2 * ‖σ‖ ^ 2 * (T - t)) := by gcongr
      _ = _ := by ring
  have hpt : (fun ω => condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω ^ 2)
      = fun ω => ((T - t) ^ 2)⁻¹ * V ω ^ 2 := by
    funext ω; simp only [condAvgToHorizon, hVdef]; rw [mul_pow, inv_pow]
  rw [hpt, integral_const_mul]
  calc ((T - t) ^ 2)⁻¹ * ∫ ω, V ω ^ 2 ∂P
      ≤ ((T - t) ^ 2)⁻¹ * ((T - t) ^ 2 * ((L : ℝ) ^ 2 * ‖σ‖ ^ 2)) := by gcongr
    _ = _ := by field_simp

include hcoord in
/-- **The conditional averages over the remaining horizon form a martingale.** For
`0 ≤ t < t' < T`, `N_t = E[N_{t'} | ℱ_t]`. -/
theorem condAvgToHorizon_eq_condExp
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {t t' : ℝ} (ht : 0 ≤ t) (htt' : t < t') (ht'T : t' < T) :
    condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t
      =ᵐ[P] P[condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' | ℱ t] := by
  have hT : 0 < T := ht.trans_lt (htt'.trans ht'T)
  have hZT := hZs 0 T hT
  have hsub : ∀ {a b : ℝ}, 0 ≤ a → b ≤ T → ∫⁻ ω, ∫⁻ s in Set.Icc a b,
      (‖Z s ω 0‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun ha hb =>
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc ha hb)) hZT
  have hF1 := memLp_integral_interval htt' (hZm 0) (hsub ht ht'T.le)
  have hF2 := memLp_integral_interval ht'T (hZm 0) (hsub (ht.trans htt'.le) le_rfl)
  -- additivity of the time integral
  have hadd : (fun ω => ∫ s in Set.Icc t T, Z s ω 0)
      =ᵐ[P] (fun ω => ∫ s in Set.Icc t t', Z s ω 0) + fun ω => ∫ s in Set.Icc t' T, Z s ω 0 := by
    have hae := ae_memLp_interval (hZm 0) (hsub ht le_rfl)
    filter_upwards [hae] with ω hω
    haveI : IsFiniteMeasure (volume.restrict (Set.Icc t T)) :=
      ⟨by rw [Measure.restrict_apply_univ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top⟩
    have hint : IntegrableOn (fun s => Z s ω 0) (Set.Icc t T) := hω.integrable one_le_two
    rw [Pi.add_apply, ← Set.Icc_union_Ioc_eq_Icc htt'.le ht'T.le,
      setIntegral_union (Set.disjoint_left.mpr fun x hx hy => absurd hx.2 (not_le.mpr hy.1))
        measurableSet_Ioc (hint.mono_set (Set.Icc_subset_Icc le_rfl ht'T.le))
        (hint.mono_set (fun x hx => ⟨htt'.le.trans hx.1.le, hx.2⟩)),
      integral_Icc_eq_integral_Ioc (x := t')]
  have hcond := condAvg_eq_condAvg_terminal D ℱ hcoord hZm hZp hZs hξm hξ hg hYa heq ht htt'
    ht'T.le
  have htower : P[P[fun ω => ∫ s in Set.Icc t' T, Z s ω 0 | ℱ t'] | ℱ t]
      =ᵐ[P] P[fun ω => ∫ s in Set.Icc t' T, Z s ω 0 | ℱ t] :=
    condExp_condExp_of_le (ℱ.mono htt'.le) (ℱ.le t')
  have hscale : P[fun ω => ∫ s in Set.Icc t' T, Z s ω 0 | ℱ t']
      = fun ω => (T - t') * condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' ω := by
    funext ω
    simp only [condAvgToHorizon]
    have : T - t' ≠ 0 := by linarith
    field_simp
  have hsmul := condExp_smul (m := ℱ t) (μ := P) (T - t')
    (condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t')
  have hsum := condExp_add (m := ℱ t) (hF1.integrable one_le_two) (hF2.integrable one_le_two)
  filter_upwards [condExp_congr_ae (m := ℱ t) hadd, hsum, hcond, htower, hsmul] with
    ω e1 e2 e3 e4 e5
  rw [hscale] at e4
  have e5' : P[fun ω => (T - t') * condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' ω | ℱ t] ω
      = (T - t') * P[condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' | ℱ t] ω := e5
  rw [Pi.add_apply] at e2
  have hA : condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω
      = (T - t)⁻¹ * P[fun ω => ∫ s in Set.Icc t T, Z s ω 0 | ℱ t] ω := rfl
  have h1 : t' - t ≠ 0 := by linarith
  have h2 : T - t ≠ 0 := by linarith
  have h3 : T - t' ≠ 0 := by linarith
  have key : P[fun ω => ∫ s in Set.Icc t T, Z s ω 0 | ℱ t] ω
      = (t' - t) * condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω
        + (T - t') * P[condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' | ℱ t] ω := by
    rw [e1, e2, ← e4, e5', hA, ← e3]
    field_simp
  rw [hA] at key ⊢
  field_simp at key ⊢
  have e : (P[fun ω => ∫ s in Set.Icc t T, Z s ω 0 | ℱ t] ω
      - (T - t) * P[condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' | ℱ t] ω) * (T - t') = 0 := by
    linear_combination key
  rcases mul_eq_zero.mp e with e | e
  · linarith
  · exact absurd e h3

include hcoord in
/-- The second moment of the conditional average over the remaining horizon is nondecreasing
in time. -/
theorem integral_condAvgToHorizon_sq_mono
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z hZm hZp
          hZs t ω))
    {t t' : ℝ} (ht : 0 ≤ t) (htt' : t ≤ t') (ht'T : t' < T) :
    ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω ^ 2 ∂P
      ≤ ∫ ω, condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' ω ^ 2 ∂P := by
  rcases eq_or_lt_of_le htt' with rfl | hlt
  · exact le_rfl
  have hT : 0 < T := ht.trans_lt (htt'.trans_lt ht'T)
  have h := integral_sq_sub_eq_of_condExp_eq ℱ (stronglyMeasurable_condAvgToHorizon ℱ T _ t)
    (memLp_condAvgToHorizon ℱ (hZm 0) (hZs 0 T hT) ht (htt'.trans_lt ht'T))
    (memLp_condAvgToHorizon ℱ (hZm 0) (hZs 0 T hT) (ht.trans htt') ht'T)
    (condAvgToHorizon_eq_condExp D ℱ hcoord hZm hZp hZs hξm hξ hg hYa heq ht hlt ht'T).symm
  have h0 : 0 ≤ ∫ ω, (condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t' ω
      - condAvgToHorizon ℱ P T (fun s ω => Z s ω 0) t ω) ^ 2 ∂P :=
    integral_nonneg fun ω => sq_nonneg _
  linarith

end Identification

end LevyStochCalc.BSDEJ.PathRegularity
