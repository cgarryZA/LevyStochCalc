/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CondCellConvergence
import LevyStochCalc.Driver.CellConditionalIsometry
import LevyStochCalc.Brownian.ItoFourthMomentIncrements

/-!
# A second-moment bound for the control process from a Lipschitz decoupling field

Let `W` be the Brownian motion of a Lévy driver, `ℱ` a filtration that is Brownian for each of its
coordinates, and `(Y, Z)` a solution of the backward equation

  `Y_a = Y_b + ∫_a^b F_s ds − (∫_0^b Z dW − ∫_0^a Z dW)`,   `0 ≤ a ≤ b ≤ T`,

with a jointly measurable driver process `F` of energy at most `K_F` on `[0, T]`. Suppose
`Y_t = u(t, X_t)` almost surely for a deterministic field `u` that is `L`-Lipschitz in the state,
uniformly in time, and an adapted square-integrable process `X` with
`E ‖X_b − X_a‖² ≤ K (b − a)`. Then every conditional cell average of `Z` on every uniform grid
satisfies `E ‖Z̄_i‖² ≤ d (2 L² K + 2 K_F)`, and so `E ‖Z_t‖² ≤ d (2 L² K + 2 K_F)` for almost every
`t ∈ [0, T]`.

The proof works on one cell `[a, b]` at a time. The conditional cell average is the conditional
expectation of the increment of the stochastic integral against the Brownian increment
(`condExp_brownian_cell_mul_increment`); the increment of `Y` splits into
`u(b, X_b) − u(b, X_a)`, bounded by `L ‖X_b − X_a‖`, and `u(b, X_a) − u(a, X_a)`, measurable at
`a` and so orthogonal to the Brownian increment; and a variable `V`, measurable at `a`, equal to
the conditional expectation of `G ΔW` satisfies `E V² ≤ (b − a) E G²`.

## Main statements

* `integral_sq_le_of_eq_condExp_mul_increment` — the duality bound against a Brownian
  increment.
* `condExp_increment_mul_increment` — the cell identity for the vector stochastic integral.
* `lintegral_condCellAvg_sq_le_of_lipschitz` — the bound on the conditional cell averages.
* `ae_lintegral_sq_le_of_lipschitz` — the bound on the second moment of the control process.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.PathRegularity

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

section Duality

/-- **Duality bound against a Brownian increment.** Let `ℱ` be a Brownian filtration for `W`,
`0 ≤ a < b`, and `V`, `D` square-integrable and measurable at `a`. If `V` is the conditional
expectation at `a` of `(G + D) (W_b − W_a)` for a square-integrable `G`, then
`E V² ≤ (b − a) E G²`. -/
theorem integral_sq_le_of_eq_condExp_mul_increment (W : Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : Brownian.IsBrownianFiltration W ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {V G D : Ω → ℝ}
    (hVm : StronglyMeasurable[ℱ a] V) (hV : MemLp V 2 P)
    (hDm : StronglyMeasurable[ℱ a] D) (hD : MemLp D 2 P) (hG : MemLp G 2 P)
    (hVeq : V =ᵐ[P] P[fun ω => (G ω + D ω) * (W.W b ω - W.W a ω) | ℱ a]) :
    ∫ ω, V ω ^ 2 ∂P ≤ (b - a) * ∫ ω, G ω ^ 2 ∂P := by
  set Δ : Ω → ℝ := fun ω => W.W b ω - W.W a ω with hΔdef
  have hτ : 0 < b - a := sub_pos.mpr hab
  have hΔm : Measurable Δ := (W.measurable_eval b).sub (W.measurable_eval a)
  have hΔ2 : MemLp Δ 2 P := Brownian.Ito.memLp_increment W ha hab 2 (by norm_num)
  have hVmeas : Measurable V := (hVm.mono (ℱ.le a)).measurable
  have hIF : IndepFun V Δ P := by
    have hindepσ := hℱ.indep ha hab
    rw [IndepFun_iff]
    intro s t hs ht
    rw [Indep_iff] at hindepσ
    exact hindepσ s t (hVm.measurable.comap_le s hs) ht
  have hIF2 : IndepFun (fun ω => V ω ^ 2) (fun ω => Δ ω ^ 2) P :=
    hIF.comp (measurable_id.pow_const 2) (measurable_id.pow_const 2)
  have hVΔsq : Integrable (fun ω => (V ω * Δ ω) ^ 2) P := by
    have := hIF2.integrable_mul hV.integrable_sq hΔ2.integrable_sq
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  have hVΔ : MemLp (fun ω => V ω * Δ ω) 2 P :=
    (memLp_two_iff_integrable_sq (hVmeas.mul hΔm).aestronglyMeasurable).mpr hVΔsq
  have hVΔint : ∫ ω, (V ω * Δ ω) ^ 2 ∂P = (b - a) * ∫ ω, V ω ^ 2 ∂P := by
    have h := Brownian.Ito.integral_mul_increment_pow W ℱ hℱ ha hab
      (Y := fun ω => V ω ^ 2) (hVm.pow 2) (hVmeas.pow_const 2) 2
    rw [Brownian.Ito.integral_increment_sq W ha hab] at h
    rw [← mul_comm (b - a)] at h
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
  have hGD : MemLp (fun ω => G ω + D ω) 2 P := hG.add hD
  have hH : Integrable (fun ω => (G ω + D ω) * Δ ω) P := hGD.integrable_mul hΔ2
  have hVH : Integrable (V * fun ω => (G ω + D ω) * Δ ω) P := by
    have := hVΔ.integrable_mul hGD
    refine this.congr (Eventually.of_forall fun ω => ?_)
    simp only [Pi.mul_apply]
    ring
  have hce := condExp_mul_of_stronglyMeasurable_left (m := ℱ a) hVm hVH hH
  have hq : ∫ ω, V ω ^ 2 ∂P = ∫ ω, (V ω * Δ ω) * G ω ∂P + ∫ ω, (V ω * D ω) * Δ ω ∂P := by
    calc ∫ ω, V ω ^ 2 ∂P
        = ∫ ω, V ω * P[fun ω => (G ω + D ω) * Δ ω | ℱ a] ω ∂P := by
          refine integral_congr_ae ?_
          filter_upwards [hVeq] with ω hω
          rw [sq, ← hω]
      _ = ∫ ω, P[V * fun ω => (G ω + D ω) * Δ ω | ℱ a] ω ∂P :=
          integral_congr_ae (by filter_upwards [hce] with ω hω using hω.symm)
      _ = ∫ ω, V ω * ((G ω + D ω) * Δ ω) ∂P := integral_condExp (ℱ.le a)
      _ = ∫ ω, ((V ω * Δ ω) * G ω + (V ω * D ω) * Δ ω) ∂P :=
          integral_congr_ae (Eventually.of_forall fun ω => by simp only; ring)
      _ = _ := integral_add (hVΔ.integrable_mul hG)
          ((hVΔ.integrable_mul hD).congr (Eventually.of_forall fun ω => by
            simp only [Pi.mul_apply]; ring))
  have hzero : ∫ ω, (V ω * D ω) * Δ ω ∂P = 0 := by
    have h := Brownian.Ito.integral_mul_increment_pow W ℱ hℱ ha hab
      (Y := fun ω => V ω * D ω) (hVm.mul hDm) (hVmeas.mul ((hDm.mono (ℱ.le a)).measurable)) 1
    rw [Brownian.Ito.integral_increment_pow_odd W ha hab odd_one, mul_zero] at h
    simpa only [pow_one] using h
  rw [hzero, add_zero] at hq
  have hamgm : ∫ ω, (V ω * Δ ω) * G ω ∂P
      ≤ ∫ ω, ((V ω * Δ ω) ^ 2 / (2 * (b - a)) + (b - a) / 2 * G ω ^ 2) ∂P := by
    refine integral_mono (hVΔ.integrable_mul hG)
      ((hVΔsq.div_const _).add (hG.integrable_sq.const_mul _)) fun ω => ?_
    have h0 : 0 ≤ (V ω * Δ ω - (b - a) * G ω) ^ 2 / (2 * (b - a)) := by positivity
    have e : (V ω * Δ ω - (b - a) * G ω) ^ 2 / (2 * (b - a))
        = (V ω * Δ ω) ^ 2 / (2 * (b - a)) + (b - a) / 2 * G ω ^ 2
          - (V ω * Δ ω) * G ω := by field_simp; ring
    linarith
  rw [integral_add (hVΔsq.div_const _) (hG.integrable_sq.const_mul _), integral_div,
    integral_const_mul, hVΔint] at hamgm
  have e2 : (b - a) * (∫ ω, V ω ^ 2 ∂P) / (2 * (b - a)) = (∫ ω, V ω ^ 2 ∂P) / 2 := by
    field_simp
  rw [e2] at hamgm
  linarith

end Duality

section CellIdentity

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  (D : Driver.LevyDriver.{u, v, w} P d ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {Z : ℝ → Ω → (Fin d → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
  (hZs : ∀ k, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc 0 T', (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hcoord in
/-- **The cell identity.** For `0 ≤ a < b` the conditional expectation at `a` of the increment
over `(a, b]` of the vector stochastic integral of `Z` against the increment of the `k`-th
Brownian coordinate is the conditional expectation of the integral of `Z^k` over `[a, b]`. -/
theorem condExp_increment_mul_increment {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (k : Fin d) :
    P[fun ω => (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs b ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs a ω) * ((D.W.W k).W b ω - (D.W.W k).W a ω) | ℱ a]
      =ᵐ[P] P[fun ω => ∫ s in Set.Icc a b, Z s ω k | ℱ a] := by
  classical
  set J : Fin d → ℝ → Ω → ℝ := fun j t => Brownian.Ito.stochasticIntegralBrownian (D.W.W j) ℱ
    (hcoord j) (fun ω s => Z s ω j) (hZm j) (hZp j) (hZs j) t with hJ
  set f : Fin d → Ω → ℝ := fun j ω => (J j b ω - J j a ω) * ((D.W.W k).W b ω - (D.W.W k).W a ω)
    with hf
  have hpt : (fun ω => (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
        Z hZm hZp hZs b ω
      - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
        hZm hZp hZs a ω) * ((D.W.W k).W b ω - (D.W.W k).W a ω)) = ∑ j, f j := by
    funext ω
    simp only [Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral,
      Brownian.Ito.stochasticIntegral, Finset.sum_apply, hf, hJ, ← Finset.sum_sub_distrib,
      Finset.sum_mul]
  have hint : ∀ j ∈ Finset.univ, Integrable (f j) P := by
    intro j _
    exact ((Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ (hcoord j) _ (hZm j)
      (hZp j) (hZs j) b).sub (Brownian.Ito.stochasticIntegralBrownian_memLp (D.W.W j) ℱ
      (hcoord j) _ (hZm j) (hZp j) (hZs j) a)).integrable_mul
      (Brownian.Ito.memLp_increment (D.W.W k) ha hab 2 (by norm_num))
  have hterm : ∀ j, P[f j | ℱ a] =ᵐ[P]
      if j = k then P[fun ω => ∫ s in Set.Ioc a b, Z s ω k | ℱ a] else 0 := by
    intro j
    by_cases hjk : j = k
    · subst hjk
      rw [if_pos rfl]
      exact Driver.LevyDriver.condExp_brownian_cell_mul_increment (D := D) hcoord (i := j)
        (H := fun ω s => Z s ω j) (hZm j) (hZp j) (hZs j) ha hab
    · rw [if_neg hjk]
      exact Driver.LevyDriver.condExp_brownian_cell_mul_brownian_increment_eq_zero (D := D)
        hcoord hjk (H := fun ω s => Z s ω j) (hZm j) (hZp j) (hZs j) ha hab
  have hIcc : (fun ω => ∫ s in Set.Icc a b, Z s ω k)
      = fun ω => ∫ s in Set.Ioc a b, Z s ω k := by
    funext ω; exact integral_Icc_eq_integral_Ioc
  rw [hpt, hIcc]
  refine (condExp_finsetSum hint _).trans ?_
  filter_upwards [ae_all_iff.mpr hterm] with ω hω
  rw [Finset.sum_apply]
  simp only [hω]
  rw [Finset.sum_eq_single k (fun j _ hj => by rw [if_neg hj]; rfl)
    (fun h => absurd (Finset.mem_univ k) h), if_pos rfl]

end CellIdentity

section MomentBound

/-- A Lipschitz function of a square-integrable vector is square-integrable. -/
theorem memLp_comp_of_lipschitzWith {n : ℕ} {g : (Fin n → ℝ) → ℝ} {L : ℝ≥0}
    (hg : LipschitzWith L g) {X : Ω → (Fin n → ℝ)} (hX : MemLp X 2 P) :
    MemLp (fun ω => g (X ω)) 2 P := by
  refine MemLp.of_le ((memLp_const ‖g 0‖).add (hX.norm.const_mul (L : ℝ)))
    (hg.continuous.comp_aestronglyMeasurable hX.aestronglyMeasurable)
    (Eventually.of_forall fun ω => ?_)
  have h1 := hg.norm_sub_le (X ω) 0
  rw [sub_zero] at h1
  have h2 : ‖g (X ω)‖ ≤ ‖g 0‖ + (L : ℝ) * ‖X ω‖ := by
    have := norm_sub_norm_le (g (X ω)) (g 0)
    linarith
  exact h2.trans (Real.le_norm_self _)

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  (D : Driver.LevyDriver.{u, v, w} P d ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {Z : ℝ → Ω → (Fin d → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
  (hZs : ∀ k, ∀ T' : ℝ, 0 < T' →
    ∫⁻ ω, ∫⁻ s in Set.Icc 0 T', (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {T : ℝ} {Y F : ℝ → Ω → ℝ} {n : ℕ} {X : ℝ → Ω → (Fin n → ℝ)} {u : ℝ → (Fin n → ℝ) → ℝ}
  {L : ℝ≥0} {K : ℝ} {KF : ℝ≥0}

include hcoord in
/-- **Moment bound on a cell.** Under a Lipschitz decoupling field `Y_t = u(t, X_t)` with
`E ‖X_b − X_a‖² ≤ K (b − a)` and a driver process of energy at most `K_F` on `[0, T]`, every
coordinate of the conditional cell average of `Z` on a cell `[a, b] ⊆ [0, T]` has second moment
at most `2 L² K + 2 K_F`. -/
theorem integral_condIntervalAvg_sq_le_of_lipschitz
    (heq : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → Y a =ᵐ[P] fun ω => Y b ω
      + (∫ s in Set.Icc a b, F s ω)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs b ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs a ω))
    (hFm : Measurable (Function.uncurry fun ω s => F s ω))
    (hF : ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖F s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ KF)
    (hXm : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (X t))
    (hX2 : ∀ t ∈ Set.Icc 0 T, MemLp (X t) 2 P)
    (hXinc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂P ≤ K * (b - a))
    (hu : ∀ t, LipschitzWith L (u t))
    (hY : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => u t (X t ω))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hbT : b ≤ T) (k : Fin d) :
    ∫ ω, ((b - a)⁻¹ * P[fun ω' => ∫ s in Set.Icc a b, Z s ω' k | ℱ a] ω) ^ 2 ∂P
      ≤ 2 * (L : ℝ) ^ 2 * K + 2 * KF := by
  have hτ : 0 < b - a := sub_pos.mpr hab
  have hT : 0 < T := hτ.trans_le (by linarith)
  have haI : a ∈ Set.Icc 0 T := ⟨ha, by linarith⟩
  have hbI : b ∈ Set.Icc 0 T := ⟨by linarith, hbT⟩
  have hsub : Set.Icc a b ⊆ Set.Icc 0 T := Set.Icc_subset_Icc ha hbT
  have hZc : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set hsub) (hZs k T hT)
  have hFc : ∫⁻ ω, ∫⁻ s in Set.Icc a b, (‖F s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ KF :=
    le_trans (lintegral_mono fun ω => lintegral_mono_set hsub) hF
  have hFc' := lt_of_le_of_lt hFc ENNReal.coe_lt_top
  set V : Ω → ℝ := P[fun ω' => ∫ s in Set.Icc a b, Z s ω' k | ℱ a] with hVdef
  set Δ : Ω → ℝ := fun ω => (D.W.W k).W b ω - (D.W.W k).W a ω with hΔdef
  set IF : Ω → ℝ := fun ω => ∫ s in Set.Icc a b, F s ω with hIF
  set G : Ω → ℝ := fun ω => (u b (X b ω) - u b (X a ω)) + IF ω with hGdef
  set D2 : Ω → ℝ := fun ω => u b (X a ω) - u a (X a ω) with hD2def
  have hVm : StronglyMeasurable[ℱ a] V := stronglyMeasurable_condExp
  have hV : MemLp V 2 P := (memLp_integral_interval hab (hZm k) hZc).condExp one_le_two
  have hIF2 : MemLp IF 2 P := memLp_integral_interval hab hFm hFc'
  have hub : MemLp (fun ω => u b (X b ω)) 2 P := memLp_comp_of_lipschitzWith (hu b) (hX2 b hbI)
  have hua : MemLp (fun ω => u b (X a ω)) 2 P := memLp_comp_of_lipschitzWith (hu b) (hX2 a haI)
  have hua' : MemLp (fun ω => u a (X a ω)) 2 P :=
    memLp_comp_of_lipschitzWith (hu a) (hX2 a haI)
  have hG : MemLp G 2 P := (hub.sub hua).add hIF2
  have hD2 : MemLp D2 2 P := hua.sub hua'
  have hD2m : StronglyMeasurable[ℱ a] D2 :=
    ((hu b).continuous.comp_stronglyMeasurable (hXm a haI)).sub
      ((hu a).continuous.comp_stronglyMeasurable (hXm a haI))
  have hVeq : V =ᵐ[P] P[fun ω => (G ω + D2 ω) * Δ ω | ℱ a] := by
    refine (condExp_increment_mul_increment D ℱ hcoord hZm hZp hZs ha hab k).symm.trans ?_
    refine condExp_congr_ae ?_
    filter_upwards [heq a b ha hab.le hbT, hY a haI, hY b hbI] with ω e1 e2 e3
    simp only [hGdef, hD2def, hIF, hΔdef]
    rw [← e2, ← e3]
    have : Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs b ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs a ω = Y b ω - Y a ω + ∫ s in Set.Icc a b, F s ω := by
      rw [e1]; ring
    rw [this]
    ring
  have hdual := integral_sq_le_of_eq_condExp_mul_increment (D.W.W k) ℱ (hcoord k) ha hab
    hVm hV hD2m hD2 hG hVeq
  -- the energy of `G`
  have hFint : ∫ ω, ∫ s in Set.Icc a b, F s ω ^ 2 ∂volume ∂P ≤ KF := by
    obtain ⟨-, h⟩ := lintegral_interval_sq_sub_eq_ofReal hab hFm hFc' (memLp_const (0 : ℝ))
    simp only [sub_zero, zero_mul, integral_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero] at h
    rw [h] at hFc
    rwa [← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff KF.coe_nonneg] at hFc
  have hΔX : MemLp (fun ω => ‖X b ω - X a ω‖) 2 P := ((hX2 b hbI).sub (hX2 a haI)).norm
  have hGle : ∫ ω, G ω ^ 2 ∂P
      ≤ ∫ ω, (2 * (L : ℝ) ^ 2 * ‖X b ω - X a ω‖ ^ 2
          + 2 * (b - a) * ∫ s in Set.Icc a b, F s ω ^ 2) ∂P := by
    refine integral_mono_ae hG.integrable_sq
      ((hΔX.integrable_sq.const_mul _).add
        ((integrable_integral_interval_sq hFm hFc').const_mul _)) ?_
    filter_upwards [ae_memLp_interval hFm hFc'] with ω hω
    have hcs := sq_integral_interval_le hab hω
    have hlip : (u b (X b ω) - u b (X a ω)) ^ 2 ≤ (L : ℝ) ^ 2 * ‖X b ω - X a ω‖ ^ 2 := by
      have h := (hu b).norm_sub_le (X b ω) (X a ω)
      rw [Real.norm_eq_abs] at h
      rw [← sq_abs, ← mul_pow]
      exact pow_le_pow_left₀ (abs_nonneg _) h 2
    simp only [hGdef, hIF]
    nlinarith [sq_nonneg ((u b (X b ω) - u b (X a ω)) - ∫ s in Set.Icc a b, F s ω)]
  rw [integral_add (hΔX.integrable_sq.const_mul _)
      ((integrable_integral_interval_sq hFm hFc').const_mul _), integral_const_mul,
    integral_const_mul] at hGle
  have hX := hXinc a b ha hab.le hbT
  have hV2 : ∫ ω, V ω ^ 2 ∂P ≤ (b - a) ^ 2 * (2 * (L : ℝ) ^ 2 * K + 2 * KF) := by
    have h1 : 2 * (L : ℝ) ^ 2 * ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂P ≤ 2 * (L : ℝ) ^ 2 * (K * (b - a)) :=
      by gcongr
    have h2 : 2 * (b - a) * ∫ ω, ∫ s in Set.Icc a b, F s ω ^ 2 ∂volume ∂P
        ≤ 2 * (b - a) * KF := by gcongr
    calc ∫ ω, V ω ^ 2 ∂P ≤ (b - a) * ∫ ω, G ω ^ 2 ∂P := hdual
      _ ≤ (b - a) * (2 * (L : ℝ) ^ 2 * (K * (b - a)) + 2 * (b - a) * KF) := by gcongr; linarith
      _ = _ := by ring
  have hpt : (fun ω => ((b - a)⁻¹ * V ω) ^ 2) = fun ω => ((b - a) ^ 2)⁻¹ * V ω ^ 2 := by
    funext ω; rw [mul_pow, inv_pow]
  rw [hpt, integral_const_mul]
  calc ((b - a) ^ 2)⁻¹ * ∫ ω, V ω ^ 2 ∂P
      ≤ ((b - a) ^ 2)⁻¹ * ((b - a) ^ 2 * (2 * (L : ℝ) ^ 2 * K + 2 * KF)) := by gcongr
    _ = _ := by field_simp

include hcoord in
/-- **Moment bound on the conditional cell averages.** Under a Lipschitz decoupling field
`Y_t = u(t, X_t)` with `E ‖X_b − X_a‖² ≤ K (b − a)` and a driver process of energy at most
`K_F` on `[0, T]`, the conditional cell average of `Z` on every cell of every uniform grid of
`[0, T]` satisfies `E ‖Z̄_i‖² ≤ d (2 L² K + 2 K_F)`. -/
theorem lintegral_condCellAvg_sq_le_of_lipschitz (hT : 0 < T)
    (heq : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → Y a =ᵐ[P] fun ω => Y b ω
      + (∫ s in Set.Icc a b, F s ω)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs b ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs a ω))
    (hFm : Measurable (Function.uncurry fun ω s => F s ω))
    (hF : ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖F s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ KF)
    (hXm : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (X t))
    (hX2 : ∀ t ∈ Set.Icc 0 T, MemLp (X t) 2 P)
    (hXinc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂P ≤ K * (b - a))
    (hu : ∀ t, LipschitzWith L (u t))
    (hY : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => u t (X t ω))
    {N : ℕ} (hN : 0 < N) {i : ℕ} (hi : i < N) :
    ∫⁻ ω, ∑ k, (‖condCellAvg ℱ P (T / N) Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ENNReal.ofReal (d * (2 * (L : ℝ) ^ 2 * K + 2 * KF)) := by
  set τ : ℝ := T / N with hτdef
  have hτ : 0 < τ := div_pos hT (by exact_mod_cast hN)
  have hsub := cell_subset_Icc hT.le hi
  have hab : (i : ℝ) * τ < ((i : ℝ) + 1) * τ := by nlinarith
  have ha : 0 ≤ (i : ℝ) * τ := (hsub ⟨le_rfl, hab.le⟩).1
  have hbT : ((i : ℝ) + 1) * τ ≤ T := (hsub ⟨hab.le, le_rfl⟩).2
  have hlen : ((i : ℝ) + 1) * τ - (i : ℝ) * τ = τ := by ring
  have hZc : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc ((i : ℝ) * τ) (((i : ℝ) + 1) * τ),
      (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := fun k =>
    lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono_set hsub) (hZs k T hT)
  have hcm : ∀ k ∈ Finset.univ, Measurable fun ω =>
      (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 := fun k _ =>
    (((stronglyMeasurable_condCellAvg ℱ i k).mono
      (ℱ.le _)).measurable).nnnorm.coe_nnreal_ennreal.pow_const 2
  rw [lintegral_finsetSum _ hcm]
  calc ∑ k, ∫⁻ ω, (‖condCellAvg ℱ P τ Z i ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
      ≤ ∑ _k : Fin d, ENNReal.ofReal (2 * (L : ℝ) ^ 2 * K + 2 * KF) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [lintegral_nnnorm_sq_eq_ofReal (memLp_condCellAvg ℱ hτ hZm hZc k)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := integral_condIntervalAvg_sq_le_of_lipschitz D ℱ hcoord hZm hZp hZs heq hFm hF
          hXm hX2 hXinc hu hY ha hab hbT k
        rw [hlen] at h
        exact h
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Nat.cast_nonneg d), ENNReal.ofReal_natCast]

include hcoord in
/-- **The second moment of the control process from a Lipschitz decoupling field.** Let `ℱ` be
a filtration that is Brownian for every coordinate of the Brownian motion of a Lévy driver, and
`(Y, Z)` solve `Y_a = Y_b + ∫_a^b F − (∫_0^b Z dW − ∫_0^a Z dW)` on `[0, T]` with a jointly
measurable driver process `F` of energy at most `K_F`. If `Y_t = u(t, X_t)` almost surely for a
deterministic field `u` that is `L`-Lipschitz in the state for every time, and `X` is adapted,
square-integrable and satisfies `E ‖X_b − X_a‖² ≤ K (b − a)`, then
`E ‖Z_t‖² ≤ d (2 L² K + 2 K_F)` for almost every `t ∈ [0, T]`. -/
theorem ae_lintegral_sq_le_of_lipschitz (hT : 0 < T)
    (heq : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → Y a =ᵐ[P] fun ω => Y b ω
      + (∫ s in Set.Icc a b, F s ω)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs b ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord Z
          hZm hZp hZs a ω))
    (hFm : Measurable (Function.uncurry fun ω s => F s ω))
    (hF : ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖F s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ KF)
    (hXm : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (X t))
    (hX2 : ∀ t ∈ Set.Icc 0 T, MemLp (X t) 2 P)
    (hXinc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂P ≤ K * (b - a))
    (hu : ∀ t, LipschitzWith L (u t))
    (hY : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => u t (X t ω)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal (d * (2 * (L : ℝ) ^ 2 * K + 2 * KF)) :=
  ae_lintegral_sq_le_of_condCellAvg_le ℱ hT hZm hZp (fun k => hZs k T hT)
    fun _ hN _ hi => lintegral_condCellAvg_sq_le_of_lipschitz D ℱ hcoord hZm hZp hZs hT heq hFm
      hF hXm hX2 hXinc hu hY hN hi

end MomentBound

end LevyStochCalc.BSDEJ.PathRegularity
