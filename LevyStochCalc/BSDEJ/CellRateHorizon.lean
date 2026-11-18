/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.CellRateGaussian
import LevyStochCalc.Brownian.MultidimItoCongr
import LevyStochCalc.Poisson.CompensatedNonpos

/-!
# The cell-projection rates under hypotheses on the horizon only

The cell-projection error of a process `Z` on the uniform grids of `[0, T]` reads `Z` only on
`[0, T]`. The truncation `Zᵀ = 1_{[0, T]} Z` (`horizonTrunc`) is admissible for the Itô integral
on every positive horizon as soon as it is jointly and progressively measurable and `Z` has
finite energy on `[0, T]`, and these three conditions involve `Z` only through its values on
`[0, T]`. The truncation has the same cell-projection error as `Z`, and when `Z` is itself
admissible on every positive horizon the two Itô integrals agree almost surely at every time of
`[0, T]`, so their increments on `[0, T]` agree too.

Applied through the truncation, the rate for a martingale plus a mean-square Lipschitz process,
the second-moment bound under a Lipschitz decoupling field, and the first-order rate for a
Gaussian terminal datum hold for a control process `Z` constrained on `[0, T]` only, the backward
equation being written with the Itô integral of `Zᵀ`; in the second-moment bound the driver
process `F` and the decoupling field `u` are likewise constrained on `[0, T]` only.

## Main statements

* `horizonTrunc` — the truncation to the horizon `[0, T]`.
* `sq_int_global_horizonTrunc_pi` — finite energy on `[0, T]` makes the truncation square
  integrable on every positive horizon.
* `measurable_horizonTrunc_pi`, `progressivelyMeasurable_horizonTrunc_pi` — the truncation of a
  jointly, resp. progressively, measurable process is jointly, resp. progressively, measurable.
* `stochasticIntegral_horizonTrunc_ae_eq` — the Itô integrals of a process and of its truncation
  agree almost surely at every time of the horizon.
* `cellProjError_horizonTrunc`, `cellRegularity_horizonTrunc_iff` — truncating does not change
  the cell-projection error or `CellRegularity`.
* `cellProjError_le_of_martingale_add_horizon`, `ae_lintegral_sq_le_of_lipschitz_horizon`,
  `cellProjError_le_of_gaussianTerminal_horizon`, `ae_lintegral_sq_le_of_gaussianTerminal_horizon`,
  `cellRegularity_of_gaussianTerminal_horizon` — the rates and bounds under hypotheses on the
  horizon only.
-/

open MeasureTheory ProbabilityTheory Filter

open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.PathRegularity

open LevyStochCalc.BSDEJ.Solves (augJoint)

universe u v w

section Truncation

variable {α β : Type*} [Zero β] {T : ℝ}

/-- The truncation of a time-indexed family to the horizon `[0, T]`: it agrees with `f` at the
times of `[0, T]` and is `0` at every other time. -/
noncomputable def horizonTrunc (T : ℝ) (f : ℝ → α → β) : ℝ → α → β := fun s x =>
  (Set.Icc (0 : ℝ) T).indicator (fun s => f s x) s

/-- On the horizon the truncation is the family itself. -/
theorem horizonTrunc_of_mem (f : ℝ → α → β) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) (x : α) :
    horizonTrunc T f s x = f s x :=
  Set.indicator_of_mem hs _

/-- Off the horizon the truncation vanishes. -/
theorem horizonTrunc_of_notMem (f : ℝ → α → β) {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) T) (x : α) :
    horizonTrunc T f s x = 0 :=
  Set.indicator_of_notMem hs _

/-- On the horizon the truncation is the family itself, as a function. -/
theorem horizonTrunc_eq_of_mem (f : ℝ → α → β) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    horizonTrunc T f s = f s :=
  funext (horizonTrunc_of_mem f hs)

/-- A coordinate of the truncation of a vector family is the truncation of the coordinate. -/
theorem horizonTrunc_apply_apply {d : ℕ} (Z : ℝ → α → (Fin d → ℝ)) (s : ℝ) (x : α)
    (k : Fin d) : horizonTrunc T Z s x k = horizonTrunc T (fun s x => Z s x k) s x := by
  by_cases hs : s ∈ Set.Icc (0 : ℝ) T
  · rw [horizonTrunc_of_mem _ hs, horizonTrunc_of_mem _ hs]
  · rw [horizonTrunc_of_notMem _ hs, horizonTrunc_of_notMem _ hs]
    rfl

/-- The truncation of a field that is `L`-Lipschitz in the state at every time of the horizon is
`L`-Lipschitz in the state at every time. -/
theorem lipschitzWith_horizonTrunc {n : ℕ} {u : ℝ → (Fin n → ℝ) → ℝ} {L : ℝ≥0}
    (hu : ∀ t ∈ Set.Icc (0 : ℝ) T, LipschitzWith L (u t)) (t : ℝ) :
    LipschitzWith L (horizonTrunc T u t) := by
  by_cases ht : t ∈ Set.Icc (0 : ℝ) T
  · rw [horizonTrunc_eq_of_mem u ht]
    exact hu t ht
  · have h0 : horizonTrunc T u t = fun _ => 0 := funext (horizonTrunc_of_notMem u ht)
    rw [h0]
    exact (LipschitzWith.const (0 : ℝ)).weaken bot_le

end Truncation

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

section Admissible

variable {T : ℝ} {d : ℕ}

omit [MeasurableSpace Ω] in
/-- The time integral over `[a, b] ⊆ [0, T]` of the truncation is that of the process. -/
theorem setIntegral_horizonTrunc {F : ℝ → Ω → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hbT : b ≤ T)
    (ω : Ω) : ∫ s in Set.Icc a b, horizonTrunc T F s ω = ∫ s in Set.Icc a b, F s ω :=
  setIntegral_congr_fun measurableSet_Icc fun _ hs =>
    horizonTrunc_of_mem F ⟨ha.trans hs.1, hs.2.trans hbT⟩ ω

/-- The energy of the truncation on the horizon is that of the process. -/
theorem lintegral_horizonTrunc_eq {f : ℝ → Ω → ℝ} :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖horizonTrunc T f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
  lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    rw [horizonTrunc_of_mem f hs]

/-- The truncation of a process of finite energy on the horizon has finite energy on every
positive horizon. -/
theorem sq_int_global_horizonTrunc {f : ℝ → Ω → ℝ}
    (hf : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖horizonTrunc T f s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T' _
  have h := Brownian.Ito.energy_le_of_vanishing (P := P)
    (H := fun ω s => horizonTrunc T f s ω) (fun ω s hs => horizonTrunc_of_notMem f hs ω) T'
  simp only [Brownian.Ito.energy] at h
  exact lt_of_le_of_lt h (by rw [lintegral_horizonTrunc_eq]; exact hf)

/-- The truncation of a vector process whose coordinates have finite energy on the horizon has
coordinates of finite energy on every positive horizon. -/
theorem sq_int_global_horizonTrunc_pi {Z : ℝ → Ω → (Fin d → ℝ)}
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ k : Fin d, ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖horizonTrunc T Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro k
  simp only [horizonTrunc_apply_apply]
  exact sq_int_global_horizonTrunc (hZs k)

/-- The coordinates of the truncation have the energy of the coordinates on the horizon. -/
theorem lintegral_horizonTrunc_pi_eq {Z : ℝ → Ω → (Fin d → ℝ)} (k : Fin d) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖horizonTrunc T Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
  simp only [horizonTrunc_apply_apply]
  exact lintegral_horizonTrunc_eq

/-- The truncation of a jointly measurable process is jointly measurable. -/
theorem measurable_horizonTrunc {f : ℝ → Ω → ℝ}
    (hf : Measurable (Function.uncurry fun ω s => f s ω)) (T : ℝ) :
    Measurable (Function.uncurry fun ω s => horizonTrunc T f s ω) := by
  have e : (Function.uncurry fun ω s => horizonTrunc T f s ω)
      = (Prod.snd ⁻¹' Set.Icc (0 : ℝ) T).indicator (Function.uncurry fun ω s => f s ω) := by
    funext p
    by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
    · rw [Set.indicator_of_mem (Set.mem_preimage.mpr hp)]
      exact horizonTrunc_of_mem f hp p.1
    · rw [Set.indicator_of_notMem fun hc => hp (Set.mem_preimage.mp hc)]
      exact horizonTrunc_of_notMem f hp p.1
  rw [e]
  exact hf.indicator (measurable_snd measurableSet_Icc)

/-- The coordinates of the truncation of a jointly measurable vector process are jointly
measurable. -/
theorem measurable_horizonTrunc_pi {Z : ℝ → Ω → (Fin d → ℝ)}
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k)) (T : ℝ) :
    ∀ k, Measurable (Function.uncurry fun ω s => horizonTrunc T Z s ω k) := by
  intro k
  simp only [horizonTrunc_apply_apply]
  exact measurable_horizonTrunc (hZm k) T

/-- The truncation of a progressively measurable process is progressively measurable. -/
theorem progressivelyMeasurable_horizonTrunc {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {f : ℝ → Ω → ℝ} (hf : Probability.ProgressivelyMeasurable ℱ fun ω s => f s ω) (T : ℝ) :
    Probability.ProgressivelyMeasurable ℱ fun ω s => horizonTrunc T f s ω :=
  Brownian.Ito.progressivelyMeasurable_indicator_Icc hf T

/-- The coordinates of the truncation of a progressively measurable vector process are
progressively measurable. -/
theorem progressivelyMeasurable_horizonTrunc_pi {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {Z : ℝ → Ω → (Fin d → ℝ)}
    (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k) (T : ℝ) :
    ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => horizonTrunc T Z s ω k := by
  intro k
  simp only [horizonTrunc_apply_apply]
  exact progressivelyMeasurable_horizonTrunc (hZp k) T

/-- **The Itô integrals of a process and of its truncation agree on the horizon.** For a vector
process admissible on every positive horizon and `t ∈ [0, T]`, `T > 0`, the multidimensional Itô
integral of `1_{[0, T]} Z` at `t` is almost surely that of `Z`. -/
theorem stochasticIntegral_horizonTrunc_ae_eq [IsProbabilityMeasure P]
    (W : Brownian.Multidim.MultidimBrownianMotion P d) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hcoord : ∀ k, Brownian.IsBrownianFiltration (W.W k) ℱ) {Z : ℝ → Ω → (Fin d → ℝ)}
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => Z s ω k))
    (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω k)
    (hZs : ∀ k, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc 0 T', (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hT : 0 < T) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hcoord (horizonTrunc T Z)
        (measurable_horizonTrunc_pi hZm T) (progressivelyMeasurable_horizonTrunc_pi hZp T)
        (sq_int_global_horizonTrunc_pi fun k => hZs k T hT) t
      =ᵐ[P] Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral W ℱ hcoord Z hZm hZp
        hZs t := by
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · have ht0 : t ≤ 0 := h0.symm.le
    exact (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos W ℱ
      hcoord _ _ _ _ ht0).trans
      (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos W ℱ hcoord
        _ _ _ _ ht0).symm
  · refine Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral_congr_ae W ℱ hcoord _ _ _
      hZm hZp hZs hpos (Eventually.of_forall fun ω => ?_)
    exact ae_restrict_of_forall_mem measurableSet_Icc fun s hs =>
      horizonTrunc_of_mem Z ⟨hs.1, hs.2.trans ht.2⟩ ω

end Admissible

section Projection

variable {d : ℕ} (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {T : ℝ}

/-- Processes agreeing at every time of `[0, T]` have the same cell-projection error on the
uniform grids of `[0, T]`. -/
theorem cellProjError_congr (hT : 0 ≤ T) {N : ℕ} {Z Z' : ℝ → Ω → (Fin d → ℝ)}
    (h : ∀ s ∈ Set.Icc (0 : ℝ) T, Z s = Z' s) :
    cellProjError ℱ P T N Z = cellProjError ℱ P T N Z' := by
  unfold cellProjError
  refine Finset.sum_congr rfl fun i hi => ?_
  have hsub := cell_subset_Icc hT (Finset.mem_range.mp hi)
  have hc : condCellAvg ℱ P (T / (N : ℝ)) Z i = condCellAvg ℱ P (T / (N : ℝ)) Z' i := by
    funext ω k
    have hf : (fun ω' => ∫ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
          Z s ω' k)
        = fun ω' => ∫ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
          Z' s ω' k :=
      funext fun ω' => setIntegral_congr_fun measurableSet_Icc fun s hs => by
        rw [h s (hsub hs)]
    simp only [condCellAvg, hf]
  rw [hc]
  exact lintegral_congr fun ω => setLIntegral_congr_fun measurableSet_Icc fun s hs => by
    rw [h s (hsub hs)]

/-- The truncation to the horizon has the cell-projection error of the process. -/
theorem cellProjError_horizonTrunc (hT : 0 ≤ T) (N : ℕ) (Z : ℝ → Ω → (Fin d → ℝ)) :
    cellProjError ℱ P T N (horizonTrunc T Z) = cellProjError ℱ P T N Z :=
  cellProjError_congr ℱ hT fun _ hs => horizonTrunc_eq_of_mem Z hs

/-- The truncation of the integrand `Z` to the horizon has the path-regularity rate exactly when
`Z` has it. -/
theorem cellRegularity_horizonTrunc_iff [IsProbabilityMeasure P] {E : Type v} [MeasurableSpace E]
    {ν : Measure E} [SigmaFinite ν] {m : ℕ} (D : Driver.LevyDriver.{u, v, w} P d ν)
    (hT : 0 ≤ T) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) (A : Fin m → Set E) (C : ℝ) :
    CellRegularity D T (horizonTrunc T Z) U A C ↔ CellRegularity D T Z U A C := by
  rw [cellRegularity_iff, cellRegularity_iff]
  simp only [cellProjError_horizonTrunc (augJoint D) hT]

end Projection

variable [IsProbabilityMeasure P]

section Martingale

variable (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) {d : ℕ} {T : ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}

/-- **The cell-projection rate of a martingale plus a mean-square Lipschitz process, on the
horizon.** The rate `(2 B + K T) T / N` of `cellProjError_le_of_martingale_add` holds for a
process `Z` whose truncation `1_{[0, T]} Z` is jointly measurable and which has finite energy on
`[0, T]`, with `Z_t = M_t + A_t` almost surely for almost every `t ∈ [0, T]`. -/
theorem cellProjError_le_of_martingale_add_horizon (hT : 0 < T)
    (hZm : ∀ k, Measurable (Function.uncurry fun ω s => horizonTrunc T Z s ω k))
    (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {M A : ℝ → Ω → (Fin d → ℝ)}
    (hMa : ∀ t ∈ Set.Icc 0 T, ∀ k, StronglyMeasurable[ℱ t] fun ω => M t ω k)
    (hM2 : ∀ t ∈ Set.Icc 0 T, ∀ k, MemLp (fun ω => M t ω k) 2 P)
    (hMart : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T → ∀ k,
      P[fun ω => M t ω k | ℱ s] =ᵐ[P] fun ω => M s ω k)
    {B : ℝ} (hB : ∫ ω, ∑ k, M T ω k ^ 2 ∂P ≤ B)
    (hAa : ∀ t ∈ Set.Icc 0 T, ∀ k, StronglyMeasurable[ℱ t] fun ω => A t ω k)
    (hA2 : ∀ t ∈ Set.Icc 0 T, ∀ k, MemLp (fun ω => A t ω k) 2 P)
    {K : ℝ} (hA : ∀ s t, 0 ≤ s → s ≤ t → t ≤ T →
      ∫ ω, ∑ k, (A t ω k - A s ω k) ^ 2 ∂P ≤ K * (t - s))
    (hZ : ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)), Z t =ᵐ[P] fun ω => M t ω + A t ω)
    {N : ℕ} (hN : 0 < N) :
    cellProjError ℱ P T N Z ≤ ENNReal.ofReal ((2 * B + K * T) * (T / N)) := by
  rw [← cellProjError_horizonTrunc ℱ hT.le]
  refine cellProjError_le_of_martingale_add ℱ hT hZm
    (fun k => by rw [lintegral_horizonTrunc_pi_eq]; exact hZs k) hMa hM2 hMart hB hAa hA2 hA
    ?_ hN
  filter_upwards [hZ, ae_restrict_mem measurableSet_Icc] with t h1 ht
  rwa [horizonTrunc_eq_of_mem Z ht]

end Martingale

section MomentBound

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d : ℕ}
  (D : Driver.LevyDriver.{u, v, w} P d ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {T : ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => horizonTrunc T Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => horizonTrunc T Z s ω k)
  (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {Y F : ℝ → Ω → ℝ} {n : ℕ} {X : ℝ → Ω → (Fin n → ℝ)} {u : ℝ → (Fin n → ℝ) → ℝ}
  {L : ℝ≥0} {K : ℝ} {KF : ℝ≥0}

/-- **The second moment of the control process from a Lipschitz decoupling field, on the
horizon.** Let `Z` have jointly and progressively measurable truncation `Zᵀ = 1_{[0, T]} Z` and
finite energy on `[0, T]`, and let `(Y, Z)` solve
`Y_a = Y_b + ∫_a^b F − (∫_0^b Zᵀ dW − ∫_0^a Zᵀ dW)` on `[0, T]` with a driver process `F` whose
truncation is jointly measurable and whose energy on `[0, T]` is at most `K_F`. If
`Y_t = u(t, X_t)` almost surely for `t ∈ [0, T]`, with `u(t, ·)` `L`-Lipschitz for every
`t ∈ [0, T]` and `X` adapted, square-integrable and with `E ‖X_b − X_a‖² ≤ K (b − a)`, then
`E ‖Z_t‖² ≤ d (2 L² K + 2 K_F)` for almost every `t ∈ [0, T]`. -/
theorem ae_lintegral_sq_le_of_lipschitz_horizon (hT : 0 < T)
    (heq : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → Y a =ᵐ[P] fun ω => Y b ω
      + (∫ s in Set.Icc a b, F s ω)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) b ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) a ω))
    (hFm : Measurable (Function.uncurry fun ω s => horizonTrunc T F s ω))
    (hF : ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖F s ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P ≤ KF)
    (hXm : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (X t))
    (hX2 : ∀ t ∈ Set.Icc 0 T, MemLp (X t) 2 P)
    (hXinc : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → ∫ ω, ‖X b ω - X a ω‖ ^ 2 ∂P ≤ K * (b - a))
    (hu : ∀ t ∈ Set.Icc 0 T, LipschitzWith L (u t))
    (hY : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => u t (X t ω)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P
        ≤ ENNReal.ofReal (d * (2 * (L : ℝ) ^ 2 * K + 2 * KF)) := by
  have heq' : ∀ a b, 0 ≤ a → a ≤ b → b ≤ T → Y a =ᵐ[P] fun ω => Y b ω
      + (∫ s in Set.Icc a b, horizonTrunc T F s ω)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) b ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) a ω) := by
    intro a b ha hab hbT
    filter_upwards [heq a b ha hab hbT] with ω hω
    rw [hω, setIntegral_horizonTrunc ha hbT]
  have hY' : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => horizonTrunc T u t (X t ω) := by
    intro t ht
    filter_upwards [hY t ht] with ω hω
    rw [hω, horizonTrunc_of_mem u ht]
  have h := ae_lintegral_sq_le_of_lipschitz D ℱ hcoord hZm hZp
    (sq_int_global_horizonTrunc_pi hZs) hT heq' hFm (by rwa [lintegral_horizonTrunc_eq]) hXm
    hX2 hXinc (lipschitzWith_horizonTrunc hu) hY'
  filter_upwards [h, ae_restrict_mem measurableSet_Icc] with t h1 ht
  rwa [horizonTrunc_eq_of_mem Z ht] at h1

end MomentBound

section Gaussian

variable {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν]
  (D : Driver.LevyDriver.{u, v, w} P 1 ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k, Brownian.IsBrownianFiltration (D.W.W k) ℱ) {T : ℝ} {Z : ℝ → Ω → (Fin 1 → ℝ)}
  (hZm : ∀ k, Measurable (Function.uncurry fun ω s => horizonTrunc T Z s ω k))
  (hZp : ∀ k, Probability.ProgressivelyMeasurable ℱ fun ω s => horizonTrunc T Z s ω k)
  (hZs : ∀ k, ∫⁻ ω, ∫⁻ s in Set.Icc 0 T, (‖Z s ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  {n : ℕ} {ξ₀ : Ω → (Fin n → ℝ)} {σ : Fin n → ℝ} {g : (Fin n → ℝ) → ℝ}
  {L : ℝ≥0} {h : ℝ → ℝ} {Y : ℝ → Ω → ℝ}

/-- **The first-order cell-projection rate for a Gaussian terminal datum, on the horizon.** Let
`Z` have jointly and progressively measurable truncation `Zᵀ = 1_{[0, T]} Z` and finite energy
on `[0, T]`, and let `Y_t = g(ξ₀ + W_T σ) + ∫_t^T h − (∫_0^T Zᵀ dW − ∫_0^t Zᵀ dW)` for
`t ∈ [0, T]`, with `g` `L`-Lipschitz, `ξ₀` square-integrable and measurable at `0` and `Y`
adapted. For every `N ≥ 1` the cell-projection error of `Z` on the uniform grid of `N` cells of
`[0, T]` is at most `L² ‖σ‖² T / N`. -/
theorem cellProjError_le_of_gaussianTerminal_horizon (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) t ω))
    {N : ℕ} (hN : 0 < N) :
    cellProjError ℱ P T N Z ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ‖σ‖ ^ 2 * (T / N)) := by
  rw [← cellProjError_horizonTrunc ℱ hT.le]
  exact cellProjError_le_of_gaussianTerminal D ℱ hcoord hZm hZp
    (sq_int_global_horizonTrunc_pi hZs) hT hξm hξ hg hYa heq hN

/-- **The second moment of the control process for a Gaussian terminal datum, on the horizon.**
Under the hypotheses of `cellProjError_le_of_gaussianTerminal_horizon`, `E |Z_t|² ≤ L² ‖σ‖²` for
almost every `t ∈ [0, T]`. -/
theorem ae_lintegral_sq_le_of_gaussianTerminal_horizon (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) t ω)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc 0 T)),
      ∫⁻ ω, ∑ k, (‖Z t ω k‖₊ : ℝ≥0∞) ^ 2 ∂P ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ‖σ‖ ^ 2) := by
  have h1 := ae_lintegral_sq_le_of_gaussianTerminal D ℱ hcoord hZm hZp
    (sq_int_global_horizonTrunc_pi hZs) hT hξm hξ hg hYa heq
  filter_upwards [h1, ae_restrict_mem measurableSet_Icc] with t h2 ht
  rwa [horizonTrunc_eq_of_mem Z ht] at h2

/-- **`CellRegularity` for a Gaussian terminal datum, on the horizon.** Over the augmented joint
filtration of a Lévy driver with one Brownian coordinate, under the hypotheses of
`cellProjError_le_of_gaussianTerminal_horizon`, the pair `(Z, U)` has the `L²` path-regularity
rate with constant `L² ‖σ‖²`, given that rate for the marked integrals. -/
theorem cellRegularity_of_gaussianTerminal_horizon (hℱ : ℱ = augJoint D) (hT : 0 < T)
    (hξm : StronglyMeasurable[ℱ 0] ξ₀) (hξ : MemLp ξ₀ 2 P) (hg : LipschitzWith L g)
    (hYa : ∀ t ∈ Set.Icc 0 T, StronglyMeasurable[ℱ t] (Y t))
    (heq : ∀ t ∈ Set.Icc 0 T, Y t =ᵐ[P] fun ω => g (ξ₀ ω + (D.W.W 0).W T ω • σ)
      + (∫ s in Set.Icc t T, h s)
      - (Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) T ω
        - Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W ℱ hcoord
          (horizonTrunc T Z) hZm hZp (sq_int_global_horizonTrunc_pi hZs) t ω))
    {m : ℕ} {U : ℝ → Ω → E → ℝ} {A : Fin m → Set E}
    (hU : ∀ N : ℕ, 0 < N →
      ∑ i ∈ Finset.range N, ∫⁻ ω,
        ∫⁻ s in Set.Icc ((i : ℝ) * (T / (N : ℝ))) (((i : ℝ) + 1) * (T / (N : ℝ))),
          ∑ k : Fin m,
            (‖(∫ e in A k, U s ω e ∂ν)
              - condCellAverage_U D (T / (N : ℝ)) U A i ω k‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
        ≤ ENNReal.ofReal ((L : ℝ) ^ 2 * ‖σ‖ ^ 2 * (T / (N : ℝ)))) :
    CellRegularity D T Z U A ((L : ℝ) ^ 2 * ‖σ‖ ^ 2) :=
  (cellRegularity_horizonTrunc_iff D hT.le Z U A _).mp
    (cellRegularity_of_gaussianTerminal D ℱ hcoord hZm hZp (sq_int_global_horizonTrunc_pi hZs)
      hℱ hT hξm hξ hg hYa heq hU)

end Gaussian

end LevyStochCalc.BSDEJ.PathRegularity
