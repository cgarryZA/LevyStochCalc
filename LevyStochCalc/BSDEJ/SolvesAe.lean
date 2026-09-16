/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.UniquenessIndistinguishable
import LevyStochCalc.Brownian.MultidimItoCongr
import LevyStochCalc.Poisson.CompensatedCongr
import LevyStochCalc.Poisson.CompensatedNonpos
import LevyStochCalc.Ito.CompensatedLocalityWindow
import LevyStochCalc.Driver.AugJointUsualConditions

/-!
# Solutions of a BSDEJ up to a null set of sample points

`SolvesBSDEJAe D f ξ T Y Z U` is the solution predicate `SolvesBSDEJ D f ξ T Y Z U` with its
three everywhere-quantified path conditions — right-continuity with left limits of `Y`, and the
vanishing of `Z` and of `U` off the horizon — asked only for almost every sample point.

The two predicates describe the same solutions: setting the three processes to `0` on a
measurable null superset of the exceptional set produces a `SolvesBSDEJ` triple whose paths agree
with the given ones off that null set (`SolvesBSDEJAe.exists_modification`), so the value
processes of two almost-everywhere solutions of the same equation remain indistinguishable on the
horizon.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

omit [IsProbabilityMeasure P] in
/-- An integrand vanishing off a horizon at almost every sample point, and having finite energy
on that horizon in each coordinate, is square integrable on every horizon. -/
theorem sq_int_global_of_vanishing_ae {Z : ℝ → Ω → (Fin d → ℝ)} {T : ℝ}
    (hvan : ∀ᵐ ω ∂P, ∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
    (hsq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤) :
    ∀ i : Fin d, ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', (‖Z s ω i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  classical
  intro i T' _
  obtain ⟨g, hgz, hgeq⟩ : ∃ g : Ω → ℝ → ℝ, (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → g ω s = 0)
      ∧ ∀ᵐ ω ∂P, ∀ s : ℝ, g ω s = Z s ω i := by
    refine ⟨fun ω s => if (∀ s' : ℝ, s' ∉ Set.Icc (0 : ℝ) T → Z s' ω = 0) then Z s ω i else 0,
      ?_, ?_⟩
    · intro ω s hs
      dsimp only
      by_cases hc : ∀ s' : ℝ, s' ∉ Set.Icc (0 : ℝ) T → Z s' ω = 0
      · rw [if_pos hc, hc s hs]
        rfl
      · rw [if_neg hc]
    · filter_upwards [hvan] with ω hω
      intro s
      rw [if_pos hω]
  have hE : ∀ T'' : ℝ, LevyStochCalc.Brownian.Ito.energy P T'' g
      = LevyStochCalc.Brownian.Ito.energy P T'' fun ω s => Z s ω i := by
    intro T''
    refine lintegral_congr_ae ?_
    filter_upwards [hgeq] with ω hω
    exact lintegral_congr fun s => by rw [hω s]
  have hle := LevyStochCalc.Brownian.Ito.energy_le_of_vanishing (P := P) hgz T'
  rw [hE T', hE T] at hle
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr (hsq i))

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- A marked integrand vanishing off a horizon at almost every sample point, and having finite
marked energy on that horizon, is square integrable on every horizon. -/
theorem marked_sq_int_global_of_vanishing_ae {U : ℝ → Ω → E → ℝ} {T : ℝ}
    (hvan : ∀ᵐ ω ∂P, ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0)
    (hsq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤) :
    ∀ T' : ℝ, 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖(fun ω' s e => U s ω' e) ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
  classical
  intro T' _
  obtain ⟨g, hgz, hgeq⟩ : ∃ g : Ω → ℝ → E → ℝ,
      (∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → g ω s e = 0)
      ∧ ∀ᵐ ω ∂P, ∀ (s : ℝ) (e : E), g ω s e = U s ω e := by
    refine ⟨fun ω s e =>
      if (∀ (s' : ℝ) (e' : E), s' ∉ Set.Icc (0 : ℝ) T → U s' ω e' = 0) then U s ω e else 0,
      ?_, ?_⟩
    · intro ω s e hs
      dsimp only
      by_cases hc : ∀ (s' : ℝ) (e' : E), s' ∉ Set.Icc (0 : ℝ) T → U s' ω e' = 0
      · rw [if_pos hc, hc s e hs]
      · rw [if_neg hc]
    · filter_upwards [hvan] with ω hω
      intro s e
      rw [if_pos hω]
  have hE : ∀ T'' : ℝ, LevyStochCalc.Poisson.Compensated.markedEnergy P ν T'' g
      = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T'' fun ω s e => U s ω e := by
    intro T''
    refine lintegral_congr_ae ?_
    filter_upwards [hgeq] with ω hω
    exact lintegral_congr fun s => lintegral_congr fun e => by rw [hω s e]
  have hle := LevyStochCalc.Poisson.Compensated.markedEnergy_le_of_vanishing
    (P := P) (ν := ν) hgz T'
  rw [hE T', hE T] at hle
  exact lt_of_le_of_lt hle (lt_top_iff_ne_top.mpr hsq)

/-- `(Y, Z, U)` solves the BSDEJ with generator `f`, terminal value `ξ` and horizon `T`, driven
by `D` over the augmented joint filtration `augJoint D`, with the path conditions on `Y`, `Z` and
`U` holding for almost every sample point:

`Y_t = ξ + ∫_t^T f(s, Y_s, Z_s, U_s) ds − ∫_t^T Z_s dW_s − ∫_t^T ∫_E U_s(e) Ñ(ds, de)`

almost surely at each `t ∈ [0, T]`, with the two stochastic integrals the canonical ones for
`augJoint D`, `Y` almost surely càdlàg, adapted to `(augJoint D).rightCont` and of finite `S²`
seminorm on the horizon, and `Z`, `U` progressive with finite energy on `[0, T]` and almost surely
vanishing off it. -/
structure SolvesBSDEJAe (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) (ξ : Ω → ℝ) (T : ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable for the augmented joint filtration. -/
  Z_prog : ∀ i : Fin d,
    LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon at almost every sample point. -/
  Z_vanish : ∀ᵐ ω ∂P, ∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable for the augmented joint filtration. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun ω s e => U s ω e
  /-- `U` vanishes off the horizon at almost every sample point. -/
  U_vanish : ∀ᵐ ω ∂P, ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
  /-- `Y` is jointly measurable. -/
  Y_meas : Measurable (Function.uncurry Y)
  /-- `Y` is adapted to the right-continuous augmented joint filtration. -/
  Y_adapted : MeasureTheory.Adapted (augJoint D).rightCont Y
  /-- Almost every path of `Y` is right-continuous with left limits. -/
  Y_cadlag : ∀ᵐ ω ∂P, ∀ t : ℝ,
    Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
      ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- The running supremum of `Y` on the horizon is square integrable. -/
  Y_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
  /-- The backward equation, almost surely at each time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, f s (Y s ω) (Z s ω) (U s ω))
      - (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing_ae Z_vanish Z_sq) T ω
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing_ae Z_vanish Z_sq) t ω)
      - (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing_ae U_vanish U_sq) T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing_ae U_vanish U_sq) t ω)

/-- A solution is a solution up to a null set of sample points. -/
theorem SolvesBSDEJ.toAe {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJ D f ξ T Y Z U) :
    SolvesBSDEJAe D f ξ T Y Z U where
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := Filter.Eventually.of_forall fun ω => h.Z_vanish ω
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := Filter.Eventually.of_forall fun ω => h.U_vanish ω
  U_sq := h.U_sq
  Y_meas := h.Y_meas
  Y_adapted := h.Y_adapted
  Y_cadlag := Filter.Eventually.of_forall fun ω => h.Y_cadlag ω
  Y_sup := h.Y_sup
  eqn := h.eqn

open LevyStochCalc.Brownian.Multidim LevyStochCalc.Poisson in
/-- A solution holding off a null set of sample points has a modification that is a solution in
the everywhere-quantified sense: the three processes are set to `0` on a measurable null superset
`N` of the exceptional set, which leaves them progressive because `N` belongs to every field of
the augmented joint filtration, and leaves the two stochastic integrals unchanged. The modified
processes agree with the given ones at every time, off `N`. -/
theorem SolvesBSDEJAe.exists_modification_indistinguishable
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJAe D f ξ T Y Z U) :
    ∃ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y' Z' U' ∧ (∀ᵐ ω ∂P, ∀ t : ℝ, Y' t ω = Y t ω)
        ∧ (∀ᵐ ω ∂P, ∀ s : ℝ, Z' s ω = Z s ω) ∧ ∀ᵐ ω ∂P, ∀ s : ℝ, U' s ω = U s ω := by
  classical
  have hSae : ∀ᵐ ω ∂P, (∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
          ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
      ∧ (∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
      ∧ ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0 := by
    filter_upwards [h.Y_cadlag, h.Z_vanish, h.U_vanish] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  obtain ⟨N, hsub, hNmeas, hNzero⟩ :=
    MeasureTheory.exists_measurable_superset_of_null (MeasureTheory.ae_iff.mp hSae)
  have hout : ∀ ω : Ω, ω ∉ N → (∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
          ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L))
      ∧ (∀ s : ℝ, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0)
      ∧ ∀ (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0 := by
    intro ω hω
    by_contra hc
    exact hω (hsub hc)
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hNzero] with ω hω
    exact Set.notMem_of_mem_compl hω
  have hN0 : MeasurableSet[augJoint D 0] N := D.measurableSet_augFiltration_of_null hNmeas hNzero
  have hNt : ∀ t : ℝ, MeasurableSet[augJoint D t] N := by
    intro t
    rcases le_or_gt 0 t with ht | ht
    · exact (augJoint D).mono ht _ hN0
    · exact D.augFiltration_le_of_nonpos ht.le _ hN0
  obtain ⟨Y', hY'def⟩ : ∃ Y' : ℝ → Ω → ℝ,
      ∀ (t : ℝ) (ω : Ω), Y' t ω = if ω ∈ N then (0 : ℝ) else Y t ω :=
    ⟨fun t ω => if ω ∈ N then (0 : ℝ) else Y t ω, fun _ _ => rfl⟩
  obtain ⟨Z', hZ'def⟩ : ∃ Z' : ℝ → Ω → (Fin d → ℝ),
      ∀ (s : ℝ) (ω : Ω), Z' s ω = if ω ∈ N then (0 : Fin d → ℝ) else Z s ω :=
    ⟨fun s ω => if ω ∈ N then (0 : Fin d → ℝ) else Z s ω, fun _ _ => rfl⟩
  obtain ⟨U', hU'def⟩ : ∃ U' : ℝ → Ω → E → ℝ,
      ∀ (s : ℝ) (ω : Ω), U' s ω = if ω ∈ N then (0 : E → ℝ) else U s ω :=
    ⟨fun s ω => if ω ∈ N then (0 : E → ℝ) else U s ω, fun _ _ => rfl⟩
  have hY'out : ∀ (t : ℝ) (ω : Ω), ω ∉ N → Y' t ω = Y t ω := by
    intro t ω hω
    rw [hY'def t ω, if_neg hω]
  have hZ'out : ∀ (s : ℝ) (ω : Ω), ω ∉ N → Z' s ω = Z s ω := by
    intro s ω hω
    rw [hZ'def s ω, if_neg hω]
  have hU'out : ∀ (s : ℝ) (ω : Ω), ω ∉ N → U' s ω = U s ω := by
    intro s ω hω
    rw [hU'def s ω, if_neg hω]
  have hZ'coord : ∀ (s : ℝ) (ω : Ω) (i : Fin d),
      Z' s ω i = if ω ∈ N then (0 : ℝ) else Z s ω i := by
    intro s ω i
    by_cases hω : ω ∈ N
    · rw [hZ'def s ω, if_pos hω, if_pos hω]
      rfl
    · rw [hZ'def s ω, if_neg hω, if_neg hω]
  have hU'mark : ∀ (s : ℝ) (ω : Ω) (e : E),
      U' s ω e = if ω ∈ N then (0 : ℝ) else U s ω e := by
    intro s ω e
    by_cases hω : ω ∈ N
    · rw [hU'def s ω, if_pos hω, if_pos hω]
      rfl
    · rw [hU'def s ω, if_neg hω, if_neg hω]
  have hZ'meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z' s ω i) := by
    intro i
    have he : (Function.uncurry fun ω s => Z' s ω i)
        = fun p : Ω × ℝ => if p.1 ∈ N then (0 : ℝ) else Z p.2 p.1 i :=
      funext fun p => hZ'coord p.2 p.1 i
    rw [he]
    exact Measurable.ite (measurable_fst hNmeas) measurable_const (h.Z_meas i)
  have hZ'prog : ∀ i : Fin d,
      LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z' s ω i := by
    intro i t
    have hNti := hNt t
    have hbase := h.Z_prog i t
    letI : MeasurableSpace Ω := augJoint D t
    have he : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => Z' s p.1 i) p.2)
        = fun p : Ω × ℝ => if p.1 ∈ N then (0 : ℝ)
            else (Set.Iic t).indicator (fun s => Z s p.1 i) p.2 := by
      funext p
      by_cases hp : p.1 ∈ N
      · rw [if_pos hp]
        by_cases hq : p.2 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, hZ'coord, if_pos hp]
        · rw [Set.indicator_of_notMem hq]
      · rw [if_neg hp]
        by_cases hq : p.2 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, hZ'coord, if_neg hp]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
    rw [he]
    exact StronglyMeasurable.ite (measurable_fst hNti) stronglyMeasurable_const hbase
  have hZ'van : ∀ (ω : Ω) (s : ℝ), s ∉ Set.Icc (0 : ℝ) T → Z' s ω = 0 := by
    intro ω s hs
    by_cases hω : ω ∈ N
    · rw [hZ'def s ω, if_pos hω]
    · rw [hZ'def s ω, if_neg hω]
      exact (hout ω hω).2.1 s hs
  have hZ'sq : ∀ i : Fin d,
      LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z' s ω i) ≠ ⊤ := by
    intro i
    have he : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z' s ω i)
        = LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with ω hω
      exact lintegral_congr fun s => by rw [hZ'coord s ω i, if_neg hω]
    rw [he]
    exact h.Z_sq i
  have hU'meas : Measurable fun p : Ω × ℝ × E => U' p.2.1 p.1 p.2.2 := by
    have he : (fun p : Ω × ℝ × E => U' p.2.1 p.1 p.2.2)
        = fun p : Ω × ℝ × E => if p.1 ∈ N then (0 : ℝ) else U p.2.1 p.1 p.2.2 :=
      funext fun p => hU'mark p.2.1 p.1 p.2.2
    rw [he]
    exact Measurable.ite (measurable_fst hNmeas) measurable_const h.U_meas
  have hU'prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D)
      fun ω s e => U' s ω e := by
    intro t
    have hNti := hNt t
    have hbase := h.U_prog t
    letI : MeasurableSpace Ω := augJoint D t
    have he : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => U' s p.1 p.2.2) p.2.1)
        = fun p : Ω × ℝ × E => if p.1 ∈ N then (0 : ℝ)
            else (Set.Iic t).indicator (fun s => U s p.1 p.2.2) p.2.1 := by
      funext p
      by_cases hp : p.1 ∈ N
      · rw [if_pos hp]
        by_cases hq : p.2.1 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, hU'mark, if_pos hp]
        · rw [Set.indicator_of_notMem hq]
      · rw [if_neg hp]
        by_cases hq : p.2.1 ∈ Set.Iic t
        · rw [Set.indicator_of_mem hq, Set.indicator_of_mem hq, hU'mark, if_neg hp]
        · rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hq]
    rw [he]
    exact StronglyMeasurable.ite (measurable_fst hNti) stronglyMeasurable_const hbase
  have hU'van : ∀ (ω : Ω) (s : ℝ) (e : E), s ∉ Set.Icc (0 : ℝ) T → U' s ω e = 0 := by
    intro ω s e hs
    rw [hU'mark s ω e]
    by_cases hω : ω ∈ N
    · rw [if_pos hω]
    · rw [if_neg hω]
      exact (hout ω hω).2.2 s e hs
  have hU'sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T
      (fun ω s e => U' s ω e) ≠ ⊤ := by
    have he : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U' s ω e)
        = LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) := by
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with ω hω
      exact lintegral_congr fun s => lintegral_congr fun e => by
        rw [hU'mark s ω e, if_neg hω]
    rw [he]
    exact h.U_sq
  have hY'meas : Measurable (Function.uncurry Y') := by
    have he : Function.uncurry Y' = fun p : ℝ × Ω => if p.2 ∈ N then (0 : ℝ) else Y p.1 p.2 :=
      funext fun p => hY'def p.1 p.2
    rw [he]
    exact Measurable.ite (measurable_snd hNmeas) measurable_const h.Y_meas
  have hY'adapted : MeasureTheory.Adapted (augJoint D).rightCont Y' := by
    intro t
    have hNrc : MeasurableSet[(augJoint D).rightCont t] N :=
      D.rightCont_augFiltration_zero_le_rightCont t _
        (D.measurableSet_rightCont_augFiltration_of_null N hNmeas hNzero)
    have hbase := h.Y_adapted t
    letI : MeasurableSpace Ω := (augJoint D).rightCont t
    have he : Y' t = fun ω => if ω ∈ N then (0 : ℝ) else Y t ω := funext fun ω => hY'def t ω
    rw [he]
    exact Measurable.ite hNrc measurable_const hbase
  have hY'cadlag : ∀ (ω : Ω) (t : ℝ),
      Filter.Tendsto (fun s => Y' s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y' t ω))
        ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y' s ω) (nhdsWithin t (Set.Iio t)) (nhds L) := by
    intro ω t
    by_cases hω : ω ∈ N
    · have hfun : (fun s => Y' s ω) = fun _ : ℝ => (0 : ℝ) :=
        funext fun s => by rw [hY'def s ω, if_pos hω]
      have hval : Y' t ω = 0 := by rw [hY'def t ω, if_pos hω]
      rw [hfun, hval]
      exact ⟨tendsto_const_nhds, 0, tendsto_const_nhds⟩
    · have hfun : (fun s => Y' s ω) = fun s => Y s ω := funext fun s => hY'out s ω hω
      rw [hfun, hY'out t ω hω]
      exact (hout ω hω).1 t
  have hY'sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y' t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
    have he : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y' t ω‖₊ : ℝ≥0∞) ^ 2) ∂P
        = ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P := by
      refine lintegral_congr_ae ?_
      filter_upwards [hNae] with ω hω
      exact iSup_congr fun t => iSup_congr fun _ => by rw [hY'out t ω hω]
    rw [he]
    exact h.Y_sup
  have hWeq : ∀ r : ℝ, ∀ᵐ ω ∂P,
      MultidimBrownianMotion.stochasticIntegral D.W (augJoint D) D.isBrownianFiltration_aug
          Z' hZ'meas hZ'prog (sq_int_global_of_vanishing hZ'van hZ'sq) r ω
        = MultidimBrownianMotion.stochasticIntegral D.W (augJoint D) D.isBrownianFiltration_aug
          Z h.Z_meas h.Z_prog (sq_int_global_of_vanishing_ae h.Z_vanish h.Z_sq) r ω := by
    intro r
    rcases le_or_gt r 0 with hr | hr
    · have a1 := MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W (augJoint D)
        D.isBrownianFiltration_aug Z' hZ'meas hZ'prog
        (sq_int_global_of_vanishing hZ'van hZ'sq) hr
      have a2 := MultidimBrownianMotion.stochasticIntegral_ae_zero_of_nonpos D.W (augJoint D)
        D.isBrownianFiltration_aug Z h.Z_meas h.Z_prog
        (sq_int_global_of_vanishing_ae h.Z_vanish h.Z_sq) hr
      filter_upwards [a1, a2] with ω b1 b2
      rw [b1, b2]
    · refine MultidimBrownianMotion.stochasticIntegral_congr_ae D.W (augJoint D)
        D.isBrownianFiltration_aug hZ'meas hZ'prog (sq_int_global_of_vanishing hZ'van hZ'sq)
        h.Z_meas h.Z_prog (sq_int_global_of_vanishing_ae h.Z_vanish h.Z_sq) hr ?_
      filter_upwards [hNae] with ω hω
      exact Filter.Eventually.of_forall fun s => hZ'out s ω hω
  have hJeq : ∀ r : ℝ, ∀ᵐ ω ∂P,
      Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
          (fun ω' s e => U' s ω' e) hU'meas hU'prog
          (marked_sq_int_global_of_vanishing hU'van hU'sq) r ω
        = Compensated.stochasticIntegral D.N (augJoint D) D.isPoissonFiltration_aug
          (fun ω' s e => U s ω' e) h.U_meas h.U_prog
          (marked_sq_int_global_of_vanishing_ae h.U_vanish h.U_sq) r ω := by
    intro r
    rcases le_or_gt r 0 with hr | hr
    · have a1 := Compensated.stochasticIntegral_ae_zero_of_nonpos D.N
        D.isPoissonFiltration_aug (φ := fun ω' s e => U' s ω' e) hU'meas hU'prog
        (marked_sq_int_global_of_vanishing hU'van hU'sq) hr
      have a2 := Compensated.stochasticIntegral_ae_zero_of_nonpos D.N
        D.isPoissonFiltration_aug (φ := fun ω' s e => U s ω' e) h.U_meas h.U_prog
        (marked_sq_int_global_of_vanishing_ae h.U_vanish h.U_sq) hr
      filter_upwards [a1, a2] with ω b1 b2
      rw [b1, b2]
    · refine Compensated.stochasticIntegral_congr_ae D.N D.isPoissonFiltration_aug
        (fun ω' s e => U' s ω' e) (fun ω' s e => U s ω' e) hU'meas h.U_meas hU'prog h.U_prog
        (marked_sq_int_global_of_vanishing hU'van hU'sq)
        (marked_sq_int_global_of_vanishing_ae h.U_vanish h.U_sq) hr ?_
      refine LevyStochCalc.Ito.markedEnergyMeasure_ae_eq_of_ae_ae
        (φ := fun ω' s e => U' s ω' e) (ψ := fun ω' s e => U s ω' e) hU'meas h.U_meas r ?_
      filter_upwards [hNae] with ω hω
      refine Filter.Eventually.of_forall fun s e => ?_
      rw [hU'mark s ω e, if_neg hω]
  refine ⟨Y', Z', U', ?_, ?_, ?_, ?_⟩
  · refine
      { Z_meas := hZ'meas
        Z_prog := hZ'prog
        Z_vanish := hZ'van
        Z_sq := hZ'sq
        U_meas := hU'meas
        U_prog := hU'prog
        U_vanish := hU'van
        U_sq := hU'sq
        Y_meas := hY'meas
        Y_adapted := hY'adapted
        Y_cadlag := hY'cadlag
        Y_sup := hY'sup
        eqn := ?_ }
    intro t ht
    have hdrift : ∀ ω : Ω, ω ∉ N →
        (∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω))
          = ∫ s in Set.Icc t T, f s (Y s ω) (Z s ω) (U s ω) := by
      intro ω hω
      have hfun : (fun s => f s (Y' s ω) (Z' s ω) (U' s ω))
          = fun s => f s (Y s ω) (Z s ω) (U s ω) :=
        funext fun s => by rw [hY'out s ω hω, hZ'out s ω hω, hU'out s ω hω]
      rw [hfun]
    filter_upwards [h.eqn t ht, hNae, hWeq T, hWeq t, hJeq T, hJeq t] with ω hω hωN e1 e2 e3 e4
    rw [hY'out t ω hωN, hdrift ω hωN, e1, e2, e3, e4]
    exact hω
  · filter_upwards [hNae] with ω hω
    exact fun t => hY'out t ω hω
  · filter_upwards [hNae] with ω hω
    exact fun s => hZ'out s ω hω
  · filter_upwards [hNae] with ω hω
    exact fun s => hU'out s ω hω

/-- A solution holding off a null set of sample points has a modification that is a solution in
the everywhere-quantified sense, with the same value, control and jump processes at each time up
to a null set of sample points. -/
theorem SolvesBSDEJAe.exists_modification
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : SolvesBSDEJAe D f ξ T Y Z U) :
    ∃ (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ),
      SolvesBSDEJ D f ξ T Y' Z' U' ∧ (∀ t : ℝ, Y' t =ᵐ[P] Y t) ∧ (∀ t : ℝ, Z' t =ᵐ[P] Z t)
        ∧ ∀ t : ℝ, ∀ᵐ ω ∂P, U' t ω = U t ω := by
  obtain ⟨Y', Z', U', hsol, hY, hZ, hU⟩ := h.exists_modification_indistinguishable
  refine ⟨Y', Z', U', hsol, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · filter_upwards [hY] with ω hω using hω t
  · filter_upwards [hZ] with ω hω using hω t
  · filter_upwards [hU] with ω hω using hω t

/-- The value processes of two solutions of the same backward equation holding off a null set of
sample points are indistinguishable on the horizon: on a single set of full measure they agree at
every time of `[0, T]`. -/
theorem SolvesBSDEJAe.unique_Y_indistinguishable
    {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : SolvesBSDEJAe D f ξ T Y₁ Z₁ U₁) (h₂ : SolvesBSDEJAe D f ξ T Y₂ Z₂ U₂) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hL : 0 ≤ L)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, Y₁ t ω = Y₂ t ω := by
  obtain ⟨Y₁', Z₁', U₁', hs₁, hm₁, -, -⟩ := h₁.exists_modification_indistinguishable
  obtain ⟨Y₂', Z₂', U₂', hs₂, hm₂, -, -⟩ := h₂.exists_modification_indistinguishable
  filter_upwards [hs₁.unique_Y_indistinguishable hs₂ hT hf hL hlip hf0, hm₁, hm₂]
    with ω hω b1 b2
  intro t ht
  rw [← b1 t, ← b2 t]
  exact hω t ht

end LevyStochCalc.BSDEJ.Solves
