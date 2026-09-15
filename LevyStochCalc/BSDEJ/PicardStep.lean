/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardTerminal
import LevyStochCalc.BSDEJ.CadlagLegs
import LevyStochCalc.BSDEJ.DriftLeg
import LevyStochCalc.BSDEJ.SupBound
import LevyStochCalc.Probability.DoobContinuous

/-!
# One Picard step of a backward equation with jumps

The Picard map of a backward equation with jumps sends a triple `(Y', Z', U')` to the triple
solving the equation whose generator is frozen along the input, that is to the martingale
representation of the terminal datum `ξ + ∫_0^T b_s ds` for `b = f(·, Y', Z', U')`.
`PicardOutput` is the predicate satisfied by the output triple: the fields of `SolvesBSDEJ` with
the drift integral taken along the input triple, together with the terminal value of `Y` and its
finite `S²` seminorm. A fixed point of the map, that is a `PicardOutput` whose input and output
triples agree, solves the backward equation.

The output is built from the martingale representation of the centred terminal datum
(`exists_picard_integrands_of_rightCont`), the everywhere-càdlàg versions of the two stochastic
legs (`exists_cadlag_brownianLeg`, `exists_cadlag_poissonLeg`) and the primitive of the drift
(`driftLeg`), as `Y_t = c + M^W_t + M^N_t − ∫_0^t b_s ds` with `c` the mean of the terminal
datum.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.PicardOutput` — the output triple of one Picard step.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.PicardOutput.toSolvesBSDEJ` — a fixed point of the Picard step
  solves the backward equation.
* `LevyStochCalc.BSDEJ.Solves.measurable_biSup_sq_of_rightContinuous` — the squared running
  supremum of a right-continuous process with measurable slices is measurable.
* `LevyStochCalc.BSDEJ.Solves.exists_picardOutput` — the Picard step has an output triple.

## References

* Tang–Li, *Necessary conditions for optimal control of stochastic systems with random jumps*,
  SIAM J. Control Optim. 32 (1994), §2.
* Barles–Buckdahn–Pardoux, *BSDEs and integral-partial differential equations*, Stochastics 60
  (1997), §2.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.BSDEJ.Solves

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### The output of a Picard step -/

/-- `(Y, Z, U)` is the output of the Picard step from the input triple `(Y', Z', U')` for the
backward equation with generator `f`, terminal value `ξ` and horizon `T` driven by `D`: it
satisfies the fields of `SolvesBSDEJ` with the drift integral of the equation taken along
`(Y', Z', U')`, ends at `ξ` and has finite `S²` seminorm on `[0, T]`. -/
structure PicardOutput (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) (ξ : Ω → ℝ) (T : ℝ)
    (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- Each coordinate of `Z` is jointly measurable. -/
  Z_meas : ∀ i : Fin d, Measurable (Function.uncurry fun ω s => Z s ω i)
  /-- Each coordinate of `Z` is progressively measurable for the augmented joint filtration. -/
  Z_prog : ∀ i : Fin d,
    LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D) fun ω s => Z s ω i
  /-- `Z` vanishes off the horizon. -/
  Z_vanish : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → Z s ω = 0
  /-- Each coordinate of `Z` has finite energy on the horizon. -/
  Z_sq : ∀ i : Fin d, LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤
  /-- `U` is jointly measurable in the sample point, the time and the mark. -/
  U_meas : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2
  /-- `U` is marked progressively measurable for the augmented joint filtration. -/
  U_prog : LevyStochCalc.Probability.MarkedProgressivelyMeasurable (augJoint D)
    fun ω s e => U s ω e
  /-- `U` vanishes off the horizon. -/
  U_vanish : ∀ ω s e, s ∉ Set.Icc (0 : ℝ) T → U s ω e = 0
  /-- `U` has finite marked energy on the horizon. -/
  U_sq : LevyStochCalc.Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≠ ⊤
  /-- `Y` is jointly measurable. -/
  Y_meas : Measurable (Function.uncurry Y)
  /-- `Y` is adapted to the right-continuous augmented joint filtration. -/
  Y_adapted : MeasureTheory.Adapted (augJoint D).rightCont Y
  /-- Every path of `Y` is right-continuous with left limits. -/
  Y_cadlag : ∀ ω : Ω, ∀ t : ℝ,
    Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω))
      ∧ ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- The backward equation with the drift frozen along the input triple, almost surely at each
  time of the horizon. -/
  eqn : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
    Y t ω = ξ ω + (∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω))
      - (LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) T ω
          - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral D.W
            (augJoint D) D.isBrownianFiltration_aug Z Z_meas Z_prog
            (sq_int_global_of_vanishing Z_vanish Z_sq) t ω)
      - (LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing U_vanish U_sq) T ω
          - LevyStochCalc.Poisson.Compensated.stochasticIntegral D.N (augJoint D)
            D.isPoissonFiltration_aug (fun ω' s e => U s ω' e) U_meas U_prog
            (marked_sq_int_global_of_vanishing U_vanish U_sq) t ω)
  /-- `Y` ends at the terminal value. -/
  Y_terminal : Y T =ᵐ[P] ξ
  /-- `Y` has finite `S²` seminorm on the horizon. -/
  Y_sup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, (‖Y t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤

/-- A triple that is its own Picard output solves the backward equation. -/
theorem PicardOutput.toSolvesBSDEJ {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : PicardOutput D f ξ T Y Z U Y Z U) :
    SolvesBSDEJ D f ξ T Y Z U where
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := h.U_vanish
  U_sq := h.U_sq
  Y_meas := h.Y_meas
  Y_adapted := h.Y_adapted
  Y_cadlag := h.Y_cadlag
  Y_sup := h.Y_sup
  eqn := h.eqn

/-! ### Measurability of the running supremum -/

/-- The squared supremum over `[0, T]` of a process with measurable slices and right-continuous
paths is measurable. -/
theorem measurable_biSup_sq_of_rightContinuous {M : ℝ → Ω → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hm : ∀ t : ℝ, Measurable (M t))
    (hrc : ∀ (ω : Ω) (t : ℝ), Tendsto (fun s => M s ω) (𝓝[>] t) (𝓝 (M t ω))) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2 := by
  have heq : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖M t ω‖₊ : ℝ≥0∞) ^ 2)
      = fun ω => (⨆ n : ℕ, (‖Probability.dyadicRunMax M T n ω‖₊ : ℝ≥0∞)) ^ 2 := by
    funext ω
    rw [SupBound.biSup_sq_eq_iSup_subtype_sq (fun t => (‖M t ω‖₊ : ℝ≥0∞)) T,
      Probability.iSup_enorm_eq_iSup_dyadicRunMax hT (hrc ω)]
  rw [heq]
  exact (Measurable.iSup fun n =>
    Probability.measurable_enorm_dyadicRunMax hm T n).pow_const 2

/-! ### The Picard step -/

/-- The Picard step from an input triple `(Y', Z', U')` has an output triple: for a drift `b`
that is almost everywhere the generator frozen along the input, the martingale representation of
the centred terminal datum, the càdlàg versions of the two stochastic legs and the primitive of
the drift assemble into a `PicardOutput`. -/
theorem exists_picardOutput (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) {T : ℝ} (hT : 0 < T) {ξ : Ω → ℝ}
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)
    (Y' : ℝ → Ω → ℝ) (Z' : ℝ → Ω → (Fin d → ℝ)) (U' : ℝ → Ω → E → ℝ)
    {b : Ω → ℝ → ℝ} (hbm : Measurable (Function.uncurry b))
    (hbp : Probability.ProgressivelyMeasurable (augJoint D).rightCont b)
    (hbz : ∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    (hbq : Brownian.Ito.energy P T b ≠ ⊤)
    (hb : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      b p.1 p.2 = f p.2 (Y' p.2 p.1) (Z' p.2 p.1) (U' p.2 p.1)) :
    ∃ (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ),
      PicardOutput D f ξ T Y' Z' U' Y Z U := by
  classical
  obtain ⟨Z, U, hZm, hZp, hZv, hZq, hUm, hUp, hUv, hUq, hrep⟩ :=
    exists_picard_integrands_of_rightCont D hT hξ2 hξm hbm hbp hbz hbq
  obtain ⟨MW, hWad, hWme, hWae, hWcd, -, -, hWsup⟩ :=
    exists_cadlag_brownianLeg D T hT.le Z hZm hZp hZv hZq
  obtain ⟨MN, hNad, hNme, hNae, hNcd, -, -, hNsup⟩ :=
    exists_cadlag_poissonLeg D T hT.le U hUm hUp hUv hUq
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ∫ ω, terminalDatum ξ b T ω ∂P := ⟨_, rfl⟩
  have hcen : ∀ ω : Ω, centred P (terminalDatum ξ b T) ω
      = ξ ω + (∫ s in Set.Icc (0 : ℝ) T, b ω s) - c := by
    intro ω
    rw [hc]
    rfl
  have hAme : Measurable (Function.uncurry (driftLeg b T)) := measurable_uncurry_driftLeg hbm
  have hAsl : ∀ t : ℝ, Measurable (driftLeg b T t) := fun t =>
    hAme.comp (measurable_const.prodMk measurable_id)
  have hAct : ∀ ω : Ω, Continuous fun t => driftLeg b T t ω := continuous_driftLeg hbz
  have hWsl : ∀ t : ℝ, Measurable (MW t) := fun t =>
    hWme.comp (measurable_const.prodMk measurable_id)
  have hNsl : ∀ t : ℝ, Measurable (MN t) := fun t =>
    hNme.comp (measurable_const.prodMk measurable_id)
  have hWam : AEMeasurable
      (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MW t ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (measurable_biSup_sq_of_rightContinuous hT.le hWsl fun ω t => (hWcd ω t).1).aemeasurable
  have hNam : AEMeasurable
      (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖MN t ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (measurable_biSup_sq_of_rightContinuous hT.le hNsl fun ω t => (hNcd ω t).1).aemeasurable
  have hAam : AEMeasurable
      (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, (‖-driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) P :=
    (measurable_biSup_sq_of_rightContinuous (M := fun t ω => -driftLeg b T t ω) hT.le
      (fun t => (hAsl t).neg)
      fun ω t => (((hAct ω).neg).tendsto t).mono_left nhdsWithin_le_nhds).aemeasurable
  have hAsup : ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
      (‖-driftLeg b T t ω‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤ := by
    simpa only [nnnorm_neg] using lintegral_biSup_sq_driftLeg_lt_top (P := P) hbm hbq
  refine ⟨fun t ω => c + MW t ω + MN t ω - driftLeg b T t ω, Z, U,
    { Z_meas := hZm, Z_prog := hZp, Z_vanish := hZv, Z_sq := hZq, U_meas := hUm,
      U_prog := hUp, U_vanish := hUv, U_sq := hUq, Y_meas := ?_, Y_adapted := ?_,
      Y_cadlag := ?_, eqn := ?_, Y_terminal := ?_, Y_sup := ?_ }⟩
  · exact ((measurable_const.add hWme).add hNme).sub hAme
  · exact fun t => ((measurable_const.add (hWad t)).add (hNad t)).sub
      (adapted_driftLeg_rightCont_of_rightCont hbm hbp hbz hbq
        (fun _s hs h0 => D.measurableSet_augFiltration_of_null hs h0) t)
  · intro ω t
    obtain ⟨hWr, L₁, hWl⟩ := hWcd ω t
    obtain ⟨hNr, L₂, hNl⟩ := hNcd ω t
    have hAr : Tendsto (fun s => driftLeg b T s ω) (𝓝[>] t) (𝓝 (driftLeg b T t ω)) :=
      ((hAct ω).tendsto t).mono_left nhdsWithin_le_nhds
    have hAl : Tendsto (fun s => driftLeg b T s ω) (𝓝[<] t) (𝓝 (driftLeg b T t ω)) :=
      ((hAct ω).tendsto t).mono_left nhdsWithin_le_nhds
    exact ⟨((tendsto_const_nhds.add hWr).add hNr).sub hAr,
      ⟨c + L₁ + L₂ - driftLeg b T t ω, ((tendsto_const_nhds.add hWl).add hNl).sub hAl⟩⟩
  · intro t ht
    have hbf : ∀ᵐ ω ∂P, ∫ s in Set.Icc t T, b ω s
        = ∫ s in Set.Icc t T, f s (Y' s ω) (Z' s ω) (U' s ω) := by
      filter_upwards [Measure.ae_ae_of_ae_prod hb] with ω hω
      exact integral_congr_ae
        (ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc ht.1 le_rfl) hω)
    filter_upwards [hrep, hWae t, hNae t, driftLeg_ae_eq hbm hbq T,
      driftLeg_sub_ae hbm hbq ht.1 ht.2, hbf] with ω h1 h2 h3 h4 h5 h6
    rw [hcen ω] at h1
    rw [h2, h3]
    linarith [h1, h4, h5, h6]
  · filter_upwards [hrep, hWae T, hNae T, driftLeg_ae_eq hbm hbq T] with ω h1 h2 h3 h4
    rw [hcen ω] at h1
    rw [h2, h3, h4]
    linarith [h1]
  · have hstep := SupBound.lintegral_biSup_sq_const_add_add_add_lt_top (μ := P) c MW MN
      (fun t ω => -driftLeg b T t ω) T hWam hNam hAam hWsup hNsup hAsup
    simpa only [← sub_eq_add_neg] using hstep

end LevyStochCalc.BSDEJ.Solves
