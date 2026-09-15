/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.PicardContraction
import LevyStochCalc.BSDEJ.GeneratorModification
import LevyStochCalc.BSDEJ.DriftModification
import LevyStochCalc.BSDEJ.PicardStep
import LevyStochCalc.Probability.ProgressiveCadlag
import LevyStochCalc.Probability.MarkedProgressiveSlice

/-!
# The Picard iterates of a backward equation with jumps

An admissible triple carries the measurability, progressive measurability and square
integrability the Picard step consumes, and the output of a step along an admissible triple is
again admissible, so the step iterates from any admissible starting triple. On the sequence of
iterates the one-step contraction of the exponentially weighted norm `wNorm` at the Young weight
`β = max 2 (24 L²)` gives a geometric bound on the weighted norm of consecutive differences, and
hence a Cauchy estimate for the iterates in `wNorm` and in the unweighted energies.

## Main definitions

* `LevyStochCalc.BSDEJ.Solves.Admissible` — the triples on which the Picard step is defined.
* `LevyStochCalc.BSDEJ.Solves.IsStep` — an output triple of the Picard step, together with the
  drift along the input triple.
* `LevyStochCalc.BSDEJ.Solves.picardSeq` — the sequence of Picard iterates from an admissible
  starting triple.

## Main statements

* `LevyStochCalc.BSDEJ.Solves.Admissible.exists_drift` — the generator frozen along an
  admissible triple has a progressively measurable version of finite energy.
* `LevyStochCalc.BSDEJ.Solves.Admissible.exists_step` — the Picard step along an admissible
  triple has an admissible output triple.
* `LevyStochCalc.BSDEJ.Solves.wNorm_picardSeq_geom` — the weighted norm of consecutive
  iterates decays geometrically with ratio `1/4`.
* `LevyStochCalc.BSDEJ.Solves.wNorm_picardSeq_cauchy` — the iterates are Cauchy for the
  weighted norm.
* `LevyStochCalc.BSDEJ.Solves.energy_picardSeq_cauchy` — the value processes of the iterates
  are Cauchy for the energy on the horizon.

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

/-! ### Admissible triples -/

/-- `(Y, Z, U)` is an admissible triple for the horizon `T`: the triples on which the Picard
step of the backward equation driven by `D` is defined. -/
structure Admissible (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) : Prop where
  /-- `Y` is jointly measurable. -/
  Y_meas : Measurable (Function.uncurry Y)
  /-- `Y` is progressively measurable for the right-continuous augmented joint filtration. -/
  Y_prog : LevyStochCalc.Probability.ProgressivelyMeasurable (augJoint D).rightCont
    fun ω s => Y s ω
  /-- `Y` has finite energy on the horizon. -/
  Y_sq : LevyStochCalc.Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤
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

/-- The output triple of a Picard step is admissible. -/
theorem PicardOutput.admissible {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {ξ : Ω → ℝ} {T : ℝ}
    {Y' Y : ℝ → Ω → ℝ} {Z' Z : ℝ → Ω → (Fin d → ℝ)} {U' U : ℝ → Ω → E → ℝ}
    (h : PicardOutput D f ξ T Y' Z' U' Y Z U) : Admissible D T Y Z U where
  Y_meas := h.Y_meas
  Y_prog := Probability.progressivelyMeasurable_of_rightContinuous
    (fun t => h.Y_adapted t) fun ω t => (h.Y_cadlag ω t).1
  Y_sq := ne_top_of_le_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.Y_sup.ne) energy_le_of_biSup
  Z_meas := h.Z_meas
  Z_prog := h.Z_prog
  Z_vanish := h.Z_vanish
  Z_sq := h.Z_sq
  U_meas := h.U_meas
  U_prog := h.U_prog
  U_vanish := h.U_vanish
  U_sq := h.U_sq

/-! ### The drift of an admissible triple -/

/-- The generator frozen along an admissible triple has a jointly and progressively measurable
version of finite energy that vanishes off the horizon. -/
theorem Admissible.exists_drift {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : Admissible D T Y Z U) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤) :
    ∃ b : Ω → ℝ → ℝ, Measurable (Function.uncurry b)
      ∧ Probability.ProgressivelyMeasurable (augJoint D) b
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
      ∧ Brownian.Ito.energy P T b ≠ ⊤
      ∧ ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          b p.1 p.2 = f p.2 (Y p.2 p.1) (Z p.2 p.1) (U p.2 p.1) := by
  have hle : ∀ t : ℝ, (augJoint D) t ≤ (augJoint D).rightCont t := fun t =>
    Filtration.le_rightCont _ t
  obtain ⟨b, hbm, hbp, hbz, hbq, hb⟩ :=
    Generator.exists_progressive_generator_modification (L := L) D.N (augJoint D).rightCont hf
      hlip hT hf0 h.Y_meas h.Y_prog h.Y_sq h.Z_meas (fun i => (h.Z_prog i).mono hle) h.Z_sq
      h.U_meas (h.U_prog.mono hle)
      (marked_sq_int_global_of_vanishing h.U_vanish h.U_sq)
  obtain ⟨b', hb'm, hb'p, hb'z, hb'q, hb'⟩ :=
    Generator.exists_progressive_modification_of_rightCont (P := P) (ℱ := augJoint D)
      hbm hbp hbz hbq
  refine ⟨b', hb'm, hb'p, hb'z, hb'q, ?_⟩
  filter_upwards [hb', hb] with p h1 h2
  rw [h1, h2]

/-! ### The Picard step on admissible triples -/

/-- A triple of a value process, a diffusion integrand and a jump integrand. -/
abbrev Triple (Ω : Type u) (E : Type v) (d : ℕ) : Type max u v :=
  (ℝ → Ω → ℝ) × (ℝ → Ω → (Fin d → ℝ)) × (ℝ → Ω → E → ℝ)

/-- `(Y₁, Z₁, U₁)` is an output of the Picard step along `(Y, Z, U)`: it is a `PicardOutput`
for a drift that is jointly and progressively measurable, has finite energy, vanishes off the
horizon and agrees almost everywhere with the generator frozen along `(Y, Z, U)`. -/
def IsStep (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν)
    (f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ) (ξ : Ω → ℝ) (T : ℝ)
    (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ)
    (Y₁ : ℝ → Ω → ℝ) (Z₁ : ℝ → Ω → (Fin d → ℝ)) (U₁ : ℝ → Ω → E → ℝ) : Prop :=
  ∃ b : Ω → ℝ → ℝ, Measurable (Function.uncurry b)
    ∧ Probability.ProgressivelyMeasurable (augJoint D) b
    ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
    ∧ Brownian.Ito.energy P T b ≠ ⊤
    ∧ (∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
        b p.1 p.2 = f p.2 (Y p.2 p.1) (Z p.2 p.1) (U p.2 p.1))
    ∧ PicardOutput D f ξ T Y Z U Y₁ Z₁ U₁

/-- The Picard step along an admissible triple has an admissible output triple. -/
theorem Admissible.exists_step {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ} {Y : ℝ → Ω → ℝ}
    {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ} (h : Admissible D T Y Z U) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P) :
    ∃ (Y₁ : ℝ → Ω → ℝ) (Z₁ : ℝ → Ω → (Fin d → ℝ)) (U₁ : ℝ → Ω → E → ℝ),
      Admissible D T Y₁ Z₁ U₁ ∧ IsStep D f ξ T Y Z U Y₁ Z₁ U₁ := by
  obtain ⟨b, hbm, hbp, hbz, hbq, hb⟩ := h.exists_drift (L := L) hT hf hlip hf0
  obtain ⟨Y₁, Z₁, U₁, hout⟩ := exists_picardOutput D f hT hξ2 hξm Y Z U hbm
    (hbp.mono fun t => Filtration.le_rightCont _ t) hbz hbq hb
  exact ⟨Y₁, Z₁, U₁, hout.admissible, b, hbm, hbp, hbz, hbq, hb, hout⟩

/-- The Picard step along an admissible triple, as an existential over triples. -/
theorem Admissible.exists_stepTriple {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
    {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ} {p : Triple Ω E d}
    (h : Admissible D T p.1 p.2.1 p.2.2) (hT : 0 < T)
    (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P) :
    ∃ q : Triple Ω E d, Admissible D T q.1 q.2.1 q.2.2
      ∧ IsStep D f ξ T p.1 p.2.1 p.2.2 q.1 q.2.1 q.2.2 := by
  obtain ⟨Y₁, Z₁, U₁, hA, hS⟩ := h.exists_step (L := L) hT hf hlip hf0 hξ2 hξm
  exact ⟨(Y₁, Z₁, U₁), hA, hS⟩

/-! ### The sequence of Picard iterates -/

section Iterates

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}

/-- The admissible triples of the backward equation driven by `D` over the horizon `T`. -/
abbrev AdmTriple (D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν) (T : ℝ) :
    Type max u v :=
  {p : Triple Ω E d // Admissible D T p.1 p.2.1 p.2.2}

variable (hT : 0 < T)
  (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
  (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
    (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
  (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
  (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)

/-- One Picard step, as a map on admissible triples. -/
noncomputable def stepAdm (q : AdmTriple D T) : AdmTriple D T :=
  ⟨Classical.choose (q.2.exists_stepTriple (L := L) hT hf hlip hf0 hξ2 hξm),
    (Classical.choose_spec (q.2.exists_stepTriple (L := L) hT hf hlip hf0 hξ2 hξm)).1⟩

/-- The sequence of Picard iterates from an admissible starting triple. -/
noncomputable def picardSeq (p₀ : AdmTriple D T) (n : ℕ) : Triple Ω E d :=
  ((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀).val

/-- The Picard iterates start at the given triple. -/
theorem picardSeq_zero (p₀ : AdmTriple D T) :
    picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0 = p₀.val := rfl

/-- Every Picard iterate is admissible. -/
theorem picardSeq_admissible (p₀ : AdmTriple D T) (n : ℕ) :
    Admissible D T (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 :=
  ((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀).2

/-- Each Picard iterate is an output of the Picard step along its predecessor. -/
theorem picardSeq_succ_isStep (p₀ : AdmTriple D T) (n : ℕ) :
    IsStep D f ξ T (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 := by
  have hsucc : picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)
      = (stepAdm hT hf hlip hf0 hξ2 hξm
          ((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀)).val :=
    congrArg Subtype.val (Function.iterate_succ_apply' _ n p₀)
  rw [hsucc]
  exact (Classical.choose_spec
    ((((stepAdm hT hf hlip hf0 hξ2 hξm)^[n] p₀).2).exists_stepTriple
      (L := L) hT hf hlip hf0 hξ2 hξm)).2

/-- Each Picard iterate is a `PicardOutput` along its predecessor. -/
theorem picardSeq_succ_picardOutput (p₀ : AdmTriple D T) (n : ℕ) :
    PicardOutput D f ξ T (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1
      (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 := by
  obtain ⟨b, -, -, -, -, -, hout⟩ := picardSeq_succ_isStep hT hf hlip hf0 hξ2 hξm p₀ n
  exact hout

end Iterates

/-! ### Subadditivity and lower bounds for the weighted norm -/

section WNorm

variable {β T : ℝ}

/-- The extended norm of a difference of reals is symmetric. -/
theorem coe_nnnorm_sub_comm (x y : ℝ) : (‖x - y‖₊ : ℝ≥0∞) = (‖y - x‖₊ : ℝ≥0∞) := by
  have h : ‖x - y‖₊ = ‖y - x‖₊ := by rw [← nnnorm_neg (x - y), neg_sub]
  rw [h]

/-- The squared extended norm of a difference is dominated by twice the sum of the squares of
the two differences through an intermediate point. -/
theorem sq_nnnorm_sub_le_two_mul_mid (a b c : ℝ) :
    (‖a - c‖₊ : ℝ≥0∞) ^ 2 ≤ 2 * (‖a - b‖₊ : ℝ≥0∞) ^ 2 + 2 * (‖b - c‖₊ : ℝ≥0∞) ^ 2 := by
  have h := Brownian.Ito.sq_nnnorm_sub_le_two_mul (a - b) (c - b)
  rw [show a - b - (c - b) = a - c by ring, coe_nnnorm_sub_comm c b] at h
  refine h.trans (le_of_eq ?_)
  ring

omit [MeasurableSpace Ω] in
/-- The pointwise energy density of a difference is dominated by twice the sum of the densities
of the two differences through an intermediate triple. -/
theorem density_sub_le_two_mul_mid (ν : Measure E) {Y₁ Y₃ : ℝ → Ω → ℝ}
    (Y₂ : ℝ → Ω → ℝ) {Z₁ Z₃ : ℝ → Ω → (Fin d → ℝ)} (Z₂ : ℝ → Ω → (Fin d → ℝ))
    {U₁ U₂ U₃ : ℝ → Ω → E → ℝ} (ω : Ω) (s : ℝ)
    (hU : Measurable fun e => U₁ s ω e - U₂ s ω e) :
    density ν (fun t ω => Y₁ t ω - Y₃ t ω) (fun t ω => Z₁ t ω - Z₃ t ω)
        (fun t ω e => U₁ t ω e - U₃ t ω e) ω s
      ≤ 2 * density ν (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
            (fun t ω e => U₁ t ω e - U₂ t ω e) ω s
        + 2 * density ν (fun t ω => Y₂ t ω - Y₃ t ω) (fun t ω => Z₂ t ω - Z₃ t ω)
            (fun t ω e => U₂ t ω e - U₃ t ω e) ω s := by
  classical
  simp only [density, Pi.sub_apply]
  have hY := sq_nnnorm_sub_le_two_mul_mid (Y₁ s ω) (Y₂ s ω) (Y₃ s ω)
  have hZ : ∑ j, (‖Z₁ s ω j - Z₃ s ω j‖₊ : ℝ≥0∞) ^ 2
      ≤ 2 * (∑ j, (‖Z₁ s ω j - Z₂ s ω j‖₊ : ℝ≥0∞) ^ 2)
        + 2 * ∑ j, (‖Z₂ s ω j - Z₃ s ω j‖₊ : ℝ≥0∞) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => sq_nnnorm_sub_le_two_mul_mid _ _ _
  have hUi : (∫⁻ e, (‖U₁ s ω e - U₃ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      ≤ 2 * (∫⁻ e, (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
        + 2 * ∫⁻ e, (‖U₂ s ω e - U₃ s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν := by
    have hm : Measurable fun e => 2 * (‖U₁ s ω e - U₂ s ω e‖₊ : ℝ≥0∞) ^ 2 :=
      measurable_const.mul (hU.nnnorm.coe_nnreal_ennreal.pow_const 2)
    refine le_trans (lintegral_mono fun e => sq_nnnorm_sub_le_two_mul_mid _ (U₂ s ω e) _)
      (le_of_eq ?_)
    rw [lintegral_add_left hm, lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
  refine le_trans (add_le_add (add_le_add hY hZ) hUi) (le_of_eq ?_)
  ring

omit [IsProbabilityMeasure P] in
/-- A window integral dominated pointwise by twice the sum of two others is dominated by twice
the sum of their window integrals. -/
theorem lintegral_Icc_le_two_mul_add {G G₁ G₂ : Ω → ℝ → ℝ≥0∞}
    (hG₁ : Measurable (Function.uncurry G₁)) (hle : ∀ ω s, G ω s ≤ 2 * G₁ ω s + 2 * G₂ ω s) :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G ω s ∂volume ∂P
      ≤ 2 * (∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G₁ ω s ∂volume ∂P)
        + 2 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G₂ ω s ∂volume ∂P := by
  have h1 : ∀ ω : Ω, Measurable fun s => G₁ ω s := fun ω =>
    hG₁.comp (measurable_const.prodMk measurable_id)
  have hin : ∀ ω : Ω, ∫⁻ s in Set.Icc (0 : ℝ) T, G ω s ∂volume
      ≤ 2 * (∫⁻ s in Set.Icc (0 : ℝ) T, G₁ ω s ∂volume)
        + 2 * ∫⁻ s in Set.Icc (0 : ℝ) T, G₂ ω s ∂volume := by
    intro ω
    refine le_trans (lintegral_mono fun s => hle ω s) (le_of_eq ?_)
    rw [lintegral_add_left ((h1 ω).const_mul 2), lintegral_const_mul' _ _ (by norm_num),
      lintegral_const_mul' _ _ (by norm_num)]
  refine le_trans (lintegral_mono hin) (le_of_eq ?_)
  have hout : Measurable fun ω : Ω => ∫⁻ s in Set.Icc (0 : ℝ) T, G₁ ω s ∂volume :=
    hG₁.lintegral_prod_right'
  rw [lintegral_add_left (hout.const_mul 2), lintegral_const_mul' _ _ (by norm_num),
    lintegral_const_mul' _ _ (by norm_num)]

omit [IsProbabilityMeasure P] in
/-- The weighted norm of a difference is dominated by twice the sum of the weighted norms of the
two differences through an intermediate triple. -/
theorem wNorm_sub_le_two_mul_mid {Y₁ Y₂ Y₃ : ℝ → Ω → ℝ} {Z₁ Z₂ Z₃ : ℝ → Ω → (Fin d → ℝ)}
    {U₁ U₂ U₃ : ℝ → Ω → E → ℝ}
    (hYm : Measurable (Function.uncurry fun ω s => Y₁ s ω - Y₂ s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z₁ s ω j - Z₂ s ω j))
    (hUm : Measurable fun p : Ω × ℝ × E => U₁ p.2.1 p.1 p.2.2 - U₂ p.2.1 p.1 p.2.2) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₃ t ω) (fun t ω => Z₁ t ω - Z₃ t ω)
        (fun t ω e => U₁ t ω e - U₃ t ω e)
      ≤ 2 * wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
            (fun t ω e => U₁ t ω e - U₂ t ω e)
        + 2 * wNorm P ν β T (fun t ω => Y₂ t ω - Y₃ t ω) (fun t ω => Z₂ t ω - Z₃ t ω)
            (fun t ω e => U₂ t ω e - U₃ t ω e) := by
  have hwm : Measurable fun s : ℝ => ENNReal.ofReal (Real.exp (β * s)) :=
    ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_id))
  have hdm : Measurable (Function.uncurry fun (ω : Ω) (s : ℝ) =>
      ENNReal.ofReal (Real.exp (β * s))
        * density ν (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
            (fun t ω e => U₁ t ω e - U₂ t ω e) ω s) :=
    (hwm.comp measurable_snd).mul (measurable_uncurry_density hYm hZm hUm)
  simp only [wNorm_eq_lintegral_density]
  refine lintegral_Icc_le_two_mul_add hdm fun ω s => ?_
  have hU : Measurable fun e => U₁ s ω e - U₂ s ω e :=
    hUm.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  refine le_trans (mul_le_mul' le_rfl (density_sub_le_two_mul_mid ν Y₂ Z₂ ω s hU))
    (le_of_eq ?_)
  ring

omit [SigmaFinite ν] in
/-- The weighted norm of the difference of a triple with itself vanishes. -/
theorem wNorm_sub_self (Y : ℝ → Ω → ℝ) (Z : ℝ → Ω → (Fin d → ℝ)) (U : ℝ → Ω → E → ℝ) :
    wNorm P ν β T (fun t ω => Y t ω - Y t ω) (fun t ω => Z t ω - Z t ω)
      (fun t ω e => U t ω e - U t ω e) = 0 := by
  simp [wNorm]

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The weighted norm of a difference of triples is symmetric in the two triples. -/
theorem wNorm_sub_comm (Y₁ Y₂ : ℝ → Ω → ℝ) (Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ))
    (U₁ U₂ : ℝ → Ω → E → ℝ) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
        (fun t ω e => U₁ t ω e - U₂ t ω e)
      = wNorm P ν β T (fun t ω => Y₂ t ω - Y₁ t ω) (fun t ω => Z₂ t ω - Z₁ t ω)
        (fun t ω e => U₂ t ω e - U₁ t ω e) := by
  classical
  have hswap : ∀ a b : ℝ, (‖a - b‖₊ : ℝ≥0∞) ^ 2 = (‖b - a‖₊ : ℝ≥0∞) ^ 2 := fun a b => by
    rw [coe_nnnorm_sub_comm]
  simp only [wNorm, Pi.sub_apply]
  refine lintegral_congr fun ω => lintegral_congr fun s => ?_
  congr 2
  · congr 1
    · exact hswap _ _
    · exact Finset.sum_congr rfl fun j _ => hswap _ _
  · exact lintegral_congr fun e => hswap _ _

omit [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- The energy of the pointwise density on the horizon is at most the weighted norm. -/
theorem lintegral_density_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} :
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, density ν Y Z U ω s ∂volume ∂P ≤ wNorm P ν β T Y Z U := by
  rw [wNorm_eq_lintegral_density]
  refine lintegral_mono fun ω => lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal]
  exact Real.one_le_exp (mul_nonneg hβ hs.1)

omit [SigmaFinite ν] in
/-- The sum of the energy of the value, of the energies of the diffusion coordinates and of the
marked energy of the jump integrand is at most the weighted norm. -/
theorem energies_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    Brownian.Ito.energy P T (fun ω s => Y s ω)
        + (∑ j, Brownian.Ito.energy P T (fun ω s => Z s ω j))
        + Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e)
      ≤ wNorm P ν β T Y Z U := by
  rw [← lintegral_density_eq hYm hZm]
  exact lintegral_density_le_wNorm hβ

omit [SigmaFinite ν] in
/-- The energy of the value of a triple is at most its weighted norm. -/
theorem energy_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    Brownian.Ito.energy P T (fun ω s => Y s ω) ≤ wNorm P ν β T Y Z U :=
  (le_self_add.trans le_self_add).trans (energies_le_wNorm hβ hYm hZm)

omit [SigmaFinite ν] in
/-- The energy of a diffusion coordinate of a triple is at most its weighted norm. -/
theorem energy_coord_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) (i : Fin d) :
    Brownian.Ito.energy P T (fun ω s => Z s ω i) ≤ wNorm P ν β T Y Z U :=
  ((Finset.single_le_sum (f := fun j => Brownian.Ito.energy P T (fun ω s => Z s ω j))
    (fun _ _ => zero_le) (Finset.mem_univ i)).trans
      (le_add_self.trans le_self_add)).trans (energies_le_wNorm hβ hYm hZm)

omit [SigmaFinite ν] in
/-- The marked energy of the jump integrand of a triple is at most its weighted norm. -/
theorem markedEnergy_le_wNorm (hβ : 0 ≤ β) {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
    {U : ℝ → Ω → E → ℝ} (hYm : Measurable (Function.uncurry fun ω s => Y s ω))
    (hZm : ∀ j, Measurable (Function.uncurry fun ω s => Z s ω j)) :
    Poisson.Compensated.markedEnergy P ν T (fun ω s e => U s ω e) ≤ wNorm P ν β T Y Z U :=
  le_add_self.trans (energies_le_wNorm hβ hYm hZm)

/-- The value process of an admissible triple is jointly measurable in the sample point and the
time. -/
theorem Admissible.measurable_uncurry_Y {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)} {U : ℝ → Ω → E → ℝ}
    (h : Admissible D T Y Z U) : Measurable (Function.uncurry fun ω s => Y s ω) :=
  h.Y_meas.comp measurable_swap

/-- The weighted norm of the difference of two admissible triples is finite. -/
theorem Admissible.wNorm_sub_ne_top {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
    {Y₁ Y₂ : ℝ → Ω → ℝ} {Z₁ Z₂ : ℝ → Ω → (Fin d → ℝ)} {U₁ U₂ : ℝ → Ω → E → ℝ}
    (h₁ : Admissible D T Y₁ Z₁ U₁) (h₂ : Admissible D T Y₂ Z₂ U₂) (hβ : 0 ≤ β) :
    wNorm P ν β T (fun t ω => Y₁ t ω - Y₂ t ω) (fun t ω => Z₁ t ω - Z₂ t ω)
      (fun t ω e => U₁ t ω e - U₂ t ω e) ≠ ⊤ :=
  wNorm_ne_top_of_energies hβ (h₁.measurable_uncurry_Y.sub h₂.measurable_uncurry_Y)
    (fun j => (h₁.Z_meas j).sub (h₂.Z_meas j))
    (energy_sub_ne_top h₁.measurable_uncurry_Y h₂.measurable_uncurry_Y h₁.Y_sq h₂.Y_sq)
    (fun j => energy_sub_ne_top (h₁.Z_meas j) (h₂.Z_meas j) (h₁.Z_sq j) (h₂.Z_sq j))
    (Ito.Stability.lintegral_sq_sub_marked_lt_top h₁.U_meas h₂.U_meas
      (lt_top_iff_ne_top.mpr h₁.U_sq) (lt_top_iff_ne_top.mpr h₂.U_sq)).ne

end WNorm

/-! ### The geometric Cauchy estimate along the iterates -/

section Cauchy

variable {D : LevyStochCalc.Driver.LevyDriver.{u, v, w} P d ν}
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L T : ℝ} {ξ : Ω → ℝ}
  (hT : 0 < T)
  (hf : ∀ u : E → ℝ, Measurable fun q : ℝ × ℝ × (Fin d → ℝ) => f q.1 q.2.1 q.2.2 u)
  (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
    (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
      ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
        + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
  (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
  (hξ2 : MemLp ξ 2 P) (hξm : AEStronglyMeasurable[augJoint D T] ξ P)

/-- The Young weight of the Picard contraction is nonnegative. -/
theorem zero_le_youngWeight (L : ℝ) : (0 : ℝ) ≤ max 2 (24 * L ^ 2) :=
  le_trans (by norm_num) (le_max_left _ _)

/-- Consecutive Picard iterates contract the weighted norm by `1/4` at the Young weight
`max 2 (24 L²)`. -/
theorem wNorm_picardSeq_succ_le (hL : 0 ≤ L) (p₀ : AdmTriple D T) (n : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1 + 1)).1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1 t ω)
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1 + 1)).2.1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1 t ω)
        (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1 + 1)).2.2 t ω e
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 t ω e)
      ≤ 4⁻¹ * wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
        (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 t ω e
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) := by
  obtain ⟨b₁, hb₁m, hb₁p, hb₁z, hb₁q, hb₁, hout₁⟩ :=
    picardSeq_succ_isStep hT hf hlip hf0 hξ2 hξm p₀ (n + 1)
  obtain ⟨b₂, hb₂m, hb₂p, hb₂z, hb₂q, hb₂, hout₂⟩ :=
    picardSeq_succ_isStep hT hf hlip hf0 hξ2 hξm p₀ n
  have hA₁ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ (n + 1)
  have hA₀ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ n
  exact wNorm_sub_le_of_picardOutput hL hlip hT hout₁ hout₂
    (hA₁.measurable_uncurry_Y.sub hA₀.measurable_uncurry_Y)
    (fun j => (hA₁.Z_meas j).sub (hA₀.Z_meas j)) (hA₁.U_meas.sub hA₀.U_meas)
    hb₁m hb₁p hb₁z hb₁q hb₁ hb₂m hb₂p hb₂z hb₂q hb₂
    (hA₁.wNorm_sub_ne_top hA₀ (zero_le_youngWeight L))

/-- The weighted norm of consecutive Picard iterates decays geometrically with ratio `1/4`. -/
theorem wNorm_picardSeq_geom (hL : 0 ≤ L) (p₀ : AdmTriple D T) (n : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (n + 1)).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e)
      ≤ ((4 : ℝ≥0∞)⁻¹) ^ n *
        wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
          (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) := by
  induction n with
  | zero => simp
  | succ n ih =>
    refine le_trans (wNorm_picardSeq_succ_le hT hf hlip hf0 hξ2 hξm hL p₀ n) ?_
    refine le_trans (mul_le_mul' le_rfl ih) (le_of_eq ?_)
    rw [pow_succ]
    ring

/-- The weighted norm of the difference between an iterate and a later one is at most four
times the geometric bound at the earlier index. -/
theorem wNorm_picardSeq_sub_le_of_add (hL : 0 ≤ L) (p₀ : AdmTriple D T) (k m : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (m + k)).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (m + k)).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ (m + k)).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e)
      ≤ 4 * ((4 : ℝ≥0∞)⁻¹) ^ m *
        wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
          (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) := by
  have harith : ∀ a W : ℝ≥0∞,
      2 * (4 * (a * (4 : ℝ≥0∞)⁻¹) * W) + 2 * (a * W) = 4 * a * W := by
    intro a W
    have h84 : (8 : ℝ≥0∞) * (4 : ℝ≥0∞)⁻¹ = 2 := by
      rw [show (8 : ℝ≥0∞) = 2 * 4 by norm_num, mul_assoc,
        ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]
    calc 2 * (4 * (a * (4 : ℝ≥0∞)⁻¹) * W) + 2 * (a * W)
        = 8 * (4 : ℝ≥0∞)⁻¹ * (a * W) + 2 * (a * W) := by ring
      _ = 2 * (a * W) + 2 * (a * W) := by rw [h84]
      _ = 4 * a * W := by ring
  induction k generalizing m with
  | zero =>
    rw [Nat.add_zero, wNorm_sub_self]
    exact zero_le
  | succ k ih =>
    have hidx : m + (k + 1) = m + 1 + k := by omega
    rw [hidx]
    have hA₁ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ (m + 1 + k)
    have hA₂ := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ (m + 1)
    refine le_trans (wNorm_sub_le_two_mul_mid
      (hA₁.measurable_uncurry_Y.sub hA₂.measurable_uncurry_Y)
      (fun j => (hA₁.Z_meas j).sub (hA₂.Z_meas j)) (hA₁.U_meas.sub hA₂.U_meas)) ?_
    refine le_trans (add_le_add (mul_le_mul' le_rfl (ih (m + 1)))
      (mul_le_mul' le_rfl (wNorm_picardSeq_geom hT hf hlip hf0 hξ2 hξm hL p₀ m)))
      (le_of_eq ?_)
    rw [pow_succ]
    exact harith _ _

/-- Powers of `1/4` in the extended nonnegative reals decrease along the exponent. -/
theorem pow_four_inv_le_of_le {i j : ℕ} (hij : i ≤ j) :
    ((4 : ℝ≥0∞)⁻¹) ^ j ≤ ((4 : ℝ≥0∞)⁻¹) ^ i := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hij
  rw [pow_add]
  exact mul_le_of_le_one_right' (pow_le_one' (ENNReal.inv_le_one.mpr (by norm_num)) c)

/-- A geometric sequence of ratio `1/4` with a finite factor is eventually below any positive
threshold. -/
theorem exists_geom_lt (W : ℝ≥0∞) (hW : W ≠ ⊤) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ j : ℕ, N ≤ j → 4 * ((4 : ℝ≥0∞)⁻¹) ^ j * W < ε := by
  have htend : Tendsto (fun N : ℕ => ((4 : ℝ≥0∞)⁻¹) ^ N * (4 * W)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => ((4 : ℝ≥0∞)⁻¹) ^ N) atTop (𝓝 0) :=
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by rw [ENNReal.inv_lt_one]; norm_num)
    simpa using ENNReal.Tendsto.mul_const h1
      (Or.inr (ENNReal.mul_ne_top (by norm_num) hW))
  obtain ⟨N, hN⟩ := (htend.eventually (gt_mem_nhds hε)).exists
  refine ⟨N, fun j hj => ?_⟩
  refine lt_of_le_of_lt ?_ hN
  calc 4 * ((4 : ℝ≥0∞)⁻¹) ^ j * W = ((4 : ℝ≥0∞)⁻¹) ^ j * (4 * W) := by ring
    _ ≤ ((4 : ℝ≥0∞)⁻¹) ^ N * (4 * W) := mul_le_mul' (pow_four_inv_le_of_le hj) le_rfl

/-- The weighted norm of the difference of two Picard iterates is at most four times the
geometric bound at the smaller index. -/
theorem wNorm_picardSeq_sub_le (hL : 0 ≤ L) (p₀ : AdmTriple D T) (m n : ℕ) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e)
      ≤ 4 * ((4 : ℝ≥0∞)⁻¹) ^ min m n *
        wNorm P ν (max 2 (24 * L ^ 2)) T
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
          (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
          (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
            - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) := by
  rcases le_total m n with h | h
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [min_eq_left (Nat.le_add_right m k)]
    refine le_trans (le_of_eq (wNorm_sub_comm _ _ _ _ _ _)) ?_
    exact wNorm_picardSeq_sub_le_of_add hT hf hlip hf0 hξ2 hξm hL p₀ k m
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [min_eq_right (Nat.le_add_right n k)]
    exact wNorm_picardSeq_sub_le_of_add hT hf hlip hf0 hξ2 hξm hL p₀ k n

/-- The weighted norm of the first difference of the Picard iterates is finite. -/
theorem wNorm_picardSeq_zero_ne_top (p₀ : AdmTriple D T) :
    wNorm P ν (max 2 (24 * L ^ 2)) T
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).1 t ω)
      (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.1 t ω)
      (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 1).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ 0).2.2 t ω e) ≠ ⊤ :=
  (picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ 1).wNorm_sub_ne_top
    (picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ 0) (zero_le_youngWeight L)

/-- The Picard iterates are Cauchy for the weighted norm at the Young weight
`max 2 (24 L²)`. -/
theorem wNorm_picardSeq_cauchy (hL : 0 ≤ L) (p₀ : AdmTriple D T) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      wNorm P ν (max 2 (24 * L ^ 2)) T
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
        (fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
        (fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_geom_lt _
    (wNorm_picardSeq_zero_ne_top hT hf hlip hf0 hξ2 hξm p₀) ε hε
  exact ⟨N, fun m hm n hn => lt_of_le_of_lt
    (wNorm_picardSeq_sub_le hT hf hlip hf0 hξ2 hξm hL p₀ m n) (hN _ (le_min hm hn))⟩

/-- The value processes of the Picard iterates are Cauchy for the energy on the horizon. -/
theorem energy_picardSeq_cauchy (hL : 0 ≤ L) (p₀ : AdmTriple D T) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 s ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 s ω) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := wNorm_picardSeq_cauchy hT hf hlip hf0 hξ2 hξm hL p₀ ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have hAm := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ m
  have hAn := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ n
  exact lt_of_le_of_lt
    (energy_le_wNorm (Y := fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (Z := fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (U := fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) (zero_le_youngWeight L)
      (hAm.measurable_uncurry_Y.sub hAn.measurable_uncurry_Y)
      fun j => (hAm.Z_meas j).sub (hAn.Z_meas j)) (hN m hm n hn)

/-- Each diffusion coordinate of the Picard iterates is Cauchy for the energy on the
horizon. -/
theorem energy_picardSeq_cauchy_coord (hL : 0 ≤ L) (p₀ : AdmTriple D T) (i : Fin d) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Brownian.Ito.energy P T (fun ω s => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 s ω i
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 s ω i) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := wNorm_picardSeq_cauchy hT hf hlip hf0 hξ2 hξm hL p₀ ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have hAm := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ m
  have hAn := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ n
  exact lt_of_le_of_lt
    (energy_coord_le_wNorm (Y := fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (Z := fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (U := fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) (zero_le_youngWeight L)
      (hAm.measurable_uncurry_Y.sub hAn.measurable_uncurry_Y)
      (fun j => (hAm.Z_meas j).sub (hAn.Z_meas j)) i) (hN m hm n hn)

/-- The jump integrands of the Picard iterates are Cauchy for the marked energy on the
horizon. -/
theorem markedEnergy_picardSeq_cauchy (hL : 0 ≤ L) (p₀ : AdmTriple D T) :
    ∀ ε : ℝ≥0∞, 0 < ε → ∃ N : ℕ, ∀ m, N ≤ m → ∀ n, N ≤ n →
      Poisson.Compensated.markedEnergy P ν T
        (fun ω s e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 s ω e
          - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 s ω e) < ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := wNorm_picardSeq_cauchy hT hf hlip hf0 hξ2 hξm hL p₀ ε hε
  refine ⟨N, fun m hm n hn => ?_⟩
  have hAm := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ m
  have hAn := picardSeq_admissible hT hf hlip hf0 hξ2 hξm p₀ n
  exact lt_of_le_of_lt
    (markedEnergy_le_wNorm (Y := fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).1 t ω)
      (Z := fun t ω => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.1 t ω
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.1 t ω)
      (U := fun t ω e => (picardSeq hT hf hlip hf0 hξ2 hξm p₀ m).2.2 t ω e
        - (picardSeq hT hf hlip hf0 hξ2 hξm p₀ n).2.2 t ω e) (zero_le_youngWeight L)
      (hAm.measurable_uncurry_Y.sub hAn.measurable_uncurry_Y)
      fun j => (hAm.Z_meas j).sub (hAn.Z_meas j)) (hN m hm n hn)

end Cauchy

end LevyStochCalc.BSDEJ.Solves
