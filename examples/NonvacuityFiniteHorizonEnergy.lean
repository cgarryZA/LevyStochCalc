/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.FiniteHorizonBrownian
import LevyStochCalc.Ito.FiniteHorizonWeighted
import LevyStochCalc.Driver.CrossFiltration
import LevyStochCalc.Poisson.CompensatedDensityLimit
import LevyStochCalc.Brownian.ItoRange

/-!
# The finite-horizon expected product identity on a non-degenerate model

The hypotheses of the finite-horizon expected product identity are met by Itô processes with a
random initial value. Over a Lévy driver `(W, N)`, the Brownian past enlarged by the whole Poisson
path is a filtration for which every coordinate of `W` is a Brownian motion, and its σ-algebra at
time zero contains the compensated masses `Ñ(B) = N(B) - 𝔼 N(B)`. For vectors `v, w`, constant
matrices `G, G'` and `B` of finite positive intensity, the processes

`X_t = Ñ(B) v + ∫_0^t Ñ(B) v ds + ∫_0^t G dW_s`, `Y_t = Ñ(B) w + ∫_0^t G' dW_s`

are square-integrable Itô processes on every window `[0, T]` with random initial values
(`𝔼⟪X₀, Y₀⟫ = ν̄(B) ⟪v, w⟫`, `integral_inner_initial`), and

`𝔼⟪X_t, Y_t⟫ = ν̄(B) ⟪v, w⟫ + ∫_0^t 𝔼(⟪Ñ(B) v, Y_s⟫ + ⟪X_s, 0⟫) ds + t ∑_{m,k} G^{mk} G'^{mk}`

(`integral_inner_example`): the bracket is the Frobenius pairing of the two diffusion matrices.
-/

open MeasureTheory ProbabilityTheory LevyStochCalc.Ito.FiniteHorizon
open scoped NNReal ENNReal RealInnerProductSpace

namespace LevyStochCalc.Examples.FiniteHorizonEnergy

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {E : Type v} [MeasurableSpace E] {ν : Measure E} [SigmaFinite ν] {d n : ℕ}
  (D : Driver.LevyDriver.{u, v, w} P d ν)

/-- A constant integrand has finite energy on every window. -/
theorem lintegral_sq_const_lt_top (c : ℝ) (T : ℝ) :
    ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T, (‖c‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  simp only [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  exact ENNReal.mul_lt_top (ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top)
    (measure_lt_top P _)

/-- The Itô integral `∫_0^t G dW` of a constant matrix against the Brownian part of the driver,
on the Brownian past enlarged by the Poisson path. -/
noncomputable def constItoIntegral (G : Fin n → Fin d → ℝ) : ℝ → Ω → EuclideanSpace ℝ (Fin n) :=
  euclideanItoIntegral D.W D.crossBrownianFiltration D.isBrownianFiltration_crossBrownian
    (fun m k _ _ => G m k) (fun _ _ => measurable_const)
    (fun m k => Brownian.Ito.progressivelyMeasurable_const _ (G m k))
    (fun m k T _ => lintegral_sq_const_lt_top (G m k) T)

/-- The random initial value `Ñ(B) v`. -/
noncomputable def initial (B : Set (ℝ × E)) (x : EuclideanSpace ℝ (Fin n)) (ω : Ω) :
    EuclideanSpace ℝ (Fin n) :=
  D.N.compensated B ω • x

/-- The process `X_t = X₀ + ∫_0^t c X₀ ds + ∫_0^t G dW_s` with `X₀ = Ñ(B) x`. -/
noncomputable def process (B : Set (ℝ × E)) (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (G : Fin n → Fin d → ℝ) (t : ℝ) (ω : Ω) : EuclideanSpace ℝ (Fin n) :=
  initial D B x ω + (∫ _s in Set.Icc (0 : ℝ) t, c • initial D B x ω) + constItoIntegral D G t ω

variable {D} {B : Set (ℝ × E)} (hB : MeasurableSet B)
  (hfin : Poisson.referenceIntensity ν B ≠ ⊤)

include hB in
/-- The initial value is measurable at time zero. -/
theorem stronglyMeasurable_initial (x : EuclideanSpace ℝ (Fin n)) :
    StronglyMeasurable[D.crossBrownianFiltration 0] (initial D B x) :=
  (D.stronglyMeasurable_compensated_crossBrownian 0 hB).smul_const x

include hB hfin in
/-- The initial value is square integrable. -/
theorem memLp_initial (x : EuclideanSpace ℝ (Fin n)) : MemLp (initial D B x) 2 P :=
  (ContinuousLinearMap.toSpanSingleton ℝ x).comp_memLp'
    (Poisson.Compensated.compensated_memLp D.N hB hfin)

include hB hfin in
/-- **The initial values are random:** `𝔼⟪Ñ(B) v, Ñ(B) w⟫ = ν̄(B) ⟪v, w⟫`, with `ν̄(B)` the
intensity of `B`. -/
theorem integral_inner_initial (x y : EuclideanSpace ℝ (Fin n)) :
    ∫ ω, ⟪initial D B x ω, initial D B y ω⟫ ∂P
      = (Poisson.referenceIntensity ν B).toReal * ⟪x, y⟫ := by
  simp only [initial, real_inner_smul_left, real_inner_smul_right, ← mul_assoc, ← sq]
  rw [integral_mul_const, Poisson.Compensated.compensated_second_moment D.N hB hfin]

include hB hfin in
/-- The example processes are square-integrable Itô processes on every window. -/
theorem isL2ItoProcessOn_process (x : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (G : Fin n → Fin d → ℝ) (T : ℝ) :
    IsL2ItoProcessOn D.crossBrownianFiltration P T (process D B x c G) (initial D B x)
      (fun _ ω => c • initial D B x ω) (constItoIntegral D G) where
  initial_aestronglyMeasurable := (stronglyMeasurable_initial hB x).aestronglyMeasurable
  initial_memLp := memLp_initial hB hfin x
  drift_memLp := memLp_comp_fst ((memLp_initial hB hfin x).const_smul c) T
  drift_adapted := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact (((stronglyMeasurable_initial hB x).mono
      (D.crossBrownianFiltration.mono hs.1)).const_smul c).aestronglyMeasurable
  martingale := hasOrthogonalIncrementsOn_euclideanItoIntegral T
  decomposition _ _ _ := Filter.EventuallyEq.rfl

include hB hfin in
/-- **The expected product identity on the example.** For `t ∈ [0, T]`,
`𝔼⟪X_t, Y_t⟫ = ν̄(B) ⟪v, w⟫ + ∫_0^t 𝔼(⟪Ñ(B) v, Y_s⟫ + ⟪X_s, 0⟫) ds
  + t ∑_{m,k} G^{mk} G'^{mk}`. -/
theorem integral_inner_example (x y : EuclideanSpace ℝ (Fin n)) (G G' : Fin n → Fin d → ℝ)
    {t T : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ ω, ⟪process D B x 1 G t ω, process D B y 0 G' t ω⟫ ∂P
      = (Poisson.referenceIntensity ν B).toReal * ⟪x, y⟫
        + (∫ s in Set.Icc (0 : ℝ) t, ∫ ω, (⟪(1 : ℝ) • initial D B x ω, process D B y 0 G' s ω⟫
            + ⟪process D B x 1 G s ω, (0 : ℝ) • initial D B y ω⟫) ∂P)
        + t * ∑ m, ∑ k, G m k * G' m k := by
  rw [integral_inner_eq_add_bracket (isL2ItoProcessOn_process hB hfin x 1 G T)
    (isL2ItoProcessOn_process hB hfin y 0 G' T)
    (hasPolarisedIsometryOn_euclideanItoIntegral T) ht0 htT,
    integral_inner_initial hB hfin x y]
  congr 1
  simp only [inner_euclideanMatrix, integral_const, Measure.restrict_apply_univ,
    Real.volume_Icc, sub_zero, smul_eq_mul, measureReal_def, measure_univ, ENNReal.toReal_one,
    one_mul]
  rw [ENNReal.toReal_ofReal ht0]

end LevyStochCalc.Examples.FiniteHorizonEnergy
