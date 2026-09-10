/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaClosure
import LevyStochCalc.Ito.CadlagExitTime
import LevyStochCalc.Ito.JumpSplittingPath
import LevyStochCalc.Ito.StochasticIntegralLimit

/-!
# The Itô–Lévy formula for a jump diffusion, assembled

The canonical residual of the Itô–Lévy formula, stated for a jump diffusion and proved from the
finite-activity formula by truncating the small jumps and passing to the limit. The statement
carries the hypotheses the assembly consumes, which are those of the cited result together with
the corrections listed in `tools/cited_axioms.md`, entry 16.

## Main statements

* `LevyStochCalc.Ito.JumpFormula.itoLevyFormula_jumpResidual_canonical` — the canonical residual
  is the compensated jump integral plus the compensator-drift integral.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]

theorem itoLevyFormula_jumpResidual_canonical
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ)
    (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
    (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
    -- Statement corrections identified 2026-09-10 (tools/cited_axioms.md, entry 16).
    -- (3) The structure calls its solution adapted but carries no such field.
    (hXadapt : ∀ t : ℝ, Measurable[ℱ t] (X.X t))
    -- (5) The drift along the path: the structure needs neither, its drift term being a Bochner
    -- integral, and the original statement assumed only pathwise integrability.
    (hμm : ∀ i : Fin n, Measurable (Function.uncurry fun ω s => coeffs.μ s (X.X s ω) i))
    (hμq : ∀ (i : Fin n) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coeffs.μ s (X.X s ω) i‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    -- (6) Joint measurability of the jump coefficient, which the bare bundle does not carry.
    (hγmeas : Measurable fun q : ℝ × (Fin n → ℝ) × E => coeffs.γ q.1 q.2.1 q.2.2)
    -- (7) A pointwise-in-the-mark bound along the path, needed by the localisation and not
    -- implied by the coefficient data.
    (hγbound : ∀ᵐ ω ∂P, ∀ T' : ℝ, ∃ M : ℝ,
      ∀ s ∈ Set.Icc (0 : ℝ) T', ∀ e : E, ‖coeffs.γ s (X.X s ω) e‖ ≤ M)
    (u : ℝ → (Fin n → ℝ) → ℝ)
    (_hu : ContDiff ℝ 2 (Function.uncurry u))
    (T : ℝ) (_hT : 0 < T)
    (_h_μ_int : ∀ᵐ ω ∂P, ∀ i : Fin n,
        IntegrableOn (fun s => coeffs.μ s (X.X s ω) i) (Set.Icc (0 : ℝ) T))
    (h_sigmaGrad_meas : ∀ j : Fin d,
        Measurable (Function.uncurry
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j)))
    (h_sigmaGrad_progMeas : ∀ j : Fin d,
        Probability.ProgressivelyMeasurable ℱ
          (fun ω s => diffusionIntegrand u coeffs.σ s (X.X s ω) j))
    (h_sigmaGrad_sq : ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖diffusionIntegrand u coeffs.σ s (X.X s ω) j‖₊ : ℝ≥0∞) ^ 2
            ∂volume ∂P < ⊤)
    (h_jumpInt_meas : Measurable
        (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                          - u s (X.X s ω')) p.1 p.2.1 p.2.2))
    (h_jumpInt_progMeas :
        Probability.MarkedProgressivelyMeasurable ℱ
          (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e) - u s (X.X s ω')))
    (h_jumpInt_sq : ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖u s (X.X s ω + coeffs.γ s (X.X s ω) e)
              - u s (X.X s ω)‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (_h_compDrift_int : ∀ᵐ ω ∂P,
        ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e‖₊ : ℝ≥0∞)
            ∂ν ∂volume < ⊤) :
    ∀ᵐ ω ∂P,
      (u T (X.X T ω) - u 0 (X.X 0 ω)
        - (∫ s in Set.Icc (0 : ℝ) T, driftIntegrand u coeffs s (X.X s ω))
        - LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W ℱ hℱW
            (fun s ω => diffusionIntegrand u coeffs.σ s (X.X s ω))
            h_sigmaGrad_meas h_sigmaGrad_progMeas h_sigmaGrad_sq T ω)
        =
        LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω' s e => u s (X.X s ω' + coeffs.γ s (X.X s ω') e)
                            - u s (X.X s ω'))
            h_jumpInt_meas h_jumpInt_progMeas h_jumpInt_sq T ω
        + ∫ s in Set.Icc (0 : ℝ) T, ∫ e,
            compensatorDriftIntegrand u coeffs.γ s (X.X s ω) e ∂ν := by
  classical
  -- The proof is the small-jump truncation: exhaust the σ-finite mark space by the complements
  -- of a spanning family, apply the finite-activity formula at each, and pass to the limit.
  -- `ae_itoLevy_of_ae_tendsto_integrals` is that last step; what remains are its six inputs.
  --
  -- OBLIGATION 0 (the truncated data). The truncated paths and the two truncated stochastic
  -- terms. `xs m` is `Ito/BigJumpDiffusion.lean`'s `bigJumpPath` at `smallMarks ν m`, whose
  -- `SdeData` comes from `X.is_solution` and whose condition at zero is now discharged by
  -- `Brownian.hF0_augFiltration`; `Bro m` and `Cmp m` are the corresponding integrals.
  obtain ⟨xs, Bro, Cmp, hxs⟩ :
      ∃ (xs : ℕ → ℝ → Ω → (Fin n → ℝ)) (Bro Cmp : ℕ → Ω → ℝ), True := by
    sorry
  refine ae_itoLevy_of_ae_tendsto_integrals coeffs u T (smallMarks ν) xs
    (fun t ω => X.X t ω) Bro _ Cmp _ ?_ ?_ ?_ ?_ ?_ ?_
  · -- OBLIGATION 1 (the finite-activity identity at each mark set). The telescope of
    -- `Ito/JumpFormulaAssembly.lean` over the capped arrival times, with the base point at the
    -- truncated path (`JumpSplittingPath.ae_forall_eq_add_jumpSumLeftAt_of_path`), the jump sum
    -- identified with the compensated integral (`Poisson.PathwiseIdentity`), and the drift
    -- translated by `JumpFormulaFiniteActivity.setIntegral_splitDrift_dictionary` into
    -- `itoLevy_of_splitDrift_and_jumpSum`. The derivative bounds are removed by
    -- `Ito/JumpFormulaCutoff.lean`, whose stochastic-integral transfer is discharged by
    -- `Ito/CadlagExitTime.lean` — for the CONTINUOUS part only, which is where this obligation
    -- has to show that suffices.
    sorry
  · -- OBLIGATION 2 (the endpoint limit). `SmallJumpProcess.exists_seq_ae_tendsto_comp`.
    sorry
  · -- OBLIGATION 3 (the drift limit). `SmallJumpProcess.exists_seq_ae_tendsto_drift_bigJumpProcess`
    -- and `_quadVar_`, bridged into `driftIntegrand` by the dictionary lemmas.
    sorry
  · -- OBLIGATION 4 (the Brownian term's limit). `StochasticIntegralLimit`, whose domination
    -- hypothesis the localisation is meant to supply.
    sorry
  · -- OBLIGATION 5 (the compensated term's limit). `StochasticIntegralLimit`'s mark-cut
    -- corollary, over the eventual-exclusion form of `smallMarks`.
    sorry
  · -- OBLIGATION 6 (the compensator-drift limit). `JumpFormulaLimit`'s
    -- `tendsto_setIntegral_compensatorDrift`, under its domination hypothesis.
    sorry

end LevyStochCalc.Ito.JumpFormula
