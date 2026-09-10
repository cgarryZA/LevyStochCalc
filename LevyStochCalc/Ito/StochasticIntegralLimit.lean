/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaRandomShift
import LevyStochCalc.Poisson.SmallJump

/-!
# Limits of stochastic integrals along dominated sequences of integrands

A sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function converges to its limit in the energy norm, over `P ⊗ ds` for a
Brownian integrand and over `P ⊗ ds ⊗ ν` for a marked one. Through the `L²` isometries of the
Itô and compensated Itô–Lévy integrals this transfers to the integrals themselves: they converge
in `L²`, hence almost surely along a subsequence.

## Main statements

All statements live in the `LevyStochCalc.Ito.IntegralLimit` namespace.

* `tendsto_lintegral_sq_sub_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds`.
* `tendsto_lintegral_sq_sub_mark_of_dominated` — dominated convergence in the energy norm over
  `P ⊗ ds ⊗ ν`.
* `tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated` and
  `exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated` — the Itô integrals of a
  dominated sequence of integrands converge in `L²`, and almost surely along a strictly monotone
  subsequence.
* `tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated` and
  `exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated` — the same for the
  compensated Itô–Lévy integral.
* `tendsto_lintegral_sq_stochasticIntegral_markCut_compl` and
  `exists_seq_ae_tendsto_stochasticIntegral_markCut_compl` — the compensated Itô–Lévy integrals
  of an integrand cut to the complements of a family of mark sets that eventually misses almost
  every mark converge to the compensated Itô–Lévy integral of the integrand; the suffix
  `_of_antitone` names the same conclusions under an antitone family with null intersection.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.4 (Thm 4.4.7).
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.IntegralLimit

universe u v

section Basic

variable {α : Type*} [MeasurableSpace α]

/-- Dominated convergence for a sequence of nonnegative functions tending to `0`. -/
theorem tendsto_lintegral_of_dominated_tendsto_zero {μ : Measure α} {F : ℕ → α → ℝ≥0∞}
    (bound : α → ℝ≥0∞) (hF : ∀ m, AEMeasurable (F m) μ) (hb : ∀ m, F m ≤ᵐ[μ] bound)
    (hfin : ∫⁻ a, bound a ∂μ ≠ ⊤)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun m => F m a) atTop (𝓝 0)) :
    Tendsto (fun m => ∫⁻ a, F m a ∂μ) atTop (𝓝 0) := by
  have h := MeasureTheory.tendsto_lintegral_of_dominated_convergence' (μ := μ) (F := F)
    (f := fun _ => (0 : ℝ≥0∞)) bound hF hb hfin hlim
  simpa using h

/-- Two reals whose norms are bounded by `c` differ by at most `2 c` in the squared extended
norm. -/
theorem sq_enorm_sub_le_of_norm_le {u v c : ℝ} (hu : ‖u‖ ≤ c) (hv : ‖v‖ ≤ c) :
    (‖u - v‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * (‖c‖₊ : ℝ≥0∞) ^ 2 := by
  have hc0 : (0 : ℝ) ≤ c := le_trans (norm_nonneg u) hu
  have habs : |u - v| ≤ 2 * |c| := by
    rw [abs_of_nonneg hc0]
    have h1 : |u - v| ≤ |u| + |v| := by
      rw [sub_eq_add_neg]
      exact (abs_add_le _ _).trans_eq (by rw [abs_neg])
    have h2 : |u| + |v| ≤ c + c := add_le_add hu hv
    linarith
  have h := LevyStochCalc.Brownian.Ito.sq_enorm_le_of_abs_le (c := 2) (by norm_num) habs
  simpa [show ((2 : ℝ≥0∞)) ^ 2 = 4 from by norm_num] using h

/-- The square of the extended norm of a sequence of reals converging to a limit tends to `0`
after subtracting the limit. -/
theorem tendsto_sq_enorm_sub {f : ℕ → ℝ} {a : ℝ} (h : Tendsto f atTop (𝓝 a)) :
    Tendsto (fun m => (‖f m - a‖₊ : ℝ≥0∞) ^ 2) atTop (𝓝 0) := by
  have h1 : Tendsto (fun m => f m - a) atTop (𝓝 0) := by
    simpa using h.sub_const a
  have h2 : Tendsto (fun m => (‖f m - a‖₊ : ℝ≥0)) atTop (𝓝 0) := by simpa using h1.nnnorm
  have h3 : Tendsto (fun m => (‖f m - a‖₊ : ℝ≥0) ^ 2) atTop (𝓝 0) := by simpa using h2.pow 2
  simpa [ENNReal.coe_pow] using ENNReal.tendsto_coe.2 h3

end Basic

section Unmarked

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- Along a sequence of integrands converging pointwise almost everywhere and dominated by a
square-integrable function, the energy of the difference to the limit over `P ⊗ ds` vanishes. -/
theorem tendsto_lintegral_sq_sub_of_dominated {H : ℕ → Ω → ℝ → ℝ} {H₀ : Ω → ℝ → ℝ}
    {g : Ω → ℝ → ℝ} {T : ℝ}
    (hHm : ∀ m, Measurable (Function.uncurry (H m)))
    (hH₀m : Measurable (Function.uncurry H₀)) (hgm : Measurable (Function.uncurry g))
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ‖H m ω s‖ ≤ g ω s)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
        (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) atTop (𝓝 0) := by
  set bound : Ω → ℝ≥0∞ :=
    fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume with hbound
  have hgsq : Measurable (Function.uncurry fun ω s => 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2) :=
    measurable_const.mul (hgm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hFm : ∀ m, Measurable
      (Function.uncurry fun ω s => (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2) :=
    fun m => (((hHm m).sub hH₀m).nnnorm.coe_nnreal_ennreal).pow_const 2
  have hboundm : Measurable bound := hgsq.lintegral_prod_right'
  have hboundfin : ∫⁻ ω, bound ω ∂P ≠ ⊤ := by
    have hswap : ∫⁻ ω, bound ω ∂P
        = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
      rw [← MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)]
      exact MeasureTheory.lintegral_congr fun ω =>
        MeasureTheory.lintegral_const_mul' _ _ (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
    rw [hswap]
    exact ENNReal.mul_ne_top (by norm_num) hg.ne
  -- the pointwise data, gathered on one set of full measure
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)) ∧ ∀ m, ‖H m ω s‖ ≤ g ω s := by
    filter_upwards [hpt, (MeasureTheory.ae_all_iff).2 hdom] with ω hptω hdomω
    filter_upwards [hptω, (MeasureTheory.ae_all_iff).2 hdomω] with s h1 h2
    exact ⟨h1, h2⟩
  -- the limit function inherits the bound, so the difference is dominated by `4 g²`
  have hstep : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ m,
      (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hae] with ω hω
    filter_upwards [hω] with s hs m
    have hlim : ‖H₀ ω s‖ ≤ g ω s :=
      le_of_tendsto hs.1.norm (Filter.Eventually.of_forall fun k => hs.2 k)
    exact sq_enorm_sub_le_of_norm_le (hs.2 m) hlim
  -- the inner limit, for almost every sample point
  have hinner : ∀ᵐ ω ∂P, Tendsto (fun m => ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H m ω s - H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) atTop (𝓝 0) := by
    filter_upwards [hae, hstep, MeasureTheory.ae_lt_top hboundm hboundfin] with ω hω hstepω hfinω
    refine tendsto_lintegral_of_dominated_tendsto_zero
      (fun s => 4 * (‖g ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun m => (Measurable.of_uncurry_left (hFm m)).aemeasurable) ?_ hfinω.ne ?_
    · exact fun m => by filter_upwards [hstepω] with s hs using hs m
    · filter_upwards [hω] with s hs using tendsto_sq_enorm_sub hs.1
  refine tendsto_lintegral_of_dominated_tendsto_zero bound
    (fun m => (hFm m).lintegral_prod_right'.aemeasurable) ?_ hboundfin hinner
  intro m
  filter_upwards [hstep] with ω hω
  exact MeasureTheory.lintegral_mono_ae (by filter_upwards [hω] with s hs using hs m)

end Unmarked

section Marked

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} [SigmaFinite ν]

/-- A section in the sample point of a jointly measurable nonnegative marked kernel has a
measurable mark integral. -/
theorem measurable_section_markLIntegral {f : Ω → ℝ → E → ℝ≥0∞}
    (hf : Measurable fun p : Ω × ℝ × E => f p.1 p.2.1 p.2.2) (ω : Ω) :
    Measurable fun s => ∫⁻ e, f ω s e ∂ν := by
  have hcurry : Measurable fun q : ℝ × E => f ω q.1 q.2 :=
    hf.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  exact hcurry.lintegral_prod_right'

/-- Along a sequence of marked integrands converging pointwise almost everywhere and dominated
by a square-integrable function, the energy of the difference to the limit over `P ⊗ ds ⊗ ν`
vanishes. -/
theorem tendsto_lintegral_sq_sub_mark_of_dominated {φ : ℕ → Ω → ℝ → E → ℝ}
    {φ₀ : Ω → ℝ → E → ℝ} {g : Ω → ℝ → E → ℝ} {T : ℝ}
    (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
    (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
    (hgm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖φ m ω s e‖ ≤ g ω s e)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) atTop (𝓝 0) := by
  have h4 : (4 : ℝ≥0∞) ≠ ⊤ := by norm_num
  have hgsq : Measurable fun p : Ω × ℝ × E => 4 * (‖g p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    measurable_const.mul (hgm.nnnorm.coe_nnreal_ennreal.pow_const 2)
  have hFm : ∀ m, Measurable fun p : Ω × ℝ × E =>
      (‖φ m p.1 p.2.1 p.2.2 - φ₀ p.1 p.2.1 p.2.2‖₊ : ℝ≥0∞) ^ 2 :=
    fun m => (((hφm m).sub hφ₀m).nnnorm.coe_nnreal_ennreal).pow_const 2
  set bound : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume with hbounddef
  have hboundm : Measurable bound :=
    LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2) hgsq T
  have hboundval : ∀ ω, bound ω
      = 4 * ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e, (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume := by
    intro ω
    rw [hbounddef, ← MeasureTheory.lintegral_const_mul' _ _ h4]
    exact MeasureTheory.lintegral_congr fun s => MeasureTheory.lintegral_const_mul' _ _ h4
  have hboundfin : ∫⁻ ω, bound ω ∂P ≠ ⊤ := by
    have hswap : ∫⁻ ω, bound ω ∂P = 4 * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
      simp_rw [hboundval]
      exact MeasureTheory.lintegral_const_mul' _ _ h4
    rw [hswap]
    exact ENNReal.mul_ne_top h4 hg.ne
  -- the pointwise data, gathered on one set of full measure
  have hae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)) ∧ ∀ m, ‖φ m ω s e‖ ≤ g ω s e := by
    filter_upwards [hpt, (MeasureTheory.ae_all_iff).2 hdom] with ω hptω hdomω
    filter_upwards [hptω, (MeasureTheory.ae_all_iff).2 hdomω] with s hpts hdoms
    filter_upwards [hpts, (MeasureTheory.ae_all_iff).2 hdoms] with e h1 h2
    exact ⟨h1, h2⟩
  -- the limit integrand inherits the bound, so the difference is dominated by `4 g²`
  have hstep : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν, ∀ m,
      (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ≤ 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 := by
    filter_upwards [hae] with ω hω
    filter_upwards [hω] with s hs
    filter_upwards [hs] with e he m
    have hlim : ‖φ₀ ω s e‖ ≤ g ω s e :=
      le_of_tendsto he.1.norm (Filter.Eventually.of_forall fun k => he.2 k)
    exact sq_enorm_sub_le_of_norm_le (he.2 m) hlim
  -- the mark integral vanishes at almost every sample point and time
  have hmark : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => ∫⁻ e, (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) atTop (𝓝 0) := by
    filter_upwards [hae, hstep, MeasureTheory.ae_lt_top hboundm hboundfin] with ω hω hstepω hfinω
    have hsfin : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
        (∫⁻ e, 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν) < ⊤ :=
      MeasureTheory.ae_lt_top (measurable_section_markLIntegral
        (f := fun ω s e => 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2) hgsq ω) hfinω.ne
    filter_upwards [hω, hstepω, hsfin] with s hs hsteps hfins
    refine tendsto_lintegral_of_dominated_tendsto_zero
      (fun e => 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2) (fun m => ?_) ?_ hfins.ne ?_
    · have hcurry : Measurable fun e => (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 :=
        (hFm m).comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      exact hcurry.aemeasurable
    · exact fun m => by filter_upwards [hsteps] with e he using he m
    · filter_upwards [hs] with e he using tendsto_sq_enorm_sub he.1
  -- the time integral vanishes at almost every sample point
  have hinner : ∀ᵐ ω ∂P, Tendsto (fun m => ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume) atTop (𝓝 0) := by
    filter_upwards [hmark, hstep, MeasureTheory.ae_lt_top hboundm hboundfin] with ω hω hstepω hfinω
    refine tendsto_lintegral_of_dominated_tendsto_zero
      (fun s => ∫⁻ e, 4 * (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν)
      (fun m => (measurable_section_markLIntegral
        (f := fun ω s e => (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2) (hFm m) ω).aemeasurable)
      ?_ hfinω.ne hω
    intro m
    filter_upwards [hstepω] with s hs
    exact MeasureTheory.lintegral_mono_ae (by filter_upwards [hs] with e he using he m)
  refine tendsto_lintegral_of_dominated_tendsto_zero bound (fun m => ?_) ?_ hboundfin hinner
  · exact (LevyStochCalc.Poisson.Compensated.measurable_markEnergy
      (f := fun ω s e => (‖φ m ω s e - φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2) (hFm m) T).aemeasurable
  · intro m
    filter_upwards [hstep] with ω hω
    refine MeasureTheory.lintegral_mono_ae ?_
    filter_upwards [hω] with s hs
    exact MeasureTheory.lintegral_mono_ae (by filter_upwards [hs] with e he using he m)

end Marked

section Subsequence

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}

/-- Almost-everywhere convergence along indices `ms` with `i ≤ ms i` can be rearranged into
almost-everywhere convergence along a strictly monotone reindexing. -/
theorem exists_strictMono_ae_tendsto {u : ℕ → Ω → ℝ} {v : Ω → ℝ} {ms : ℕ → ℕ}
    (hms : ∀ i : ℕ, i ≤ ms i)
    (h : ∀ᵐ ω ∂P, Tendsto (fun i => u (ms i) ω) atTop (𝓝 (v ω))) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧
      ∀ᵐ ω ∂P, Tendsto (fun i => u (k i) ω) atTop (𝓝 (v ω)) := by
  let n : ℕ → ℕ := fun i => Nat.rec (motive := fun _ => ℕ) 0 (fun _ j => ms j + 1) i
  have hnsucc : ∀ i : ℕ, n (i + 1) = ms (n i) + 1 := fun _ => rfl
  have hnge : ∀ i : ℕ, i ≤ n i := by
    intro i
    induction i with
    | zero => exact Nat.zero_le _
    | succ j ih =>
      have h1 := hms (n j)
      rw [hnsucc]
      omega
  have hnmono : StrictMono n := strictMono_nat_of_lt_succ fun i => by
    have h1 := hms (n i)
    rw [hnsucc]
    omega
  refine ⟨fun i => ms (n i), strictMono_nat_of_lt_succ fun i => ?_, fun i => ?_, ?_⟩
  · have h1 := hms (n (i + 1))
    have h2 := hnsucc i
    omega
  · exact le_trans (hnge i) (hms (n i))
  · filter_upwards [h] with ω hω
    exact hω.comp (Filter.tendsto_atTop_mono hnge Filter.tendsto_id)

end Subsequence

section Brownian

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Brownian.IsBrownianFiltration W ℱ)
  (H : ℕ → Ω → ℝ → ℝ) (H₀ : Ω → ℝ → ℝ) (g : Ω → ℝ → ℝ)
  (hHm : ∀ m, Measurable (Function.uncurry (H m)))
  (hHp : ∀ m, Probability.ProgressivelyMeasurable ℱ (H m))
  (hHq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H m ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
  (hH₀m : Measurable (Function.uncurry H₀))
  (hH₀p : Probability.ProgressivelyMeasurable ℱ H₀)
  (hH₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
    (‖H₀ ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)

include hℱ in
/-- The Itô integrals of a sequence of admissible integrands converging pointwise almost
everywhere and dominated by a square-integrable function converge in `L²`. -/
theorem tendsto_lintegral_sq_stochasticIntegralBrownian_of_dominated
    (hgm : Measurable (Function.uncurry g)) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ‖H m ω s‖ ≤ g ω s)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω,
        (‖Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (H m) (hHm m) (hHp m) (hHq m) T ω
          - Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₀ hH₀m hH₀p hH₀q T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) :=
  Brownian.Ito.tendsto_lintegral_sq_stochInt_of_tendsto_energy W ℱ hℱ H H₀ hHm hHp hHq
    hH₀m hH₀p hH₀q hT
    (tendsto_lintegral_sq_sub_of_dominated hHm hH₀m hgm hpt hdom hg)

include hℱ in
/-- The Itô integrals of a sequence of admissible integrands converging pointwise almost
everywhere and dominated by a square-integrable function converge almost surely along a strictly
monotone subsequence. -/
theorem exists_seq_ae_tendsto_stochasticIntegralBrownian_of_dominated
    (hgm : Measurable (Function.uncurry g)) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Tendsto (fun m => H m ω s) atTop (𝓝 (H₀ ω s)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ‖H m ω s‖ ≤ g ω s)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖g ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧ ∀ᵐ ω ∂P, Tendsto
      (fun m => Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (H (k m))
        (hHm (k m)) (hHp (k m)) (hHq (k m)) T ω) atTop
      (𝓝 (Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₀ hH₀m hH₀p hH₀q T ω)) := by
  obtain ⟨ms, hmsge, hms⟩ :=
    Brownian.Ito.exists_seq_ae_tendsto_stochInt_of_tendsto_energy (ι := Unit)
      (fun _ => W) ℱ (fun _ => hℱ) (fun m _ => H m) (fun _ => H₀) (fun m _ => hHm m)
      (fun m _ => hHp m) (fun m _ => hHq m) (fun _ => hH₀m) (fun _ => hH₀p) (fun _ => hH₀q) hT
      fun _ => tendsto_lintegral_sq_sub_of_dominated hHm hH₀m hgm hpt hdom hg
  refine exists_strictMono_ae_tendsto (P := P)
    (u := fun j ω => Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ (H j)
      (hHm j) (hHp j) (hHq j) T ω)
    (v := fun ω => Brownian.Ito.stochasticIntegralBrownian W ℱ hℱ H₀ hH₀m hH₀p hH₀q T ω)
    hmsge ?_
  filter_upwards [hms] with ω hω
  exact hω ()

end Brownian

section Compensated

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : ℕ → Ω → ℝ → E → ℝ) (φ₀ : Ω → ℝ → E → ℝ) (g : Ω → ℝ → E → ℝ)
  (hφm : ∀ m, Measurable fun p : Ω × ℝ × E => φ m p.1 p.2.1 p.2.2)
  (hφp : ∀ m, Probability.MarkedProgressivelyMeasurable ℱ (φ m))
  (hφq : ∀ (m : ℕ) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ m ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (hφ₀m : Measurable fun p : Ω × ℝ × E => φ₀ p.1 p.2.1 p.2.2)
  (hφ₀p : Probability.MarkedProgressivelyMeasurable ℱ φ₀)
  (hφ₀q : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
    (‖φ₀ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- The compensated Itô–Lévy integrals of a sequence of admissible marked integrands converging
pointwise almost everywhere and dominated by a square-integrable function converge in `L²`. -/
theorem tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated
    (hgm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖φ m ω s e‖ ≤ g ω s e)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    Tendsto (fun m => ∫⁻ ω,
        (‖stochasticIntegral N ℱ hℱ (φ m) (hφm m) (hφp m) (hφq m) T ω
          - stochasticIntegral N ℱ hℱ φ₀ hφ₀m hφ₀p hφ₀q T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) :=
  (tendsto_lintegral_sq_sub_mark_of_dominated hφm hφ₀m hgm hpt hdom hg).congr fun m =>
    (itoIsometry_diff_compensated N ℱ hℱ (φ m) φ₀ (hφm m) hφ₀m (hφp m) hφ₀p
      (hφq m) hφ₀q T hT).symm

include hℱ in
/-- The compensated Itô–Lévy integrals of a sequence of admissible marked integrands converging
pointwise almost everywhere and dominated by a square-integrable function converge almost surely
along a strictly monotone subsequence. -/
theorem exists_seq_ae_tendsto_compensatedStochasticIntegral_of_dominated
    (hgm : Measurable fun p : Ω × ℝ × E => g p.1 p.2.1 p.2.2) {T : ℝ} (hT : 0 < T)
    (hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => φ m ω s e) atTop (𝓝 (φ₀ ω s e)))
    (hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖φ m ω s e‖ ≤ g ω s e)
    (hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖g ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧ ∀ᵐ ω ∂P, Tendsto
      (fun m => stochasticIntegral N ℱ hℱ (φ (k m)) (hφm (k m)) (hφp (k m)) (hφq (k m)) T ω)
      atTop (𝓝 (stochasticIntegral N ℱ hℱ φ₀ hφ₀m hφ₀p hφ₀q T ω)) := by
  have hmeas : ∀ (ψ : Ω → ℝ → E → ℝ)
      (hm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      (hp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
      (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      Measurable (stochasticIntegral N ℱ hℱ ψ hm hp hq T) := fun ψ hm hp hq =>
    ((stochasticIntegral_adapted N ℱ hℱ ψ hm hp hq T).stronglyMeasurable).measurable.mono
      (ℱ.rightCont.le T) le_rfl
  obtain ⟨ms, hmsge, hms⟩ := Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral
    (μ := P) (ι := Unit)
    (u := fun m _ ω => stochasticIntegral N ℱ hℱ (φ m) (hφm m) (hφp m) (hφq m) T ω)
    (v := fun _ ω => stochasticIntegral N ℱ hℱ φ₀ hφ₀m hφ₀p hφ₀q T ω)
    (fun m _ => hmeas _ _ _ _) (fun _ => hmeas _ _ _ _)
    fun _ => tendsto_lintegral_sq_compensatedStochasticIntegral_of_dominated N ℱ hℱ φ φ₀ g
      hφm hφp hφq hφ₀m hφ₀p hφ₀q hgm hT hpt hdom hg
  refine exists_strictMono_ae_tendsto (P := P)
    (u := fun j ω => stochasticIntegral N ℱ hℱ (φ j) (hφm j) (hφp j) (hφq j) T ω)
    (v := fun ω => stochasticIntegral N ℱ hℱ φ₀ hφ₀m hφ₀p hφ₀q T ω) hmsge ?_
  filter_upwards [hms] with ω hω
  exact hω ()

end Compensated

section MarkCut

open LevyStochCalc.Poisson.Compensated

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : Poisson.IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable fun p : Ω × ℝ × E => φ p.1 p.2.1 p.2.2)
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
    (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
  (A : ℕ → Set E) (hA : ∀ m, MeasurableSet (A m))

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- The mark cut to the complement of a set differs from the integrand by the mark cut to the
set itself. -/
theorem markCut_compl_sub (S : Set E) (ψ : Ω → ℝ → E → ℝ) (ω : Ω) (s : ℝ) (e : E) :
    markCut Sᶜ ψ ω s e - ψ ω s e = -markCut S ψ ω s e := by
  by_cases h : e ∈ S <;> simp [markCut, h]

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] [SigmaFinite ν] in
/-- An antitone family of mark sets whose intersection is null eventually misses almost every
mark. -/
theorem ae_eventually_notMem_of_antitone (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0) :
    ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m := by
  have hset : {a : E | ¬ (a ∉ ⋂ m, A m)} = ⋂ m, A m := by
    ext a
    simp
  have hae : ∀ᵐ e ∂ν, e ∉ ⋂ m, A m := by
    rw [MeasureTheory.ae_iff, hset]
    exact hnull
  filter_upwards [hae] with e he
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, e ∉ A m₀ := by
    by_contra hcon
    exact he (Set.mem_iInter.mpr fun m => not_not.mp fun h => hcon ⟨m, h⟩)
  filter_upwards [Filter.eventually_ge_atTop m₀] with m hm
  exact fun hmem => hm₀ (hanti hm hmem)

include hℱ in
/-- The compensated Itô–Lévy integrals of an integrand cut to the complements of a family of
mark sets that eventually misses almost every mark converge in `L²` to the compensated
Itô–Lévy integral of the integrand. -/
theorem tendsto_lintegral_sq_stochasticIntegral_markCut_compl
    (hout : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m)ᶜ φ)
          (measurable_markCut h_meas (hA m).compl) (h_progMeas.indicator_mark (hA m).compl)
          (fun T' hT' => sq_markCut h_sq (A m)ᶜ T' hT') T ω
        - stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) := by
  have hmcut : ∀ m, Measurable fun p : Ω × ℝ × E => markCut (A m)ᶜ φ p.1 p.2.1 p.2.2 :=
    fun m => measurable_markCut h_meas (hA m).compl
  have hgm : Measurable fun p : Ω × ℝ × E => ‖φ p.1 p.2.1 p.2.2‖ := h_meas.norm
  have hpt : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      Tendsto (fun m => markCut (A m)ᶜ φ ω s e) atTop (𝓝 (φ ω s e)) := by
    refine Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun s => ?_
    filter_upwards [hout] with e he
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [he] with m hm
    simp [markCut, hm]
  have hdom : ∀ m, ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)), ∀ᵐ e ∂ν,
      ‖markCut (A m)ᶜ φ ω s e‖ ≤ ‖φ ω s e‖ := by
    intro m
    refine Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun s =>
      Filter.Eventually.of_forall fun e => ?_
    rcases Classical.em (e ∈ A m) with hm | hm
    · have hz : markCut (A m)ᶜ φ ω s e = 0 := by simp [markCut, hm]
      rw [hz, norm_zero]
      exact norm_nonneg _
    · have hid : markCut (A m)ᶜ φ ω s e = φ ω s e := by simp [markCut, hm]
      rw [hid]
  have hg : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖‖φ ω s e‖‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤ := by
    simpa using h_sq T hT
  refine (tendsto_lintegral_sq_sub_mark_of_dominated (φ := fun m => markCut (A m)ᶜ φ)
    (φ₀ := φ) (g := fun ω s e => ‖φ ω s e‖) hmcut h_meas hgm hpt hdom hg).congr fun m => ?_
  exact (itoIsometry_diff_compensated N ℱ hℱ (markCut (A m)ᶜ φ) φ (hmcut m) h_meas
    (h_progMeas.indicator_mark (hA m).compl) h_progMeas
    (fun T' hT' => sq_markCut h_sq (A m)ᶜ T' hT') h_sq T hT).symm

include hℱ in
/-- The compensated Itô–Lévy integrals of an integrand cut to the complements of an antitone
family of mark sets whose intersection is null converge in `L²` to the compensated Itô–Lévy
integral of the integrand. -/
theorem tendsto_lintegral_sq_stochasticIntegral_markCut_compl_of_antitone
    (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun m => ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ (markCut (A m)ᶜ φ)
          (measurable_markCut h_meas (hA m).compl) (h_progMeas.indicator_mark (hA m).compl)
          (fun T' hT' => sq_markCut h_sq (A m)ᶜ T' hT') T ω
        - stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω‖₊ : ℝ≥0∞) ^ 2 ∂P)
      atTop (𝓝 0) :=
  tendsto_lintegral_sq_stochasticIntegral_markCut_compl N ℱ hℱ φ h_meas h_progMeas h_sq A hA
    (ae_eventually_notMem_of_antitone A hanti hnull) hT

include hℱ in
/-- The compensated Itô–Lévy integrals of an integrand cut to the complements of a family of
mark sets that eventually misses almost every mark converge almost surely along a strictly
monotone subsequence to the compensated Itô–Lévy integral of the integrand. -/
theorem exists_seq_ae_tendsto_stochasticIntegral_markCut_compl
    (hout : ∀ᵐ e ∂ν, ∀ᶠ m in atTop, e ∉ A m) {T : ℝ} (hT : 0 < T) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧ ∀ᵐ ω ∂P, Tendsto
      (fun m => stochasticIntegral N ℱ hℱ (markCut (A (k m))ᶜ φ)
        (measurable_markCut h_meas (hA (k m)).compl)
        (h_progMeas.indicator_mark (hA (k m)).compl)
        (fun T' hT' => sq_markCut h_sq (A (k m))ᶜ T' hT') T ω) atTop
      (𝓝 (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω)) := by
  have hmeas : ∀ (ψ : Ω → ℝ → E → ℝ)
      (hm : Measurable fun p : Ω × ℝ × E => ψ p.1 p.2.1 p.2.2)
      (hp : Probability.MarkedProgressivelyMeasurable ℱ ψ)
      (hq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
        (‖ψ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
      Measurable (stochasticIntegral N ℱ hℱ ψ hm hp hq T) := fun ψ hm hp hq =>
    ((stochasticIntegral_adapted N ℱ hℱ ψ hm hp hq T).stronglyMeasurable).measurable.mono
      (ℱ.rightCont.le T) le_rfl
  obtain ⟨ms, hmsge, hms⟩ := Brownian.Ito.exists_seq_ae_tendsto_of_tendsto_lintegral
    (μ := P) (ι := Unit)
    (u := fun m _ ω => stochasticIntegral N ℱ hℱ (markCut (A m)ᶜ φ)
      (measurable_markCut h_meas (hA m).compl) (h_progMeas.indicator_mark (hA m).compl)
      (fun T' hT' => sq_markCut h_sq (A m)ᶜ T' hT') T ω)
    (v := fun _ ω => stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω)
    (fun m _ => hmeas _ _ _ _) (fun _ => hmeas _ _ _ _)
    fun _ => tendsto_lintegral_sq_stochasticIntegral_markCut_compl N ℱ hℱ φ h_meas h_progMeas
      h_sq A hA hout hT
  refine exists_strictMono_ae_tendsto (P := P)
    (u := fun j ω => stochasticIntegral N ℱ hℱ (markCut (A j)ᶜ φ)
      (measurable_markCut h_meas (hA j).compl) (h_progMeas.indicator_mark (hA j).compl)
      (fun T' hT' => sq_markCut h_sq (A j)ᶜ T' hT') T ω)
    (v := fun ω => stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω) hmsge ?_
  filter_upwards [hms] with ω hω
  exact hω ()

include hℱ in
/-- The compensated Itô–Lévy integrals of an integrand cut to the complements of an antitone
family of mark sets whose intersection is null converge almost surely along a strictly monotone
subsequence to the compensated Itô–Lévy integral of the integrand. -/
theorem exists_seq_ae_tendsto_stochasticIntegral_markCut_compl_of_antitone
    (hanti : Antitone A) (hnull : ν (⋂ m, A m) = 0) {T : ℝ} (hT : 0 < T) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ (∀ i : ℕ, i ≤ k i) ∧ ∀ᵐ ω ∂P, Tendsto
      (fun m => stochasticIntegral N ℱ hℱ (markCut (A (k m))ᶜ φ)
        (measurable_markCut h_meas (hA (k m)).compl)
        (h_progMeas.indicator_mark (hA (k m)).compl)
        (fun T' hT' => sq_markCut h_sq (A (k m))ᶜ T' hT') T ω) atTop
      (𝓝 (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq T ω)) :=
  exists_seq_ae_tendsto_stochasticIntegral_markCut_compl N ℱ hℱ φ h_meas h_progMeas h_sq A hA
    (ae_eventually_notMem_of_antitone A hanti hnull) hT

end MarkCut

end LevyStochCalc.Ito.IntegralLimit
