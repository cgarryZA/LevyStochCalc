/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.BSDEJ.GeneratorAlongMarkStep
import LevyStochCalc.BSDEJ.GeneratorEnergy
import LevyStochCalc.Poisson.CompensatedApprox

/-!
# A progressively measurable version of the generator along a triple of processes

A generator `f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ` that is measurable in `(s, y, z)` for each
fixed jump variable and Lipschitz in `(y, z, u)` for the `L²(ν)` distance on the jump variable is
not assumed measurable in the jump variable, so the composite `(ω, s) ↦ f s (Y s ω) (Z s ω)
(U s ω)` along a triple of processes need not be measurable. Approximating the marked process `U`
in `L²` by mark-step integrands makes the composite the pointwise limit, along a subsequence and
almost everywhere on `Ω × [0, T]`, of the jointly and progressively measurable processes obtained
by evaluating the generator along the approximants; the pointwise `limsup` of that subsequence is
then a progressively measurable process of finite energy, vanishing off the horizon, which agrees
with the composite almost everywhere.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace LevyStochCalc.BSDEJ.Generator

open LevyStochCalc.Poisson.Compensated

universe u v

/-! ### Almost everywhere convergence from summable integrals -/

/-- The geometric series of ratio `2⁻¹` in `ℝ≥0∞` is finite. -/
theorem tsum_geometric_two_inv_ne_top : ∑' i : ℕ, ((2 : ℝ≥0∞)⁻¹) ^ i ≠ ⊤ := by
  rw [ENNReal.tsum_geometric]
  refine ENNReal.inv_ne_top.2 ?_
  rw [Ne, tsub_eq_zero_iff_le]
  exact not_le.mpr (ENNReal.inv_lt_one.mpr (by norm_num))

/-- A sequence in `ℝ≥0∞` tending to zero has a subsequence dominated by the geometric sequence
of ratio `2⁻¹`. -/
theorem exists_subseq_lt_geometric {u : ℕ → ℝ≥0∞} (h : Tendsto u atTop (𝓝 0)) :
    ∃ ms : ℕ → ℕ, (∀ i : ℕ, i ≤ ms i) ∧ ∀ i : ℕ, u (ms i) < ((2 : ℝ≥0∞)⁻¹) ^ i := by
  have hchoice : ∀ i : ℕ, ∃ j : ℕ, i ≤ j ∧ u j < ((2 : ℝ≥0∞)⁻¹) ^ i := by
    intro i
    have hpos : (0 : ℝ≥0∞) < ((2 : ℝ≥0∞)⁻¹) ^ i :=
      pos_iff_ne_zero.mpr (pow_ne_zero i (by simp))
    obtain ⟨n, hn⟩ := eventually_atTop.mp (h.eventually (gt_mem_nhds hpos))
    exact ⟨max n i, le_max_right n i, hn (max n i) (le_max_left n i)⟩
  choose ms hge hms using hchoice
  exact ⟨ms, hge, hms⟩

/-- Nonnegative measurable functions with summable integrals tend to zero almost everywhere. -/
theorem ae_tendsto_zero_of_tsum_lintegral_ne_top {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : ℕ → α → ℝ≥0∞} (hg : ∀ i, Measurable (g i))
    (hsum : ∑' i : ℕ, ∫⁻ a, g i a ∂μ ≠ ⊤) :
    ∀ᵐ a ∂μ, Tendsto (fun i => g i a) atTop (𝓝 0) := by
  have h1 : ∫⁻ a, ∑' i : ℕ, g i a ∂μ ≠ ⊤ := by
    rw [lintegral_tsum fun i => (hg i).aemeasurable]
    exact hsum
  filter_upwards [ae_lt_top (Measurable.tsum hg) h1] with a ha
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top ha.ne

/-- A real sequence whose extended distance to a point is dominated by a sequence tending to
zero converges to that point. -/
theorem tendsto_of_enorm_sub_le {u : ℕ → ℝ} {w : ℝ} {c : ℕ → ℝ≥0∞}
    (hle : ∀ i, (‖w - u i‖₊ : ℝ≥0∞) ≤ c i) (hc : Tendsto c atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 w) := by
  have h0 : Tendsto (fun i => ((‖w - u i‖₊ : ℝ≥0) : ℝ≥0∞)) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le) hle
  have h1 : Tendsto (fun i => ‖w - u i‖₊) atTop (𝓝 0) := by
    rw [← ENNReal.tendsto_coe]
    simpa using h0
  have h2 : Tendsto (fun i => ‖w - u i‖) atTop (𝓝 0) := by
    simpa using NNReal.tendsto_coe.2 h1
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hrw : (fun i => ‖w - u i‖) = fun i => ‖u i - w‖ := funext fun i => norm_sub_rev _ _
  rwa [hrw] at h2

/-! ### The generator along a triple of processes -/

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} {ν : Measure E} {d : ℕ}
  {f : ℝ → ℝ → (Fin d → ℝ) → (E → ℝ) → ℝ} {L : ℝ}

/-- A generator Lipschitz in the state variables is, at fixed time and fixed `(y, z)`, Lipschitz
in the jump variable for the `L²(ν)` distance. -/
theorem enorm_sub_generator_jump_le
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)))
    (s y : ℝ) (z : Fin d → ℝ) (u₁ u₂ : E → ℝ) :
    (‖f s y z u₁ - f s y z u₂‖₊ : ℝ≥0∞)
      ≤ ENNReal.ofReal L * (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ) := by
  have key := hlip s y y z z u₁ u₂
  simp only [sub_self, nnnorm_zero, ENNReal.coe_zero, zero_add] at key
  exact key

variable [IsProbabilityMeasure P] [SigmaFinite ν] {Y : ℝ → Ω → ℝ} {Z : ℝ → Ω → (Fin d → ℝ)}
  {U : ℝ → Ω → E → ℝ}

/-- A generator measurable in `(s, y, z)` for each jump variable and Lipschitz in `(y, z, u)`,
evaluated along progressively measurable processes of finite energy, has a jointly and
progressively measurable version of finite energy that vanishes off the horizon. -/
theorem exists_progressive_generator_modification (N : Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ mΩ)
    (hf : ∀ u : E → ℝ, Measurable fun p : ℝ × ℝ × (Fin d → ℝ) => f p.1 p.2.1 p.2.2 u)
    (hlip : ∀ (s y₁ y₂ : ℝ) (z₁ z₂ : Fin d → ℝ) (u₁ u₂ : E → ℝ),
      (‖f s y₁ z₁ u₁ - f s y₂ z₂ u₂‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L *
        ((‖y₁ - y₂‖₊ : ℝ≥0∞) + (‖z₁ - z₂‖₊ : ℝ≥0∞)
          + (∫⁻ e, (‖u₁ e - u₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ))) {T : ℝ} (hT : 0 < T)
    (hf0 : ∫⁻ s in Set.Icc (0 : ℝ) T, (‖f s 0 0 0‖₊ : ℝ≥0∞) ^ 2 < ⊤)
    (hYm : Measurable (Function.uncurry Y))
    (hYp : Probability.ProgressivelyMeasurable ℱ fun ω s => Y s ω)
    (hY : Brownian.Ito.energy P T (fun ω s => Y s ω) ≠ ⊤)
    (hZm : ∀ i, Measurable (Function.uncurry fun ω s => Z s ω i))
    (hZp : ∀ i, Probability.ProgressivelyMeasurable ℱ fun ω s => Z s ω i)
    (hZ : ∀ i, Brownian.Ito.energy P T (fun ω s => Z s ω i) ≠ ⊤)
    (hUm : Measurable fun p : Ω × ℝ × E => U p.2.1 p.1 p.2.2)
    (hUp : Probability.MarkedProgressivelyMeasurable ℱ fun ω s e => U s ω e)
    (hUq : ∀ T' : ℝ, 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
      (‖U s ω e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤) :
    ∃ b : Ω → ℝ → ℝ, Measurable (Function.uncurry b)
      ∧ Probability.ProgressivelyMeasurable ℱ b
      ∧ (∀ ω s, s ∉ Set.Icc (0 : ℝ) T → b ω s = 0)
      ∧ Brownian.Ito.energy P T b ≠ ⊤
      ∧ ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
          b p.1 p.2 = f p.2 (Y p.2 p.1) (Z p.2 p.1) (U p.2 p.1) := by
  classical
  obtain ⟨G, hGad, hGerr⟩ : ∃ G : ∀ n : ℕ, Σ ℓ : ℕ,
      MarkStep Ω E ν (TimeGrid.dyadic (stageHorizon n) (stageHorizon_pos n) ℓ),
      (∀ n, (G n).2.Adapted ℱ) ∧
        ∀ n, stageErr (fun ω s e => U s ω e) P n (G n).2 < ((n : ℝ≥0∞) + 1)⁻¹ :=
    ⟨master N ℱ (fun ω s e => U s ω e) hUm hUp hUq,
      master_adapted N ℱ (fun ω s e => U s ω e) hUm hUp hUq,
      master_err N ℱ (fun ω s e => U s ω e) hUm hUp hUq⟩
  set W : Ω → ℝ → ℝ := fun ω s =>
    Set.indicator (Set.Icc (0 : ℝ) T) (fun s => f s (Y s ω) (Z s ω) (U s ω)) s with hWdef
  set g : ℕ → Ω × ℝ → ℝ≥0∞ := fun n p =>
    ∫⁻ e, (‖U p.2 p.1 e - (G n).2.eval p.2 e p.1‖₊ : ℝ≥0∞) ^ 2 ∂ν with hgdef
  have hswap : Measurable fun q : (Ω × ℝ) × E => ((q.1.1, q.1.2, q.2) : Ω × ℝ × E) :=
    (measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hgm : ∀ n, Measurable (g n) := by
    intro n
    have h1 : Measurable fun q : (Ω × ℝ) × E => U q.1.2 q.1.1 q.2 := hUm.comp hswap
    have h2 : Measurable fun q : (Ω × ℝ) × E => (G n).2.eval q.1.2 q.2 q.1.1 :=
      (G n).2.eval_measurable.comp hswap
    exact (((h1.sub h2).nnnorm.coe_nnreal_ennreal).pow_const 2).lintegral_prod_right'
  have hgle : ∀ n, T ≤ stageHorizon n →
      ∫⁻ p, g n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))) ≤ ((n : ℝ≥0∞) + 1)⁻¹ := by
    intro n hn
    refine le_of_lt (lt_of_le_of_lt ?_ (hGerr n))
    rw [lintegral_prod _ (hgm n).aemeasurable]
    exact lintegral_mono fun ω => lintegral_mono_set (Set.Icc_subset_Icc_right hn)
  obtain ⟨N₀, hN₀⟩ : ∃ N₀ : ℕ, T ≤ stageHorizon N₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt T (one_lt_two : (1 : ℝ) < 2)
    exact ⟨k, hk.le⟩
  have htend : Tendsto
      (fun n => ∫⁻ p, g n p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => ((n : ℝ≥0∞) + 1)⁻¹) atTop (𝓝 0) := by
      have h := ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
      refine h.congr fun n => ?_
      simp [Function.comp]
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv
      (Eventually.of_forall fun _ => bot_le) (eventually_atTop.2 ⟨N₀, fun n hn => ?_⟩)
    exact hgle n (hN₀.trans (stageHorizon_mono hn))
  obtain ⟨ms, -, hmslt⟩ := exists_subseq_lt_geometric htend
  have hsum : ∑' i : ℕ, ∫⁻ p, g (ms i) p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
      ≠ ⊤ :=
    ne_top_of_le_ne_top tsum_geometric_two_inv_ne_top
      (ENNReal.tsum_le_tsum fun i => (hmslt i).le)
  have hae0 : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Tendsto (fun i => g (ms i) p) atTop (𝓝 0) :=
    ae_tendsto_zero_of_tsum_lintegral_ne_top (fun i => hgm (ms i)) hsum
  obtain ⟨H, hHm, hHp, hHz, hHle⟩ : ∃ H : ℕ → Ω → ℝ → ℝ,
      (∀ n, Measurable (Function.uncurry (H n))) ∧
      (∀ n, Probability.ProgressivelyMeasurable ℱ (H n)) ∧
      (∀ n ω s, s ∉ Set.Icc (0 : ℝ) T → H n ω s = 0) ∧
      ∀ n ω s, s ∈ Set.Icc (0 : ℝ) T →
        (‖W ω s - H n ω s‖₊ : ℝ≥0∞) ≤ ENNReal.ofReal L * g n (ω, s) ^ (1 / 2 : ℝ) := by
    refine ⟨fun n ω s => Set.indicator (Set.Icc (0 : ℝ) T)
      (fun s => f s (Y s ω) (Z s ω) (fun e => (G n).2.eval s e ω)) s, ?_, ?_, ?_, ?_⟩
    · intro n
      have hbase := measurable_generator_along_markStep hf hlip (G n).2 hYm hZm
      have hrw : (Function.uncurry fun ω s => Set.indicator (Set.Icc (0 : ℝ) T)
            (fun s => f s (Y s ω) (Z s ω) (fun e => (G n).2.eval s e ω)) s)
          = {q : Ω × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T}.indicator
            (Function.uncurry fun ω s =>
              f s (Y s ω) (Z s ω) (fun e => (G n).2.eval s e ω)) := by
        funext p
        simp only [Function.uncurry]
        by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
        · rw [Set.indicator_of_mem hp,
            Set.indicator_of_mem (show p ∈ {q : Ω × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T} from hp)]
          rfl
        · rw [Set.indicator_of_notMem hp,
            Set.indicator_of_notMem (show p ∉ {q : Ω × ℝ | q.2 ∈ Set.Icc (0 : ℝ) T} from hp)]
      rw [hrw]
      exact hbase.indicator (measurable_snd measurableSet_Icc)
    · intro n
      exact Brownian.Ito.progressivelyMeasurable_indicator_Icc
        (progressive_generator_along_markStep hf hlip (G n).2 (hGad n) hYp hZp) T
    · intro n ω s hs
      exact Set.indicator_of_notMem hs _
    · intro n ω s hs
      simp only [hWdef, hgdef, Set.indicator_of_mem hs]
      exact enorm_sub_generator_jump_le hlip s (Y s ω) (Z s ω) (U s ω)
        (fun e => (G n).2.eval s e ω)
  have haeW : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
      Brownian.Ito.limsupIntegrand H ms p.1 p.2 = W p.1 p.2 := by
    filter_upwards [hae0] with p hp0
    have hc : Tendsto (fun i => ENNReal.ofReal L * g (ms i) p ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
      have h1 : Tendsto (fun i => g (ms i) p ^ (1 / 2 : ℝ)) atTop (𝓝 0) := by
        have h2 := hp0.ennrpow_const (1 / 2 : ℝ)
        rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h2
      simpa using ENNReal.Tendsto.const_mul h1 (Or.inr ENNReal.ofReal_ne_top)
    have hlim : Tendsto (fun i => H (ms i) p.1 p.2) atTop (𝓝 (W p.1 p.2)) := by
      by_cases hp : p.2 ∈ Set.Icc (0 : ℝ) T
      · exact tendsto_of_enorm_sub_le (fun i => hHle (ms i) p.1 p.2 hp) hc
      · have hW0 : W p.1 p.2 = 0 := by
          simp only [hWdef]
          exact Set.indicator_of_notMem hp _
        have hH0 : ∀ i, H (ms i) p.1 p.2 = 0 := fun i => hHz (ms i) p.1 p.2 hp
        rw [hW0]
        simp only [hH0]
        exact tendsto_const_nhds
    exact hlim.limsup_eq
  have haeW' : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Brownian.Ito.limsupIntegrand H ms ω s = W ω s := Measure.ae_ae_of_ae_prod haeW
  have hWfin : Brownian.Ito.energy P T W ≠ ⊤ := by
    simp only [hWdef]
    exact lintegral_sq_generator_along_indicator_lt_top hlip hf hf0 hYm hY hZm hZ hUm
      (hUq T hT).ne
  refine ⟨Brownian.Ito.limsupIntegrand H ms, Measurable.limsup fun i => hHm (ms i),
    Probability.ProgressivelyMeasurable.limsup fun i => hHp (ms i), ?_, ?_, ?_⟩
  · intro ω s hs
    have h0 : (fun i => H (ms i) ω s) = fun _ => (0 : ℝ) :=
      funext fun i => hHz (ms i) ω s hs
    rw [Brownian.Ito.limsupIntegrand, h0]
    exact limsup_const 0
  · have heq : Brownian.Ito.energy P T (Brownian.Ito.limsupIntegrand H ms)
        = Brownian.Ito.energy P T W := by
      unfold Brownian.Ito.energy
      refine lintegral_congr_ae ?_
      filter_upwards [haeW'] with ω hω
      refine lintegral_congr_ae ?_
      filter_upwards [hω] with s hs
      rw [hs]
    rw [heq]
    exact hWfin
  · have hnull : (P.prod (volume.restrict (Set.Icc (0 : ℝ) T)))
        ((Set.univ : Set Ω) ×ˢ (Set.Icc (0 : ℝ) T)ᶜ) = 0 := by
      rw [Measure.prod_prod, Measure.restrict_apply' measurableSet_Icc,
        Set.compl_inter_self, measure_empty, mul_zero]
    have haeIcc : ∀ᵐ p ∂(P.prod (volume.restrict (Set.Icc (0 : ℝ) T))),
        p.2 ∈ Set.Icc (0 : ℝ) T := by
      rw [ae_iff]
      refine measure_mono_null ?_ hnull
      intro p hp
      exact Set.mem_prod.2 ⟨Set.mem_univ _, hp⟩
    filter_upwards [haeW, haeIcc] with p h1 h2
    rw [h1]
    simp only [hWdef]
    exact Set.indicator_of_mem h2 _

end LevyStochCalc.BSDEJ.Generator
