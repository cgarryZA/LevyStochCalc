/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.ItoFormulaStopped
import LevyStochCalc.Brownian.ItoLocality

/-!
# Itô's formula along a path stopped at an arbitrary stopping time

A stopping time is approximated from above by the stopping times that stop at the first point of
a uniform grid strictly beyond it, which take finitely many values. The horizons clipped at the
approximations converge to the horizon clipped at the stopping time, the integrands cut off at the
approximations converge in the energy of a window to the integrand cut off at the stopping time,
and Itô's formula along the finite-range stopped paths passes to the limit.

## Main statements

* `LevyStochCalc.Brownian.Ito.tendsto_clipTime_gridStop` — the clipped horizons converge.
* `LevyStochCalc.Brownian.Ito.tendsto_energy_stopped_gridStop` — the cut-off integrands converge
  in the energy of the window.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped_general` — the process stopped at a
  stopping time is the vector Itô process of the stopped coefficients.
* `LevyStochCalc.Brownian.Ito.itoFormula_stopped_general` — Itô's formula along the stopped path.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim
open scoped NNReal ENNReal Topology

universe u

section ClipLimit

variable {Ω : Type u}

/-- A horizon clipped at a time that has already been passed lies below the passing time. -/
theorem clipTime_lt_of_lt {σ : Ω → WithTop ℝ} {t s : ℝ} {ω : Ω}
    (h : σ ω < ((s : ℝ) : WithTop ℝ)) : clipTime σ t ω < s := by
  have hne : σ ω ≠ ⊤ := by
    intro hcon
    rw [hcon] at h
    exact absurd h (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hrs : r < s := by
    rw [← hr] at h
    exact_mod_cast h
  rw [clipTime_eq_min hr.symm]
  exact lt_of_le_of_lt (min_le_right _ _) hrs

/-- The grid stopping time takes one of the grid values, or the value `⊤`. -/
theorem gridStop_eq_or_top (τ : Ω → WithTop ℝ) (t : ℝ) (m : ℕ) (ω : Ω) :
    (∃ c ∈ (Finset.range (m + 1)).image (gridPt t m),
        gridStop τ t m ω = ((c : ℝ) : WithTop ℝ)) ∨ gridStop τ t m ω = ⊤ := by
  rw [gridStop]
  rcases gridStopAux_eq τ t m m ω with ⟨j, hj, hje⟩ | hje
  · exact Or.inl ⟨gridPt t m j,
      Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (Nat.lt_succ_of_le hj), rfl⟩, hje⟩
  · exact Or.inr hje

/-- The horizons clipped at the grid stopping times converge to the horizon clipped at the
stopping time. -/
theorem tendsto_clipTime_gridStop (τ : Ω → WithTop ℝ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω) {t : ℝ} (ht : 0 < t) (ω : Ω) :
    Filter.Tendsto (fun m : ℕ => clipTime (gridStop τ t m) t ω) Filter.atTop
      (𝓝 (clipTime τ t ω)) := by
  by_cases hle : ((t : ℝ) : WithTop ℝ) ≤ τ ω
  · have hconst : ∀ m : ℕ, clipTime (gridStop τ t m) t ω = clipTime τ t ω := by
      intro m
      rw [clipTime_of_le (le_trans hle (le_gridStop τ t m ω)), clipTime_of_le hle]
    simp only [hconst]
    exact tendsto_const_nhds
  · rw [not_le] at hle
    have hne : τ ω ≠ ⊤ := by
      intro hcon
      rw [hcon] at hle
      exact absurd hle (by simp)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    have hrt : r < t := by
      rw [← hr] at hle
      exact_mod_cast hle
    have hr0 : 0 ≤ r := by
      have h0 := hτ0 ω
      rw [← hr] at h0
      exact_mod_cast h0
    have hclip : clipTime τ t ω = r := by
      rw [clipTime_eq_min hr.symm, min_eq_right hrt.le]
    rw [hclip]
    refine tendsto_order.2 ⟨fun a ha => Filter.Eventually.of_forall fun m => ?_, fun b hb => ?_⟩
    · refine lt_of_lt_of_le ha ?_
      refine (le_clipTime_iff hrt.le).mp ?_
      rw [hr]
      exact le_gridStop τ t m ω
    · have hrs : r < min b t := lt_min hb hrt
      have hs0 : 0 < min b t := lt_of_le_of_lt hr0 hrs
      have hst : min b t ≤ t := min_le_right _ _
      have hτs : τ ω < ((min b t : ℝ) : WithTop ℝ) := by
        rw [← hr]
        exact_mod_cast hrs
      filter_upwards [eventually_gridStop_lt τ ht ω hs0 hst hτs] with m hm
      exact lt_of_lt_of_le (clipTime_lt_of_lt hm) (min_le_left _ _)

/-- A pointwise limit of strongly measurable vector-valued functions is strongly measurable. -/
theorem stronglyMeasurable_of_tendsto_pi {mΩ : MeasurableSpace Ω} {N : ℕ}
    {F : ℕ → Ω → Fin N → ℝ} {G : Ω → Fin N → ℝ}
    (hF : ∀ i, MeasureTheory.StronglyMeasurable (F i))
    (hlim : ∀ ω, Filter.Tendsto (fun i => F i ω) Filter.atTop (𝓝 (G ω))) :
    MeasureTheory.StronglyMeasurable G :=
  _root_.stronglyMeasurable_of_tendsto Filter.atTop hF (tendsto_pi_nhds.2 hlim)

end ClipLimit

section Energy

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The integrands cut off at the grid stopping times converge, in the energy of the window, to
the integrand cut off at the stopping time. -/
theorem tendsto_energy_stopped_gridStop {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) {t : ℝ} (ht : 0 < t)
    (hq : ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    Filter.Tendsto (fun m : ℕ => ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
        (‖Probability.stopped (gridStop τ t m) H ω s
          - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P) Filter.atTop (𝓝 0) := by
  have hmS : Measurable (Function.uncurry (Probability.stopped τ H)) :=
    Probability.measurable_uncurry_stopped hτ hm
  have hmG : ∀ m : ℕ, Measurable (Function.uncurry (Probability.stopped (gridStop τ t m) H)) :=
    fun m => Probability.measurable_uncurry_stopped (isStoppingTime_gridStop τ hτ t m) hm
  have hptw : ∀ (m : ℕ) (ω : Ω) (s : ℝ),
      (‖Probability.stopped (gridStop τ t m) H ω s
        - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ≤ (‖H ω s‖₊ : ℝ≥0∞) ^ 2 := by
    intro m ω s
    have habs : |Probability.stopped (gridStop τ t m) H ω s - Probability.stopped τ H ω s|
        ≤ |H ω s| := by
      rw [Probability.stopped, Probability.stopped]
      by_cases h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t m ω
      · by_cases h2 : ((s : ℝ) : WithTop ℝ) ≤ τ ω
        · simp [h1, h2]
        · simp [h1, h2]
      · have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := fun hcon =>
          h1 (le_trans hcon (le_gridStop τ t m ω))
        simp [h1, h2]
    have hle : (‖Probability.stopped (gridStop τ t m) H ω s
        - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ≤ (‖H ω s‖₊ : ℝ≥0∞) := by
      refine ENNReal.coe_le_coe.mpr ?_
      rw [← NNReal.coe_le_coe]
      simpa [Real.norm_eq_abs] using habs
    gcongr
  have hbmeas : Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume := measurable_energyDensity hm t
  have hFmeas : ∀ m : ℕ, Measurable fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStop τ t m) H ω s
        - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume :=
    fun m => measurable_energyDensity ((hmG m).sub hmS) t
  have hinner : ∀ᵐ ω ∂P, Filter.Tendsto (fun m : ℕ => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStop τ t m) H ω s
        - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume) Filter.atTop (𝓝 0) := by
    filter_upwards [MeasureTheory.ae_lt_top hbmeas hq.ne] with ω hfin
    have hlims : ∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        Filter.Tendsto (fun m : ℕ =>
          (‖Probability.stopped (gridStop τ t m) H ω s
            - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2) Filter.atTop (𝓝 0) := by
      have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
      filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
        MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
      have hsne : s ≠ 0 := by simpa using hs0
      have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
      by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
      · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun m _ => ?_
        have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t m ω :=
          le_trans hτs (le_gridStop τ t m ω)
        simp [Probability.stopped, h1, hτs]
      · rw [not_le] at hτs
        obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
          (eventually_gridStop_lt τ ht ω hs hsmem.2 hτs)
        refine tendsto_atTop_of_eventually_const (i₀ := N) fun m hmN => ?_
        have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t m ω := not_le.mpr (hN m hmN)
        have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
        simp [Probability.stopped, h1, h2]
    have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
      (μ := volume.restrict (Set.Icc (0 : ℝ) t))
      (F := fun m s => (‖Probability.stopped (gridStop τ t m) H ω s
        - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2)
      (f := fun _ : ℝ => (0 : ℝ≥0∞))
      (bound := fun s => (‖H ω s‖₊ : ℝ≥0∞) ^ 2)
      (fun m => ((((hmG m).sub hmS).comp measurable_prodMk_left).nnnorm.coe_nnreal_ennreal
        ).pow_const 2)
      (fun m => Filter.Eventually.of_forall fun s => hptw m ω s) hfin.ne hlims
    simpa using hconv
  have hconv := MeasureTheory.tendsto_lintegral_of_dominated_convergence
    (F := fun m ω => ∫⁻ s in Set.Icc (0 : ℝ) t,
      (‖Probability.stopped (gridStop τ t m) H ω s
        - Probability.stopped τ H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    (f := fun _ : Ω => (0 : ℝ≥0∞))
    (bound := fun ω => ∫⁻ s in Set.Icc (0 : ℝ) t, (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume)
    hFmeas
    (fun m => Filter.Eventually.of_forall fun ω => lintegral_mono fun s => hptw m ω s)
    hq.ne hinner
  simpa using hconv

end Energy

section StoppedGeneral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ' : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ')

include hcoord in
/-- **The process stopped at a stopping time is the vector Itô process of the coefficients cut
off at that time.** -/
theorem IsVectorItoVersion.stopped_general
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω) :
    IsVectorItoVersion W ℱ' hcoord (fun p k => Probability.stopped τ (H p k))
      (fun p k => Probability.measurable_uncurry_stopped hτ (hHm p k))
      (fun p k => Probability.ProgressivelyMeasurable.stopped hτ (hHp p k))
      (fun p k => energy_lt_top_of_abs_le
        (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
      X₀ (fun p => Probability.stopped τ (bdrift p))
      (fun t ω => X (clipTime τ t ω) ω) := by
  classical
  refine ⟨fun ω => (h.continuous_path ω).comp (continuous_clipTime τ ω), ?_, ?_⟩
  · intro t
    rcases le_or_gt t 0 with ht | ht
    · have hEq : (fun ω => X (clipTime τ t ω) ω) = X t := by
        funext ω
        refine congrArg (fun u => X u ω) ?_
        exact clipTime_of_le (le_trans (by exact_mod_cast ht) (hτ0 ω))
      rw [hEq]
      exact h.adapted t
    · refine stronglyMeasurable_of_tendsto_pi
        (F := fun m ω => X (clipTime (gridStop τ t m) t ω) ω) (fun m => ?_) (fun ω => ?_)
      · exact stronglyMeasurable_clip ℱ' (isStoppingTime_gridStop τ hτ t m) h.adapted
          ((Finset.range (m + 1)).image (gridPt t m)) (gridStop_eq_or_top τ t m) t
      · exact ((h.continuous_path ω).tendsto _).comp (tendsto_clipTime_gridStop τ hτ0 ht ω)
  · intro t ht
    rcases eq_or_lt_of_le ht with rfl | ht'
    · have hclip : ∀ ω, clipTime τ (0 : ℝ) ω = 0 := fun ω => clipTime_of_le (hτ0 ω)
      filter_upwards [h.ae_eq 0 le_rfl,
        vectorItoProcess_zero_ae W ℱ' hcoord H hHm hHp hHs X₀ bdrift,
        vectorItoProcess_zero_ae W ℱ' hcoord (fun p k => Probability.stopped τ (H p k))
          (fun p k => Probability.measurable_uncurry_stopped hτ (hHm p k))
          (fun p k => Probability.ProgressivelyMeasurable.stopped hτ (hHp p k))
          (fun p k => energy_lt_top_of_abs_le
            (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
          X₀ (fun p => Probability.stopped τ (bdrift p))] with ω e1 e2 e3
      simp only [hclip ω]
      rw [e1, e2, e3]
    · have hσ : ∀ m : ℕ, MeasureTheory.IsStoppingTime ℱ' (gridStop τ t m) :=
        fun m => isStoppingTime_gridStop τ hτ t m
      have hσ0 : ∀ (m : ℕ) (ω : Ω), ((0 : ℝ) : WithTop ℝ) ≤ gridStop τ t m ω :=
        fun m ω => le_trans (hτ0 ω) (le_gridStop τ t m ω)
      have hmG : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          (Probability.stopped (gridStop τ t m) (H p k))) :=
        fun m p k => Probability.measurable_uncurry_stopped (hσ m) (hHm p k)
      have hpG : ∀ (m : ℕ) (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
          (Probability.stopped (gridStop τ t m) (H p k)) :=
        fun m p k => Probability.ProgressivelyMeasurable.stopped (hσ m) (hHp p k)
      have hqG : ∀ (m : ℕ) (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖Probability.stopped (gridStop τ t m) (H p k) ω s‖₊ : ℝ≥0∞) ^ 2
              ∂volume ∂P < ⊤ :=
        fun m p k => energy_lt_top_of_abs_le
          (fun ω s => Probability.abs_stopped_le (gridStop τ t m) (H p k) ω s) (hHs p k)
      have hmS : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          (Probability.stopped τ (H p k))) :=
        fun p k => Probability.measurable_uncurry_stopped hτ (hHm p k)
      have hpS : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
          (Probability.stopped τ (H p k)) :=
        fun p k => Probability.ProgressivelyMeasurable.stopped hτ (hHp p k)
      have hqS : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖Probability.stopped τ (H p k) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
        fun p k => energy_lt_top_of_abs_le
          (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k)
      have hgrid : ∀ m : ℕ, (fun ω => X (clipTime (gridStop τ t m) t ω) ω)
          =ᵐ[P] vectorItoProcess W ℱ' hcoord
            (fun p k => Probability.stopped (gridStop τ t m) (H p k)) (hmG m) (hpG m) (hqG m)
            X₀ (fun p => Probability.stopped (gridStop τ t m) (bdrift p)) t := by
        intro m
        exact (h.stopped W ℱ' hcoord (hσ m) (hσ0 m)
          ((Finset.range (m + 1)).image (gridPt t m))
          (fun c hc => by
            obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hc
            exact gridPt_nonneg ht'.le m j)
          (gridStop_eq_or_top τ t m)).ae_eq t ht
      obtain ⟨ms, hmsge, hSI⟩ := exists_seq_ae_tendsto_of_tendsto_lintegral (μ := P)
        (ι := Fin n × Fin d)
        (u := fun m c ω => stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
          (Probability.stopped (gridStop τ t m) (H c.1 c.2)) (hmG m c.1 c.2) (hpG m c.1 c.2)
          (hqG m c.1 c.2) t ω)
        (v := fun c ω => stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
          (Probability.stopped τ (H c.1 c.2)) (hmS c.1 c.2) (hpS c.1 c.2) (hqS c.1 c.2) t ω)
        (fun m c => ((stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
          (hmG m c.1 c.2) (hpG m c.1 c.2) (hqG m c.1 c.2) t).mono (ℱ'.le t)).measurable)
        (fun c => ((stochasticIntegralBrownian_stronglyAdapted (W.W c.2) ℱ' (hcoord c.2) _
          (hmS c.1 c.2) (hpS c.1 c.2) (hqS c.1 c.2) t).mono (ℱ'.le t)).measurable)
        (fun c => by
          refine Filter.Tendsto.congr (fun m => ?_)
            (tendsto_energy_stopped_gridStop hτ (hHm c.1 c.2) ht' (hHs c.1 c.2 t ht'))
          exact (isometry_diff_stochasticIntegralBrownian (W.W c.2) ℱ' (hcoord c.2)
            (Probability.stopped (gridStop τ t m) (H c.1 c.2))
            (Probability.stopped τ (H c.1 c.2))
            (hmG m c.1 c.2) (hmS c.1 c.2) (hpG m c.1 c.2) (hpS c.1 c.2)
            (hqG m c.1 c.2) (hqS c.1 c.2) ht').symm)
      have hdrift : ∀ᵐ ω ∂P, ∀ p : Fin n, Filter.Tendsto
          (fun m : ℕ => ∫ s in Set.Icc (0 : ℝ) t,
            Probability.stopped (gridStop τ t m) (bdrift p) ω s ∂volume) Filter.atTop
          (𝓝 (∫ s in Set.Icc (0 : ℝ) t, Probability.stopped τ (bdrift p) ω s ∂volume)) := by
        have hint : ∀ᵐ ω ∂P, ∀ p : Fin n,
            MeasureTheory.IntegrableOn (bdrift p ω) (Set.Icc (0 : ℝ) t) volume := by
          rw [MeasureTheory.ae_all_iff]
          exact fun p => ae_integrableOn_of_energy_lt_top (hbm p) (hbq p t ht')
        filter_upwards [hint] with ω hω
        intro p
        refine MeasureTheory.tendsto_integral_of_dominated_convergence
          (fun s => |bdrift p ω s|) (fun m => ?_) (hω p).abs (fun m => ?_) ?_
        · exact (Measurable.of_uncurry_left
            (Probability.measurable_uncurry_stopped (hσ m) (hbm p))).aestronglyMeasurable
        · refine Filter.Eventually.of_forall fun s => ?_
          rw [Real.norm_eq_abs]
          exact Probability.abs_stopped_le (gridStop τ t m) (bdrift p) ω s
        · have hnull : (volume.restrict (Set.Icc (0 : ℝ) t)) {(0 : ℝ)} = 0 := by simp
          filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull,
            MeasureTheory.ae_restrict_mem measurableSet_Icc] with s hs0 hsmem
          have hsne : s ≠ 0 := by simpa using hs0
          have hs : 0 < s := lt_of_le_of_ne hsmem.1 (Ne.symm hsne)
          by_cases hτs : ((s : ℝ) : WithTop ℝ) ≤ τ ω
          · refine tendsto_atTop_of_eventually_const (i₀ := 0) fun m _ => ?_
            have h1 : ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t m ω :=
              le_trans hτs (le_gridStop τ t m ω)
            simp [Probability.stopped, h1, hτs]
          · rw [not_le] at hτs
            obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
              (eventually_gridStop_lt τ ht' ω hs hsmem.2 hτs)
            refine tendsto_atTop_of_eventually_const (i₀ := N) fun m hmN => ?_
            have h1 : ¬ ((s : ℝ) : WithTop ℝ) ≤ gridStop τ t m ω := not_le.mpr (hN m hmN)
            have h2 : ¬ ((s : ℝ) : WithTop ℝ) ≤ τ ω := not_le.mpr hτs
            simp [Probability.stopped, h1, h2]
      have hmsTop : Filter.Tendsto ms Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono hmsge Filter.tendsto_id
      filter_upwards [MeasureTheory.ae_all_iff.mpr hgrid, hSI, hdrift] with ω h1 h2 h3
      funext p
      have hB : Filter.Tendsto (fun i : ℕ => X₀ ω p
          + (∫ s in Set.Icc (0 : ℝ) t,
              Probability.stopped (gridStop τ t (ms i)) (bdrift p) ω s ∂volume)
          + ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
              (Probability.stopped (gridStop τ t (ms i)) (H p k))
              (hmG (ms i) p k) (hpG (ms i) p k) (hqG (ms i) p k) t ω) Filter.atTop
          (𝓝 (X₀ ω p
            + (∫ s in Set.Icc (0 : ℝ) t, Probability.stopped τ (bdrift p) ω s ∂volume)
            + ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
                (Probability.stopped τ (H p k)) (hmS p k) (hpS p k) (hqS p k) t ω)) :=
        (tendsto_const_nhds.add ((h3 p).comp hmsTop)).add
          (tendsto_finsetSum _ fun k _ => h2 (p, k))
      have hA : Filter.Tendsto (fun i : ℕ => X (clipTime (gridStop τ t (ms i)) t ω) ω p)
          Filter.atTop (𝓝 (X (clipTime τ t ω) ω p)) :=
        (((continuous_apply p).comp (h.continuous_path ω)).tendsto _).comp
          ((tendsto_clipTime_gridStop τ hτ0 ht' ω).comp hmsTop)
      exact tendsto_nhds_unique hA
        (Filter.Tendsto.congr (fun i => (congrFun (h1 (ms i)) p).symm) hB)

include hcoord in
/-- **Itô's formula along a path stopped at a stopping time.** -/
theorem itoFormula_stopped_general
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ' (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ' hcoord H hHm hHp hHs X₀ bdrift X)
    (𝒲 : ∀ j : Fin d, Multidim.MultidimBrownianMotion.CrossWitness W ℱ' j)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ' 0 ≤ ℱ' t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ' 0] s)
    (hX₀ : ∀ p : Fin n, Measurable[ℱ' 0] fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p)))
    (hbp : ∀ p, Probability.ProgressivelyMeasurable ℱ' (bdrift p))
    (hbq : ∀ (p : Fin n) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖bdrift p ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ' τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) ω s‖₊
        : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X (clipTime τ T ω) ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s ∂volume)
        + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
            (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
            (hmg p k) (hpg p k) (hqg p k) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
              * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
  classical
  have hstop := h.stopped_general W ℱ' hcoord hbm hbq hτ hτ0
  have hG : ∀ (p : Fin n) (k : Fin d),
      (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (H p k) ω s)
        = Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * H p k ω s) :=
    fun p k => stopped_comp_eq τ (coordDeriv f' p) (H p k)
  have hGb : ∀ p : Fin n,
      (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (bdrift p) ω s)
        = Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) :=
    fun p => stopped_comp_eq τ (coordDeriv f' p) (bdrift p)
  have hGq : ∀ p q : Fin n,
      (fun ω s => coordDeriv₂ f'' p q (X (clipTime τ s ω) ω)
          * ∑ k : Fin d, Probability.stopped τ (H p k) ω s
              * Probability.stopped τ (H q k) ω s)
        = Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
            * ∑ k : Fin d, H p k ω s * H q k ω s) :=
    fun p q => stopped_comp₂_eq τ (coordDeriv₂ f'' p q) (fun k => H p k) (fun k => H q k)
  have hmgτ : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
      fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
        * Probability.stopped τ (H p k) ω s) := by
    intro p k
    rw [hG p k]
    exact hmg p k
  have hpgτ : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ'
      fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
        * Probability.stopped τ (H p k) ω s := by
    intro p k
    rw [hG p k]
    exact hpg p k
  have hqgτ : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
        (‖coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (H p k) ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
    intro p k
    have hthis := hqg p k
    rw [← hG p k] at hthis
    exact hthis
  have hres := itoFormula_of_unbounded W ℱ' hcoord hstop 𝒲 hℱ0 hnull hX₀
    (fun p => Probability.measurable_uncurry_stopped hτ (hbm p))
    (fun p => Probability.ProgressivelyMeasurable.stopped hτ (hbp p))
    (fun p T' hT' => energy_lt_top_of_abs_le
      (fun ω s => Probability.abs_stopped_le τ (bdrift p) ω s) (hbq p) T' hT')
    hfC hf hf' hmgτ hpgτ hqgτ hT
  have hSI : ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
            * Probability.stopped τ (H p k) ω s)
          (hmgτ p k) (hpgτ p k) (hqgτ p k) T
        = stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
          (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
          (hmg p k) (hpg p k) (hqg p k) T :=
    fun p k => stochasticIntegralBrownian_congr_fun (W.W k) ℱ' (hcoord k) (hG p k)
      (hmgτ p k) (hpgτ p k) (hqgτ p k) (hmg p k) (hpg p k) (hqg p k) T
  filter_upwards [hres] with ω hω
  rw [clipTime_of_le (hτ0 ω)] at hω
  have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv f' p (X (clipTime τ s ω) ω) * Probability.stopped τ (bdrift p) ω s ∂volume)
      = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        Probability.stopped τ (fun ω s => coordDeriv f' p (X s ω) * bdrift p ω s) ω s
          ∂volume := by
    refine Finset.sum_congr rfl fun p _ => ?_
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun s _ => congrFun (congrFun (hGb p) ω) s
  have e2 : (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (fun ω s => coordDeriv f' p (X (clipTime τ s ω) ω)
          * Probability.stopped τ (H p k) ω s) (hmgτ p k) (hpgτ p k) (hqgτ p k) T ω)
      = ∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ' (hcoord k)
        (Probability.stopped τ fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
        (hmg p k) (hpg p k) (hqg p k) T ω :=
    Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun k _ => congrFun (hSI p k) ω
  have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        coordDeriv₂ f'' p q (X (clipTime τ s ω) ω)
          * ∑ k : Fin d, Probability.stopped τ (H p k) ω s
              * Probability.stopped τ (H q k) ω s ∂volume)
      = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
        Probability.stopped τ (fun ω s => coordDeriv₂ f'' p q (X s ω)
          * ∑ k : Fin d, H p k ω s * H q k ω s) ω s ∂volume := by
    refine congrArg (fun x => 1 / 2 * x) ?_
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      fun s _ => congrFun (congrFun (hGq p q) ω) s
  rw [hω, e1, e2, e3]

end StoppedGeneral

end LevyStochCalc.Brownian.Ito
