/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Brownian.ItoOptionalStopping
import LevyStochCalc.Brownian.VectorItoProcessVersion

/-!
# Stopping a vector Itô process

Cutting the coefficients of a vector Itô process off at a stopping time of finite range leaves a
vector Itô process, whose version is the original one evaluated at the clipped time.

## Main statements

* `LevyStochCalc.Brownian.Ito.clipTime` — the horizon clipped at a stopping time.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped_clip` — the Itô integral of a
  stopped integrand is the integral evaluated at the clipped horizon.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.stopped` — the stopped version.
-/

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

section Clip

variable {Ω : Type u}

/-- The horizon `t` clipped at a stopping time: `t` itself where the time has not been reached,
and the time's value otherwise. -/
noncomputable def clipTime (τ : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) : ℝ :=
  if ((t : ℝ) : WithTop ℝ) ≤ τ ω then t else (τ ω).untopD t

variable {τ : Ω → WithTop ℝ} {t : ℝ} {ω : Ω}

theorem clipTime_of_le (h : ((t : ℝ) : WithTop ℝ) ≤ τ ω) : clipTime τ t ω = t := if_pos h

theorem clipTime_eq_self_of_top (h : τ ω = ⊤) : clipTime τ t ω = t :=
  clipTime_of_le (by rw [h]; exact le_top)

theorem clipTime_eq_min {r : ℝ} (h : τ ω = ((r : ℝ) : WithTop ℝ)) :
    clipTime τ t ω = min t r := by
  rw [clipTime, h]
  by_cases hle : t ≤ r
  · rw [if_pos (by exact_mod_cast hle), min_eq_left hle]
  · rw [if_neg (by exact_mod_cast hle), min_eq_right (le_of_not_ge hle)]
    simp

theorem clipTime_le_self (τ : Ω → WithTop ℝ) (t : ℝ) (ω : Ω) : clipTime τ t ω ≤ t := by
  by_cases hle : ((t : ℝ) : WithTop ℝ) ≤ τ ω
  · exact le_of_eq (clipTime_of_le hle)
  · have hne : τ ω ≠ ⊤ := by
      intro hcon
      exact hle (by rw [hcon]; exact le_top)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    rw [clipTime_eq_min hr.symm]
    exact min_le_left _ _

theorem le_clipTime_iff {s : ℝ} (hs : s ≤ t) :
    ((s : ℝ) : WithTop ℝ) ≤ τ ω ↔ s ≤ clipTime τ t ω := by
  by_cases hle : ((t : ℝ) : WithTop ℝ) ≤ τ ω
  · rw [clipTime_of_le hle]
    refine ⟨fun _ => hs, fun _ => le_trans (by exact_mod_cast hs) hle⟩
  · have hne : τ ω ≠ ⊤ := by
      intro hcon
      exact hle (by rw [hcon]; exact le_top)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    have hrt : r < t := by
      by_contra hcon
      exact hle (by rw [← hr]; exact_mod_cast le_of_not_gt hcon)
    rw [clipTime_eq_min hr.symm, min_eq_right hrt.le, ← hr]
    exact WithTop.coe_le_coe

theorem clipTime_nonneg (ht : 0 ≤ t) (hτ0 : ((0 : ℝ) : WithTop ℝ) ≤ τ ω) :
    0 ≤ clipTime τ t ω := (le_clipTime_iff ht).mp hτ0

theorem continuous_clipTime (τ : Ω → WithTop ℝ) (ω : Ω) :
    Continuous fun t : ℝ => clipTime τ t ω := by
  by_cases hne : τ ω = ⊤
  · exact continuous_id.congr fun t => (clipTime_eq_self_of_top hne).symm
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    exact (continuous_id.min continuous_const).congr fun t => (clipTime_eq_min hr.symm).symm

end Clip

section StoppedIntegral

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  (W : LevyStochCalc.Brownian.BrownianMotion P) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hℱ : IsBrownianFiltration W ℱ) (τ : Ω → WithTop ℝ)

include hℱ in
/-- **The Itô integral of a stopped integrand is the integral evaluated at the clipped
horizon.** -/
theorem stochasticIntegralBrownian_stopped_clip
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
        (Probability.measurable_uncurry_stopped hτ hm)
        (Probability.ProgressivelyMeasurable.stopped hτ hp)
        (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq (clipTime τ t ω) ω := by
  classical
  filter_upwards [stochasticIntegralBrownian_stopped τ W ℱ hℱ hτ hm hp hq ht J hJ0 hJt hτJ]
    with ω hω
  rw [hω]
  rcases hτJ ω with ⟨c, hcJ, hceq⟩ | hle
  · have hct : c < t := hJt c hcJ
    have hsum : ∑ c' ∈ J, hitInd τ c' ω *
        (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c' ω)
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω := by
      refine (Finset.sum_eq_single c ?_ ?_).trans ?_
      · intro c' _ hne
        have : hitInd τ c' ω = 0 := by
          refine Set.indicator_of_notMem ?_ _
          intro hmem
          exact hne (by exact_mod_cast (hmem.symm.trans hceq))
        rw [this, zero_mul]
      · intro hcon
        exact absurd hcJ hcon
      · have hone : hitInd τ c ω = 1 := by
          simp only [hitInd]
          exact Set.indicator_of_mem (by simpa using hceq) _
        rw [hone, one_mul]
    rw [hsum, clipTime_eq_min hceq, min_eq_right hct.le]
    ring
  · have hsum : ∑ c' ∈ J, hitInd τ c' ω *
        (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c' ω) = 0 := by
      refine Finset.sum_eq_zero fun c' hc' => ?_
      have : hitInd τ c' ω = 0 := by
        refine Set.indicator_of_notMem ?_ _
        intro hmem
        have : ((t : ℝ) : WithTop ℝ) ≤ ((c' : ℝ) : WithTop ℝ) := hmem ▸ hle
        exact absurd (by exact_mod_cast this) (not_le.mpr (hJt c' hc'))
      rw [this, zero_mul]
    rw [hsum, clipTime_of_le hle, sub_zero]

end StoppedIntegral

section StoppedDrift

variable {Ω : Type u}

/-- The window integral of a stopped integrand is the integral over the clipped window. -/
theorem setIntegral_stopped_eq (τ : Ω → WithTop ℝ) (b : Ω → ℝ → ℝ) {t : ℝ} (ω : Ω) :
    ∫ s in Set.Icc (0 : ℝ) t, Probability.stopped τ b ω s ∂volume
      = ∫ s in Set.Icc (0 : ℝ) (clipTime τ t ω), b ω s ∂volume := by
  have hsub : Set.Icc (0 : ℝ) (clipTime τ t ω) ⊆ Set.Icc (0 : ℝ) t :=
    Set.Icc_subset_Icc le_rfl (clipTime_le_self τ t ω)
  have hpt : ∀ s ∈ Set.Icc (0 : ℝ) t, Probability.stopped τ b ω s
      = Set.indicator (Set.Icc (0 : ℝ) (clipTime τ t ω)) (b ω) s := by
    intro s hs
    simp only [Probability.stopped]
    by_cases hle : ((s : ℝ) : WithTop ℝ) ≤ τ ω
    · have hsc : s ≤ clipTime τ t ω := (le_clipTime_iff hs.2).mp hle
      have hmem : s ∈ Set.Icc (0 : ℝ) (clipTime τ t ω) := ⟨hs.1, hsc⟩
      rw [if_pos hle, Set.indicator_of_mem hmem]
    · have hsc : ¬ s ≤ clipTime τ t ω := fun hcon => hle ((le_clipTime_iff hs.2).mpr hcon)
      rw [if_neg hle, Set.indicator_of_notMem (fun hmem => hsc hmem.2)]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt,
    MeasureTheory.setIntegral_indicator measurableSet_Icc,
    Set.inter_eq_self_of_subset_right hsub]

end StoppedDrift

section StoppedVersion

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} (W : Multidim.MultidimBrownianMotion P d)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
  (hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ)

omit [IsProbabilityMeasure P] in
/-- A continuous adapted process evaluated at a clipped horizon is adapted, for a stopping time
of finite range. -/
theorem stronglyMeasurable_clip {X : ℝ → Ω → Fin n → ℝ} {τ : Ω → WithTop ℝ}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hX : ∀ r : ℝ, @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ r) (X r))
    (J : Finset ℝ)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤)
    (t : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω (Fin n → ℝ) _ (ℱ t)
      (fun ω => X (clipTime τ t ω) ω) := by
  classical
  set Jt : Finset ℝ := J.filter (fun c => c ≤ t) with hJtdef
  have hJtle : ∀ c ∈ Jt, c ≤ t := fun c hc => (Finset.mem_filter.mp hc).2
  have hdec : (fun ω => X (clipTime τ t ω) ω)
      = fun ω => Set.indicator {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)}
            (fun ω => X t ω) ω
          + ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} (fun ω => X c ω) ω := by
    funext ω
    rcases hτJ ω with ⟨c₀, hc₀J, hc₀⟩ | htop
    · by_cases hle : c₀ ≤ t
      · have hc₀Jt : c₀ ∈ Jt := Finset.mem_filter.mpr ⟨hc₀J, hle⟩
        have hnot : ω ∉ {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
          intro hcon
          exact hcon c₀ hc₀Jt hc₀
        have hsum : ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)}
            (fun ω => X c ω) ω = X c₀ ω := by
          refine (Finset.sum_eq_single c₀ ?_ ?_).trans ?_
          · intro c _ hne
            refine Set.indicator_of_notMem ?_ _
            intro hmem
            exact hne (by exact_mod_cast (hmem.symm.trans hc₀ : _))
          · intro hcon
            exact absurd hc₀Jt hcon
          · exact Set.indicator_of_mem (by simpa using hc₀) _
        rw [Set.indicator_of_notMem hnot, hsum, clipTime_eq_min hc₀, min_eq_right hle]
        simp
      · have hmemc : ω ∈ {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
          intro c hc hcon
          have : c₀ = c := by exact_mod_cast (hc₀.symm.trans hcon : _)
          exact hle (this ▸ hJtle c hc)
        have hsum : ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)}
            (fun ω => X c ω) ω = 0 :=
          Finset.sum_eq_zero fun c hc => by
            refine Set.indicator_of_notMem ?_ _
            exact hmemc c hc
        rw [Set.indicator_of_mem hmemc, hsum, clipTime_eq_min hc₀,
          min_eq_left (le_of_not_ge hle)]
        simp
    · have hmemc : ω ∈ {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
        intro c _ hcon
        rw [htop] at hcon
        exact (WithTop.coe_ne_top hcon.symm : _)
      have hsum : ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)}
          (fun ω => X c ω) ω = 0 :=
        Finset.sum_eq_zero fun c hc => by
          refine Set.indicator_of_notMem ?_ _
          exact hmemc c hc
      rw [Set.indicator_of_mem hmemc, hsum, clipTime_eq_self_of_top htop]
      simp
  rw [hdec]
  letI : MeasurableSpace Ω := ℱ t
  have hsetc : MeasurableSet {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)} := by
    have : {ω | ∀ c ∈ Jt, τ ω ≠ ((c : ℝ) : WithTop ℝ)}
        = ⋂ c ∈ Jt, {ω | τ ω = ((c : ℝ) : WithTop ℝ)}ᶜ := by
      ext ω; simp [Set.mem_iInter]
    rw [this]
    refine MeasurableSet.biInter (Jt.countable_toSet) fun c hc => ?_
    exact (ℱ.mono (hJtle c hc) _ (hτ.measurableSet_eq c)).compl
  refine ((hX t).indicator hsetc).add ?_
  have hfun : (fun ω => ∑ c ∈ Jt,
        Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} (fun ω => X c ω) ω)
      = ∑ c ∈ Jt, Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} (fun ω => X c ω) := by
    funext ω
    simp
  rw [hfun]
  refine Finset.stronglyMeasurable_sum _ fun c hc => ?_
  exact ((hX c).mono (ℱ.mono (hJtle c hc))).indicator
    (ℱ.mono (hJtle c hc) _ (hτ.measurableSet_eq c))

include hcoord in
/-- A vector Itô process starts at its initial value. -/
theorem vectorItoProcess_zero_ae
    (H : Fin n → Fin d → Ω → ℝ → ℝ)
    (hHm : ∀ p k, Measurable (Function.uncurry (H p k)))
    (hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k))
    (hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (X₀ : Ω → Fin n → ℝ) (bdrift : Fin n → Ω → ℝ → ℝ) :
    vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift 0 =ᵐ[P] X₀ := by
  have hall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
      stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k) (hHs p k) 0 ω
        = 0 := by
    rw [MeasureTheory.ae_all_iff]
    intro p
    rw [MeasureTheory.ae_all_iff]
    intro k
    exact stochasticIntegralBrownian_ae_zero_of_nonpos (W.W k) ℱ (hcoord k) (H p k)
      (hHm p k) (hHp p k) (hHs p k) le_rfl
  filter_upwards [hall] with ω hz
  funext p
  have hdrift : ∫ s in Set.Icc (0 : ℝ) 0, bdrift p ω s ∂volume = 0 := by
    rw [show Set.Icc (0 : ℝ) 0 = {(0 : ℝ)} from Set.Icc_self 0,
      MeasureTheory.setIntegral_measure_zero _ Real.volume_singleton]
  simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral, hdrift]
  have hsum : ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k)
      (hHm p k) (hHp p k) (hHs p k) 0 ω = 0 :=
    Finset.sum_eq_zero fun k _ => hz p k
  rw [hsum]
  ring

include hcoord in
/-- **The process stopped at a stopping time of finite range is the vector Itô process of the
stopped coefficients.** -/
theorem IsVectorItoVersion.stopped
    {H : Fin n → Fin d → Ω → ℝ → ℝ}
    {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
    {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
    {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
    {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    {τ : Ω → WithTop ℝ} (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    (hτ0 : ∀ ω, ((0 : ℝ) : WithTop ℝ) ≤ τ ω)
    (J : Finset ℝ) (hJ0 : ∀ c ∈ J, 0 ≤ c)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ τ ω = ⊤) :
    IsVectorItoVersion W ℱ hcoord (fun p k => Probability.stopped τ (H p k))
      (fun p k => Probability.measurable_uncurry_stopped hτ (hHm p k))
      (fun p k => Probability.ProgressivelyMeasurable.stopped hτ (hHp p k))
      (fun p k => energy_lt_top_of_abs_le
        (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
      X₀ (fun p => Probability.stopped τ (bdrift p))
      (fun t ω => X (clipTime τ t ω) ω) := by
  classical
  refine ⟨fun ω => (h.continuous_path ω).comp (continuous_clipTime τ ω),
    fun t => stronglyMeasurable_clip ℱ hτ (fun r => h.adapted r) J hτJ t, ?_⟩
  intro t ht
  rcases eq_or_lt_of_le ht with rfl | ht'
  · have hclip : ∀ ω, clipTime τ (0 : ℝ) ω = 0 := fun ω => clipTime_of_le (hτ0 ω)
    filter_upwards [h.ae_eq 0 le_rfl,
      vectorItoProcess_zero_ae W ℱ hcoord H hHm hHp hHs X₀ bdrift,
      vectorItoProcess_zero_ae W ℱ hcoord (fun p k => Probability.stopped τ (H p k))
        (fun p k => Probability.measurable_uncurry_stopped hτ (hHm p k))
        (fun p k => Probability.ProgressivelyMeasurable.stopped hτ (hHp p k))
        (fun p k => energy_lt_top_of_abs_le
          (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k))
        X₀ (fun p => Probability.stopped τ (bdrift p))] with ω e1 e2 e3
    simp only [hclip ω]
    rw [e1, e2, e3]
  · set J' : Finset ℝ := J.filter (fun c => c < t) with hJ'def
    have hJ'0 : ∀ c ∈ J', 0 ≤ c := fun c hc => hJ0 c (Finset.mem_filter.mp hc).1
    have hJ't : ∀ c ∈ J', c < t := fun c hc => (Finset.mem_filter.mp hc).2
    have hτJ' : ∀ ω, (∃ c ∈ J', τ ω = ((c : ℝ) : WithTop ℝ))
        ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω := by
      intro ω
      rcases hτJ ω with ⟨c, hcJ, hceq⟩ | htop
      · by_cases hlt : c < t
        · exact Or.inl ⟨c, Finset.mem_filter.mpr ⟨hcJ, hlt⟩, hceq⟩
        · refine Or.inr ?_
          rw [hceq]
          exact_mod_cast le_of_not_gt hlt
      · refine Or.inr ?_
        rw [htop]
        exact le_top
    have hclip0 : ∀ ω, 0 ≤ clipTime τ t ω := fun ω => clipTime_nonneg ht (hτ0 ω)
    have hmemc : ∀ ω, clipTime τ t ω ∈ insert t (J : Set ℝ) := by
      intro ω
      rcases hτJ ω with ⟨c, hcJ, hceq⟩ | htop
      · rw [clipTime_eq_min hceq]
        rcases min_choice t c with hmin | hmin
        · rw [hmin]
          exact Set.mem_insert _ _
        · rw [hmin]
          exact Set.mem_insert_of_mem _ hcJ
      · rw [clipTime_eq_self_of_top htop]
        exact Set.mem_insert _ _
    have hcount : (insert t (J : Set ℝ)).Countable := (J.countable_toSet).insert t
    have hval : ∀ᵐ ω ∂P, ∀ c ∈ insert t (J : Set ℝ), 0 ≤ c →
        X c ω = vectorItoProcess W ℱ hcoord H hHm hHp hHs X₀ bdrift c ω := by
      rw [MeasureTheory.ae_ball_iff hcount]
      intro c _
      by_cases hc0 : 0 ≤ c
      · filter_upwards [h.ae_eq c hc0] with ω hω
        exact fun _ => hω
      · exact Filter.Eventually.of_forall fun ω hcon => absurd hcon hc0
    have hSIall : ∀ᵐ ω ∂P, ∀ (p : Fin n) (k : Fin d),
        stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (Probability.stopped τ (H p k))
            (Probability.measurable_uncurry_stopped hτ (hHm p k))
            (Probability.ProgressivelyMeasurable.stopped hτ (hHp p k))
            (energy_lt_top_of_abs_le
              (fun ω s => Probability.abs_stopped_le τ (H p k) ω s) (hHs p k)) t ω
          = stochasticIntegralBrownian (W.W k) ℱ (hcoord k) (H p k) (hHm p k) (hHp p k)
              (hHs p k) (clipTime τ t ω) ω := by
      rw [MeasureTheory.ae_all_iff]
      intro p
      rw [MeasureTheory.ae_all_iff]
      intro k
      exact stochasticIntegralBrownian_stopped_clip (W.W k) ℱ (hcoord k) τ hτ (hHm p k)
        (hHp p k) (hHs p k) ht' J' hJ'0 hJ't hτJ'
    filter_upwards [hval, hSIall] with ω e1 e2
    rw [e1 (clipTime τ t ω) (hmemc ω) (hclip0 ω)]
    funext m
    simp only [vectorItoProcess, vectorItoMartingale, coordItoIntegral]
    rw [setIntegral_stopped_eq τ (bdrift m) ω]
    congr 1
    exact Finset.sum_congr rfl fun k _ => (e2 m k).symm

end StoppedVersion

end LevyStochCalc.Brownian.Ito
