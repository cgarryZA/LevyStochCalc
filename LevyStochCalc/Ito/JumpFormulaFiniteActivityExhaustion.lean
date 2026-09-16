/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Ito.JumpFormulaFiniteActivityDrift

/-!
# Exhausting a finite-activity jump path by its arrival times

The jumps of a mark set accumulated up to the arrival times capped at the horizon no longer move
once the arrival time has passed the horizon, so a telescope over a chain of arrival times has
only in-window terms, and the in-window members of such a chain are matched one for one with the
entries of the strictly monotone enumeration of the window's atom times. On a mark set of finite
intensity almost every path has an arrival time beyond the horizon, so an identity holding almost
everywhere on each event where the chain has passed the horizon holds almost everywhere. Between
consecutive arrival times inside the window the accumulated jumps gain exactly the jump
coefficient carried by the later arrival time and the mark enumerated with it, and the progressive
measurability of the chain data and of the integrands passes to the right-continuous
regularisation of a filtration.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, Theorem 4.4.7, §6.2.
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.5, §IV.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.JumpFormula

universe u v

section CappedShift

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

/-- The jumps of a mark set accumulated up to the `k`-th arrival time capped at the horizon. -/
noncomputable def cappedJumpSum (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀)
    (A : Set E) (T : ℝ) (k : ℕ) (ω : Ω) : Fin n → ℝ :=
  LevyStochCalc.Ito.JumpSplitting.jumpSum X A
    (LevyStochCalc.Brownian.Ito.clipTime (LevyStochCalc.Poisson.jumpTime N A k) T ω) ω

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) (A : Set E)

/-- The capped jump sum at the zeroth arrival time vanishes. -/
theorem cappedJumpSum_zero {T : ℝ} (hT : 0 ≤ T) (ω : Ω) : cappedJumpSum X A T 0 ω = 0 := by
  funext i
  rw [cappedJumpSum,
    LevyStochCalc.Brownian.Ito.clipTime_eq_zero hT (LevyStochCalc.Poisson.jumpTime_zero N A ω),
    LevyStochCalc.Ito.JumpSplitting.jumpSum_zero]
  rfl

/-- Past the horizon the capped jump sum is the jump sum over the whole window. -/
theorem cappedJumpSum_of_le {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSum X A T k ω = LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω := by
  rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_of_le hk]

/-- Past the horizon the capped jump sum no longer moves with the index. -/
theorem cappedJumpSum_succ_eq {T : ℝ} {k : ℕ} {ω : Ω}
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    cappedJumpSum X A T (k + 1) ω = cappedJumpSum X A T k ω := by
  rw [cappedJumpSum_of_le X A hk,
    cappedJumpSum_of_le X A
      (hk.trans (LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω))]

/-- Past the horizon the telescope's jump term vanishes. -/
theorem jumpTerm_eq_zero_of_le {T : ℝ} {k : ℕ} {ω : Ω} (f : (Fin n → ℝ) → ℝ) (y : Fin n → ℝ)
    (hk : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A k ω) :
    f (y + cappedJumpSum X A T (k + 1) ω) - f (y + cappedJumpSum X A T k ω) = 0 := by
  rw [cappedJumpSum_succ_eq X A hk, sub_self]

/-- The chain of capped shifts reaches the whole jump sum at any index whose arrival time has
passed the horizon, so a path that splits at the horizon is the translated Itô path there. -/
theorem eq_add_cappedJumpSum_of_le {T : ℝ} {m : ℕ} {ω : Ω} {V : ℝ → Ω → Fin n → ℝ}
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω)
    (hsplit : ∀ i : Fin n, X.X T ω i
      = V T ω i + LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω i) (i : Fin n) :
    V T ω i + cappedJumpSum X A T m ω i = X.X T ω i := by
  rw [cappedJumpSum_of_le X A hm, hsplit i]

/-- Past the horizon index the telescope's jump sum no longer grows with the range. -/
theorem sum_range_jumpTerm_eq_of_le (f : (Fin n → ℝ) → ℝ) (Y : ℕ → Fin n → ℝ)
    {T : ℝ} {ω : Ω} {m m' : ℕ} (hmm : m ≤ m')
    (hm : ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω) :
    (∑ k ∈ Finset.range m', (f (Y k + cappedJumpSum X A T (k + 1) ω)
          - f (Y k + cappedJumpSum X A T k ω)))
      = ∑ k ∈ Finset.range m, (f (Y k + cappedJumpSum X A T (k + 1) ω)
          - f (Y k + cappedJumpSum X A T k ω)) := by
  refine (Finset.sum_subset (fun x hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) hmm)) fun k _ hk => ?_).symm
  have hmk : m ≤ k := not_lt.mp fun hc => hk (Finset.mem_range.mpr hc)
  exact jumpTerm_eq_zero_of_le X A f (Y k)
    (hm.trans (LevyStochCalc.Poisson.jumpTime_mono N A hmk ω))

end CappedShift

section Reindex

/-- **Reindexing the in-window arrival indices by the atom enumeration.** For a chain of times
starting at the origin, increasing with the index, strictly increasing at every index whose
successor lies inside the window, and passing the horizon at index `m`, a choice of atom index
carrying each in-window arrival time matches the in-window indices below `m` with the entries of
the strictly monotone enumeration of the window's atom times. -/
theorem sum_range_ite_eq_sum_atomEnum {K m : ℕ} {θ : Fin K → ℝ} {σ : ℕ → WithTop ℝ} {T : ℝ}
    (hθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, σ i = ((v : ℝ) : WithTop ℝ) ∧ 0 < v ∧ v ≤ T})
    (hσmono : Monotone σ) (hσ0 : σ 0 = ((0 : ℝ) : WithTop ℝ))
    (hstrict : ∀ i : ℕ, σ (i + 1) ≤ ((T : ℝ) : WithTop ℝ) → σ i < σ (i + 1))
    (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m) (idx : ℕ → Fin K)
    (hidx : ∀ k : ℕ, σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) →
      σ (k + 1) = ((θ (idx k) : ℝ) : WithTop ℝ)) (G : Fin K → ℝ) :
    (∑ k ∈ Finset.range m,
        if σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then G (idx k) else 0)
      = ∑ j : Fin K, G j := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun k _ => idx k) (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
  · intro a₁ ha₁ a₂ ha₂ hidxeq
    have hp₁ : σ (a₁ + 1) ≤ ((T : ℝ) : WithTop ℝ) := (Finset.mem_filter.mp ha₁).2
    have hp₂ : σ (a₂ + 1) ≤ ((T : ℝ) : WithTop ℝ) := (Finset.mem_filter.mp ha₂).2
    have heq : σ (a₁ + 1) = σ (a₂ + 1) := by
      rw [hidx a₁ hp₁, hidx a₂ hp₂, hidxeq]
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact absurd heq
        (ne_of_lt (lt_of_le_of_lt (hσmono (Nat.succ_le_of_lt hlt)) (hstrict a₂ hp₂)))
    · exact absurd heq.symm
        (ne_of_lt (lt_of_le_of_lt (hσmono (Nat.succ_le_of_lt hlt)) (hstrict a₁ hp₁)))
  · intro j _
    have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
    rw [hrange] at hmemj
    obtain ⟨i, hi, hpos, -⟩ := hmemj
    have hi0 : i ≠ 0 := by
      intro hc
      rw [hc, hσ0] at hi
      exact absurd (by exact_mod_cast hi.symm : (θ j : ℝ) = 0) (ne_of_gt hpos)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hi0
    subst hk
    have hpk : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) := by
      rw [hi]
      exact_mod_cast (hmemθ j).2
    have hkm : k < m := by
      by_contra hc
      have hmk : m ≤ k := not_lt.mp hc
      exact absurd (lt_of_lt_of_le (hstrict k hpk) (hpk.trans (hm.trans (hσmono hmk))))
        (lt_irrefl _)
    have hjeq : idx k = j := by
      have : ((θ (idx k) : ℝ) : WithTop ℝ) = ((θ j : ℝ) : WithTop ℝ) := by
        rw [← hidx k hpk, hi]
      exact hθ.injective (by exact_mod_cast this)
    exact ⟨k, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hkm, hpk⟩, hjeq⟩
  · intro _ _
    rfl

/-- **Reindexing with the atom index supplied existentially.** The form of
`sum_range_ite_eq_sum_atomEnum` that asks only for an atom index at each in-window arrival time,
so no total index function has to be produced when the window carries no atoms. -/
theorem sum_range_ite_eq_sum_atomEnum_exists {K m : ℕ} {θ : Fin K → ℝ} {σ : ℕ → WithTop ℝ}
    {T : ℝ} (hθ : StrictMono θ) (hmemθ : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, σ i = ((v : ℝ) : WithTop ℝ) ∧ 0 < v ∧ v ≤ T})
    (hσmono : Monotone σ) (hσ0 : σ 0 = ((0 : ℝ) : WithTop ℝ))
    (hstrict : ∀ i : ℕ, σ (i + 1) ≤ ((T : ℝ) : WithTop ℝ) → σ i < σ (i + 1))
    (hm : ((T : ℝ) : WithTop ℝ) ≤ σ m) (G' : ℕ → ℝ) (G : Fin K → ℝ)
    (hex : ∀ k : ℕ, σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) →
      ∃ j : Fin K, σ (k + 1) = ((θ j : ℝ) : WithTop ℝ) ∧ G' k = G j) :
    (∑ k ∈ Finset.range m,
        if σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then G' k else 0)
      = ∑ j : Fin K, G j := by
  classical
  rcases isEmpty_or_nonempty (Fin K) with hK | hK
  · have hzero : ∀ k : ℕ,
        (if σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then G' k else 0) = 0 := by
      intro k
      by_cases hp : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ)
      · exact absurd (hex k hp) fun h => hK.false h.choose
      · exact if_neg hp
    rw [Finset.sum_congr rfl fun k _ => hzero k, Finset.sum_const_zero,
      Finset.sum_eq_zero fun j _ => (hK.false j).elim]
  · obtain ⟨j₀⟩ := hK
    refine (Finset.sum_congr rfl fun k _ => ?_).trans
      (sum_range_ite_eq_sum_atomEnum hθ hmemθ hrange hσmono hσ0 hstrict hm
        (fun k => if h : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ) then (hex k h).choose else j₀)
        (fun k h => by rw [dif_pos h]; exact (hex k h).choose_spec.1) G)
    by_cases hp : σ (k + 1) ≤ ((T : ℝ) : WithTop ℝ)
    · rw [if_pos hp, if_pos hp, dif_pos hp]
      exact (hex k hp).choose_spec.2
    · rw [if_neg hp, if_neg hp]

end Reindex

section RightContinuous

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]

omit [MeasurableSpace Ω] [MeasurableSpace E] in
/-- Enlarging the first factor's `σ`-algebra enlarges the product `σ`-algebra. -/
theorem prod_le_prod_left {α : Type*} [MeasurableSpace α]
    {m₁ m₂ : MeasurableSpace Ω} (h : m₁ ≤ m₂) :
    @Prod.instMeasurableSpace Ω α m₁ inferInstance
      ≤ @Prod.instMeasurableSpace Ω α m₂ inferInstance :=
  sup_le_sup_right (MeasurableSpace.comap_mono h) _

omit [MeasurableSpace E] in
/-- A process progressively measurable for a filtration is progressively measurable for any
larger filtration. -/
theorem progressivelyMeasurable_of_le {H : Ω → ℝ → ℝ}
    {ℱ 𝒢 : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} (hle : ℱ ≤ 𝒢)
    (h : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable 𝒢 H :=
  fun t => (h t).mono (prod_le_prod_left (hle t))

/-- A marked process progressively measurable for a filtration is progressively measurable for
any larger filtration. -/
theorem markedProgressivelyMeasurable_of_le {φ : Ω → ℝ → E → ℝ}
    {ℱ 𝒢 : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›} (hle : ℱ ≤ 𝒢)
    (h : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.MarkedProgressivelyMeasurable 𝒢 φ :=
  fun t => (h t).mono (prod_le_prod_left (hle t))

omit [MeasurableSpace E] in
/-- A process progressively measurable for a filtration is progressively measurable for its
right-continuous regularisation. -/
theorem progressivelyMeasurable_rightCont {H : Ω → ℝ → ℝ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    (h : Probability.ProgressivelyMeasurable ℱ H) :
    Probability.ProgressivelyMeasurable ℱ.rightCont H :=
  progressivelyMeasurable_of_le ℱ.le_rightCont h

/-- A marked process progressively measurable for a filtration is progressively measurable for
its right-continuous regularisation. -/
theorem markedProgressivelyMeasurable_rightCont {φ : Ω → ℝ → E → ℝ}
    {ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›}
    (h : Probability.MarkedProgressivelyMeasurable ℱ φ) :
    Probability.MarkedProgressivelyMeasurable ℱ.rightCont φ :=
  markedProgressivelyMeasurable_of_le ℱ.le_rightCont h

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **The chain data of the arrival times.** For the right-continuous regularisation of a
filtration for which the random measure is Poisson, the arrival times of a measurable mark set
are stopping times, they increase with the index, and the zeroth is the origin. -/
theorem jumpTime_chain_rightCont (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)
    (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
    (hℱ : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ) (hA : MeasurableSet A) :
    (∀ k : ℕ, MeasureTheory.IsStoppingTime ℱ.rightCont
        (LevyStochCalc.Poisson.jumpTime N A k))
      ∧ (∀ (k : ℕ) (ω : Ω), LevyStochCalc.Poisson.jumpTime N A k ω
          ≤ LevyStochCalc.Poisson.jumpTime N A (k + 1) ω)
      ∧ ∀ ω : Ω, LevyStochCalc.Poisson.jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ) :=
  ⟨fun k => LevyStochCalc.Poisson.isStoppingTime_jumpTime_rightCont N A hℱ hA k,
    fun k ω => LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω,
    fun ω => LevyStochCalc.Poisson.jumpTime_zero N A ω⟩

end RightContinuous

section Exhaustion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (A : Set E)

/-- Consecutive arrival times increase. -/
theorem jumpTime_le_jumpTime_succ (k : ℕ) (ω : Ω) :
    LevyStochCalc.Poisson.jumpTime N A k ω ≤ LevyStochCalc.Poisson.jumpTime N A (k + 1) ω :=
  LevyStochCalc.Poisson.jumpTime_mono N A (Nat.le_succ k) ω

/-- The chain of arrival times starts at the origin. -/
theorem jumpTime_chain_zero (ω : Ω) :
    LevyStochCalc.Poisson.jumpTime N A 0 ω = ((0 : ℝ) : WithTop ℝ) :=
  LevyStochCalc.Poisson.jumpTime_zero N A ω

/-- The events on which the chain of arrival times has passed the horizon cover almost every
sample point. -/
theorem ae_exists_le_jumpTime (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ) :
    ∀ᵐ ω ∂P, ∃ m : ℕ,
      ω ∈ {ω' : Ω | ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω'} := by
  filter_upwards [LevyStochCalc.Poisson.ae_jumpTime_chain N A hA hAν T] with ω hω
  exact hω.2

/-- An identity that holds almost everywhere on each event where the chain of arrival times has
passed the horizon holds almost everywhere. -/
theorem ae_eq_of_ae_eq_of_le_jumpTime (hA : MeasurableSet A) (hAν : ν A ≠ ⊤) (T : ℝ)
    {L R : Ω → ℝ}
    (h : ∀ m : ℕ, ∀ᵐ ω ∂P, ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω →
      L ω = R ω) :
    L =ᵐ[P] R :=
  LevyStochCalc.Brownian.Ito.ae_eq_of_ae_eq_on_exhausting
    (S := fun m => {ω' : Ω | ((T : ℝ) : WithTop ℝ) ≤ LevyStochCalc.Poisson.jumpTime N A m ω'})
    (ae_exists_le_jumpTime N A hA hAν T) h

end Exhaustion

section MarkIdentification

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {n d : ℕ}
  {W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d}
  {N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν}
  {coeffs : LevyStochCalc.Ito.Setting.JumpDiffusionCoeffs n d E} {x₀ : Fin n → ℝ}

variable (X : LevyStochCalc.Ito.Setting.JumpDiffusion W N coeffs x₀) {A : Set E} {K : ℕ}
  {θ : Fin K → ℝ} {ε : Fin K → E} {T : ℝ} {ω : Ω}

/-- The jump sum over a sub-window of an enumerated window is the sum of the jump coefficient
over the enumerated atoms whose times lie in the sub-window. -/
theorem jumpSum_eq_sum_atomEnum (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    {t : ℝ} (ht : t ≤ T) (i : Fin n) :
    LevyStochCalc.Ito.JumpSplitting.jumpSum X A t ω i
      = ∑ j : Fin K, if θ j ≤ t then coeffs.γ (θ j) (X.X (θ j) ω) (ε j) i else 0 := by
  classical
  have hmt : MeasurableSet (Set.Ioc (0 : ℝ) t ×ˢ A) := measurableSet_Ioc.prod hA
  have hsub : (Set.Ioc (0 : ℝ) T ×ˢ A) ∩ (Set.Ioc (0 : ℝ) t ×ˢ A) = Set.Ioc (0 : ℝ) t ×ˢ A :=
    Set.inter_eq_self_of_subset_right
      (Set.prod_mono (Set.Ioc_subset_Ioc_right ht) le_rfl)
  have hind := hsum ((Set.Ioc (0 : ℝ) t ×ˢ A).indicator
    fun q : ℝ × E => coeffs.γ q.1 (X.X q.1 ω) q.2 i)
  rw [setIntegral_indicator hmt, hsub] at hind
  simp only [LevyStochCalc.Ito.JumpSplitting.jumpSum]
  rw [hind]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : θ j ≤ t
  · have hmemj : ((θ j, ε j) : ℝ × E) ∈ Set.Ioc (0 : ℝ) t ×ˢ A :=
      Set.mem_prod.mpr ⟨Set.mem_Ioc.mpr ⟨(hmem j).1.1, hj⟩, (hmem j).2⟩
    rw [if_pos hj, Set.indicator_of_mem hmemj]
  · have hnot : ((θ j, ε j) : ℝ × E) ∉ Set.Ioc (0 : ℝ) t ×ˢ A := fun hc =>
      hj (Set.mem_Ioc.mp (Set.mem_prod.mp hc).1).2
    rw [if_neg hj, Set.indicator_of_notMem hnot]

/-- Between consecutive arrival times inside the window the jump sum gains exactly the jump
coefficient carried by the later arrival time and its mark. -/
theorem cappedJumpSum_succ_eq_add_gamma (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j))
    (hθ : Function.Injective θ)
    (hrange : Set.range θ
      = {v : ℝ | ∃ i : ℕ, LevyStochCalc.Poisson.jumpTime N A i ω = (v : WithTop ℝ)
          ∧ 0 < v ∧ v ≤ T})
    {k : ℕ}
    (hlt : LevyStochCalc.Poisson.jumpTime N A k ω
      < LevyStochCalc.Poisson.jumpTime N A (k + 1) ω)
    (hle : LevyStochCalc.Poisson.jumpTime N A (k + 1) ω ≤ ((T : ℝ) : WithTop ℝ)) :
    ∃ j : Fin K, LevyStochCalc.Poisson.jumpTime N A (k + 1) ω = ((θ j : ℝ) : WithTop ℝ) ∧
      cappedJumpSum X A T (k + 1) ω
        = cappedJumpSum X A T k ω + coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  classical
  -- The two arrival times are finite reals `q < r ≤ T`, with `0 ≤ q`.
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp
    (hle.trans_lt (WithTop.coe_lt_top T)).ne
  have hkle : LevyStochCalc.Poisson.jumpTime N A k ω ≤ ((r : ℝ) : WithTop ℝ) := by
    rw [hr]; exact hlt.le
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp
    (lt_of_le_of_lt hkle (WithTop.coe_lt_top r)).ne
  have hqr : q < r := by
    have := hlt
    rw [← hq, ← hr] at this
    exact_mod_cast this
  have hrT : r ≤ T := by
    have := hle
    rw [← hr] at this
    exact_mod_cast this
  have hq0 : (0 : ℝ) ≤ q := by
    have := LevyStochCalc.Poisson.coe_zero_le_jumpTime N A k ω
    rw [← hq] at this
    exact_mod_cast this
  have hqT : q ≤ T := le_of_lt (lt_of_lt_of_le hqr hrT)
  have hr0 : (0 : ℝ) < r := lt_of_le_of_lt hq0 hqr
  -- The later arrival time is one of the enumerated atom times.
  have hmemr : r ∈ Set.range θ := by
    rw [hrange]
    exact ⟨k + 1, hr.symm, hr0, hrT⟩
  obtain ⟨j₀, hj₀⟩ := hmemr
  refine ⟨j₀, by rw [← hr, hj₀], ?_⟩
  -- The two capped shifts are the jump sums at `r` and at `q`.
  have hck1 : cappedJumpSum X A T (k + 1) ω
      = LevyStochCalc.Ito.JumpSplitting.jumpSum X A r ω := by
    rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hr.symm, min_eq_right hrT]
  have hck : cappedJumpSum X A T k ω = LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω := by
    rw [cappedJumpSum, LevyStochCalc.Brownian.Ito.clipTime_eq_min hq.symm, min_eq_right hqT]
  -- Only the atom at the later arrival time enters the increment.
  have hkey : ∀ j : Fin K, j ≠ j₀ → (θ j ≤ r ↔ θ j ≤ q) := by
    intro j hj
    constructor
    · intro hjr
      have hmemj : θ j ∈ Set.range θ := Set.mem_range_self j
      rw [hrange] at hmemj
      obtain ⟨i, hi, -, -⟩ := hmemj
      rcases le_or_gt i k with hik | hik
      · have := LevyStochCalc.Poisson.jumpTime_mono N A hik ω
        rw [hi, ← hq] at this
        exact_mod_cast this
      · have := LevyStochCalc.Poisson.jumpTime_mono N A (Nat.succ_le_of_lt hik) ω
        rw [hi, ← hr] at this
        have hrj : r ≤ θ j := by exact_mod_cast this
        exact absurd (hθ (hj₀.trans (le_antisymm hrj hjr))).symm hj
    · intro hjq
      exact le_of_lt (lt_of_le_of_lt hjq hqr)
  funext i
  have h1 := jumpSum_eq_sum_atomEnum X hA hmem hsum hrT i
  have h2 := jumpSum_eq_sum_atomEnum X hA hmem hsum hqT i
  have hdiff : LevyStochCalc.Ito.JumpSplitting.jumpSum X A r ω i
      - LevyStochCalc.Ito.JumpSplitting.jumpSum X A q ω i
      = coeffs.γ (θ j₀) (X.X (θ j₀) ω) (ε j₀) i := by
    rw [h1, h2, ← Finset.sum_sub_distrib]
    refine (Finset.sum_eq_single j₀ ?_ ?_).trans ?_
    · intro j _ hj
      by_cases hjr : θ j ≤ r
      · rw [if_pos hjr, if_pos ((hkey j hj).mp hjr), sub_self]
      · rw [if_neg hjr, if_neg (fun hc => hjr ((hkey j hj).mpr hc)), sub_self]
    · intro hj
      exact absurd (Finset.mem_univ j₀) hj
    · rw [if_pos (le_of_eq hj₀), if_neg (by rw [hj₀]; exact not_le.mpr hqr), sub_zero]
  rw [hck1, hck]
  simp only [Pi.add_apply]
  linarith

/-- The jump sum over the whole enumerated window is the sum of the jump coefficient over the
enumerated atoms. -/
theorem jumpSum_eq_sum_atomEnum_horizon (hA : MeasurableSet A)
    (hmem : ∀ j : Fin K, θ j ∈ Set.Ioc (0 : ℝ) T ∧ ε j ∈ A)
    (hsum : ∀ g : ℝ × E → ℝ,
      ∫ p in Set.Ioc (0 : ℝ) T ×ˢ A, g p ∂(N.N ω) = ∑ j : Fin K, g (θ j, ε j)) :
    LevyStochCalc.Ito.JumpSplitting.jumpSum X A T ω
      = ∑ j : Fin K, coeffs.γ (θ j) (X.X (θ j) ω) (ε j) := by
  classical
  funext i
  rw [Finset.sum_apply, jumpSum_eq_sum_atomEnum X hA hmem hsum le_rfl i]
  exact Finset.sum_congr rfl fun j _ => if_pos (hmem j).1.2

end MarkIdentification

end LevyStochCalc.Ito.JumpFormula
