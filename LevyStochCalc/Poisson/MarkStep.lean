/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Poisson.CompensatedDensity

/-!
# Mark-step integrands and their compensated integrals

A *mark-step integrand* is a finite sum `∑ᵢ 𝟙_{(pᵢ, pᵢ₊₁]}(s) ∑ₖ ξᵢₖ(ω) 𝟙_{Bₖ}(e)` over a
time grid `0 = p₀ < ⋯ < p_{N₀}` and finitely many mark sets `Bₖ` of finite `ν`-measure, with
bounded coefficients `ξᵢₖ`. Its compensated integral up to time `t` is
`∑ᵢ ∑ₖ ξᵢₖ Ñ((pᵢ ∧ t, pᵢ₊₁ ∧ t] × Bₖ)`.

The grid is a separate object (`TimeGrid`) so that integrands on a common grid can be
added; a grid can be clamped at a time `t` (`TimeGrid.clamp`), which expresses the
integral up to `t` as the integral over the whole clamped horizon and thereby gives the
`L²` isometry at every time from the horizon isometry.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- A finite time grid `0 = p 0 < p 1 < ⋯ < p N₀`; values of `p` beyond `N₀` are
irrelevant. -/
structure TimeGrid where
  /-- Number of pieces. -/
  N₀ : ℕ
  /-- The grid points. -/
  p : ℕ → ℝ
  p_zero : p 0 = 0
  p_lt : ∀ i, i < N₀ → p i < p (i + 1)

namespace TimeGrid

variable (g : TimeGrid)

lemma p_mono {i j : ℕ} (hij : i ≤ j) (hj : j ≤ g.N₀) : g.p i ≤ g.p j := by
  induction hij with
  | refl => exact le_rfl
  | step h ih =>
    exact (ih (Nat.le_of_succ_le hj)).trans (g.p_lt _ (Nat.lt_of_succ_le hj)).le

lemma p_strictMono {i j : ℕ} (hij : i < j) (hj : j ≤ g.N₀) : g.p i < g.p j :=
  (g.p_lt i (lt_of_lt_of_le hij hj)).trans_le (g.p_mono (Nat.succ_le_of_lt hij) hj)

lemma p_nonneg {i : ℕ} (hi : i ≤ g.N₀) : 0 ≤ g.p i := by
  have := g.p_mono (Nat.zero_le i) hi
  rwa [g.p_zero] at this

/-- The grid as a strictly monotone map on `Fin (N₀ + 1)`. -/
lemma strictMono_fin : StrictMono (fun i : Fin (g.N₀ + 1) => g.p i) := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  simp only [Fin.val_castSucc, Fin.val_succ]
  exact g.p_lt i i.isLt

/-- The horizon of the grid. -/
def horizon : ℝ := g.p g.N₀

lemma horizon_nonneg : 0 ≤ g.horizon := g.p_nonneg le_rfl

end TimeGrid

/-- A mark-step integrand on the time grid `g`: mark sets `B k` of finite `ν`-measure and
bounded measurable coefficients `ξ i k` for each piece `i` and mark `k`. Coefficients
with `N₀ ≤ i` are irrelevant. -/
structure MarkStep (Ω : Type u) [MeasurableSpace Ω] (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] (g : TimeGrid) where
  /-- Number of mark sets. -/
  K : ℕ
  /-- The mark sets. -/
  B : Fin K → Set E
  B_measurable : ∀ k, MeasurableSet (B k)
  B_finite : ∀ k, ν (B k) ≠ ⊤
  /-- The coefficients. -/
  ξ : ℕ → Fin K → Ω → ℝ
  ξ_bounded : ∀ i k, ∃ M : ℝ, ∀ ω, |ξ i k ω| ≤ M
  ξ_measurable : ∀ i k, Measurable (ξ i k)

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The compensated integral of a mark-step integrand up to time `t`. -/
noncomputable def integral (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range g.N₀, ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω

/-- The compensated integral of a mark-step integrand over its whole horizon. -/
noncomputable def full (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range g.N₀, ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω

/-- The integrand as a function of time, mark and sample point. -/
noncomputable def eval (G : MarkStep Ω E ν g) (s : ℝ) (e : E) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range g.N₀, (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
    * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e

/-- Adaptedness of the coefficients to the natural filtration at the left endpoints of
their pieces. -/
def Adapted (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) : Prop :=
  ∀ i, i < g.N₀ → ∀ k,
    @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (g.p i)) (G.ξ i k)

variable (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)

lemma full_eq_fin (ω : Ω) :
    G.full N ω = ∑ i : Fin g.N₀, ∑ k, G.ξ i k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω :=
  (Fin.sum_univ_eq_sum_range (fun i => ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω) g.N₀).symm

lemma eval_eq_fin (s : ℝ) (e : E) (ω : Ω) :
    G.eval s e ω = ∑ i : Fin g.N₀,
      (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
        * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e :=
  (Fin.sum_univ_eq_sum_range (fun i =>
    (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
      * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e) g.N₀).symm

/-- The compensated integral of an empty time interval vanishes. -/
lemma compensated_Ioc_self (a : ℝ) (B : Set E) (ω : Ω) :
    N.compensated (Set.Ioc a a ×ˢ B) ω = 0 := by
  rw [Set.Ioc_self, Set.empty_prod]
  show (N.N ω ∅).toReal - (referenceIntensity ν ∅).toReal = 0
  simp

/-- Past the horizon, the integral up to `t` is the integral over the whole horizon. -/
lemma integral_eq_full_of_horizon_le {t : ℝ} (ht : g.horizon ≤ t) (ω : Ω) :
    G.integral N t ω = G.full N ω := by
  unfold integral full
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [min_eq_left ((g.p_mono hi.le le_rfl).trans ht),
    min_eq_left ((g.p_mono hi le_rfl).trans ht)]

/-- The integral up to a nonpositive time vanishes. -/
lemma integral_eq_zero_of_nonpos {t : ℝ} (ht : t ≤ 0) (ω : Ω) : G.integral N t ω = 0 := by
  unfold integral
  refine Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun k _ => ?_
  rw [Finset.mem_range] at hi
  rw [min_eq_right (ht.trans (g.p_nonneg hi.le)), min_eq_right (ht.trans (g.p_nonneg hi)),
    compensated_Ioc_self, mul_zero]

/-- The `k`-th mark of a mark-step integrand as a simple predictable integrand. -/
noncomputable def toSimple (k : Fin G.K) : SimplePredictable Ω E ν g.horizon where
  N := g.N₀
  partition := fun i => g.p i
  partition_zero := by simp [g.p_zero]
  partition_le_T := by simp [TimeGrid.horizon]
  partition_strictMono := g.strictMono_fin
  A := fun _ => G.B k
  A_measurable := fun _ => G.B_measurable k
  A_finite := fun _ => G.B_finite k
  ξ := fun i => G.ξ i k
  ξ_bounded := fun i => G.ξ_bounded i k
  ξ_measurable := fun i => G.ξ_measurable i k

lemma integral_eq_stepIntegral (t : ℝ) (ω : Ω) :
    G.integral N t ω = stepIntegral N G.toSimple t ω := by
  unfold integral stepIntegral simpleIntegral
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun i => G.ξ i k ω
    * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω) g.N₀]
  rfl

/-- The compensated integral of an adapted mark-step integrand is a martingale on the
natural filtration. -/
lemma martingale_integral (hG : G.Adapted N) :
    Martingale (fun t => G.integral N t) (naturalFiltration N) P := by
  have hfun : (fun t => G.integral N t) = fun t => stepIntegral N G.toSimple t :=
    funext fun t => funext fun ω => G.integral_eq_stepIntegral N t ω
  rw [hfun]
  exact martingale_stepIntegral_compensated N G.toSimple (fun k i => hG i i.isLt k)

/-- The compensated integral of a mark-step integrand up to any time is square
integrable. -/
lemma memLp_integral (t : ℝ) : MemLp (fun ω => G.integral N t ω) 2 P := by
  have : (fun ω => G.integral N t ω) = fun ω => ∑ k, simpleIntegral N (G.toSimple k) t ω := by
    funext ω
    exact G.integral_eq_stepIntegral N t ω
  rw [this]
  exact memLp_finsetSum _ fun k _ => simpleIntegral_memLp_at N (G.toSimple k) t

lemma memLp_full : MemLp (fun ω => G.full N ω) 2 P := by
  have : (fun ω => G.full N ω) = fun ω => G.integral N g.horizon ω := by
    funext ω
    exact (G.integral_eq_full_of_horizon_le N le_rfl ω).symm
  rw [this]
  exact G.memLp_integral N _

/-- The `L²` isometry of the compensated integral over the whole horizon. -/
theorem integral_full_sq (hG : G.Adapted N) {T : ℝ} (hT : g.horizon ≤ T) :
    ∫ ω, (G.full N ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T, (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have key := markSumProcess_isometry_L2 (fun i : Fin (g.N₀ + 1) => g.p i)
    (by simp [g.p_zero]) g.strictMono_fin (T := T) (by simpa [TimeGrid.horizon] using hT) N G.B
    G.B_measurable G.B_finite (fun i k => G.ξ i k) (fun i k => G.ξ_bounded i k)
    (fun i k => G.ξ_measurable i k) (fun i k => hG i i.isLt k)
  simp only [Fin.val_castSucc, Fin.val_succ] at key
  simp_rw [full_eq_fin, eval_eq_fin]
  exact key

end MarkStep

namespace TimeGrid

variable (g : TimeGrid)

open Classical in
/-- The index of the first grid point at or after `t`, capped at `N₀`. -/
noncomputable def clampIndex (t : ℝ) : ℕ :=
  Nat.find (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ t ≤ g.p i)

open Classical in
lemma clampIndex_le (t : ℝ) : g.clampIndex t ≤ g.N₀ := Nat.find_le (Or.inl le_rfl)

open Classical in
lemma lt_of_lt_clampIndex {t : ℝ} {i : ℕ} (hi : i < g.clampIndex t) :
    i < g.N₀ ∧ g.p i < t := by
  have := Nat.find_min (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ t ≤ g.p i) hi
  exact ⟨not_le.1 fun h => this (Or.inl h), not_le.1 fun h => this (Or.inr h)⟩

open Classical in
lemma le_p_of_clampIndex_le {t : ℝ} {i : ℕ} (hi : g.clampIndex t ≤ i) (hiN : i < g.N₀) :
    t ≤ g.p i := by
  have hspec := Nat.find_spec (⟨g.N₀, Or.inl le_rfl⟩ : ∃ i, g.N₀ ≤ i ∨ t ≤ g.p i)
  rcases hspec with h | h
  · exact absurd (lt_of_le_of_lt hi hiN) (not_lt.2 h)
  · exact h.trans (g.p_mono hi hiN.le)

/-- The grid clamped at a time `t ≥ 0`: the pieces starting before `t`, the last grid
point being cut at `t`. -/
noncomputable def clamp (t : ℝ) (ht : 0 ≤ t) : TimeGrid where
  N₀ := g.clampIndex t
  p := fun i => min (g.p i) t
  p_zero := by simp [g.p_zero, ht]
  p_lt := fun i hi => by
    obtain ⟨hiN, hpi⟩ := g.lt_of_lt_clampIndex hi
    show min (g.p i) t < min (g.p (i + 1)) t
    rw [min_eq_left hpi.le]
    exact lt_min (g.p_lt i hiN) hpi

lemma clamp_p_of_lt {t : ℝ} (ht : 0 ≤ t) {i : ℕ} (hi : i < (g.clamp t ht).N₀) :
    (g.clamp t ht).p i = g.p i :=
  min_eq_left (g.lt_of_lt_clampIndex hi).2.le

lemma clamp_horizon_le (t : ℝ) (ht : 0 ≤ t) : (g.clamp t ht).horizon ≤ t :=
  min_le_right _ _

lemma clampIndex_p {b : ℕ} (hb : b ≤ g.N₀) : g.clampIndex (g.p b) = b := by
  refine le_antisymm (not_lt.1 fun h => ?_) (not_lt.1 fun h => ?_)
  · exact lt_irrefl _ (g.lt_of_lt_clampIndex h).2
  · rcases Nat.lt_or_ge (g.clampIndex (g.p b)) g.N₀ with h' | h'
    · exact absurd (g.le_p_of_clampIndex_le le_rfl h') (not_le.2 (g.p_strictMono h hb))
    · exact absurd (lt_of_lt_of_le h hb) (not_lt.2 h')

end TimeGrid

namespace MarkStep

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} {N : PoissonRandomMeasure P ν} {G : MarkStep Ω E ν g}

/-- A mark-step integrand transported to the clamped grid. -/
def clamp (G : MarkStep Ω E ν g) (t : ℝ) (ht : 0 ≤ t) : MarkStep Ω E ν (g.clamp t ht) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable

lemma integral_eq_full_clamp (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) (t : ℝ)
    (ht : 0 ≤ t) (ω : Ω) : G.integral N t ω = (G.clamp t ht).full N ω := by
  unfold integral full
  symm
  refine Finset.sum_subset
    (Finset.range_subset.2 fun i hi => Finset.mem_range.2 (lt_of_lt_of_le hi (g.clampIndex_le t)))
    ?_
  intro i hi hni
  rw [Finset.mem_range] at hi hni
  have hti := g.le_p_of_clampIndex_le (not_lt.1 hni) hi
  refine Finset.sum_eq_zero fun k _ => ?_
  show G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω = 0
  rw [min_eq_right hti, min_eq_right (hti.trans (g.p_mono (Nat.le_succ i) hi)),
    compensated_Ioc_self, mul_zero]

lemma eval_clamp (G : MarkStep Ω E ν g) (t : ℝ) (ht : 0 ≤ t) (s : ℝ) (e : E) (ω : Ω) :
    (G.clamp t ht).eval s e ω = if s ≤ t then G.eval s e ω else 0 := by
  unfold eval
  split_ifs with hst
  · symm
    calc ∑ i ∈ Finset.range g.N₀,
          (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
        = ∑ i ∈ Finset.range (g.clampIndex t),
          (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
          symm
          refine Finset.sum_subset (Finset.range_subset.2 fun i hi =>
            Finset.mem_range.2 (lt_of_lt_of_le hi (g.clampIndex_le t))) ?_
          intro i hi hni
          rw [Finset.mem_range] at hi hni
          have hti := g.le_p_of_clampIndex_le (not_lt.1 hni) hi
          rw [Set.indicator_of_notMem, zero_mul]
          intro hs
          exact absurd (hst.trans hti) (not_le.2 hs.1)
      _ = ∑ i ∈ Finset.range (g.clampIndex t),
          (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t)).indicator (fun _ => (1 : ℝ)) s
            * ∑ k, G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
          refine Finset.sum_congr rfl fun i hi => ?_
          rw [Finset.mem_range] at hi
          have hpi := (g.lt_of_lt_clampIndex hi).2
          congr 1
          rw [min_eq_left hpi.le]
          by_cases hs : s ∈ Set.Ioc (g.p i) (g.p (i + 1))
          · rw [Set.indicator_of_mem hs, Set.indicator_of_mem
              (show s ∈ Set.Ioc (g.p i) (min (g.p (i + 1)) t) from ⟨hs.1, le_min hs.2 hst⟩)]
          · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem]
            intro hs'
            exact hs ⟨hs'.1, hs'.2.trans (min_le_left _ _)⟩
  · refine Finset.sum_eq_zero fun i _ => ?_
    rw [Set.indicator_of_notMem, zero_mul]
    intro hs
    exact hst (hs.2.trans (min_le_right _ _))

lemma Adapted.clamp (hG : G.Adapted N) (t : ℝ) (ht : 0 ≤ t) :
    (G.clamp t ht).Adapted N := by
  intro i hi k
  have h := hG i (g.lt_of_lt_clampIndex hi).1 k
  show @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (min (g.p i) t)) (G.ξ i k)
  rwa [min_eq_left (g.lt_of_lt_clampIndex hi).2.le]

/-- The `L²` isometry of the compensated integral up to any time `t ≥ 0`. -/
theorem integral_sq_at (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g)
    (hG : G.Adapted N) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (G.integral N t ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t, (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  simp_rw [G.integral_eq_full_clamp N t ht]
  rw [(G.clamp t ht).integral_full_sq N (hG.clamp t ht) (g.clamp_horizon_le t ht)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [G.eval_clamp t ht, if_pos hs.2]

section Eval

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid} (G : MarkStep Ω E ν g)

lemma abs_indicator_one_le {α : Type*} (s : Set α) (x : α) :
    |s.indicator (fun _ => (1 : ℝ)) x| ≤ 1 := by
  by_cases h : x ∈ s <;> simp [h]

/-- The integrand is jointly measurable in sample point, time and mark. -/
lemma eval_measurable : Measurable (fun q : Ω × ℝ × E => G.eval q.2.1 q.2.2 q.1) := by
  unfold eval
  refine Finset.measurable_sum _ fun i _ => Measurable.mul ?_ (Finset.measurable_sum _ fun k _ =>
    Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator measurableSet_Ioc).comp (measurable_fst.comp measurable_snd)
  · exact (G.ξ_measurable i k).comp measurable_fst
  · exact (measurable_const.indicator (G.B_measurable k)).comp (measurable_snd.comp measurable_snd)

/-- The integrand is bounded. -/
lemma eval_bounded : ∃ C : ℝ, ∀ ω s e, |G.eval s e ω| ≤ C := by
  choose M hM using G.ξ_bounded
  refine ⟨∑ i ∈ Finset.range g.N₀, ∑ k, |M i k|, fun ω s e => ?_⟩
  unfold eval
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  refine (mul_le_of_le_one_left (abs_nonneg _) (abs_indicator_one_le _ _)).trans ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) (abs_indicator_one_le _ _)).trans
    ((hM i k ω).trans (le_abs_self _))

/-- The integrand vanishes off the union of the mark sets. -/
lemma eval_support (ω : Ω) (s : ℝ) (e : E) (he : e ∉ ⋃ k, G.B k) : G.eval s e ω = 0 := by
  unfold eval
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.sum_eq_zero fun k _ => ?_, mul_zero]
  rw [Set.indicator_of_notMem (fun hk => he (Set.mem_iUnion.2 ⟨k, hk⟩)), mul_zero]

lemma measurableSet_iUnion_B : MeasurableSet (⋃ k, G.B k) :=
  MeasurableSet.iUnion fun k => G.B_measurable k

lemma measure_iUnion_B_ne_top : ν (⋃ k, G.B k) ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.sum_ne_top.2 fun k _ => G.B_finite k)
    (measure_iUnion_fintype_le ν G.B)

variable (N : PoissonRandomMeasure P ν)

/-- The `L²` isometry over the whole horizon, in `ℝ≥0∞` form. -/
theorem lintegral_full_sq (hG : G.Adapted N) {T : ℝ} (hT : g.horizon ≤ T) :
    ∫⁻ ω, (‖G.full N ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  obtain ⟨C, hC⟩ := G.eval_bounded
  rw [lintegral_sq_eq_ofReal_integral (G.memLp_full N), G.integral_full_sq N hG hT]
  exact triple_ofReal_integral_eq_lintegral (fun ω s e => G.eval s e ω) G.eval_measurable hC
    G.measurableSet_iUnion_B G.measure_iUnion_B_ne_top (fun ω s e he => G.eval_support ω s e he)

/-- The `L²` isometry up to any time `t ≥ 0`, in `ℝ≥0∞` form. -/
theorem lintegral_integral_sq_at (hG : G.Adapted N) {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  simp_rw [G.integral_eq_full_clamp N t ht]
  rw [(G.clamp t ht).lintegral_full_sq N (hG.clamp t ht) (g.clamp_horizon_le t ht)]
  refine lintegral_congr fun ω => lintegral_congr fun e => ?_
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  rw [G.eval_clamp t ht, if_pos hs.2]

end Eval

section Append

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The sum of two mark-step integrands on a common grid, by concatenating their marks. -/
def append (G G' : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K + G'.K
  B := Fin.append G.B G'.B
  B_measurable := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_measurable k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_measurable k) k
  B_finite := fun k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.B_finite k) (fun k => by
    simp only [Fin.append_right]; exact G'.B_finite k) k
  ξ := fun i => Fin.append (G.ξ i) (G'.ξ i)
  ξ_bounded := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_bounded i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_bounded i k) k
  ξ_measurable := fun i k => Fin.addCases (fun k => by
    simp only [Fin.append_left]; exact G.ξ_measurable i k) (fun k => by
    simp only [Fin.append_right]; exact G'.ξ_measurable i k) k

/-- The negative of a mark-step integrand. -/
def neg (G : MarkStep Ω E ν g) : MarkStep Ω E ν g where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => -G.ξ i k ω
  ξ_bounded := fun i k => by
    obtain ⟨M, hM⟩ := G.ξ_bounded i k
    exact ⟨M, fun ω => by rw [abs_neg]; exact hM ω⟩
  ξ_measurable := fun i k => (G.ξ_measurable i k).neg

variable (N : PoissonRandomMeasure P ν) (G G' : MarkStep Ω E ν g)

lemma integral_append (t : ℝ) (ω : Ω) :
    (G.append G').integral N t ω = G.integral N t ω + G'.integral N t ω := by
  unfold integral
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t)
        ×ˢ Fin.append G.B G'.B k) ω = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma full_append (ω : Ω) : (G.append G').full N ω = G.full N ω + G'.full N ω := by
  unfold full
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  show ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ Fin.append G.B G'.B k) ω = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma eval_append (s : ℝ) (e : E) (ω : Ω) :
    (G.append G').eval s e ω = G.eval s e ω + G'.eval s e ω := by
  unfold eval
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_add]
  congr 1
  show ∑ k : Fin (G.K + G'.K), Fin.append (G.ξ i) (G'.ξ i) k ω
      * (Fin.append G.B G'.B k).indicator (fun _ => (1 : ℝ)) e = _
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

lemma Adapted.append {N : PoissonRandomMeasure P ν} {G G' : MarkStep Ω E ν g}
    (hG : G.Adapted N) (hG' : G'.Adapted N) : (G.append G').Adapted N := by
  intro i hi k
  refine Fin.addCases (fun k => ?_) (fun k => ?_) k
  · show @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.castAdd _ k))
    rw [Fin.append_left]
    exact hG i hi k
  · show @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (g.p i))
      (Fin.append (G.ξ i) (G'.ξ i) (Fin.natAdd _ k))
    rw [Fin.append_right]
    exact hG' i hi k

lemma integral_neg (t : ℝ) (ω : Ω) : G.neg.integral N t ω = -G.integral N t ω := by
  unfold integral
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  show -G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω
    = -(G.ξ i k ω * N.compensated (Set.Ioc (min (g.p i) t) (min (g.p (i + 1)) t) ×ˢ G.B k) ω)
  exact neg_mul _ _

lemma full_neg (ω : Ω) : G.neg.full N ω = -G.full N ω := by
  unfold full
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  show -G.ξ i k ω * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω
    = -(G.ξ i k ω * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω)
  exact neg_mul _ _

lemma eval_neg (s : ℝ) (e : E) (ω : Ω) : G.neg.eval s e ω = -G.eval s e ω := by
  unfold eval
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  show -G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e
    = -(G.ξ i k ω * (G.B k).indicator (fun _ => (1 : ℝ)) e)
  exact neg_mul _ _

lemma Adapted.neg {N : PoissonRandomMeasure P ν} {G : MarkStep Ω E ν g} (hG : G.Adapted N) :
    G.neg.Adapted N := fun i hi k => (hG i hi k).neg

/-- The `L²` distance of the compensated integrals of two adapted mark-step integrands on
a common grid, up to time `t ≥ 0`, is the `L²` distance of the integrands. -/
theorem integral_sub_sq_at (hG : G.Adapted N) (hG' : G'.Adapted N) {t : ℝ} (ht : 0 ≤ t) :
    ∫ ω, (G.integral N t ω - G'.integral N t ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) t,
          (G.eval s e ω - G'.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have key := (G.append G'.neg).integral_sq_at N (hG.append hG'.neg) ht
  simp only [integral_append, integral_neg, eval_append, eval_neg, ← sub_eq_add_neg] at key
  exact key

/-- The `L²` distance of the compensated integrals of two adapted mark-step integrands on
a common grid, up to time `t ≥ 0`, in `ℝ≥0∞` form. -/
theorem lintegral_integral_sub_sq_at (hG : G.Adapted N) (hG' : G'.Adapted N) {t : ℝ}
    (ht : 0 ≤ t) :
    ∫⁻ ω, (‖G.integral N t ω - G'.integral N t ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ e, ∫⁻ s in Set.Icc (0 : ℝ) t,
          (‖G.eval s e ω - G'.eval s e ω‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂ν ∂P := by
  have key := (G.append G'.neg).lintegral_integral_sq_at N (hG.append hG'.neg) ht
  simp only [integral_append, integral_neg, eval_append, eval_neg, ← sub_eq_add_neg] at key
  exact key

end Append

section Weight

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]
  {g : TimeGrid}

/-- The mark-step integrand whose coefficients on the pieces from index `a` on are
multiplied by a bounded measurable weight `w`, and whose earlier coefficients vanish. -/
def weight (G : MarkStep Ω E ν g) (w : Ω → ℝ) (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C)
    (hwm : Measurable w) (a : ℕ) : MarkStep Ω E ν g where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k ω => if a ≤ i then w ω * G.ξ i k ω else 0
  ξ_bounded := fun i k => by
    obtain ⟨C, hC⟩ := hw
    obtain ⟨M, hM⟩ := G.ξ_bounded i k
    refine ⟨|C| * |M|, fun ω => ?_⟩
    split_ifs
    · rw [abs_mul]
      exact mul_le_mul ((hC ω).trans (le_abs_self C)) ((hM ω).trans (le_abs_self M))
        (abs_nonneg _) (abs_nonneg _)
    · rw [abs_zero]
      positivity
  ξ_measurable := fun i k => by
    by_cases h : a ≤ i
    · simp only [h, if_true]
      exact hwm.mul (G.ξ_measurable i k)
    · simp only [h, if_false]
      exact measurable_const

variable (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν g) {w : Ω → ℝ}
  (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w)

include hw hwm in
lemma Adapted.weight {N : PoissonRandomMeasure P ν} {G : MarkStep Ω E ν g} (hG : G.Adapted N)
    {a : ℕ} (hwa : @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (g.p a)) w) :
    (G.weight w hw hwm a).Adapted N := by
  intro i hi k
  show @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (g.p i))
    (fun ω => if a ≤ i then w ω * G.ξ i k ω else 0)
  by_cases h : a ≤ i
  · simp only [h, if_true]
    exact (hwa.mono ((naturalFiltration N).mono (g.p_mono h hi.le))).mul (hG i hi k)
  · simp only [h, if_false]
    exact stronglyMeasurable_const

/-- The integral of a mark-step integrand up to a grid point, as a sum over the pieces
before it. -/
lemma integral_p_eq (b : ℕ) (hb : b ≤ g.N₀) (ω : Ω) :
    G.integral N (g.p b) ω = ∑ i ∈ Finset.range b, ∑ k, G.ξ i k ω
      * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω := by
  unfold integral
  refine (Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi hb)) ?_).symm.trans
    (Finset.sum_congr rfl fun i hi => ?_)
  · intro i hi hni
    rw [Finset.mem_range] at hi hni
    have hti : g.p b ≤ g.p i := g.p_mono (not_lt.1 hni) hi.le
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [min_eq_right hti, min_eq_right (hti.trans (g.p_mono (Nat.le_succ i) hi)),
      compensated_Ioc_self, mul_zero]
  · rw [Finset.mem_range] at hi
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb)]

/-- The weighted increment of the integral between two grid points, as the integral of
the weighted integrand over the clamped horizon. -/
lemma full_weight_clamp {a b : ℕ} (hab : a ≤ b) (hb : b ≤ g.N₀) (ω : Ω) :
    ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).full N ω
      = w ω * (G.integral N (g.p b) ω - G.integral N (g.p a) ω) := by
  rw [G.integral_p_eq N b hb, G.integral_p_eq N a (hab.trans hb)]
  have hN : (g.clamp (g.p b) (g.p_nonneg hb)).N₀ = b := g.clampIndex_p hb
  unfold full
  rw [hN]
  show ∑ i ∈ Finset.range b, ∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
      * N.compensated (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b)) ×ˢ G.B k) ω
    = _
  set F : ℕ → ℝ := fun i => ∑ k, G.ξ i k ω
    * N.compensated (Set.Ioc (g.p i) (g.p (i + 1)) ×ˢ G.B k) ω with hF
  have hL : ∀ i ∈ Finset.range b, (∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
      * N.compensated (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b)) ×ˢ G.B k) ω)
      = if a ≤ i then w ω * F i else 0 := by
    intro i hi
    rw [Finset.mem_range] at hi
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb), hF]
    split_ifs
    · simp only [Finset.mul_sum, mul_assoc]
    · simp
  rw [Finset.sum_congr rfl hL]
  have h2 : ∑ i ∈ Finset.range b, (if a ≤ i then 0 else w ω * F i)
      = ∑ i ∈ Finset.range a, w ω * F i := by
    refine (Finset.sum_subset (Finset.range_subset.2 fun i hi =>
      Finset.mem_range.2 (lt_of_lt_of_le hi hab)) ?_).symm.trans
      (Finset.sum_congr rfl fun i hi => ?_)
    · intro i hi hni
      rw [Finset.mem_range] at hni
      simp [not_lt.1 hni]
    · rw [Finset.mem_range] at hi
      simp [not_le.2 hi]
  have hsplit : ∑ i ∈ Finset.range b, (if a ≤ i then w ω * F i else 0)
      + ∑ i ∈ Finset.range a, w ω * F i = ∑ i ∈ Finset.range b, w ω * F i := by
    rw [← h2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [mul_sub, Finset.mul_sum, Finset.mul_sum]
  linarith [hsplit]

/-- The integrand of the weighted clamped integrand. -/
lemma eval_weight_clamp {a b : ℕ} (hab : a ≤ b) (hb : b ≤ g.N₀) (s : ℝ) (e : E) (ω : Ω) :
    ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).eval s e ω
      = if g.p a < s ∧ s ≤ g.p b then w ω * G.eval s e ω else 0 := by
  have hN : (g.clamp (g.p b) (g.p_nonneg hb)).N₀ = b := g.clampIndex_p hb
  have hL : ((G.clamp (g.p b) (g.p_nonneg hb)).weight w hw hwm a).eval s e ω
      = ∑ i ∈ Finset.range b, (Set.Ioc (g.p i) (g.p (i + 1))).indicator (fun _ => (1 : ℝ)) s
        * ∑ k, (if a ≤ i then w ω * G.ξ i k ω else 0)
          * (G.B k).indicator (fun _ => (1 : ℝ)) e := by
    unfold eval
    rw [hN]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    show (Set.Ioc (min (g.p i) (g.p b)) (min (g.p (i + 1)) (g.p b))).indicator
        (fun _ => (1 : ℝ)) s * _ = _
    rw [min_eq_left (g.p_mono hi.le hb), min_eq_left (g.p_mono hi hb)]
    rfl
  rw [hL]
  split_ifs with hs
  · unfold eval
    rw [Finset.mul_sum]
    refine (Finset.sum_congr rfl fun i hi => ?_).trans (Finset.sum_subset
      (Finset.range_subset.2 fun i hi => Finset.mem_range.2 (lt_of_lt_of_le hi hb)) ?_)
    · rw [Finset.mem_range] at hi
      by_cases hai : a ≤ i
      · simp only [hai, if_true, Finset.mul_sum, mul_assoc]
        ring_nf
      · have hs0 : s ∉ Set.Ioc (g.p i) (g.p (i + 1)) := fun hs' =>
          absurd (hs'.2.trans (g.p_mono (Nat.succ_le_of_lt (not_le.1 hai)) (hab.trans hb)))
            (not_le.2 hs.1)
        rw [Set.indicator_of_notMem hs0]
        simp
    · intro i hi hni
      rw [Finset.mem_range] at hi hni
      rw [Set.indicator_of_notMem, zero_mul, mul_zero]
      intro hs'
      exact absurd (hs.2.trans (g.p_mono (not_lt.1 hni) hi.le)) (not_le.2 hs'.1)
  · refine Finset.sum_eq_zero fun i hi => ?_
    rw [Finset.mem_range] at hi
    by_cases hai : a ≤ i
    · rw [Set.indicator_of_notMem, zero_mul]
      intro hs'
      exact hs ⟨(g.p_mono hai (hi.le.trans hb)).trans_lt hs'.1, hs'.2.trans (g.p_mono hi hb)⟩
    · simp [hai]

/-- The set-level `L²` isometry of the increment of the integral between two grid points,
against a bounded weight measurable at the earlier grid point. -/
theorem integral_weight_increment_sq (hG : G.Adapted N) {w : Ω → ℝ}
    (hw : ∃ C : ℝ, ∀ ω, |w ω| ≤ C) (hwm : Measurable w) {a b : ℕ} (hab : a ≤ b)
    (hb : b ≤ g.N₀)
    (hwa : @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (g.p a)) w) :
    ∫ ω, (w ω * (G.integral N (g.p b) ω - G.integral N (g.p a) ω)) ^ 2 ∂P
      = ∫ ω, (w ω) ^ 2 * (∫ e, ∫ s in Set.Ioc (g.p a) (g.p b),
          (G.eval s e ω) ^ 2 ∂volume ∂ν) ∂P := by
  have hb0 := g.p_nonneg hb
  have hwa' : @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq
      ((g.clamp (g.p b) hb0).p a)) w := by
    show @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq (min (g.p a) (g.p b))) w
    rwa [min_eq_left (g.p_mono hab hb)]
  have key := ((G.clamp (g.p b) hb0).weight w hw hwm a).integral_full_sq N
    ((hG.clamp (g.p b) hb0).weight hw hwm hwa') (g.clamp_horizon_le (g.p b) hb0)
  simp_rw [G.full_weight_clamp N hw hwm hab hb, G.eval_weight_clamp hw hwm hab hb] at key
  rw [key]
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  beta_reduce
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun e => ?_)
  beta_reduce
  rw [← integral_const_mul]
  have hsub : Set.Ioc (g.p a) (g.p b) ⊆ Set.Icc 0 (g.p b) := fun s hs =>
    ⟨(g.p_nonneg (hab.trans hb)).trans hs.1.le, hs.2⟩
  rw [← Set.inter_eq_self_of_subset_right hsub, ← setIntegral_indicator measurableSet_Ioc]
  refine setIntegral_congr_fun measurableSet_Icc fun s _ => ?_
  by_cases hs : s ∈ Set.Ioc (g.p a) (g.p b)
  · rw [Set.indicator_of_mem hs, if_pos (Set.mem_Ioc.1 hs)]
    ring
  · rw [Set.indicator_of_notMem hs, if_neg (fun h => hs (Set.mem_Ioc.2 h))]
    ring

end Weight

section Dyadic

variable {ν : Measure E} [SigmaFinite ν] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The dyadic grid of level `n` on `[0, T]`. -/
noncomputable def _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic (T : ℝ) (hT : 0 < T)
    (n : ℕ) : TimeGrid where
  N₀ := 2 ^ n
  p := fun i => (i : ℝ) * T / (2 ^ n : ℕ)
  p_zero := by simp
  p_lt := fun i _ => by
    have h : (0 : ℝ) < (2 ^ n : ℕ) := by positivity
    rw [div_lt_div_iff_of_pos_right h]
    push_cast
    nlinarith

lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_horizon (T : ℝ) (hT : 0 < T)
    (n : ℕ) : (TimeGrid.dyadic T hT n).horizon = T := by
  show ((2 ^ n : ℕ) : ℝ) * T / (2 ^ n : ℕ) = T
  field_simp

lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_p_castSucc (T : ℝ) (hT : 0 < T)
    (n : ℕ) (i : Fin (2 ^ n)) :
    (TimeGrid.dyadic T hT n).p i = dyadicPartition T n i.castSucc := rfl

lemma _root_.LevyStochCalc.Poisson.Compensated.TimeGrid.dyadic_p_succ (T : ℝ) (hT : 0 < T)
    (n : ℕ) (i : Fin (2 ^ n)) :
    (TimeGrid.dyadic T hT n).p (i + 1) = dyadicPartition T n i.succ := rfl

variable {T : ℝ} {hT : 0 < T} {n m : ℕ}

/-- A mark-step integrand on the level-`n` dyadic grid, re-expressed on the level-`m`
dyadic grid (`n ≤ m`): each fine piece inherits the coefficients of the coarse piece
containing it. -/
def dyadicRefine (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)) (_hnm : n ≤ m) :
    MarkStep Ω E ν (TimeGrid.dyadic T hT m) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := fun i k => G.ξ (i / 2 ^ (m - n)) k
  ξ_bounded := fun _ k => G.ξ_bounded _ k
  ξ_measurable := fun _ k => G.ξ_measurable _ k

variable (N : PoissonRandomMeasure P ν) (G : MarkStep Ω E ν (TimeGrid.dyadic T hT n))
  (hnm : n ≤ m)

lemma full_dyadicRefine : (fun ω => (G.dyadicRefine hnm).full N ω) =ᵐ[P] fun ω => G.full N ω := by
  have h := stepIntegral_dyadic_refine_integral N hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) (fun _ k => G.B_measurable k) (fun _ k => G.B_finite k)
  filter_upwards [h] with ω hω
  rw [full_eq_fin, full_eq_fin]
  exact hω

lemma eval_dyadicRefine (s : ℝ) (e : E) (ω : Ω) :
    (G.dyadicRefine hnm).eval s e ω = G.eval s e ω := by
  rw [eval_eq_fin, eval_eq_fin]
  exact stepIntegral_dyadic_refine_eval hT hnm (Ki := fun _ => G.K) (fun _ => G.B)
    (fun i k => G.ξ i k) s ω e

lemma Adapted.dyadicRefine {N : PoissonRandomMeasure P ν}
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT n)} (hG : G.Adapted N) (hnm : n ≤ m) :
    (G.dyadicRefine hnm).Adapted N := by
  intro i hi k
  exact dyadic_refine_adapted N hT hnm (Ki := fun _ => G.K) (fun i k => G.ξ i k)
    (fun i k => hG i i.isLt k) ⟨i, hi⟩ k

/-- A mark-step integrand on the level-`ℓ` dyadic grid of `[0, T]`, restricted to the
prefix `[0, T / 2 ^ d]` (`d ≤ ℓ`), which is the level-`(ℓ - d)` dyadic grid there. -/
def dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) (_hd : d ≤ ℓ) :
    MarkStep Ω E ν (TimeGrid.dyadic (T / 2 ^ d) (by positivity) (ℓ - d)) where
  K := G.K
  B := G.B
  B_measurable := G.B_measurable
  B_finite := G.B_finite
  ξ := G.ξ
  ξ_bounded := G.ξ_bounded
  ξ_measurable := G.ξ_measurable

lemma dyadic_p_restrict {ℓ d : ℕ} (hd : d ≤ ℓ) (i : ℕ) :
    (TimeGrid.dyadic (T / 2 ^ d) (by positivity) (ℓ - d)).p i = (TimeGrid.dyadic T hT ℓ).p i := by
  show (i : ℝ) * (T / 2 ^ d) / ((2 ^ (ℓ - d) : ℕ) : ℝ) = (i : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ)
  have h : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h]
  field_simp

lemma dyadic_p_pow {ℓ d : ℕ} (hd : d ≤ ℓ) :
    (TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) = T / 2 ^ d := by
  show ((2 ^ (ℓ - d) : ℕ) : ℝ) * T / ((2 ^ ℓ : ℕ) : ℝ) = T / 2 ^ d
  have h : (2 : ℝ) ^ ℓ = 2 ^ d * 2 ^ (ℓ - d) := by rw [← pow_add, Nat.add_sub_cancel' hd]
  push_cast
  rw [h]
  field_simp

lemma full_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) (hd : d ≤ ℓ)
    (ω : Ω) : (G.dyadicRestrict hd).full N ω = G.integral N (T / 2 ^ d) ω := by
  have h : (G.dyadicRestrict hd).full N ω
      = G.integral N ((TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d))) ω := by
    rw [G.integral_p_eq N _ (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))]
    unfold full
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    show G.ξ i k ω * N.compensated (Set.Ioc
        ((TimeGrid.dyadic (T / 2 ^ d) (by positivity) (ℓ - d)).p i)
        ((TimeGrid.dyadic (T / 2 ^ d) (by positivity) (ℓ - d)).p (i + 1)) ×ˢ G.B k) ω = _
    rw [dyadic_p_restrict (hT := hT) hd, dyadic_p_restrict (hT := hT) hd]
  rw [h, dyadic_p_pow (hT := hT) hd]

lemma eval_dyadicRestrict {ℓ d : ℕ} (G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)) (hd : d ≤ ℓ)
    {s : ℝ} (hs : s ≤ T / 2 ^ d) (e : E) (ω : Ω) :
    (G.dyadicRestrict hd).eval s e ω = G.eval s e ω := by
  unfold eval
  simp_rw [dyadic_p_restrict (hT := hT) hd]
  refine Finset.sum_subset (Finset.range_subset.2 fun i hi =>
    Finset.mem_range.2 (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d)))) ?_
  intro i hi hni
  rw [Finset.mem_range] at hi hni
  rw [Set.indicator_of_notMem, zero_mul]
  intro hs'
  have : (TimeGrid.dyadic T hT ℓ).p (2 ^ (ℓ - d)) ≤ (TimeGrid.dyadic T hT ℓ).p i :=
    (TimeGrid.dyadic T hT ℓ).p_mono (not_lt.1 hni) hi.le
  rw [dyadic_p_pow (hT := hT) hd] at this
  exact absurd (hs.trans this) (not_le.2 hs'.1)

lemma Adapted.dyadicRestrict {N : PoissonRandomMeasure P ν} {ℓ d : ℕ}
    {G : MarkStep Ω E ν (TimeGrid.dyadic T hT ℓ)} (hG : G.Adapted N) (hd : d ≤ ℓ) :
    (G.dyadicRestrict hd).Adapted N := by
  intro i hi k
  show @StronglyMeasurable Ω ℝ _ ((naturalFiltration N).seq
    ((TimeGrid.dyadic (T / 2 ^ d) (by positivity) (ℓ - d)).p i)) (G.ξ i k)
  rw [dyadic_p_restrict (hT := hT) hd]
  exact hG i (lt_of_lt_of_le hi (Nat.pow_le_pow_right two_pos (Nat.sub_le ℓ d))) k


end Dyadic

end MarkStep

end LevyStochCalc.Poisson.Compensated
