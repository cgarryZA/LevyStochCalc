/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointMultidim
import LevyStochCalc.Driver.JointCharacters
import LevyStochCalc.Driver.JointFiltration
import LevyStochCalc.Poisson.PerpBridge
import LevyStochCalc.Brownian.PRPBrownian

/-!
# The orthogonal complement of the joint ranges

The times of a finite family of Brownian coordinate values, together with the horizon, sort into
an increasing grid whose last point is the horizon, and a finite family of window sets sits
inside a single window of finite mark intensity. A product of a Brownian cylinder character and a
window character is therefore a value character along the grid, and the joint grid induction
applies. The clamping horizon of that induction is strictly beyond the last grid point, so the
orthogonality hypothesis is carried up by the marked perp bridge.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace LevyStochCalc.Driver

open LevyStochCalc.Poisson LevyStochCalc.Poisson.Compensated
open LevyStochCalc.Brownian LevyStochCalc.Brownian.Ito LevyStochCalc.Brownian.Multidim

universe u v

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E]
  {P : Measure Ω} [IsProbabilityMeasure P] {d : ℕ} {ν : Measure E} [SigmaFinite ν] {T : ℝ}

section MarkSet

/-- A mark set of finite intensity carrying a window set. -/
noncomputable def markSet (B : Poisson.WindowSet E ν T) : Set E := B.2.2.choose

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [SigmaFinite ν] in
theorem measurableSet_markSet (B : Poisson.WindowSet E ν T) : MeasurableSet (markSet B) :=
  B.2.2.choose_spec.1

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [SigmaFinite ν] in
theorem markSet_ne_top (B : Poisson.WindowSet E ν T) : ν (markSet B) ≠ ⊤ :=
  B.2.2.choose_spec.2.1

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] [SigmaFinite ν] in
theorem subset_markSet (B : Poisson.WindowSet E ν T) :
    (B : Set (ℝ × E)) ⊆ Set.Ioc (0 : ℝ) T ×ˢ markSet B := B.2.2.choose_spec.2.2

/-- A mark set of finite intensity containing those of a finite family of window sets and the
`n`-th stage of a σ-finite exhaustion of the marks. -/
noncomputable def markUnion (G : Finset (Poisson.WindowSet E ν T)) (n : ℕ) : Set E :=
  (⋃ B ∈ G, markSet B) ∪ spanningSets ν n

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem measurableSet_markUnion (G : Finset (Poisson.WindowSet E ν T)) (n : ℕ) :
    MeasurableSet (markUnion G n) :=
  (G.measurableSet_biUnion fun B _ => measurableSet_markSet B).union
    (measurableSet_spanningSets ν n)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem markUnion_ne_top (G : Finset (Poisson.WindowSet E ν T)) (n : ℕ) :
    ν (markUnion G n) ≠ ⊤ := by
  refine (lt_of_le_of_lt (measure_union_le _ _) ?_).ne
  refine ENNReal.add_lt_top.mpr ⟨lt_of_le_of_lt (measure_biUnion_finset_le G markSet) ?_,
    measure_spanningSets_lt_top ν n⟩
  exact ENNReal.sum_lt_top.mpr fun B _ => (markSet_ne_top B).lt_top

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem markSet_subset_markUnion {G : Finset (Poisson.WindowSet E ν T)}
    {B : Poisson.WindowSet E ν T} (hB : B ∈ G) (n : ℕ) : markSet B ⊆ markUnion G n :=
  fun _ hx => Or.inl (Set.mem_iUnion₂.mpr ⟨B, hB, hx⟩)

omit [MeasurableSpace.CountablyGenerated E] [MeasurableSingletonClass E] in
theorem mem_markUnion (G : Finset (Poisson.WindowSet E ν T)) {n : ℕ} {e : E}
    (he : e ∈ spanningSets ν n) : e ∈ markUnion G n := Or.inr he

end MarkSet

section Complement

variable (W : MultidimBrownianMotion P d) (N : PoissonRandomMeasure P ν)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)

/-- **Product characters.** A square-integrable weight of mean zero, measurable before the
horizon, orthogonal to every coordinate's Itô integrals and to the compensated integral of every
admissible integrand, is orthogonal to every product of a Brownian cylinder character and a
window character. -/
theorem pairing_char_joint_eq_zero [Nonempty E] (hd : 0 < d)
    (hℱi : ∀ i, IsBrownianFiltration (W.W i) ℱ)
    (hℱB : ∀ {c : Fin d → ℝ} (hc : ∑ i, c i ^ 2 = 1),
      IsBrownianFiltration (MultidimBrownianMotion.combineBM W hc) ℱ)
    (hℱN : IsPoissonFiltration N ℱ)
    (hℱ0 : ∀ t : ℝ, t ≤ 0 → ℱ 0 ≤ ℱ t)
    (hnull : ∀ s : Set Ω, MeasurableSet s → P s = 0 → MeasurableSet[ℱ 0] s)
    (hT : 0 < T) {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P) (hZm : AEStronglyMeasurable[ℱ T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (W.W i) ℱ (hℱi i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν ℱ T, ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) (F : Finset (Fin d × Set.Iic T))
    (G : Finset (Poisson.WindowSet E ν T)) (w : F → ℝ) (v : G → ℝ) :
    ∫ ω, Complex.exp (((∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
      * Complex.exp (((∑ B : G,
          (N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B : ℝ) : ℂ)
        * Complex.I) * ((Z ω : ℝ) : ℂ) ∂P = 0 := by
  classical
  obtain ⟨n₀, hn₀⟩ : ∃ n : ℕ, (Classical.arbitrary E) ∈ spanningSets ν n := by
    have : (Classical.arbitrary E) ∈ ⋃ n, spanningSets ν n := by
      rw [iUnion_spanningSets ν]; trivial
    exact Set.mem_iUnion.mp this
  set S : Finset ℝ := insert T (Analysis.posTimes F) with hSdef
  set τ : ℕ → ℝ := Analysis.sortedGrid S with hτdef
  have hSpos : ∀ x ∈ S, 0 < x := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hT
    · exact Analysis.pos_of_mem_posTimes hx
  have hSle : ∀ x ∈ S, x ≤ T := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact le_rfl
    · exact Analysis.le_of_mem_posTimes hx
  have hlt : ∀ k, k < S.card → τ k < τ (k + 1) := fun k hk =>
    Analysis.sortedGrid_lt_succ S hSpos hk
  have hTle : T ≤ τ S.card := Analysis.le_sortedGrid_card (Finset.mem_insert_self T _)
  have hleT : τ S.card ≤ T :=
    hSle _ (Analysis.sortedGrid_card_mem ⟨T, Finset.mem_insert_self T _⟩)
  have hTn : τ S.card < T + 1 := lt_of_le_of_lt hleT (by linarith)
  have hR : (0 : ℝ) < T + 1 := by linarith
  have hTR : T ≤ T + 1 := by linarith
  have hBm : ∀ B : G, MeasurableSet ((B : Poisson.WindowSet E ν T) : Set (ℝ × E)) :=
    fun B => (B : Poisson.WindowSet E ν T).measurableSet
  have hBsub : ∀ B : G, ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))
      ⊆ Set.Ioc (0 : ℝ) (T + 1) ×ˢ markUnion G n₀ := by
    intro B
    refine (subset_markSet (B : Poisson.WindowSet E ν T)).trans ?_
    exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hTR)
      (markSet_subset_markUnion B.2 n₀)
  have hZcompR : ∀ G' : MarkedHorizonIntegrand P ν ℱ (T + 1),
      ∫ ω, Z ω * G'.integral N hℱN ω ∂P = 0 := fun G' =>
    Compensated.integral_mul_integral_eq_zero N hℱN hT hZ2 hZm hZcomp hTR G'
  have hkey := pairing_joint_value_characterMultidim_eq_zero W N ℱ hd hℱi hℱB hℱN hℱ0 hnull
    (τ := τ) (Analysis.sortedGrid_zero S) hR (measurableSet_markUnion G n₀)
    (markUnion_ne_top G n₀) v hBm hBsub (mem_markUnion G hn₀) hZ2 hperp hZcompR hZ0
    (fun k i => Analysis.weightAt F w (τ k) i) S.card hlt hTn
  refine Eq.trans (integral_congr_ae ?_) hkey
  filter_upwards [ae_forall_eq_zero_of_nonpos W F] with ω hω
  have hBrown : (∑ p : F, (W.W p.1.1).W (p.1.2 : ℝ) ω * w p)
      = ∑ i, ∑ k ∈ Finset.Ico 1 (S.card + 1),
          Analysis.weightAt F w (τ k) i * (W.W i).W (τ k) ω :=
    Analysis.sum_weight_eq_sum_grid F w (fun i t => (W.W i).W t ω)
      (fun p hp => hω p.1 p.2 hp) (Finset.subset_insert _ _) hSpos
  have hwin : (∑ B : G,
        (N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal * v B)
      = ∑ B : G, v B * (N.N ω (((B : Poisson.WindowSet E ν T) : Set (ℝ × E))
          ∩ Set.Ioc (0 : ℝ) (τ S.card) ×ˢ Set.univ)).toReal := by
    refine Finset.sum_congr rfl fun B _ => ?_
    have hsub : ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))
        ⊆ Set.Ioc (0 : ℝ) (τ S.card) ×ˢ Set.univ := by
      refine (subset_markSet (B : Poisson.WindowSet E ν T)).trans ?_
      exact Set.prod_mono (Set.Ioc_subset_Ioc le_rfl hTle) (Set.subset_univ _)
    rw [Set.inter_eq_self_of_subset_left hsub, mul_comm]
  have hE : ∀ x : ℝ, Complex.exp ((x : ℂ) * Complex.I)
      = Complex.exp (Complex.I * (x : ℂ)) := fun x => by rw [mul_comm]
  rw [hE, hE, hBrown, hwin, charAt]
  ring

/-- **The orthogonal complement of the joint ranges is trivial.** A square-integrable weight of
mean zero, measurable for the augmented joint filtration of a Lévy driver at the horizon and
orthogonal both to every coordinate's Itô integrals and to the compensated integral of every
admissible integrand, vanishes almost everywhere. -/
theorem ae_eq_zero_of_perp_joint [Nonempty E] (D : LevyDriver P d ν) (hd : 0 < d) (hT : 0 < T)
    {Z : Ω → ℝ} (hZ2 : MemLp Z 2 P)
    (hZm : AEStronglyMeasurable[Brownian.augFiltration D.filtration P T] Z P)
    (hperp : ∀ i, PerpItoIntegrals (D.W.W i) (Brownian.augFiltration D.filtration P)
      (D.isBrownianFiltration_aug i) fun ω => (Z ω : ℂ))
    (hZcomp : ∀ G' : MarkedHorizonIntegrand P ν (Brownian.augFiltration D.filtration P) T,
      ∫ ω, Z ω * G'.integral D.N D.isPoissonFiltration_aug ω ∂P = 0)
    (hZ0 : ∫ ω, Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by
  have hfeq : Brownian.augFiltration D.filtration P T
      = Probability.aug (D.filtration T) ‹MeasurableSpace Ω› P := by
    change Probability.aug (D.filtration (max T 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left hT.le]
  have hZ2C : MemLp (fun ω => ((Z ω : ℝ) : ℂ)) 2 P := by
    refine ⟨Complex.continuous_ofReal.comp_aestronglyMeasurable hZ2.1, ?_⟩
    rw [eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun ω => Complex.norm_real (Z ω))]
    exact hZ2.2
  have hZmC : AEStronglyMeasurable[Probability.aug (D.filtration T) ‹MeasurableSpace Ω› P]
      (fun ω => ((Z ω : ℝ) : ℂ)) P := by
    rw [← hfeq]
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable hZm
  have hzero := D.ae_eq_zero_of_integral_char_joint T (hZ2C.integrable (by norm_num)) hZmC
    fun F G w v => pairing_char_joint_eq_zero D.W D.N (Brownian.augFiltration D.filtration P)
      hd D.isBrownianFiltration_aug (fun hc => D.isBrownianFiltration_combineBM_aug hc)
      D.isPoissonFiltration_aug (fun _ ht => D.augFiltration_le_of_nonpos ht)
      (fun _ hs h0 => D.measurableSet_augFiltration_of_null hs h0) hT hZ2 hZm hperp hZcomp hZ0
      F G w v
  filter_upwards [hzero] with ω hω
  have hc : ((Z ω : ℝ) : ℂ) = 0 := hω
  exact_mod_cast hc

end Complement

end LevyStochCalc.Driver
