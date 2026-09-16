/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.AugJointUsualConditions
import LevyStochCalc.Probability.SetIntegralPiSystem

/-!
# Right-continuity of the augmented joint filtration of a Lévy driver

Write `𝔸 = augFiltration D.filtration P` for the `0`-clamped augmentation of the joint filtration
of a Lévy driver. Its germ field at a time `t ≥ 0` is already its field at `t`.

The driver's data over `(t, T]` measured from `t` — the Brownian increments `W u - W t` for
`u ∈ (t, T]` and the counts on the measurable regions inside `(t, T] × E` — generates the
σ-algebra `futureSigma t T`. Joined with `ℱ t` it contains `ℱ T`, and it is independent of the
germ field `ℱ₊ t`, the independence coming from the data of a grid starting at `t`. A σ-algebra
that contains `ℱ t`, sits inside the join `ℱ t ⊔ futureSigma t T` and is independent of
`futureSigma t T` differs from `ℱ t` only by null sets: the conditional expectation on `ℱ t` of
the indicator of one of its sets is that indicator, because the two integrate alike over the
π-system of intersections generating the join. Hence `ℱ₊ t ≤ aug (ℱ t)`, and since augmentation
commutes with the countable antitone infimum `⨅ n, ℱ (t + (n + 1)⁻¹)` this gives `𝔸₊ t = 𝔸 t`.
Below time `0` the filtration `𝔸` is constant, so `𝔸` is right-continuous.

## Main statements

* `LevyStochCalc.Probability.le_aug_of_indep_of_le_sup` — the σ-algebra criterion for lying in
  an augmentation.
* `LevyStochCalc.Driver.LevyDriver.filtration_le_sup_futureSigma` — `ℱ T ≤ ℱ t ⊔ futureSigma t T`.
* `LevyStochCalc.Driver.LevyDriver.indep_futureSigma_rightCont` — `futureSigma t T` against
  `ℱ₊ t`.
* `LevyStochCalc.Driver.LevyDriver.filtration_rightCont_le_aug` — `ℱ₊ t ≤ aug (ℱ t)`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_le_self` — `𝔸₊ t ≤ 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.rightCont_augFiltration_eq` — `𝔸₊ t = 𝔸 t` for `t ≥ 0`.
* `LevyStochCalc.Driver.LevyDriver.isRightContinuous_augFiltration` — `𝔸` is right-continuous.
-/

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- For a σ-algebra `𝒩` independent of `𝒢`, a function measurable for `𝒩` integrates over the
intersection of `Z ∈ 𝒩` with `F ∈ 𝒢` to its integral over `Z` times the measure of `F`. -/
theorem setIntegral_inter_of_indep {𝒩 𝒢 : MeasurableSpace Ω} (h𝒩 : 𝒩 ≤ mΩ) (h𝒢 : 𝒢 ≤ mΩ)
    (hind : Indep 𝒩 𝒢 P) {g : Ω → ℝ} (hgm : Measurable[𝒩] g) {Z F : Set Ω}
    (hZ : MeasurableSet[𝒩] Z) (hF : MeasurableSet[𝒢] F) :
    ∫ x in Z ∩ F, g x ∂P = (∫ x in Z, g x ∂P) * P.real F := by
  have hZ0 : MeasurableSet[mΩ] Z := h𝒩 Z hZ
  have hF0 : MeasurableSet[mΩ] F := h𝒢 F hF
  have hX1 : Measurable[𝒩] (Z.indicator g) := hgm.indicator hZ
  have hX2 : Measurable[𝒢] (F.indicator (1 : Ω → ℝ)) := measurable_one.indicator hF
  have hindf : IndepFun (Z.indicator g) (F.indicator (1 : Ω → ℝ)) P := by
    change Indep (MeasurableSpace.comap _ _) (MeasurableSpace.comap _ _) P
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hX1.comap_le) hX2.comap_le
  have hprod : Z.indicator g * F.indicator (1 : Ω → ℝ) = (Z ∩ F).indicator g := by
    funext x
    by_cases hz : x ∈ Z <;> by_cases hf : x ∈ F <;> simp [hz, hf]
  have hmul := hindf.integral_mul_eq_mul_integral
    ((hX1.mono h𝒩 le_rfl).aestronglyMeasurable) ((hX2.mono h𝒢 le_rfl).aestronglyMeasurable)
  rw [hprod] at hmul
  rw [← integral_indicator (μ := P) (hZ0.inter hF0), hmul, integral_indicator hZ0,
    integral_indicator_one hF0]

/-- A σ-algebra that contains `𝒜`, lies inside `𝒜 ⊔ 𝒢` and is independent of `𝒢` lies in the
augmentation of `𝒜` by the `P`-null sets. -/
theorem le_aug_of_indep_of_le_sup {𝒜 𝒢 𝒞 : MeasurableSpace Ω} (h𝒜 : 𝒜 ≤ mΩ) (h𝒢 : 𝒢 ≤ mΩ)
    (h𝒜𝒞 : 𝒜 ≤ 𝒞) (h𝒞 : 𝒞 ≤ 𝒜 ⊔ 𝒢) (hind : Indep 𝒞 𝒢 P) :
    𝒞 ≤ aug 𝒜 mΩ P := by
  haveI : IsFiniteMeasure (P.trim h𝒜) := isFiniteMeasure_trim h𝒜
  have hsup : 𝒜 ⊔ 𝒢 ≤ mΩ := sup_le h𝒜 h𝒢
  have h𝒞0 : 𝒞 ≤ mΩ := h𝒞.trans hsup
  have hind𝒜 : Indep 𝒜 𝒢 P := indep_of_indep_of_le_left hind h𝒜𝒞
  intro A hA
  have hA0 : MeasurableSet[mΩ] A := h𝒞0 A hA
  have hfm : Measurable[𝒞] (A.indicator (1 : Ω → ℝ)) := measurable_one.indicator hA
  have hfint : Integrable (A.indicator (1 : Ω → ℝ)) P :=
    (integrable_const (1 : ℝ)).indicator hA0
  have hYm : Measurable[𝒜] (P[A.indicator (1 : Ω → ℝ) | 𝒜]) :=
    stronglyMeasurable_condExp.measurable
  have hzero : (A.indicator (1 : Ω → ℝ) - P[A.indicator (1 : Ω → ℝ) | 𝒜]) =ᵐ[P] 0 := by
    refine ae_eq_zero_of_forall_setIntegral_eq_zero_isPiSystem hsup
      sup_eq_generateFrom_interSets isPiSystem_interSets
      (hfint.sub integrable_condExp) ?_ ?_ ?_
    · exact (stronglyMeasurable_one.indicator (h𝒞 A hA)).sub
        (stronglyMeasurable_condExp.mono le_sup_left)
    · simp only [Pi.sub_apply]
      rw [integral_sub hfint integrable_condExp, integral_condExp h𝒜, sub_self]
    · rintro _ ⟨Z, F, hZ, hF, rfl⟩
      simp only [Pi.sub_apply]
      rw [integral_sub hfint.integrableOn integrable_condExp.integrableOn,
        setIntegral_inter_of_indep h𝒞0 h𝒢 hind hfm (h𝒜𝒞 Z hZ) hF,
        setIntegral_inter_of_indep h𝒜 h𝒢 hind𝒜 hYm hZ hF,
        setIntegral_condExp h𝒜 hfint hZ, sub_self]
  have hkey : ∀ᵐ x ∂P,
      A.indicator (1 : Ω → ℝ) x = (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x := by
    filter_upwards [hzero] with x hx
    have hx' : A.indicator (1 : Ω → ℝ) x - (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x = 0 := hx
    linarith
  refine ⟨hA0, (P[A.indicator (1 : Ω → ℝ) | 𝒜]) ⁻¹' Set.Ioi (1 / 2 : ℝ),
    hYm measurableSet_Ioi, ?_⟩
  refine measure_mono_null (fun x hx => ?_) (ae_iff.1 hkey)
  rcases Set.mem_symmDiff.1 hx with ⟨hxA, hxB⟩ | ⟨hxB, hxA⟩
  · have hfx : A.indicator (1 : Ω → ℝ) x = 1 := by simp [hxA]
    have hYx : (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x ≤ 1 / 2 := not_lt.1 hxB
    intro hcon
    rw [hfx] at hcon
    linarith
  · have hfx : A.indicator (1 : Ω → ℝ) x = 0 := by simp [hxA]
    have hYx : 1 / 2 < (P[A.indicator (1 : Ω → ℝ) | 𝒜]) x := hxB
    intro hcon
    rw [hfx] at hcon
    linarith

end LevyStochCalc.Probability

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

namespace LevyDriver

open LevyStochCalc.Probability

variable (D : LevyDriver.{u, v, w} P d ν)

/-- The σ-algebra of the driver's data over `(t, T]` measured from `t`: the Brownian increments
from `t` to the times of `(t, T]`, and the counts on the measurable regions inside `(t, T] × E`. -/
noncomputable abbrev futureSigma (t T : ℝ) : MeasurableSpace Ω :=
  (⨆ u ∈ Set.Ioc t T, ⨆ j : Fin d, D.incrementSigma j t u)
    ⊔ ⨆ C ∈ {C : Set (ℝ × E) | C ⊆ Set.Ioc t T ×ˢ Set.univ ∧ MeasurableSet C},
        D.regionSigma C

theorem futureSigma_le (t T : ℝ) : D.futureSigma t T ≤ ‹MeasurableSpace Ω› :=
  sup_le
    (iSup₂_le fun u _ => iSup_le fun _ =>
      (Brownian.comap_increment_le_sigmaBrownian _ t u).trans (Brownian.sigmaBrownian_le _))
    (iSup₂_le fun _ hC => (D.N.measurable_eval hC.2).comap_le)

/-- A Brownian value at a time before `s` is measurable for the joint filtration at `s`. -/
theorem comap_eval_le_filtration (j : Fin d) {u s : ℝ} (hus : u ≤ s) :
    MeasurableSpace.comap (fun ω => (D.W.W j).W u ω) inferInstance ≤ D.filtration s := by
  refine le_trans ?_ (D.naturalFiltration_brownian_le s)
  rw [D.W.naturalFiltration_apply]
  refine le_iSup_of_le j ?_
  rw [brownianNaturalFiltration_apply (D.W.W j) s]
  exact le_iSup₂_of_le u (Set.mem_Iic.2 hus) le_rfl

/-- **The joint filtration at `T` is generated by its state at `t` together with the driver's
data over `(t, T]`.** -/
theorem filtration_le_sup_futureSigma {t T : ℝ} (htT : t ≤ T) :
    D.filtration T ≤ D.filtration t ⊔ D.futureSigma t T := by
  rw [D.filtration_apply, D.W.naturalFiltration_apply]
  refine sup_le (iSup_le fun j => ?_) ?_
  · rw [brownianNaturalFiltration_apply (D.W.W j) T]
    refine iSup₂_le fun u hu => ?_
    rcases le_or_gt u t with hut | hut
    · exact le_sup_of_le_left (D.comap_eval_le_filtration j hut)
    · have heq : (fun ω => (D.W.W j).W u ω)
          = fun ω => (D.W.W j).W t ω + ((D.W.W j).W u ω - (D.W.W j).W t ω) := by
        funext ω; ring
      change MeasurableSpace.comap (fun ω => (D.W.W j).W u ω) inferInstance ≤ _
      rw [heq]
      refine Probability.comap_add_le
        (le_sup_of_le_left (D.comap_eval_le_filtration j le_rfl)) ?_
      exact le_sup_of_le_right (le_sup_of_le_left
        (le_iSup₂_of_le u (Set.mem_Ioc.2 ⟨hut, Set.mem_Iic.1 hu⟩)
          (le_iSup (fun j : Fin d => D.incrementSigma j t u) j)))
  · rw [poissonNaturalFiltration_apply]
    refine iSup₂_le fun B hB => ?_
    have hIic : MeasurableSet (B ∩ Set.Iic t ×ˢ Set.univ) :=
      hB.2.inter (measurableSet_Iic.prod MeasurableSet.univ)
    have hIoc : MeasurableSet (B ∩ Set.Ioc t T ×ˢ Set.univ) :=
      hB.2.inter (measurableSet_Ioc.prod MeasurableSet.univ)
    have hdisj : Disjoint (B ∩ Set.Iic t ×ˢ Set.univ) (B ∩ Set.Ioc t T ×ˢ Set.univ) :=
      Set.disjoint_left.2 fun x hx hx' => absurd hx.2.1 (not_le.2 hx'.2.1.1)
    have hsplit : B = (B ∩ Set.Iic t ×ˢ Set.univ) ∪ (B ∩ Set.Ioc t T ×ˢ Set.univ) := by
      rw [← Set.inter_union_distrib_left, ← Set.union_prod, Set.Iic_union_Ioc_eq_Iic htT]
      exact (Set.inter_eq_self_of_subset_left hB.1).symm
    have heq : (fun ω => D.N.N ω B)
        = fun ω => D.N.N ω (B ∩ Set.Iic t ×ˢ Set.univ)
          + D.N.N ω (B ∩ Set.Ioc t T ×ˢ Set.univ) := by
      funext ω
      conv_lhs => rw [hsplit]
      exact measure_union hdisj hIoc
    change MeasurableSpace.comap (fun ω => D.N.N ω B) inferInstance ≤ _
    rw [heq]
    refine Probability.comap_add_le
      (le_sup_of_le_left (D.regionSigma_le_filtration hIic Set.inter_subset_right)) ?_
    exact le_sup_of_le_right (le_sup_of_le_right
      (le_iSup₂_of_le (B ∩ Set.Ioc t T ×ˢ Set.univ) ⟨Set.inter_subset_right, hIoc⟩ le_rfl))

/-- **The driver's data over `(t, T]` measured from `t` is independent of the germ field
`ℱ₊ t`.** -/
theorem indep_futureSigma_rightCont {t T : ℝ} (ht : 0 ≤ t) (htT : t < T) :
    Indep (D.futureSigma t T) (D.filtration.rightCont t) P := by
  classical
  set mfam : {u : ℝ // u ∈ Set.Ioc t T}
      ⊕ {C : Set (ℝ × E) // C ⊆ Set.Ioc t T ×ˢ Set.univ ∧ MeasurableSet C}
      → MeasurableSpace Ω := Sum.elim
    (fun u => ⨆ j : Fin d, D.incrementSigma j t (u : ℝ))
    (fun C => D.regionSigma (C : Set (ℝ × E))) with hmfam
  have hmfam_le : ∀ i, mfam i ≤ ‹MeasurableSpace Ω› := by
    rintro (u | C)
    · exact iSup_le fun j =>
        (Brownian.comap_increment_le_sigmaBrownian _ t (u : ℝ)).trans (Brownian.sigmaBrownian_le _)
    · exact (D.N.measurable_eval C.2.2).comap_le
  have hM : Indep (⨆ i, mfam i) (D.filtration.rightCont t) P := by
    refine Probability.indep_iSup_of_finset hmfam_le (D.filtration.rightCont.le t) fun S => ?_
    set G : Finset ℝ :=
      insert T (Finset.image (fun u : {u : ℝ // u ∈ Set.Ioc t T} => (u : ℝ)) S.toLeft) with hG
    have hGne : G.Nonempty := ⟨T, Finset.mem_insert_self _ _⟩
    have hGmem : ∀ x ∈ G, x ∈ Set.Ioc t T := by
      intro x hx
      rcases Finset.mem_insert.1 hx with h | h
      · subst h
        exact Set.mem_Ioc.2 ⟨htT, le_rfl⟩
      · obtain ⟨u, -, hu⟩ := Finset.mem_image.1 h
        exact hu ▸ u.2
    have hgpos : ∀ l, t < gridOf G hGne l := by
      intro l
      by_cases hl : l < G.card
      · exact (hGmem _ (gridOf_mem G hGne hl)).1
      · have hval : gridOf G hGne l = G.max' hGne + ((l - G.card + 1 : ℕ) : ℝ) := by
          simp only [gridOf, dif_neg hl]
        have hmax : t < G.max' hGne := (hGmem _ (G.max'_mem hGne)).1
        have hpos : (0 : ℝ) < ((l - G.card + 1 : ℕ) : ℝ) := by
          exact_mod_cast Nat.succ_pos (l - G.card)
        rw [hval]
        linarith
    set g : ℕ → ℝ := fun l => if l = 0 then t else gridOf G hGne (l - 1) with hg
    have hg0 : g 0 = t := by simp [hg]
    have hgsucc : ∀ l, g (l + 1) = gridOf G hGne l := by
      intro l
      simp [hg]
    have hg_mono : StrictMono g := by
      intro a b hab
      rcases Nat.eq_zero_or_pos a with rfl | ha
      · have hb : b ≠ 0 := by omega
        simp only [hg, if_pos rfl, if_neg hb]
        exact hgpos _
      · have ha' : a ≠ 0 := by omega
        have hb' : b ≠ 0 := by omega
        simp only [hg, if_neg ha', if_neg hb']
        exact strictMono_gridOf G hGne (by omega)
    refine indep_of_indep_of_le_left (D.indep_iSup_stepSigma_start
      (fun k : Fin S.toRight.card => ((S.toRight.equivFin.symm k : _) : Set (ℝ × E)))
      (fun k => (S.toRight.equivFin.symm k).1.2.2) hg_mono (by rw [hg0]; exact ht)
      (G.card + 1)) ?_
    refine iSup₂_le fun i hi => ?_
    match i with
    | Sum.inl a =>
      obtain ⟨l, hl, hgl⟩ := exists_gridOf_eq G hGne
        (Finset.mem_insert_of_mem (Finset.mem_image.2 ⟨a, Finset.mem_toLeft.2 hi, rfl⟩))
      refine le_iSup₂_of_le l (by omega) ?_
      have hgl' : g (l + 1) = (a : ℝ) := by rw [hgsucc, hgl]
      simp only [hmfam, Sum.elim_inl]
      refine le_sup_of_le_left (iSup_le fun j => le_iSup_of_le j (le_of_eq ?_))
      rw [hg0, hgl']
    | Sum.inr b =>
      obtain ⟨l, hl, hgl⟩ := exists_gridOf_eq G hGne (Finset.mem_insert_self T _)
      refine le_iSup₂_of_le l (by omega) ?_
      have hgT : g (l + 1) = T := by rw [hgsucc, hgl]
      simp only [hmfam, Sum.elim_inr]
      refine le_sup_of_le_right
        (le_iSup_of_le (S.toRight.equivFin ⟨b, Finset.mem_toRight.2 hi⟩) ?_)
      simp only [Equiv.symm_apply_apply]
      rw [hg0, hgT, Set.inter_eq_self_of_subset_left b.2.1]
  refine indep_of_indep_of_le_left hM (sup_le (iSup₂_le fun u hu => ?_) (iSup₂_le fun C hC => ?_))
  · exact le_iSup_of_le (Sum.inl ⟨u, hu⟩) (by simp [hmfam])
  · exact le_iSup_of_le (Sum.inr ⟨C, hC⟩) (by simp [hmfam])

/-- **The germ field of the joint filtration at a nonnegative time is contained in the
augmentation of the filtration there.** -/
theorem filtration_rightCont_le_aug {t : ℝ} (ht : 0 ≤ t) :
    D.filtration.rightCont t ≤ aug (D.filtration t) ‹MeasurableSpace Ω› P := by
  have hle : D.filtration.rightCont t ≤ D.filtration (t + 1) := by
    rw [Filtration.rightCont_eq_of_neBot_nhdsGT D.filtration t]
    exact iInf₂_le (t + 1) (by linarith)
  refine Probability.le_aug_of_indep_of_le_sup (D.filtration.le t) (D.futureSigma_le t (t + 1))
    (D.filtration.le_rightCont t) (hle.trans (D.filtration_le_sup_futureSigma (by linarith)))
    (D.indep_futureSigma_rightCont ht (by linarith)).symm

/-- **The germ field of the augmented joint filtration at a nonnegative time is its field
there.** -/
theorem rightCont_augFiltration_le_self {t : ℝ} (ht : 0 ≤ t) :
    (Brownian.augFiltration D.filtration P).rightCont t
      ≤ Brownian.augFiltration D.filtration P t := by
  have hseq : ∀ n : ℕ, t < t + ((n : ℝ) + 1)⁻¹ := by
    intro n
    have hpos : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
    linarith
  have hanti : Antitone fun n : ℕ => D.filtration (t + ((n : ℝ) + 1)⁻¹) := by
    intro a b hab
    refine D.filtration.mono ?_
    have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
    have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by gcongr
    linarith
  have h1 : (Brownian.augFiltration D.filtration P).rightCont t
      ≤ ⨅ n : ℕ, aug (D.filtration (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› P := by
    refine le_iInf fun n => ?_
    have h2 : (Brownian.augFiltration D.filtration P).rightCont t
        ≤ Brownian.augFiltration D.filtration P (t + ((n : ℝ) + 1)⁻¹) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ (hseq n)
    have h3 : Brownian.augFiltration D.filtration P (t + ((n : ℝ) + 1)⁻¹)
        = aug (D.filtration (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› P := by
      change aug (D.filtration (max (t + ((n : ℝ) + 1)⁻¹) 0)) ‹MeasurableSpace Ω› P = _
      rw [max_eq_left (by linarith [hseq n])]
    rwa [h3] at h2
  rw [aug_iInf_of_antitone hanti] at h1
  have h4 : (⨅ n : ℕ, D.filtration (t + ((n : ℝ) + 1)⁻¹)) ≤ D.filtration.rightCont t := by
    rw [Filtration.rightCont_eq]
    refine le_iInf₂ fun u hu => ?_
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u - t by linarith)
    refine le_trans (iInf_le _ n) (D.filtration.mono ?_)
    rw [one_div] at hn
    linarith
  have h5 : Brownian.augFiltration D.filtration P t
      = aug (D.filtration t) ‹MeasurableSpace Ω› P := by
    change aug (D.filtration (max t 0)) ‹MeasurableSpace Ω› P = _
    rw [max_eq_left ht]
  rw [h5]
  exact h1.trans ((aug_mono h4).trans (aug_le_of_le_aug (D.filtration_rightCont_le_aug ht)))

/-- The germ field of the augmented joint filtration at a nonnegative time equals its field
there. -/
theorem rightCont_augFiltration_eq {t : ℝ} (ht : 0 ≤ t) :
    (Brownian.augFiltration D.filtration P).rightCont t
      = Brownian.augFiltration D.filtration P t :=
  le_antisymm (D.rightCont_augFiltration_le_self ht)
    (Filtration.le_rightCont (Brownian.augFiltration D.filtration P) t)

/-- **The augmented joint filtration of a Lévy driver is right-continuous.** -/
instance isRightContinuous_augFiltration :
    Filtration.IsRightContinuous (Brownian.augFiltration D.filtration P) := by
  constructor
  intro t
  rcases le_or_gt 0 t with ht | ht
  · exact D.rightCont_augFiltration_le_self ht
  · have h1 : (Brownian.augFiltration D.filtration P).rightCont t
        ≤ Brownian.augFiltration D.filtration P (t / 2) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ (by linarith)
    rw [Brownian.augFiltration_of_nonpos _ _ (by linarith : t / 2 ≤ 0)] at h1
    rw [Brownian.augFiltration_of_nonpos _ _ ht.le]
    exact h1

end LevyDriver

end LevyStochCalc.Driver
