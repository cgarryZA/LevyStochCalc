/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/

import LevyStochCalc.Ito.FiniteHorizonProcess
import LevyStochCalc.Ito.FiniteHorizonInnerIntegral

/-!
# The expected product of two Itô processes on a finite horizon

Let `X = X₀ + ∫ a ds + M` and `Y = Y₀ + ∫ b ds + N` be square-integrable Itô processes on
`[0, T]` for one filtration (`IsL2ItoProcessOn`), with values in a complete real inner product
space. For `t ∈ [0, T]`,

`𝔼⟪X_t, Y_t⟫ = 𝔼⟪X₀, Y₀⟫ + ∫_0^t 𝔼(⟪a_s, Y_s⟫ + ⟪X_s, b_s⟫) ds + 𝔼⟪M_t, N_t⟫`,

and the rate `s ↦ 𝔼(⟪a_s, Y_s⟫ + ⟪X_s, b_s⟫)` is integrable on `[0, t]`. The proof uses of the
martingale parts only that they have orthogonal increments; the last term is identified with the
bracket of the two martingale parts by a polarised isometry
(`LevyStochCalc.Ito.FiniteHorizonBracket`).

The hypotheses are those of `IsL2ItoProcessOn`: square-integrable initial values measurable at
time zero, drifts square integrable for `P ⊗ ds` on `[0, T]` and adapted at almost every time,
square-integrable martingale parts. No moment of order higher than two, no integrability of the
product of a process with its drift beyond what these give, and no extension of the processes or
of the filtration beyond `T` is assumed.

The proof writes `⟪X_t, Y_t⟫ - ⟪X₀ + M_t, Y₀ + N_t⟫` as the time integral of a density
`Φ(ω, s) = ⟪a_s, Y₀ + ∫_0^s b + N_t⟫ + ⟪X₀ + ∫_0^s a + M_t, b_s⟫`, integrable for `P ⊗ ds`
(the pathwise product rule `inner_setIntegral_eq`), exchanges the integrals, and reads `N_t`,
`M_t` back at the time `s` against the `ℱ_s`-measurable drifts.
-/

open MeasureTheory Filter
open scoped RealInnerProductSpace

namespace LevyStochCalc.Ito.FiniteHorizon

variable {Ω E : Type*} {m0 : MeasurableSpace Ω} {P : Measure Ω}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

section Helpers

omit [CompleteSpace E] in
/-- The pairing of an integrable function against a bounded one is integrable. -/
theorem integrable_inner_of_norm_le {μ : Measure ℝ} {u w : ℝ → E} (hu : Integrable u μ)
    (hw : AEStronglyMeasurable w μ) {C : ℝ} (hC : ∀ r, ‖w r‖ ≤ C) :
    Integrable (fun r => ⟪u r, w r⟫) μ :=
  Integrable.mono' (hu.norm.mul_const C) (hu.aestronglyMeasurable.inner hw)
    (Eventually.of_forall fun r => (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left (hC r) (norm_nonneg _)))

omit [CompleteSpace E] in
/-- The pairing of a bounded function against an integrable one is integrable. -/
theorem integrable_inner_of_norm_le' {μ : Measure ℝ} {u w : ℝ → E} (hu : Integrable u μ)
    (hw : AEStronglyMeasurable w μ) {C : ℝ} (hC : ∀ r, ‖w r‖ ≤ C) :
    Integrable (fun r => ⟪w r, u r⟫) μ :=
  (integrable_inner_of_norm_le hu hw hC).congr
    (Eventually.of_forall fun r => real_inner_comm (w r) (u r))

omit [CompleteSpace E] in
/-- The expected pairing of two sums of square-integrable functions. -/
theorem integral_inner_add_add {f g h k : Ω → E} (hf : MemLp f 2 P) (hg : MemLp g 2 P)
    (hh : MemLp h 2 P) (hk : MemLp k 2 P) :
    ∫ ω, ⟪f ω + g ω, h ω + k ω⟫ ∂P
      = ∫ ω, ⟪f ω, h ω⟫ ∂P + ∫ ω, ⟪f ω, k ω⟫ ∂P + ∫ ω, ⟪g ω, h ω⟫ ∂P
        + ∫ ω, ⟪g ω, k ω⟫ ∂P := by
  have hfh := integrable_inner_of_memLp hf hh
  have hfk := integrable_inner_of_memLp hf hk
  have hgh := integrable_inner_of_memLp hg hh
  have hgk := integrable_inner_of_memLp hg hk
  have hexp : (fun ω => ⟪f ω + g ω, h ω + k ω⟫)
      = fun ω => ⟪f ω, h ω⟫ + ⟪f ω, k ω⟫ + ⟪g ω, h ω⟫ + ⟪g ω, k ω⟫ := by
    funext ω
    simp only [inner_add_left, inner_add_right]
    ring
  have h12 : Integrable (fun ω => ⟪f ω, h ω⟫ + ⟪f ω, k ω⟫) P := hfh.add hfk
  have h123 : Integrable (fun ω => ⟪f ω, h ω⟫ + ⟪f ω, k ω⟫ + ⟪g ω, h ω⟫) P := h12.add hgh
  rw [hexp, integral_add h123 hgk, integral_add h12 hgh, integral_add hfh hfk]

variable {ℱ : Filtration ℝ m0} {T : ℝ} {N : ℝ → Ω → E}

omit [CompleteSpace E] in
/-- Against a variable measurable at time `s`, a process with orthogonal increments may be read at
any later time of the window. -/
theorem integral_inner_add_increment (hN : HasOrthogonalIncrementsOn ℱ P T N) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) {f c : Ω → E}
    (hf : AEStronglyMeasurable[ℱ s] f P) (hf2 : MemLp f 2 P) (hc : MemLp c 2 P) :
    ∫ ω, ⟪f ω, c ω + N s ω⟫ ∂P = ∫ ω, ⟪f ω, c ω + N t ω⟫ ∂P := by
  simp_rw [inner_add_right]
  rw [integral_add (integrable_inner_of_memLp hf2 hc)
      (integrable_inner_of_memLp hf2 (hN.memLp s hs (hst.trans htT))),
    integral_add (integrable_inner_of_memLp hf2 hc)
      (integrable_inner_of_memLp hf2 (hN.memLp t (hs.trans hst) htT)),
    hN.integral_inner_eq s t hs hst htT f hf hf2]

omit [CompleteSpace E] in
/-- The reading of a process with orthogonal increments at a later time, with the pairing
reversed. -/
theorem integral_inner_add_increment' (hN : HasOrthogonalIncrementsOn ℱ P T N) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) {f c : Ω → E}
    (hf : AEStronglyMeasurable[ℱ s] f P) (hf2 : MemLp f 2 P) (hc : MemLp c 2 P) :
    ∫ ω, ⟪c ω + N s ω, f ω⟫ ∂P = ∫ ω, ⟪c ω + N t ω, f ω⟫ ∂P := by
  have e : ∀ r, ∫ ω, ⟪c ω + N r ω, f ω⟫ ∂P = ∫ ω, ⟪f ω, c ω + N r ω⟫ ∂P := fun r =>
    integral_congr_ae (Eventually.of_forall fun ω => real_inner_comm _ _)
  rw [e, e]
  exact integral_inner_add_increment hN hs hst htT hf hf2 hc

end Helpers

variable [IsFiniteMeasure P] {ℱ : Filtration ℝ m0} {T : ℝ} {X Y a b M N : ℝ → Ω → E}
  {X₀ Y₀ : Ω → E}

/-- The density of the drift pairing for strongly measurable drifts; see
`exists_integrable_density`. -/
theorem exists_integrable_density_of_stronglyMeasurable
    (hX : IsL2ItoProcessOn ℱ P T X X₀ a M) (hY : IsL2ItoProcessOn ℱ P T Y Y₀ b N)
    (ha : StronglyMeasurable fun p : Ω × ℝ => a p.2 p.1)
    (hb : StronglyMeasurable fun p : Ω × ℝ => b p.2 p.1) {t : ℝ} (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∃ Φ : Ω × ℝ → ℝ, Integrable Φ (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) ∧
      (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        ∫ ω, Φ (ω, s) ∂P = ∫ ω, (⟪a s ω, Y s ω⟫ + ⟪X s ω, b s ω⟫) ∂P) ∧
      ∫ ω, ⟪X t ω, Y t ω⟫ ∂P
        = ∫ ω, ⟪X₀ ω, Y₀ ω⟫ ∂P + ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, Φ (ω, s) ∂volume ∂P
          + ∫ ω, ⟪M t ω, N t ω⟫ ∂P := by
  have ha2 : MemLp (fun p : Ω × ℝ => a p.2 p.1) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := memLp_prod_Icc_mono htT hX.drift_memLp
  have hb2 : MemLp (fun p : Ω × ℝ => b p.2 p.1) 2
      (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) := memLp_prod_Icc_mono htT hY.drift_memLp
  have hMt := hX.martingale.memLp t ht0 htT
  have hNt := hY.martingale.memLp t ht0 htT
  have hRA2 := memLp_runningIntegral ha ha2 ht0
  have hRB2 := memLp_runningIntegral hb hb2 ht0
  set Yh : Ω × ℝ → E := fun p => Y₀ p.1 + runningIntegral b t p + N t p.1 with hYh
  set Xh : Ω × ℝ → E := fun p => X₀ p.1 + runningIntegral a t p + M t p.1 with hXh
  have hYh2 : MemLp Yh 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
    ((memLp_comp_fst hY.initial_memLp t).add hRB2).add (memLp_comp_fst hNt t)
  have hXh2 : MemLp Xh 2 (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
    ((memLp_comp_fst hX.initial_memLp t).add hRA2).add (memLp_comp_fst hMt t)
  set Φ : Ω × ℝ → ℝ := fun p => ⟪a p.2 p.1, Yh p⟫ + ⟪Xh p, b p.2 p.1⟫ with hΦ
  have hΦi : Integrable Φ (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) :=
    (integrable_inner_of_memLp ha2 hYh2).add (integrable_inner_of_memLp hXh2 hb2)
  refine ⟨Φ, hΦi, ?_, ?_⟩
  · -- at almost every time, the density integrates to the rate
    have hadX := ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl htT)
      hX.drift_adapted
    have hadY := ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl htT)
      hY.drift_adapted
    filter_upwards [ae_restrict_mem measurableSet_Icc, hadX, hadY, ae_memLp_slice ha2,
      ae_memLp_slice hb2] with s hs has hbs has2 hbs2
    have hsT : s ≤ T := hs.2.trans htT
    have eA : (fun ω => runningIntegral a t (ω, s)) = fun ω => ∫ r in Set.Icc (0 : ℝ) s, a r ω :=
      funext fun ω => runningIntegral_eq hs
    have eB : (fun ω => runningIntegral b t (ω, s)) = fun ω => ∫ r in Set.Icc (0 : ℝ) s, b r ω :=
      funext fun ω => runningIntegral_eq hs
    have hAs : MemLp (fun ω => runningIntegral a t (ω, s)) 2 P := by
      rw [eA]
      exact memLp_setIntegral ha (memLp_prod_Icc_mono hs.2 ha2) hs.1
    have hBs : MemLp (fun ω => runningIntegral b t (ω, s)) 2 P := by
      rw [eB]
      exact memLp_setIntegral hb (memLp_prod_Icc_mono hs.2 hb2) hs.1
    have hYhs : MemLp (fun ω => Yh (ω, s)) 2 P := (hY.initial_memLp.add hBs).add hNt
    have hXhs : MemLp (fun ω => Xh (ω, s)) 2 P := (hX.initial_memLp.add hAs).add hMt
    have e1 : ∫ ω, ⟪a s ω, Y s ω⟫ ∂P = ∫ ω, ⟪a s ω, Yh (ω, s)⟫ ∂P := by
      calc ∫ ω, ⟪a s ω, Y s ω⟫ ∂P
          = ∫ ω, ⟪a s ω, (Y₀ ω + runningIntegral b t (ω, s)) + N s ω⟫ ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hY.decomposition s hs.1 hsT] with ω hω
            rw [hω, runningIntegral_eq hs]
        _ = ∫ ω, ⟪a s ω, (Y₀ ω + runningIntegral b t (ω, s)) + N t ω⟫ ∂P :=
            integral_inner_add_increment hY.martingale hs.1 hs.2 htT
              (c := fun ω => Y₀ ω + runningIntegral b t (ω, s)) has has2
              (hY.initial_memLp.add hBs)
        _ = ∫ ω, ⟪a s ω, Yh (ω, s)⟫ ∂P := rfl
    have e2 : ∫ ω, ⟪X s ω, b s ω⟫ ∂P = ∫ ω, ⟪Xh (ω, s), b s ω⟫ ∂P := by
      calc ∫ ω, ⟪X s ω, b s ω⟫ ∂P
          = ∫ ω, ⟪(X₀ ω + runningIntegral a t (ω, s)) + M s ω, b s ω⟫ ∂P := by
            refine integral_congr_ae ?_
            filter_upwards [hX.decomposition s hs.1 hsT] with ω hω
            rw [hω, runningIntegral_eq hs]
        _ = ∫ ω, ⟪(X₀ ω + runningIntegral a t (ω, s)) + M t ω, b s ω⟫ ∂P :=
            integral_inner_add_increment' hX.martingale hs.1 hs.2 htT
              (c := fun ω => X₀ ω + runningIntegral a t (ω, s)) hbs hbs2
              (hX.initial_memLp.add hAs)
        _ = ∫ ω, ⟪Xh (ω, s), b s ω⟫ ∂P := rfl
    rw [integral_add (integrable_inner_of_memLp has2 (hY.memLp hs.1 hsT))
      (integrable_inner_of_memLp (hX.memLp hs.1 hsT) hbs2), e1, e2]
    exact integral_add (integrable_inner_of_memLp has2 hYhs) (integrable_inner_of_memLp hXhs hbs2)
  · -- the pathwise product rule
    have hpath : ∀ᵐ ω ∂P, ∫ s in Set.Icc (0 : ℝ) t, Φ (ω, s)
        = ⟪X₀ ω + (∫ s in Set.Icc (0 : ℝ) t, a s ω) + M t ω,
            Y₀ ω + (∫ s in Set.Icc (0 : ℝ) t, b s ω) + N t ω⟫
          - ⟪X₀ ω + M t ω, Y₀ ω + N t ω⟫ := by
      filter_upwards [ae_integrableOn_of_memLp ha2, ae_integrableOn_of_memLp hb2] with ω hωa hωb
      have hRAs : AEStronglyMeasurable (fun s => runningIntegral a t (ω, s))
          (volume.restrict (Set.Icc (0 : ℝ) t)) :=
        ((stronglyMeasurable_runningIntegral ha).comp_measurable
          measurable_prodMk_left).aestronglyMeasurable
      have hRBs : AEStronglyMeasurable (fun s => runningIntegral b t (ω, s))
          (volume.restrict (Set.Icc (0 : ℝ) t)) :=
        ((stronglyMeasurable_runningIntegral hb).comp_measurable
          measurable_prodMk_left).aestronglyMeasurable
      have i1 : Integrable (fun s => ⟪a s ω, Y₀ ω + N t ω⟫)
          (volume.restrict (Set.Icc (0 : ℝ) t)) :=
        integrable_inner_of_norm_le hωa aestronglyMeasurable_const fun _ => le_rfl
      have i2 : Integrable (fun s => ⟪a s ω, runningIntegral b t (ω, s)⟫)
          (volume.restrict (Set.Icc (0 : ℝ) t)) :=
        integrable_inner_of_norm_le hωa hRBs (norm_runningIntegral_le hωb)
      have i3 : Integrable (fun s => ⟪X₀ ω + M t ω, b s ω⟫)
          (volume.restrict (Set.Icc (0 : ℝ) t)) :=
        integrable_inner_of_norm_le' hωb aestronglyMeasurable_const fun _ => le_rfl
      have i4 : Integrable (fun s => ⟪runningIntegral a t (ω, s), b s ω⟫)
          (volume.restrict (Set.Icc (0 : ℝ) t)) :=
        integrable_inner_of_norm_le' hωb hRAs (norm_runningIntegral_le hωa)
      have hexp : (fun s => Φ (ω, s))
          = fun s => ⟪a s ω, Y₀ ω + N t ω⟫ + ⟪a s ω, runningIntegral b t (ω, s)⟫
            + (⟪X₀ ω + M t ω, b s ω⟫ + ⟪runningIntegral a t (ω, s), b s ω⟫) := by
        funext s
        simp only [hΦ, hYh, hXh, inner_add_left, inner_add_right]
        ring
      have e2 : ∫ s in Set.Icc (0 : ℝ) t, ⟪a s ω, runningIntegral b t (ω, s)⟫
          = ∫ s in Set.Icc (0 : ℝ) t, ⟪a s ω, ∫ r in Set.Icc (0 : ℝ) s, b r ω⟫ :=
        setIntegral_congr_fun measurableSet_Icc fun s hs => by rw [runningIntegral_eq hs]
      have e4 : ∫ s in Set.Icc (0 : ℝ) t, ⟪runningIntegral a t (ω, s), b s ω⟫
          = ∫ s in Set.Icc (0 : ℝ) t, ⟪∫ r in Set.Icc (0 : ℝ) s, a r ω, b s ω⟫ :=
        setIntegral_congr_fun measurableSet_Icc fun s hs => by rw [runningIntegral_eq hs]
      have hV := inner_setIntegral_eq hωa hωb
      have i12 : Integrable (fun s => ⟪a s ω, Y₀ ω + N t ω⟫ + ⟪a s ω, runningIntegral b t (ω, s)⟫)
          (volume.restrict (Set.Icc (0 : ℝ) t)) := i1.add i2
      have i34 : Integrable
          (fun s => ⟪X₀ ω + M t ω, b s ω⟫ + ⟪runningIntegral a t (ω, s), b s ω⟫)
          (volume.restrict (Set.Icc (0 : ℝ) t)) := i3.add i4
      rw [hexp, integral_add i12 i34, integral_add i1 i2, integral_add i3 i4, e2,
        e4, integral_inner_const_right hωa, integral_inner hωb]
      simp only [inner_add_left, inner_add_right] at hV ⊢
      rw [hV]
      ring
    have hi1 : Integrable (fun ω => ⟪X₀ ω + M t ω, Y₀ ω + N t ω⟫) P :=
      integrable_inner_of_memLp (hX.initial_memLp.add hMt) (hY.initial_memLp.add hNt)
    have hi2 : Integrable (fun ω => ∫ s in Set.Icc (0 : ℝ) t, Φ (ω, s)) P :=
      hΦi.integral_prod_left
    have hL : ∫ ω, ⟪X t ω, Y t ω⟫ ∂P
        = ∫ ω, (⟪X₀ ω + M t ω, Y₀ ω + N t ω⟫ + ∫ s in Set.Icc (0 : ℝ) t, Φ (ω, s)) ∂P := by
      refine integral_congr_ae ?_
      filter_upwards [hX.decomposition t ht0 htT, hY.decomposition t ht0 htT, hpath]
        with ω h1 h2 h3
      rw [h1, h2, h3]
      ring
    have hcross : ∫ ω, ⟪X₀ ω + M t ω, Y₀ ω + N t ω⟫ ∂P
        = ∫ ω, ⟪X₀ ω, Y₀ ω⟫ ∂P + ∫ ω, ⟪M t ω, N t ω⟫ ∂P := by
      rw [integral_inner_add_add hX.initial_memLp hMt hY.initial_memLp hNt,
        hY.martingale.integral_inner_eq_zero ht0 htT hX.initial_aestronglyMeasurable
          hX.initial_memLp,
        hX.martingale.integral_inner_eq_zero' ht0 htT hY.initial_aestronglyMeasurable
          hY.initial_memLp]
      ring
    rw [hL, integral_add hi1 hi2, hcross]
    ring

/-- **The density of the drift pairing.** For two Itô processes on `[0, T]` and `t ∈ [0, T]` there
is a `P ⊗ ds`-integrable function `Φ` on `Ω × [0, t]` whose time slices integrate to the rate
`𝔼(⟪a_s, Y_s⟫ + ⟪X_s, b_s⟫)` at almost every time and with
`𝔼⟪X_t, Y_t⟫ = 𝔼⟪X₀, Y₀⟫ + 𝔼 ∫_0^t Φ ds + 𝔼⟪M_t, N_t⟫`. -/
theorem exists_integrable_density
    (hX : IsL2ItoProcessOn ℱ P T X X₀ a M) (hY : IsL2ItoProcessOn ℱ P T Y Y₀ b N) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∃ Φ : Ω × ℝ → ℝ, Integrable Φ (P.prod (volume.restrict (Set.Icc (0 : ℝ) t))) ∧
      (∀ᵐ s ∂(volume.restrict (Set.Icc (0 : ℝ) t)),
        ∫ ω, Φ (ω, s) ∂P = ∫ ω, (⟪a s ω, Y s ω⟫ + ⟪X s ω, b s ω⟫) ∂P) ∧
      ∫ ω, ⟪X t ω, Y t ω⟫ ∂P
        = ∫ ω, ⟪X₀ ω, Y₀ ω⟫ ∂P + ∫ ω, ∫ s in Set.Icc (0 : ℝ) t, Φ (ω, s) ∂volume ∂P
          + ∫ ω, ⟪M t ω, N t ω⟫ ∂P := by
  obtain ⟨a', ha', haa', hX'⟩ := hX.exists_stronglyMeasurable
  obtain ⟨b', hb', hbb', hY'⟩ := hY.exists_stronglyMeasurable
  obtain ⟨Φ, hΦi, hrate, hid⟩ :=
    exists_integrable_density_of_stronglyMeasurable hX' hY' ha' hb' ht0 htT
  refine ⟨Φ, hΦi, ?_, hid⟩
  have h1 := ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl htT)
    (ae_ae_eq_slice_of_ae_eq_prod haa')
  have h2 := ae_restrict_of_ae_restrict_of_subset (Set.Icc_subset_Icc le_rfl htT)
    (ae_ae_eq_slice_of_ae_eq_prod hbb')
  filter_upwards [hrate, h1, h2] with s hs hs1 hs2
  rw [hs]
  refine integral_congr_ae ?_
  filter_upwards [hs1, hs2] with ω hω1 hω2
  rw [show a s ω = a' s ω from hω1, show b s ω = b' s ω from hω2]

/-- **The expected product of two Itô processes on a finite horizon.** For square-integrable
Itô processes `X = X₀ + ∫ a ds + M` and `Y = Y₀ + ∫ b ds + N` on `[0, T]` for one filtration and
`t ∈ [0, T]`,

`𝔼⟪X_t, Y_t⟫ = 𝔼⟪X₀, Y₀⟫ + ∫_0^t 𝔼(⟪a_s, Y_s⟫ + ⟪X_s, b_s⟫) ds + 𝔼⟪M_t, N_t⟫`. -/
theorem integral_inner_eq
    (hX : IsL2ItoProcessOn ℱ P T X X₀ a M) (hY : IsL2ItoProcessOn ℱ P T Y Y₀ b N) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    ∫ ω, ⟪X t ω, Y t ω⟫ ∂P
      = ∫ ω, ⟪X₀ ω, Y₀ ω⟫ ∂P
        + (∫ s in Set.Icc (0 : ℝ) t, ∫ ω, (⟪a s ω, Y s ω⟫ + ⟪X s ω, b s ω⟫) ∂P)
        + ∫ ω, ⟪M t ω, N t ω⟫ ∂P := by
  obtain ⟨Φ, hΦi, hrate, hid⟩ := exists_integrable_density hX hY ht0 htT
  rw [hid, integral_integral_swap (f := fun ω s => Φ (ω, s)) hΦi, integral_congr_ae hrate]

/-- **The rate of the expected product is integrable.** For two Itô processes on `[0, T]` and
`t ∈ [0, T]`, the rate `s ↦ 𝔼(⟪a_s, Y_s⟫ + ⟪X_s, b_s⟫)` is integrable on `[0, t]`. -/
theorem integrableOn_rate
    (hX : IsL2ItoProcessOn ℱ P T X X₀ a M) (hY : IsL2ItoProcessOn ℱ P T Y Y₀ b N) {t : ℝ}
    (ht0 : 0 ≤ t) (htT : t ≤ T) :
    IntegrableOn (fun s => ∫ ω, (⟪a s ω, Y s ω⟫ + ⟪X s ω, b s ω⟫) ∂P) (Set.Icc (0 : ℝ) t) := by
  obtain ⟨Φ, hΦi, hrate, -⟩ := exists_integrable_density hX hY ht0 htT
  exact hΦi.integral_prod_right.congr hrate

end LevyStochCalc.Ito.FiniteHorizon
