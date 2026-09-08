/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.Joint
import LevyStochCalc.Brownian.CylinderCharacters
import LevyStochCalc.Poisson.WindowFiltration

/-!
# Product characters of a Lévy driver separate

The coordinate values of the Brownian motion before `T` and the window counts of the Poisson
random measure before `T` form one family of real random variables, indexed by a sum type. Its
cylinder characters are the products of a Brownian cylinder character and a window character,
and the σ-algebra it generates is `σ(W_{≤T}) ⊔ windowSigma N T`, whose augmentation contains the
joint natural filtration at `T`. The generic separation theorem
`Probability.ae_eq_zero_of_integral_char_cylinder_eq_zero` therefore shows that an integrable
weight, measurable for the augmented joint filtration at `T` and orthogonal to every product
character, vanishes almost everywhere.
-/

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace LevyStochCalc.Driver

universe u v w

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-- A weight on the members of a finset, extended by zero. -/
noncomputable def extendZero {α : Type*} (F : Finset α) (w : F → ℝ) : α → ℝ := by
  classical
  exact fun i => if h : i ∈ F then w ⟨i, h⟩ else 0

theorem extendZero_coe {α : Type*} (F : Finset α) (w : F → ℝ) (i : F) :
    extendZero F w i = w i := by
  classical
  simp [extendZero]

omit [MeasurableSpace Ω] in
/-- A sum over a finset of a sum type splits into the sums over its two halves. -/
theorem Finset.sum_toLeft_add_sum_toRight {α β : Type*} (u : Finset (α ⊕ β)) (g : α ⊕ β → ℝ) :
    ∑ i ∈ u, g i = ∑ a ∈ u.toLeft, g (Sum.inl a) + ∑ b ∈ u.toRight, g (Sum.inr b) := by
  conv_lhs => rw [← Finset.toLeft_disjSum_toRight (u := u)]
  exact Finset.sum_disjSum _ _ _

namespace LevyDriver

variable (D : LevyDriver.{u, v, w} P d ν)

/-- The joint family: the coordinate values of `W` before `T` and the window counts of `N`
before `T`. -/
noncomputable def jointFamily (T : ℝ) :
    (Fin d × Set.Iic T) ⊕ Poisson.WindowSet E ν T → Ω → ℝ
  | Sum.inl p => (D.W.W p.1).W (p.2 : ℝ)
  | Sum.inr B => fun ω => (D.N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal

theorem measurable_jointFamily (T : ℝ) :
    ∀ i, Measurable (D.jointFamily T i)
  | Sum.inl p => (D.W.W p.1).measurable_eval _
  | Sum.inr B => Poisson.measurable_windowCount D.N B

/-- The σ-algebra of the Brownian values and the window counts before `T`. -/
noncomputable abbrev jointWindowSigma (T : ℝ) : MeasurableSpace Ω :=
  D.W.naturalFiltration T ⊔ Poisson.windowSigma D.N T

theorem jointWindowSigma_eq_iSup_comap (T : ℝ) :
    D.jointWindowSigma T
      = ⨆ i, MeasurableSpace.comap (D.jointFamily T i) inferInstance := by
  rw [jointWindowSigma, iSup_sum,
    Brownian.Multidim.MultidimBrownianMotion.naturalFiltration_eq_iSup_comap]
  rfl

theorem jointWindowSigma_le (T : ℝ) : D.jointWindowSigma T ≤ ‹MeasurableSpace Ω› :=
  sup_le (D.W.naturalFiltration.le T)
    ((Poisson.windowSigma_le_natural D.N T).trans ((Poisson.naturalFiltration D.N).le T))

/-- The joint natural filtration at `T` lies below the augmentation of the σ-algebra of the
Brownian values and window counts before `T`. -/
theorem filtration_le_aug_jointWindowSigma (T : ℝ) :
    D.filtration T ≤ Probability.aug (D.jointWindowSigma T) ‹MeasurableSpace Ω› P := by
  rw [filtration_apply]
  refine sup_le ?_ ?_
  · exact le_trans le_sup_left (Probability.le_aug (D.jointWindowSigma_le T))
  · exact (Poisson.natural_le_aug_windowSigma D.N T).trans (Probability.aug_mono le_sup_right)

/-- The cylinder character of the joint family is a product of a Brownian cylinder character
and a window character. -/
theorem sum_jointFamily_eq (T : ℝ)
    (F : Finset ((Fin d × Set.Iic T) ⊕ Poisson.WindowSet E ν T)) (w : F → ℝ) (ω : Ω) :
    (∑ i : F, D.jointFamily T i ω * w i)
      = (∑ p ∈ F.toLeft, (D.W.W p.1).W (p.2 : ℝ) ω * extendZero F w (Sum.inl p))
        + ∑ B ∈ F.toRight,
            (D.N.N ω (B : Set (ℝ × E))).toReal * extendZero F w (Sum.inr B) := by
  have h1 : (∑ i : F, D.jointFamily T i ω * w i)
      = ∑ i ∈ F, D.jointFamily T i ω * extendZero F w i := by
    rw [← Finset.sum_coe_sort F (fun i => D.jointFamily T i ω * extendZero F w i)]
    exact Finset.sum_congr rfl fun i _ => by rw [extendZero_coe]
  rw [h1, Finset.sum_toLeft_add_sum_toRight]
  rfl

/-- **Product characters separate on the joint window σ-algebra.** -/
theorem ae_eq_zero_of_integral_char_jointWindowSigma (T : ℝ) {Z : Ω → ℂ}
    (hZ : Integrable Z P) (hZm : StronglyMeasurable[D.jointWindowSigma T] Z)
    (h : ∀ (F : Finset (Fin d × Set.Iic T)) (G : Finset (Poisson.WindowSet E ν T))
      (w : F → ℝ) (v : G → ℝ),
      ∫ ω, Complex.exp (((∑ p : F, (D.W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((∑ B : G, (D.N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal
            * v B : ℝ) : ℂ) * Complex.I) * Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by
  refine Probability.ae_eq_zero_of_integral_char_cylinder_eq_zero (Y := D.jointFamily T)
    (D.measurable_jointFamily T) (D.jointWindowSigma_le T)
    (D.jointWindowSigma_eq_iSup_comap T) hZ hZm ?_
  intro F w
  refine Eq.trans ?_ (h F.toLeft F.toRight (fun p => extendZero F w (Sum.inl p))
    (fun B => extendZero F w (Sum.inr B)))
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
  have hw : ∀ i : F, (⟪D.jointFamily T i ω, w i⟫ : ℝ) = D.jointFamily T i ω * w i :=
    fun i => by simp [RCLike.inner_apply, mul_comm]
  simp only [hw]
  rw [D.sum_jointFamily_eq T F w ω,
    ← Finset.sum_coe_sort F.toLeft
      (fun p => (D.W.W p.1).W (p.2 : ℝ) ω * extendZero F w (Sum.inl p)),
    ← Finset.sum_coe_sort F.toRight
      (fun B => (D.N.N ω (B : Set (ℝ × E))).toReal * extendZero F w (Sum.inr B)),
    Complex.ofReal_add, add_mul, Complex.exp_add]

/-- **Product characters separate on the augmented joint filtration.** An integrable weight,
almost everywhere strongly measurable for the joint natural filtration at `T` augmented by the
null sets, and integrating to zero against every product of a Brownian cylinder character and a
window character, vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_char_joint (T : ℝ) {Z : Ω → ℂ} (hZ : Integrable Z P)
    (hZm : AEStronglyMeasurable[Probability.aug (D.filtration T) ‹MeasurableSpace Ω› P] Z P)
    (h : ∀ (F : Finset (Fin d × Set.Iic T)) (G : Finset (Poisson.WindowSet E ν T))
      (w : F → ℝ) (v : G → ℝ),
      ∫ ω, Complex.exp (((∑ p : F, (D.W.W p.1.1).W (p.1.2 : ℝ) ω * w p : ℝ) : ℂ) * Complex.I)
        * Complex.exp (((∑ B : G, (D.N.N ω ((B : Poisson.WindowSet E ν T) : Set (ℝ × E))).toReal
            * v B : ℝ) : ℂ) * Complex.I) * Z ω ∂P = 0) :
    Z =ᵐ[P] 0 := by
  obtain ⟨Z₁, hZ₁m, hZZ₁⟩ := hZm
  have hZ₁m' :
      StronglyMeasurable[Probability.aug (D.jointWindowSigma T) ‹MeasurableSpace Ω› P] Z₁ :=
    hZ₁m.mono (Probability.aug_le_of_le_aug (D.filtration_le_aug_jointWindowSigma T))
  obtain ⟨Y, hYm, hZ₁Y⟩ := Probability.aestronglyMeasurable_of_stronglyMeasurable_aug hZ₁m'
  have hZY : Z =ᵐ[P] Y := hZZ₁.trans hZ₁Y
  refine hZY.trans
    (D.ae_eq_zero_of_integral_char_jointWindowSigma T (hZ.congr hZY) hYm fun F G w v => ?_)
  rw [← h F G w v]
  refine integral_congr_ae ?_
  filter_upwards [hZY] with ω hω
  rw [hω]

end LevyDriver

end LevyStochCalc.Driver
