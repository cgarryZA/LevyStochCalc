/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
import LevyStochCalc.Driver.JointChaosProfileComplex
import LevyStochCalc.Poisson.ProfileChaosExpansion
import LevyStochCalc.Poisson.ProfileExpVectorCont
import LevyStochCalc.Probability.WienerChaosExpansion

/-!
# The joint chaos expansion of the exponential vector of a step at a mark profile

For a Lévy driver, a coordinate `j`, a step `(a, b]` with `τ = b − a`, a finite pairwise disjoint
family `A` of mark sets of finite intensity, a Brownian frequency `α` and a complex profile `c`
constant on each mark set, the block of total degree `e` of the step is

  `C_e(α, c; A) = ∑_(r + s = e) ((i α) ^ r / r!) H_r(ΔWʲ; τ) (D_s(c) / s!)`,

a combination of the complex joint chaos elements of the bidegrees `(r, s)` with `r + s = e`.
Through the bidegree Gram across families and the binomial identity
`∑_(r + s = e) x ^ r y ^ s / (r! s!) = (x + y) ^ e / e!`, blocks of different total degree are
orthogonal whatever the two families, and

  `E[C_e(α, c; A) C_e(α', c'; A')] = (τ (⟨c, c'⟩ − α α')) ^ e / e!`,
  `E‖C_e(α, c; A)‖ ^ 2 = (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k))) ^ e / e!`,

with `⟨c, c'⟩ = ∑_(k, l) c_k c'_l ν(A k ∩ A' l)`. The blocks are the Cauchy product of the Wiener
chaos series of the increment, absolutely summable everywhere, and the chaos series of the strips,
absolutely summable almost everywhere, so they sum almost everywhere, and by the summability of
their `L²` norms in `L²(P; ℂ)`, to the joint exponential vector `V_W(α) V_N(c; A)`, the product of
the exponential vector of the increment and that of the strips; its second moment is
`exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`. At `c_k = e^{i u h_k} − 1` for a simple mark profile `h`
the joint exponential vector is almost surely `V_W(α) 𝓔_u(h)`, with `𝓔_u(h)` the exponential vector
of the step at `h`, and the constants of the block moments are
`∫ ‖e^{i u h} − 1‖ ^ 2 dν` and `∫ (e^{i u h} − 1) ^ 2 dν`. The product `V_W(α) 𝓔_u(h)` depends
continuously on `h ∈ L²(ν)`, as the first factor is bounded.

## Main definitions

* `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC` — the block of total degree `e`.
* `LevyStochCalc.Driver.LevyDriver.jointProfileExpVector` — the joint exponential vector.

## Main statements

* `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_cross`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_mul_conj_cross` — the block Gram
  across two mark families.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileBlockC`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_sq` — the two second moments.
* `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_zero`,
  `LevyStochCalc.Driver.LevyDriver.jointProfileBlockC_one` — the blocks of total degree zero and
  one, `1` and `i α ΔWʲ + ∑_k c_k Ñ((a, b] ×ˢ A k)`.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileBlockC_simpleProfile`,
  `LevyStochCalc.Driver.LevyDriver.integral_jointProfileBlockC_sq_simpleProfile` — the second
  moments at `c_k = e^{i u h_k} − 1` through `∫ ‖e^{i u h} − 1‖ ^ 2 dν` and
  `∫ (e^{i u h} − 1) ^ 2 dν`.
* `LevyStochCalc.Driver.LevyDriver.integral_coeff_mul_jointProfileBlockC_mul_conj` — the pairing
  of blocks against a coefficient measurable at the node preceding the step.
* `LevyStochCalc.Driver.LevyDriver.hasSum_jointProfileBlockC` — the blocks sum almost everywhere
  to the joint exponential vector.
* `LevyStochCalc.Driver.LevyDriver.hasSum_toLp_jointProfileBlockC` — the same in `L²(P; ℂ)`.
* `LevyStochCalc.Driver.LevyDriver.integral_norm_sq_jointProfileExpVector` —
  `E‖V_W(α) V_N(c; A)‖ ^ 2 = exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`.
* `LevyStochCalc.Driver.LevyDriver.jointProfileExpVector_ae_eq` — at `c_k = e^{i u h_k} − 1` the
  joint exponential vector is `V_W(α) 𝓔_u(h)`.
* `LevyStochCalc.Driver.LevyDriver.hasSum_toLp_jointProfileBlockC_simpleProfile` — the blocks
  sum in `L²(P; ℂ)` to `V_W(α) 𝓔_u(h)`.
* `LevyStochCalc.Driver.LevyDriver.tendsto_eLpNorm_wienerExpVector_mul_profileExpVector_sub` —
  `V_W(α) 𝓔_u(h)` is continuous in `h` from `L²(ν)` to `L²(P; ℂ)`.
-/

namespace LevyStochCalc.Driver.LevyDriver

open MeasureTheory ProbabilityTheory LevyStochCalc.Probability LevyStochCalc.Poisson Finset
  Filter
open scoped NNReal ENNReal Topology

universe u v w

section Expansion

variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E] {P : Measure Ω}
  [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν] {d : ℕ}

/-! ### Blocks of a total degree -/

/-- The block of total degree `e` of the step `(a, b]` at the Brownian frequency `α` and the
complex profile `c` on the family `A`: `∑_(r + s = e) ((i α) ^ r / r!) H_r (D_s(c) / s!)`. -/
noncomputable def jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) (ω : Ω) : ℂ :=
  ∑ rs ∈ antidiagonal e,
    wienerChaosStepC rs.1 (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
      * (markedChaosDegreeC D.N rs.2 (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω
        / (rs.2.factorial : ℂ))

/-- A block as a combination of the bidegree elements. -/
theorem jointProfileBlockC_eq_sum (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) (ω : Ω) :
    D.jointProfileBlockC j a b A α c e ω
      = ∑ rs ∈ antidiagonal e, (Complex.I * α) ^ rs.1
          / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
          * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω := by
  refine Finset.sum_congr rfl fun rs _ => ?_
  rw [wienerChaosStepC, jointChaosStepProfileC]
  field_simp

/-- The conjugate of a block is the block at the opposite frequency and the conjugate profile. -/
theorem conj_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) (a b : ℝ≥0)
    {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) (ω : Ω) :
    (starRingEnd ℂ) (D.jointProfileBlockC j a b A α c e ω)
      = D.jointProfileBlockC j a b A (-α) (fun k => (starRingEnd ℂ) (c k)) e ω := by
  rw [jointProfileBlockC_eq_sum, jointProfileBlockC_eq_sum, map_sum]
  refine Finset.sum_congr rfl fun rs _ => ?_
  rw [map_mul, map_div₀, map_pow, map_mul, Complex.conj_I, Complex.conj_ofReal, map_mul,
    Complex.conj_natCast, Complex.conj_natCast, conj_jointChaosStepProfileC]
  push_cast
  ring

/-- The block of total degree zero is `1`. -/
@[simp] theorem jointProfileBlockC_zero (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (ω : Ω) :
    D.jointProfileBlockC j a b A α c 0 ω = 1 := by
  simp [jointProfileBlockC, wienerChaosStepC]

/-- The block of total degree one is `i α ΔWʲ + ∑_k c_k Ñ((a, b] ×ˢ A k)`. -/
theorem jointProfileBlockC_one (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (ω : Ω) :
    D.jointProfileBlockC j a b A α c 1 ω
      = Complex.I * α * (((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω : ℝ) : ℂ)
        + ∑ k, c k * (D.N.compensated (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) ω : ℂ) := by
  rw [jointProfileBlockC, Finset.Nat.antidiagonal_succ]
  simp [wienerChaosStepC, wienerChaosStep, markedChaosDegreeC_one]
  ring

/-- A block of a step at a profile on a finite pairwise disjoint family of mark sets of finite
intensity lies in `L²`. -/
theorem memLp_two_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) (e : ℕ) :
    MemLp (D.jointProfileBlockC j a b A α c e) 2 P := by
  have h := memLp_finsetSum (μ := P) (p := 2) (antidiagonal e)
    (f := fun rs (ω : Ω) => (Complex.I * α) ^ rs.1
      / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
      * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω)
    fun rs _ => (D.memLp_two_jointChaosStepProfileC j hab hA hAν hd rs.1 rs.2 c).const_mul _
  rw [show D.jointProfileBlockC j a b A α c e = fun ω => ∑ rs ∈ antidiagonal e,
      (Complex.I * α) ^ rs.1 / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
        * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω from
    funext (D.jointProfileBlockC_eq_sum j a b A α c e)]
  exact h

/-- **The block Gram across two mark families.** Blocks of different total degree are
orthogonal, and
`E[C_e(α, c; A) C_e(α', c'; A')] = (τ (∑_(k, l) c_k c'_l ν(A k ∩ A' l) − α α')) ^ e / e!`. -/
theorem integral_jointProfileBlockC_mul_cross (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (α α' : ℝ) (c : Fin p → ℂ) (c' : Fin q → ℂ) (e e' : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b A α c e ω * D.jointProfileBlockC j a b A' α' c' e' ω ∂P
      = if e = e' then ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A' l)).toReal : ℂ) - (α : ℂ) * α')) ^ e
          / (e.factorial : ℂ) else 0 := by
  classical
  set τ : ℂ := (((b : ℝ) - (a : ℝ) : ℝ) : ℂ) with hτ
  set L : ℂ := ∑ k, ∑ l, c k * c' l * ((ν (A k ∩ A' l)).toReal : ℂ) with hL
  set κ : ℝ → ℕ × ℕ → ℂ := fun β rs => (Complex.I * β) ^ rs.1
    / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ)) with hκ
  set F : ℕ × ℕ → ℕ × ℕ → Ω → ℂ := fun rs rs' ω => (κ α rs * κ α' rs')
    * (D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω
      * D.jointChaosStepProfileC j rs'.1 rs'.2 a b A' c' ω) with hF
  have hint : ∀ rs rs', Integrable (F rs rs') P := fun rs rs' =>
    ((D.memLp_two_jointChaosStepProfileC j hab hA hAν hd rs.1 rs.2 c).integrable_mul
      (D.memLp_two_jointChaosStepProfileC j hab hA' hAν' hd' rs'.1 rs'.2 c')).const_mul _
  have hexp : (fun ω => D.jointProfileBlockC j a b A α c e ω
      * D.jointProfileBlockC j a b A' α' c' e' ω)
      = fun ω => ∑ rs ∈ antidiagonal e, ∑ rs' ∈ antidiagonal e', F rs rs' ω := by
    funext ω
    rw [jointProfileBlockC_eq_sum, jointProfileBlockC_eq_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun rs _ => Finset.sum_congr rfl fun rs' _ => ?_
    simp only [hF, hκ]
    ring
  have hterm : ∀ rs rs', ∫ ω, F rs rs' ω ∂P = (κ α rs * κ α' rs')
      * ((((if rs.1 = rs'.1 then (rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1 else 0 : ℝ))
          : ℂ) * (if rs.2 = rs'.2 then (rs.2.factorial : ℂ) * (τ * L) ^ rs.2 else 0)) := by
    intro rs rs'
    rw [hF, integral_const_mul, D.integral_jointChaosStepProfileC_mul_cross j hab hA hAν hd
      hA' hAν' hd']
  rw [hexp, integral_finsetSum _ fun rs _ => integrable_finsetSum _ fun rs' _ => hint rs rs']
  simp_rw [integral_finsetSum _ fun rs' _ => hint _ rs', hterm]
  have hkill : ∀ rs rs' : ℕ × ℕ, rs ≠ rs' →
      (((if rs.1 = rs'.1 then (rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1 else 0 : ℝ))
        : ℂ) * (if rs.2 = rs'.2 then (rs.2.factorial : ℂ) * (τ * L) ^ rs.2 else 0) = 0 := by
    intro rs rs' hne
    by_cases h1 : rs.1 = rs'.1
    · have h2 : rs.2 ≠ rs'.2 := fun h => hne (Prod.ext h1 h)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, Complex.ofReal_zero, zero_mul]
  split_ifs with hee
  · subst hee
    have hdiag : ∀ rs ∈ antidiagonal e, (∑ rs' ∈ antidiagonal e, κ α rs * κ α' rs'
        * ((((if rs.1 = rs'.1 then (rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1
            else 0 : ℝ)) : ℂ)
          * (if rs.2 = rs'.2 then (rs.2.factorial : ℂ) * (τ * L) ^ rs.2 else 0)))
        = (τ * (-((α : ℂ) * α'))) ^ rs.1 * (τ * L) ^ rs.2
          / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ)) := by
      intro rs hrs
      rw [Finset.sum_eq_single_of_mem rs hrs fun rs' _ hne => by
        rw [hkill rs rs' (Ne.symm hne), mul_zero]]
      rw [if_pos rfl, if_pos rfl]
      simp only [hκ]
      have hB : ((((rs.1.factorial : ℝ) * ((b : ℝ) - (a : ℝ)) ^ rs.1 : ℝ)) : ℂ)
          = (rs.1.factorial : ℂ) * τ ^ rs.1 := by
        rw [hτ]; push_cast; ring
      rw [div_mul_div_comm, ← mul_pow, show Complex.I * (α : ℂ) * (Complex.I * (α' : ℂ))
        = -((α : ℂ) * α') by ring_nf; rw [Complex.I_sq]; ring, hB, mul_pow τ]
      generalize -((α : ℂ) * α') = X
      generalize τ * L = Y
      field_simp
      ring
    rw [Finset.sum_congr rfl hdiag, sum_antidiagonal_div_factorial]
    congr 1
    ring
  · refine Finset.sum_eq_zero fun rs hrs => Finset.sum_eq_zero fun rs' hrs' => ?_
    have hne : rs ≠ rs' := by
      rintro rfl
      exact hee ((mem_antidiagonal.1 hrs).symm.trans (mem_antidiagonal.1 hrs'))
    rw [hkill rs rs' hne, mul_zero]

/-- **The Hermitian block Gram across two mark families.** Blocks of different total degree are
orthogonal, and
`E[C_e(α, c; A) conj C_e(α', c'; A')] = (τ (∑_(k, l) c_k conj c'_l ν(A k ∩ A' l) + α α')) ^ e / e!`.
-/
theorem integral_jointProfileBlockC_mul_conj_cross (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (hA' : ∀ l, MeasurableSet (A' l))
    (hAν' : ∀ l, ν (A' l) ≠ ⊤) (hd' : Pairwise fun k l => Disjoint (A' k) (A' l))
    (α α' : ℝ) (c : Fin p → ℂ) (c' : Fin q → ℂ) (e e' : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b A α c e ω
        * (starRingEnd ℂ) (D.jointProfileBlockC j a b A' α' c' e' ω) ∂P
      = if e = e' then ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∑ k, ∑ l, c k * (starRingEnd ℂ) (c' l) * ((ν (A k ∩ A' l)).toReal : ℂ)
            + (α : ℂ) * α')) ^ e / (e.factorial : ℂ) else 0 := by
  simp_rw [conj_jointProfileBlockC]
  rw [D.integral_jointProfileBlockC_mul_cross j hab hA hAν hd hA' hAν' hd']
  push_cast
  ring_nf

/-- The second moment of the modulus of a block,
`E‖C_e(α, c; A)‖ ^ 2 = (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k))) ^ e / e!`. -/
theorem integral_norm_sq_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) (e : ℕ) :
    ∫ ω, ‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 ∂P
      = (((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal)) ^ e
          / (e.factorial : ℝ) := by
  have h := D.integral_jointProfileBlockC_mul_conj_cross j hab hA hAν hd hA hAν hd α α c c e e
  rw [if_pos rfl, sum_sum_mul_measure_inter_self hd] at h
  have hpt : ∀ ω, ((‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 : ℝ) : ℂ)
      = D.jointProfileBlockC j a b A α c e ω
        * (starRingEnd ℂ) (D.jointProfileBlockC j a b A α c e ω) := by
    intro ω
    rw [Complex.mul_conj']
    push_cast
    ring
  have hs : ∑ k, c k * (starRingEnd ℂ) (c k) * ((ν (A k)).toReal : ℂ)
      = ((∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj']
  refine Complex.ofReal_injective ?_
  rw [← integral_complex_ofReal, integral_congr_ae (Eventually.of_forall hpt), h, hs]
  push_cast
  ring

/-- The bilinear second moment of a block,
`E[C_e(α, c; A) ^ 2] = (τ (∑_k c_k ^ 2 ν(A k) − α ^ 2)) ^ e / e!`. -/
theorem integral_jointProfileBlockC_sq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) (e : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b A α c e ω ^ 2 ∂P
      = ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∑ k, c k ^ 2 * ((ν (A k)).toReal : ℂ) - (α : ℂ) ^ 2)) ^ e / (e.factorial : ℂ) := by
  have h := D.integral_jointProfileBlockC_mul_cross j hab hA hAν hd hA hAν hd α α c c e e
  rw [if_pos rfl, sum_sum_mul_measure_inter_self hd] at h
  simp_rw [sq]
  rw [h]

/-- A block of a step at a profile on a family of mark sets whose strips are members of the
family `C` is measurable for the σ-algebra of the step over `C`. -/
theorem measurable_jointProfileBlockC_stepSigma (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {m p : ℕ} (C : Fin m → Set (ℝ × E)) {A : Fin p → Set E}
    (hAC : ∀ k, ∃ i, C i = Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) (α : ℝ) (c : Fin p → ℂ) (e : ℕ) :
    Measurable[D.stepSigma C (a : ℝ) (b : ℝ)] (D.jointProfileBlockC j a b A α c e) := by
  rw [show D.jointProfileBlockC j a b A α c e = fun ω => ∑ rs ∈ antidiagonal e,
      (Complex.I * α) ^ rs.1 / ((rs.1.factorial : ℂ) * (rs.2.factorial : ℂ))
        * D.jointChaosStepProfileC j rs.1 rs.2 a b A c ω from
    funext (D.jointProfileBlockC_eq_sum j a b A α c e)]
  exact Finset.measurable_sum _ fun rs _ =>
    (D.measurable_jointChaosStepProfileC_stepSigma j rs.1 rs.2 a b C hAC c).const_mul _

/-! ### The joint exponential vector -/

/-- The joint exponential vector of the step `(a, b]` at the Brownian frequency `α` and the
complex profile `c` on the family `A`: the exponential vector of the increment of the coordinate
`j` times the exponential vector of the strips `(a, b] ×ˢ A k`. -/
noncomputable def jointProfileExpVector (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    (a b : ℝ≥0) {p : ℕ} (A : Fin p → Set E) (α : ℝ) (c : Fin p → ℂ) (ω : Ω) : ℂ :=
  wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
    * markedExpVector D.N (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω

/-- **The blocks sum to the joint exponential vector.** The blocks of a step at a profile on a
finite pairwise disjoint family of mark sets of finite intensity sum almost everywhere to the
joint exponential vector. -/
theorem hasSum_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (α : ℝ) (c : Fin p → ℂ) :
    ∀ᵐ ω ∂P, HasSum (fun e : ℕ => D.jointProfileBlockC j a b A α c e ω)
      (D.jointProfileExpVector j a b A α c ω) := by
  filter_upwards [hasSum_markedChaosDegreeC D.N (fun k => measurableSet_Ioc.prod (hA k))
    (fun k => referenceIntensity_strip_ne_top a.coe_nonneg (hAν k)) c] with ω hω
  set x : ℝ := (D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω with hx
  set f : ℕ → ℂ := fun r => wienerChaosStepC r (b - a) α x with hf
  set g : ℕ → ℂ := fun s => markedChaosDegreeC D.N s
    (fun k => Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A k) c ω / (s.factorial : ℂ) with hg
  have hfn : Summable fun r => ‖f r‖ := by
    refine (summable_norm_hermiteScaled ((b - a : ℝ≥0) : ℝ) x (Complex.I * α)).congr
      fun r => ?_
    simp only [hf, wienerChaosStepC, wienerChaosStep]
  have hfs : HasSum f (wienerExpVector (b - a) α x) := hasSum_wienerChaosStepC (b - a) α x
  have hprod : Summable fun e : ℕ => ∑ rs ∈ antidiagonal e, f rs.1 * g rs.2 :=
    (summable_norm_sum_mul_antidiagonal_of_summable_norm hfn hω.1).of_norm
  have hval : (∑' e : ℕ, ∑ rs ∈ antidiagonal e, f rs.1 * g rs.2)
      = D.jointProfileExpVector j a b A α c ω := by
    rw [← tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hfn hω.1, hfs.tsum_eq,
      hω.2.tsum_eq]
    rfl
  have hsum := hprod.hasSum
  rw [hval] at hsum
  exact hsum

/-- The `L²` norms of the blocks are summable. -/
theorem summable_sqrt_integral_norm_sq_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hAν : ∀ k, ν (A k) ≠ ⊤)
    (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ) (c : Fin p → ℂ) :
    Summable fun e : ℕ => Real.sqrt (∫ ω, ‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 ∂P) := by
  have hτ : (0 : ℝ) ≤ (b : ℝ) - (a : ℝ) := sub_nonneg.2 (by exact_mod_cast hab)
  refine (summable_sqrt_pow_div_factorial
    (x := ((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal))
    (by positivity)).congr fun e => ?_
  rw [D.integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c e]

/-- The joint exponential vector of a step lies in `L²`. -/
theorem memLp_two_jointProfileExpVector (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) :
    MemLp (D.jointProfileExpVector j a b A α c) 2 P :=
  memLp_two_of_hasSum_ae (fun e => D.memLp_two_jointProfileBlockC j hab hA hAν hd α c e)
    (D.summable_sqrt_integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c)
    (D.hasSum_jointProfileBlockC j hA hAν α c)

/-- **The joint chaos expansion in `L²`.** The blocks of a step at a profile on a finite pairwise
disjoint family of mark sets of finite intensity sum in `L²(P; ℂ)` to the joint exponential
vector. -/
theorem hasSum_toLp_jointProfileBlockC (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) :
    HasSum (fun e : ℕ => (D.memLp_two_jointProfileBlockC j hab hA hAν hd α c e).toLp
        (D.jointProfileBlockC j a b A α c e))
      ((D.memLp_two_jointProfileExpVector j hab hA hAν hd α c).toLp
        (D.jointProfileExpVector j a b A α c)) :=
  hasSum_toLp_of_summable_norm _ _
    (D.summable_sqrt_integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c)
    (D.hasSum_jointProfileBlockC j hA hAν α c)

/-- The second moment of the modulus of the joint exponential vector,
`E‖V_W(α) V_N(c; A)‖ ^ 2 = exp (τ (α ^ 2 + ∑_k ‖c_k‖ ^ 2 ν(A k)))`. -/
theorem integral_norm_sq_jointProfileExpVector (D : LevyDriver.{u, v, w} P d ν) (j : Fin d)
    {a b : ℝ≥0} (hab : a ≤ b) {p : ℕ} {A : Fin p → Set E} (hA : ∀ k, MeasurableSet (A k))
    (hAν : ∀ k, ν (A k) ≠ ⊤) (hd : Pairwise fun k l => Disjoint (A k) (A l)) (α : ℝ)
    (c : Fin p → ℂ) :
    ∫ ω, ‖D.jointProfileExpVector j a b A α c ω‖ ^ 2 ∂P
      = Real.exp (((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal)) := by
  have h1 := hasSum_integral_norm_sq_of_hasSum_toLp _ _ (fun e e' hee => ?_)
    (D.hasSum_toLp_jointProfileBlockC j hab hA hAν hd α c)
  · have h2 : HasSum (fun e : ℕ => ∫ ω, ‖D.jointProfileBlockC j a b A α c e ω‖ ^ 2 ∂P)
        (Real.exp (((b : ℝ) - (a : ℝ)) * (α ^ 2 + ∑ k, ‖c k‖ ^ 2 * (ν (A k)).toReal))) := by
      rw [Real.exp_eq_exp_ℝ]
      refine (NormedSpace.expSeries_div_hasSum_exp _).congr_fun fun e => ?_
      rw [D.integral_norm_sq_jointProfileBlockC j hab hA hAν hd α c e]
    exact h1.unique h2
  · have h := D.integral_jointProfileBlockC_mul_conj_cross j hab hA hAν hd hA hAν hd α α c c e' e
    rw [if_neg (Ne.symm hee)] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only
    ring

/-- **The joint exponential vector at a simple profile.** At the profile `c_k = e^{i u h_k} − 1`
of the values of a simple mark profile `h`, the joint exponential vector of the strips of its mark
sets is almost surely the exponential vector of the increment times the exponential vector
`𝓔_u(h)` of the step at `h`. -/
theorem jointProfileExpVector_ae_eq (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0}
    (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) :
    D.jointProfileExpVector j a b G.B α
        (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1)
      =ᵐ[P] fun ω => wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
        * profileExpVector D.N G.toFun (a : ℝ) (b : ℝ) u ω := by
  filter_upwards [profileExpVector_ae_eq_markedExpVector D.N G a.coe_nonneg
    (by exact_mod_cast hab) u] with ω hω
  exact congrArg (fun z => wienerExpVector (b - a) α
    ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω) * z) hω.symm

/-- **The block moments at a simple profile, modulus.** At the profile `c_k = e^{i u h_k} − 1` of
the values of a simple mark profile `h`,
`E‖C_e(α, c; A)‖ ^ 2 = (τ (α ^ 2 + ∫ ‖e^{i u h} − 1‖ ^ 2 dν)) ^ e / e!`. -/
theorem integral_norm_sq_jointProfileBlockC_simpleProfile (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) (e : ℕ) :
    ∫ ω, ‖D.jointProfileBlockC j a b G.B α
        (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e ω‖ ^ 2 ∂P
      = (((b : ℝ) - (a : ℝ)) * (α ^ 2
          + ∫ x, ‖Complex.exp (Complex.I * ((u * G.toFun x : ℝ) : ℂ)) - 1‖ ^ 2 ∂ν)) ^ e
          / (e.factorial : ℝ) := by
  rw [D.integral_norm_sq_jointProfileBlockC j hab G.B_measurable G.B_finite G.B_disjoint,
    SimpleProfile.integral_comp_toFun G
      (fun x => ‖Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1‖ ^ 2) (by simp)]
  simp_rw [smul_eq_mul, mul_comm ((ν (G.B _)).toReal)]

/-- **The block moments at a simple profile, bilinear.** At the profile `c_k = e^{i u h_k} − 1`
of the values of a simple mark profile `h`,
`E[C_e(α, c; A) ^ 2] = (τ (∫ (e^{i u h} − 1) ^ 2 dν − α ^ 2)) ^ e / e!`. -/
theorem integral_jointProfileBlockC_sq_simpleProfile (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) (e : ℕ) :
    ∫ ω, D.jointProfileBlockC j a b G.B α
        (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e ω ^ 2 ∂P
      = ((((b : ℝ) - (a : ℝ) : ℝ) : ℂ)
          * (∫ x, (Complex.exp (Complex.I * ((u * G.toFun x : ℝ) : ℂ)) - 1) ^ 2 ∂ν
            - (α : ℂ) ^ 2)) ^ e / (e.factorial : ℂ) := by
  rw [D.integral_jointProfileBlockC_sq j hab G.B_measurable G.B_finite G.B_disjoint,
    SimpleProfile.integral_comp_toFun G
      (fun x => (Complex.exp (Complex.I * ((u * x : ℝ) : ℂ)) - 1) ^ 2) (by simp)]
  simp_rw [Complex.real_smul, mul_comm ((ν (G.B _)).toReal : ℂ)]

/-- The exponential vector of the increment times the exponential vector of the step at a simple
profile lies in `L²`. -/
theorem memLp_two_wienerExpVector_mul_profileExpVector (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) :
    MemLp (fun ω => wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
      * profileExpVector D.N G.toFun (a : ℝ) (b : ℝ) u ω) 2 P :=
  (D.memLp_two_jointProfileExpVector j hab G.B_measurable G.B_finite G.B_disjoint α _).ae_eq
    (D.jointProfileExpVector_ae_eq j hab G α u)

/-- **The joint chaos expansion at a simple profile.** At the profile `c_k = e^{i u h_k} − 1` of
the values of a simple mark profile `h`, the blocks sum in `L²(P; ℂ)` to the exponential vector
of the increment times the exponential vector `𝓔_u(h)` of the step at `h`. -/
theorem hasSum_toLp_jointProfileBlockC_simpleProfile (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) (G : SimpleProfile E ν) (α u : ℝ) :
    HasSum (fun e : ℕ => (D.memLp_two_jointProfileBlockC j hab G.B_measurable G.B_finite
        G.B_disjoint α (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e).toLp
        (D.jointProfileBlockC j a b G.B α
          (fun k => Complex.exp (Complex.I * ((u * G.c k : ℝ) : ℂ)) - 1) e))
      ((D.memLp_two_wienerExpVector_mul_profileExpVector j hab G α u).toLp
        (fun ω => wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * profileExpVector D.N G.toFun (a : ℝ) (b : ℝ) u ω)) := by
  rw [← MemLp.toLp_congr _ _ (D.jointProfileExpVector_ae_eq j hab G α u)]
  exact D.hasSum_toLp_jointProfileBlockC j hab G.B_measurable G.B_finite G.B_disjoint α _

/-- **Continuity of the joint exponential vector in the profile.** If square-integrable mark
profiles `h_n` converge to `h` in `L²(ν)`, then `V_W(α) 𝓔_u(h_n) → V_W(α) 𝓔_u(h)` in
`L²(P; ℂ)`. -/
theorem tendsto_eLpNorm_wienerExpVector_mul_profileExpVector_sub
    (D : LevyDriver.{u, v, w} P d ν) (j : Fin d) {a b : ℝ≥0} (hab : a ≤ b) {h : ℕ → E → ℝ}
    {f : E → ℝ} (hh : ∀ n, MemLp (h n) 2 ν) (hf : MemLp f 2 ν) (α u : ℝ)
    (hc : Tendsto (fun n => eLpNorm (fun e => h n e - f e) 2 ν) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (fun ω =>
      wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * profileExpVector D.N (h n) (a : ℝ) (b : ℝ) u ω
        - wienerExpVector (b - a) α ((D.W.W j).W (b : ℝ) ω - (D.W.W j).W (a : ℝ) ω)
          * profileExpVector D.N f (a : ℝ) (b : ℝ) u ω) 2 P) atTop (𝓝 0) :=
  Probability.tendsto_eLpNorm_mul_sub_mul (C := Real.exp (α ^ 2 * ((b - a : ℝ≥0) : ℝ) / 2))
    (fun ω => (norm_wienerExpVector _ _ _).le)
    (tendsto_eLpNorm_profileExpVector_sub D.N hh hf a.coe_nonneg (by exact_mod_cast hab) u hc)

end Expansion

/-! ### The pairing of blocks at the node preceding the step -/

section Node

variable {Ω : Type u} {M : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω] {E : Type v}
  [MeasurableSpace E] {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  {d : ℕ}

/-- **The pairing of blocks at the node across two mark families.** Against a complex
coefficient `Q` measurable for a σ-algebra `M` independent of the σ-algebra of the step over
`(a, b]` and every finite family of measurable regions inside `(a, b] ×ˢ E` (such as the joint
filtration at `a`), the Hermitian pairing of two blocks of the step over two families of mark sets
is the mean of `Q` times their pairing. -/
theorem integral_coeff_mul_jointProfileBlockC_mul_conj (D : LevyDriver.{u, v, w} P d ν)
    (j : Fin d) {a b : ℝ≥0} {p q : ℕ} {A : Fin p → Set E} {A' : Fin q → Set E}
    (hA : ∀ k, MeasurableSet (A k)) (hA' : ∀ l, MeasurableSet (A' l)) (hM : M ≤ mΩ)
    (hind : ∀ {m : ℕ} (C : Fin m → Set (ℝ × E)), (∀ k, MeasurableSet (C k)) →
      (∀ k, C k ⊆ Set.Ioc (a : ℝ) (b : ℝ) ×ˢ Set.univ) →
        Indep (D.stepSigma C (a : ℝ) (b : ℝ)) M P)
    {Q : Ω → ℂ} (hQ : StronglyMeasurable[M] Q) (α α' : ℝ) (c : Fin p → ℂ)
    (c' : Fin q → ℂ) (e e' : ℕ) :
    ∫ ω, Q ω * (D.jointProfileBlockC j a b A α c e ω
        * (starRingEnd ℂ) (D.jointProfileBlockC j a b A' α' c' e' ω)) ∂P
      = (∫ ω, Q ω ∂P) * ∫ ω, D.jointProfileBlockC j a b A α c e ω
          * (starRingEnd ℂ) (D.jointProfileBlockC j a b A' α' c' e' ω) ∂P := by
  have hCm := measurableSet_append_strip a b hA hA'
  refine D.integral_mul_eq_mul_integral_of_indep_stepSigma _ hCm _ _ hM
    (hind _ hCm (append_strip_subset a b A A')) hQ ?_
  simp_rw [conj_jointProfileBlockC]
  exact (D.measurable_jointProfileBlockC_stepSigma j a b _
      (fun k => ⟨Fin.castAdd q k, Fin.append_left _ _ k⟩) α c e).mul
    (D.measurable_jointProfileBlockC_stepSigma j a b _
      (fun l => ⟨Fin.natAdd p l, Fin.append_right _ _ l⟩) _ _ e')

end Node

end LevyStochCalc.Driver.LevyDriver
