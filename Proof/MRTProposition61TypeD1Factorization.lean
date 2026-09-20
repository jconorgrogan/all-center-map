import MRTCorollary25TypeD1CoefficientBound
import FarAnnulusSourceToModel

/-!
# Literal Type-d1 Dirichlet-polynomial factorization

This file connects the collected Dirichlet convolution used by Corollary 2.5
to the factored norm fields used in the Proposition 6.1 Cauchy step.
-/

namespace MAPMRTProposition61TypeD1Factorization

open scoped BigOperators
open MixedMeanFrontend
open MAPMRTCorollary25 MAPMRTCorollary25Instantiation
open MAPMRTCorollary25TypeD1LiteralWeld
open MAPFarAnnulusSourceToModel

noncomputable section

/-- The literal real dyadic support inside the finite carrier used by
`halfLineDirichletPolynomial`. -/
def realDyadicSupport (N : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (Nat.ceil (2 * N))).filter fun n ↦
    N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N

/-- One normalized character-twisted Dirichlet-polynomial term. -/
def normalizedTwistedTerm
    (phase f : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  (characterTwist phase f n / (Real.sqrt (n : ℝ) : ℂ)) * mellinPhase n t

/-- One dyadic factor in the exact normalization of MRT Section 7. -/
def dyadicFactorPolynomial
    (N : ℝ) (phase f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ realDyadicSupport N, normalizedTwistedTerm phase f n t

theorem mem_realDyadicSupport {N : ℝ} {n : ℕ} :
    n ∈ realDyadicSupport N ↔
      n ∈ Finset.Icc 1 (Nat.ceil (2 * N)) ∧
        N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N := by
  rw [realDyadicSupport, Finset.mem_filter]

theorem realDyadicSupport_pos {N : ℝ} {n : ℕ}
    (hn : n ∈ realDyadicSupport N) : 0 < n := by
  have := (Finset.mem_Icc.mp (mem_realDyadicSupport.mp hn).1).1
  omega

/-- Restricting the full finite carrier to the literal dyadic support changes
nothing when the coefficient obeys the source support condition. -/
theorem halfLineDirichletPolynomial_eq_dyadicFactorPolynomial
    {N : ℝ} {phase f : ℕ → ℂ}
    (hf : SupportedDyadic N f) (t : ℝ) :
    halfLineDirichletPolynomial N 2 (characterTwist phase f) t =
      dyadicFactorPolynomial N phase f t := by
  unfold halfLineDirichletPolynomial dyadicFactorPolynomial realDyadicSupport
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hblock : N ≤ (n : ℝ) ∧ (n : ℝ) ≤ 2 * N
  · rw [if_pos hblock]
    rfl
  · rw [if_neg hblock]
    simp [characterTwist, hf n hblock]

/-- Product-support pairs map into the finite carrier of the collected
convolution polynomial. -/
theorem product_mem_convolutionCarrier
    {N M : ℝ} (hN : 0 < N)
    {p : ℕ × ℕ}
    (hp : p ∈ (realDyadicSupport N).product (realDyadicSupport M)) :
    p.1 * p.2 ∈ Finset.Icc 1 (Nat.ceil (4 * N * M)) := by
  have hpS := Finset.mem_product.mp hp
  have hp1 := mem_realDyadicSupport.mp hpS.1
  have hp2 := mem_realDyadicSupport.mp hpS.2
  have hp1pos : 0 < p.1 := realDyadicSupport_pos hpS.1
  have hp2pos : 0 < p.2 := realDyadicSupport_pos hpS.2
  apply Finset.mem_Icc.mpr
  constructor
  · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero
      (Nat.ne_of_gt hp1pos) (Nat.ne_of_gt hp2pos))
  · have hprodReal : ((p.1 * p.2 : ℕ) : ℝ) ≤ 4 * N * M := by
      rw [Nat.cast_mul]
      have hmul := mul_le_mul hp1.2.2 hp2.2.2
        (by positivity : (0 : ℝ) ≤ p.2) (by positivity : (0 : ℝ) ≤ 2 * N)
      nlinarith
    have hceil : 4 * N * M ≤ (Nat.ceil (4 * N * M) : ℝ) := Nat.le_ceil _
    exact_mod_cast hprodReal.trans hceil

/-- A product fiber inside the two literal supports is exactly the collected
Dirichlet convolution, because every omitted divisor pair has a zero
coefficient. -/
theorem productFiber_sum_eq_literalDirichletConvolution
    {N M : ℝ} {alpha beta : ℕ → ℂ}
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    {k : ℕ} (hk : 0 < k) :
    (∑ p ∈ (realDyadicSupport N).product (realDyadicSupport M) with
        p.1 * p.2 = k, alpha p.1 * beta p.2) =
      literalDirichletConvolution alpha beta k := by
  let fiber := ((realDyadicSupport N).product (realDyadicSupport M)).filter
    fun p ↦ p.1 * p.2 = k
  have hsubset : fiber ⊆ k.divisorsAntidiagonal := by
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨hmem.2, Nat.ne_of_gt hk⟩
  have hoff : ∀ p ∈ k.divisorsAntidiagonal, p ∉ fiber →
      alpha p.1 * beta p.2 = 0 := by
    intro p hpAnti hpNot
    have hnotProd : p ∉ (realDyadicSupport N).product (realDyadicSupport M) := by
      intro hpProd
      apply hpNot
      exact Finset.mem_filter.mpr ⟨hpProd,
        (Nat.mem_divisorsAntidiagonal.mp hpAnti).1⟩
    by_cases ha : N ≤ (p.1 : ℝ) ∧ (p.1 : ℝ) ≤ 2 * N
    · by_cases hb : M ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * M
      · exfalso
        apply hnotProd
        apply Finset.mem_product.mpr
        constructor
        · apply mem_realDyadicSupport.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ha⟩
          · exact Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_zero_of_mem_divisorsAntidiagonal hpAnti).1
          · have hc : (p.1 : ℝ) ≤ (Nat.ceil (2 * N) : ℝ) :=
              ha.2.trans (Nat.le_ceil _)
            exact_mod_cast hc
        · apply mem_realDyadicSupport.mpr
          refine ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hb⟩
          · exact Nat.one_le_iff_ne_zero.mpr
              (Nat.ne_zero_of_mem_divisorsAntidiagonal hpAnti).2
          · have hc : (p.2 : ℝ) ≤ (Nat.ceil (2 * M) : ℝ) :=
              hb.2.trans (Nat.le_ceil _)
            exact_mod_cast hc
      · rw [hbeta p.2 hb, mul_zero]
    · rw [halpha p.1 ha, zero_mul]
  unfold literalDirichletConvolution
  change (∑ p ∈ fiber, alpha p.1 * beta p.2) = _
  exact Finset.sum_subset hsubset hoff

/-- The normalized term is multiplicative on positive arguments whenever the
phase is multiplicative. -/
theorem normalizedTwistedTerm_mul
    {phase alpha beta : ℕ → ℂ}
    (hphase : ∀ m n, phase (m * n) = phase m * phase n)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (t : ℝ) :
    normalizedTwistedTerm phase alpha m t *
        normalizedTwistedTerm phase beta n t =
      (phase (m * n) * (alpha m * beta n) /
          (Real.sqrt (m * n : ℕ) : ℂ)) * mellinPhase (m * n) t := by
  unfold normalizedTwistedTerm characterTwist
  rw [hphase, Nat.cast_mul, Real.sqrt_mul (by positivity : (0 : ℝ) ≤ m),
    Complex.ofReal_mul, mellinPhase_mul hm hn]
  ring

/-- The uncollected product sum over the two literal dyadic supports. -/
def uncollectedTypeD1Polynomial
    (N M : ℝ) (phase alpha beta : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ (realDyadicSupport N).product (realDyadicSupport M),
    normalizedTwistedTerm phase alpha p.1 t *
      normalizedTwistedTerm phase beta p.2 t

theorem uncollectedTypeD1Polynomial_eq_mul_factors
    (N M : ℝ) (phase alpha beta : ℕ → ℂ) (t : ℝ) :
    uncollectedTypeD1Polynomial N M phase alpha beta t =
      dyadicFactorPolynomial N phase alpha t *
        dyadicFactorPolynomial M phase beta t := by
  unfold uncollectedTypeD1Polynomial dyadicFactorPolynomial
  calc
    (∑ p ∈ (realDyadicSupport N).product (realDyadicSupport M),
        normalizedTwistedTerm phase alpha p.1 t *
          normalizedTwistedTerm phase beta p.2 t) =
      ∑ m ∈ realDyadicSupport N, ∑ n ∈ realDyadicSupport M,
        normalizedTwistedTerm phase alpha m t *
          normalizedTwistedTerm phase beta n t := by
        exact Finset.sum_product _ _ _
    _ = (∑ n ∈ realDyadicSupport N,
        normalizedTwistedTerm phase alpha n t) *
        ∑ n ∈ realDyadicSupport M,
          normalizedTwistedTerm phase beta n t := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]

/-- Exact collection of equal products. -/
theorem uncollectedTypeD1Polynomial_eq_convolutionPolynomial
    {N M : ℝ} (hN : 0 < N) (hM : 0 < M)
    {phase alpha beta : ℕ → ℂ}
    (hphase : ∀ m n, phase (m * n) = phase m * phase n)
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    (t : ℝ) :
    uncollectedTypeD1Polynomial N M phase alpha beta t =
      halfLineDirichletPolynomial (N * M) 4
        (characterTwist phase (literalDirichletConvolution alpha beta)) t := by
  let S := (realDyadicSupport N).product (realDyadicSupport M)
  let P := Finset.Icc 1 (Nat.ceil (4 * (N * M)))
  let w : ℕ × ℕ → ℂ := fun p ↦
    normalizedTwistedTerm phase alpha p.1 t *
      normalizedTwistedTerm phase beta p.2 t
  have hmaps : ∀ p ∈ S, p.1 * p.2 ∈ P := by
    intro p hp
    simpa only [P, mul_assoc] using
      (product_mem_convolutionCarrier hN hp)
  have hfiber := Finset.sum_fiberwise_of_maps_to hmaps w
  unfold uncollectedTypeD1Polynomial
  change (∑ p ∈ S, w p) = _
  rw [← hfiber]
  unfold halfLineDirichletPolynomial
  change (∑ k ∈ P, ∑ p ∈ S with p.1 * p.2 = k, w p) = _
  apply Finset.sum_congr rfl
  intro k hkP
  have hkpos : 0 < k := by
    have := (Finset.mem_Icc.mp hkP).1
    omega
  have hterm : ∀ p ∈ S, p.1 * p.2 = k →
      w p = (phase k * (alpha p.1 * beta p.2) /
          (Real.sqrt (k : ℝ) : ℂ)) * mellinPhase k t := by
    intro p hpS hpk
    have hpProd := Finset.mem_product.mp hpS
    have hp1 : 0 < p.1 := realDyadicSupport_pos hpProd.1
    have hp2 : 0 < p.2 := realDyadicSupport_pos hpProd.2
    dsimp only [w]
    rw [normalizedTwistedTerm_mul hphase hp1 hp2]
    rw [hpk]
  rw [Finset.sum_congr rfl (fun p hp ↦
    hterm p (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hp).2)]
  have hconv := productFiber_sum_eq_literalDirichletConvolution
    halpha hbeta hkpos
  calc
    (∑ p ∈ S with p.1 * p.2 = k,
        phase k * (alpha p.1 * beta p.2) /
          (Real.sqrt (k : ℝ) : ℂ) * mellinPhase k t) =
      ∑ p ∈ S with p.1 * p.2 = k,
        (phase k / (Real.sqrt (k : ℝ) : ℂ)) *
          (alpha p.1 * beta p.2) * mellinPhase k t := by
        apply Finset.sum_congr rfl
        intro p hp
        ring
    _ = (phase k / (Real.sqrt (k : ℝ) : ℂ) *
        (∑ p ∈ S with p.1 * p.2 = k, alpha p.1 * beta p.2)) *
          mellinPhase k t := by
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = characterTwist phase (literalDirichletConvolution alpha beta) k /
          (Real.sqrt (k : ℝ) : ℂ) * mellinPhase k t := by
      rw [hconv]
      unfold characterTwist
      ring

/-- The actual collected Type-d1 polynomial is exactly the product of its two
factor polynomials. -/
theorem halfLineDirichletPolynomial_convolution_eq_mul
    {N M : ℝ} (hN : 0 < N) (hM : 0 < M)
    {phase alpha beta : ℕ → ℂ}
    (hphase : ∀ m n, phase (m * n) = phase m * phase n)
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    (t : ℝ) :
    halfLineDirichletPolynomial (N * M) 4
        (characterTwist phase (literalDirichletConvolution alpha beta)) t =
      halfLineDirichletPolynomial N 2 (characterTwist phase alpha) t *
        halfLineDirichletPolynomial M 2 (characterTwist phase beta) t := by
  rw [halfLineDirichletPolynomial_eq_dyadicFactorPolynomial halpha,
    halfLineDirichletPolynomial_eq_dyadicFactorPolynomial hbeta]
  rw [← uncollectedTypeD1Polynomial_eq_mul_factors]
  exact (uncollectedTypeD1Polynomial_eq_convolutionPolynomial
    hN hM hphase halpha hbeta t).symm

/-- Norm form consumed by the Proposition 6.1 Cauchy layer. -/
theorem norm_halfLineDirichletPolynomial_convolution_eq_mul
    {N M : ℝ} (hN : 0 < N) (hM : 0 < M)
    {phase alpha beta : ℕ → ℂ}
    (hphase : ∀ m n, phase (m * n) = phase m * phase n)
    (halpha : SupportedDyadic N alpha)
    (hbeta : SupportedDyadic M beta)
    (t : ℝ) :
    ‖halfLineDirichletPolynomial (N * M) 4
        (characterTwist phase (literalDirichletConvolution alpha beta)) t‖ =
      ‖halfLineDirichletPolynomial N 2 (characterTwist phase alpha) t‖ *
        ‖halfLineDirichletPolynomial M 2 (characterTwist phase beta) t‖ := by
  rw [halfLineDirichletPolynomial_convolution_eq_mul
    hN hM hphase halpha hbeta, norm_mul]

end
end MAPMRTProposition61TypeD1Factorization

#print axioms MAPMRTProposition61TypeD1Factorization.productFiber_sum_eq_literalDirichletConvolution
#print axioms MAPMRTProposition61TypeD1Factorization.normalizedTwistedTerm_mul
#print axioms MAPMRTProposition61TypeD1Factorization.uncollectedTypeD1Polynomial_eq_convolutionPolynomial
#print axioms MAPMRTProposition61TypeD1Factorization.halfLineDirichletPolynomial_convolution_eq_mul
#print axioms MAPMRTProposition61TypeD1Factorization.norm_halfLineDirichletPolynomial_convolution_eq_mul
