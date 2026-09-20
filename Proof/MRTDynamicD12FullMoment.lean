import MRTDynamicD12PolynomialFactorization
import MRTDynamicD12ShortPrefixUniform
import MRTDynamicD12LiteralMass
import MRTProposition61TypeD1FirstInequality

/-! # Exact unmasked d1/d2 polynomials at the continuum moment interface -/
namespace MRTDynamicD12FullMoment

open scoped ArithmeticFunction BigOperators
open ArithmeticFunction MeasureTheory
open MAPMRTProposition61TypeD1Factorization
open MAPMRTProposition61TypeD1FirstInequality
open MRTLemma215DynamicSupportV3
open MRTDynamicD12PolynomialFactorization

noncomputable section

/-- Exact normalized d1 product. -/
theorem norm_prefix_tail_one {q : ℕ} (c : ℂ)
    (factors : List NatDyadicFactor) (hone : ∀ f ∈ factors, 1 ≤ f.length)
    (s : ℕ) (beta : NatDyadicFactor) (htail : factors.drop s = [beta])
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖prefixPolynomial q (factorUpperProduct factors) (c • factorConvolution factors) chi t‖ =
      ‖prefixPolynomial q (factorUpperProduct (factors.take s))
        (c • factorConvolution (factors.take s)) chi t‖ *
      ‖dyadicFactorPolynomial (beta.length : ℝ) (fun n => chi n) beta.coeff t‖ := by
  rw [prefixPolynomial_scalar_prefix_tail c factors hone s, htail]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [norm_mul, prefixPolynomial_eq_dyadicFactorPolynomial beta.coeff beta.support]

/-- Exact normalized d2 product. The scalar remains entirely in the short
prefix and both literal smooth factors remain separately visible. -/
theorem norm_prefix_tail_two {q : ℕ} (c : ℂ)
    (factors : List NatDyadicFactor) (hone : ∀ f ∈ factors, 1 ≤ f.length)
    (s : ℕ) (beta gamma : NatDyadicFactor) (htail : factors.drop s = [beta,gamma])
    (chi : DirichletCharacter ℂ q) (t : ℝ) :
    ‖prefixPolynomial q (factorUpperProduct factors) (c • factorConvolution factors) chi t‖ =
      ‖prefixPolynomial q (factorUpperProduct (factors.take s))
        (c • factorConvolution (factors.take s)) chi t‖ *
      ‖dyadicFactorPolynomial (beta.length : ℝ) (fun n => chi n) beta.coeff t‖ *
      ‖dyadicFactorPolynomial (gamma.length : ℝ) (fun n => chi n) gamma.coeff t‖ := by
  rw [prefixPolynomial_scalar_prefix_tail c factors hone s, htail]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [norm_mul, norm_mul,
    prefixPolynomial_eq_dyadicFactorPolynomial beta.coeff beta.support,
    prefixPolynomial_eq_dyadicFactorPolynomial gamma.coeff gamma.support]
  ring

end
end MRTDynamicD12FullMoment

#print axioms MRTDynamicD12FullMoment.norm_prefix_tail_one
#print axioms MRTDynamicD12FullMoment.norm_prefix_tail_two
