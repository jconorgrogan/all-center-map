import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Khale Appendix B trigonometric polynomial

Khale's equation (5.1) is algebraic.  The Appendix-B specialization is
`a₁ = 0.225`, `a₂ = 0.9`; the source line saying `a₀ = 9` is a typographical
error, as the printed coefficients uniquely match `a₂ = 0.9`.
-/

namespace MAPKhaleAppendixBTrigPolynomialCertified

/-- Exact Appendix-B coefficient values obtained from (5.2). -/
theorem coefficient_values :
    let a₁ : ℝ := 0.225
    let a₂ : ℝ := 0.9
    let b₄ : ℝ := 1
    let b₃ : ℝ := 4 * (a₁ + a₂)
    let b₂ : ℝ := 4 * (1 + a₁ ^ 2 + a₂ ^ 2 + 4 * a₁ * a₂)
    let b₁ : ℝ := (a₁ + a₂) * (12 + 16 * a₁ * a₂)
    let b₀ : ℝ := b₂ - 1 + 8 * (a₁ * a₂) ^ 2
    let b₅ : ℝ := b₁ + b₂ + b₃ + b₄
    b₀ = 10.01055 ∧ b₁ = 17.145 ∧ b₂ = 10.6825 ∧
      b₃ = 4.5 ∧ b₄ = 1 ∧ b₅ = 33.3275 := by
  norm_num

/-- Equation (5.1), specialized to the values actually used in Appendix B. -/
theorem appendixB_trigonometric_identity (theta : ℝ) :
    10.01055 + 17.145 * Real.cos theta +
        10.6825 * Real.cos (2 * theta) +
        4.5 * Real.cos (3 * theta) +
        Real.cos (4 * theta) =
      8 * (0.225 + Real.cos theta) ^ 2 *
        (0.9 + Real.cos theta) ^ 2 := by
  have hunit := Real.sin_sq_add_cos_sq theta
  have hcos2 : Real.cos (2 * theta) = 2 * Real.cos theta ^ 2 - 1 := by
    rw [Real.cos_two_mul]
  have hcos3 : Real.cos (3 * theta) =
      4 * Real.cos theta ^ 3 - 3 * Real.cos theta := by
    rw [show (3 : ℝ) * theta = 2 * theta + theta by ring,
      Real.cos_add, Real.sin_two_mul, hcos2]
    have hunitmul := congrArg (fun x : ℝ => x * Real.cos theta) hunit
    ring_nf at hunitmul
    ring_nf
    linarith
  have hcos4 : Real.cos (4 * theta) =
      8 * Real.cos theta ^ 4 - 8 * Real.cos theta ^ 2 + 1 := by
    rw [show (4 : ℝ) * theta = 2 * (2 * theta) by ring,
      Real.cos_two_mul, hcos2]
    ring
  rw [hcos2, hcos3, hcos4]
  ring

/-- The specialized trigonometric polynomial is nonnegative for every real
angle. -/
theorem appendixB_trigonometric_nonneg (theta : ℝ) :
    0 ≤ 10.01055 + 17.145 * Real.cos theta +
        10.6825 * Real.cos (2 * theta) +
        4.5 * Real.cos (3 * theta) +
        Real.cos (4 * theta) := by
  rw [appendixB_trigonometric_identity]
  positivity

/-- Uniform correction bound for the parity term in Khale Lemma 4.1.

The published Appendix-B proof writes `(b₂+b₄)e⁻¹⁹³⁷`.  That is valid when
the starting character is odd, but an even primitive character can also make
the `j=1,3` corrections nonzero.  Bounding each parity/principality indicator
by one gives the uniform coefficient `b₅=33.3275`.  This tiny correction is
the one used by the certified downstream chain. -/
theorem parity_correction_coefficient_le
    {e₁ e₂ e₃ e₄ : ℝ}
    (he₁0 : 0 ≤ e₁) (he₁1 : e₁ ≤ 1)
    (he₂0 : 0 ≤ e₂) (he₂1 : e₂ ≤ 1)
    (he₃0 : 0 ≤ e₃) (he₃1 : e₃ ≤ 1)
    (he₄0 : 0 ≤ e₄) (he₄1 : e₄ ≤ 1) :
    0 ≤ 17.145 * e₁ + 10.6825 * e₂ + 4.5 * e₃ + e₄ ∧
    17.145 * e₁ + 10.6825 * e₂ + 4.5 * e₃ + e₄ ≤ 33.3275 := by
  constructor <;> nlinarith

end MAPKhaleAppendixBTrigPolynomialCertified

#print axioms MAPKhaleAppendixBTrigPolynomialCertified.coefficient_values
#print axioms MAPKhaleAppendixBTrigPolynomialCertified.appendixB_trigonometric_nonneg
#print axioms MAPKhaleAppendixBTrigPolynomialCertified.parity_correction_coefficient_le
