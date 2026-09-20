import HuxleyProductEnergy

/-!
# Algebra of Huxley's reflection kernel

This module certifies the rational partial fraction identity in Huxley 1973
(2.4) and the cancellation of its three apparent poles after multiplication
by the exponential numerator in (2.6).  Mellin inversion (2.5), removable
holomorphy, and the contour estimates remain analytic work.
-/

namespace MAPHuxleyReflectionKernelAlgebra

noncomputable section

/-- Huxley's rational kernel `J` from equation (2.4). -/
def huxleyJ (w : ℂ) : ℂ :=
  (Real.pi : ℂ) ^ 2 /
    (2 * w * (w - (Real.pi : ℂ) * Complex.I) *
      (w + (Real.pi : ℂ) * Complex.I))

/-- The partial fractions printed in Huxley (2.4). -/
def huxleyJPartialFractions (w : ℂ) : ℂ :=
  1 / (2 * w) -
    1 / (4 * (w + (Real.pi : ℂ) * Complex.I)) -
    1 / (4 * (w - (Real.pi : ℂ) * Complex.I))

theorem huxleyJ_eq_partialFractions
    {w : ℂ}
    (hw0 : w ≠ 0)
    (hwPlus : w + (Real.pi : ℂ) * Complex.I ≠ 0)
    (hwMinus : w - (Real.pi : ℂ) * Complex.I ≠ 0) :
    huxleyJ w = huxleyJPartialFractions w := by
  unfold huxleyJ huxleyJPartialFractions
  field_simp [hw0, hwPlus, hwMinus, Real.pi_ne_zero]
  ring_nf
  simp [Complex.I_sq]

/-- Exponential numerator multiplying `J` in Huxley (2.6). -/
def huxleyKernelNumerator (w : ℂ) : ℂ :=
  Complex.exp (4 * w) + Complex.exp (3 * w) - Complex.exp w - 1

/-- Huxley's full kernel away from the three removable points. -/
def huxleyK (w : ℂ) : ℂ := huxleyKernelNumerator w * huxleyJ w

/-- The exponential numerator vanishes whenever `exp w=-1`. -/
theorem huxleyKernelNumerator_eq_zero_of_exp_eq_neg_one
    {w : ℂ} (hw : Complex.exp w = -1) :
    huxleyKernelNumerator w = 0 := by
  unfold huxleyKernelNumerator
  rw [show (4 : ℂ) * w = (4 : ℕ) * w by norm_num,
    Complex.exp_nat_mul,
    show (3 : ℂ) * w = (3 : ℕ) * w by norm_num,
    Complex.exp_nat_mul, hw]
  norm_num

theorem huxleyKernelNumerator_zero :
    huxleyKernelNumerator 0 = 0 := by
  simp [huxleyKernelNumerator]

theorem huxleyKernelNumerator_pi_mul_I :
    huxleyKernelNumerator ((Real.pi : ℂ) * Complex.I) = 0 := by
  apply huxleyKernelNumerator_eq_zero_of_exp_eq_neg_one
  exact Complex.exp_pi_mul_I

theorem huxleyKernelNumerator_neg_pi_mul_I :
    huxleyKernelNumerator (-((Real.pi : ℂ) * Complex.I)) = 0 := by
  apply huxleyKernelNumerator_eq_zero_of_exp_eq_neg_one
  rw [Complex.exp_neg, Complex.exp_pi_mul_I]
  norm_num

end


end MAPHuxleyReflectionKernelAlgebra

#print axioms MAPHuxleyReflectionKernelAlgebra.huxleyJ_eq_partialFractions
#print axioms MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator_zero
#print axioms MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator_pi_mul_I
#print axioms MAPHuxleyReflectionKernelAlgebra.huxleyKernelNumerator_neg_pi_mul_I
