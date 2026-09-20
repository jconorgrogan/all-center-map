import GuthMaynardDiscreteInverseVariation
namespace GuthMaynardDiscreteHalfAngle
open GuthMaynardDiscreteFirstDerivative

theorem inverseCoeff_halfAngle {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    inverseCoeff d = ((-1 / 2 : ℝ) : ℂ) -
      ((Real.cot (d / 2) / 2 : ℝ) : ℂ) * Complex.I := by
  have hden := exp_mul_I_sub_one_ne_zero_of_unit_interval hd0 hd1
  have hs : Real.sin (d / 2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [Real.pi_gt_three]))
  have hsin : Real.sin d = 2 * Real.sin (d / 2) * Real.cos (d / 2) := by
    convert Real.sin_two_mul (d / 2) using 1 <;> congr 1 <;> ring
  have hcos : Real.cos d = 2 * Real.cos (d / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (d / 2) using 1 <;> congr 1 <;> ring
  have hunit := Real.sin_sq_add_cos_sq (d / 2)
  have hunitC := congrArg (fun x : ℝ => x * Real.cos (d / 2)) hunit
  rw [inverseCoeff, div_eq_iff hden]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.exp_re, Complex.exp_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, sub_zero,
      Real.exp_zero] <;>
    rw [Real.cot_eq_cos_div_sin, hsin, hcos] <;>
    field_simp [hs] <;> nlinarith [hunit, hunitC]
end GuthMaynardDiscreteHalfAngle
#print axioms GuthMaynardDiscreteHalfAngle.inverseCoeff_halfAngle
