import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! A uniform integrable envelope for a polynomial divided by two more powers. -/

namespace GuthMaynardLemma295PolynomialKernel

open MeasureTheory

noncomputable section

theorem polynomial_over_higher_power_le_inv_sq
    (d : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (1 + x) ^ d / (1 + x ^ (d + 4)) ≤
      (2 : ℝ) ^ (d + 1) / (1 + x ^ 2) := by
  have hden1 : 0 < 1 + x ^ (d + 4) := by positivity
  have hden2 : 0 < 1 + x ^ 2 := by positivity
  rw [div_le_div_iff₀ hden1 hden2]
  by_cases hx1 : x ≤ 1
  · have hbase : 1 + x ≤ 2 := by linarith
    have hp : (1 + x) ^ d ≤ (2 : ℝ) ^ d := by gcongr
    have hx2 : x ^ 2 ≤ 1 := by nlinarith
    have hright : (1 : ℝ) ≤ 1 + x ^ (d + 4) := by
      linarith [pow_nonneg hx (d + 4)]
    calc
      (1 + x) ^ d * (1 + x ^ 2) ≤ (2 : ℝ) ^ d * 2 := by
        exact mul_le_mul hp (by linarith) (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (d + 1) := by ring
      _ ≤ (2 : ℝ) ^ (d + 1) * (1 + x ^ (d + 4)) := by
        exact le_mul_of_one_le_right (pow_nonneg (by norm_num) _) hright
  · have hx1' : 1 ≤ x := le_of_not_ge hx1
    have hbase : 1 + x ≤ 2 * x := by linarith
    have hp : (1 + x) ^ d ≤ (2 * x) ^ d := by gcongr
    have hd : x ^ d ≤ x ^ (d + 4) := by
      exact pow_le_pow_right₀ hx1' (by omega)
    have hd2 : x ^ (d + 2) ≤ x ^ (d + 4) := by
      exact pow_le_pow_right₀ hx1' (by omega)
    calc
      (1 + x) ^ d * (1 + x ^ 2) ≤ (2 * x) ^ d * (1 + x ^ 2) := by
        gcongr
      _ = (2 : ℝ) ^ d * (x ^ d + x ^ (d + 2)) := by ring
      _ ≤ (2 : ℝ) ^ d * (2 * x ^ (d + 4)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [hd, hd2]
      _ ≤ (2 : ℝ) ^ d * (2 * (1 + x ^ (d + 4))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [pow_nonneg hx (d + 4)]
      _ = (2 : ℝ) ^ (d + 1) * (1 + x ^ (d + 4)) := by ring

theorem integrable_polynomial_kernel (d : ℕ) :
    Integrable (fun t : ℝ =>
      (1 + |t|) ^ d / (1 + |t| ^ (d + 4))) := by
  apply Integrable.mono' (integrable_inv_one_add_sq.const_mul ((2 : ℝ) ^ (d + 1)))
  · exact (((continuous_const.add continuous_abs).pow d).div
      ((continuous_const.add (continuous_abs.pow (d + 4))))
      (fun t => ne_of_gt (add_pos_of_pos_of_nonneg zero_lt_one
        (pow_nonneg (abs_nonneg t) (d + 4))))).aestronglyMeasurable
  · filter_upwards with t
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by positivity) (by positivity))]
    simpa [mul_div_assoc, div_eq_mul_inv] using
      polynomial_over_higher_power_le_inv_sq d (abs_nonneg t)

theorem integral_polynomial_kernel_le (d : ℕ) :
    (∫ t : ℝ, (1 + |t|) ^ d / (1 + |t| ^ (d + 4))) ≤
      (2 : ℝ) ^ (d + 1) * Real.pi := by
  calc
    (∫ t : ℝ, (1 + |t|) ^ d / (1 + |t| ^ (d + 4))) ≤
        ∫ t : ℝ, (2 : ℝ) ^ (d + 1) * (1 + t^2)⁻¹ := by
      apply integral_mono (integrable_polynomial_kernel d)
        (integrable_inv_one_add_sq.const_mul ((2 : ℝ)^(d+1)))
      intro t
      simpa [mul_div_assoc, div_eq_mul_inv] using
        polynomial_over_higher_power_le_inv_sq d (abs_nonneg t)
    _ = (2 : ℝ) ^ (d + 1) * Real.pi := by
      rw [integral_const_mul, integral_univ_inv_one_add_sq]

end
end GuthMaynardLemma295PolynomialKernel

#print axioms GuthMaynardLemma295PolynomialKernel.polynomial_over_higher_power_le_inv_sq
#print axioms GuthMaynardLemma295PolynomialKernel.integrable_polynomial_kernel
#print axioms GuthMaynardLemma295PolynomialKernel.integral_polynomial_kernel_le
