import HuxleyEntireKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Vertical integrability of Huxley's Mellin kernel

This is the convergence input for Huxley 1973 (2.5).  It is proved directly
from the three linear factors in (2.4), with a deliberately coarse global
`(1+t^2)^{-1}` majorant on the source line `Re w = 2`.
-/

namespace MAPHuxleyJVertical

open Complex Real Set MeasureTheory

noncomputable section

private def verticalPoint (t : ℝ) : ℂ := (2 : ℂ) + (t : ℂ) * I

private theorem norm_verticalPoint_ge_two (t : ℝ) :
    2 ≤ ‖verticalPoint t‖ := by
  have h := Complex.abs_re_le_norm (verticalPoint t)
  simpa [verticalPoint] using h

private theorem norm_verticalPoint_sub_ge_two (t a : ℝ) :
    2 ≤ ‖verticalPoint t - (a : ℂ) * I‖ := by
  have h := Complex.abs_re_le_norm (verticalPoint t - (a : ℂ) * I)
  simpa [verticalPoint] using h

private theorem abs_t_le_norm_verticalPoint (t : ℝ) :
    |t| ≤ ‖verticalPoint t‖ := by
  have h := Complex.abs_im_le_norm (verticalPoint t)
  simpa [verticalPoint] using h

private theorem abs_t_sub_le_norm_verticalPoint_sub (t a : ℝ) :
    |t - a| ≤ ‖verticalPoint t - (a : ℂ) * I‖ := by
  have h := Complex.abs_im_le_norm (verticalPoint t - (a : ℂ) * I)
  simpa [verticalPoint] using h

private theorem abs_t_add_le_norm_verticalPoint_add (t a : ℝ) :
    |t + a| ≤ ‖verticalPoint t + (a : ℂ) * I‖ := by
  have h := Complex.abs_im_le_norm (verticalPoint t + (a : ℂ) * I)
  simpa [verticalPoint] using h

private theorem norm_huxleyJ_le_pi_sq_div_sixteen (t : ℝ) :
    ‖MAPHuxleyReflectionKernelAlgebra.huxleyJ (verticalPoint t)‖ ≤
      Real.pi ^ 2 / 16 := by
  have h0 := norm_verticalPoint_ge_two t
  have hm := norm_verticalPoint_sub_ge_two t Real.pi
  have hp : 2 ≤ ‖verticalPoint t + (Real.pi : ℂ) * I‖ := by
    have h := norm_verticalPoint_sub_ge_two t (-Real.pi)
    simpa [sub_neg_eq_add] using h
  have hden : 16 ≤
      ‖(2 : ℂ) * verticalPoint t *
        (verticalPoint t - (Real.pi : ℂ) * I) *
        (verticalPoint t + (Real.pi : ℂ) * I)‖ := by
    simp only [norm_mul, Complex.norm_ofNat]
    calc
      16 = 2 * 2 * 2 * 2 := by norm_num
      _ ≤ 2 * ‖verticalPoint t‖ *
          ‖verticalPoint t - (Real.pi : ℂ) * I‖ *
          ‖verticalPoint t + (Real.pi : ℂ) * I‖ := by gcongr
  unfold MAPHuxleyReflectionKernelAlgebra.huxleyJ
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  exact div_le_div₀ (sq_nonneg Real.pi) le_rfl (by norm_num) hden

private theorem half_abs_le_abs_sub_pi
    {t : ℝ} (ht : 2 * Real.pi ≤ |t|) :
    |t| / 2 ≤ |t - Real.pi| := by
  have htri : |t| ≤ |t - Real.pi| + Real.pi := by
    calc
      |t| = |(t - Real.pi) + Real.pi| := by ring_nf
      _ ≤ |t - Real.pi| + |Real.pi| := abs_add_le _ _
      _ = |t - Real.pi| + Real.pi := by rw [abs_of_pos Real.pi_pos]
  linarith

private theorem half_abs_le_abs_add_pi
    {t : ℝ} (ht : 2 * Real.pi ≤ |t|) :
    |t| / 2 ≤ |t + Real.pi| := by
  have htri : |t| ≤ |t + Real.pi| + Real.pi := by
    calc
      |t| = |(t + Real.pi) + (-Real.pi)| := by ring_nf
      _ ≤ |t + Real.pi| + |-Real.pi| := abs_add_le _ _
      _ = |t + Real.pi| + Real.pi := by rw [abs_neg, abs_of_pos Real.pi_pos]
  linarith

private theorem norm_huxleyJ_le_two_pi_sq_div_abs_cube
    {t : ℝ} (ht : 2 * Real.pi ≤ |t|) :
    ‖MAPHuxleyReflectionKernelAlgebra.huxleyJ (verticalPoint t)‖ ≤
      2 * Real.pi ^ 2 / |t| ^ 3 := by
  have htpos : 0 < |t| := lt_of_lt_of_le (by positivity : 0 < 2 * Real.pi) ht
  have h0 := abs_t_le_norm_verticalPoint t
  have hm0 := abs_t_sub_le_norm_verticalPoint_sub t Real.pi
  have hp0 := abs_t_add_le_norm_verticalPoint_add t Real.pi
  have hm : |t| / 2 ≤
      ‖verticalPoint t - (Real.pi : ℂ) * I‖ :=
    (half_abs_le_abs_sub_pi ht).trans hm0
  have hp : |t| / 2 ≤
      ‖verticalPoint t + (Real.pi : ℂ) * I‖ :=
    (half_abs_le_abs_add_pi ht).trans hp0
  have hden : |t| ^ 3 / 2 ≤
      ‖(2 : ℂ) * verticalPoint t *
        (verticalPoint t - (Real.pi : ℂ) * I) *
        (verticalPoint t + (Real.pi : ℂ) * I)‖ := by
    simp only [norm_mul, Complex.norm_ofNat]
    calc
      |t| ^ 3 / 2 = 2 * |t| * (|t| / 2) * (|t| / 2) := by ring
      _ ≤ 2 * ‖verticalPoint t‖ *
          ‖verticalPoint t - (Real.pi : ℂ) * I‖ *
          ‖verticalPoint t + (Real.pi : ℂ) * I‖ := by gcongr
  unfold MAPHuxleyReflectionKernelAlgebra.huxleyJ
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hdenpos : 0 <
      ‖(2 : ℂ) * verticalPoint t *
        (verticalPoint t - (Real.pi : ℂ) * I) *
        (verticalPoint t + (Real.pi : ℂ) * I)‖ :=
    lt_of_lt_of_le (by positivity : 0 < |t| ^ 3 / 2) hden
  apply (div_le_div_iff₀ hdenpos
      (by positivity : 0 < |t| ^ 3)).2
  nlinarith [sq_nonneg Real.pi]

/-- Coarse global `L^1` majorant for Huxley's `J` on the exact source line
`Re w = 2`. -/
theorem norm_huxleyJ_vertical_le (t : ℝ) :
    ‖MAPHuxleyReflectionKernelAlgebra.huxleyJ (verticalPoint t)‖ ≤
      (2 * Real.pi ^ 2 * (1 + 4 * Real.pi ^ 2)) * (1 + t ^ 2)⁻¹ := by
  by_cases ht : |t| ≤ 2 * Real.pi
  · have hj := norm_huxleyJ_le_pi_sq_div_sixteen t
    rw [inv_eq_one_div, mul_one_div]
    apply hj.trans
    apply (le_div_iff₀ (by positivity : 0 < 1 + t ^ 2)).2
    have ht2 := pow_le_pow_left₀ (abs_nonneg t) ht 2
    rw [sq_abs] at ht2
    have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    nlinarith
  · have ht' : 2 * Real.pi < |t| := lt_of_not_ge ht
    have hj := norm_huxleyJ_le_two_pi_sq_div_abs_cube ht'.le
    rw [inv_eq_one_div, mul_one_div]
    apply hj.trans
    have habspos : 0 < |t| := lt_trans (by positivity : 0 < 2 * Real.pi) ht'
    apply (div_le_div_iff₀ (by positivity : 0 < |t| ^ 3)
      (by positivity : 0 < 1 + t ^ 2)).2
    have htone : 1 < |t| := by
      have : 1 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
      exact this.trans ht'
    have hpi : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    have hone_sq : 1 ≤ |t| ^ 2 := by nlinarith [sq_nonneg (|t| - 1)]
    have hsq_cube : |t| ^ 2 ≤ |t| ^ 3 := by
      nlinarith [mul_nonneg (sq_nonneg |t|) (sub_nonneg.mpr htone.le)]
    have hsum : 1 + t ^ 2 ≤ 2 * |t| ^ 3 := by
      rw [← sq_abs]
      linarith
    have hcoef : 2 ≤ 1 + 4 * Real.pi ^ 2 := by
      nlinarith [Real.pi_gt_three]
    have hscale : 1 + t ^ 2 ≤
        (1 + 4 * Real.pi ^ 2) * |t| ^ 3 := by
      exact hsum.trans (mul_le_mul_of_nonneg_right hcoef (pow_nonneg (abs_nonneg t) 3))
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left hscale
        (show 0 ≤ 2 * Real.pi ^ 2 by positivity)

/-- The vertical integral in Huxley (2.5) is absolutely convergent. -/
theorem verticalIntegrable_huxleyJ :
    Complex.VerticalIntegrable
      MAPHuxleyReflectionKernelAlgebra.huxleyJ 2 := by
  unfold Complex.VerticalIntegrable
  let C : ℝ := 2 * Real.pi ^ 2 * (1 + 4 * Real.pi ^ 2)
  have hdom : Integrable (fun t : ℝ => C * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul C
  apply hdom.mono'
  · apply Continuous.aestronglyMeasurable
    unfold MAPHuxleyReflectionKernelAlgebra.huxleyJ
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    apply mul_ne_zero
    · apply mul_ne_zero
      · exact mul_ne_zero (by norm_num) (Complex.ne_zero_of_re_pos (by simp [verticalPoint]))
      · exact Complex.ne_zero_of_re_pos (by simp [verticalPoint])
    · exact Complex.ne_zero_of_re_pos (by simp [verticalPoint])
  · exact Filter.Eventually.of_forall (fun t => by
      simpa [C, verticalPoint] using norm_huxleyJ_vertical_le t)

end

end MAPHuxleyJVertical

#print axioms MAPHuxleyJVertical.norm_huxleyJ_vertical_le
#print axioms MAPHuxleyJVertical.verticalIntegrable_huxleyJ
