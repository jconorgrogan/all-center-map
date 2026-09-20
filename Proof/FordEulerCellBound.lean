import Mathlib

open MeasureTheory Set Interval intervalIntegral
noncomputable section
namespace FordEulerCellBound

theorem norm_cpow_sub_le {a x : ℝ} {s : ℂ}
    (ha : 0 < a) (hs : 0 < s.re) (hx : x ∈ Icc a (a + 1)) :
    ‖(x : ℂ) ^ (-s) - (a : ℂ) ^ (-s)‖ ≤
      ‖s‖ * a ^ (-s.re - 1) := by
  have hs0 : -s ≠ 0 := neg_ne_zero.mpr (by intro h; simp [h] at hs)
  have hder : ∀ y ∈ Icc a (a + 1),
      HasDerivWithinAt (fun z : ℝ => (z : ℂ) ^ (-s))
        ((-s) * (y : ℂ) ^ (-s - 1)) (Icc a (a + 1)) y := by
    intro y hy
    exact (hasDerivAt_ofReal_cpow_const (by linarith [hy.1]) hs0).hasDerivWithinAt
  have hb : ∀ y ∈ Ico a (a + 1),
      ‖(-s) * (y : ℂ) ^ (-s - 1)‖ ≤ ‖s‖ * a ^ (-s.re - 1) := by
    intro y hy
    have hy0 : 0 < y := lt_of_lt_of_le ha hy.1
    rw [norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy0]
    simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hy.1 (by linarith)) (norm_nonneg s)
  have h := norm_image_sub_le_of_norm_deriv_le_segment' hder hb x hx
  have hC : 0 ≤ ‖s‖ * a ^ (-s.re - 1) := by positivity
  exact h.trans (by nlinarith [hx.2])

theorem norm_cell_le {a : ℝ} {s : ℂ}
    (ha : 0 < a) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    ‖(a : ℂ) ^ (-s) -
      (((a + 1 : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s)‖ ≤
      ‖s‖ * a ^ (-s.re - 1) := by
  have hab : a ≤ a + 1 := by linarith
  have hz : (0 : ℝ) ∉ [[a, a + 1]] := by
    rw [uIcc_of_le hab]
    intro h
    linarith [h.1]
  have hi : IntervalIntegrable (fun x : ℝ => (x : ℂ) ^ (-s)) volume a (a + 1) :=
    intervalIntegrable_cpow (Or.inr hz)
  have hc : IntervalIntegrable (fun _ : ℝ => (a : ℂ) ^ (-s)) volume a (a + 1) :=
    continuous_const.intervalIntegrable a (a + 1)
  have hformula := integral_cpow (a := a) (b := a + 1) (r := -s)
    (Or.inr ⟨by intro h; apply hs1; linear_combination -h, hz⟩)
  have hid : (∫ x in a..a + 1, ((a : ℂ) ^ (-s) - (x : ℂ) ^ (-s))) =
      (a : ℂ) ^ (-s) -
      (((a + 1 : ℝ) : ℂ) ^ (1 - s) - (a : ℂ) ^ (1 - s)) / (1 - s) := by
    rw [intervalIntegral.integral_sub hc hi, hformula]
    simp [intervalIntegral.integral_const, sub_eq_add_neg, add_comm]
  rw [← hid]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := a + 1) (C := ‖s‖ * a ^ (-s.re - 1))
    (f := fun x : ℝ => (a : ℂ) ^ (-s) - (x : ℂ) ^ (-s)) (by
      intro x hx
      rw [uIoc_of_le hab] at hx
      rw [norm_sub_rev]
      exact norm_cpow_sub_le ha hs ⟨hx.1.le, hx.2⟩)
  simpa using hb

end FordEulerCellBound
#print axioms FordEulerCellBound.norm_cpow_sub_le
#print axioms FordEulerCellBound.norm_cell_le
