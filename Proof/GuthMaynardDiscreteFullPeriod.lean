import GuthMaynardDiscreteInverseVariation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
namespace GuthMaynardDiscreteFullPeriod
open GuthMaynardDiscreteFirstDerivative

theorem inverseCoeff_halfAngle {d : ℝ} (hd0 : 0 < d) (hd1 : d < 2 * Real.pi) :
    inverseCoeff d = ((-1 / 2 : ℝ) : ℂ) -
      ((Real.cot (d / 2) / 2 : ℝ) : ℂ) * Complex.I := by
  have hs : Real.sin (d / 2) ≠ 0 := ne_of_gt
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by nlinarith [Real.pi_gt_three]))
  have hsin : Real.sin d = 2 * Real.sin (d / 2) * Real.cos (d / 2) := by
    convert Real.sin_two_mul (d / 2) using 1 <;> congr 1 <;> ring
  have hcos : Real.cos d = 2 * Real.cos (d / 2) ^ 2 - 1 := by
    convert Real.cos_two_mul (d / 2) using 1 <;> congr 1 <;> ring
  have hunit := Real.sin_sq_add_cos_sq (d / 2)
  have hunitC := congrArg (fun x : ℝ => x * Real.cos (d / 2)) hunit
  have hden : Complex.exp (Complex.I * (d : ℂ)) - 1 ≠ 0 := by
    intro heq
    have hre := congrArg Complex.re heq
    simp [Complex.exp_re] at hre
    rw [hcos] at hre
    have hs2 : Real.sin (d / 2) ^ 2 = 0 := by nlinarith [hunit]
    exact hs (sq_eq_zero_iff.mp hs2)
  rw [inverseCoeff, div_eq_iff hden]
  apply Complex.ext <;>
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
      Complex.exp_re, Complex.exp_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
      zero_mul, mul_zero, one_mul, mul_one, add_zero, zero_add, sub_zero,
      Real.exp_zero] <;>
    rw [Real.cot_eq_cos_div_sin, hsin, hcos] <;>
    field_simp [hs] <;> nlinarith [hunit, hunitC]
theorem cot_half_le_pi_div {d : ℝ} (hd0 : 0 < d) (hdpi : d ≤ Real.pi) :
    Real.cot (d / 2) ≤ Real.pi / d := by
  have hs : 0 < Real.sin (d / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
  have hsin := Real.mul_le_sin (x := d / 2) (by linarith) (by linarith)
  have hs' : d ≤ Real.pi * Real.sin (d / 2) := by
    have hh := (div_le_iff₀ Real.pi_pos).mp
      (show d / Real.pi ≤ Real.sin (d / 2) by convert hsin using 1 <;> ring)
    nlinarith
  rw [Real.cot_eq_cos_div_sin]
  apply (div_le_div_iff₀ hs hd0).2
  have hc := mul_le_mul_of_nonneg_right (Real.cos_le_one (d / 2)) hd0.le
  nlinarith

theorem cot_half_reflect (d : ℝ) :
    Real.cot ((2 * Real.pi - d) / 2) = -Real.cot (d / 2) := by
  rw [show (2 * Real.pi - d) / 2 = Real.pi - d / 2 by ring]
  simp [Real.cot_eq_cos_div_sin, Real.cos_pi_sub, Real.sin_pi_sub, neg_div]

theorem cot_antitone_on_pi : AntitoneOn Real.cot (Set.Ioo (0 : ℝ) Real.pi) := by
  intro x hx y hy hxy
  rw [Real.cot_eq_cos_div_sin, Real.cot_eq_cos_div_sin]
  have hsx := Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2
  have hsy := Real.sin_pos_of_pos_of_lt_pi hy.1 hy.2
  apply (div_le_div_iff₀ hsy hsx).2
  have hs := Real.sin_nonneg_of_nonneg_of_le_pi
    (sub_nonneg.mpr hxy) (by linarith [hx.1, hy.2] : y - x ≤ Real.pi)
  rw [Real.sin_sub] at hs
  linarith

theorem cot_half_le_pi_div_full {d : ℝ} (hd0 : 0 < d)
    (hd2 : d < 2 * Real.pi) : Real.cot (d / 2) ≤ Real.pi / d := by
  by_cases hsmall : d ≤ Real.pi
  · exact cot_half_le_pi_div hd0 hsmall
  · have hanti := cot_antitone_on_pi
      (show Real.pi / 2 ∈ Set.Ioo (0 : ℝ) Real.pi by constructor <;> linarith [Real.pi_pos])
      (show d / 2 ∈ Set.Ioo (0 : ℝ) Real.pi by constructor <;> linarith)
      (show Real.pi / 2 ≤ d / 2 by linarith)
    have hcot0 : Real.cot (Real.pi / 2) = 0 := by
      simp [Real.cot_eq_cos_div_sin]
    rw [hcot0] at hanti
    exact hanti.trans (div_pos Real.pi_pos hd0).le

theorem abs_cot_half_le_pi_div_margin {d δ : ℝ} (hδ : 0 < δ)
    (hdlo : δ ≤ d) (hdhi : d ≤ 2 * Real.pi - δ) :
    |Real.cot (d / 2)| ≤ Real.pi / δ := by
  have hd0 : 0 < d := lt_of_lt_of_le hδ hdlo
  have hd2 : d < 2 * Real.pi := by linarith
  have hupper := cot_half_le_pi_div_full hd0 hd2
  have hother := cot_half_le_pi_div_full
    (show 0 < 2 * Real.pi - d by linarith)
    (show 2 * Real.pi - d < 2 * Real.pi by linarith)
  rw [cot_half_reflect] at hother
  have hu : Real.pi / d ≤ Real.pi / δ := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le hδ hdlo
  have hl : Real.pi / (2 * Real.pi - d) ≤ Real.pi / δ := by
    exact div_le_div_of_nonneg_left Real.pi_pos.le hδ (by linarith)
  exact abs_le.mpr ⟨by linarith, hupper.trans hu⟩

theorem exp_sub_one_ne_zero {d : ℝ} (hd0 : 0 < d) (hd2 : d < 2 * Real.pi) :
    Complex.exp (Complex.I * (d : ℂ)) - 1 ≠ 0 := by
  intro hz
  have hi := inverseCoeff_halfAngle hd0 hd2
  rw [inverseCoeff, hz] at hi
  have hre := congrArg Complex.re hi
  simp only [div_zero, Complex.zero_re, Complex.sub_re, Complex.ofReal_re,
    Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im] at hre
  norm_num at hre

theorem inverseCoeff_norm_le_pi_div_margin {d δ : ℝ} (hδ : 0 < δ)
    (hdlo : δ ≤ d) (hdhi : d ≤ 2 * Real.pi - δ) :
    ‖inverseCoeff d‖ ≤ Real.pi / δ := by
  have hd0 : 0 < d := lt_of_lt_of_le hδ hdlo
  have hd2 : d < 2 * Real.pi := by linarith
  have habs := abs_cot_half_le_pi_div_margin hδ hdlo hdhi
  have hratio : 1 ≤ Real.pi / δ := by
    apply (le_div_iff₀ hδ).2
    linarith
  rw [inverseCoeff_halfAngle hd0 hd2]
  have hb := norm_sub_le (((-1 / 2 : ℝ) : ℂ))
    (((Real.cot (d / 2) / 2 : ℝ) : ℂ) * Complex.I)
  have hn1 : ‖((-1 / 2 : ℝ) : ℂ)‖ = (1 / 2 : ℝ) := by
    norm_num [Complex.norm_real, Real.norm_eq_abs]
  have hn2 : ‖((Real.cot (d / 2) / 2 : ℝ) : ℂ) * Complex.I‖ =
      |Real.cot (d / 2)| / 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, Complex.norm_I]
    norm_num
  rw [hn1, hn2] at hb
  linarith

end GuthMaynardDiscreteFullPeriod
#print axioms GuthMaynardDiscreteFullPeriod.inverseCoeff_halfAngle
#print axioms GuthMaynardDiscreteFullPeriod.cot_half_le_pi_div
#print axioms GuthMaynardDiscreteFullPeriod.cot_half_reflect
#print axioms GuthMaynardDiscreteFullPeriod.abs_cot_half_le_pi_div_margin
#print axioms GuthMaynardDiscreteFullPeriod.exp_sub_one_ne_zero
#print axioms GuthMaynardDiscreteFullPeriod.inverseCoeff_norm_le_pi_div_margin
