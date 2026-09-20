import KhaleAppendixB1FirstPartReduction
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# The tiny cotangent inequality in Khale Appendix B.1
-/

namespace MAPKhaleAppendixBCotangentCertified

noncomputable section

private theorem sin_le_fifth_envelope
    {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.sin x ≤ x - x ^ 3 / 6 + x ^ 4 * (5 / 96) := by
  have habs : |x| = x := abs_of_nonneg hx0
  have habound : |x| ≤ 1 := by rw [habs]; exact hx1
  have h := le_of_abs_le (Real.sin_bound habound)
  rw [habs] at h
  linarith

private theorem polynomial_margin
    {x : ℝ} (hx0 : 0 ≤ x) (hxTop : x ≤ 0.0188496) :
    (0.99988 : ℝ) * (x - x ^ 3 / 6 + x ^ 4 * (5 / 96)) ≤
      x * (1 - x ^ 2 / 2) := by
  have hx2 : x ^ 2 ≤ (0.0188496 : ℝ) ^ 2 :=
    pow_le_pow_left₀ hx0 hxTop 2
  have hx3 : x ^ 3 ≤ (0.0188496 : ℝ) ^ 3 :=
    pow_le_pow_left₀ hx0 hxTop 3
  have hnum :
      (0.99988 : ℝ) *
          (1 - (0.0188496 : ℝ) ^ 2 / 6 +
            (0.0188496 : ℝ) ^ 3 * (5 / 96)) ≤
        1 - (0.0188496 : ℝ) ^ 2 / 2 := by norm_num
  have hbracket :
      (0.99988 : ℝ) * (1 - x ^ 2 / 6 + x ^ 3 * (5 / 96)) ≤
        1 - x ^ 2 / 2 := by
    nlinarith
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hbracket)]

/-- Premise-free inhabitant of the normalized `0.99988` cotangent leaf. -/
theorem appendixBCotangent0012 :
    MAPKhaleAppendixB1FirstPartReduction.AppendixBCotangent0012 := by
  intro y hy hyTop
  let x : ℝ := (Real.pi / 2) * y
  have hx : 0 < x := mul_pos Real.pi_div_two_pos hy
  have hxTop : x ≤ 0.0188496 := by
    dsimp [x]
    have hp := Real.pi_lt_d4.le
    nlinarith
  have hxOne : x ≤ 1 := hxTop.trans (by norm_num)
  have hsinUpper := sin_le_fifth_envelope hx.le hxOne
  have hcosLower := Real.one_sub_sq_div_two_le_cos (x := x)
  have hpoly := polynomial_margin hx.le hxTop
  have hsinCos : (0.99988 : ℝ) * Real.sin x ≤ x * Real.cos x := by
    have hmulSin := mul_le_mul_of_nonneg_left hsinUpper (by norm_num : (0 : ℝ) ≤ 0.99988)
    have hmulCos := mul_le_mul_of_nonneg_left hcosLower hx.le
    exact hmulSin.trans (hpoly.trans hmulCos)
  have hxPi : x < Real.pi := by
    dsimp [x]
    have hpi := Real.pi_pos
    nlinarith
  have hsinPos : 0 < Real.sin x := Real.sin_pos_of_pos_of_lt_pi hx hxPi
  have hxcot : (0.99988 : ℝ) ≤ x * Real.cot x := by
    rw [Real.cot_eq_cos_div_sin]
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hsinPos).2
    nlinarith
  apply (div_le_iff₀ hy).2
  dsimp [x] at hxcot ⊢
  nlinarith

end
end MAPKhaleAppendixBCotangentCertified

#print axioms MAPKhaleAppendixBCotangentCertified.appendixBCotangent0012
