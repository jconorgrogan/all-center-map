import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-! Elementary absolute integrability of the `cosh^{-2}` kernel. -/

namespace MAPKhaleCoshSqKernelIntegrable

open MeasureTheory Set

noncomputable section

private theorem exp_neg_two_abs_integrable :
    Integrable (fun u : ℝ => Real.exp (-2 * |u|)) := by
  have hleft0 := integrableOn_exp_mul_Iic (a := (2 : ℝ)) (by norm_num) 0
  have hleft : IntegrableOn (fun u : ℝ => Real.exp (-2 * |u|)) (Iic 0) := by
    apply hleft0.congr_fun
    · intro u hu
      change Real.exp (2 * u) = Real.exp (-2 * |u|)
      rw [abs_of_nonpos hu]
      congr 1
      ring
    · exact measurableSet_Iic
  have hright0 := integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) 0
  have hright : IntegrableOn (fun u : ℝ => Real.exp (-2 * |u|)) (Ioi 0) := by
    apply hright0.congr_fun
    · intro u hu
      change Real.exp (-2 * u) = Real.exp (-2 * |u|)
      rw [abs_of_pos hu]
    · exact measurableSet_Ioi
  have hu := hleft.union hright
  rw [Iic_union_Ioi] at hu
  simpa using hu

private theorem exp_abs_half_le_cosh (u : ℝ) :
    Real.exp |u| / 2 ≤ Real.cosh u := by
  by_cases hu : 0 ≤ u
  · rw [abs_of_nonneg hu, Real.cosh_eq]
    nlinarith [Real.exp_pos (-u)]
  · have hu' : u < 0 := lt_of_not_ge hu
    rw [abs_of_neg hu']
    calc
      Real.exp (-u) / 2 ≤
          (Real.exp (-u) + Real.exp (-(-u))) / 2 := by
        gcongr
        nlinarith [Real.exp_pos (-(-u))]
      _ = Real.cosh (-u) := (Real.cosh_eq (-u)).symm
      _ = Real.cosh u := Real.cosh_neg u

/-- Uniform exponential majorant for the kernel. -/
theorem inv_cosh_sq_le_exp (u : ℝ) :
    1 / (Real.cosh u) ^ 2 ≤ 4 * Real.exp (-2 * |u|) := by
  have hcpos : 0 < Real.cosh u := Real.cosh_pos u
  have hhalf := exp_abs_half_le_cosh u
  have hsquare : (Real.exp |u|) ^ 2 / 4 ≤ (Real.cosh u) ^ 2 := by
    have hsq := (sq_le_sq₀ (by positivity) hcpos.le).2 hhalf
    nlinarith
  have hexp : Real.exp (-2 * |u|) * (Real.exp |u|) ^ 2 = 1 := by
    rw [pow_two, ← Real.exp_add, ← Real.exp_add]
    rw [show -2 * |u| + (|u| + |u|) = 0 by ring, Real.exp_zero]
  apply (div_le_iff₀ (sq_pos_of_pos hcpos)).2
  have hmul := mul_le_mul_of_nonneg_left hsquare
    (by positivity : 0 ≤ 4 * Real.exp (-2 * |u|))
  nlinarith [hmul, hexp]

/-- `cosh(u)^{-2}` is absolutely integrable on the real line. -/
theorem invCoshSq_integrable :
    Integrable (fun u : ℝ => 1 / (Real.cosh u) ^ 2) := by
  have hg := (exp_neg_two_abs_integrable.const_mul 4)
  apply hg.mono'
  · have hcont : Continuous (fun u : ℝ => 1 / (Real.cosh u) ^ 2) := by
      fun_prop (disch := aesop (add safe forward Real.cosh_pos))
    exact hcont.aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ 1 / (Real.cosh u) ^ 2)]
    simpa only [mul_comm] using inv_cosh_sq_le_exp u

/-- A bounded cosine factor preserves integrability of the `cosh^{-2}`
kernel. -/
theorem cos_mul_invCoshSq_integrable (y : ℝ) :
    Integrable (fun u : ℝ => Real.cos (y * u) / (Real.cosh u) ^ 2) := by
  apply invCoshSq_integrable.mono'
  · have hnum : Continuous (fun u : ℝ => Real.cos (y * u)) := by fun_prop
    have hden : Continuous (fun u : ℝ => (Real.cosh u) ^ 2) :=
      Real.continuous_cosh.pow 2
    exact (hnum.div hden (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_div]
    simp only [abs_of_nonneg (sq_nonneg (Real.cosh u))]
    have hc := Real.abs_cos_le_one (y * u)
    exact div_le_div_of_nonneg_right hc (sq_nonneg _)

/-- A bounded sine factor preserves integrability of the `cosh^{-2}`
kernel. -/
theorem sin_mul_invCoshSq_integrable (y : ℝ) :
    Integrable (fun u : ℝ => Real.sin (y * u) / (Real.cosh u) ^ 2) := by
  apply invCoshSq_integrable.mono'
  · have hnum : Continuous (fun u : ℝ => Real.sin (y * u)) := by fun_prop
    have hden : Continuous (fun u : ℝ => (Real.cosh u) ^ 2) :=
      Real.continuous_cosh.pow 2
    exact (hnum.div hden (fun u => pow_ne_zero 2 (Real.cosh_pos u).ne')).aestronglyMeasurable
  · filter_upwards with u
    rw [Real.norm_eq_abs, abs_div]
    simp only [abs_of_nonneg (sq_nonneg (Real.cosh u))]
    have hs := Real.abs_sin_le_one (y * u)
    exact div_le_div_of_nonneg_right hs (sq_nonneg _)

/-- The sine transform vanishes by oddness. -/
theorem integral_sin_mul_invCoshSq_eq_zero (y : ℝ) :
    (∫ u : ℝ, Real.sin (y * u) / (Real.cosh u) ^ 2) = 0 := by
  have h := MeasureTheory.integral_neg_eq_self
    (fun u : ℝ => Real.sin (y * u) / (Real.cosh u) ^ 2)
    (volume : Measure ℝ)
  have hodd (u : ℝ) :
      Real.sin (y * (-u)) / (Real.cosh (-u)) ^ 2 =
        -(Real.sin (y * u) / (Real.cosh u) ^ 2) := by
    rw [show y * (-u) = -(y * u) by ring, Real.sin_neg, Real.cosh_neg]
    ring
  simp_rw [hodd, integral_neg] at h
  linarith

end
end MAPKhaleCoshSqKernelIntegrable

#print axioms MAPKhaleCoshSqKernelIntegrable.invCoshSq_integrable
