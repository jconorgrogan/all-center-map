import Mathlib

open MeasureTheory Set
noncomputable section
namespace GuthMaynardS3InversionIntegral

private theorem inv_continuousOn_unit :
    ContinuousOn (fun v : ℝ => v⁻¹) (Icc (1/2 : ℝ) 2) := by
  apply continuousOn_id.inv₀
  intro v hv
  change v ≠ 0
  linarith [hv.1]

/-- Exact inversion Jacobian on the source interval. -/
theorem integral_inversion_jacobian (G : ℝ → ℝ) (hG : Continuous G) :
    (∫ v in (1/2 : ℝ)..2, G v⁻¹ / v^2) = ∫ v in (1/2 : ℝ)..2, G v := by
  have hd : ∀ v ∈ uIcc (1/2 : ℝ) 2,
      HasDerivAt (fun x : ℝ => x⁻¹) (-(v^2)⁻¹) v := by
    intro v hv
    have hv' : v ∈ Icc (1/2 : ℝ) 2 := by
      rw [uIcc_of_le (by norm_num : (1/2:ℝ)≤2)] at hv
      exact hv
    have hvne : v ≠ 0 := by linarith [hv'.1]
    simpa [div_eq_mul_inv] using (hasDerivAt_id v).inv hvne
  have hc : ContinuousOn (fun v : ℝ => -(v^2)⁻¹) (uIcc (1/2 : ℝ) 2) := by
    rw [uIcc_of_le (by norm_num : (1/2:ℝ)≤2)]
    have hi := inv_continuousOn_unit
    simpa [inv_pow] using (hi.pow 2).neg
  have h := intervalIntegral.integral_comp_mul_deriv hd hc hG
  have he : (fun v : ℝ => (G ∘ (fun x : ℝ => x⁻¹)) v * (-(v^2)⁻¹)) =
      (fun v : ℝ => -(G v⁻¹ / v^2)) := by funext v; simp [Function.comp_def, div_eq_mul_inv]
  rw [he, intervalIntegral.integral_neg] at h
  norm_num at h
  rw [intervalIntegral.integral_symm (f := G) (1/2 : ℝ) 2] at h
  linarith

/-- Inversion costs at most four in a nonnegative integral over [1/2,2]. -/
theorem integral_inversion_le_four (G : ℝ → ℝ) (hG : Continuous G)
    (hG0 : ∀ v, 0 ≤ G v) :
    (∫ v in Icc (1/2 : ℝ) 2, G v⁻¹) ≤
      4 * ∫ v in Icc (1/2 : ℝ) 2, G v := by
  have hi := inv_continuousOn_unit
  have hcomp : ContinuousOn (fun v : ℝ => G v⁻¹) (Icc (1/2 : ℝ) 2) :=
    hG.comp_continuousOn hi
  have hw : ContinuousOn (fun v : ℝ => G v⁻¹ / v^2) (Icc (1/2 : ℝ) 2) := by
    simpa [div_eq_mul_inv, inv_pow] using hcomp.mul (hi.pow 2)
  have ha : IntervalIntegrable (fun v : ℝ => G v⁻¹) volume (1/2) 2 :=
    hcomp.intervalIntegrable_of_Icc (by norm_num)
  have hb : IntervalIntegrable (fun v : ℝ => 4 * (G v⁻¹ / v^2)) volume (1/2) 2 :=
    (continuousOn_const.mul hw).intervalIntegrable_of_Icc (by norm_num)
  have hpoint : ∀ v ∈ Icc (1/2 : ℝ) 2, G v⁻¹ ≤ 4 * (G v⁻¹ / v^2) := by
    intro v hv
    have hv0 : 0 < v := by linarith [hv.1]
    have hs : v^2 ≤ (4 : ℝ) := by nlinarith [hv.2]
    have hg0 := hG0 v⁻¹
    have hh := mul_le_mul_of_nonneg_right hs (div_nonneg hg0 (sq_nonneg v))
    have he := div_mul_cancel₀ (G v⁻¹) (pow_ne_zero 2 hv0.ne')
    nlinarith
  have hm := intervalIntegral.integral_mono_on (by norm_num : (1/2:ℝ)≤2) ha hb hpoint
  rw [intervalIntegral.integral_const_mul, integral_inversion_jacobian G hG] at hm
  simpa only [integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by norm_num : (1/2:ℝ)≤2)] using hm
end GuthMaynardS3InversionIntegral
#print axioms GuthMaynardS3InversionIntegral.integral_inversion_le_four
