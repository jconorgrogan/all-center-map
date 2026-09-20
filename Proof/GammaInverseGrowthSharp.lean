import GammaCompactStripSharp
import GammaInverseGrowth

/-!
# Sharp reciprocal-Gamma growth on a positive compact strip

Reflection converts the sharp `exp (-pi |t| / 2)` Gamma decay proved in
`GammaCompactStripSharp` into `exp (pi |t| / 2)` reciprocal growth.  This is
the second half of the exact exponential cancellation in Huxley's
functional-equation multiplier.
-/

namespace MAPGammaInverseGrowthSharp

open Complex Real

noncomputable section

private theorem one_sub_stripPoint_eq (a t : ℝ) :
    1 - GammaCompactStripScratch.stripPoint a t =
      GammaCompactStripScratch.stripPoint (1 - a) (-t) := by
  apply Complex.ext <;> simp [GammaCompactStripScratch.stripPoint]

private theorem stripPoint_not_neg_nat_of_abs_im
    {a t : ℝ} (ht : 1 ≤ |t|) (n : ℕ) :
    GammaCompactStripScratch.stripPoint a t ≠ -(n : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  simp [GammaCompactStripScratch.stripPoint] at him
  subst t
  norm_num at ht

/-- Sharp reciprocal Gamma bound on `1/2 <= Re z <= 3/2`. -/
theorem norm_inv_Gamma_positive_strip_le_exp_pi_half
    {a t : ℝ} (ha : 1 / 2 ≤ a) (ha' : a ≤ 3 / 2) (ht : 1 ≤ |t|) :
    ‖(Complex.Gamma (GammaCompactStripScratch.stripPoint a t))⁻¹‖ ≤
      12 * (1 + |t|) * Real.exp ((Real.pi / 2) * |t|) := by
  let w := GammaCompactStripScratch.stripPoint a t
  have hwne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero (stripPoint_not_neg_nat_of_abs_im ht)
  have h1wne : Complex.Gamma (1 - w) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n h
    have him := congrArg Complex.im h
    simp [w, GammaCompactStripScratch.stripPoint] at him
    subst t
    norm_num at ht
  have href := Complex.Gamma_mul_Gamma_one_sub w
  have hsin : Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro hs
    rw [hs, div_zero] at href
    exact (mul_ne_zero hwne h1wne) href
  have heq : (Complex.Gamma w)⁻¹ =
      Complex.Gamma (1 - w) * Complex.sin ((Real.pi : ℂ) * w) /
        Real.pi := by
    apply mul_left_cancel₀ hwne
    rw [mul_inv_cancel₀ hwne, mul_div_assoc, ← mul_assoc, href]
    field_simp [hsin, Real.pi_ne_zero]
  have hgamma : ‖Complex.Gamma (1 - w)‖ ≤
      12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) := by
    rw [one_sub_stripPoint_eq]
    simpa [abs_neg] using
      MAPGammaCompactStripSharp.norm_Gamma_compactStrip_le_exp_pi_half
        (a := 1 - a) (t := -t) (by linarith) (by linarith)
          (by simpa [abs_neg])
  have hsinb : ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤
      Real.exp (Real.pi * |t|) := by
    have hs := PLInteriorGrowth.norm_complex_sin_le_exp_abs_im
      ((Real.pi : ℂ) * w)
    have him : (((Real.pi : ℂ) * w).im) = Real.pi * t := by
      simp [w, GammaCompactStripScratch.stripPoint]
    rw [him, abs_mul, abs_of_pos Real.pi_pos] at hs
    exact hs
  rw [heq, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos]
  have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
  have hnum : ‖Complex.Gamma (1 - w)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤
      12 * (1 + |t|) * Real.exp ((Real.pi / 2) * |t|) := by
    calc
      ‖Complex.Gamma (1 - w)‖ *
          ‖Complex.sin ((Real.pi : ℂ) * w)‖ ≤
        (12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|)) *
          Real.exp (Real.pi * |t|) :=
        mul_le_mul hgamma hsinb (norm_nonneg _) (by positivity)
      _ = 12 * (1 + |t|) * Real.exp ((Real.pi / 2) * |t|) := by
        rw [show 12 * (1 + |t|) * Real.exp (-(Real.pi / 2) * |t|) *
            Real.exp (Real.pi * |t|) =
          12 * (1 + |t|) *
            (Real.exp (-(Real.pi / 2) * |t|) *
              Real.exp (Real.pi * |t|)) by ring]
        rw [← Real.exp_add]
        congr 2
        ring
  exact (div_le_self (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hpi).trans hnum

end

end MAPGammaInverseGrowthSharp

#print axioms MAPGammaInverseGrowthSharp.norm_inv_Gamma_positive_strip_le_exp_pi_half
