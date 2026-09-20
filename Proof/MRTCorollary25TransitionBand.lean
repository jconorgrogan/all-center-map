import MRTCorollary25PerronCore

/-!
# Transition-band estimate for MRT Corollary 2.5

This file reconstructs the `min(1, X/(T |x-n|))` mechanism in the
published truncated Perron formula.  It does not assume Corollary 2.5.
-/

namespace MAPMRTCorollary25TransitionBand

open MAPMRTCorollary25PerronCore PrimitiveTruncatedExplicitFormulaBridge

noncomputable section

/-- At the centre of the Perron transition, the kernel is between zero and
one; hence its distance from either sharp-step value is at most one. -/
theorem norm_kernel_one_sub_step_le_one
    {y c T : ℝ} (hc : 0 < c) (hT : 0 ≤ T) :
    ‖PerronKernel.kernel 1 c T -
        (if 1 < y then (1 : ℂ) else 0)‖ ≤ 1 := by
  rw [PerronKernel.kernel_one_eq_arctan hc]
  have hdiv : 0 ≤ T / c := div_nonneg hT hc.le
  have ha0 : 0 ≤ Real.arctan (T / c) := Real.arctan_nonneg.mpr hdiv
  have hapi : Real.arctan (T / c) ≤ Real.pi := by
    linarith [Real.arctan_lt_pi_div_two (T / c), Real.pi_pos]
  have hpi : 0 < Real.pi := Real.pi_pos
  have hq0 : 0 ≤ Real.arctan (T / c) / Real.pi := div_nonneg ha0 hpi.le
  have hq1 : Real.arctan (T / c) / Real.pi ≤ 1 :=
    (div_le_one hpi).2 hapi
  by_cases hy1 : 1 < y
  · simp only [hy1, if_true]
    change ‖((Real.arctan (T / c) / Real.pi : ℝ) : ℂ) - 1‖ ≤ 1
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs]
    rw [abs_of_nonpos (by linarith : Real.arctan (T / c) / Real.pi - 1 ≤ 0)]
    linarith
  · simp only [hy1, if_false, sub_zero]
    change ‖((Real.arctan (T / c) / Real.pi : ℝ) : ℂ)‖ ≤ 1
    rw [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg hq0]
    exact hq1

/-- Away from the small contour neighbourhood of one, the product
`T*|log y|` is still bounded below by `2/3`.  This is the quantitative weld
which lets the sharp `1/(T|log y|)` estimate meet the trivial transition-band
bound without a logarithmic loss. -/
theorem two_thirds_le_T_mul_abs_log_of_not_near
    {y T : ℝ} (hT : 1 ≤ T)
    (hfar : ¬ |Real.log y| * ((1 / 2 : ℝ) + T) ≤ 1) :
    (2 / 3 : ℝ) < T * |Real.log y| := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have ha0 : 0 ≤ |Real.log y| := abs_nonneg _
  have ha_le : |Real.log y| ≤ T * |Real.log y| := by
    nlinarith
  have hstrict : 1 < |Real.log y| * ((1 / 2 : ℝ) + T) := lt_of_not_ge hfar
  nlinarith

/-- Reciprocal form of the preceding transition-band lower bound. -/
theorem inv_T_mul_abs_log_le_three_halves_of_not_near
    {y T : ℝ} (hT : 1 ≤ T)
    (hfar : ¬ |Real.log y| * ((1 / 2 : ℝ) + T) ≤ 1) :
    1 / (T * |Real.log y|) < (3 / 2 : ℝ) := by
  have hz := two_thirds_le_T_mul_abs_log_of_not_near hT hfar
  have hzpos : 0 < T * |Real.log y| := lt_trans (by norm_num) hz
  rw [div_lt_iff₀ hzpos]
  nlinarith

/-- Source-faithful transition-band Perron estimate.  The right side has the
literal `min(1, 1/(T|log y|))` shape used before the harmonic summation in MRT
Lemma 2.4(ii).  The constant is deliberately generous and depends only on an
upper bound for the ratio `y`. -/
theorem norm_kernel_sub_step_le_transitionMin
    {y R T : ℝ} (hy : 0 < y) (hyne : y ≠ 1)
    (hyR : y ≤ R) (hT : 1 ≤ T) :
    ‖PerronKernel.kernel y (1 / 2 : ℝ) T -
        (if 1 < y then (1 : ℂ) else 0)‖ ≤
      3 * (1 + Real.sqrt R) *
        min 1 (1 / (T * |Real.log y|)) := by
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one hT
  have hT0 : 0 ≤ T := hTpos.le
  have hc : (0 : ℝ) < 1 / 2 := by norm_num
  have hR0 : 0 ≤ R := le_trans hy.le hyR
  have hsqrt : Real.sqrt y ≤ Real.sqrt R := Real.sqrt_le_sqrt hyR
  have haPos : 0 < |Real.log y| := abs_pos.mpr
    (Real.log_ne_zero_of_pos_of_ne_one hy hyne)
  by_cases hnear : |Real.log y| * ((1 / 2 : ℝ) + T) ≤ 1
  · have hTa : T * |Real.log y| ≤ 1 := by
      nlinarith [abs_nonneg (Real.log y)]
    have hmin : min 1 (1 / (T * |Real.log y|)) = 1 := by
      rw [min_eq_left]
      exact (le_div_iff₀ (mul_pos hTpos haPos)).2 (by simpa using hTa)
    rw [hmin]
    have hnearKernel := PerronKernel.norm_kernel_sub_one_le hy hc hT0 hnear
    have hcenter := norm_kernel_one_sub_step_le_one (y := y) hc hT0
    have htri :
        ‖PerronKernel.kernel y (1 / 2 : ℝ) T -
            (if 1 < y then (1 : ℂ) else 0)‖ ≤
          ‖PerronKernel.kernel y (1 / 2 : ℝ) T -
              PerronKernel.kernel 1 (1 / 2 : ℝ) T‖ +
            ‖PerronKernel.kernel 1 (1 / 2 : ℝ) T -
              (if 1 < y then (1 : ℂ) else 0)‖ := by
      simpa [sub_eq_add_neg, add_assoc] using
        norm_add_le
          (PerronKernel.kernel y (1 / 2 : ℝ) T -
            PerronKernel.kernel 1 (1 / 2 : ℝ) T)
          (PerronKernel.kernel 1 (1 / 2 : ℝ) T -
            (if 1 < y then (1 : ℂ) else 0))
    calc
      _ ≤ 2 * T * |Real.log y| / Real.pi + 1 :=
        htri.trans (add_le_add hnearKernel hcenter)
      _ ≤ 3 := by
        have hpi : 1 ≤ Real.pi := by linarith [Real.pi_gt_three]
        have hfrac : 2 * T * |Real.log y| / Real.pi ≤ 2 := by
          apply (div_le_iff₀ Real.pi_pos).2
          nlinarith
        linarith
      _ ≤ 3 * (1 + Real.sqrt R) * 1 := by
        nlinarith [Real.sqrt_nonneg R]
  · have hk := SharpFinitePerronStep.norm_kernel_sub_step_le
      hy hc hTpos hyne
    have hsqrtPow : y ^ (1 / 2 : ℝ) = Real.sqrt y := by
      simpa [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num] using
        (Real.sqrt_eq_rpow y).symm
    rw [hsqrtPow] at hk
    have hpiInv : 1 / Real.pi ≤ 1 := by
      exact (div_le_one Real.pi_pos).2 (by linarith [Real.pi_gt_three])
    have hzpos : 0 < T * |Real.log y| := mul_pos hTpos haPos
    have hsharp :
        ‖PerronKernel.kernel y (1 / 2 : ℝ) T -
            (if 1 < y then (1 : ℂ) else 0)‖ ≤
          Real.sqrt R * (1 / (T * |Real.log y|)) := by
      refine hk.trans ?_
      have hden : 0 < Real.pi * T * |Real.log y| := by positivity
      calc
        Real.sqrt y / (Real.pi * T * |Real.log y|) =
            Real.sqrt y * (1 / Real.pi) *
              (1 / (T * |Real.log y|)) := by field_simp
        _ ≤ Real.sqrt R * 1 * (1 / (T * |Real.log y|)) := by
          gcongr
        _ = Real.sqrt R * (1 / (T * |Real.log y|)) := by ring
    by_cases hz : 1 ≤ T * |Real.log y|
    · rw [min_eq_right]
      · exact hsharp.trans (by
          gcongr
          nlinarith [Real.sqrt_nonneg R])
      · exact (div_le_one hzpos).2 hz
    · have hinv := inv_T_mul_abs_log_le_three_halves_of_not_near hT hnear
      rw [min_eq_left]
      · exact hsharp.trans (by
          have hs0 := Real.sqrt_nonneg R
          have hmul := mul_le_mul_of_nonneg_left (le_of_lt hinv) hs0
          nlinarith)
      · exact (le_div_iff₀ hzpos).2 (by
          simpa using (le_of_not_ge hz))

end
end MAPMRTCorollary25TransitionBand

#print axioms MAPMRTCorollary25TransitionBand.norm_kernel_one_sub_step_le_one
#print axioms MAPMRTCorollary25TransitionBand.norm_kernel_sub_step_le_transitionMin
