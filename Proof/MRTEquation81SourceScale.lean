import MRTEquation81

/-!
# Source-scale form of MRT equation (81)

This is the deterministic cancellation which turns the multiplication-only
Schur inequality into the exact `R⁻¹` scale used after equation (82).  It does
not consume a packet estimate or any source theorem.
-/

namespace MAPMRTEquation81SourceScale

open MeasureTheory
open MAPMRTEquation81AveragingBilinear MAPMRTEquation81

noncomputable section

/-- Cancelling the finite positive box mass in equation (81) gives the
source-facing normalization `R * B_R(F) ≤ 18 ∫ A_R(F)^2`. -/
theorem equation81_source_scale
    {R : ℝ} {F : ℝ → ENNReal} (hR : 0 < R) (hF : Measurable F)
    (hAfin : ∀ x, equation81Average R F x ≠ ⊤) :
    ENNReal.ofReal R * equation81Bilinear R F ≤
      18 * (∫⁻ x : ℝ, (equation81Average R F x) ^ 2) := by
  have h := equation81_averaging_schur hR hF hAfin
  have htwo : ENNReal.ofReal (2 * R) = 2 * ENNReal.ofReal R := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat]
  have hfour : ENNReal.ofReal (4 * R) = 4 * ENNReal.ofReal R := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  rw [htwo, hfour] at h
  let r : ENNReal := ENNReal.ofReal R
  let I : ENNReal := ∫⁻ x : ℝ, (equation81Average R F x) ^ 2
  have hr0 : r ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr hR)
  have hrtop : r ≠ ⊤ := ENNReal.ofReal_ne_top
  have hfactor0 : 4 * r ≠ 0 := mul_ne_zero (by norm_num) hr0
  have hfactortop : 4 * r ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hrtop
  apply (ENNReal.mul_le_mul_iff_right hfactor0 hfactortop).mp
  calc
    (4 * r) * (r * equation81Bilinear R F) =
        (2 * r) ^ 2 * equation81Bilinear R F := by ring
    _ ≤ 18 * (4 * r) * I := by simpa [r, I] using h
    _ = (4 * r) * (18 * I) := by ring

#print axioms equation81_source_scale

end
end MAPMRTEquation81SourceScale
