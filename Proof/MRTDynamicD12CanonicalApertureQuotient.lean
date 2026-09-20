import MRTDynamicD12CanonicalElementary
namespace MRTDynamicD12CanonicalApertureQuotient

theorem rpow_div_canonical_aperture_le {X delta reserve : ℝ}
    (hX : 1 ≤ X) (hr : 0 ≤ reserve) :
    Real.rpow X delta / ((1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve)) ≤
      2 * Real.rpow X (delta - 2 / 15 : ℝ) := by
  have hXpos : 0 < X := by linarith
  have hp : 0 < Real.rpow X (2 / 15 + reserve) := Real.rpow_pos_of_pos hXpos _
  have heq : Real.rpow X delta / ((1 / 2 : ℝ) * Real.rpow X (2 / 15 + reserve)) =
      2 * Real.rpow X (delta - (2 / 15 + reserve)) := by
    have hsub : Real.rpow X (delta - (2 / 15 + reserve)) =
        Real.rpow X delta / Real.rpow X (2 / 15 + reserve) := by
      simpa only [Real.rpow_eq_pow] using Real.rpow_sub hXpos delta (2 / 15 + reserve)
    rw [hsub]
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) (by norm_num)
end MRTDynamicD12CanonicalApertureQuotient
#print axioms MRTDynamicD12CanonicalApertureQuotient.rpow_div_canonical_aperture_le
