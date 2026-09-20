import Mathlib

noncomputable section
namespace FordLogScaleThreshold

/-- A direct fifth-power form of the scale implication. -/
theorem ratio_fourth_of_fifth {L T : ℝ} (hL : 0 < L)
    (h5 : (256000000000000 : ℝ) * T ^ 4 ≤ L ^ 5) :
    (256000000000000 : ℝ) * (T / L) ^ 4 ≤ L := by
  calc
    (256000000000000 : ℝ) * (T / L) ^ 4 =
        ((256000000000000 : ℝ) * T ^ 4) / L ^ 4 := by
      rw [div_pow]
      ring
    _ ≤ L ^ 5 / L ^ 4 := by
      exact div_le_div_of_nonneg_right h5 (by positivity)
    _ = L := by
      field_simp

/-- The concrete `1000 * T^(4/5) ≤ L` threshold implies the fourth-power
ratio bound used by the logarithmic scale conversion. -/
theorem ratio_fourth_of_threshold {L T : ℝ} (hL : 0 < L) (hT : 0 < T)
    (hthreshold : (1000 : ℝ) * T ^ ((4 : ℝ) / 5) ≤ L) :
    (256000000000000 : ℝ) * (T / L) ^ 4 ≤ L := by
  have hpow :
      ((1000 : ℝ) * T ^ ((4 : ℝ) / 5)) ^ (5 : ℕ) ≤ L ^ 5 := by
    exact pow_le_pow_left₀ (by positivity) hthreshold 5
  have hTpow :
      (T ^ ((4 : ℝ) / 5)) ^ (5 : ℕ) = T ^ (4 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hT.le]
    norm_num
  have hfive :
      (1000000000000000 : ℝ) * T ^ 4 ≤ L ^ 5 := by
    calc
      (1000000000000000 : ℝ) * T ^ 4 =
          ((1000 : ℝ) * T ^ ((4 : ℝ) / 5)) ^ (5 : ℕ) := by
        rw [mul_pow, hTpow]
        norm_num
      _ ≤ L ^ 5 := hpow
  have hconst : (256000000000000 : ℝ) ≤ 1000000000000000 := by norm_num
  have h5 : (256000000000000 : ℝ) * T ^ 4 ≤ L ^ 5 := by
    exact (mul_le_mul_of_nonneg_right hconst (by positivity)).trans hfive
  exact ratio_fourth_of_fifth hL h5

end FordLogScaleThreshold

#print axioms FordLogScaleThreshold.ratio_fourth_of_fifth
#print axioms FordLogScaleThreshold.ratio_fourth_of_threshold
