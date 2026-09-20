import GuthMaynardS3ActualProfileInputs

open scoped Real

noncomputable section
namespace GuthMaynardS3FourierTailAbsorption

theorem actualFourierTail_scalar_absorption
    {T eta Ceta K D M1 M3 : ℝ}
    (hT : 1 ≤ T) (heta1 : eta ≤ 1)
    (hCeta : 0 ≤ Ceta) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hM1 : 0 ≤ M1) (hM3 : 0 ≤ M3) (hM1T : M1 ≤ T) (hM3T : M3 ≤ T) :
    (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 * (M1 + M3)) *
      ((2 * Real.rpow T eta) * (4 * D ^ 2 * Real.rpow T (-229 : ℝ))) ≤
      256 * Ceta * K ^ 2 * D ^ 2 * Real.rpow T (-100 : ℝ) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have heta : Real.rpow T eta ≤ T := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hT heta1
  have h2eta : Real.rpow T (2 * eta) ≤ T ^ (2 : ℕ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hT
      (show 2 * eta ≤ (2 : ℝ) by linarith)
    simpa only [Real.rpow_two] using h
  have hsum : M1 + M3 ≤ 2 * T := by linarith
  have hpow : T ^ (4 : ℕ) * Real.rpow T (-229 : ℝ) =
      Real.rpow T (-225 : ℝ) := by
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_natCast, ← Real.rpow_add hT0]
    norm_num
  have hdecay : Real.rpow T (-225 : ℝ) ≤ Real.rpow T (-100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hT (by norm_num)
  calc
    _ ≤ (16 * Ceta * T ^ (2 : ℕ) * K ^ 2 * (2 * T)) *
        ((2 * T) * (4 * D ^ 2 * Real.rpow T (-229 : ℝ))) := by
      have htneg := Real.rpow_nonneg hT0.le (-229 : ℝ)
      have hepos := Real.rpow_nonneg hT0.le eta
      gcongr <;> positivity
    _ = (256 * Ceta * K ^ 2 * D ^ 2) *
        (T ^ (4 : ℕ) * Real.rpow T (-229 : ℝ)) := by ring
    _ = (256 * Ceta * K ^ 2 * D ^ 2) * Real.rpow T (-225 : ℝ) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end GuthMaynardS3FourierTailAbsorption
end

#print axioms GuthMaynardS3FourierTailAbsorption.actualFourierTail_scalar_absorption
