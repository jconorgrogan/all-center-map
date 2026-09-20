import GuthMaynardS3MediumActualAlgebra

open scoped Real

noncomputable section
namespace GuthMaynardS3NormalizedMainAbsorption
open GuthMaynardS3MediumActualAlgebra

theorem normalizedSigma_main_with_radius
    {T eta delta Ceta K M M1 M2 M3 F2 J : ℝ}
    (hT : 1 ≤ T) (heta : 0 < eta) (hCeta : 0 ≤ Ceta)
    (hK : 0 ≤ K) (hM : 0 ≤ M) (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2)
    (hM3 : 0 ≤ M3) (hM1M : M1 ≤ M) (hM2M : M2 ≤ M)
    (hM3M : M3 ≤ M) :
    (16 * Ceta * Real.rpow T (2 * eta) * K ^ 2 * (M1 + M3)) *
      ((2 * Real.rpow T eta * (4 * Real.rpow T eta * K)) *
        (2 : ℝ) ^ 2 * M2 *
          Real.sqrt (F2 * ((4 * Real.rpow T delta) ^ 2 * J))) ≤
      8192 * Ceta * K ^ 3 * Real.rpow T (4 * eta + delta) *
        M ^ 2 * Real.sqrt (F2 * J) := by
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hdelta : 0 ≤ 4 * Real.rpow T delta :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg hT0.le _)
  have hsqrt : Real.sqrt (F2 * ((4 * Real.rpow T delta) ^ 2 * J)) =
      (4 * Real.rpow T delta) * Real.sqrt (F2 * J) := by
    rw [show F2 * ((4 * Real.rpow T delta) ^ 2 * J) =
      (4 * Real.rpow T delta) ^ 2 * (F2 * J) by ring]
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs, abs_of_nonneg hdelta]
  have hmain := normalizedSigma_main_factor_le hT heta hCeta hK hM hM1 hM2 hM3
    hM1M hM2M hM3M (Real.sqrt_nonneg (F2 * ((4 * Real.rpow T delta) ^ 2 * J)))
  calc
    _ ≤ 2048 * Ceta * K ^ 3 * Real.rpow T (4 * eta) * M ^ 2 *
        Real.sqrt (F2 * ((4 * Real.rpow T delta) ^ 2 * J)) := hmain
    _ = 8192 * Ceta * K ^ 3 *
        (Real.rpow T (4 * eta) * Real.rpow T delta) * M ^ 2 * Real.sqrt (F2 * J) := by
      rw [hsqrt]
      ring
    _ = _ := by
      simp only [Real.rpow_eq_pow]
      rw [← Real.rpow_add hT0]

end GuthMaynardS3NormalizedMainAbsorption
end

#print axioms GuthMaynardS3NormalizedMainAbsorption.normalizedSigma_main_with_radius
