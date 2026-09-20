import GuthMaynardS3CubicHorizonTail

open scoped Real
noncomputable section
namespace GuthMaynardS3CubicHorizonMomentTail
open GuthMaynardS3CubicHorizonTail

/-- A source-time moment tail is kept distinct from the analytic-horizon
frequency tail. Both leave enough reserve for the final square root. -/
theorem source_moment_tail_after_cubic_prefactor
    {T epsilon P : ℝ} (hT : 1 ≤ T) (heps : epsilon ≤ 1)
    (hP0 : 0 ≤ P) (hP : P ≤ 128*T^15) :
    P*(64*T^3)^epsilon*T^(-400 : ℝ) ≤ 8192*T^(-382 : ℝ) := by
  have hTp : 0 < T := by linarith
  have hT3 : 1 ≤ T^3 := one_le_pow₀ hT
  have hU1 : 1 ≤ 64*T^3 := by linarith
  have hU : (64*T^3)^epsilon ≤ 64*T^3 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hU1 heps
  have hprod : P*(64*T^3)^epsilon ≤ 8192*T^18 := by
    calc
      P*(64*T^3)^epsilon ≤ (128*T^15)*(64*T^3) :=
        mul_le_mul hP hU (by positivity) (by positivity)
      _ = 8192*T^18 := by ring
  calc
    P*(64*T^3)^epsilon*T^(-400 : ℝ) ≤
        (8192*T^18)*T^(-400 : ℝ) :=
      mul_le_mul_of_nonneg_right hprod (by positivity)
    _ = 8192*T^(-382 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_natCast T 18, ← Real.rpow_add hTp]
      norm_num

theorem log_weighted_sqrt_moment_tail
    {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C) :
    (1+Real.log T)^2 * Real.sqrt (C*T^(-382 : ℝ)) ≤
      Real.sqrt C*T^(-100 : ℝ) := by
  have hp : C*T^(-382 : ℝ) ≤ C*T^(-282 : ℝ) :=
    mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)) hC
  exact (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hp) (sq_nonneg _)).trans
    (log_weighted_sqrt_tail hT hC)

end GuthMaynardS3CubicHorizonMomentTail
#print axioms GuthMaynardS3CubicHorizonMomentTail.source_moment_tail_after_cubic_prefactor
#print axioms GuthMaynardS3CubicHorizonMomentTail.log_weighted_sqrt_moment_tail
