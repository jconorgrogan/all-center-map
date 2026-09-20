import GuthMaynardS3CubicSeamParameters
import GuthMaynardS3DyadicLogLoss

open scoped Real
noncomputable section
namespace GuthMaynardS3CubicLoss
open GuthMaynardS3CubicSeamParameters

/-- Changing only the analytic horizon costs three copies of the source
subpower loss; the numerical factor is uniform for eta at most one. -/
theorem cubic_horizon_loss {T eta : ℝ} (hT : 1 ≤ T) (heta : eta ≤ 1) :
    (64*T^3)^eta ≤ 64*(T^eta)^3 := by
  have hTp : 0 < T := by linarith
  rw [cubic_horizon_power hTp.le]
  have h64 : (64 : ℝ)^eta ≤ 64 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 64) heta
  have hp : (T^eta)^(3 : ℕ) = T^(3*eta) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hTp.le]
    congr 1 <;> ring
  rw [hp]
  exact mul_le_mul_of_nonneg_right h64 (by positivity)

end GuthMaynardS3CubicLoss
#print axioms GuthMaynardS3CubicLoss.cubic_horizon_loss
