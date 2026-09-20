import FordCubicGrowthOptimization

noncomputable section
namespace FordWeightedCubicEnvelope

/-- Multiplying a cubic cancellation bound by the real decay weight produces
a uniform envelope independent of the block location. -/
theorem weighted_cubic_envelope {N T c eta : ℝ}
    (hN : 1 ≤ N) (hT : 0 < T) (hc : 0 < c) (heta : 0 ≤ eta) :
    N ^ (-(1 - eta)) *
        (272 * N * Real.exp (-c * (Real.log N) ^ 3 / T ^ 2)) ≤
      272 * Real.exp (eta * Real.sqrt (eta / c) * T) := by
  have hNp : 0 < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg hN
  have hid : N ^ (-(1 - eta)) *
      (272 * N * Real.exp (-c * (Real.log N) ^ 3 / T ^ 2)) =
      272 * Real.exp (eta * Real.log N - c * (Real.log N) ^ 3 / T ^ 2) := by
    rw [Real.rpow_def_of_pos hNp]
    conv_lhs => rw [← Real.exp_log hNp]
    rw [show Real.log (Real.exp (Real.log N)) = Real.log N by rw [Real.log_exp]]
    calc
      _ = 272 * (Real.exp (Real.log N * -(1 - eta)) * Real.exp (Real.log N) *
          Real.exp (-c * (Real.log N) ^ 3 / T ^ 2)) := by ring
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr
      (FordCubicGrowthOptimization.cubic_growth_optimization heta hL hT hc))
    (by norm_num)

end FordWeightedCubicEnvelope
#print axioms FordWeightedCubicEnvelope.weighted_cubic_envelope
