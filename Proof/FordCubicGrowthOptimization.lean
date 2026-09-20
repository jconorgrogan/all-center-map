import Mathlib

noncomputable section
namespace FordCubicGrowthOptimization

/-- The cubic penalty is optimized at the square-root scale. -/
theorem cubic_growth_optimization
    {eta L T c : ℝ} (heta : 0 ≤ eta) (hL : 0 ≤ L)
    (hT : 0 < T) (hc : 0 < c) :
    eta * L - c * L ^ 3 / T ^ 2 ≤
      eta * Real.sqrt (eta / c) * T := by
  have hratio : 0 ≤ eta / c := div_nonneg heta hc.le
  have hsqrt : 0 ≤ Real.sqrt (eta / c) := Real.sqrt_nonneg _
  have hsquare : (Real.sqrt (eta / c)) ^ 2 = eta / c :=
    Real.sq_sqrt hratio
  by_cases hsmall : L ≤ Real.sqrt (eta / c) * T
  · have hpen : 0 ≤ c * L ^ 3 / T ^ 2 := by positivity
    have hlin : eta * L ≤ eta * (Real.sqrt (eta / c) * T) :=
      mul_le_mul_of_nonneg_left hsmall heta
    linarith
  · have hlarge : Real.sqrt (eta / c) * T ≤ L := le_of_not_ge hsmall
    have hbase : 0 ≤ Real.sqrt (eta / c) * T := by positivity
    have hsq : (Real.sqrt (eta / c) * T) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ hbase hlarge 2
    have hscale : eta * T ^ 2 ≤ c * L ^ 2 := by
      calc
        eta * T ^ 2 = c * (Real.sqrt (eta / c) * T) ^ 2 := by
          rw [mul_pow, hsquare]
          field_simp
        _ ≤ c * L ^ 2 := mul_le_mul_of_nonneg_left hsq hc.le
    have hpen : eta * L ≤ c * L ^ 3 / T ^ 2 := by
      apply (le_div_iff₀ (sq_pos_of_pos hT)).2
      calc
        eta * L * T ^ 2 = L * (eta * T ^ 2) := by ring
        _ ≤ L * (c * L ^ 2) := mul_le_mul_of_nonneg_left hscale hL
        _ = c * L ^ 3 := by ring
    have hrhs : 0 ≤ eta * Real.sqrt (eta / c) * T := by positivity
    linarith

end FordCubicGrowthOptimization

#print axioms FordCubicGrowthOptimization.cubic_growth_optimization
