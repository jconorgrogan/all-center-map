import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary near-one core for the sharp zeta logarithmic derivative

This file isolates the numerical and algebraic end of the sum--integral proof.
It deliberately has no dependency on the MAP build graph, so it can be checked
while the larger project is being rebuilt.
-/

namespace MAPKhaleZetaNearOneCore

noncomputable section

/-- A deliberately coarse certified upper bound, sufficient for the near-one
calculation. -/
theorem log_three_lt_eleven_tenths : Real.log 3 < (1.1 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)]
  have h := Real.sum_le_exp_of_nonneg (x := (1.1 : ℝ)) (by norm_num) 6
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

/-- The numerical inequality left after the *correct* integral comparison.
The logarithmic summand is only antitone from `3` onward, so the terms at `2`
and `3` are retained separately. -/
theorem corrected_scalar_near_one
    {delta : ℝ} (hdelta : 0 < delta) (hdeltaTop : delta ≤ 1 / 1000) :
    delta * Real.log 2 * (2 : ℝ) ^ (-(1 + delta) : ℝ) +
        delta * Real.log 3 * (3 : ℝ) ^ (-(1 + delta) : ℝ) +
        (3 : ℝ) ^ (-delta : ℝ) * Real.log 3
      ≤ 1 + (2 : ℝ) ^ (-(1 + delta) : ℝ) := by
  have hdlt : delta < 1 := lt_of_le_of_lt hdeltaTop (by norm_num)
  have hpow2nonneg : 0 ≤ (2 : ℝ) ^ (-(1 + delta) : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow3nonneg : 0 ≤ (3 : ℝ) ^ (-(1 + delta) : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow3dnonneg : 0 ≤ (3 : ℝ) ^ (-delta : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hpow2one : (2 : ℝ) ^ (-(1 + delta) : ℝ) ≤ 1 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
        (y := -(1 + delta)) (z := 0) (by norm_num) (by linarith))
  have hpow3one : (3 : ℝ) ^ (-(1 + delta) : ℝ) ≤ 1 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ))
        (y := -(1 + delta)) (z := 0) (by norm_num) (by linarith))
  have hpow3done : (3 : ℝ) ^ (-delta : ℝ) ≤ 1 := by
    simpa using
      (Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ))
        (y := -delta) (z := 0) (by norm_num) (by linarith))
  have hpow2quarter : (1 / 4 : ℝ) ≤
      (2 : ℝ) ^ (-(1 + delta) : ℝ) := by
    have hp := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
      (y := (-2 : ℝ)) (z := -(1 + delta)) (by norm_num) (by linarith)
    norm_num [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)] at hp ⊢
    exact hp
  have hlog2pos : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num)).le
  have hlog3pos : 0 ≤ Real.log 3 := (Real.log_pos (by norm_num)).le
  have hlog2 : Real.log 2 ≤ (0.7 : ℝ) := Real.log_two_lt_d9.le.trans (by norm_num)
  have hlog3 : Real.log 3 ≤ (1.1 : ℝ) := log_three_lt_eleven_tenths.le
  have hdelta001 : delta ≤ (0.001 : ℝ) := by
    norm_num at hdeltaTop ⊢
    exact hdeltaTop
  have hterm2 : delta * Real.log 2 * (2 : ℝ) ^ (-(1 + delta) : ℝ)
      ≤ (0.001 : ℝ) * 0.7 * 1 := by gcongr
  have hterm3 : delta * Real.log 3 * (3 : ℝ) ^ (-(1 + delta) : ℝ)
      ≤ (0.001 : ℝ) * 1.1 * 1 := by gcongr
  have htail : (3 : ℝ) ^ (-delta : ℝ) * Real.log 3 ≤ 1 * 1.1 := by
    gcongr
  nlinarith

/-- Algebraic weld from the two sum--integral estimates to positivity of
`zeta + delta * zeta'`.  Here `z` stands for zeta and `n` for `-zeta'`.
The hypotheses are exactly the estimates delivered by the integral test.
-/
theorem normalized_nonnegative_of_corrected_sum_integral_bounds
    {delta z n : ℝ} (hdelta : 0 < delta) (hdeltaTop : delta ≤ 1 / 1000)
    (hz : 1 + (2 : ℝ) ^ (-(1 + delta) : ℝ) +
      (3 : ℝ) ^ (-delta : ℝ) / delta ≤ z)
    (hn : n ≤ Real.log 2 * (2 : ℝ) ^ (-(1 + delta) : ℝ) +
      Real.log 3 * (3 : ℝ) ^ (-(1 + delta) : ℝ) +
      (3 : ℝ) ^ (-delta : ℝ) *
        (Real.log 3 / delta + 1 / delta ^ 2)) :
    0 ≤ z - delta * n := by
  have hkey := corrected_scalar_near_one hdelta hdeltaTop
  have hdelta0 : delta ≠ 0 := hdelta.ne'
  have hn' : delta * n ≤ delta *
      (Real.log 2 * (2 : ℝ) ^ (-(1 + delta) : ℝ) +
        Real.log 3 * (3 : ℝ) ^ (-(1 + delta) : ℝ) +
        (3 : ℝ) ^ (-delta : ℝ) *
          (Real.log 3 / delta + 1 / delta ^ 2)) :=
    mul_le_mul_of_nonneg_left hn hdelta.le
  calc
    0 ≤ (1 + (2 : ℝ) ^ (-(1 + delta) : ℝ) +
        (3 : ℝ) ^ (-delta : ℝ) / delta) - delta *
        (Real.log 2 * (2 : ℝ) ^ (-(1 + delta) : ℝ) +
          Real.log 3 * (3 : ℝ) ^ (-(1 + delta) : ℝ) +
          (3 : ℝ) ^ (-delta : ℝ) *
            (Real.log 3 / delta + 1 / delta ^ 2)) := by
      field_simp [hdelta0] at hkey ⊢
      nlinarith
    _ ≤ z - delta * n := by linarith

end

end MAPKhaleZetaNearOneCore

#print axioms MAPKhaleZetaNearOneCore.corrected_scalar_near_one
#print axioms MAPKhaleZetaNearOneCore.normalized_nonnegative_of_corrected_sum_integral_bounds
