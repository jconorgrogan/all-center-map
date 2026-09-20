import Mathlib

noncomputable section
namespace FordDifferencePowerStep

/-- A scalar power step for a nonnegative increment. -/
theorem power_step {m : ℕ} (hm : 1 ≤ m) {a y : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hy0 : 0 ≤ y) :
    (a + 4 * y) ^ m ≤ 5 ^ m * (a + y ^ m) := by
  have hbase : a + 4 * y ≤ 5 * max a y := by
    by_cases hay : a ≤ y
    · rw [max_eq_right hay]
      nlinarith
    · have hya : y ≤ a := le_of_not_ge hay
      rw [max_eq_left hya]
      nlinarith
  have hpowbase : (a + 4 * y) ^ m ≤ (5 * max a y) ^ m := by
    exact pow_le_pow_left₀ (by positivity) hbase m
  have hmaxpow : (max a y) ^ m ≤ a + y ^ m := by
    by_cases hay : a ≤ y
    · rw [max_eq_right hay]
      nlinarith
    · have hya : y ≤ a := le_of_not_ge hay
      rw [max_eq_left hya]
      have hapow : a ^ m ≤ a := by
        rw [show m = (m - 1) + 1 by omega, pow_add]
        have hpowone : a ^ (m - 1) ≤ (1 : ℝ) :=
          pow_le_one₀ ha0 ha1
        simpa using mul_le_mul_of_nonneg_right hpowone ha0
      have hym0 : 0 ≤ y ^ m := pow_nonneg hy0 _
      nlinarith
  calc
    (a + 4 * y) ^ m ≤ (5 * max a y) ^ m := hpowbase
    _ = 5 ^ m * (max a y) ^ m := by rw [mul_pow]
    _ ≤ 5 ^ m * (a + y ^ m) :=
      mul_le_mul_of_nonneg_left hmaxpow (by positivity)

/-- The fixed coefficient is absorbed by `16^m` for every positive order. -/
theorem coefficient_step {m : ℕ} (hm : 1 ≤ m) :
    (2 : ℝ) * 5 ^ m ≤ 16 ^ m := by
  have h2pow : (2 : ℝ) ^ 1 ≤ 2 ^ m := by
    exact pow_le_pow_right₀ (by norm_num) hm
  have hmul : (2 : ℝ) * 5 ^ m ≤ 2 ^ m * 5 ^ m := by
    have hh := mul_le_mul_of_nonneg_right h2pow
      (by positivity : (0 : ℝ) ≤ 5 ^ m)
    simpa using hh
  calc
    (2 : ℝ) * 5 ^ m ≤ 2 ^ m * 5 ^ m := hmul
    _ = (2 * 5) ^ m := by rw [mul_pow]
    _ ≤ 16 ^ m := by
      exact pow_le_pow_left₀ (by positivity) (by norm_num) m

end FordDifferencePowerStep

#print axioms FordDifferencePowerStep.power_step
#print axioms FordDifferencePowerStep.coefficient_step
