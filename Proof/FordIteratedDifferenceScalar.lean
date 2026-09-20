import FordDifferencePowerStep

noncomputable section
namespace FordIteratedDifferenceScalar

/-- Scalar iteration only: the recurrence must be supplied by actual differencing. -/
theorem iterated_bound (r : ℕ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (x : ℕ → ℝ) (hx : ∀ j, 0 ≤ x j)
    (hstep : ∀ j < r, x j ^ 2 ≤ a + 4 * x (j + 1)) :
    x 0 ^ (2 ^ r) ≤ 16 ^ (2 ^ r) * (a + x r) := by
  induction r generalizing x with
  | zero =>
      simp only [pow_zero, pow_one]
      nlinarith [hx 0]
  | succ r ih =>
      let m : ℕ := 2 ^ r
      have hm : 1 ≤ m := Nat.one_le_pow r 2 (by omega)
      have hi := ih (fun j => x (j + 1)) (fun j => hx (j + 1))
        (fun j hj => hstep (j + 1) (by omega))
      have hp := pow_le_pow_left₀ (sq_nonneg (x 0)) (hstep 0 (by omega)) m
      have hs := FordDifferencePowerStep.power_step hm ha0 ha1 (hx 1)
      have hc := FordDifferencePowerStep.coefficient_step hm
      have hk : (1 : ℝ) ≤ 16 ^ m := one_le_pow₀ (by norm_num)
      have hz : 0 ≤ a + x (r + 1) := add_nonneg ha0 (hx _)
      have haK : a ≤ 16 ^ m * (a + x (r + 1)) := by
        have hh := mul_le_mul_of_nonneg_right hk hz
        nlinarith [hx (r + 1)]
      have hexp : 2 ^ (r + 1) = 2 * m := by dsimp [m]; omega
      calc
        x 0 ^ (2 ^ (r + 1)) = (x 0 ^ 2) ^ m := by rw [hexp, pow_mul]
        _ ≤ (a + 4 * x 1) ^ m := hp
        _ ≤ 5 ^ m * (a + x 1 ^ m) := hs
        _ ≤ 5 ^ m * (2 * (16 ^ m * (a + x (r + 1)))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          change x 1 ^ m ≤ 16 ^ m * (a + x (r + 1)) at hi
          linarith
        _ = (2 * 5 ^ m) * 16 ^ m * (a + x (r + 1)) := by ring
        _ ≤ 16 ^ m * 16 ^ m * (a + x (r + 1)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hc (by positivity)) hz
        _ = 16 ^ (2 ^ (r + 1)) * (a + x (r + 1)) := by
          rw [← pow_add, hexp, two_mul]

end FordIteratedDifferenceScalar
#print axioms FordIteratedDifferenceScalar.iterated_bound
