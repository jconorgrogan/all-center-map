import FordJ2GeometricAlgebra

noncomputable section
set_option autoImplicit false
namespace FordSmallPowerAbsorption
open FordJ2GeometricAlgebra

/-- Scalar finite-scale patch. The count lift is deliberately a scalar input here. -/
theorem small_power_absorb {s k : ℕ} {P C J0 J1 Delta DeltaNext : ℝ}
    (hP : 1 ≤ P) (hC : 0 ≤ C)
    (hsmall : P ≤ (2 : ℝ) ^ (100 * k ^ 4))
    (hdrop : Delta - DeltaNext ≤ (k : ℝ))
    (hlift : J1 ≤ P ^ (2 * k) * J0)
    (hJ : J0 ≤ C * P ^ lambda (s : ℝ) (k : ℝ) Delta) :
    J1 ≤ (2 : ℝ) ^ (8192 * k ^ 5) * C *
      P ^ lambda ((s + k : ℕ) : ℝ) (k : ℝ) DeltaNext := by
  have hPpos : 0 < P := by linarith
  have hpow : P ^ (Delta - DeltaNext) ≤ (2 : ℝ) ^ (100 * k ^ 5) := by
    calc
      P ^ (Delta - DeltaNext) ≤ P ^ (k : ℝ) := Real.rpow_le_rpow_of_exponent_le hP hdrop
      _ = P ^ k := Real.rpow_natCast P k
      _ ≤ ((2 : ℝ) ^ (100 * k ^ 4)) ^ k := pow_le_pow_left₀ (by linarith) hsmall _
      _ = (2 : ℝ) ^ (100 * k ^ 5) := by rw [← pow_mul]; congr 1 <;> ring
  have hexp : (2 * k : ℕ) + lambda (s : ℝ) (k : ℝ) Delta =
      lambda ((s + k : ℕ) : ℝ) (k : ℝ) DeltaNext + (Delta - DeltaNext) := by
    simp only [lambda, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring
  have hid : P ^ (2 * k) * (C * P ^ lambda (s : ℝ) (k : ℝ) Delta) =
      P ^ (Delta - DeltaNext) * C *
        P ^ lambda ((s + k : ℕ) : ℝ) (k : ℝ) DeltaNext := by
    rw [← Real.rpow_natCast P (2 * k)]
    calc
      _ = C * (P ^ ((2 * k : ℕ) : ℝ) * P ^ lambda (s : ℝ) (k : ℝ) Delta) := by ring
      _ = C * P ^ ((2 * k : ℕ) + lambda (s : ℝ) (k : ℝ) Delta) := by rw [Real.rpow_add hPpos]
      _ = _ := by rw [hexp, Real.rpow_add hPpos]; ring
  have hcost : (2 : ℝ) ^ (100 * k ^ 5) ≤ (2 : ℝ) ^ (8192 * k ^ 5) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  calc
    J1 ≤ P ^ (2 * k) * (C * P ^ lambda (s : ℝ) (k : ℝ) Delta) :=
      hlift.trans (mul_le_mul_of_nonneg_left hJ (by positivity))
    _ = _ := hid
    _ ≤ (2 : ℝ) ^ (8192 * k ^ 5) * C *
        P ^ lambda ((s + k : ℕ) : ℝ) (k : ℝ) DeltaNext := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hpow.trans hcost) hC) (Real.rpow_nonneg hPpos.le _)
end FordSmallPowerAbsorption
#print axioms FordSmallPowerAbsorption.small_power_absorb
