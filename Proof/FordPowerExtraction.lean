import Mathlib
noncomputable section
namespace FordPowerExtraction

/-- Extract the positive natural root without replacing its exponent by an asymptotic. -/
theorem extract {x N a : ℝ} {m : ℕ} (hN : 0 < N) (hm : 0 < m)
    (h : x^m ≤ N^(-a)) : x ≤ N^(-a/(m : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  apply le_of_pow_le_pow_left₀ (Nat.ne_of_gt hm) (Real.rpow_nonneg hN.le _)
  calc
    x^m ≤ N^(-a) := h
    _ = (N^(-a/(m : ℝ)))^m := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
      congr 1
      field_simp

/-- Normalize a powered bound by the exact positive averaging cardinality. -/
theorem divide_power {x D A : ℝ} {m : ℕ} (hD : 0 < D)
    (h : x^m ≤ D^m*A) : (x/D)^m ≤ A := by
  rw [div_pow]
  exact (div_le_iff₀ (pow_pos hD m)).mpr (by simpa [mul_comm] using h)

end FordPowerExtraction
#print axioms FordPowerExtraction.extract
#print axioms FordPowerExtraction.divide_power
