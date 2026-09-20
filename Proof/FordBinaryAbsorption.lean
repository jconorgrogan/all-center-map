import Mathlib
noncomputable section
namespace FordBinaryAbsorption

/-- Explicit sufficient logarithmic scale; no asymptotic constant is hidden. -/
theorem binary_cost_le {N : ℝ} {k : ℕ} (hN : 0 < N)
    (hlarge : 1000000000000 * (k : ℝ)^4 ≤ Real.log N) :
    (2 : ℝ)^((2^26)*k^6) ≤ N^((k : ℝ)^2/200) := by
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos hN]
  apply Real.exp_le_exp.mpr
  push_cast
  have hl := mul_le_mul_of_nonneg_right hlarge (by positivity : 0 ≤ (k : ℝ)^2/200)
  have hc := mul_le_mul_of_nonneg_right hlog2
    (by positivity : 0 ≤ (2 : ℝ)^26*(k : ℝ)^6)
  have hp : (1000000000000 : ℝ)*(k : ℝ)^4*((k : ℝ)^2/200) =
      5000000000*(k : ℝ)^6 := by ring
  rw [hp] at hl
  norm_num at hc ⊢
  nlinarith [pow_nonneg (by positivity : (0 : ℝ) ≤ k) 6]

/-- Spend half of the negative source exponent to absorb a bounded prefactor. -/
theorem absorb {C N : ℝ} {k : ℕ} (hN : 0 < N)
    (hlarge : 1000000000000 * (k : ℝ)^4 ≤ Real.log N)
    (hC : C ≤ (2 : ℝ)^((2^26)*k^6)) :
    C*N^(-(k : ℝ)^2/100) ≤ N^(-(k : ℝ)^2/200) := by
  calc
    _ ≤ N^((k : ℝ)^2/200)*N^(-(k : ℝ)^2/100) :=
      mul_le_mul_of_nonneg_right (hC.trans (binary_cost_le hN hlarge)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hN]; congr 1 <;> ring

end FordBinaryAbsorption
#print axioms FordBinaryAbsorption.binary_cost_le
#print axioms FordBinaryAbsorption.absorb
