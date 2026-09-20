import FordPowerFibers

open scoped BigOperators
noncomputable section

namespace FordPolynomialPhase

def e (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)

/-- Exact finite expansion of a polynomial exponential sum into power fibers. -/
theorem polynomial_phase_pow (r k M : ℕ) (gamma : Fin k → ℝ) (b : ℝ) :
    (∑ a : Fin M,
      e (∑ j : Fin k,
        gamma j * b ^ (j.val + 1) * (((a.val + 1 : ℕ) : ℝ) ^ (j.val + 1)))) ^ r =
      ∑ x : Fin r → Fin M,
        e (∑ j : Fin k,
          gamma j * b ^ (j.val + 1) *
            (FordPowerFibers.powerMap r k M x j : ℝ)) := by
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro x hx
  rw [show (∏ i : Fin r,
      e (∑ j : Fin k,
        gamma j * b ^ (j.val + 1) * (((x i).val + 1 : ℕ) : ℝ) ^ (j.val + 1))) =
      Complex.exp (∑ i : Fin r, ∑ j : Fin k,
        ((2 * Real.pi *
          (gamma j * b ^ (j.val + 1) * (((x i).val + 1 : ℕ) : ℝ) ^ (j.val + 1)) : ℝ) : ℂ) * Complex.I) by
    simp only [e]
    rw [← Complex.exp_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    push_cast
    rw [Finset.mul_sum, Finset.sum_mul]
    ]
  simp only [e]
  congr 1
  push_cast
  rw [Finset.sum_comm]
  rw [Finset.mul_sum]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  unfold FordPowerFibers.powerMap
  push_cast
  rw [← Finset.sum_mul]
  rw [Finset.mul_sum, Finset.mul_sum]

end FordPolynomialPhase

#print axioms FordPolynomialPhase.polynomial_phase_pow
