import FordPolynomialPhase

namespace FordUnitPhaseLipschitz

noncomputable section

/-- Unit frequency phase `exp(i x)` with the real input cast into `ℂ`. -/
def unitPhase (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

lemma unitPhase_norm (x : ℝ) : ‖unitPhase x‖ = 1 := by
  simp [unitPhase, Complex.norm_exp]

/-- Exact unit-phase Lipschitz bound, with constant one. -/
theorem unitPhase_sub_norm_le (x y : ℝ) :
    ‖unitPhase x - unitPhase y‖ ≤ |x - y| := by
  have hfactor : unitPhase x - unitPhase y =
      unitPhase y * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    unfold unitPhase
    rw [mul_sub, ← Complex.exp_add]
    congr 1
    push_cast
    ring
    simp
  rw [hfactor, norm_mul, unitPhase_norm]
  simpa [Real.norm_eq_abs] using
    (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

theorem fordPhase_sub_norm_le (x y : ℝ) :
    ‖FordPolynomialPhase.e x - FordPolynomialPhase.e y‖ ≤
      2 * Real.pi * |x - y| := by
  have hex (z : ℝ) : FordPolynomialPhase.e z =
      unitPhase (2 * Real.pi * z) := by
    unfold FordPolynomialPhase.e unitPhase
    congr 1
    push_cast
    ring
  rw [hex x, hex y]
  calc
    _ ≤ |2 * Real.pi * x - 2 * Real.pi * y| :=
      unitPhase_sub_norm_le _ _
    _ = 2 * Real.pi * |x - y| := by
      rw [show 2 * Real.pi * x - 2 * Real.pi * y =
        (2 * Real.pi) * (x - y) by ring, abs_mul,
        abs_of_pos (by positivity)]

#print axioms FordUnitPhaseLipschitz.unitPhase_sub_norm_le
#print axioms FordUnitPhaseLipschitz.fordPhase_sub_norm_le

end
end FordUnitPhaseLipschitz
