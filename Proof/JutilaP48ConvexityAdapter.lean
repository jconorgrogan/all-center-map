import BHPRademacherGaussianThreeLines
import JutilaCollarA5Budget

/-!
# Jutila p.48 convexity bound at the live collar budget

The Gaussian three-lines argument already supplies an explicit primitive
nonprincipal convexity estimate.  This module specializes it to the exact
`1/560` loss reserved by the MAP collar ledger, so the p.48 strip estimate is
no longer a source premise in the selected-system descent.
-/

namespace MAPJutilaP48ConvexityAdapter

open Complex DirichletCharacter
open MAPJutilaCollarA5Budget
open MAPBHPRademacherGaussianThreeLines

noncomputable section

/-- The completely explicit constant in the live p.48 specialization. -/
def p48ConvexityConstant : ℝ :=
  36 * (1 + detectorLogBudget⁻¹) *
    Real.rpow 6 (detectorLogBudget + 1 / 2)

theorem p48ConvexityConstant_pos : 0 < p48ConvexityConstant := by
  have hbudget : 0 < detectorLogBudget := by
    norm_num [detectorLogBudget]
  unfold p48ConvexityConstant
  exact mul_pos
    (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg zero_lt_one
      (inv_nonneg.mpr hbudget.le)))
    (Real.rpow_pos_of_pos (by norm_num) _)

/-- Jutila's primitive nonprincipal strip estimate with exactly the loss
used by the terminal `21/10` exponent ledger. -/
theorem primitive_norm_LFunction_le_p48
    {q : ℕ} [NeZero q] (chi : DirichletCharacter ℂ q)
    (hprim : chi.IsPrimitive) (hchi : chi ≠ 1)
    {sigma u : ℝ} (hsigma0 : 0 ≤ sigma) (hsigma1 : sigma ≤ 1) :
    ‖DirichletCharacter.LFunction chi
        ((sigma : ℂ) + (u : ℂ) * I)‖ ≤
      p48ConvexityConstant *
        Real.rpow ((q : ℝ) * (1 + |u|))
          ((1 / 2) * (1 - sigma) + detectorLogBudget) := by
  simpa only [p48ConvexityConstant] using
    (norm_LFunction_le_jutila_convexity
      (eta := detectorLogBudget)
      (by norm_num [detectorLogBudget])
      (by norm_num [detectorLogBudget])
      chi hprim hchi hsigma0 hsigma1)

end

end MAPJutilaP48ConvexityAdapter

#print axioms MAPJutilaP48ConvexityAdapter.primitive_norm_LFunction_le_p48
