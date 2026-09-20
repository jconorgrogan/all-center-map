import PrincipalZetaFixedStrip
import Mathlib.NumberTheory.LSeries.Nonvanishing

namespace MAPPrincipalZetaFixedStrip

/-- Zeros of the pole-removed principal zeta function are strictly left of one.
This includes the zero-gap case; no positive gap or ordinate bound is needed. -/
theorem principalRegularized_zero_re_lt_one {rho : ℂ}
    (hzero : principalRegularized rho = 0) : rho.re < 1 := by
  have hrho : rho ≠ 1 := by
    intro heq
    subst rho
    exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero 1 hzero
  by_contra hnot
  have hzeta := riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)
  rw [principalRegularized_apply_of_ne_one hrho] at hzero
  exact (mul_ne_zero (sub_ne_zero.mpr hrho) hzeta) hzero

end MAPPrincipalZetaFixedStrip

#print axioms MAPPrincipalZetaFixedStrip.principalRegularized_zero_re_lt_one
