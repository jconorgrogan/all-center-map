import BudgetedFixedCharacterPoweredLargeValueBridge

/-!
# Collar-aware Type-I/II exponent assembly

This file proves the purely algebraic branch estimate needed after the
selected powered block has been placed in a logarithmically enlarged GM
window.  It contains no source proposition or analytic assumption.
-/

namespace CGLProofDAG

open AppendixTypeIPower

noncomputable section

/-- The exact GM/mean-value branch inequalities tolerate an upper length
collar `3*rho`.  The first GM term spends at most `6*rho`; the middle term
spends at most `3*rho`; the decreasing third GM and mean-value terms spend no
collar. -/
theorem powered_length_branch_exponents_with_collar
    {σ mu rho : ℝ}
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hrho : 0 ≤ rho)
    (hmuLow : poweredLengthLower σ ≤ mu)
    (hmuHigh : mu ≤ poweredLengthUpper σ + 3 * rho) :
    2 * mu * (1 - σ) ≤ gmExponent σ + 6 * rho ∧
    1 + (12 / 5 - 4 * σ) * mu ≤ gmExponent σ ∧
    (mu ≤ gmSwitchExponent σ + 3 * rho →
      (18 / 5 - 4 * σ) * mu ≤ gmExponent σ + 3 * rho) ∧
    (gmSwitchExponent σ ≤ mu →
      1 + (1 - 2 * σ) * mu ≤ gmExponent σ) := by
  have hone : 0 ≤ 1 - σ := by linarith
  have hone_le : 1 - σ ≤ 1 := by linarith
  have hfirst := first_term_at_powered_upper hσlow
  have hthird := third_term_at_powered_lower hσlow
  have hmiddle := middle_term_at_switch hσlow hσhigh
  have hmean := mean_value_switch_le_gm hσlow hσhigh
  constructor
  · calc
      2 * mu * (1 - σ) ≤
          2 * (poweredLengthUpper σ + 3 * rho) * (1 - σ) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hmuHigh (by norm_num)) hone
      _ = gmExponent σ + 6 * rho * (1 - σ) := by rw [← hfirst]; ring
      _ ≤ gmExponent σ + 6 * rho := by
        have hscale : 6 * rho * (1 - σ) ≤ 6 * rho * 1 :=
          mul_le_mul_of_nonneg_left hone_le (mul_nonneg (by norm_num) hrho)
        nlinarith
  constructor
  · have hc : 12 / 5 - 4 * σ ≤ 0 := by linarith
    calc
      1 + (12 / 5 - 4 * σ) * mu ≤
          1 + (12 / 5 - 4 * σ) * poweredLengthLower σ := by
        linarith [mul_le_mul_of_nonpos_left hmuLow hc]
      _ = gmExponent σ := hthird
  constructor
  · intro hmuSwitch
    have hc0 : 0 ≤ 18 / 5 - 4 * σ := by linarith
    have hc1 : 18 / 5 - 4 * σ ≤ 1 := by linarith
    calc
      (18 / 5 - 4 * σ) * mu ≤
          (18 / 5 - 4 * σ) * (gmSwitchExponent σ + 3 * rho) :=
        mul_le_mul_of_nonneg_left hmuSwitch hc0
      _ = gmExponent σ + (18 / 5 - 4 * σ) * (3 * rho) := by
        rw [← hmiddle]
        ring
      _ ≤ gmExponent σ + 3 * rho := by
        have hscale : (18 / 5 - 4 * σ) * (3 * rho) ≤ 1 * (3 * rho) :=
          mul_le_mul_of_nonneg_right hc1 (mul_nonneg (by norm_num) hrho)
        nlinarith
  · intro hswitchMu
    have hc : 1 - 2 * σ ≤ 0 := by linarith
    calc
      1 + (1 - 2 * σ) * mu ≤
          1 + (1 - 2 * σ) * gmSwitchExponent σ := by
        linarith [mul_le_mul_of_nonpos_left hswitchMu hc]
      _ ≤ gmExponent σ := hmean

/-- Rpow form of the collar-aware branch assembly. -/
theorem powered_length_branch_rpow_bounds_with_collar
    {T σ mu rho : ℝ} (hT : 1 ≤ T)
    (hσlow : 7 / 10 ≤ σ) (hσhigh : σ ≤ 4 / 5)
    (hrho : 0 ≤ rho)
    (hmuLow : poweredLengthLower σ ≤ mu)
    (hmuHigh : mu ≤ poweredLengthUpper σ + 3 * rho) :
    Real.rpow T (2 * mu * (1 - σ)) ≤
        Real.rpow T (gmExponent σ + 6 * rho) ∧
    Real.rpow T (1 + (12 / 5 - 4 * σ) * mu) ≤
        Real.rpow T (gmExponent σ) ∧
    (mu ≤ gmSwitchExponent σ + 3 * rho →
      Real.rpow T ((18 / 5 - 4 * σ) * mu) ≤
        Real.rpow T (gmExponent σ + 3 * rho)) ∧
    (gmSwitchExponent σ ≤ mu →
      Real.rpow T (1 + (1 - 2 * σ) * mu) ≤
        Real.rpow T (gmExponent σ)) := by
  obtain ⟨h1, h3, h2, hmv⟩ :=
    powered_length_branch_exponents_with_collar
      hσlow hσhigh hrho hmuLow hmuHigh
  exact ⟨Real.rpow_le_rpow_of_exponent_le hT h1,
    Real.rpow_le_rpow_of_exponent_le hT h3,
    fun h => Real.rpow_le_rpow_of_exponent_le hT (h2 h),
    fun h => Real.rpow_le_rpow_of_exponent_le hT (hmv h)⟩

end
end CGLProofDAG

#print axioms CGLProofDAG.powered_length_branch_exponents_with_collar
#print axioms CGLProofDAG.powered_length_branch_rpow_bounds_with_collar
