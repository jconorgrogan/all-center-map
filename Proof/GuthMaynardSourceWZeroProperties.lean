import GuthMaynardJutilaReflection2941

/-!
# Exact properties of Jutila's four-endpoint smooth cutoff

The source cutoff is built from `Theta(x)=exp(-1/x)` on `x>0` and
`Upsilon(x)=Theta(x)/(Theta(x)+Theta(1-x))`.  This file proves the only
properties needed by the initial smoothing reduction: nonnegativity and the
identity `w₀=1` on the hard dyadic core `[1,2]`.
-/

namespace GuthMaynardSourceWZeroProperties

open GuthMaynardJutilaReflection2941

noncomputable section

theorem sourceTheta_nonneg (x : ℝ) : 0 ≤ sourceTheta x := by
  unfold sourceTheta
  split_ifs
  · positivity
  · exact le_rfl

theorem sourceTheta_pos_of_pos {x : ℝ} (hx : 0 < x) :
    0 < sourceTheta x := by
  simpa [sourceTheta, hx] using Real.exp_pos (-x⁻¹)

theorem sourceTheta_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    sourceTheta x = 0 := by
  simp [sourceTheta, not_lt.mpr hx]

theorem sourceUpsilon_nonneg (x : ℝ) : 0 ≤ sourceUpsilon x := by
  unfold sourceUpsilon
  exact div_nonneg (sourceTheta_nonneg x)
    (add_nonneg (sourceTheta_nonneg x) (sourceTheta_nonneg (1 - x)))

theorem sourceUpsilon_le_one (x : ℝ) : sourceUpsilon x ≤ 1 := by
  unfold sourceUpsilon
  have hd0 : 0 ≤ sourceTheta x + sourceTheta (1 - x) :=
    add_nonneg (sourceTheta_nonneg x) (sourceTheta_nonneg (1 - x))
  by_cases hd : sourceTheta x + sourceTheta (1 - x) = 0
  · rw [hd]
    simp
  · have hdpos : 0 < sourceTheta x + sourceTheta (1 - x) :=
      lt_of_le_of_ne hd0 (Ne.symm hd)
    exact (div_le_one hdpos).2 (by
      exact le_add_of_nonneg_right (sourceTheta_nonneg (1 - x)))

theorem sourceUpsilon_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    sourceUpsilon x = 1 := by
  have htheta : sourceTheta x ≠ 0 :=
    (sourceTheta_pos_of_pos (lt_of_lt_of_le zero_lt_one hx)).ne'
  have hother : sourceTheta (1 - x) = 0 :=
    sourceTheta_eq_zero_of_nonpos (by linarith)
  unfold sourceUpsilon
  rw [hother, add_zero, div_self htheta]

theorem sourceWZero_nonneg (alpha a b c d : ℝ) :
    0 ≤ sourceWZero alpha a b c d := by
  unfold sourceWZero
  exact mul_nonneg (sourceUpsilon_nonneg _) (sourceUpsilon_nonneg _)

theorem sourceWZero_le_one (alpha a b c d : ℝ) :
    sourceWZero alpha a b c d ≤ 1 := by
  unfold sourceWZero
  have h₁ := sourceUpsilon_nonneg ((alpha - a) / (b - a))
  have h₂ := sourceUpsilon_nonneg ((d - alpha) / (d - c))
  have h₁' := sourceUpsilon_le_one ((alpha - a) / (b - a))
  have h₂' := sourceUpsilon_le_one ((d - alpha) / (d - c))
  nlinarith

/-- The literal source cutoff `(1/2,1,2,5/2)` equals one on `[1,2]`. -/
theorem sourceWZero_eq_one_on_core
    {alpha : ℝ} (hlow : 1 ≤ alpha) (hhigh : alpha ≤ 2) :
    sourceWZero alpha (1 / 2) 1 2 (5 / 2) = 1 := by
  unfold sourceWZero
  have hleft : 1 ≤ (alpha - 1 / 2) / (1 - 1 / 2) := by
    norm_num
    linarith
  have hright : 1 ≤ ((5 / 2 : ℝ) - alpha) / ((5 / 2 : ℝ) - 2) := by
    norm_num
    linarith
  rw [sourceUpsilon_eq_one_of_one_le hleft,
    sourceUpsilon_eq_one_of_one_le hright, one_mul]

end

end GuthMaynardSourceWZeroProperties

#print axioms GuthMaynardSourceWZeroProperties.sourceUpsilon_eq_one_of_one_le
#print axioms GuthMaynardSourceWZeroProperties.sourceWZero_eq_one_on_core
