import APHeightMonotonicity

/-!
# Deterministic reserve padding for the selected AP zero height

Equation (2.8) at a common height in `(H,H+1)` produces weighted mass through
`H+1`.  Spending half of the positive reserve enlarges the prescribed height
by a power of `X`, which absorbs this additive unit for sufficiently large
`X`.  This file contains that deterministic comparison only.
-/

namespace MAPAPZeroHeightPadding

open MAPFixedScaleAPZeroRoute MAPAPHeightMonotonicity

noncomputable section

/-- Half the positive reserve absorbs the selected-height additive unit. -/
theorem apZeroHeight_add_one_le_halfReserve
    {reserve X : ℝ} (hreserve : 0 < reserve)
    (hreserveCap : reserve ≤ 1 / 10)
    (hX : Real.exp (4 * Real.log 2 / reserve) ≤ X) :
    apZeroHeight reserve X + 1 ≤ apZeroHeight (reserve / 2) X := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hthresholdPos : 0 < 4 * Real.log 2 / reserve := by positivity
  have hXone : 1 ≤ X := by
    have hexpone : 1 < Real.exp (4 * Real.log 2 / reserve) :=
      Real.one_lt_exp_iff.mpr hthresholdPos
    exact hexpone.le.trans hX
  have hXpos : 0 < X := zero_lt_one.trans_le hXone
  have hlogLower : 4 * Real.log 2 / reserve ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact hX
  have hscaled : Real.log 2 ≤ Real.log X * (reserve / 4) := by
    have hmul := mul_le_mul_of_nonneg_right hlogLower
      (show 0 ≤ reserve / 4 by positivity)
    calc
      Real.log 2 = (4 * Real.log 2 / reserve) * (reserve / 4) := by
        field_simp
      _ ≤ Real.log X * (reserve / 4) := hmul
  have hpowerTwo : 2 ≤ Real.rpow X (reserve / 4) := by
    change 2 ≤ X ^ (reserve / 4)
    rw [Real.rpow_def_of_pos hXpos]
    have hexp := Real.exp_le_exp.mpr hscaled
    simpa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using hexp
  have hexpNonneg : 0 ≤ 13 / 15 - reserve / 2 := by
    linarith
  have hHone : 1 ≤ Real.rpow X (13 / 15 - reserve / 2) :=
    Real.one_le_rpow hXone hexpNonneg
  have hHnonneg : 0 ≤ Real.rpow X (13 / 15 - reserve / 2) :=
    Real.rpow_nonneg hXpos.le _
  unfold apZeroHeight
  calc
    Real.rpow X (13 / 15 - reserve / 2) + 1 ≤
        2 * Real.rpow X (13 / 15 - reserve / 2) := by linarith
    _ ≤ Real.rpow X (13 / 15 - reserve / 2) *
        Real.rpow X (reserve / 4) := by
      simpa [mul_comm] using
        (mul_le_mul_of_nonneg_left hpowerTwo hHnonneg)
    _ = Real.rpow X ((13 / 15 - reserve / 2) + reserve / 4) :=
      (Real.rpow_add hXpos _ _).symm
    _ = Real.rpow X (13 / 15 - (reserve / 2) / 2) := by
      congr 1
      ring

/-- Positive weighted zero mass at `H+1` is dominated by the half-reserve
height, so equation (2.7) can be invoked without strengthening its interface. -/
theorem apWeightedZeroMass_add_one_le_halfReserve
    (Q : ℕ) {reserve X : ℝ} (hreserve : 0 < reserve)
    (hreserveCap : reserve ≤ 1 / 10)
    (hX : Real.exp (4 * Real.log 2 / reserve) ≤ X) :
    apWeightedZeroMass Q X (apZeroHeight reserve X + 1) ≤
      apWeightedZeroMass Q X (apZeroHeight (reserve / 2) X) := by
  exact apWeightedZeroMass_mono_height Q
    (zero_le_one.trans (show 1 ≤ X by
      have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have ht : 0 < 4 * Real.log 2 / reserve := by positivity
      exact (Real.one_lt_exp_iff.mpr ht).le.trans hX))
    (apZeroHeight_add_one_le_halfReserve hreserve hreserveCap hX)

end
end MAPAPZeroHeightPadding

#print axioms MAPAPZeroHeightPadding.apZeroHeight_add_one_le_halfReserve
#print axioms MAPAPZeroHeightPadding.apWeightedZeroMass_add_one_le_halfReserve
