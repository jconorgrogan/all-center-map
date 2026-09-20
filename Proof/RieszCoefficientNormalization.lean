import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Arithmetic-side normalization for the Riesz detector

The replacement weight is compactly supported and has modulus at most one on
the positive arithmetic axis.  Consequently every later Type-I coefficient
bound survives unchanged, with a shorter support.
-/

namespace MAPAppendixA4RieszCoefficients

noncomputable section

/-- The order-`k` compact Riesz weight `(1-x)_+^k`. -/
def rieszWeight (k : ℕ) (x : ℝ) : ℝ :=
  max (1 - x) 0 ^ k

theorem rieszWeight_nonneg (k : ℕ) (x : ℝ) :
    0 ≤ rieszWeight k x := by
  exact pow_nonneg (le_max_right _ _) _

theorem rieszWeight_eq_zero_of_one_le
    (k : ℕ) {x : ℝ} (hx : 1 ≤ x) (hk : 0 < k) :
    rieszWeight k x = 0 := by
  rw [rieszWeight, max_eq_right (by linarith)]
  exact zero_pow hk.ne'

theorem rieszWeight_eq_one_sub_pow
    (k : ℕ) {x : ℝ} (_hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    rieszWeight k x = (1 - x) ^ k := by
  rw [rieszWeight, max_eq_left]
  linarith

theorem rieszWeight_le_one
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    rieszWeight k x ≤ 1 := by
  unfold rieszWeight
  have hbase0 : 0 ≤ max (1 - x) 0 := le_max_right _ _
  have hbase1 : max (1 - x) 0 ≤ 1 := by
    apply max_le
    · linarith
    · norm_num
  simpa using pow_le_one₀ hbase0 hbase1

theorem abs_rieszWeight_le_one
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |rieszWeight k x| ≤ 1 := by
  rw [abs_of_nonneg (rieszWeight_nonneg k x)]
  exact rieszWeight_le_one k hx

/-- Multiplying an arbitrary complex coefficient by the Riesz weight cannot
increase its modulus at any positive arithmetic argument. -/
theorem norm_rieszWeight_mul_le
    (k : ℕ) {x : ℝ} (hx : 0 ≤ x) (a : ℂ) :
    ‖(rieszWeight k x : ℂ) * a‖ ≤ ‖a‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc
    |rieszWeight k x| * ‖a‖ ≤ 1 * ‖a‖ :=
      mul_le_mul_of_nonneg_right (abs_rieszWeight_le_one k hx) (norm_nonneg a)
    _ = ‖a‖ := one_mul _

/-- For positive `Y`, the arithmetic support is literally `n < Y` (apart
from the harmless order-zero kernel, which is never used for inversion). -/
theorem rieszWeight_nat_div_eq_zero_of_Y_le
    (k n : ℕ) {Y : ℝ} (hYpos : 0 < Y) (hY : Y ≤ n) (hk : 0 < k) :
    rieszWeight k ((n : ℝ) / Y) = 0 := by
  apply rieszWeight_eq_zero_of_one_le k _ hk
  apply (le_div_iff₀ hYpos).2
  simpa using hY

/-- The distinguished `n=1` term retains a fixed positive mass once
`Y >= 2k`.  In the intended choice `k = O(log R / log log R)` and
`Y = R^(1/2)`, this condition is eventually automatic. -/
theorem one_half_le_rieszWeight_one_div
    {k : ℕ} (hk : 0 < k) {Y : ℝ} (hY : (2 : ℝ) * k ≤ Y) :
    (1 : ℝ) / 2 ≤ rieszWeight k (1 / Y) := by
  have hYpos : 0 < Y := by
    have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hx0 : 0 ≤ (1 : ℝ) / Y := le_of_lt (div_pos zero_lt_one hYpos)
  have hYtwo : 2 ≤ Y := by
    have hkreal : 1 ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hx1 : (1 : ℝ) / Y ≤ 1 := by
    apply (div_le_iff₀ hYpos).2
    linarith
  rw [rieszWeight_eq_one_sub_pow k hx0 hx1]
  have hbern : 1 + (k : ℝ) * (-(1 / Y)) ≤
      (1 + (-(1 / Y))) ^ k := by
    apply one_add_mul_le_pow
    have : (1 : ℝ) / Y ≤ 1 / 2 := by
      apply (div_le_iff₀ hYpos).2
      linarith
    linarith
  have hratio : (k : ℝ) / Y ≤ 1 / 2 := by
    apply (div_le_iff₀ hYpos).2
    nlinarith
  have hmul : (k : ℝ) * Y⁻¹ = (k : ℝ) / Y := by
    rw [div_eq_mul_inv]
  norm_num [sub_eq_add_neg] at hbern ⊢
  rw [hmul] at hbern
  nlinarith

end

end MAPAppendixA4RieszCoefficients
