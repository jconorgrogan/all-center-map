import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Exact decimal inequalities in Khale Appendix B.1

The margins in the penultimate display are only a few parts in one million.
These lemmas certify the irrational scale `(4/3)^(-2/3)` and the logarithmic
rounding used there without floating-point evaluation.
-/

namespace MAPKhaleAppendixBNumericalCore

noncomputable section

def sourceScale : ℝ := Real.rpow (4 / 3 : ℝ) (-2 / 3 : ℝ)

private theorem sourceScale_cube : sourceScale ^ (3 : ℕ) = (9 / 16 : ℝ) := by
  have h : Real.rpow (4 / 3 : ℝ) ((-2 / 3 : ℝ) * 3) =
      (Real.rpow (4 / 3 : ℝ) (-2 / 3 : ℝ)) ^ (3 : ℕ) :=
    Real.rpow_mul_natCast (show (0 : ℝ) ≤ 4 / 3 by norm_num)
      (-2 / 3 : ℝ) 3
  rw [show (-2 / 3 : ℝ) * 3 = -2 by norm_num] at h
  rw [sourceScale, ← h]
  have hn : Real.rpow (4 / 3 : ℝ) (-(2 : ℝ)) =
      (Real.rpow (4 / 3 : ℝ) (2 : ℝ))⁻¹ :=
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4 / 3) 2
  rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, hn]
  norm_num [Real.rpow_natCast]

private theorem sourceScale_nonneg : 0 ≤ sourceScale := by
  exact Real.rpow_nonneg (by norm_num) _

theorem sourceScale_lower : (0.82548 : ℝ) ≤ sourceScale := by
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 0.82548)
    sourceScale_nonneg (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [sourceScale_cube]
  norm_num

theorem sourceScale_upper : sourceScale ≤ (0.8254819 : ℝ) := by
  apply (pow_le_pow_iff_left₀ sourceScale_nonneg
    (by norm_num : (0 : ℝ) ≤ 0.8254819)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  rw [sourceScale_cube]
  norm_num

theorem sourceScale_main_coefficient :
    sourceScale * (33.3275 * ((1 / 3 : ℝ) + (4 / 3 : ℝ) / 2) +
      10.01055 / 3) ≤ 30.26576 := by
  have h := sourceScale_upper
  nlinarith

theorem sourceScale_log3_coefficient :
    (2.7545 : ℝ) ≤ sourceScale * (10.01055 / 3) := by
  have h := sourceScale_lower
  nlinarith

theorem sourceScale_logA_coefficient :
    sourceScale * (33.3275 / 2) ≤ (13.75563 : ℝ) := by
  have h := sourceScale_upper
  nlinarith

private theorem exp_020523_lower :
    (1.2278 : ℝ) < Real.exp (0.20523 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (x := (0.20523 : ℝ)) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem log_3_3375_lt : Real.log (3.3375 : ℝ) < 1.20523 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3.3375)]
  rw [show (1.20523 : ℝ) = 1 + 0.20523 by norm_num, Real.exp_add]
  calc
    (3.3375 : ℝ) < (2.7182818283 : ℝ) * 1.2278 := by norm_num
    _ < Real.exp 1 * Real.exp 0.20523 := by
      gcongr
      · exact Real.exp_one_gt_d9
      · exact exp_020523_lower

theorem sourceScale_constant_coefficient :
    sourceScale * (10.01055 / 3) * Real.log (3.3375 : ℝ) + 0.010122 ≤
      (3.33 : ℝ) := by
  have hk := sourceScale_upper
  have hk0 := sourceScale_nonneg
  have hlog := log_3_3375_lt.le
  have hlog0 : 0 ≤ Real.log (3.3375 : ℝ) := Real.log_nonneg (by norm_num)
  calc
    sourceScale * (10.01055 / 3) * Real.log (3.3375 : ℝ) + 0.010122 ≤
        0.8254819 * (10.01055 / 3) * Real.log (3.3375 : ℝ) + 0.010122 := by
      gcongr
    _ ≤ 0.8254819 * (10.01055 / 3) * 1.20523 + 0.010122 := by
      gcongr
    _ ≤ (3.33 : ℝ) := by norm_num

private theorem rpow_5110_6_lower :
    (296.697 : ℝ) ≤ Real.rpow (5110.6 : ℝ) (2 / 3 : ℝ) := by
  have hx0 : 0 ≤ Real.rpow (5110.6 : ℝ) (2 / 3 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  apply (pow_le_pow_iff_left₀ (by norm_num : (0 : ℝ) ≤ 296.697) hx0
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hc : (Real.rpow (5110.6 : ℝ) (2 / 3 : ℝ)) ^ (3 : ℕ) =
      (5110.6 : ℝ) ^ (2 : ℕ) := by
    have h := Real.rpow_mul_natCast (show (0 : ℝ) ≤ 5110.6 by norm_num)
      (2 / 3 : ℝ) 3
    have h' : Real.rpow (5110.6 : ℝ) ((2 / 3 : ℝ) * 3) =
        (Real.rpow (5110.6 : ℝ) (2 / 3 : ℝ)) ^ (3 : ℕ) := h
    rw [show (2 / 3 : ℝ) * 3 = 2 by norm_num] at h'
    rw [← h']
    norm_num [Real.rpow_natCast]
  rw [hc]
  norm_num

private theorem exp_neg_1937_lt : Real.exp (-1937 : ℝ) < (1 / 100000000 : ℝ) := by
  have hexp24 : (100000000 : ℝ) < Real.exp 27 := by
    rw [show Real.exp (27 : ℝ) = Real.exp 1 ^ (27 : ℕ) by
      simpa using (Real.exp_one_pow 27).symm]
    calc
      (100000000 : ℝ) < (2 : ℝ) ^ (27 : ℕ) := by norm_num
      _ < Real.exp 1 ^ (27 : ℕ) := by
        gcongr
        exact (by norm_num : (2 : ℝ) < 2.7182818283).trans Real.exp_one_gt_d9
  have hexp1937 : (100000000 : ℝ) < Real.exp 1937 :=
    hexp24.trans_le (Real.exp_le_exp.mpr (by norm_num))
  rw [Real.exp_neg]
  simpa only [one_div] using
    (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 100000000) hexp1937)

/-- The very tight startup absorption `(3b0)` in Khale's proof. -/
theorem startup_constant_absorption
    {B L ell : ℝ} (hB : 0 < B) (hEll : 0 < ell)
    (hRatio : 5110.6 / B ≤ L / ell) :
    0.3 * 10.01055 + 33.3275 * Real.exp (-1937) ≤
      0.010122 * Real.rpow B (2 / 3 : ℝ) *
        Real.rpow (L / ell) (2 / 3 : ℝ) := by
  have hratioNonneg : 0 ≤ L / ell := by
    have hleft : 0 < 5110.6 / B := div_pos (by norm_num) hB
    exact hleft.le.trans hRatio
  have hproduct : (5110.6 : ℝ) ≤ B * (L / ell) := by
    have := (div_le_iff₀ hB).mp hRatio
    nlinarith
  have hrpow : Real.rpow (5110.6 : ℝ) (2 / 3 : ℝ) ≤
      Real.rpow (B * (L / ell)) (2 / 3 : ℝ) :=
    Real.rpow_le_rpow (by norm_num) hproduct (by norm_num)
  have hbase : (296.697 : ℝ) ≤
      Real.rpow B (2 / 3 : ℝ) * Real.rpow (L / ell) (2 / 3 : ℝ) := by
    have hmul : Real.rpow (B * (L / ell)) (2 / 3 : ℝ) =
        Real.rpow B (2 / 3 : ℝ) * Real.rpow (L / ell) (2 / 3 : ℝ) :=
      Real.mul_rpow hB.le hratioNonneg
    rw [hmul] at hrpow
    exact rpow_5110_6_lower.trans hrpow
  have hexp := exp_neg_1937_lt.le
  nlinarith

theorem startup_eta_upper :
    Real.rpow (((4 / 3 : ℝ)) / 5110.6) (2 / 3 : ℝ) ≤ 0.06 := by
  have hx0 : 0 ≤ Real.rpow (((4 / 3 : ℝ)) / 5110.6) (2 / 3 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  apply (pow_le_pow_iff_left₀ hx0 (by norm_num : (0 : ℝ) ≤ 0.06)
    (by norm_num : (3 : ℕ) ≠ 0)).mp
  have hc : (Real.rpow (((4 / 3 : ℝ)) / 5110.6) (2 / 3 : ℝ)) ^ (3 : ℕ) =
      (((4 / 3 : ℝ)) / 5110.6) ^ (2 : ℕ) := by
    have h := Real.rpow_mul_natCast
      (show (0 : ℝ) ≤ ((4 / 3 : ℝ)) / 5110.6 by norm_num)
      (2 / 3 : ℝ) 3
    have h' : Real.rpow (((4 / 3 : ℝ)) / 5110.6) ((2 / 3 : ℝ) * 3) =
        (Real.rpow (((4 / 3 : ℝ)) / 5110.6) (2 / 3 : ℝ)) ^ (3 : ℕ) := h
    rw [show (2 / 3 : ℝ) * 3 = 2 by norm_num] at h'
    rw [← h']
    norm_num [Real.rpow_natCast]
  rw [hc]
  norm_num

end
end MAPKhaleAppendixBNumericalCore

#print axioms MAPKhaleAppendixBNumericalCore.sourceScale_main_coefficient
#print axioms MAPKhaleAppendixBNumericalCore.sourceScale_log3_coefficient
#print axioms MAPKhaleAppendixBNumericalCore.sourceScale_logA_coefficient
#print axioms MAPKhaleAppendixBNumericalCore.sourceScale_constant_coefficient
