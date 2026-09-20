import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import KhaleWeakVKApplication

/-!
# Numerical repair for Khale's weak Vinogradov--Korobov corollary

The printed proof of the second part of Khale's Appendix-B corollary uses the
intermediate estimate `... ≤ 59.8`.  With the constants printed in the theorem
(`14.44` and `3.59`) that intermediate estimate is false.  It is also
unnecessary: the resulting coefficient is still strictly smaller than `104`.

This file proves that last assertion directly, with rational Taylor bounds for
the exponential function.  No numerical oracle or floating-point evaluation is
used by the Lean proof.
-/

namespace MAPKhaleWeakVKApplication

noncomputable section

private theorem exp_0345_lt :
    Real.exp (0.345 : ℝ) < 1.4121 := by
  have h := Real.exp_bound' (x := (0.345 : ℝ)) (by norm_num) (by norm_num)
    (n := 7) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem exp_0234_lt :
    Real.exp (0.234 : ℝ) < 1.2637 := by
  have h := Real.exp_bound' (x := (0.234 : ℝ)) (by norm_num) (by norm_num)
    (n := 7) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem exp_0052_lt :
    Real.exp (0.052 : ℝ) < 1.0535 := by
  have h := Real.exp_bound' (x := (0.052 : ℝ)) (by norm_num) (by norm_num)
    (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem exp_005_lt :
    Real.exp (0.05 : ℝ) < 1.052 := by
  have h := Real.exp_bound' (x := (0.05 : ℝ)) (by norm_num) (by norm_num)
    (n := 6) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem one_point_4147_lt_exp_0347 :
    (1.4147 : ℝ) < Real.exp 0.347 := by
  have h := Real.sum_le_exp_of_nonneg (x := (0.347 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

private theorem one_point_4131_lt_exp_0346 :
    (1.4131 : ℝ) < Real.exp 0.346 := by
  have h := Real.sum_le_exp_of_nonneg (x := (0.346 : ℝ)) (by norm_num) 9
  norm_num [Finset.sum_range_succ, Nat.factorial] at h ⊢
  linarith

theorem log_11450_gt :
    (9.345 : ℝ) < Real.log 11450 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 11450)]
  rw [show (9.345 : ℝ) = 9 + 0.345 by norm_num, Real.exp_add,
    show Real.exp (9 : ℝ) = Real.exp 1 ^ 9 by
      simpa using (Real.exp_one_pow 9).symm]
  calc
    Real.exp 1 ^ 9 * Real.exp 0.345 <
        (2.7182818286 : ℝ) ^ 9 * 1.4121 := by
      gcongr
      · exact Real.exp_one_lt_d9
      · exact exp_0345_lt
    _ < 11450 := by norm_num

theorem log_11450_lt :
    Real.log 11450 < (9.346 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 11450)]
  rw [show (9.346 : ℝ) = 9 + 0.346 by norm_num, Real.exp_add,
    show Real.exp (9 : ℝ) = Real.exp 1 ^ 9 by
      simpa using (Real.exp_one_pow 9).symm]
  calc
    (11450 : ℝ) < (2.7182818283 : ℝ) ^ 9 * 1.4131 := by norm_num
    _ < Real.exp 1 ^ 9 * Real.exp 0.346 := by
      gcongr
      · exact Real.exp_one_gt_d9
      · exact one_point_4131_lt_exp_0346

theorem log_log_11450_gt :
    (2.234 : ℝ) < Real.log (Real.log 11450) := by
  rw [Real.lt_log_iff_exp_lt (lt_trans (by norm_num) log_11450_gt)]
  calc
    Real.exp (2.234 : ℝ) = Real.exp 1 ^ 2 * Real.exp 0.234 := by
      rw [show (2.234 : ℝ) = 2 + 0.234 by norm_num, Real.exp_add,
        show Real.exp (2 : ℝ) = Real.exp 1 ^ 2 by
          simpa using (Real.exp_one_pow 2).symm]
    _ < (2.7182818286 : ℝ) ^ 2 * 1.2637 := by
      gcongr
      · exact Real.exp_one_lt_d9
      · exact exp_0234_lt
    _ < 9.345 := by norm_num
    _ < Real.log 11450 := log_11450_gt

theorem log_77_2_lt :
    Real.log (77.2 : ℝ) < 4.347 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 77.2)]
  rw [show (4.347 : ℝ) = 4 + 0.347 by norm_num, Real.exp_add,
    show Real.exp (4 : ℝ) = Real.exp 1 ^ 4 by
      simpa using (Real.exp_one_pow 4).symm]
  calc
    (77.2 : ℝ) < (2.7182818283 : ℝ) ^ 4 * 1.4147 := by norm_num
    _ < Real.exp 1 ^ 4 * Real.exp 0.347 := by
      gcongr
      · exact Real.exp_one_gt_d9
      · exact one_point_4147_lt_exp_0347

theorem one_twentieth_lt_log_log_three :
    (1 / 20 : ℝ) < Real.log (Real.log 3) := by
  have hlogThree : (1.052 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    rw [show (1.052 : ℝ) = 1 + 0.052 by norm_num, Real.exp_add]
    calc
      Real.exp 1 * Real.exp 0.052 <
          (2.7182818286 : ℝ) * 1.0535 := by
        gcongr
        · exact Real.exp_one_lt_d9
        · exact exp_0052_lt
      _ < 3 := by norm_num
  rw [Real.lt_log_iff_exp_lt (Real.log_pos (by linarith))]
  simpa only [show (1 / 20 : ℝ) = 0.05 by norm_num] using
    exp_005_lt.trans hlogThree

theorem rpow_4_45_two_thirds_lt :
    Real.rpow (4.45 : ℝ) (2 / 3 : ℝ) < 2.708 := by
  have hbase : (0 : ℝ) ≤ 4.45 := by norm_num
  have hy : 0 ≤ Real.rpow (4.45 : ℝ) (2 / 3 : ℝ) :=
    Real.rpow_nonneg hbase _
  have hcube : (Real.rpow (4.45 : ℝ) (2 / 3 : ℝ)) ^ 3 = (4.45 : ℝ) ^ 2 := by
    convert (Real.rpow_mul_natCast hbase (2 / 3 : ℝ) 3).symm using 1 <;>
      norm_num [Real.rpow_natCast]
  by_contra h
  have hle : (2.708 : ℝ) ≤ Real.rpow (4.45 : ℝ) (2 / 3 : ℝ) := le_of_not_gt h
  have hcubes : (2.708 : ℝ) ^ 3 ≤
      (Real.rpow (4.45 : ℝ) (2 / 3 : ℝ)) ^ 3 := by
    exact pow_le_pow_left₀ (by norm_num) hle 3
  rw [hcube] at hcubes
  norm_num at hcubes

/-- The direct numerical calculation needed for the second part of Khale's
Appendix-B corollary, using exactly the constants printed in the theorem.

At `T₀ = exp 11450`, the height coefficient obtained from Theorem B.1 with
`A = 76.2`, `B = 4.45` is strictly smaller than `104`.  This theorem deliberately
bypasses the false intermediate bound by `59.8` in the corollary proof. -/
theorem khale_printed_constants_direct_height_coefficient_lt_104 :
    (31.76 +
        (-2.89 * Real.log (Real.log 11450) +
            14.44 * Real.log 77.2 + 3.59) / Real.log 11450) *
      Real.rpow 4.45 (2 / 3 : ℝ) < 104 := by
  let numerator : ℝ :=
    -2.89 * Real.log (Real.log 11450) + 14.44 * Real.log 77.2 + 3.59
  let numeratorUpper : ℝ := -2.89 * 2.234 + 14.44 * 4.347 + 3.59
  let coefficientUpper : ℝ := 31.76 + numeratorUpper / 9.345
  have hn : numerator ≤ numeratorUpper := by
    dsimp [numerator, numeratorUpper]
    nlinarith [log_log_11450_gt, log_77_2_lt]
  have hnumUpper : 0 ≤ numeratorUpper := by
    dsimp [numeratorUpper]
    norm_num
  have hlogpos : 0 < Real.log (11450 : ℝ) :=
    (by norm_num : (0 : ℝ) < 9.345).trans log_11450_gt
  have hfrac₁ : numerator / Real.log 11450 ≤
      numeratorUpper / Real.log 11450 :=
    (div_le_div_iff_of_pos_right hlogpos).2 hn
  have hfrac₂ : numeratorUpper / Real.log 11450 ≤
      numeratorUpper / 9.345 := by
    exact div_le_div_of_nonneg_left hnumUpper (by norm_num) log_11450_gt.le
  have hcoefficient : 31.76 + numerator / Real.log 11450 ≤ coefficientUpper := by
    dsimp [coefficientUpper]
    linarith
  have hpow_nonneg : 0 ≤ Real.rpow (4.45 : ℝ) (2 / 3 : ℝ) :=
    Real.rpow_nonneg (by norm_num) _
  have hcoefficientUpper : 0 < coefficientUpper := by
    dsimp [coefficientUpper, numeratorUpper]
    norm_num
  change (31.76 + numerator / Real.log 11450) *
      Real.rpow 4.45 (2 / 3 : ℝ) < 104
  calc
    (31.76 + numerator / Real.log 11450) * Real.rpow 4.45 (2 / 3 : ℝ) ≤
        coefficientUpper * Real.rpow 4.45 (2 / 3 : ℝ) := by
      exact mul_le_mul_of_nonneg_right hcoefficient hpow_nonneg
    _ < coefficientUpper * 2.708 := by
      exact mul_lt_mul_of_pos_left rpow_4_45_two_thirds_lt hcoefficientUpper
    _ < 104 := by
      dsimp [coefficientUpper, numeratorUpper]
      norm_num

end

end MAPKhaleWeakVKApplication
