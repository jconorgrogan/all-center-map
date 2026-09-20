import GuthMaynardS3FixedEnergyRecurrence

open scoped Real
noncomputable section
namespace GuthMaynardS3CubicHorizonTail

/-- A larger analytic horizon leaves an explicit absolute-error reserve,
without changing any source variable or hiding exponent losses. -/
theorem cubic_horizon_tail {T epsilon : ℝ} (hT : 1 ≤ T) (heps : epsilon ≤ 1) :
    (64*T^3)^epsilon / (64*T^3)^100 ≤ T^(-297 : ℝ) := by
  have hTp : 0 < T := by linarith
  have hUp : 0 < 64*T^3 := by positivity
  have hT3 : 1 ≤ T^3 := one_le_pow₀ hT
  have hU1 : 1 ≤ 64*T^3 := by linarith
  calc
    (64*T^3)^epsilon / (64*T^3)^100 =
        (64*T^3)^(epsilon-100) := by
      rw [Real.rpow_sub hUp]
      norm_cast
    _ ≤ (64*T^3)^(-99 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hU1 (by linarith)
    _ ≤ (T^3)^(-99 : ℝ) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by nlinarith) (by norm_num)
    _ = T^(-297 : ℝ) := by
      rw [← Real.rpow_natCast T 3, ← Real.rpow_mul hTp.le]
      norm_num

/-- Safe polynomial cap for the variable portion of the source block error.
`L=k+7≤8*2^k` and `K=2^k≤T²` supply the two last geometric hypotheses. -/
theorem block_error_prefactor_le
    {T rho n K R L : ℝ} (hT : 1 ≤ T)
    (hr0 : 0 ≤ rho) (hr : rho ≤ T) (hn0 : 0 ≤ n) (hn : n ≤ T)
    (hK0 : 0 ≤ K) (hK : K ≤ T^2) (hR0 : 0 ≤ R) (hR : R ≤ 2*T)
    (hL0 : 0 ≤ L) (hL : L ≤ 8*K) :
    rho^2*n^4*K^2*R*L^2 ≤ 128*T^15 := by
  have hL' : L ≤ 8*T^2 := hL.trans (mul_le_mul_of_nonneg_left hK (by norm_num))
  calc
    rho^2*n^4*K^2*R*L^2 ≤ T^2*T^4*(T^2)^2*(2*T)*(8*T^2)^2 := by
      gcongr
    _ = 128*T^15 := by ring

theorem polynomial_prefactor_cubic_tail
    {T epsilon P : ℝ} (hT : 1 ≤ T) (heps : epsilon ≤ 1)
    (hP0 : 0 ≤ P) (hP : P ≤ 128*T^15) :
    P*((64*T^3)^epsilon/(64*T^3)^100) ≤ 128*T^(-282 : ℝ) := by
  have hTp : 0 < T := by linarith
  calc
    P*((64*T^3)^epsilon/(64*T^3)^100) ≤
        (128*T^15)*T^(-297 : ℝ) :=
      mul_le_mul hP (cubic_horizon_tail hT heps) (by positivity) (by positivity)
    _ = 128*T^(-282 : ℝ) := by
      rw [mul_assoc, ← Real.rpow_natCast T 15, ← Real.rpow_add hTp]
      norm_num

theorem dyadic_bin_factor_le (k : ℕ) : (k : ℝ)+7 ≤ 8*(2 : ℝ)^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
      push_cast
      rw [pow_succ]
      have hh : (1 : ℝ) ≤ 2^k := one_le_pow₀ (by norm_num)
      nlinarith

/-- The square root and the original selection logarithm still leave the
source's desired T^-100 error after the cubic-horizon reserve. -/
theorem log_weighted_sqrt_tail {T C : ℝ} (hT : 1 ≤ T) (hC : 0 ≤ C) :
    (1+Real.log T)^2 * Real.sqrt (C*T^(-282 : ℝ)) ≤
      Real.sqrt C * T^(-100 : ℝ) := by
  have hTp : 0 < T := by linarith
  have hlog0 := Real.log_nonneg hT
  have hlog := Real.log_le_sub_one_of_pos hTp
  have hL : (1+Real.log T)^2 ≤ T^2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  have hs : Real.sqrt (C*T^(-282 : ℝ)) = Real.sqrt C * T^(-141 : ℝ) := by
    rw [Real.sqrt_mul hC, Real.sqrt_eq_rpow (T^(-282 : ℝ)), ← Real.rpow_mul hTp.le]
    norm_num
  rw [hs]
  calc
    (1+Real.log T)^2*(Real.sqrt C*T^(-141 : ℝ)) ≤
        T^2*(Real.sqrt C*T^(-141 : ℝ)) :=
      mul_le_mul_of_nonneg_right hL (by positivity)
    _ = Real.sqrt C*T^(-139 : ℝ) := by
      rw [show T^2*(Real.sqrt C*T^(-141 : ℝ)) =
        Real.sqrt C*(T^2*T^(-141 : ℝ)) by ring]
      rw [← Real.rpow_natCast T 2, ← Real.rpow_add hTp]
      norm_num
    _ ≤ Real.sqrt C*T^(-100 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hT (by norm_num)) (Real.sqrt_nonneg _)

end GuthMaynardS3CubicHorizonTail
#print axioms GuthMaynardS3CubicHorizonTail.cubic_horizon_tail
#print axioms GuthMaynardS3CubicHorizonTail.block_error_prefactor_le
#print axioms GuthMaynardS3CubicHorizonTail.polynomial_prefactor_cubic_tail

#print axioms GuthMaynardS3CubicHorizonTail.dyadic_bin_factor_le
#print axioms GuthMaynardS3CubicHorizonTail.log_weighted_sqrt_tail
