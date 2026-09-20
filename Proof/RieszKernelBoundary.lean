import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Factorial.BigOperators

/-!
# A finite-product replacement for the Gamma detector boundary decay

This file certifies the algebraic core of the proposed high-order Riesz
detector.  Its Mellin kernel is a finite rational product.  After the zero of
the translated L-function cancels the factor at `z = 0`, every remaining
factor has imaginary part `t`; this gives the literal boundary estimate
`k! / |t|^k` without Stirling.
-/

namespace MAPAppendixA4RieszKernel

open Complex

noncomputable section

/-- Mellin transform of the order-`k` Riesz weight `(1-x)^k` on `[0,1]`. -/
def rieszMellinKernel (k : ℕ) (z : ℂ) : ℂ :=
  (k.factorial : ℂ) /
    ∏ j ∈ Finset.range (k + 1), (z + (j : ℂ))

/-- The kernel after cancellation of its `z = 0` pole. -/
def regularizedRieszKernel (k : ℕ) (z : ℂ) : ℂ :=
  (k.factorial : ℂ) /
    ∏ j ∈ Finset.range k, (z + ((j + 1 : ℕ) : ℂ))

/-- Mathlib's Beta integral is exactly the Riesz Mellin kernel. -/
theorem betaIntegral_eq_rieszMellinKernel {z : ℂ} (hz : 0 < z.re) (k : ℕ) :
    Complex.betaIntegral z (k + 1) = rieszMellinKernel k z := by
  simpa [rieszMellinKernel] using
    (Complex.betaIntegral_eval_nat_add_one_right hz k)

/-- Split off the unique pole at zero. -/
theorem rieszMellinKernel_eq_div_regularized (k : ℕ) (z : ℂ) :
    rieszMellinKernel k z = regularizedRieszKernel k z / z := by
  rw [rieszMellinKernel, regularizedRieszKernel,
    Finset.prod_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  field_simp

/-- Every shifted factor on a horizontal side dominates the height. -/
theorem abs_height_le_shifted_factor_norm
    (sigma t : ℝ) (j : ℕ) :
    |t| ≤ ‖((sigma : ℂ) + t * I) + ((j + 1 : ℕ) : ℂ)‖ := by
  have h := Complex.abs_im_le_norm
    (((sigma : ℂ) + t * I) + ((j + 1 : ℕ) : ℂ))
  simpa using h

/-- The product denominator on a horizontal side is at least `|t|^k`. -/
theorem abs_height_pow_le_regularized_denominator_norm
    (k : ℕ) (sigma t : ℝ) :
    |t| ^ k ≤
      ‖∏ j ∈ Finset.range k,
        (((sigma : ℂ) + t * I) + ((j + 1 : ℕ) : ℂ))‖ := by
  rw [norm_prod]
  have hprod := Finset.prod_le_prod
    (fun _ _ => abs_nonneg t)
    (fun j (_ : j ∈ Finset.range k) =>
      abs_height_le_shifted_factor_norm sigma t j)
  simpa using hprod

/-- Exact finite-product boundary decay.  This is the load-bearing death test
for replacing Gamma/Stirling by a Riesz kernel. -/
theorem norm_regularizedRieszKernel_le
    (k : ℕ) (sigma t : ℝ) (ht : t ≠ 0) :
    ‖regularizedRieszKernel k ((sigma : ℂ) + t * I)‖ ≤
      (k.factorial : ℝ) / |t| ^ k := by
  rw [regularizedRieszKernel, norm_div, Complex.norm_natCast]
  apply div_le_div_of_nonneg_left
  · exact_mod_cast Nat.zero_le k.factorial
  · exact pow_pos (abs_pos.mpr ht) k
  · exact abs_height_pow_le_regularized_denominator_norm k sigma t

/-- A coarser but convenient form with `k^k` in the numerator. -/
theorem norm_regularizedRieszKernel_le_pow
    (k : ℕ) (sigma t : ℝ) (ht : t ≠ 0) :
    ‖regularizedRieszKernel k ((sigma : ℂ) + t * I)‖ ≤
      (k : ℝ) ^ k / |t| ^ k := by
  calc
    ‖regularizedRieszKernel k ((sigma : ℂ) + t * I)‖
        ≤ (k.factorial : ℝ) / |t| ^ k :=
      norm_regularizedRieszKernel_le k sigma t ht
    _ ≤ (k : ℝ) ^ k / |t| ^ k := by
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast k.factorial_le_pow) (pow_nonneg (abs_nonneg t) k)

/-- On the entire shifted strip `Re z >= -1/2`, the regularized kernel has
only the subexponential-in-`R` loss `2^k`.  This controls the near-zero part
of the shifted vertical line, where the horizontal-height estimate is not
useful. -/
theorem regularized_denominator_lower_bound
    (k : ℕ) (sigma t : ℝ) (hsigma : -(1 : ℝ) / 2 ≤ sigma) :
    (k.factorial : ℝ) / 2 ^ k ≤
      ‖∏ j ∈ Finset.range k,
        (((sigma : ℂ) + t * I) + ((j + 1 : ℕ) : ℂ))‖ := by
  rw [norm_prod]
  calc
    (k.factorial : ℝ) / 2 ^ k =
        ∏ j ∈ Finset.range k, (((j + 1 : ℕ) : ℝ) / 2) := by
      simp_rw [div_eq_mul_inv]
      rw [Finset.prod_mul_distrib]
      rw [← Nat.cast_prod, Finset.prod_range_add_one_eq_factorial]
      simp
    _ ≤ ∏ j ∈ Finset.range k,
        ‖((sigma : ℂ) + t * I) + ((j + 1 : ℕ) : ℂ)‖ := by
      apply Finset.prod_le_prod
      · intro j hj
        positivity
      · intro j hj
        calc
          (((j + 1 : ℕ) : ℝ) / 2) ≤ sigma + (j + 1 : ℕ) := by
            have hj1 : (1 : ℝ) ≤ (j + 1 : ℕ) := by
              exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)
            linarith
          _ ≤ |sigma + (j + 1 : ℕ)| := le_abs_self _
          _ = |(((sigma : ℂ) + t * I) +
              ((j + 1 : ℕ) : ℂ)).re| := by simp
          _ ≤ ‖((sigma : ℂ) + t * I) +
              ((j + 1 : ℕ) : ℂ)‖ := Complex.abs_re_le_norm _

theorem norm_regularizedRieszKernel_le_two_pow
    (k : ℕ) (sigma t : ℝ) (hsigma : -(1 : ℝ) / 2 ≤ sigma) :
    ‖regularizedRieszKernel k ((sigma : ℂ) + t * I)‖ ≤
      (2 : ℝ) ^ k := by
  rw [regularizedRieszKernel, norm_div, Complex.norm_natCast]
  let d : ℝ :=
    ‖∏ j ∈ Finset.range k,
      (((sigma : ℂ) + t * I) + ((j + 1 : ℕ) : ℂ))‖
  have hfac : 0 < (k.factorial : ℝ) := by positivity
  have hpow : 0 < (2 : ℝ) ^ k := by positivity
  have hd : (k.factorial : ℝ) / 2 ^ k ≤ d := by
    simpa [d] using regularized_denominator_lower_bound k sigma t hsigma
  have hdpos : 0 < d := lt_of_lt_of_le (div_pos hfac hpow) hd
  have hmul : (k.factorial : ℝ) ≤ d * 2 ^ k :=
    (div_le_iff₀ hpow).mp hd
  rw [div_le_iff₀ hdpos]
  nlinarith

end

end MAPAppendixA4RieszKernel
