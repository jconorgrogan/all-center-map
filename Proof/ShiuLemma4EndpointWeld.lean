import ShiuLemma4TauTail

/-!
# Final exponent weld for Shiu's Lemma 4

This file contains only the exact algebra which combines the certified
`-1/8` Rankin saving with a `+1/40` Euler-distortion allowance.  Their sum is
the printed `-1/10` exponent.
-/

namespace ShiuLemma4EndpointWeld

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuLemma4TauTail
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

def omittedPrimeInvSum (y modulus : ℕ) : ℝ :=
  ∑ p ∈ (y + 1).primesBelow,
    if p ∣ modulus then 0 else (p : ℝ)⁻¹

/-- Exact endpoint algebra.  The hypothesis is solely the local finite
Euler-product distortion which the companion Chebyshev module attacks. -/
theorem tauSquareSmoothTail_le_oneTenth_of_eulerDistortion
    (k z y modulus : ℕ) (r C : ℝ)
    (hk : 1 ≤ k) (hz : 3 ≤ z) (hr : 1 ≤ r)
    (hrange : r * Real.log r ≤ Real.log (z : ℝ))
    (hC : 0 ≤ C)
    (hdist :
      (∏ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 1
            else 1 / (1 - (p : ℝ) ^ (-shiuDelta z r)) ^ (k * k))) ≤
        C * Real.exp
          ((k * k : ℕ) * omittedPrimeInvSum y modulus +
            (1 / 40 : ℝ) * r * Real.log r)) :
    tauSquareSmoothTail k z y modulus ≤
      C * Real.exp
        ((k * k : ℕ) * omittedPrimeInvSum y modulus -
          (1 / 10 : ℝ) * r * Real.log r) := by
  have hbase := tauSquareSmoothTail_le_shiuEulerProduct
    k z y modulus r hk hz hr hrange
  have hexpnonneg :
      0 ≤ Real.exp (-(1 / 8 : ℝ) * r * Real.log r) :=
    (Real.exp_pos _).le
  calc
    tauSquareSmoothTail k z y modulus ≤
        Real.exp (-(1 / 8 : ℝ) * r * Real.log r) *
          ∏ p ∈ (y + 1).primesBelow,
            (if p ∣ modulus then 1
              else 1 / (1 - (p : ℝ) ^ (-shiuDelta z r)) ^ (k * k)) := hbase
    _ ≤ Real.exp (-(1 / 8 : ℝ) * r * Real.log r) *
        (C * Real.exp
          ((k * k : ℕ) * omittedPrimeInvSum y modulus +
            (1 / 40 : ℝ) * r * Real.log r)) :=
      mul_le_mul_of_nonneg_left hdist hexpnonneg
    _ = C * Real.exp
        ((k * k : ℕ) * omittedPrimeInvSum y modulus -
          (1 / 10 : ℝ) * r * Real.log r) := by
      calc
        Real.exp (-(1 / 8 : ℝ) * r * Real.log r) *
            (C * Real.exp
              ((k * k : ℕ) * omittedPrimeInvSum y modulus +
                (1 / 40 : ℝ) * r * Real.log r)) =
          C * (Real.exp (-(1 / 8 : ℝ) * r * Real.log r) *
            Real.exp
              ((k * k : ℕ) * omittedPrimeInvSum y modulus +
                (1 / 40 : ℝ) * r * Real.log r)) := by ring
        _ = C * Real.exp
            (-(1 / 8 : ℝ) * r * Real.log r +
              ((k * k : ℕ) * omittedPrimeInvSum y modulus +
                (1 / 40 : ℝ) * r * Real.log r)) := by
          congr 1
          exact (Real.exp_add
            (-(1 / 8 : ℝ) * r * Real.log r)
            ((k * k : ℕ) * omittedPrimeInvSum y modulus +
              (1 / 40 : ℝ) * r * Real.log r)).symm
        _ = C * Real.exp
            ((k * k : ℕ) * omittedPrimeInvSum y modulus -
              (1 / 10 : ℝ) * r * Real.log r) := by
          congr 2
          ring

end
end ShiuLemma4EndpointWeld

#print axioms ShiuLemma4EndpointWeld.tauSquareSmoothTail_le_oneTenth_of_eulerDistortion
