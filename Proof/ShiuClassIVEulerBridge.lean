import ShiuEndToEndScaffold

/-!
# Class-IV omitted-prime exponential bridge

This file closes the arithmetic Euler-factor comparison used after the
class-IV Lemma-4 estimate.  It contains no new analytic premise: the exponential
of the omitted reciprocal-prime sum is dominated termwise by the corresponding
finite Euler product, after which the certified modulus/totient cancellation
and Mertens endpoint apply.
-/

namespace ShiuClassIVEulerBridge

open scoped BigOperators

noncomputable section

/-- Termwise Euler-factor domination of the omitted reciprocal-prime
exponential. -/
theorem exp_omittedPrimeInvSum_le_omittedEulerProduct
    (k y modulus : ℕ) :
    Real.exp
        ((k * k : ℕ) *
          ShiuLemma4EndpointWeld.omittedPrimeInvSum y modulus) ≤
      ∏ p ∈ (y + 1).primesBelow,
        (if p ∣ modulus then 1
          else ShiuEndToEnd.eulerInvFactor p ^ (k * k)) := by
  rw [ShiuLemma4EndpointWeld.omittedPrimeInvSum, Finset.mul_sum,
    Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro p hp
    exact (Real.exp_pos _).le
  · intro p hp
    by_cases hpd : p ∣ modulus
    · simp [hpd]
    · simp only [hpd, if_false]
      rw [Real.exp_nat_mul]
      apply pow_le_pow_left₀ (Real.exp_pos _).le
      have hpprime : p.Prime := Nat.prime_of_mem_primesBelow hp
      have hpone : (1 : ℝ) < p := by exact_mod_cast hpprime.one_lt
      have hu1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpone
      simpa [ShiuEndToEnd.eulerInvFactor, one_div] using
        (MAPMertensAnalyticLeaf.exp_le_inv_one_sub hu1)

/-- The exact class-IV arithmetic bridge.  The sieve factor `q/phi(q)` and the
exponential of the reciprocal primes omitted at divisors of `q` together cost
only the existing `log(x)^(k^2)` endpoint. -/
theorem modulusTotient_mul_exp_omittedPrimeInvSum_le_logPow
    (k x y modulus : ℕ) (hk : 1 ≤ k) (hyx : y ≤ x)
    (hx : 3 ≤ x) (hmodulus : 0 < modulus) (hmodx : modulus ≤ x) :
    ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        Real.exp
          ((k * k : ℕ) *
            ShiuLemma4EndpointWeld.omittedPrimeInvSum y modulus) ≤
      Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k * k) := by
  have hexp := exp_omittedPrimeInvSum_le_omittedEulerProduct k y modulus
  have hratio : 0 ≤ (modulus : ℝ) / (Nat.totient modulus : ℝ) := by positivity
  calc
    ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        Real.exp
          ((k * k : ℕ) *
            ShiuLemma4EndpointWeld.omittedPrimeInvSum y modulus) ≤
      ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        (∏ p ∈ (y + 1).primesBelow,
          (if p ∣ modulus then 1
            else ShiuEndToEnd.eulerInvFactor p ^ (k * k))) :=
      mul_le_mul_of_nonneg_left hexp hratio
    _ ≤ ((modulus : ℝ) / (Nat.totient modulus : ℝ)) *
        (∏ p ∈ (x + 1).primesBelow,
          (if p ∣ modulus then 1
            else ShiuEndToEnd.eulerInvFactor p ^ (k * k))) := by
      exact mul_le_mul_of_nonneg_left
        (ShiuEndToEnd.omittedEulerProduct_mono_cutoff k modulus hyx) hratio
    _ ≤ Real.exp ((k * k : ℕ) * (5 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k * k) :=
      ShiuEndToEnd.modulusTotient_omittedEulerProduct_le_logPow
        k x modulus hk hx hmodulus hmodx

end
end ShiuClassIVEulerBridge

#print axioms ShiuClassIVEulerBridge.exp_omittedPrimeInvSum_le_omittedEulerProduct
#print axioms ShiuClassIVEulerBridge.modulusTotient_mul_exp_omittedPrimeInvSum_le_logPow
