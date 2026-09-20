import MertensAnalyticLeaf

/-!
# Exact uniform Shiu contract and certified specialization inputs

The contract below is Shiu's Theorem 1 at `α = β = 1/3`, before the
natural-number coarsening in `DyadicTauSquareShiuTarget`.  It is a proposition,
not a theorem claimed by this file.  The subsequent theorems prove the exact
weight and Mertens pieces which feed its divisor-square specialization.
-/

namespace ShiuUniformContract

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuAnalyticLayer
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- The prime sum in Shiu's Euler exponential, retaining only primes not
dividing the progression modulus. -/
def omittedPrimeSum (f : ArithmeticFunction ℕ) (x modulus : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (x + 1)).filter Nat.Prime,
    if p ∣ modulus then 0 else (f p : ℝ) * (p : ℝ)⁻¹

/-- Shiu's uniform Brun--Titchmarsh theorem at the exact range needed by MAP.

The constants may depend on the fixed weight `f` and its prime-power
parameter `A`; they are uniform in `x`, `y`, `modulus`, and `residue`.
No progression estimate is included among the hypotheses. -/
def UniformOneThirdShiuContract : Prop :=
  ∀ (f : ArithmeticFunction ℕ) (A : ℕ),
    ShiuNatWeightHypotheses f A →
    ∃ C : ℝ, 0 < C ∧
      ∃ x₀ : ℕ, 3 ≤ x₀ ∧
        ∀ x y modulus residue : ℕ,
          x₀ ≤ x →
          0 < modulus →
          residue < modulus →
          residue.Coprime modulus →
          y ≤ x →
          x < y ^ 3 →
          modulus ^ 3 < y ^ 2 →
          (progressionSum f x y modulus residue : ℝ) ≤
            C * (y : ℝ) /
                ((Nat.totient modulus : ℝ) * Real.log (x : ℝ)) *
              Real.exp (omittedPrimeSum f x modulus)

/-- Omitting primes dividing the modulus can only decrease the nonnegative
prime sum for the divisor-square weight. -/
theorem omittedPrimeSum_tauAFSquare_le
    (k x modulus : ℕ) :
    omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus ≤
      tauAFSquarePrimeReciprocalSum k x := by
  classical
  unfold omittedPrimeSum tauAFSquarePrimeReciprocalSum
  apply Finset.sum_le_sum
  intro p hp
  split_ifs
  · positivity
  · simp [ArithmeticFunction.pmul_apply, pow_two]

/-- Certified coefficient-one Mertens controls Shiu's omitted Euler
exponential for the literal divisor-square weight, uniformly in the modulus. -/
theorem exp_omittedPrimeSum_tauAFSquare_le_explicit
    (k x modulus : ℕ) (hx : 3 ≤ x) :
    Real.exp (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus) ≤
      Real.exp ((k ^ 2 : ℕ) * (1 + 2 * Real.log 4)) *
        (Real.log (x : ℝ)) ^ (k ^ 2) := by
  exact (Real.exp_le_exp.mpr (omittedPrimeSum_tauAFSquare_le k x modulus)).trans
    (MAPMertensAnalyticLeaf.exp_tauAFSquarePrimeReciprocalSum_le_explicit
      k x hx)

/-- The two specialization inputs which are already certified for the literal
divisor-square weight: membership in Shiu's weight class and the required
coefficient-one Euler-exponential bound.  This statement contains no
progression estimate. -/
theorem tauAFSquare_certifiedShiuInputs
    (k x modulus : ℕ) (hk : 1 ≤ k) (hx : 3 ≤ x) :
    ShiuNatWeightHypotheses ((tauAF k).pmul (tauAF k)) (k * k) ∧
      Real.exp (omittedPrimeSum ((tauAF k).pmul (tauAF k)) x modulus) ≤
        Real.exp ((k ^ 2 : ℕ) * (1 + 2 * Real.log 4)) *
          (Real.log (x : ℝ)) ^ (k ^ 2) := by
  exact ⟨tauAF_square_shiuWeightHypotheses k hk,
    exp_omittedPrimeSum_tauAFSquare_le_explicit k x modulus hx⟩

end

end ShiuUniformContract
