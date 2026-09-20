import Mathlib

/-!
# An explicit square-root bound for distinct prime factors

This is the elementary convention-loss estimate needed to transfer a
primitive zero-line functional equation to an ambient Dirichlet character.
The constant 4 isolates the only possible small prime factors, 2 and 3.
-/

namespace MAPPrimeFactorSquareRootBound

open Real

noncomputable section

/-- At most two prime factors of a natural number are smaller than five. -/
theorem card_small_primeFactors_le_two (q : ℕ) :
    (q.primeFactors.filter (fun p => p < 5)).card ≤ 2 := by
  apply Finset.card_le_card (t := {2, 3})
  intro p hp
  simp only [Finset.mem_filter] at hp
  have hpPrime := Nat.prime_of_mem_primeFactors hp.1
  have hpTwo : 2 ≤ p := hpPrime.two_le
  have hpLe : p ≤ 4 := by omega
  have hpNe4 : p ≠ 4 := by
    intro h
    subst p
    norm_num at hpPrime
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

/-- Squared form of the distinct-prime-factor estimate. -/
theorem four_pow_card_primeFactors_le (q : ℕ) (hq : q ≠ 0) :
    (4 : ℕ) ^ q.primeFactors.card ≤ 16 * q := by
  let small := q.primeFactors.filter (fun p => p < 5)
  let large := q.primeFactors.filter (fun p => ¬ p < 5)
  have hsmall : small.card ≤ 2 := by
    simpa [small] using card_small_primeFactors_le_two q
  have hcard : small.card + large.card = q.primeFactors.card := by
    simpa [small, large] using
      (Finset.filter_card_add_filter_neg_card_eq_card
        (s := q.primeFactors) (fun p => p < 5))
  have hsmallPow : (4 : ℕ) ^ small.card ≤ 16 := by
    have h := pow_le_pow_right₀ (a := (4 : ℕ)) (by norm_num) hsmall
    norm_num at h ⊢
    exact h
  have hlargePow : (4 : ℕ) ^ large.card ≤ ∏ p ∈ large, p := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      (fun p hp => by
        have hp' := (Finset.mem_filter.mp hp).2
        omega)
  have hlargeSubset : large ⊆ q.primeFactors := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hlargeProd : (∏ p ∈ large, p) ≤ ∏ p ∈ q.primeFactors, p := by
    exact Finset.prod_le_prod_of_subset_of_one_le' hlargeSubset
      (fun p hp hnot => (Nat.prime_of_mem_primeFactors hp).one_le)
  have hprodQ : (∏ p ∈ q.primeFactors, p) ≤ q :=
    Nat.le_of_dvd (Nat.pos_of_ne_zero hq) (Nat.prod_primeFactors_dvd q)
  calc
    (4 : ℕ) ^ q.primeFactors.card =
        (4 : ℕ) ^ (small.card + large.card) := by rw [hcard]
    _ = (4 : ℕ) ^ small.card * (4 : ℕ) ^ large.card := pow_add 4 _ _
    _ ≤ 16 * (∏ p ∈ large, p) :=
      Nat.mul_le_mul hsmallPow hlargePow
    _ ≤ 16 * (∏ p ∈ q.primeFactors, p) :=
      Nat.mul_le_mul_left 16 hlargeProd
    _ ≤ 16 * q := Nat.mul_le_mul_left 16 hprodQ

/-- Explicit real square-root form. -/
theorem two_pow_card_primeFactors_le_four_sqrt
    (q : ℕ) (hq : q ≠ 0) :
    (2 : ℝ) ^ q.primeFactors.card ≤ 4 * Real.sqrt (q : ℝ) := by
  have hnat := four_pow_card_primeFactors_le q hq
  have hreal : ((4 : ℕ) ^ q.primeFactors.card : ℝ) ≤ 16 * (q : ℝ) := by
    exact_mod_cast hnat
  have hsquare : ((2 : ℝ) ^ q.primeFactors.card) ^ 2 =
      ((4 : ℕ) ^ q.primeFactors.card : ℝ) := by
    push_cast
    rw [pow_two, ← mul_pow]
    norm_num
  have hsqrtSq : (Real.sqrt (q : ℝ)) ^ 2 = (q : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg q)
  have hleft0 : 0 ≤ (2 : ℝ) ^ q.primeFactors.card := by positivity
  have hsqrt0 : 0 ≤ Real.sqrt (q : ℝ) := Real.sqrt_nonneg _
  rw [← hsquare] at hreal
  nlinarith

end
end MAPPrimeFactorSquareRootBound

#print axioms MAPPrimeFactorSquareRootBound.two_pow_card_primeFactors_le_four_sqrt
