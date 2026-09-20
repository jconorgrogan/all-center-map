import Mathlib

open scoped BigOperators
noncomputable section
namespace MAPFordFiniteBadPrimeAvoidance

/-- A pairwise-coprime finite family of divisors of `n` has product dividing
`n`.  The pairwise hypothesis is explicit so the proof does not smuggle in a
squarefree or prime-factor assumption. -/
lemma prod_dvd_of_pairwise_coprime_dvd
    {S : Finset ℕ} {n : ℕ}
    (hdiv : ∀ p ∈ S, p ∣ n)
    (hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q) :
    (∏ p ∈ S, p) ∣ n := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
      have hdivS : ∀ p ∈ S, p ∣ n := by
        intro p hp
        exact hdiv p (Finset.mem_insert_of_mem hp)
      have hcopS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q := by
        intro p hp q hq hpq
        exact hcop p (Finset.mem_insert_of_mem hp) q
          (Finset.mem_insert_of_mem hq) hpq
      have hprodS : (∏ p ∈ S, p) ∣ n := ih hdivS hcopS
      have hacop : Nat.Coprime a (∏ p ∈ S, p) := by
        apply Nat.Coprime.prod_right
        intro p hp
        exact hcop a (Finset.mem_insert_self a S) p
          (Finset.mem_insert_of_mem hp) (by
            intro heq
            apply ha
            simpa [heq] using hp)
      have hadiv : a ∣ n := hdiv a (Finset.mem_insert_self a S)
      rw [Finset.prod_insert ha]
      exact hacop.mul_dvd_of_dvd_of_dvd hadiv hprodS

/-- If the product of a finite pairwise-coprime prime family is larger than a
nonzero integer's absolute value, one member is a bad-prime escape. -/
theorem exists_prime_not_dvd_natAbs_of_prod_gt
    {N : ℤ} (hN : N ≠ 0) (S : Finset ℕ)
    (hprime : ∀ p ∈ S, p.Prime)
    (hprod : N.natAbs < ∏ p ∈ S, p) :
    ∃ p ∈ S, ¬ p ∣ N.natAbs := by
  by_contra hnone
  push Not at hnone
  have hdiv : ∀ p ∈ S, p ∣ N.natAbs := by
    intro p hp
    exact hnone p hp
  have hcop : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → Nat.Coprime p q := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr hpq
  have hall : (∏ p ∈ S, p) ∣ N.natAbs :=
    prod_dvd_of_pairwise_coprime_dvd hdiv hcop
  have hNpos : 0 < N.natAbs := Int.natAbs_pos.mpr hN
  have hle : (∏ p ∈ S, p) ≤ N.natAbs := Nat.le_of_dvd hNpos hall
  exact (Nat.not_lt_of_ge hle) hprod

/-- The signed determinant-style product retains the source's factor order and
signs.  The pair lists encode the free-left and free-right differences. -/
def signedDifferenceProduct
    (T : ℤ) (left right : Finset (ℤ × ℤ)) : ℤ :=
  T * (∏ a ∈ left, (a.1 - a.2)) * (∏ a ∈ right, (a.1 - a.2))

lemma signedDifferenceProduct_ne_zero
    {T : ℤ} {left right : Finset (ℤ × ℤ)}
    (hT : T ≠ 0)
    (hleft : ∀ a ∈ left, a.1 ≠ a.2)
    (hright : ∀ a ∈ right, a.1 ≠ a.2) :
    signedDifferenceProduct T left right ≠ 0 := by
  unfold signedDifferenceProduct
  have hleft0 : (∏ a ∈ left, (a.1 - a.2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact sub_ne_zero.mpr (hleft a ha)
  have hright0 : (∏ a ∈ right, (a.1 - a.2)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact sub_ne_zero.mpr (hright a ha)
  exact mul_ne_zero (mul_ne_zero hT hleft0) hright0

/-- Simultaneous bad-prime avoidance for the exact signed source product.
The conclusion is factorwise: a prime escaping the full product escapes the
integer factor and every signed difference factor. -/
theorem exists_prime_avoiding_signed_difference_product
    {S : Finset ℕ}
    (hprime : ∀ p ∈ S, p.Prime)
    {T : ℤ} {left right : Finset (ℤ × ℤ)}
    (hT : T ≠ 0)
    (hleft : ∀ a ∈ left, a.1 ≠ a.2)
    (hright : ∀ a ∈ right, a.1 ≠ a.2)
    (hprod : (signedDifferenceProduct T left right).natAbs < ∏ p ∈ S, p) :
    ∃ p ∈ S,
      ¬ p ∣ T.natAbs ∧
      (∀ a ∈ left, ¬ p ∣ (a.1 - a.2).natAbs) ∧
      (∀ a ∈ right, ¬ p ∣ (a.1 - a.2).natAbs) := by
  classical
  have hN : signedDifferenceProduct T left right ≠ 0 :=
    signedDifferenceProduct_ne_zero hT hleft hright
  obtain ⟨p, hpS, hpfull⟩ :=
    exists_prime_not_dvd_natAbs_of_prod_gt hN S hprime hprod
  have hnatAbsProd : ∀ (U : Finset (ℤ × ℤ)),
      (∏ a ∈ U, (a.1 - a.2)).natAbs =
        ∏ a ∈ U, (a.1 - a.2).natAbs := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert a U ha ih =>
        simp [ha, ih, Int.natAbs_mul]
  have hfull_expand :
      (signedDifferenceProduct T left right).natAbs =
        T.natAbs * (∏ a ∈ left, (a.1 - a.2).natAbs) *
          (∏ a ∈ right, (a.1 - a.2).natAbs) := by
    unfold signedDifferenceProduct
    rw [Int.natAbs_mul, Int.natAbs_mul,
      hnatAbsProd left, hnatAbsProd right]
  have hTfactor : T.natAbs ∣
      (signedDifferenceProduct T left right).natAbs := by
    rw [hfull_expand]
    exact ⟨(∏ a ∈ left, (a.1 - a.2).natAbs) *
      (∏ a ∈ right, (a.1 - a.2).natAbs), by ring⟩
  have hleftfactor : (∏ a ∈ left, (a.1 - a.2).natAbs) ∣
      (signedDifferenceProduct T left right).natAbs := by
    rw [hfull_expand]
    exact ⟨T.natAbs * (∏ a ∈ right, (a.1 - a.2).natAbs), by ring⟩
  have hrightfactor : (∏ a ∈ right, (a.1 - a.2).natAbs) ∣
      (signedDifferenceProduct T left right).natAbs := by
    rw [hfull_expand]
    exact ⟨T.natAbs * (∏ a ∈ left, (a.1 - a.2).natAbs), by ring⟩
  refine ⟨p, hpS, ?_, ?_, ?_⟩
  · intro hdiv
    exact hpfull (hdiv.trans hTfactor)
  · intro a ha hdiv
    exact hpfull (hdiv.trans
      ((Finset.dvd_prod_of_mem
        (fun a : ℤ × ℤ => (a.1 - a.2).natAbs) ha).trans hleftfactor))
  · intro a ha hdiv
    exact hpfull (hdiv.trans
      ((Finset.dvd_prod_of_mem
        (fun a : ℤ × ℤ => (a.1 - a.2).natAbs) ha).trans hrightfactor))

end MAPFordFiniteBadPrimeAvoidance

#print axioms MAPFordFiniteBadPrimeAvoidance.exists_prime_not_dvd_natAbs_of_prod_gt
#print axioms MAPFordFiniteBadPrimeAvoidance.signedDifferenceProduct_ne_zero
#print axioms MAPFordFiniteBadPrimeAvoidance.exists_prime_avoiding_signed_difference_product
