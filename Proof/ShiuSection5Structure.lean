import ShiuSection5Split
import ShiuLemma3TauMean

/-!
# Structural multiplicativity in Shiu's Section 5 split

The canonical prefix and suffix consist of disjoint complete prime-power
blocks.  This file proves that they are coprime and records the exact
factorization of the divisor-square weight used in all four class estimates.
-/

namespace ShiuSection5Structure

open ArithmeticFunction MixedMellinCert ShiuFoundation ShiuSection5Split
open scoped ArithmeticFunction.zeta BigOperators

noncomputable section

/-- Products of complementary pieces of a pairwise-coprime list are coprime. -/
lemma List.Pairwise.prod_take_coprime_prod_drop
    {l : List ℕ} (hpair : l.Pairwise Nat.Coprime) (j : ℕ) :
    (l.take j).prod.Coprime (l.drop j).prod := by
  induction l generalizing j with
  | nil => simp
  | cons a l ih =>
      rcases List.pairwise_cons.mp hpair with ⟨ha, hl⟩
      cases j with
      | zero => simp
      | succ j =>
          simp only [List.take_succ_cons, List.prod_cons, List.drop_succ_cons]
          rw [Nat.coprime_mul_iff_left]
          refine ⟨?_, ih hl j⟩
          rw [Nat.coprime_list_prod_right_iff]
          intro b hb
          exact ha b (List.mem_of_mem_drop hb)

/-- The complete prime-power blocks are pairwise coprime. -/
theorem primePowerBlocks_pairwise_coprime (n : ℕ) :
    (primePowerBlocks n).Pairwise Nat.Coprime := by
  have hnodup : (orderedPrimes n).Nodup := by
    simp [orderedPrimes]
  have hpwne : (orderedPrimes n).Pairwise (fun p q ↦ p ≠ q) :=
    List.nodup_iff_pairwise_ne.mp hnodup
  have hpw : (orderedPrimes n).Pairwise
      (fun p q ↦ (p ^ n.factorization p).Coprime
        (q ^ n.factorization q)) := by
    refine hpwne.imp_of_mem ?_
    intro p q hp hq hpq
    have hpfin : p ∈ n.primeFactors := by
      rw [← orderedPrimes_toFinset]
      exact List.mem_toFinset.mpr hp
    have hqfin : q ∈ n.primeFactors := by
      rw [← orderedPrimes_toFinset]
      exact List.mem_toFinset.mpr hq
    exact ((Nat.coprime_primes
      (Nat.prime_of_mem_primeFactors hpfin)
      (Nat.prime_of_mem_primeFactors hqfin)).mpr hpq).pow _ _
  simpa [primePowerBlocks, List.pairwise_map] using hpw

/-- Shiu's canonical prefix and suffix have disjoint prime support. -/
theorem canonicalB_coprime_canonicalD
    {n z : ℕ} (hn : n ≠ 0) (hz : 1 ≤ z) :
    (canonicalB n z).Coprime (canonicalD n z) := by
  rw [canonicalD_eq_suffixProduct hn hz]
  exact List.Pairwise.prod_take_coprime_prod_drop
    (primePowerBlocks_pairwise_coprime n) (canonicalIndex n z)

/-- Exact multiplicative factorization of the MAP square weight. -/
theorem tauSquare_canonical_factorization
    (k : ℕ) {n z : ℕ} (hn : n ≠ 0) (hz : 1 ≤ z) :
    tauAF k n ^ 2 = tauAF k (canonicalB n z) ^ 2 *
      tauAF k (canonicalD n z) ^ 2 := by
  have hcop := canonicalB_coprime_canonicalD hn hz
  have hmul := (tauAF_square_isMultiplicative k).map_mul_of_coprime hcop
  rw [canonicalB_mul_canonicalD hn hz] at hmul
  simpa [ArithmeticFunction.pmul_apply, pow_two] using hmul

end

end ShiuSection5Structure

#print axioms ShiuSection5Structure.canonicalB_coprime_canonicalD
#print axioms ShiuSection5Structure.tauSquare_canonical_factorization
