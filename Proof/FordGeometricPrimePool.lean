import Mathlib.NumberTheory.Bertrand
import FordFiniteBadPrimeAvoidance

open scoped BigOperators
noncomputable section
namespace MAPFordGeometricPrimePool

/-- A wider geometric pool; this is not a claim of n primes in (M,2M]. -/
theorem exists_geometric_prime_pool (M n : ℕ) (hM : 0 < M) :
    ∃ S : Finset ℕ,
      S.card = n ∧
      (∀ p ∈ S, p.Prime ∧ M < p ∧ p ≤ 2^n*M) ∧
      (M+1)^n ≤ ∏ p ∈ S, p := by
  classical
  have hex : ∀ i : Fin n, ∃ p : ℕ,
      p.Prime ∧ 2^i.val*M < p ∧ p ≤ 2^(i.val+1)*M := by
    intro i
    obtain ⟨p, hp, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul
      (2^i.val*M) (Nat.ne_of_gt (Nat.mul_pos (by positivity) hM))
    refine ⟨p, hp, hlo, ?_⟩
    simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hhi
  choose f hf using hex
  have hmono : StrictMono f := by
    intro i j hij
    have he : i.val+1 ≤ j.val := by exact hij
    have hpw : 2^(i.val+1) ≤ 2^j.val := pow_le_pow_right' (by norm_num) he
    exact (hf i).2.2.trans_lt ((Nat.mul_le_mul_right M hpw).trans_lt (hf j).2.1)
  let S := Finset.univ.image f
  have hc : S.card = n := by
    rw [Finset.card_image_of_injective _ hmono.injective]
    exact Fintype.card_fin n
  refine ⟨S, hc, ?_, ?_⟩
  · intro p hp
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
    refine ⟨(hf i).1, ?_, ?_⟩
    · have hpow : 1 ≤ (2:ℕ)^i.val := Nat.one_le_pow _ _ (by norm_num)
      have hbase : M ≤ 2^i.val*M := by simpa using Nat.mul_le_mul_right M hpow
      exact hbase.trans_lt (hf i).2.1
    · have hpow : (2:ℕ)^(i.val+1) ≤ 2^n := pow_le_pow_right' (by norm_num) i.isLt
      exact (hf i).2.2.trans (Nat.mul_le_mul_right M hpow)
  · calc
      (M+1)^n = ∏ p ∈ S, (M+1) := by simp [hc]
      _ ≤ ∏ p ∈ S, p := by
        apply Finset.prod_le_prod'
        intro p hp
        obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
        have hpow : 1 ≤ (2:ℕ)^i.val := Nat.one_le_pow _ _ (by norm_num)
        have hbase : M ≤ 2^i.val*M := by simpa using Nat.mul_le_mul_right M hpow
        have hlo : M < f i := hbase.trans_lt (hf i).2.1
        omega

theorem exists_prime_avoiding_of_geometric_bound
    (M n : ℕ) (hM : 0 < M) (N : ℤ) (hN : N ≠ 0)
    (hsize : N.natAbs < (M+1)^n) :
    ∃ p : ℕ, p.Prime ∧ M < p ∧ p ≤ 2^n*M ∧ ¬p ∣ N.natAbs := by
  obtain ⟨S, hc, hS, hprod⟩ := exists_geometric_prime_pool M n hM
  obtain ⟨p, hp, havoid⟩ :=
    MAPFordFiniteBadPrimeAvoidance.exists_prime_not_dvd_natAbs_of_prod_gt
      hN S (fun p hp => (hS p hp).1) (hsize.trans_le hprod)
  exact ⟨p, (hS p hp).1, (hS p hp).2.1, (hS p hp).2.2, havoid⟩

end MAPFordGeometricPrimePool
#print axioms MAPFordGeometricPrimePool.exists_geometric_prime_pool
#print axioms MAPFordGeometricPrimePool.exists_prime_avoiding_of_geometric_bound
