import FordGeometricPrimePool
import FordPrimeExponentGap
import FordCoordinatePrimeAvoidance

open scoped BigOperators
noncomputable section
namespace MAPFordGeometricCoordinatePool

lemma size_lt_pool_power (k d M P : ℕ) (hk : 2 ≤ k) (hd : d ≤ k)
    (hM : 1 ≤ M) (hP : P ≤ (M+1)^(k+1)) :
    P^(d+(k-d)*(k-d-1)) < (M+1)^(k^3) := by
  have hgap := MAPFordPrimeExponentGap.prime_exponent_margin k d hk hd
  have hexp : (k+1)*(d+(k-d)*(k-d-1)) < k^3 := by omega
  calc
    P^(d+(k-d)*(k-d-1)) ≤ ((M+1)^(k+1))^(d+(k-d)*(k-d-1)) :=
      Nat.pow_le_pow_left hP _
    _ = (M+1)^((k+1)*(d+(k-d)*(k-d-1))) := by rw [pow_mul]
    _ < (M+1)^(k^3) := Nat.pow_lt_pow_right (by omega) hexp

/-- One fixed geometric pool works for every pair of distinct source tuples.
All widened-pool costs remain explicit in the bounds. -/
theorem exists_uniform_coordinate_pool
    (k d M P Q s : ℕ) (hk : 2 ≤ k) (hd : d ≤ k) (hM : k ≤ M)
    (hP : P ≤ (M+1)^(k+1))
    (hnative : (4*s)^2*(2^(k^3)*M) ≤ Q)
    (T : ℤ) (hT : T ≠ 0) (hTsize : T.natAbs ≤ P^d) :
    ∃ S : Finset ℕ, S.card = k^3 ∧
      (∀ p ∈ S, p.Prime ∧ k < p ∧ p ≤ 2^(k^3)*M ∧ (4*s)^2*p ≤ Q) ∧
      (∀ z w : Fin (k-d) → Fin (P+1),
        Function.Injective z → Function.Injective w →
        ∃ p ∈ S, (T : ZMod p) ≠ 0 ∧
          Function.Injective (fun i => ((z i).val : ZMod p)) ∧
          Function.Injective (fun i => ((w i).val : ZMod p))) := by
  obtain ⟨S, hc, hS, hprod⟩ :=
    MAPFordGeometricPrimePool.exists_geometric_prime_pool M (k^3) (by omega)
  have hsize : P^(d+(k-d)*(k-d-1)) < ∏ p ∈ S, p :=
    (size_lt_pool_power k d M P hk hd (by omega) hP).trans_le hprod
  refine ⟨S, hc, ?_, ?_⟩
  · intro p hp
    refine ⟨(hS p hp).1, lt_of_le_of_lt hM (hS p hp).2.1,
      (hS p hp).2.2, ?_⟩
    exact (Nat.mul_le_mul_left ((4*s)^2) (hS p hp).2.2).trans hnative
  · intro z w hz hw
    exact MAPFordCoordinatePrimeAvoidance.exists_common_coordinate_prime
      (fun p hp => (hS p hp).1) hT hTsize z w hz hw hsize

end MAPFordGeometricCoordinatePool
#print axioms MAPFordGeometricCoordinatePool.exists_uniform_coordinate_pool
