import Mathlib

namespace MAPFordPrimeExponentGap

lemma bad_exponent_le (k d : ℕ) (hk : 2 ≤ k) (hd : d ≤ k) :
    d+(k-d)*(k-d-1) ≤ k*(k-1) := by
  have hk1 : 1 ≤ k-1 := by omega
  have h1 : d ≤ d*(k-1) := by simpa using Nat.mul_le_mul_left d hk1
  have h2 : (k-d)*(k-d-1) ≤ (k-d)*(k-1) :=
    Nat.mul_le_mul_left _ (Nat.sub_le_sub_right (Nat.sub_le k d) 1)
  calc
    _ ≤ d*(k-1)+(k-d)*(k-1) := Nat.add_le_add h1 h2
    _ = k*(k-1) := by rw [← Nat.add_mul, Nat.add_sub_of_le hd]

lemma worst_gap_identity (k : ℕ) (hk : 1 ≤ k) :
    k^3 = (k+1)*(k*(k-1))+k := by
  cases k with
  | zero => omega
  | succ t => simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]; ring

theorem prime_exponent_margin (k d : ℕ) (hk : 2 ≤ k) (hd : d ≤ k) :
    (k+1)*(d+(k-d)*(k-d-1))+k ≤ k^3 := by
  rw [worst_gap_identity k (by omega)]
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (bad_exponent_le k d hk hd)) k

end MAPFordPrimeExponentGap
#print axioms MAPFordPrimeExponentGap.prime_exponent_margin
