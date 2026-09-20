import Mathlib

noncomputable section
set_option autoImplicit false
namespace FordWeakTotalCoefficient

private lemma nat_le_two_pow (n : ℕ) : n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        n + 1 ≤ 2 ^ n + 1 := Nat.succ_le_succ ih
        _ ≤ 2 ^ n + 2 ^ n := by
          have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
          omega
        _ = 2 ^ (n + 1) := by rw [pow_succ]; ring

private lemma factorial_real_le_two_pow
    {k : ℕ} (hk : 1 ≤ k) :
    (k.factorial : ℝ) ≤ (2 : ℝ) ^ (k ^ 2) := by
  have hfac : k.factorial ≤ k ^ k := Nat.factorial_le_pow k
  have hbase : k ≤ 2 ^ k := nat_le_two_pow k
  have hpow : k ^ k ≤ (2 ^ k) ^ k := Nat.pow_le_pow_left hbase _
  have hpow' : k ^ k ≤ 2 ^ (k ^ 2) := by
    calc
      k ^ k ≤ (2 ^ k) ^ k := hpow
      _ = 2 ^ (k * k) := by rw [← pow_mul]
      _ = 2 ^ (k ^ 2) := by congr 1 <;> ring
  exact_mod_cast hfac.trans hpow'

/-- Natural trajectory length gives the elementary linear bound used by the
large-P coefficient envelope. -/
theorem natural_length_bound
    {k n : ℕ} (hk : 2000 ≤ k) (hn : n ≤ 1001 * k + 1) :
    n ≤ 1002 * k := by
  omega

/-- Total factorial and repeated J2 coefficient cost, with the deliberately
large `2^24 k^6` envelope. -/
theorem total_coefficient_bound
    {k n : ℕ} (hk : 2000 ≤ k) (hn : n ≤ 1001 * k + 1) :
    (k.factorial : ℝ) * (2 : ℝ) ^ (n * (8192 * k ^ 5)) ≤
      (2 : ℝ) ^ ((2 ^ 24) * k ^ 6) := by
  have hk1 : 1 ≤ k := by omega
  have hn' : n ≤ 1002 * k := natural_length_bound hk hn
  have hN : n * (8192 * k ^ 5) ≤ 8192 * 1002 * k ^ 6 := by
    calc
      n * (8192 * k ^ 5) ≤ (1002 * k) * (8192 * k ^ 5) :=
        Nat.mul_le_mul_right _ hn'
      _ = 8192 * 1002 * k ^ 6 := by ring
  have hk2k6 : k ^ 2 ≤ k ^ 6 := by
    have hk4 : 1 ≤ k ^ 4 := Nat.one_le_pow _ _ (by omega)
    calc
      k ^ 2 ≤ k ^ 2 * k ^ 4 := by
        simpa using (Nat.mul_le_mul_left (k ^ 2) hk4)
      _ = k ^ 6 := by ring
  have hExp : k ^ 2 + n * (8192 * k ^ 5) ≤ (2 ^ 24) * k ^ 6 := by
    have hsum : k ^ 2 + n * (8192 * k ^ 5) ≤
        k ^ 2 + 8192 * 1002 * k ^ 6 := Nat.add_le_add_left hN _
    have hcoef : 1 + 8192 * 1002 ≤ 2 ^ 24 := by norm_num
    calc
      k ^ 2 + n * (8192 * k ^ 5) ≤ k ^ 2 + 8192 * 1002 * k ^ 6 := hsum
      _ ≤ k ^ 6 + 8192 * 1002 * k ^ 6 :=
        Nat.add_le_add_right hk2k6 _
      _ = (1 + 8192 * 1002) * k ^ 6 := by ring
      _ ≤ (2 ^ 24) * k ^ 6 := Nat.mul_le_mul_right _ hcoef
  have hfac := factorial_real_le_two_pow hk1
  calc
    (k.factorial : ℝ) * (2 : ℝ) ^ (n * (8192 * k ^ 5)) ≤
        (2 : ℝ) ^ (k ^ 2) * (2 : ℝ) ^ (n * (8192 * k ^ 5)) :=
      mul_le_mul_of_nonneg_right hfac (by positivity)
    _ = (2 : ℝ) ^ (k ^ 2 + n * (8192 * k ^ 5)) := by
      rw [← pow_add]
    _ ≤ (2 : ℝ) ^ ((2 ^ 24) * k ^ 6) := by
      exact pow_le_pow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hExp

end FordWeakTotalCoefficient
#print axioms FordWeakTotalCoefficient.total_coefficient_bound
